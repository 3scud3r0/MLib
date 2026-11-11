// POSIX single-flight mailbox. All readers/writers take flock on the shm fd.
// Wire integers are little-endian; no std::atomic ABI is shared with clients.
class SharedMemoryMailbox {
    int fd_=-1;uint8_t* bytes_=nullptr;std::string name_;
    static constexpr size_t header_size=32,capacity=1024*1024;
    uint64_t get(size_t pos,size_t width)const {
        uint64_t r=0;for(size_t i=0;i<width;++i)r|=uint64_t(bytes_[pos+i])<<(8*i);return r;
    }
    void put(size_t pos,size_t width,uint64_t n) {
        for(size_t i=0;i<width;++i)bytes_[pos+i]=(uint8_t)(n>>(8*i));
    }
    void lock(Clock::time_point deadline) {
        while(::flock(fd_,LOCK_EX|LOCK_NB)!=0) {
            require(errno==EAGAIN||errno==EWOULDBLOCK||errno==EINTR,"IPC lock failure");
            require(Clock::now()<deadline,"IPC lock timeout");::usleep(1000);
        }
    }
    void unlock(){::flock(fd_,LOCK_UN);}
    void validate()const {
        require(std::memcmp(bytes_,"GDIPC001",8)==0&&get(8,4)==1&&get(28,4)==0,"IPC schema mismatch");
        require(get(24,4)<=capacity,"IPC payload length exceeds capacity");
    }
public:
    explicit SharedMemoryMailbox(std::string name):name_(std::move(name)) {
        require(name_.size()>1&&name_.size()<120&&name_[0]=='/',"invalid POSIX shm name");
        for(size_t i=1;i<name_.size();++i)require(std::isalnum((unsigned char)name_[i])||name_[i]=='_'||name_[i]=='-',"invalid shm name character");
        fd_=::shm_open(name_.c_str(),O_RDWR|O_CREAT|O_EXCL|O_CLOEXEC,0600);
        require(fd_>=0,"cannot create exclusive IPC mailbox (name already in use?)");
        try {
            lock(Clock::now()+std::chrono::milliseconds(1000));
            require(::fchmod(fd_,0600)==0&&::ftruncate(fd_,header_size+capacity)==0,"cannot size IPC mailbox");
            void* p=::mmap(nullptr,header_size+capacity,PROT_READ|PROT_WRITE,MAP_SHARED,fd_,0);
            require(p!=MAP_FAILED,"cannot map IPC mailbox");bytes_=static_cast<uint8_t*>(p);
            std::memset(bytes_,0,header_size);std::memcpy(bytes_,"GDIPC001",8);put(8,4,1);unlock();
        }catch(...) {::close(fd_);fd_=-1;::shm_unlink(name_.c_str());throw;}
    }
    SharedMemoryMailbox(const SharedMemoryMailbox&)=delete;
    ~SharedMemoryMailbox() {
        if(bytes_)::munmap(bytes_,header_size+capacity);
        if(fd_>=0){::close(fd_);::shm_unlink(name_.c_str());}
    }
    void publish(uint32_t state,uint64_t request,std::string_view payload,Clock::time_point deadline) {
        require(payload.size()<=capacity,"outgoing IPC payload budget");lock(deadline);
        std::memcpy(bytes_+header_size,payload.data(),payload.size());
        put(16,8,request);put(24,4,payload.size());put(12,4,state);unlock();
    }
    std::string response(uint64_t request,Clock::time_point deadline) {
        while(Clock::now()<deadline) {
            lock(deadline);
            try {
                validate();auto state=get(12,4);
                require(get(16,8)==request,"IPC stale request id");
                if(state==2) {
                    std::string r(reinterpret_cast<char*>(bytes_+header_size),(size_t)get(24,4));unlock();return r;
                }
                require(state==1,"unexpected IPC state");unlock();
            }catch(...) {unlock();throw;}
            ::usleep(2000);
        }
        throw std::runtime_error("IPC proposal timeout");
    }
};
static std::string proposal_expression(std::string_view response,uint64_t request,const std::string& source_hash) {
    require(response.size()<100000&&response.find('\0')==std::string_view::npos,"IPC response size/encoding");
    std::string_view magic,id,hash,expression,rest;
    require(split_once(response,'\n',magic,rest)&&magic=="GODEL_REPLACE_V1"&&
        split_once(rest,'\n',id,rest)&&split_once(rest,'\n',hash,expression),"invalid proposal frame");
    require(id==std::to_string(request)&&hash==source_hash,"proposal is bound to another request/source");
    require(expression.find('\n')==std::string_view::npos&&expression.find('\r')==std::string_view::npos,"proposal must contain exactly one expression");
    return std::string(expression);
}
static int ipc_optimize(const std::string& name,size_t vars,const std::string& source,
    uint32_t timeout_ms,const std::string& output) {
    require(timeout_ms>0&&timeout_ms<=60000,"IPC timeout range 1..60000 ms");
    ExpressionGraph graph;TrustedKernel kernel;auto before=AlgebraParser(graph,source,vars).parse();
    // Validate all input semantics before publishing a request.
    graph.symbolic(before,vars);auto repr=graph.repr(before),hash=blake3::hex(repr);
    SharedMemoryMailbox mailbox(name);
    uint64_t id=uint64_t(Clock::now().time_since_epoch().count())^uint64_t(::getpid());
    auto deadline=Clock::now()+std::chrono::milliseconds(timeout_ms);
    std::string request="{\"schema\":\"godel-proposal-v1\",\"request_id\":\""+std::to_string(id)+
        "\",\"variables\":"+std::to_string(vars)+",\"source_blake3\":"+json_string(hash)+
        ",\"source\":"+json_string(repr)+",\"static_cost\":"+std::to_string(graph.static_cost(before))+"}";
    mailbox.publish(1,id,request,deadline);std::cout<<"[IPC] ready "<<name<<std::endl;
    try {
        auto text=proposal_expression(mailbox.response(id,deadline),id,hash);
        auto after=AlgebraParser(graph,text,vars).parse();
        auto cert=certify_graph_improvement(kernel,graph,before,after,vars);
        auto path=export_lean(kernel,graph,before,after,vars,cert,output);
        auto result="{\"accepted\":true,\"cpp_verified\":true,\"lean_status\":\"pending-kernel\",\"lean_file\":"+json_string(path)+"}";
        mailbox.publish(3,id,result,Clock::now()+std::chrono::milliseconds(1000));
        std::cout<<result<<"\n";return 0;
    }catch(const std::exception& e) {
        auto result="{\"accepted\":false,\"error\":"+json_string(e.what())+"}";
        try{mailbox.publish(3,id,result,Clock::now()+std::chrono::milliseconds(100));}catch(...){}
        std::cerr<<result<<"\n";return 1;
    }
}
