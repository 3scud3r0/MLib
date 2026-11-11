// Included inside namespace godel, after the exact arithmetic/kernel definitions.
// Pure, total, bounded DSL. No native instructions or model-supplied proof code.
enum class ExprKind:uint8_t { Constant,Variable,Add,Multiply,Negate,Power,
    IfLess,Tensor,BoundedLoop,Accumulator,LoopIndex };
struct ExprNode {
    ExprKind kind=ExprKind::Constant;
    int32_t left=-1,right=-1;
    uint32_t index=0;
    Q value=0;
    bool alive=true;
    int32_t guard_left=-1,guard_right=-1;
    uint32_t binding=0;
    std::vector<uint32_t> shape;
    std::vector<int32_t> entries;
};

// Polynomial ring over named atoms. Conditional subexpressions are opaque atoms;
// equality here is sound but deliberately incomplete for piecewise functions.
struct SymbolicScalar {
    using Monomial=std::map<std::string,uint32_t>;
    std::map<Monomial,Q> terms;
    static SymbolicScalar constant(const Q& q) {
        SymbolicScalar r;if(q!=0)r.terms[{}]=q;return r;
    }
    static SymbolicScalar atom(const std::string& name) {
        SymbolicScalar r;r.terms[{{name,1}}]=1;return r;
    }
    void add_term(const Monomial& m,const Q& q) {
        if(q==0)return;
        require(mpz_sizeinbase(q.get_num_mpz_t(),2)<=65536&&mpz_sizeinbase(q.get_den_mpz_t(),2)<=65536,"rational bit budget");
        Q& t=terms[m];t+=q;
        require(mpz_sizeinbase(t.get_num_mpz_t(),2)<=65536&&mpz_sizeinbase(t.get_den_mpz_t(),2)<=65536,"coefficient growth budget");
        if(t==0)terms.erase(m);
        require(terms.size()<=10000,"symbolic term budget");
    }
    SymbolicScalar operator+(const SymbolicScalar& b)const {
        auto r=*this;for(const auto& t:b.terms)r.add_term(t.first,t.second);return r;
    }
    SymbolicScalar operator-()const {
        auto r=*this;for(auto& t:r.terms)t.second=-t.second;return r;
    }
    SymbolicScalar operator*(const SymbolicScalar& b)const {
        require(b.terms.empty()||terms.size()<=10000/b.terms.size(),"symbolic product budget");
        SymbolicScalar r;
        for(const auto& a:terms)for(const auto& t:b.terms) {
            auto m=a.first;
            for(const auto& e:t.first) {
                uint64_t p=uint64_t(m[e.first])+e.second;
                require(p<=65535,"symbolic exponent budget");m[e.first]=(uint32_t)p;
            }
            r.add_term(m,a.second*t.second);
        }
        return r;
    }
    SymbolicScalar pow(uint32_t n)const {
        auto r=constant(1),b=*this;
        while(n){if(n&1)r=r*b;n>>=1;if(n)b=b*b;}return r;
    }
    std::optional<Q> number()const {
        if(terms.empty())return Q(0);
        if(terms.size()==1&&terms.begin()->first.empty())return terms.begin()->second;
        return std::nullopt;
    }
    std::string canonical()const {
        std::string s;
        for(const auto& t:terms) {
            s+="("+t.second.get_str();
            for(const auto& e:t.first)s+=";"+std::to_string(e.first.size())+":"+e.first+"^"+std::to_string(e.second);
            s+=")";require(s.size()<1024*1024,"symbolic representation budget");
        }
        return s;
    }
};
struct SymbolicValue {
    std::vector<uint32_t> shape;
    std::vector<SymbolicScalar> cells;
    std::string canonical()const {
        std::string s="shape:";
        for(auto d:shape)s+=std::to_string(d)+",";
        for(const auto& c:cells){auto t=c.canonical();s+="|"+std::to_string(t.size())+":"+t;}
        require(s.size()<4*1024*1024,"symbolic tensor representation budget");return s;
    }
};
class ExpressionGraph {
    std::vector<ExprNode> nodes_;
    std::unordered_map<std::string,int32_t> interned_;
    std::vector<int32_t> persistent_;
    uint32_t next_binding_=1;
    std::string key(const ExprNode& n)const {
        std::string s=std::to_string((unsigned)n.kind)+"|"+std::to_string(n.left)+"|"+
            std::to_string(n.right)+"|"+std::to_string(n.index)+"|"+n.value.get_str()+"|"+
            std::to_string(n.guard_left)+"|"+std::to_string(n.guard_right)+"|"+std::to_string(n.binding);
        for(auto d:n.shape)s+="d"+std::to_string(d);
        for(auto e:n.entries)s+="e"+std::to_string(e);
        return s;
    }
    int32_t make(ExprNode n) {
        auto k=key(n);auto it=interned_.find(k);
        if(it!=interned_.end()&&nodes_[it->second].alive)return it->second;
        require(nodes_.size()<kMaxAstNodes,"AST capacity exceeded");
        auto id=(int32_t)nodes_.size();nodes_.push_back(std::move(n));interned_.emplace(std::move(k),id);return id;
    }
    int32_t binary(ExprKind kind,int32_t a,int32_t b) {
        require(at(a).shape==at(b).shape,"operand shape mismatch");
        ExprNode n;n.kind=kind;n.left=a;n.right=b;n.shape=at(a).shape;return make(n);
    }
public:
    static size_t elements(const std::vector<uint32_t>& shape) {
        size_t count=1;require(shape.size()<=4,"tensor rank budget");
        for(auto d:shape){require(d>0&&d<=1024/count,"tensor element budget");count*=d;}return count;
    }
    const ExprNode& at(int32_t id)const {
        require(id>=0&&(size_t)id<nodes_.size()&&nodes_[id].alive,"invalid AST node");return nodes_[id];
    }
    std::vector<int32_t> children(int32_t id)const {
        const auto& n=at(id);std::vector<int32_t> r;
        for(auto c:{n.left,n.right,n.guard_left,n.guard_right})if(c>=0)r.push_back(c);
        r.insert(r.end(),n.entries.begin(),n.entries.end());return r;
    }
    int32_t constant(Q q) {q.canonicalize();ExprNode n;n.value=q;return make(n);}
    int32_t variable(uint32_t i) {require(i<16,"expression variable index");ExprNode n;n.kind=ExprKind::Variable;n.index=i;return make(n);}
    int32_t add(int32_t a,int32_t b){return binary(ExprKind::Add,a,b);}
    int32_t multiply(int32_t a,int32_t b){return binary(ExprKind::Multiply,a,b);}
    int32_t negate(int32_t a){ExprNode n;n.kind=ExprKind::Negate;n.left=a;n.shape=at(a).shape;return make(n);}
    int32_t power(int32_t a,uint32_t e){require(e<=128,"power quota");ExprNode n;n.kind=ExprKind::Power;n.left=a;n.index=e;n.shape=at(a).shape;return make(n);}
    int32_t if_less(int32_t a,int32_t b,int32_t yes,int32_t no) {
        require(at(a).shape.empty()&&at(b).shape.empty(),"comparison requires scalars");
        require(at(yes).shape==at(no).shape,"conditional branch shape mismatch");
        ExprNode n;n.kind=ExprKind::IfLess;n.left=yes;n.right=no;n.guard_left=a;n.guard_right=b;n.shape=at(yes).shape;return make(n);
    }
    int32_t tensor(std::vector<uint32_t> shape,std::vector<int32_t> entries) {
        require(!shape.empty()&&elements(shape)==entries.size(),"tensor shape/data mismatch");
        for(auto e:entries)require(at(e).shape.empty(),"tensor entries must be scalar");
        ExprNode n;n.kind=ExprKind::Tensor;n.shape=std::move(shape);n.entries=std::move(entries);return make(n);
    }
    int32_t bounded_loop(uint32_t count,int32_t initial,const std::function<int32_t(int32_t,int32_t)>& body) {
        require(count<=64,"loop iteration budget");
        uint32_t binding=next_binding_++;
        ExprNode a;a.kind=ExprKind::Accumulator;a.binding=binding;a.shape=at(initial).shape;
        auto acc=make(a);ExprNode i;i.kind=ExprKind::LoopIndex;i.binding=binding;auto index=make(i);
        auto result=body(acc,index);
        require(at(result).shape==at(initial).shape,"loop changes state shape");
        ExprNode n;n.kind=ExprKind::BoundedLoop;n.left=initial;n.right=result;n.index=count;n.binding=binding;n.shape=at(initial).shape;return make(n);
    }
    int32_t matrix_multiply(int32_t a,int32_t b) {
        auto x=at(a),y=at(b);
        require(x.kind==ExprKind::Tensor&&y.kind==ExprKind::Tensor&&x.shape.size()==2&&y.shape.size()==2&&x.shape[1]==y.shape[0],"matmul requires compatible literal rank-2 tensors");
        std::vector<int32_t> cells;
        for(uint32_t i=0;i<x.shape[0];++i)for(uint32_t j=0;j<y.shape[1];++j) {
            auto sum=constant(0);
            for(uint32_t k=0;k<x.shape[1];++k)sum=add(sum,multiply(x.entries[i*x.shape[1]+k],y.entries[k*y.shape[1]+j]));
            cells.push_back(sum);
        }
        return tensor({x.shape[0],y.shape[1]},std::move(cells));
    }
    size_t size()const{return nodes_.size();}
    void protect(int32_t r){at(r);persistent_.push_back(r);}
    void unprotect(int32_t r){auto it=std::find(persistent_.begin(),persistent_.end(),r);if(it!=persistent_.end())persistent_.erase(it);}
    std::vector<int32_t> preorder(int32_t root,size_t max_nodes=10000)const {
        std::vector<int32_t> r,stack{root};std::unordered_set<int32_t> seen;
        while(!stack.empty()) {
            auto id=stack.back();stack.pop_back();if(!seen.insert(id).second)continue;
            at(id);r.push_back(id);require(r.size()<=max_nodes,"AST walk budget");
            auto cs=children(id);for(auto it=cs.rbegin();it!=cs.rend();++it)stack.push_back(*it);
        }
        return r;
    }
    size_t collect(const std::vector<int32_t>& transient={}) {
        std::unordered_set<int32_t> marked;auto roots=persistent_;roots.insert(roots.end(),transient.begin(),transient.end());
        for(auto root:roots)for(auto id:preorder(root,kMaxAstNodes))marked.insert(id);
        size_t count=0;for(size_t i=0;i<nodes_.size();++i)if(nodes_[i].alive&&!marked.count((int32_t)i)) {
            interned_.erase(key(nodes_[i]));nodes_[i].alive=false;++count;
        }
        return count;
    }
    bool polynomial_only(int32_t root)const {
        for(auto id:preorder(root))if(at(id).kind>ExprKind::Power||!at(id).shape.empty())return false;
        return true;
    }
    Polynomial polynomial(int32_t root,size_t vars)const {
        require(polynomial_only(root),"program is not a scalar polynomial");
        std::unordered_map<int32_t,Polynomial> memo;
        std::function<Polynomial(int32_t,size_t)> eval=[&](int32_t id,size_t depth) {
            require(depth<256,"AST depth budget");auto it=memo.find(id);if(it!=memo.end())return it->second;
            const auto& n=at(id);Polynomial r(vars);
            switch(n.kind) {
            case ExprKind::Constant:r=Polynomial::constant(vars,n.value);break;
            case ExprKind::Variable:r=Polynomial::variable(vars,n.index);break;
            case ExprKind::Add:r=eval(n.left,depth+1)+eval(n.right,depth+1);break;
            case ExprKind::Multiply:r=eval(n.left,depth+1)*eval(n.right,depth+1);break;
            case ExprKind::Negate:r=-eval(n.left,depth+1);break;
            case ExprKind::Power:r=eval(n.left,depth+1).pow(n.index);break;
            default:throw std::runtime_error("nonpolynomial node");
            }
            memo.emplace(id,r);return r;
        };return eval(root,0);
    }
    SymbolicValue symbolic(int32_t root,size_t vars)const {
        require(vars>0&&vars<=16,"program input arity");size_t fuel=50000;
        std::map<uint32_t,std::pair<SymbolicValue,uint32_t>> bindings;
        std::function<SymbolicValue(int32_t,size_t)> eval=[&](int32_t id,size_t depth)->SymbolicValue {
            require(fuel>0&&depth<128,"symbolic evaluation budget");--fuel;
            const auto& n=at(id);SymbolicValue r;r.shape=n.shape;
            switch(n.kind) {
            case ExprKind::Constant:r.cells={SymbolicScalar::constant(n.value)};break;
            case ExprKind::Variable:require(n.index<vars,"variable outside declared arity");r.cells={SymbolicScalar::atom("x"+std::to_string(n.index))};break;
            case ExprKind::Accumulator:require(bindings.count(n.binding),"unbound loop accumulator");return bindings.at(n.binding).first;
            case ExprKind::LoopIndex:require(bindings.count(n.binding),"unbound loop index");r.cells={SymbolicScalar::constant(Q(bindings.at(n.binding).second))};break;
            case ExprKind::Tensor:
                for(auto e:n.entries)r.cells.push_back(eval(e,depth+1).cells.at(0));
                break;
            case ExprKind::BoundedLoop: {
                r=eval(n.left,depth+1);
                for(uint32_t i=0;i<n.index;++i){bindings[n.binding]={r,i};r=eval(n.right,depth+1);}
                bindings.erase(n.binding);break;
            }
            case ExprKind::IfLess: {
                auto a=eval(n.guard_left,depth+1).cells.at(0),b=eval(n.guard_right,depth+1).cells.at(0);
                auto an=a.number(),bn=b.number();
                if(an&&bn)return eval(*an<*bn?n.left:n.right,depth+1);
                auto yes=eval(n.left,depth+1),no=eval(n.right,depth+1);
                auto sa=a.canonical(),sb=b.canonical();
                for(size_t i=0;i<yes.cells.size();++i) {
                    auto sy=yes.cells[i].canonical(),sn=no.cells[i].canonical();
                    r.cells.push_back(sy==sn?yes.cells[i]:SymbolicScalar::atom("if:"+
                        std::to_string(sa.size())+":"+sa+std::to_string(sb.size())+":"+sb+
                        std::to_string(sy.size())+":"+sy+std::to_string(sn.size())+":"+sn));
                }
                break;
            }
            default: {
                auto a=eval(n.left,depth+1);std::optional<SymbolicValue> b;
                if(n.right>=0)b=eval(n.right,depth+1);
                for(size_t i=0;i<a.cells.size();++i) {
                    const auto& x=a.cells[i];
                    if(n.kind==ExprKind::Add)r.cells.push_back(x+b->cells[i]);
                    else if(n.kind==ExprKind::Multiply)r.cells.push_back(x*b->cells[i]);
                    else if(n.kind==ExprKind::Negate)r.cells.push_back(-x);
                    else r.cells.push_back(x.pow(n.index));
                }
            }
            }
            return r;
        };return eval(root,0);
    }
    uint32_t static_cost(int32_t root)const {
        size_t fuel=100000;
        std::function<uint64_t(int32_t,size_t)> cost=[&](int32_t id,size_t depth) {
            require(fuel>0&&depth<256,"cost traversal budget");--fuel;const auto& n=at(id);
            uint64_t base=1,result=0;
            switch(n.kind) {
            case ExprKind::Add:base=3;break;
            case ExprKind::Multiply:base=6;break;
            case ExprKind::Negate:base=2;break;
            case ExprKind::Power:base=2+4*n.index;break;
            case ExprKind::BoundedLoop:
                result=2+cost(n.left,depth+1)+n.index*(1+cost(n.right,depth+1));break;
            default:break;
            }
            if(n.kind!=ExprKind::BoundedLoop) {
                result=base;for(auto c:children(id))result+=cost(c,depth+1);
            }
            require(result<INT32_MAX,"static cost budget");return result;
        };return (uint32_t)cost(root,0);
    }
    std::string repr(int32_t root)const {
        std::vector<uint32_t> bindings;size_t fuel=30000;
        std::function<std::string(int32_t,size_t)> walk=[&](int32_t id,size_t depth)->std::string {
            require(fuel>0&&depth<256,"repr budget");--fuel;const auto& n=at(id);
            auto sub=[&](int32_t c){return walk(c,depth+1);};std::string r;
            switch(n.kind) {
            case ExprKind::Constant:r=n.value<0?"q("+n.value.get_str()+")":n.value.get_str();break;
            case ExprKind::Variable:r="x"+std::to_string(n.index);break;
            case ExprKind::Add:r="("+sub(n.left)+"+"+sub(n.right)+")";break;
            case ExprKind::Multiply:r="("+sub(n.left)+"*"+sub(n.right)+")";break;
            case ExprKind::Negate:r="(-"+sub(n.left)+")";break;
            case ExprKind::Power:r="("+sub(n.left)+")^"+std::to_string(n.index);break;
            case ExprKind::IfLess:r="iflt("+sub(n.guard_left)+","+sub(n.guard_right)+","+sub(n.left)+","+sub(n.right)+")";break;
            case ExprKind::Tensor:
                r="tensor([";for(size_t i=0;i<n.shape.size();++i)r+=(i?",":"")+std::to_string(n.shape[i]);
                r+="],[";for(size_t i=0;i<n.entries.size();++i)r+=(i?",":"")+sub(n.entries[i]);r+="])";break;
            case ExprKind::BoundedLoop: {
                auto initial=sub(n.left);bindings.push_back(n.binding);auto body=sub(n.right);bindings.pop_back();
                r="fold("+std::to_string(n.index)+","+initial+","+body+")";break;
            }
            case ExprKind::Accumulator:case ExprKind::LoopIndex: {
                auto it=std::find(bindings.rbegin(),bindings.rend(),n.binding);require(it!=bindings.rend(),"unbound loop in repr");
                r=(n.kind==ExprKind::Accumulator?"a":"i")+std::to_string(it-bindings.rbegin());break;
            }
            }
            require(r.size()<100000,"serialized program budget");return r;
        };return walk(root,0);
    }
    int32_t replace_subtree(int32_t root,int32_t target,int32_t replacement) {
        require(at(target).shape==at(replacement).shape,"replacement changes type");
        std::unordered_map<int32_t,int32_t> memo;
        std::function<int32_t(int32_t,size_t)> walk=[&](int32_t id,size_t depth) {
            require(depth<256,"replacement depth");if(id==target)return replacement;
            auto it=memo.find(id);if(it!=memo.end())return it->second;
            auto n=at(id);
            for(auto p:{&n.left,&n.right,&n.guard_left,&n.guard_right})if(*p>=0)*p=walk(*p,depth+1);
            for(auto& e:n.entries)e=walk(e,depth+1);
            auto result=make(n);memo[id]=result;return result;
        };return walk(root,0);
    }
};
