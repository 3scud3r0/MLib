class AlgebraParser {
    ExpressionGraph& graph_;
    std::string_view input_;
    size_t offset_=0,variables_=0,operations_=0,depth_=0;
    std::vector<std::pair<int32_t,int32_t>> bindings_;
    struct Depth {
        size_t& d;explicit Depth(size_t& v):d(v){require(++d<128,"parser nesting budget");}
        ~Depth(){--d;}
    };
    void space(){while(offset_<input_.size()&&(input_[offset_]==' '||input_[offset_]=='\t'))++offset_;}
    bool accept(char c){space();if(offset_<input_.size()&&input_[offset_]==c){++offset_;return true;}return false;}
    void expect(char c){require(accept(c),std::string("expected ")+c);}
    bool keyword(std::string_view word) {
        space();if(input_.substr(offset_,word.size())!=word)return false;
        offset_+=word.size();return true;
    }
    uint32_t natural() {
        space();size_t start=offset_;
        while(offset_<input_.size()&&std::isdigit((unsigned char)input_[offset_]))++offset_;
        require(offset_>start,"expected natural number");return parse_u32(input_.substr(start,offset_-start));
    }
    int32_t atom() {
        Depth guard(depth_);require(++operations_<20000,"parser operation budget");
        if(accept('(')){auto r=expression();expect(')');return r;}
        if(keyword("q")) {
            expect('(');space();size_t start=offset_;
            if(offset_<input_.size()&&input_[offset_]=='-')++offset_;
            size_t digits=offset_;
            while(offset_<input_.size()&&std::isdigit((unsigned char)input_[offset_]))++offset_;
            require(offset_>digits&&offset_-digits<=512,"invalid rational numerator");
            std::string value(input_.substr(start,offset_-start));
            if(accept('/')) {
                space();size_t ds=offset_;
                while(offset_<input_.size()&&std::isdigit((unsigned char)input_[offset_]))++offset_;
                require(offset_>ds&&offset_-ds<=512,"invalid rational denominator");
                auto den=std::string(input_.substr(ds,offset_-ds));require(Z(den)!=0,"zero denominator");value+="/"+den;
            }
            expect(')');return graph_.constant(Q(value));
        }
        if(keyword("iflt")) {
            expect('(');auto a=expression();expect(',');auto b=expression();expect(',');
            auto yes=expression();expect(',');auto no=expression();expect(')');return graph_.if_less(a,b,yes,no);
        }
        if(keyword("tensor")) {
            expect('(');expect('[');std::vector<uint32_t> shape;
            do{shape.push_back(natural());require(shape.size()<=4,"tensor rank budget");}while(accept(','));
            expect(']');expect(',');expect('[');std::vector<int32_t> cells;
            do{cells.push_back(expression());require(cells.size()<=1024,"tensor cell budget");}while(accept(','));
            expect(']');expect(')');return graph_.tensor(std::move(shape),std::move(cells));
        }
        if(keyword("matmul")) {
            expect('(');auto a=expression();expect(',');auto b=expression();expect(')');return graph_.matrix_multiply(a,b);
        }
        if(keyword("fold")) {
            expect('(');auto count=natural();expect(',');auto initial=expression();expect(',');
            auto r=graph_.bounded_loop(count,initial,[&](int32_t a,int32_t i) {
                bindings_.push_back({a,i});auto body=expression();bindings_.pop_back();return body;
            });
            expect(')');return r;
        }
        if(accept('x')){auto i=natural();require(i<variables_,"input variable out of range");return graph_.variable(i);}
        space();if(offset_<input_.size()&&(input_[offset_]=='a'||input_[offset_]=='i')) {
            bool acc=input_[offset_++]=='a';auto depth=natural();require(depth<bindings_.size(),"unbound loop variable");
            auto b=bindings_[bindings_.size()-1-depth];return acc?b.first:b.second;
        }
        space();size_t start=offset_;
        while(offset_<input_.size()&&std::isdigit((unsigned char)input_[offset_]))++offset_;
        require(offset_>start&&offset_-start<=512,"expected bounded integer");
        std::string number(input_.substr(start,offset_-start));
        if(accept('/')) {
            space();size_t ds=offset_;
            while(offset_<input_.size()&&std::isdigit((unsigned char)input_[offset_]))++offset_;
            require(offset_>ds&&offset_-ds<=512,"expected bounded denominator");
            auto den=std::string(input_.substr(ds,offset_-ds));require(Z(den)!=0,"zero denominator");number+="/"+den;
        }
        Q q(number);q.canonicalize();return graph_.constant(q);
    }
    int32_t unary(){Depth guard(depth_);if(accept('-'))return graph_.negate(unary());return atom();}
    int32_t power(){auto r=unary();if(accept('^'))r=graph_.power(r,natural());return r;}
    int32_t product(){auto r=power();while(accept('*'))r=graph_.multiply(r,power());return r;}
    int32_t expression(){auto r=product();for(;;) {
        if(accept('+'))r=graph_.add(r,product());
        else if(accept('-'))r=graph_.add(r,graph_.negate(product()));else return r;
    }}
public:
    AlgebraParser(ExpressionGraph& g,std::string_view text,size_t vars):graph_(g),input_(text),variables_(vars) {
        require(text.size()<100000&&vars>0&&vars<=16,"program input budget");
    }
    int32_t parse(){auto r=expression();space();require(offset_==input_.size(),"trailing program input");return r;}
};
