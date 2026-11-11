static std::string json_string(std::string_view s) {
    std::string r="\"";
    for(unsigned char c:s) {
        if(c=='"'||c=='\\'){r+='\\';r+=char(c);}
        else if(c=='\n')r+="\\n";
        else if(c=='\r')r+="\\r";
        else if(c=='\t')r+="\\t";
        else {require(c>=32,"control byte in JSON");r+=char(c);}
    }
    return r+'"';
}
static std::string lean_term(const ExpressionGraph& graph,int32_t root) {
    size_t fuel=30000;std::map<uint32_t,size_t> bindings;
    std::function<std::string(int32_t,size_t)> emit=[&](int32_t id,size_t depth)->std::string {
        require(fuel>0&&depth<128,"Lean translation budget");--fuel;const auto& n=graph.at(id);
        auto sub=[&](int32_t child){return emit(child,depth+1);};std::string r;
        switch(n.kind) {
        case ExprKind::Constant:r="(.value (("+n.value.get_num().get_str()+") / "+n.value.get_den().get_str()+" : ℚ))";break;
        case ExprKind::Variable:r="(.value (_x "+std::to_string(n.index)+"))";break;
        case ExprKind::Add:r="(.add "+sub(n.left)+" "+sub(n.right)+")";break;
        case ExprKind::Multiply:r="(.mul "+sub(n.left)+" "+sub(n.right)+")";break;
        case ExprKind::Negate:r="(.neg "+sub(n.left)+")";break;
        case ExprKind::Power:r="(.pow "+sub(n.left)+" "+std::to_string(n.index)+")";break;
        case ExprKind::IfLess:r="(.ifLess "+sub(n.guard_left)+" "+sub(n.guard_right)+" "+sub(n.left)+" "+sub(n.right)+")";break;
        case ExprKind::Tensor:
            r="(.tensor ![";for(size_t i=0;i<n.entries.size();++i)r+=(i?", ":"")+sub(n.entries[i]);r+="])";break;
        case ExprKind::BoundedLoop: {
            auto initial=sub(n.left);auto tag=std::to_string(bindings.size());bindings[n.binding]=bindings.size();auto body=sub(n.right);bindings.erase(n.binding);
            r="(.loop "+std::to_string(n.index)+" "+initial+" (fun _j"+tag+" _s"+tag+" => "+body+"))";break;
        }
        case ExprKind::Accumulator:case ExprKind::LoopIndex:
            require(bindings.count(n.binding),"unbound local in Lean translation");
            r=n.kind==ExprKind::Accumulator?"(.value _s"+std::to_string(bindings.at(n.binding))+")":
                "(.value (_j"+std::to_string(bindings.at(n.binding))+" : ℚ))";break;
        }
        require(r.size()<1024*1024,"Lean output budget");return r;
    };return emit(root,0);
}
static void ensure_directory(const std::string& path) {
    require(!path.empty()&&path.size()<PATH_MAX,"invalid output directory");
    std::string part;
    for(size_t i=0;i<=path.size();++i) {
        if(i<path.size())part+=path[i];
        if((i==path.size()||path[i]=='/')&&!part.empty()) {
            require(::mkdir(part.c_str(),0700)==0||errno==EEXIST,"cannot create output directory");
        }
    }
    struct stat st{};require(::stat(path.c_str(),&st)==0&&S_ISDIR(st.st_mode),"output is not a directory");
}
// An unsimplified scalar projection for each output cell. `change` in the
// generated proof requires Lean's kernel to confirm definitional equality with
// Term.denote; this translation is never accepted merely on the C++ checker's word.
static std::vector<std::string> lean_projections(const ExpressionGraph& graph,int32_t root) {
    using Cells=std::vector<std::string>;
    std::map<uint32_t,std::pair<Cells,uint32_t>> bindings;size_t fuel=50000;
    std::function<Cells(int32_t,size_t)> emit=[&](int32_t id,size_t depth)->Cells {
        require(fuel>0&&depth<128,"Lean projection budget");--fuel;const auto& n=graph.at(id);Cells r;
        switch(n.kind) {
        case ExprKind::Constant:return {"(("+n.value.get_num().get_str()+") / "+n.value.get_den().get_str()+" : ℚ)"};
        case ExprKind::Variable:return {"(x "+std::to_string(n.index)+")"};
        case ExprKind::Accumulator:return bindings.at(n.binding).first;
        case ExprKind::LoopIndex:return {"("+std::to_string(bindings.at(n.binding).second)+" : ℚ)"};
        case ExprKind::Tensor:for(auto e:n.entries)r.push_back(emit(e,depth+1).at(0));break;
        case ExprKind::BoundedLoop:
            r=emit(n.left,depth+1);
            for(uint32_t i=0;i<n.index;++i){bindings[n.binding]={r,i};r=emit(n.right,depth+1);}
            bindings.erase(n.binding);break;
        case ExprKind::IfLess: {
            auto a=emit(n.guard_left,depth+1).at(0),b=emit(n.guard_right,depth+1).at(0);
            auto yes=emit(n.left,depth+1),no=emit(n.right,depth+1);
            for(size_t i=0;i<yes.size();++i)r.push_back("(if "+a+" < "+b+" then "+yes[i]+" else "+no[i]+")");
            break;
        }
        default: {
            auto a=emit(n.left,depth+1);Cells b;if(n.right>=0)b=emit(n.right,depth+1);
            for(size_t i=0;i<a.size();++i) {
                if(n.kind==ExprKind::Add)r.push_back("("+a[i]+" + "+b[i]+")");
                else if(n.kind==ExprKind::Multiply)r.push_back("("+a[i]+" * "+b[i]+")");
                else if(n.kind==ExprKind::Negate)r.push_back("(-"+a[i]+")");
                else r.push_back("("+a[i]+" ^ "+std::to_string(n.index)+")");
            }
        }
        }
        size_t size=0;for(const auto& s:r)size+=s.size();require(size<1024*1024,"unrolled Lean projection budget");return r;
    };return emit(root,0);
}
static std::string export_lean(TrustedKernel& kernel,ExpressionGraph& graph,int32_t before,int32_t after,
    size_t vars,const ProofCertificate& claimed,const std::string& directory) {
    // Never trust a bool or a caller-provided digest as proof evidence.
    auto checked=certify_graph_improvement(kernel,graph,before,after,vars);
    require(checked.statement_hash==claimed.statement_hash&&checked.proof_hash==claimed.proof_hash&&
        checked.evidence==claimed.evidence,"certificate/AST mismatch at export");
    ensure_directory(directory);auto tag=checked.statement_hash;
    auto path=directory+"/Rewrite_"+tag+".lean";
    std::string type="ℚ";const auto& shape=graph.at(before).shape;
    if(!shape.empty()) {
        type="Fin "+std::to_string(ExpressionGraph::elements(shape))+" → ℚ";
    }
    std::string text="module\npublic import LeanML.Programs.VerifiedRewrite\n@[expose] public section\n";
    text+="noncomputable section\nopen LeanML.Programs\nset_option maxRecDepth 4096\nset_option maxHeartbeats 2000000\n-- Generated fallback branches may be unused for a particular expression.\nset_option linter.unusedTactic false\nset_option linter.unreachableTactic false\nset_option linter.unusedSimpArgs false\n";
    text+="namespace LeanML.Generated.Cert_"+tag+"\n";
    text+="-- BLAKE3 statement: "+tag+"\n-- BLAKE3 C++ proof evidence: "+checked.proof_hash+"\n";
    text+="-- C++ equivalence has been checked; this theorem still requires the Lean kernel.\n";
    if(!shape.empty()) {
        text+="def outputShape : List ℕ := [";
        for(size_t i=0;i<shape.size();++i)text+=(i?", ":"")+std::to_string(shape[i]);
        text+="]\n";
        text+="theorem shape_size : outputShape.prod = "+std::to_string(ExpressionGraph::elements(shape))+" := by decide\n";
    }
    text+="def before (_x : Fin "+std::to_string(vars)+" → ℚ) : Term ("+type+") := "+lean_term(graph,before)+"\n";
    text+="def after (_x : Fin "+std::to_string(vars)+" → ℚ) : Term ("+type+") := "+lean_term(graph,after)+"\n";
    text+="theorem certified : VerifiedRewrite before after where\n  equivalent x := by\n";
    auto lhs=lean_projections(graph,before),rhs=lean_projections(graph,after);
    if(!shape.empty())text+="    funext i\n    fin_cases i\n";
    for(size_t i=0;i<lhs.size();++i) {
        auto indent=shape.empty()?"    ":"    · ";
        text+=indent+std::string("simp only [before, after, Term.denote, boundedLoop, ite_apply, Pi.add_apply, Pi.mul_apply, Pi.neg_apply, Pi.pow_apply]\n");
        auto next=shape.empty()?"    ":"      ";
        text+=next+std::string("all_goals try dsimp +instances only [Term.denote]\n");
        text+=next+std::string("all_goals try rw [ite_apply]\n");
        text+=next+std::string("all_goals change ")+lhs[i]+" = "+rhs[i]+"\n";
        text+=next+std::string("all_goals first | (ring; done) | (split_ifs; all_goals norm_num at *; all_goals ring)\n");
    }
    text+="  cheaper x := by\n    change "+std::to_string(checked.new_static_cost)+" < "+std::to_string(checked.old_static_cost)+"\n    decide\n";
    text+="end LeanML.Generated.Cert_"+tag+"\n";
    require(atomic_write(path,text),"cannot atomically write Lean certificate");
    std::string metadata="{\n  \"schema\": \"godel-leanml-rewrite-v2\",\n  \"statement_blake3\": "+json_string(tag)+
        ",\n  \"proof_blake3\": "+json_string(checked.proof_hash)+",\n  \"evidence\": "+json_string(checked.evidence)+
        ",\n  \"cpp_verified\": true,\n  \"lean_status\": \"pending-kernel\",\n  \"lean_file\": "+json_string(path)+"\n}\n";
    require(atomic_write(path+".json",metadata),"cannot write certificate metadata");return path;
}
static std::string export_ast_certificate(const ProofCertificate& cert,const std::string& directory) {
    std::string_view rest=cert.evidence,prefix,vars,before,after,oldcost,newcost,ring_hash;
    require(split_once(rest,'|',prefix,rest)&&(prefix=="ASTv1"||prefix=="ASTv2"),"unsupported export certificate");
    require(split_once(rest,'|',vars,rest)&&split_once(rest,'|',before,rest)&&split_once(rest,'|',after,rest)&&
        split_once(rest,'|',oldcost,rest)&&split_once(rest,'|',newcost,ring_hash),"invalid export evidence");
    size_t n=parse_u32(vars);ExpressionGraph graph;TrustedKernel kernel;
    auto a=AlgebraParser(graph,before,n).parse(),b=AlgebraParser(graph,after,n).parse();
    return export_lean(kernel,graph,a,b,n,cert,directory);
}
