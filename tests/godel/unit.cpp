#define main godel_cli_main
#include "../../tools/godel/godel.cpp"
#undef main

int main() {
    using namespace godel;
    TestRunner t;ExpressionGraph g;TrustedKernel kernel;
    auto parse=[&](const std::string& s){return AlgebraParser(g,s,2).parse();};
    auto equal=[&](const std::string& a,const std::string& b) {
        return g.symbolic(parse(a),2).canonical()==g.symbolic(parse(b),2).canonical();
    };
    t.check(equal("fold(3,x0,a0+i0)","x0+3"),"loop carries state and zero-based index");
    t.check(equal("fold(0,x0,a0+999)","x0"),"zero iterations");
    t.check(equal("fold(2,x0,fold(3,a0,a0+i0+i1))","x0+9"),"nested lexical loop indices");
    t.check(equal("iflt(x0,0,x0+0,x0)","x0"),"equal conditional branches");
    t.check(!equal("iflt(x0,1000000,x0,0)","x0"),"finite sampling cannot certify different branch");
    t.check(equal("fold(2,tensor([2],[x0,x1]),a0+tensor([2],[1,i0]))",
                  "tensor([2],[x0+2,x1+1])"),"tensor loop state");
    t.check(equal("matmul(tensor([1,2],[x0,x1]),tensor([2,1],[1,2]))",
                  "tensor([1,1],[x0+2*x1])"),"row-major matrix multiplication");
    for(const auto& bad:{"a0", "fold(65,0,a0)", "fold(2,0,tensor([1],[a0]))",
        "tensor([2],[1])", "tensor([0],[1])", "tensor([2],[1,2])+1",
        "iflt(0,1,0,tensor([1],[0]))", "1/0", "x2", "fold(2,0,i1)",
        "matmul(tensor([1,2],[1,2]),tensor([1,2],[1,2]))"})
        t.rejects([&]{parse(bad);},std::string("reject invalid DSL: ")+bad);
    t.rejects([&]{parse(std::string(200,'-')+"1");},"parser stack budget");
    auto loop=parse("fold(2,x0,a0+0)");
    auto cert=certify_graph_improvement(kernel,g,loop,parse("x0"),2);
    t.check(cert.verified&&revalidate_record(record_from_certificate(cert,"ast-improvement",0),kernel),"v2 certificate replay");
    auto forged=cert;forged.proof_hash=std::string(64,'0');
    t.rejects([&]{export_lean(kernel,g,loop,parse("x0"),2,forged,"/tmp/godel-forged");},"export rechecks certificate binding");
    auto negative=g.constant(Q(-1,2));auto roundtrip=parse(g.repr(negative));
    t.check(g.at(roundtrip).kind==ExprKind::Constant&&g.static_cost(roundtrip)==1,"negative constants preserve AST cost on replay");
    auto guard=parse("iflt(x0,x1,fold(2,x0,a0+i0),x1)");g.protect(guard);g.collect();
    t.check(g.symbolic(guard,2).cells.size()==1,"GC follows guards, bodies and loop captures");
    GraphNeuralNetwork net;t.check(finite_float(net.encode(g,guard).value),"GNN traverses extended graph safely");
    return t.result();
}
