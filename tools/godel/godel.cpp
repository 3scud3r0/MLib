/*
 * GODEL RESEARCH ENGINE — single-translation-unit C++17 implementation.
 *
 * Build (Linux):
 *   g++ -std=c++17 -O2 -Wall -Wextra godel.cpp -lgmpxx -lgmp -ldl -o godel
 *   ./godel --self-test
 *   ./godel --discover
 *   ./godel --evolve 100
 *   ./godel --inspect-self ./godel.cpp
 *   ./godel --hot-swap
 *
 * This is a research implementation, not a solution to incompleteness,
 * the halting problem, general theorem discovery, or verified native C++.
 * Certified statements refer to precise symbolic models and are checked
 * independently of the neural planner and of performance observations.
 * Only proof-checking rules in TrustedKernel are trusted. Dynamic plugins
 * are optional, local, explicitly opted-in, and NOT formally certified.
 *
 * GPL-compatible permissive software. No external code included.
 */
#define _GNU_SOURCE 1
#include <gmpxx.h>
#include <algorithm>
#include <array>
#include <atomic>
#include <cassert>
#include <cctype>
#include <cerrno>
#include <chrono>
#include <cmath>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <deque>
#include <dlfcn.h>
#include <fcntl.h>
#include <functional>
#include <iomanip>
#include <iostream>
#include <limits>
#include <map>
#include <memory>
#include <mutex>
#include <numeric>
#include <optional>
#include <queue>
#include <random>
#include <set>
#include <sstream>
#include <stdexcept>
#include <string>
#include <string_view>
#include <sys/file.h>
#include <sys/mman.h>
#include <sys/resource.h>
#include <sys/stat.h>
#include <sys/types.h>
#include <sys/wait.h>
#include <unistd.h>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>
#include <signal.h>
#include <time.h>
#include <dirent.h>
#include <poll.h>

namespace godel {
using Q = mpq_class;
using Z = mpz_class;
using Clock = std::chrono::steady_clock;
constexpr uint32_t kSchema = 3;
constexpr size_t kMaxAstNodes = 200000;
constexpr size_t kMaxTypeNodes = 100000;
constexpr size_t kMaxPolynomialTerms = 200000;
constexpr size_t kMaxProofSize = 30000;
constexpr size_t kMaxSearchIterations = 50000;
constexpr size_t kMaxFileBytes = 64 * 1024 * 1024;

static void require(bool valid, const std::string& message) {
    if (!valid) throw std::runtime_error(message);
}
static Q rational(int64_t n, int64_t d=1) {
    require(d != 0, "zero denominator");
    Q result(mpz_class(static_cast<long>(n)), mpz_class(static_cast<long>(d)));
    result.canonicalize(); return result;
}
[[maybe_unused]] static std::string stringify(const Q& q) { return q.get_str(); }
[[maybe_unused]] static std::string stringify(const Z& q) { return q.get_str(); }
static bool finite_float(double x) { return std::isfinite(x); }
static uint64_t splitmix64(uint64_t& state) {
    uint64_t x = (state += 0x9e3779b97f4a7c15ULL);
    x = (x ^ (x >> 30)) * 0xbf58476d1ce4e5b9ULL;
    x = (x ^ (x >> 27)) * 0x94d049bb133111ebULL;
    return x ^ (x >> 31);
}
static double unit_random(uint64_t& s) { return (splitmix64(s) >> 11) * (1.0 / 9007199254740992.0); }
static bool write_all(int fd, const void* buffer, size_t size) {
    const uint8_t* p = static_cast<const uint8_t*>(buffer);
    while (size) { ssize_t n = ::write(fd,p,size); if (n < 0 && errno == EINTR) continue; if (n <= 0) return false; p += n; size -= (size_t)n; }
    return true;
}
static bool read_all(int fd, void* buffer, size_t size) {
    uint8_t* p = static_cast<uint8_t*>(buffer);
    while (size) { ssize_t n = ::read(fd,p,size); if (n < 0 && errno == EINTR) continue; if (n <= 0) return false; p += n; size -= (size_t)n; }
    return true;
}
static std::string read_file(const std::string& path, size_t max_bytes = kMaxFileBytes) {
    int fd = ::open(path.c_str(),O_RDONLY|O_CLOEXEC);
    if(fd < 0) throw std::runtime_error("cannot read file: " + path);
    struct stat st{};
    if(::fstat(fd,&st) < 0 || st.st_size < 0 || static_cast<uint64_t>(st.st_size)>max_bytes) { ::close(fd); throw std::runtime_error("file size invalid"); }
    std::string result((size_t)st.st_size,'\0');
    bool ok=read_all(fd,result.data(),result.size()); ::close(fd);
    require(ok,"short read"); return result;
}
static bool atomic_write(const std::string& path, std::string_view payload) {
    std::string pattern=path+".tmp.XXXXXX";
    std::vector<char> buffer(pattern.begin(),pattern.end()); buffer.push_back(0);
    int fd=::mkstemp(buffer.data()); if(fd<0) return false;
    bool ok=write_all(fd,payload.data(),payload.size()) && ::fsync(fd)==0;
    if(::close(fd)!=0) ok=false;
    if(ok) ok=(::rename(buffer.data(),path.c_str())==0);
    if(!ok) ::unlink(buffer.data());
    return ok;
}
static std::string hex_bytes(const uint8_t* p,size_t n) {
    static constexpr char h[]="0123456789abcdef"; std::string s; s.resize(2*n);
    for(size_t i=0;i<n;++i) { s[2*i]=h[p[i]>>4]; s[2*i+1]=h[p[i]&15]; }
    return s;
}

// ======================================================================
// BLAKE3 — unkeyed, portable, tree-based hash, 256-bit digest.
// Compression is derived directly from the public BLAKE3 specification.
// No SIMD, no external shared library, no dynamic code loading required.
// ======================================================================
namespace blake3 {
constexpr uint32_t IV[8]={0x6A09E667u,0xBB67AE85u,0x3C6EF372u,0xA54FF53Au,
                          0x510E527Fu,0x9B05688Cu,0x1F83D9ABu,0x5BE0CD19u};
constexpr uint8_t MSG_PERM[16]={2,6,3,10,7,0,4,13,1,11,12,5,9,14,15,8};
constexpr uint32_t CHUNK_START=1,CHUNK_END=2,PARENT=4,ROOT=8;
static uint32_t rotr(uint32_t x, unsigned n) {return (x>>n)|(x<<(32-n));}
static uint32_t load32(const uint8_t* p){return uint32_t(p[0])|(uint32_t(p[1])<<8)|(uint32_t(p[2])<<16)|(uint32_t(p[3])<<24);}
static void store32(uint8_t* p,uint32_t x){for(int i=0;i<4;++i)p[i]=uint8_t(x>>(8*i));}
static void G(uint32_t v[16],int a,int b,int c,int d,uint32_t mx,uint32_t my){
    v[a]+=v[b]+mx;v[d]=rotr(v[d]^v[a],16);
    v[c]+=v[d];v[b]=rotr(v[b]^v[c],12);
    v[a]+=v[b]+my;v[d]=rotr(v[d]^v[a],8);
    v[c]+=v[d];v[b]=rotr(v[b]^v[c],7);
}
static void round(uint32_t v[16],const uint32_t m[16]){
    G(v,0,4,8,12,m[0],m[1]);G(v,1,5,9,13,m[2],m[3]);
    G(v,2,6,10,14,m[4],m[5]);G(v,3,7,11,15,m[6],m[7]);
    G(v,0,5,10,15,m[8],m[9]);G(v,1,6,11,12,m[10],m[11]);
    G(v,2,7,8,13,m[12],m[13]);G(v,3,4,9,14,m[14],m[15]);
}
static std::array<uint32_t,16> compress(const uint32_t cv[8],const uint32_t block[16],
                                        uint64_t counter,uint32_t len,uint32_t flags){
    uint32_t v[16]{};
    for(int i=0;i<8;++i)v[i]=cv[i];
    for(int i=0;i<4;++i)v[8+i]=IV[i];
    v[12]=uint32_t(counter);v[13]=uint32_t(counter>>32);
    v[14]=len;v[15]=flags;
    uint32_t m[16];std::copy(block,block+16,m);
    for(int r=0;r<7;++r){
        round(v,m);
        if(r<6){uint32_t p[16];for(int i=0;i<16;++i)p[i]=m[MSG_PERM[i]];std::copy(p,p+16,m);}
    }
    std::array<uint32_t,16> out{};
    for(int i=0;i<8;++i){out[i]=v[i]^v[i+8];out[i+8]=v[i+8]^cv[i];}
    return out;
}
struct Output {
    std::array<uint32_t,8> cv{};
    std::array<uint32_t,16> block{};
    uint64_t counter=0;
    uint32_t len=0,flags=0;
    std::array<uint32_t,8> chaining() const {
        auto words=compress(cv.data(),block.data(),counter,len,flags);
        std::array<uint32_t,8> next{};std::copy(words.begin(),words.begin()+8,next.begin());return next;
    }
    std::array<uint8_t,32> root() const {
        auto words=compress(cv.data(),block.data(),0,len,flags|ROOT);
        std::array<uint8_t,32> digest{};
        for(int i=0;i<8;++i)store32(digest.data()+4*i,words[i]);
        return digest;
    }
};
static Output chunk_output(const uint8_t* data,size_t length,uint64_t counter){
    require(length<=1024,"BLAKE3 chunk oversized");
    std::array<uint32_t,8> cv{};std::copy(IV,IV+8,cv.begin());
    size_t processed=0;bool first=true;
    while(length-processed>64){
        uint32_t block[16];for(int j=0;j<16;++j)block[j]=load32(data+processed+j*4);
        auto x=compress(cv.data(),block,counter,64,first?CHUNK_START:0);
        std::copy(x.begin(),x.begin()+8,cv.begin());processed+=64;first=false;
    }
    uint8_t last[64]{};size_t tail=length-processed;
    if(tail)std::memcpy(last,data+processed,tail);
    Output o;o.cv=cv;o.counter=counter;o.len=(uint32_t)tail;
    o.flags=(first?CHUNK_START:0)|CHUNK_END;
    for(int i=0;i<16;++i)o.block[i]=load32(last+i*4);
    return o;
}
static Output parent_output(const std::array<uint32_t,8>& left,
                            const std::array<uint32_t,8>& right){
    Output o;std::copy(IV,IV+8,o.cv.begin());
    std::copy(left.begin(),left.end(),o.block.begin());
    std::copy(right.begin(),right.end(),o.block.begin()+8);
    o.len=64;o.flags=PARENT;return o;
}
static std::array<uint8_t,32> digest(std::string_view input){
    std::vector<std::array<uint32_t,8>> stack;
    size_t chunk_count=std::max<size_t>(1,(input.size()+1023)/1024);
    for(size_t chunk=0;chunk+1<chunk_count;++chunk){
        Output o=chunk_output(reinterpret_cast<const uint8_t*>(input.data())+chunk*1024,1024,chunk);
        auto cv=o.chaining();size_t total=chunk+1;
        while((total&1)==0){require(!stack.empty(),"BLAKE3 tree invariant");cv=parent_output(stack.back(),cv).chaining();stack.pop_back();total>>=1;}
        stack.push_back(cv);
    }
    size_t offset=(chunk_count-1)*1024;
    Output final=chunk_output(reinterpret_cast<const uint8_t*>(input.data())+offset,
                              input.size()-offset,chunk_count-1);
    while(!stack.empty()){
        final=parent_output(stack.back(),final.chaining());stack.pop_back();
    }
    return final.root();
}
static std::string hex(std::string_view input){auto h=digest(input);return hex_bytes(h.data(),h.size());}
} // namespace blake3

// ======================================================================
// EXACT MULTIVARIATE ALGEBRA OVER Q (GMP-backed)
// Monomials use an exponent vector and graded lexicographic ordering.
// All normalization is exact, so a zero coefficient means mathematical zero.
// ======================================================================
struct Monomial {
    std::vector<uint16_t> powers;
    bool operator==(const Monomial& o) const{return powers==o.powers;}
    bool operator<(const Monomial& o) const{
        uint32_t a=std::accumulate(powers.begin(),powers.end(),uint32_t(0));
        uint32_t b=std::accumulate(o.powers.begin(),o.powers.end(),uint32_t(0));
        if(a!=b)return a<b;
        return powers<o.powers;
    }
};
struct Polynomial {
    size_t vars=0;
    std::map<Monomial,Q> terms;
    explicit Polynomial(size_t n=0):vars(n){require(n<=16,"too many variables");}
    static Polynomial constant(size_t n,const Q& c){
        Polynomial p(n);if(c!=0)p.terms[Monomial{std::vector<uint16_t>(n,0)}]=c;return p;
    }
    static Polynomial variable(size_t n,size_t index){
        require(index<n,"bad variable index");
        Polynomial p(n);Monomial m{std::vector<uint16_t>(n,0)};m.powers[index]=1;p.terms[m]=1;return p;
    }
    void add_monomial(const Monomial& m,const Q& c){
        require(m.powers.size()==vars,"monomial arity mismatch");
        if(c==0)return;
        Q& cell=terms[m];cell+=c;
        if(cell==0)terms.erase(m);
        require(terms.size()<=kMaxPolynomialTerms,"polynomial size limit");
    }
    bool is_zero() const{return terms.empty();}
    bool is_constant() const{
        if(terms.empty())return true;
        if(terms.size()!=1)return false;
        for(uint16_t d:terms.begin()->first.powers)if(d!=0)return false;
        return true;
    }
    Q constant_value() const{require(is_constant(),"not constant");return terms.empty()?Q(0):terms.begin()->second;}
    size_t term_count()const{return terms.size();}
    int degree() const {
        int m=-1;
        for(auto& e:terms){int sum=0;for(auto d:e.first.powers)sum+=d;m=std::max(m,sum);}
        return m;
    }
    std::string canonical() const {
        std::string s="Q["+std::to_string(vars)+"]:";
        for(const auto& kv:terms){
            s+='('+kv.second.get_str();
            for(auto d:kv.first.powers){s+=',';s+=std::to_string(d);}s+=')';
        }
        return s;
    }
    bool operator==(const Polynomial& b)const{return vars==b.vars&&terms==b.terms;}
    bool operator!=(const Polynomial& b)const{return !(*this==b);}
    Polynomial operator-()const{Polynomial n(vars);for(auto& e:terms)n.terms.emplace(e.first,-e.second);return n;}
    Polynomial operator+(const Polynomial& b)const{
        require(vars==b.vars,"add arity");Polynomial result=*this;
        for(auto& e:b.terms)result.add_monomial(e.first,e.second);
        return result;
    }
    Polynomial operator-(const Polynomial& b)const{return *this+(-b);}
    Polynomial operator*(const Polynomial& b)const{
        require(vars==b.vars,"mul arity");Polynomial r(vars);
        if(terms.empty()||b.terms.empty())return r;
        require(terms.size()<=kMaxPolynomialTerms/b.terms.size(),"mul expansion limit");
        for(auto& x:terms)for(auto& y:b.terms){
            Monomial m{x.first.powers};
            for(size_t i=0;i<vars;++i){
                uint32_t d=uint32_t(m.powers[i])+y.first.powers[i];
                require(d<=65535,"exponent overflow");m.powers[i]=(uint16_t)d;
            }
            r.add_monomial(m,x.second*y.second);
        }
        return r;
    }
    Polynomial operator*(const Q& c)const{
        Polynomial r(vars);if(c==0)return r;
        for(auto& e:terms)r.terms.emplace(e.first,e.second*c);
        return r;
    }
    Polynomial pow(unsigned e) const{
        require(e<=512,"power too large");Polynomial result=constant(vars,1),base=*this;
        while(e){if(e&1)result=result*base;e>>=1;if(e)base=base*base;}
        return result;
    }
    Polynomial derivative(size_t var)const{
        require(var<vars,"derivative variable");Polynomial result(vars);
        for(auto& e:terms){
            uint16_t d=e.first.powers[var];if(!d)continue;
            Monomial m=e.first;m.powers[var]--;
            result.add_monomial(m,e.second*Q(d));
        }
        return result;
    }
    Polynomial substitute(size_t var,const Polynomial& expression)const{
        require(var<vars&&vars==expression.vars,"substitute arity");
        Polynomial result(vars);
        for(auto& e:terms){
            Polynomial product=constant(vars,e.second);
            for(size_t j=0;j<vars;++j){
                unsigned exponent=e.first.powers[j];if(exponent==0)continue;
                product=product*(j==var?expression:variable(vars,j)).pow(exponent);
            }
            result=result+product;
        }
        return result;
    }
    Q evaluate(const std::vector<Q>& x)const{
        require(x.size()==vars,"evaluate arity");Q result=0;
        for(auto& e:terms){
            Q term=e.second;
            for(size_t j=0;j<vars;++j){
                uint16_t exponent=e.first.powers[j];
                Q base=x[j];
                while(exponent){if(exponent&1)term*=base;exponent>>=1;if(exponent)base*=base;}
            }
            result+=term;
        }
        return result;
    }
};
[[maybe_unused]] static Polynomial operator*(const Q& c,const Polynomial& p){return p*c;}
static Polynomial poisson(const Polynomial& a,const Polynomial& b) {
    require(a.vars==b.vars&&a.vars%2==0,"symplectic coordinates must come in pairs");
    Polynomial result(a.vars);size_t n=a.vars/2;
    for(size_t i=0;i<n;++i)
        result=result+a.derivative(i)*b.derivative(n+i)-a.derivative(n+i)*b.derivative(i);
    return result;
}
static std::vector<Monomial> enumerate_monomials(size_t variables,unsigned max_degree) {
    require(variables<=8&&max_degree<=10,"monomial basis too large");
    std::vector<Monomial> all;std::vector<uint16_t> powers(variables,0);
    std::function<void(size_t,unsigned)> visit=[&](size_t pos,unsigned used){
        if(pos==variables){all.push_back(Monomial{powers});return;}
        for(unsigned e=0;e<=max_degree-used;++e){powers[pos]=(uint16_t)e;visit(pos+1,used+e);}
    };visit(0,0);
    std::sort(all.begin(),all.end());
    require(all.size()<50000,"monomial basis limit");return all;
}
static Polynomial monomial_polynomial(size_t vars,const Monomial& mon){
    Polynomial p(vars);p.terms[mon]=1;return p;
}
static std::string polynomial_nice(const Polynomial& p){
    if(p.is_zero())return "0";
    std::ostringstream out;bool first=true;
    for(auto& kv:p.terms){
        if(!first)out<<" + ";
        first=false;
        out<<kv.second.get_str();
        for(size_t i=0;i<p.vars;++i)if(kv.first.powers[i]){
            out<<"*"<<(i<p.vars/2?"q":"p")<<(i%(p.vars/2)+1);
            if(kv.first.powers[i]>1)out<<"^"<<kv.first.powers[i];
        }
    }
    return out.str();
}

// Exact row reduction, RREF, kernel vectors in Q^columns.
struct RREF {
    std::vector<std::vector<Q>> matrix;
    std::vector<size_t> pivot_columns;
    size_t columns=0;
    size_t rank()const{return pivot_columns.size();}
    std::vector<std::vector<Q>> nullspace() const{
        std::set<size_t> piv(pivot_columns.begin(),pivot_columns.end());
        std::vector<std::vector<Q>> result;
        for(size_t free=0;free<columns;++free)if(!piv.count(free)){
            std::vector<Q> v(columns,Q(0));v[free]=1;
            for(size_t i=0;i<pivot_columns.size();++i)v[pivot_columns[i]]=-matrix[i][free];
            result.push_back(std::move(v));
        }
        return result;
    }
};
static RREF row_reduce(std::vector<std::vector<Q>> m,size_t cols){
    for(auto& r:m)require(r.size()==cols,"RREF matrix not rectangular");
    require(m.size()<=10000&&cols<=10000,"RREF size limit");
    RREF result;result.columns=cols;
    size_t pivot_row=0;
    for(size_t col=0;col<cols&&pivot_row<m.size();++col){
        size_t best=pivot_row;
        while(best<m.size()&&m[best][col]==0)++best;
        if(best==m.size())continue;
        std::swap(m[pivot_row],m[best]);
        Q pivot=m[pivot_row][col];
        for(size_t j=col;j<cols;++j)m[pivot_row][j]/=pivot;
        for(size_t i=0;i<m.size();++i){
            if(i==pivot_row||m[i][col]==0)continue;
            Q factor=m[i][col];
            for(size_t j=col;j<cols;++j)m[i][j]-=factor*m[pivot_row][j];
        }
        result.pivot_columns.push_back(col);++pivot_row;
    }
    result.matrix=std::move(m);return result;
}
// A nonzero rational Jacobian minor at one rational point is a rigorous
// witness of generic functional independence: its determinant is a nonzero
// polynomial and therefore not identically zero over Q[q,p].
static bool jacobian_independence_witness(
    const std::vector<Polynomial>& accepted,const Polynomial& candidate,
    std::vector<Q>& witness){
    require(accepted.size()<candidate.vars,"cannot have more independent invariants than variables");
    for(auto& p:accepted)require(p.vars==candidate.vars,"Jacobian arity mismatch");
    for(int trial=1;trial<=32;++trial){
        std::vector<Q> x(candidate.vars);
        for(size_t j=0;j<x.size();++j){
            int64_t numerator=(int64_t)((trial*13+(int)j*17+trial*(int)j*7)%29)-14;
            x[j]=rational(numerator,(int64_t)(1+(trial+(int)j)%7));
        }
        std::vector<std::vector<Q>> gradients;
        auto row=[&](const Polynomial& p){
            std::vector<Q> v;
            for(size_t j=0;j<p.vars;++j)v.push_back(p.derivative(j).evaluate(x));
            return v;
        };
        for(auto& p:accepted)gradients.push_back(row(p));
        gradients.push_back(row(candidate));
        if(row_reduce(std::move(gradients),candidate.vars).rank()==accepted.size()+1){
            witness=std::move(x);return true;
        }
    }
    return false;
}
struct NoetherDiscovery {
    Polynomial invariant;
    std::string certificate_hash;
    uint32_t basis_degree=0;
    bool certified=false;
    bool functionally_independent=false;
    std::vector<Q> jacobian_witness;
};
static std::vector<NoetherDiscovery> discover_polynomial_invariants(
    const Polynomial& H,unsigned degree,size_t max_results=128){
    require(H.vars%2==0&&H.vars>0,"Noether: even positive dimension required");
    auto basis=enumerate_monomials(H.vars,degree);
    std::vector<Polynomial> bracket_columns;std::map<Monomial,size_t> rows;
    for(auto& mon:basis){
        Polynomial bracket=poisson(monomial_polynomial(H.vars,mon),H);
        for(auto& entry:bracket.terms)rows.emplace(entry.first,rows.size());
        bracket_columns.push_back(std::move(bracket));
    }
    require(rows.size()<=12000&&basis.size()<=12000,"Noether matrix too large");
    std::vector<std::vector<Q>> matrix(rows.size(),std::vector<Q>(basis.size(),0));
    for(size_t j=0;j<bracket_columns.size();++j)
        for(auto& kv:bracket_columns[j].terms)matrix[rows.at(kv.first)][j]=kv.second;
    auto solutions=row_reduce(std::move(matrix),basis.size()).nullspace();
    std::vector<NoetherDiscovery> result;
    std::vector<Polynomial> independent;
    for(auto& solution:solutions){
        Polynomial I(H.vars);
        for(size_t i=0;i<solution.size();++i)if(solution[i]!=0)I.add_monomial(basis[i],solution[i]);
        if(I.is_constant()||I.is_zero())continue;
        Polynomial bracket=poisson(I,H);
        NoetherDiscovery hit{I,blake3::hex(I.canonical()+"|"+H.canonical()),degree,bracket.is_zero(),false,{}};
        if(hit.certified){
            hit.functionally_independent=jacobian_independence_witness(independent,I,hit.jacobian_witness);
            if(hit.functionally_independent){
                independent.push_back(I);
                result.push_back(std::move(hit));
            }
        }
        if(result.size()>=max_results||result.size()>=H.vars)break;
    }
    return result;
}
struct QuadraticHamiltonian {
    size_t n=0; // number of canonical coordinate pairs
    std::vector<std::vector<Q>> A; // H(x) = x^T A x / 2 + b^T x + c
    std::vector<Q> b;
    Q c=0;
    explicit QuadraticHamiltonian(size_t n_pairs):n(n_pairs),A(2*n_pairs,std::vector<Q>(2*n_pairs,0)),b(2*n_pairs,0){
        require(n_pairs>0&&n_pairs<=12,"quadratic dimension limit");
    }
    Polynomial to_polynomial()const{
        Polynomial p=Polynomial::constant(2*n,c);
        for(size_t i=0;i<2*n;++i){
            p=p+Polynomial::variable(2*n,i)*b[i];
            for(size_t j=0;j<2*n;++j)
                if(A[i][j]!=0)p=p+Polynomial::variable(2*n,i)*Polynomial::variable(2*n,j)*(A[i][j]/2);
        }
        return p;
    }
};
static std::vector<Q> solve_exact_linear(std::vector<std::vector<Q>> a,std::vector<Q> y){
    size_t n=a.size();require(y.size()==n,"linear system dimensions");
    for(auto& row:a)require(row.size()==n,"linear system non-square");
    for(size_t col=0;col<n;++col){
        size_t pivot=col;while(pivot<n&&a[pivot][col]==0)++pivot;
        require(pivot<n,"singular linear system");
        std::swap(a[col],a[pivot]);std::swap(y[col],y[pivot]);
        Q scale=a[col][col];
        for(size_t j=col;j<n;++j)a[col][j]/=scale;
        y[col]/=scale;
        for(size_t i=0;i<n;++i)if(i!=col){
            Q factor=a[i][col];
            for(size_t j=col;j<n;++j)a[i][j]-=factor*a[col][j];
            y[i]-=factor*y[col];
        }
    }
    return y;
}
// Exactly solves the implicit midpoint equation for quadratic Hamiltonians.
static std::vector<Q> symplectic_midpoint(
    const QuadraticHamiltonian& H,const std::vector<Q>& x,const Q& h){
    size_t d=2*H.n;require(x.size()==d,"midpoint dimensions");
    std::vector<std::vector<Q>> A(d,std::vector<Q>(d,0));
    std::vector<Q> rhs(d,0);
    for(size_t i=0;i<d;++i){
        for(size_t j=0;j<d;++j){
            Q JA=(i<H.n?H.A[i+H.n][j]:-H.A[i-H.n][j]);
            A[i][j]=(i==j?Q(1):Q(0))-h*JA/2;
            rhs[i]+=(i==j?Q(1):Q(0))*x[j]+h*JA*x[j]/2;
        }
        rhs[i]+=h*(i<H.n?H.b[i+H.n]:-H.b[i-H.n]);
    }
    return solve_exact_linear(std::move(A),std::move(rhs));
}
// ======================================================================
// SMALL BIDIRECTIONAL DEPENDENT-TYPE KERNEL
//
// Trust boundary:
//   no oracle axioms, no "passed a test" rule, no accepted untyped graph.
//   Proofs inhabit types. The algebraic identity introduction rule uses an
//   exact polynomial normal form; the static cost rule uses a declared cost
//   model and makes NO assertion about native runtime CPU cycles.
//
// Calculus: universes, Pi, Sigma, variables (de Bruijn), lambda,
// application, equality/reflexivity, dependent pairs and projections.
// This is intentionally a small calculus, NOT full CIC (no general
// inductive eliminators, positivity checker, or universe polymorphism).
// ======================================================================
enum class TK : uint8_t {
    Universe, RationalType, Var, Pi, Sigma, Lambda, Application,
    Equality, Reflexivity, Pair, First, Second,
    RingIdentity, RingWitness, CostProposition, CostWitness
};
struct TypeTerm {
    TK kind=TK::Universe;
    int32_t a=-1,b=-1,c=-1;
    uint32_t param=0;
    bool alive=true;
};
class TrustedKernel {
    std::vector<TypeTerm> nodes_;
    std::vector<Polynomial> polynomials_;
    std::unordered_map<std::string,int32_t> interned_;
    std::vector<int32_t> persistent_roots_;
    size_t norm_fuel_=100000;
    static std::string key(const TypeTerm& t){
        return std::to_string((unsigned)t.kind)+"/"+std::to_string(t.a)+"/"+
               std::to_string(t.b)+"/"+std::to_string(t.c)+"/"+std::to_string(t.param);
    }
    const TypeTerm& get(int32_t id)const{
        require(id>=0&&(size_t)id<nodes_.size()&&nodes_[(size_t)id].alive,"bad proof term id");
        return nodes_[(size_t)id];
    }
    int32_t mk(TK k,int32_t a=-1,int32_t b=-1,int32_t c=-1,uint32_t param=0){
        TypeTerm t{k,a,b,c,param,true};
        std::string s=key(t);auto found=interned_.find(s);
        if(found!=interned_.end()&&nodes_[(size_t)found->second].alive)return found->second;
        require(nodes_.size()<kMaxTypeNodes,"proof term quota");
        int32_t id=(int32_t)nodes_.size();nodes_.push_back(t);interned_[std::move(s)]=id;return id;
    }
    int32_t shift_impl(int32_t id,int amount,unsigned cutoff,size_t& fuel){
        require(fuel--,"substitution fuel exhausted");
        TypeTerm t=get(id);
        if(t.kind==TK::Var){
            if(t.param<cutoff)return id;
            int64_t index=(int64_t)t.param+amount;
            require(index>=0&&index<1000000,"de Bruijn shift out of range");
            return mk(TK::Var,-1,-1,-1,(uint32_t)index);
        }
        if(t.kind==TK::Pi||t.kind==TK::Sigma||t.kind==TK::Lambda){
            int32_t a=shift_impl(t.a,amount,cutoff,fuel);
            int32_t b=shift_impl(t.b,amount,cutoff+1,fuel);
            return mk(t.kind,a,b,t.c,t.param);
        }
        if(t.kind==TK::Application||t.kind==TK::Equality||t.kind==TK::Pair){
            int32_t a=shift_impl(t.a,amount,cutoff,fuel);
            int32_t b=shift_impl(t.b,amount,cutoff,fuel);
            return mk(t.kind,a,b,t.c,t.param);
        }
        if(t.kind==TK::First||t.kind==TK::Second||t.kind==TK::Reflexivity)
            return mk(t.kind,shift_impl(t.a,amount,cutoff,fuel),t.b,t.c,t.param);
        return id;
    }
    int32_t substitute_impl(int32_t id,unsigned index,int32_t replacement,unsigned depth,size_t& fuel){
        require(fuel--,"substitution budget exhausted");TypeTerm t=get(id);
        if(t.kind==TK::Var){
            if(t.param==index+depth)return shift_impl(replacement,(int)depth,0,fuel);
            return id;
        }
        if(t.kind==TK::Pi||t.kind==TK::Sigma||t.kind==TK::Lambda){
            int32_t a=substitute_impl(t.a,index,replacement,depth,fuel);
            int32_t b=substitute_impl(t.b,index,replacement,depth+1,fuel);
            return mk(t.kind,a,b,t.c,t.param);
        }
        if(t.kind==TK::Application||t.kind==TK::Equality||t.kind==TK::Pair){
            int32_t a=substitute_impl(t.a,index,replacement,depth,fuel);
            int32_t b=substitute_impl(t.b,index,replacement,depth,fuel);
            return mk(t.kind,a,b,t.c,t.param);
        }
        if(t.kind==TK::First||t.kind==TK::Second||t.kind==TK::Reflexivity)
            return mk(t.kind,substitute_impl(t.a,index,replacement,depth,fuel),t.b,t.c,t.param);
        return id;
    }
    int32_t instantiate_impl(int32_t body,int32_t argument,size_t& fuel){
        // Standard lifting: (body [0 := argument↑1]) ↓1.
        int32_t raised=shift_impl(argument,1,0,fuel);
        int32_t substituted=substitute_impl(body,0,raised,0,fuel);
        return shift_impl(substituted,-1,0,fuel);
    }
    int32_t normalize_impl(int32_t id,size_t& fuel){
        require(fuel--,"normalization fuel exhausted");
        TypeTerm t=get(id);
        switch(t.kind){
            case TK::Application:{
                int32_t fn=normalize_impl(t.a,fuel);
                int32_t arg=normalize_impl(t.b,fuel);
                TypeTerm f=get(fn);
                if(f.kind==TK::Lambda)
                    return normalize_impl(instantiate_impl(f.b,arg,fuel),fuel);
                return mk(TK::Application,fn,arg);
            }
            case TK::First:case TK::Second:{
                int32_t pair=normalize_impl(t.a,fuel);TypeTerm p=get(pair);
                if(p.kind==TK::Pair)return normalize_impl(t.kind==TK::First?p.a:p.b,fuel);
                return mk(t.kind,pair);
            }
            case TK::Pi:case TK::Sigma:case TK::Lambda:{
                auto a=normalize_impl(t.a,fuel),b=normalize_impl(t.b,fuel);
                return mk(t.kind,a,b);
            }
            case TK::Equality:case TK::Pair:{
                auto a=normalize_impl(t.a,fuel),b=normalize_impl(t.b,fuel);
                return mk(t.kind,a,b);
            }
            case TK::Reflexivity:return mk(TK::Reflexivity,normalize_impl(t.a,fuel));
            default:return id;
        }
    }
    bool structurally_equal(int32_t a,int32_t b,size_t& fuel){
        require(fuel--,"conversion budget exhausted");
        if(a==b)return true;
        TypeTerm x=get(a),y=get(b);
        if(x.kind!=y.kind||x.param!=y.param)return false;
        auto same_child=[&](int32_t m,int32_t n){
            if(m<0||n<0)return m==n;
            return structurally_equal(m,n,fuel);
        };
        return same_child(x.a,y.a)&&same_child(x.b,y.b)&&same_child(x.c,y.c);
    }
    int32_t infer_impl(int32_t id,const std::vector<int32_t>& context,size_t& fuel){
        require(fuel--,"type inference budget exhausted");
        require(context.size()<=1024,"context depth limit");
        TypeTerm t=get(id);
        switch(t.kind){
            case TK::Universe:{
                require(t.param<32,"universe level limit");return universe(t.param+1);
            }
            case TK::RationalType:return universe(0);
            case TK::Var:{
                require(t.param<context.size(),"unbound variable");
                return shift_impl(context[t.param],(int)t.param+1,0,fuel);
            }
            case TK::Pi:case TK::Sigma:{
                int32_t sort_a=normalize_impl(infer_impl(t.a,context,fuel),fuel);
                require(get(sort_a).kind==TK::Universe,"binder domain is not a type");
                auto extended=context;extended.insert(extended.begin(),t.a);
                int32_t sort_b=normalize_impl(infer_impl(t.b,extended,fuel),fuel);
                require(get(sort_b).kind==TK::Universe,"binder codomain is not a type");
                return universe(std::max(get(sort_a).param,get(sort_b).param));
            }
            case TK::Lambda:{
                int32_t type_of_domain=normalize_impl(infer_impl(t.a,context,fuel),fuel);
                require(get(type_of_domain).kind==TK::Universe,"lambda binder must be type");
                auto extended=context;extended.insert(extended.begin(),t.a);
                int32_t body_type=infer_impl(t.b,extended,fuel);
                return pi(t.a,body_type);
            }
            case TK::Application:{
                int32_t fn_type=normalize_impl(infer_impl(t.a,context,fuel),fuel);
                TypeTerm fn=get(fn_type);require(fn.kind==TK::Pi,"application of a non-function");
                check_impl(t.b,fn.a,context,fuel);
                return instantiate_impl(fn.b,t.b,fuel);
            }
            case TK::Equality:{
                int32_t a=infer_impl(t.a,context,fuel);
                check_impl(t.b,a,context,fuel);return universe(0);
            }
            case TK::Reflexivity:{
                infer_impl(t.a,context,fuel);return equality(t.a,t.a);
            }
            case TK::Pair:
                throw std::runtime_error("pair needs an expected Sigma type");
            case TK::First:{
                int32_t pair_type=normalize_impl(infer_impl(t.a,context,fuel),fuel);
                TypeTerm s=get(pair_type);require(s.kind==TK::Sigma,"first projection needs Sigma");return s.a;
            }
            case TK::Second:{
                int32_t pair_type=normalize_impl(infer_impl(t.a,context,fuel),fuel);
                TypeTerm s=get(pair_type);require(s.kind==TK::Sigma,"second projection needs Sigma");
                return instantiate_impl(s.b,first(t.a),fuel);
            }
            case TK::RingIdentity:{
                require(t.param<polynomials_.size()&&t.a>=0&&(size_t)t.a<polynomials_.size(),"bad ring proposition");
                require(polynomials_[(size_t)t.a].vars==polynomials_[t.param].vars,"ring variables mismatch");
                return universe(0);
            }
            case TK::CostProposition:return universe(0);
            case TK::RingWitness:case TK::CostWitness:
                throw std::runtime_error("witness needs a checked expected proposition");
        }
        throw std::runtime_error("unknown type constructor");
    }
    void check_impl(int32_t id,int32_t expected,const std::vector<int32_t>& ctx,size_t& fuel){
        require(fuel--,"type checking fuel exhausted");
        TypeTerm term=get(id);
        int32_t actual_expected=normalize_impl(expected,fuel);
        TypeTerm proposition=get(actual_expected);
        if(term.kind==TK::Lambda&&proposition.kind==TK::Pi){
            require(defeq_impl(term.a,proposition.a,fuel),"lambda domain mismatch");
            auto extended=ctx;extended.insert(extended.begin(),proposition.a);
            check_impl(term.b,proposition.b,extended,fuel);
            return;
        }
        if(term.kind==TK::Pair&&proposition.kind==TK::Sigma){
            check_impl(term.a,proposition.a,ctx,fuel);
            check_impl(term.b,instantiate_impl(proposition.b,term.a,fuel),ctx,fuel);
            return;
        }
        if(term.kind==TK::RingWitness&&proposition.kind==TK::RingIdentity){
            const Polynomial& a=polynomials_[(size_t)proposition.a];
            const Polynomial& b=polynomials_[proposition.param];
            require(a==b,"ring normal forms differ: invalid algebraic proof");
            return;
        }
        if(term.kind==TK::CostWitness&&proposition.kind==TK::CostProposition){
            require(proposition.a>proposition.b&&proposition.b>=0,"cost model not strictly improved");
            return;
        }
        int32_t actual=infer_impl(id,ctx,fuel);
        require(defeq_impl(actual,expected,fuel),"type mismatch");
    }
    bool defeq_impl(int32_t a,int32_t b,size_t& fuel){
        return structurally_equal(normalize_impl(a,fuel),normalize_impl(b,fuel),fuel);
    }
public:
    TrustedKernel(){nodes_.reserve(4000);}
    int32_t universe(uint32_t level){require(level<33,"universe overflow");return mk(TK::Universe,-1,-1,-1,level);}
    int32_t rational_type(){return mk(TK::RationalType);}
    int32_t var(uint32_t index){return mk(TK::Var,-1,-1,-1,index);}
    int32_t pi(int32_t domain,int32_t codomain){get(domain);get(codomain);return mk(TK::Pi,domain,codomain);}
    int32_t sigma(int32_t domain,int32_t codomain){get(domain);get(codomain);return mk(TK::Sigma,domain,codomain);}
    int32_t lambda(int32_t domain,int32_t body){get(domain);get(body);return mk(TK::Lambda,domain,body);}
    int32_t app(int32_t fn,int32_t arg){get(fn);get(arg);return mk(TK::Application,fn,arg);}
    int32_t equality(int32_t a,int32_t b){get(a);get(b);return mk(TK::Equality,a,b);}
    int32_t refl(int32_t value){get(value);return mk(TK::Reflexivity,value);}
    int32_t pair(int32_t a,int32_t b){get(a);get(b);return mk(TK::Pair,a,b);}
    int32_t first(int32_t id){get(id);return mk(TK::First,id);}
    int32_t second(int32_t id){get(id);return mk(TK::Second,id);}
    int32_t polynomial(const Polynomial& p){
        require(polynomials_.size()<kMaxTypeNodes,"polynomial store quota");
        polynomials_.push_back(p);return (int32_t)(polynomials_.size()-1);
    }
    int32_t ring_identity(int32_t left,int32_t right){
        require(left>=0&&right>=0&&(size_t)left<polynomials_.size()&&(size_t)right<polynomials_.size(),"bad ring identity");
        return mk(TK::RingIdentity,left,-1,-1,(uint32_t)right);
    }
    int32_t ring_witness(){return mk(TK::RingWitness);}
    int32_t cost_prop(uint32_t old_cost,uint32_t new_cost){
        require(old_cost<=INT32_MAX&&new_cost<=INT32_MAX,"cost limit");
        return mk(TK::CostProposition,(int32_t)old_cost,(int32_t)new_cost);
    }
    int32_t cost_witness(){return mk(TK::CostWitness);}
    void check(int32_t term,int32_t expected){std::vector<int32_t> empty;size_t fuel=norm_fuel_;check_impl(term,expected,empty,fuel);}
    int32_t infer(int32_t term){std::vector<int32_t> empty;size_t fuel=norm_fuel_;return infer_impl(term,empty,fuel);}
    bool convertible(int32_t a,int32_t b){size_t fuel=norm_fuel_;return defeq_impl(a,b,fuel);}
    int32_t normalize(int32_t t){size_t fuel=norm_fuel_;return normalize_impl(t,fuel);}
    void protect(int32_t root){get(root);persistent_roots_.push_back(root);}
    size_t nodes()const{return nodes_.size();}
    size_t live_nodes()const{size_t n=0;for(auto& e:nodes_)n+=e.alive;return n;}
    size_t collect(const std::vector<int32_t>& temporary_roots={}){
        std::vector<uint8_t> marked(nodes_.size(),0);
        std::vector<int32_t> pending=persistent_roots_;
        pending.insert(pending.end(),temporary_roots.begin(),temporary_roots.end());
        while(!pending.empty()){
            int32_t id=pending.back();pending.pop_back();
            if(id<0||(size_t)id>=nodes_.size()||!nodes_[id].alive||marked[id])continue;
            marked[id]=1;
            const TypeTerm& t=nodes_[id];
            if(t.a>=0&&t.kind!=TK::RingIdentity&&t.kind!=TK::CostProposition)pending.push_back(t.a);
            if(t.b>=0&&t.kind!=TK::CostProposition)pending.push_back(t.b);
            if(t.c>=0)pending.push_back(t.c);
        }
        size_t reclaimed=0;
        for(size_t i=0;i<nodes_.size();++i)if(nodes_[i].alive&&!marked[i]){
            nodes_[i].alive=false;interned_.erase(key(nodes_[i]));++reclaimed;
        }
        // Node IDs are not reused, preventing stale-pointer aliasing. A full
        // compaction into a new kernel can be performed at a snapshot boundary.
        return reclaimed;
    }
};
struct ProofCertificate {
    std::string domain;
    std::string statement_hash;
    std::string proof_hash;
    std::string evidence;
    uint32_t old_static_cost=0,new_static_cost=0;
    bool verified=false;
};
static ProofCertificate certify_symbolic_improvement(
    TrustedKernel& kernel,const Polynomial& before,const Polynomial& after,
    uint32_t old_cost,uint32_t new_cost){
    int32_t a=kernel.polynomial(before),b=kernel.polynomial(after);
    int32_t ring=kernel.ring_identity(a,b);
    int32_t cost=kernel.cost_prop(old_cost,new_cost);
    // Sigma's second component is non-dependent here; if in future it depends
    // on the first component, a lifting operation is required at construction.
    int32_t theorem=kernel.sigma(ring,cost);
    int32_t witness=kernel.pair(kernel.ring_witness(),kernel.cost_witness());
    kernel.check(witness,theorem);
    kernel.protect(theorem);kernel.protect(witness);
    std::string statement=before.canonical()+"|"+after.canonical()+"|"+
        std::to_string(old_cost)+"|"+std::to_string(new_cost);
    return {"Q[x] exact polynomial identity + static AST cost",
            blake3::hex(statement),blake3::hex("proof:Sigma:ring+cost:"+statement),
            statement,old_cost,new_cost,true};
}
static ProofCertificate certify_noether(TrustedKernel& kernel,
                                        const Polynomial& invariant,
                                        const Polynomial& Hamiltonian){
    Polynomial bracket=poisson(invariant,Hamiltonian);
    Polynomial zero(Hamiltonian.vars);
    int32_t a=kernel.polynomial(bracket),b=kernel.polynomial(zero);
    int32_t statement=kernel.ring_identity(a,b);
    int32_t witness=kernel.ring_witness();
    kernel.check(witness,statement);kernel.protect(statement);kernel.protect(witness);
    std::string body=invariant.canonical()+"|"+Hamiltonian.canonical();
    return {"formal Poisson bracket identity in Q[q,p]",
            blake3::hex(body),blake3::hex("noether:"+body),
            body,0,0,true};
}
// ======================================================================
// EXPRESSION AST, HASH-CONSING, EXACT SEMANTICS, GRAPH NEURAL HEURISTICS,
// MONTE CARLO TREE SEARCH. AST is a mathematically specified DSL, NOT C++.
// ======================================================================
#include "expression_graph.hpp"
enum class Rewrite:uint8_t{
    AddZero, MultiplyOne, MultiplyZero, DoubleNegate, ConstantFold,
    PowerOne, PowerZero, AddSelf, Distribute, FactorLeft,
    SwapAdd, SwapMultiply, ReassociateAdd, ReassociateMultiply,
    NegateConstant, IfSame, IfConstant, LoopZero, Count
};
[[maybe_unused]] static const char* rewrite_name(Rewrite t){
    static const char* names[]={"add-zero","mul-one","mul-zero","double-negate","fold-constant",
        "pow-one","pow-zero","sum-to-double","distribute","factor-left","commute-add",
        "commute-mul","associate-add","associate-mul","negate-constant",
        "if-same","if-constant","loop-zero"};
    return names[(unsigned)t];
}
struct RewriteAction{int32_t node=-1;Rewrite rule=Rewrite::AddZero;};
static std::optional<int32_t> rewrite_at(ExpressionGraph& g,int32_t id,Rewrite rule){
    ExprNode n=g.at(id);
    if(rule==Rewrite::IfSame&&n.kind==ExprKind::IfLess&&n.left==n.right)return n.left;
    if(rule==Rewrite::LoopZero&&n.kind==ExprKind::BoundedLoop&&n.index==0)return n.left;
    if(rule==Rewrite::IfConstant&&n.kind==ExprKind::IfLess&&
        g.at(n.guard_left).kind==ExprKind::Constant&&g.at(n.guard_right).kind==ExprKind::Constant)
        return g.at(n.guard_left).value<g.at(n.guard_right).value?n.left:n.right;
    if(!n.shape.empty())return std::nullopt;
    auto is_const=[&](int32_t child,const Q& q){return child>=0&&g.at(child).kind==ExprKind::Constant&&g.at(child).value==q;};
    switch(rule){
        case Rewrite::AddZero:
            if(n.kind==ExprKind::Add){if(is_const(n.left,0))return n.right;if(is_const(n.right,0))return n.left;}
            break;
        case Rewrite::MultiplyOne:
            if(n.kind==ExprKind::Multiply){if(is_const(n.left,1))return n.right;if(is_const(n.right,1))return n.left;}
            break;
        case Rewrite::MultiplyZero:
            if(n.kind==ExprKind::Multiply&&(is_const(n.left,0)||is_const(n.right,0)))return g.constant(0);
            break;
        case Rewrite::DoubleNegate:
            if(n.kind==ExprKind::Negate&&g.at(n.left).kind==ExprKind::Negate)return g.at(n.left).left;
            break;
        case Rewrite::ConstantFold:
            if(n.kind==ExprKind::Add||n.kind==ExprKind::Multiply){
                auto a=g.at(n.left),b=g.at(n.right);
                if(a.kind==ExprKind::Constant&&b.kind==ExprKind::Constant)
                    return g.constant(n.kind==ExprKind::Add?Q(a.value+b.value):Q(a.value*b.value));
            }break;
        case Rewrite::PowerOne:if(n.kind==ExprKind::Power&&n.index==1)return n.left;break;
        case Rewrite::PowerZero:if(n.kind==ExprKind::Power&&n.index==0)return g.constant(1);break;
        case Rewrite::AddSelf:
            if(n.kind==ExprKind::Add&&n.left==n.right)return g.multiply(g.constant(2),n.left);
            break;
        case Rewrite::Distribute:
            if(n.kind==ExprKind::Multiply){
                auto a=g.at(n.left),b=g.at(n.right);
                if(b.kind==ExprKind::Add)
                    return g.add(g.multiply(n.left,b.left),g.multiply(n.left,b.right));
                if(a.kind==ExprKind::Add)
                    return g.add(g.multiply(a.left,n.right),g.multiply(a.right,n.right));
            }break;
        case Rewrite::FactorLeft:
            if(n.kind==ExprKind::Add){
                auto a=g.at(n.left),b=g.at(n.right);
                if(a.kind==ExprKind::Multiply&&b.kind==ExprKind::Multiply){
                    if(a.left==b.left)return g.multiply(a.left,g.add(a.right,b.right));
                    if(a.right==b.right)return g.multiply(g.add(a.left,b.left),a.right);
                }
            }break;
        case Rewrite::SwapAdd:
            if(n.kind==ExprKind::Add&&n.left!=n.right)return g.add(n.right,n.left);
            break;
        case Rewrite::SwapMultiply:
            if(n.kind==ExprKind::Multiply&&n.left!=n.right)return g.multiply(n.right,n.left);
            break;
        case Rewrite::ReassociateAdd:
            if(n.kind==ExprKind::Add){auto a=g.at(n.left);if(a.kind==ExprKind::Add)return g.add(a.left,g.add(a.right,n.right));}
            break;
        case Rewrite::ReassociateMultiply:
            if(n.kind==ExprKind::Multiply){auto a=g.at(n.left);if(a.kind==ExprKind::Multiply)return g.multiply(a.left,g.multiply(a.right,n.right));}
            break;
        case Rewrite::NegateConstant:
            if(n.kind==ExprKind::Negate&&g.at(n.left).kind==ExprKind::Constant)
                return g.constant(-g.at(n.left).value);
            break;
        case Rewrite::IfSame:case Rewrite::IfConstant:case Rewrite::LoopZero:case Rewrite::Count:break;
    }
    return std::nullopt;
}
static std::vector<RewriteAction> applicable_rewrites(ExpressionGraph& g,int32_t root){
    auto nodes=g.preorder(root);std::vector<RewriteAction> result;
    for(int32_t id:nodes)for(unsigned i=0;i<(unsigned)Rewrite::Count;++i)
        if(rewrite_at(g,id,(Rewrite)i).has_value())result.push_back({id,(Rewrite)i});
    return result;
}
static int32_t apply_rewrite(ExpressionGraph& g,int32_t root,const RewriteAction& a){
    auto changed=rewrite_at(g,a.node,a.rule);
    return changed?g.replace_subtree(root,a.node,*changed):root;
}

// Graph Neural Network: two rounds of neighborhood message passing,
// shared weights, graph pooling, a learned policy head and value head.
// This is not a pretrained model; data quality and training determine utility.
class GraphNeuralNetwork {
    static constexpr int D=12;
    using Vec=std::array<double,D>;
    using Mat=std::array<Vec,D>;
    Mat self_{},child_{},parent_{};
    Vec value_head_{};
    std::array<Vec,(unsigned)Rewrite::Count> action_head_{};
    std::array<double,(unsigned)Rewrite::Count> action_bias_{};
    uint64_t state_;
    uint64_t updates_=0;
    static Vec zero(){Vec x{};return x;}
    static double dot(const Vec& a,const Vec& b){double v=0;for(int i=0;i<D;++i)v+=a[i]*b[i];return v;}
    static Vec matvec(const Mat& a,const Vec& b){
        Vec out{};for(int i=0;i<D;++i)for(int j=0;j<D;++j)out[i]+=a[i][j]*b[j];return out;
    }
    static void plus(Vec& a,const Vec& b,double scale=1){for(int j=0;j<D;++j)a[j]+=scale*b[j];}
    static double clamp(double v,double lo,double hi){return std::max(lo,std::min(hi,v));}
public:
    explicit GraphNeuralNetwork(uint64_t seed=0x1337beef):state_(seed){
        auto init=[&](double scale){return (unit_random(state_)*2-1)*scale;};
        for(auto* mat:{&self_,&child_,&parent_})for(auto& r:*mat)for(double& a:r)a=init(.14);
        for(double& a:value_head_)a=init(.25);
        for(auto& a:action_head_)for(double& x:a)x=init(.25);
        for(auto& a:action_bias_)a=init(.01);
    }
    struct Features{
        std::unordered_map<int32_t,Vec> node;
        Vec pooled{};
        double value=0;
    };
    Features encode(ExpressionGraph& graph,int32_t root)const{
        auto order=graph.preorder(root,10000);Features out;
        std::unordered_map<int32_t,std::vector<int32_t>> parents;
        for(auto id:order){
            const auto& n=graph.at(id);Vec h{};
            h[(unsigned)n.kind % 6]=1;
            h[6]=std::tanh((double)n.index/8.0);
            h[7]=n.kind==ExprKind::Constant?std::tanh(n.value.get_d()/100.0):0;
            h[8]=n.left>=0?1:0;h[9]=n.right>=0?1:0;
            h[10]=1;h[11]=(n.kind==ExprKind::Multiply||n.kind==ExprKind::Power)?1:0;
            out.node.emplace(id,h);
            for(auto c:graph.children(id))parents[c].push_back(id);
        }
        for(int round=0;round<2;++round){
            auto next=out.node;
            for(int32_t id:order){
                Vec h=matvec(self_,out.node.at(id)),kids=zero(),up=zero();
                for(auto c:graph.children(id))plus(kids,out.node.at(c));
                for(int32_t p:parents[id])plus(up,out.node.at(p));
                if(!parents[id].empty())for(auto& x:up)x/=parents[id].size();
                plus(h,matvec(child_,kids),.5);plus(h,matvec(parent_,up),.3);
                for(double& x:h)x=std::tanh(x);
                next[id]=h;
            }
            out.node=std::move(next);
        }
        for(int32_t id:order)plus(out.pooled,out.node.at(id));
        for(double& x:out.pooled)x/=std::max<size_t>(1,order.size());
        out.value=std::tanh(dot(value_head_,out.pooled));return out;
    }
    double action_prior(const Features& f,const RewriteAction& a)const{
        auto it=f.node.find(a.node);if(it==f.node.end())return 0;
        unsigned k=(unsigned)a.rule;
        double score=dot(action_head_[k],it->second)+action_bias_[k];
        // Handcrafted priors prevent the untrained model from saturating the
        // search with reversible commutation steps.
        if(a.rule==Rewrite::AddZero||a.rule==Rewrite::MultiplyOne||
           a.rule==Rewrite::ConstantFold||a.rule==Rewrite::FactorLeft)score+=1.3;
        if(a.rule==Rewrite::SwapAdd||a.rule==Rewrite::SwapMultiply||
           a.rule==Rewrite::Distribute)score-=1.3;
        return std::exp(clamp(score,-12,12));
    }
    void learn(const Features& f,const RewriteAction& action,double reward,double rate=.015){
        reward=clamp(reward,-1,1);unsigned k=(unsigned)action.rule;
        auto it=f.node.find(action.node);if(it!=f.node.end()){
            for(int j=0;j<D;++j)action_head_[k][j]+=rate*reward*it->second[j];
            action_bias_[k]+=rate*reward;
        }
        double err=reward-f.value;
        for(int j=0;j<D;++j)value_head_[j]+=rate*err*f.pooled[j];
        ++updates_;
    }
    uint64_t updates()const{return updates_;}
};
// A persisted optimization proof binds its ring theorem and cost inequality
// to two actual ASTs. This prevents later replay with invented cost figures.
static ProofCertificate certify_graph_improvement(TrustedKernel& kernel,
    ExpressionGraph& graph,int32_t old_root,int32_t new_root,size_t variables){
    uint32_t old_cost=graph.static_cost(old_root);
    uint32_t new_cost=graph.static_cost(new_root);
    require(new_cost<old_cost,"no strict static cost improvement");
    auto before=graph.symbolic(old_root,variables).canonical();
    auto after=graph.symbolic(new_root,variables).canonical();
    require(before==after,"programs are not symbolically equivalent");
    ProofCertificate ring;
    bool legacy=graph.polynomial_only(old_root)&&graph.polynomial_only(new_root);
    if(legacy)ring=certify_symbolic_improvement(kernel,graph.polynomial(old_root,variables),
        graph.polynomial(new_root,variables),old_cost,new_cost);
    else {
        kernel.check(kernel.cost_witness(),kernel.cost_prop(old_cost,new_cost));
        ring={"bounded exact program equivalence (C++ checker)",blake3::hex(before),
            blake3::hex("program-normal-form-v2:"+before),"",old_cost,new_cost,true};
    }
    std::string body=std::string(legacy?"ASTv1|":"ASTv2|")+std::to_string(variables)+"|"+graph.repr(old_root)+"|"+
        graph.repr(new_root)+"|"+std::to_string(old_cost)+"|"+std::to_string(new_cost)+
        "|"+ring.statement_hash;
    ring.domain=legacy?"Q[x] polynomial identity + recomputable AST static cost":
        "bounded rational/tensor program equivalence + static cost; Lean kernel check required";
    ring.statement_hash=blake3::hex(body);
    ring.proof_hash=blake3::hex("certified-ast:"+body+":"+ring.proof_hash);
    ring.evidence=body;
    return ring;
}
struct SearchReport{
    int32_t initial_root=-1,best_root=-1;
    uint32_t start_cost=0,best_cost=0;
    unsigned simulations=0,verified=0,proposals=0;
    std::string best_expression;
    std::optional<ProofCertificate> certificate;
};
struct TreeSearchNode{
    int32_t root=-1;
    int32_t parent=-1;
    RewriteAction incoming{};
    std::vector<int32_t> children;
    std::vector<RewriteAction> actions;
    std::vector<double> prior;
    size_t expanded=0;
    double total_value=0;
    uint32_t visits=0;
    bool evaluated=false;
};
static SearchReport mcts_optimize(ExpressionGraph& graph,GraphNeuralNetwork& net,
                                  TrustedKernel& kernel,int32_t original_root,
                                  size_t vars,unsigned iterations=200){
    require(iterations<=kMaxSearchIterations,"MCTS budget");
    auto baseline=graph.symbolic(original_root,vars).canonical();
    SearchReport report;report.initial_root=report.best_root=original_root;
    report.start_cost=report.best_cost=graph.static_cost(original_root);
    std::vector<TreeSearchNode> tree;
    tree.reserve(iterations+1);
    tree.push_back(TreeSearchNode{});tree[0].root=original_root;
    std::unordered_set<std::string> transposed{graph.repr(original_root)};
    for(unsigned sim=0;sim<iterations;++sim){
        int32_t node=0;std::vector<int32_t> path{0};
        while(true){
            auto& st=tree[(size_t)node];
            if(!st.evaluated){
                auto features=net.encode(graph,st.root);
                st.actions=applicable_rewrites(graph,st.root);
                for(auto& a:st.actions)st.prior.push_back(net.action_prior(features,a));
                st.evaluated=true;
            }
            if(st.expanded<st.actions.size()){
                RewriteAction action=st.actions[st.expanded++];
                int32_t next_root=apply_rewrite(graph,st.root,action);
                if(next_root==st.root)continue;
                std::string id=graph.repr(next_root);
                if(transposed.count(id))continue;
                transposed.insert(std::move(id));
                require(tree.size()<kMaxSearchIterations+1,"MCTS tree memory quota");
                int32_t child=(int32_t)tree.size();tree.push_back(TreeSearchNode{});
                tree.back().root=next_root;tree.back().parent=node;tree.back().incoming=action;
                tree[(size_t)node].children.push_back(child);
                node=child;path.push_back(child);break;
            }
            if(st.children.empty())break;
            double best=-1e100;int32_t best_child=st.children.front();
            auto features=net.encode(graph,st.root);
            for(auto child:st.children){
                auto& c=tree[child];
                double q=c.visits?c.total_value/c.visits:0;
                double p=net.action_prior(features,c.incoming);
                double u=1.5*p*std::sqrt(1.0+st.visits)/(1.0+c.visits);
                if(q+u>best){best=q+u;best_child=child;}
            }
            node=best_child;path.push_back(node);
            if(path.size()>128)break;
        }
        auto& leaf=tree[node];uint32_t cost=graph.static_cost(leaf.root);
        double reward=std::max(-1.0,std::min(1.0,(double(report.start_cost)-cost)/std::max<double>(1,report.start_cost)));
        if(cost<report.best_cost){
            try {
                // Exact symbolic proof, independently recomputed by the
                // checker. No finite test corpus is a premise of this proof.
                auto candidate=graph.symbolic(leaf.root,vars).canonical();
                require(candidate==baseline,"candidate is not equivalent");
                auto cert=certify_graph_improvement(kernel,graph,original_root,leaf.root,vars);
                ++report.verified;
                report.best_root=leaf.root;report.best_cost=cost;
                report.best_expression=graph.repr(leaf.root);
                report.certificate=std::move(cert);reward=1;
            }catch(const std::exception&){reward=-1;}
        }
        if(path.size()>1){
            int32_t parent=path[path.size()-2];
            auto f=net.encode(graph,tree[parent].root);
            net.learn(f,tree[node].incoming,reward);
        }
        for(auto id:path){tree[id].visits++;tree[id].total_value+=reward;}
        report.simulations++;
    }
    report.proposals=(unsigned)transposed.size()-1;
    if(report.best_expression.empty())report.best_expression=graph.repr(original_root);
    return report;
}
// ======================================================================
// PERSISTENT B-TREE CONTENT-ADDRESSED KNOWLEDGE BASE
// Keys: 64 lowercase hex characters representing BLAKE3-256 digests.
// Values: bounded structured records; atomic snapshots, authenticated
// with BLAKE3. The persistent file represents a serialized B-tree image.
// ======================================================================
struct KnowledgeRecord {
    std::string hash;
    std::string category;
    std::string statement;
    std::string proof;
    uint64_t generation=0;
    uint64_t verified_at=0;
};
class KnowledgeTree {
    static constexpr size_t T=8;
    static constexpr size_t MAX_KEYS=2*T-1;
    struct Node {
        bool leaf=true;
        std::vector<KnowledgeRecord> keys;
        std::vector<std::unique_ptr<Node>> children;
    };
    std::unique_ptr<Node> root_;
    size_t size_=0;
    static bool valid_hex(const std::string& s){
        if(s.size()!=64)return false;
        for(char c:s)if(!((c>='0'&&c<='9')||(c>='a'&&c<='f')))return false;
        return true;
    }
    static const KnowledgeRecord* find_node(const Node* n,const std::string& hash){
        if(!n)return nullptr;
        auto it=std::lower_bound(n->keys.begin(),n->keys.end(),hash,
            [](const KnowledgeRecord& r,const std::string& h){return r.hash<h;});
        size_t index=(size_t)(it-n->keys.begin());
        if(it!=n->keys.end()&&it->hash==hash)return &*it;
        return n->leaf?nullptr:find_node(n->children[index].get(),hash);
    }
    static void split_child(Node* parent,size_t i){
        auto& child=parent->children[i];
        require(child->keys.size()==MAX_KEYS,"B-tree split precondition");
        auto sibling=std::make_unique<Node>();sibling->leaf=child->leaf;
        KnowledgeRecord median=child->keys[T-1];
        sibling->keys.assign(std::make_move_iterator(child->keys.begin()+T),
                             std::make_move_iterator(child->keys.end()));
        child->keys.resize(T-1);
        if(!child->leaf){
            sibling->children.reserve(T);
            for(size_t j=T;j<2*T;++j)sibling->children.push_back(std::move(child->children[j]));
            child->children.resize(T);
        }
        parent->keys.insert(parent->keys.begin()+i,std::move(median));
        parent->children.insert(parent->children.begin()+i+1,std::move(sibling));
    }
    static void insert_nonfull(Node* node,KnowledgeRecord r){
        size_t i=(size_t)(std::lower_bound(node->keys.begin(),node->keys.end(),r.hash,
            [](const KnowledgeRecord& a,const std::string& k){return a.hash<k;})-node->keys.begin());
        if(node->leaf){node->keys.insert(node->keys.begin()+i,std::move(r));return;}
        if(node->children[i]->keys.size()==MAX_KEYS){
            split_child(node,i);
            if(r.hash>node->keys[i].hash)++i;
        }
        insert_nonfull(node->children[i].get(),std::move(r));
    }
    static void inorder(const Node* n,std::vector<KnowledgeRecord>& result){
        if(!n)return;
        for(size_t i=0;i<n->keys.size();++i){
            if(!n->leaf)inorder(n->children[i].get(),result);
            result.push_back(n->keys[i]);
        }
        if(!n->leaf)inorder(n->children.back().get(),result);
    }
    static bool validate_node(const Node* n,bool is_root,size_t depth,
                              size_t& leaf_depth,const std::string* lower,
                              const std::string* upper,size_t& count){
        if(!n||n->keys.size()>MAX_KEYS||(!is_root&&n->keys.size()<T-1))return false;
        if(!n->leaf&&n->children.size()!=n->keys.size()+1)return false;
        if(n->leaf){
            if(leaf_depth==SIZE_MAX)leaf_depth=depth;
            else if(leaf_depth!=depth)return false;
        }
        for(size_t i=0;i<n->keys.size();++i){
            auto& h=n->keys[i].hash;
            if(!valid_hex(h)||(lower&&h<=*lower)||(upper&&h>=*upper))return false;
            if(i&&n->keys[i-1].hash>=h)return false;
            ++count;
        }
        if(!n->leaf)for(size_t i=0;i<n->children.size();++i){
            const std::string* l=i==0?lower:&n->keys[i-1].hash;
            const std::string* r=i==n->keys.size()?upper:&n->keys[i].hash;
            if(!validate_node(n->children[i].get(),false,depth+1,leaf_depth,l,r,count))return false;
        }
        return true;
    }
    static void append_u32(std::string& out,uint32_t n){for(int i=0;i<4;++i)out.push_back(char((n>>(8*i))&255));}
    static void append_u64(std::string& out,uint64_t n){for(int i=0;i<8;++i)out.push_back(char((n>>(8*i))&255));}
    static bool pull_u32(std::string_view p,size_t& off,uint32_t& out){
        if(off>p.size()||p.size()-off<4)return false;
        out=0;
        for(int i=0;i<4;++i)out|=uint32_t(uint8_t(p[off++]))<<(8*i);
        return true;
    }
    static bool pull_u64(std::string_view p,size_t& off,uint64_t& out){
        if(off>p.size()||p.size()-off<8)return false;
        out=0;
        for(int i=0;i<8;++i)out|=uint64_t(uint8_t(p[off++]))<<(8*i);
        return true;
    }
    static void append_string(std::string& out,const std::string& s){
        require(s.size()<=1048576,"persistent field too large");append_u32(out,(uint32_t)s.size());out+=s;
    }
    static bool pull_string(std::string_view p,size_t& off,std::string& out){
        uint32_t n=0;
        if(!pull_u32(p,off,n)||n>1048576||off>p.size()||n>p.size()-off)return false;
        out.assign(p.substr(off,n));off+=n;return true;
    }
    static void serialize_node(const Node* n,std::string& out){
        out.push_back(n->leaf?'L':'I');append_u32(out,(uint32_t)n->keys.size());
        for(auto& r:n->keys){
            append_string(out,r.hash);append_string(out,r.category);
            append_string(out,r.statement);append_string(out,r.proof);
            append_u64(out,r.generation);append_u64(out,r.verified_at);
        }
        if(!n->leaf)for(auto& c:n->children)serialize_node(c.get(),out);
    }
    static std::unique_ptr<Node> deserialize_node(std::string_view p,size_t& off,
                                                    size_t depth,size_t& budget){
        require(depth<64&&budget--,"B-tree decode resource limit");
        require(off<p.size(),"B-tree decode truncated");
        char tag=p[off++];require(tag=='L'||tag=='I',"bad B-tree node tag");
        uint32_t count=0;require(pull_u32(p,off,count)&&count<=MAX_KEYS,"bad B-tree node count");
        auto n=std::make_unique<Node>();n->leaf=tag=='L';
        for(uint32_t i=0;i<count;++i){
            KnowledgeRecord r;
            require(pull_string(p,off,r.hash)&&pull_string(p,off,r.category)&&
                    pull_string(p,off,r.statement)&&pull_string(p,off,r.proof)&&
                    pull_u64(p,off,r.generation)&&pull_u64(p,off,r.verified_at),"B-tree record truncated");
            n->keys.push_back(std::move(r));
        }
        if(!n->leaf)for(uint32_t i=0;i<=count;++i)n->children.push_back(deserialize_node(p,off,depth+1,budget));
        return n;
    }
public:
    KnowledgeTree(){root_=std::make_unique<Node>();}
    size_t size()const{return size_;}
    const KnowledgeRecord* find(const std::string& hash)const{return find_node(root_.get(),hash);}
    bool insert(KnowledgeRecord r){
        require(valid_hex(r.hash),"knowledge hash must be BLAKE3-256 hex");
        require(r.statement.size()<=1048576&&r.proof.size()<=1048576,"record quota");
        if(find(r.hash))return false;
        if(root_->keys.size()==MAX_KEYS){
            auto next=std::make_unique<Node>();next->leaf=false;
            next->children.push_back(std::move(root_));
            split_child(next.get(),0);root_=std::move(next);
        }
        insert_nonfull(root_.get(),std::move(r));++size_;return true;
    }
    std::vector<KnowledgeRecord> ordered()const{
        std::vector<KnowledgeRecord> out;out.reserve(size_);inorder(root_.get(),out);return out;
    }
    bool validate()const{
        size_t leaf_depth=SIZE_MAX,count=0;
        return validate_node(root_.get(),true,0,leaf_depth,nullptr,nullptr,count)&&count==size_;
    }
    bool save(const std::string& path)const{
        require(validate(),"refuse to save invalid B-tree");
        std::string payload="GODELTREE\0"; // magic includes explicit NUL below
        payload.push_back('\0');
        append_u32(payload,kSchema);append_u64(payload,(uint64_t)size_);
        serialize_node(root_.get(),payload);
        auto tag=blake3::digest(payload);
        payload.append((const char*)tag.data(),tag.size());
        return atomic_write(path,payload);
    }
    bool load(const std::string& path){
        std::string data;
        try{data=read_file(path);}catch(...){return false;}
        if(data.size()<10+4+8+32)return false;
        auto hash=blake3::digest(std::string_view(data.data(),data.size()-32));
        if(std::memcmp(hash.data(),data.data()+data.size()-32,32)!=0)return false;
        if(data.compare(0,10,std::string("GODELTREE\0",10))!=0)return false;
        size_t off=10;uint32_t schema=0;uint64_t expected=0;
        if(!pull_u32(data,off,schema)||schema!=kSchema||!pull_u64(data,off,expected)||expected>1000000)return false;
        try{
            size_t budget=(size_t)expected+1;
            auto decoded=deserialize_node(std::string_view(data.data(),data.size()-32),off,0,budget);
            if(off!=data.size()-32)return false;
            KnowledgeTree temp;temp.root_=std::move(decoded);temp.size_=(size_t)expected;
            if(!temp.validate())return false;
            root_=std::move(temp.root_);size_=temp.size_;
            return true;
        }catch(...){return false;}
    }
};
static KnowledgeRecord record_from_certificate(const ProofCertificate& cert,
                                                const std::string& category,
                                                uint64_t generation){
    require(cert.verified,"cannot persist an unverified certificate");
    return {cert.statement_hash,category,cert.evidence,cert.proof_hash,generation,
            (uint64_t)std::chrono::duration_cast<std::chrono::seconds>(
              std::chrono::system_clock::now().time_since_epoch()).count()};
}
// ======================================================================
// SELF-INSPECTION THROUGH CLANG AST AND LLVM TEXTUAL IR
// Hot-swappable native numerical kernels via clang++ + dlopen/dlsym.
//
// This module does NOT claim that the dependent-type kernel proves native
// shared objects correct. The ABI is fixed and the generated replacement
// is selected from known mathematical templates, validated by exhaustive
// tests over finite small matrices and randomly generated inputs.
// Never use its success as an axiom in TrustedKernel.
// ======================================================================
struct ProcessOutput {int status=-1;std::string output;bool timed_out=false;bool truncated=false;};
static ProcessOutput run_process(const std::vector<std::string>& argv,
                                 unsigned timeout_ms=12000,size_t cap=8*1024*1024){
    require(!argv.empty(),"empty command");
    int pipefd[2];require(::pipe2(pipefd,O_CLOEXEC|O_NONBLOCK)==0,"pipe creation failed");
    pid_t child=::fork();
    if(child<0){::close(pipefd[0]);::close(pipefd[1]);throw std::runtime_error("fork failed");}
    if(child==0){
        ::close(pipefd[0]);
        ::dup2(pipefd[1],STDOUT_FILENO);::dup2(pipefd[1],STDERR_FILENO);
        ::close(pipefd[1]);
        struct rlimit cpu{};cpu.rlim_cur=30;cpu.rlim_max=35;::setrlimit(RLIMIT_CPU,&cpu);
        struct rlimit output{};output.rlim_cur=256*1024*1024;output.rlim_max=256*1024*1024;
        ::setrlimit(RLIMIT_FSIZE,&output);
        std::vector<char*> args;args.reserve(argv.size()+1);
        for(auto& s:argv)args.push_back(const_cast<char*>(s.c_str()));
        args.push_back(nullptr);
        ::execvp(args[0],args.data());_exit(127);
    }
    ::close(pipefd[1]);ProcessOutput result;
    auto start=Clock::now();int status=0;bool exited=false,pipe_eof=false;
    while(!exited||!pipe_eof){
        pollfd item{pipefd[0],POLLIN|POLLHUP,0};
        ::poll(&item,1,15);
        char buffer[32768];
        while(true){
            ssize_t n=::read(pipefd[0],buffer,sizeof(buffer));
            if(n>0){
                if(result.output.size()+(size_t)n>cap){result.truncated=true;break;}
                result.output.append(buffer,(size_t)n);
            }else if(n==0){pipe_eof=true;break;}
            else if(errno==EAGAIN||errno==EINTR)break;
            else{pipe_eof=true;break;}
        }
        if(result.truncated){::kill(child,SIGKILL);}
        if(!exited){pid_t rc=::waitpid(child,&status,WNOHANG);if(rc==child)exited=true;}
        auto elapsed=std::chrono::duration_cast<std::chrono::milliseconds>(Clock::now()-start).count();
        if(!exited&&elapsed>timeout_ms){result.timed_out=true;::kill(child,SIGKILL);}
        if(result.truncated||result.timed_out){
            if(!exited){while(::waitpid(child,&status,0)<0&&errno==EINTR){}exited=true;}
            // Pipe is drained after child termination.
        }
    }
    ::close(pipefd[0]);
    if(!exited)while(::waitpid(child,&status,0)<0&&errno==EINTR){}
    result.status=WIFEXITED(status)?WEXITSTATUS(status):-1;return result;
}
struct SourceAstNode{
    std::string kind,name,raw;
    int32_t parent=-1;
    std::vector<int32_t> children;
};
struct SourceGraph{
    std::vector<SourceAstNode> nodes;
    size_t functions=0,methods=0,templates=0;
    std::string digest;
    std::vector<std::string> matching_functions(std::string_view token)const{
        std::vector<std::string> result;
        for(auto& n:nodes)if((n.kind=="FunctionDecl"||n.kind=="CXXMethodDecl")&&
             n.raw.find(token)!=std::string::npos)result.push_back(n.raw);
        return result;
    }
};
static SourceGraph parse_clang_ast_text(std::string_view text,size_t max_nodes=100000){
    SourceGraph graph;std::vector<std::pair<size_t,int32_t>> stack;
    size_t offset=0;
    while(offset<text.size()&&graph.nodes.size()<max_nodes){
        size_t end=text.find('\n',offset);if(end==std::string_view::npos)end=text.size();
        std::string_view line=text.substr(offset,end-offset);offset=end+1;
        size_t begin=line.find_first_not_of(" |`-\\t");if(begin==std::string_view::npos)continue;
        std::string_view value=line.substr(begin);
        size_t kind_end=value.find_first_of(" \t");
        std::string kind(value.substr(0,kind_end));
        if(kind.size()<4||kind.size()>40||
           (kind.find("Decl")==std::string::npos&&kind.find("Expr")==std::string::npos&&
            kind.find("Stmt")==std::string::npos&&kind.find("Type")==std::string::npos))continue;
        size_t indentation=begin;
        while(!stack.empty()&&stack.back().first>=indentation)stack.pop_back();
        int32_t parent=stack.empty()?-1:stack.back().second;
        int32_t id=(int32_t)graph.nodes.size();
        SourceAstNode n;n.kind=kind;n.raw=std::string(value);n.parent=parent;
        if(parent>=0)graph.nodes[(size_t)parent].children.push_back(id);
        if(kind=="FunctionDecl")++graph.functions;
        if(kind=="CXXMethodDecl")++graph.methods;
        if(kind=="FunctionTemplateDecl")++graph.templates;
        graph.nodes.push_back(std::move(n));stack.push_back({indentation,id});
    }
    graph.digest=blake3::hex(text);
    return graph;
}
static SourceGraph inspect_cpp_file(const std::string& filename,
                                    const std::string& filter="godel::"){
    require(filename.size()<PATH_MAX&&filter.size()<200,"source inspection arguments too long");
    auto result=run_process({"clang++","-std=c++17","-fsyntax-only",
        "-Xclang","-ast-dump","-Xclang","-ast-dump-filter="+filter,filename},
        60000,32*1024*1024);
    require(result.status==0&&!result.truncated&&!result.timed_out,
            "Clang AST inspection failed: "+result.output.substr(0,500));
    return parse_clang_ast_text(result.output);
}
static std::string emit_llvm_ir(const std::string& source_path,const std::string& output_path){
    auto result=run_process({"clang++","-std=c++17","-O1","-S","-emit-llvm",
                              source_path,"-o",output_path},90000,1024*1024);
    require(result.status==0&&!result.timed_out,"Clang LLVM IR emission failed: "+result.output.substr(0,500));
    return output_path;
}
using MatrixKernel = void(*)(const double*,const double*,double*,size_t,size_t,size_t);
static void reference_matrix_multiply(const double* A,const double* B,double* C,
                                      size_t rows,size_t cols,size_t inner){
    for(size_t i=0;i<rows;++i)for(size_t j=0;j<cols;++j){
        double sum=0;for(size_t k=0;k<inner;++k)sum+=A[i*inner+k]*B[k*cols+j];
        C[i*cols+j]=sum;
    }
}
static std::string generated_kernel_source(unsigned variant){
    require(variant<4,"invalid JIT template id");
    std::string s="#include <cstddef>\n"
      "extern \"C\" void godel_matrix_kernel(const double* A,const double* B,"
      "double* C,size_t rows,size_t cols,size_t inner){\n";
    if(variant==0){
        s+="for(size_t i=0;i<rows;++i) for(size_t j=0;j<cols;++j){"
           "double sum=0;for(size_t k=0;k<inner;++k)sum+=A[i*inner+k]*B[k*cols+j];"
           "C[i*cols+j]=sum;}\n";
    }else if(variant==1){
        s+="for(size_t i=0;i<rows;++i){size_t j=0;for(;j+3<cols;j+=4){"
           "double a=0,b=0,c=0,d=0;for(size_t k=0;k<inner;++k){"
           "double v=A[i*inner+k];a+=v*B[k*cols+j];b+=v*B[k*cols+j+1];"
           "c+=v*B[k*cols+j+2];d+=v*B[k*cols+j+3];}"
           "C[i*cols+j]=a;C[i*cols+j+1]=b;C[i*cols+j+2]=c;C[i*cols+j+3]=d;}"
           "for(;j<cols;++j){double sum=0;for(size_t k=0;k<inner;++k)"
           "sum+=A[i*inner+k]*B[k*cols+j];C[i*cols+j]=sum;}}\n";
    }else if(variant==2){
        s+="for(size_t i=0;i<rows;i+=8)for(size_t j=0;j<cols;j+=8)"
           "for(size_t ii=i;ii<rows&&ii<i+8;++ii)"
           "for(size_t jj=j;jj<cols&&jj<j+8;++jj){"
           "double sum=0;for(size_t k=0;k<inner;++k)sum+=A[ii*inner+k]*B[k*cols+jj];"
           "C[ii*cols+jj]=sum;}\n";
    }else{
        s+="for(size_t j=0;j<cols;++j)for(size_t i=0;i<rows;++i){"
           "double sum=0;size_t k=0;for(;k+1<inner;k+=2){"
           "sum+=A[i*inner+k]*B[k*cols+j];"
           "sum+=A[i*inner+k+1]*B[(k+1)*cols+j];}"
           "for(;k<inner;++k)sum+=A[i*inner+k]*B[k*cols+j];C[i*cols+j]=sum;}\n";
    }
    s+="}\n";return s;
}
class NativeHotSwap {
    struct DynamicHandle{
        void* so=nullptr;
        MatrixKernel function=nullptr;
        std::string path;
        ~DynamicHandle(){if(so)::dlclose(so);if(!path.empty())::unlink(path.c_str());}
    };
    mutable std::mutex mutex_;
    std::shared_ptr<DynamicHandle> active_;
    std::string source_digest_;
    bool compile_variant(unsigned variant,std::shared_ptr<DynamicHandle>& out,std::string& diagnostic){
        std::string code=generated_kernel_source(variant);
        char src[]="/tmp/godel-kernel-XXXXXX";
        int fd=::mkstemp(src);
        if(fd<0){diagnostic="mkstemp failed";return false;}
        bool written=write_all(fd,code.data(),code.size());::close(fd);
        if(!written){::unlink(src);diagnostic="kernel source write failed";return false;}
        std::string output=std::string(src)+".so";
        auto compiled=run_process({"clang++","-x","c++","-std=c++17","-O3","-fPIC",
                  "-shared",src,"-o",output},30000,2*1024*1024);
        ::unlink(src);
        if(compiled.status!=0||compiled.timed_out){
            diagnostic=compiled.output.substr(0,4000);::unlink(output.c_str());return false;
        }
        void* lib=::dlopen(output.c_str(),RTLD_NOW|RTLD_LOCAL);
        if(!lib){diagnostic=::dlerror();::unlink(output.c_str());return false;}
        auto sym=::dlsym(lib,"godel_matrix_kernel");
        if(!sym){diagnostic="missing exported kernel ABI";::dlclose(lib);::unlink(output.c_str());return false;}
        out=std::make_shared<DynamicHandle>();out->so=lib;out->path=output;
        out->function=reinterpret_cast<MatrixKernel>(sym);
        source_digest_=blake3::hex(code);return true;
    }
    static bool validate(const DynamicHandle& kernel){
        uint64_t seed=0x87abcde;
        for(size_t rows=0;rows<=12;++rows)for(size_t cols=0;cols<=12;++cols)
          for(size_t inner=0;inner<=12;++inner){
            std::vector<double> a(rows*inner),b(inner*cols),expected(rows*cols),actual(rows*cols);
            for(double& x:a)x=(double)((int)(splitmix64(seed)%31)-15)/8.0;
            for(double& x:b)x=(double)((int)(splitmix64(seed)%31)-15)/8.0;
            reference_matrix_multiply(a.data(),b.data(),expected.data(),rows,cols,inner);
            kernel.function(a.data(),b.data(),actual.data(),rows,cols,inner);
            if(actual!=expected)return false;
        }
        return true;
    }
public:
    bool activate(unsigned variant,std::string& error){
        std::shared_ptr<DynamicHandle> next;
        if(!compile_variant(variant,next,error))return false;
        if(!validate(*next)){error="candidate kernel failed reference validation";return false;}
        {std::lock_guard<std::mutex> lock(mutex_);active_.swap(next);}
        // Old native code is dlclose'd only when no call holds its handle.
        return true;
    }
    void multiply(const double* a,const double* b,double* c,size_t m,size_t n,size_t k)const{
        std::shared_ptr<DynamicHandle> handle;
        {std::lock_guard<std::mutex> lock(mutex_);handle=active_;}
        if(handle)handle->function(a,b,c,m,n,k);
        else reference_matrix_multiply(a,b,c,m,n,k);
    }
    bool active()const{std::lock_guard<std::mutex> lock(mutex_);return (bool)active_;}
    void reset(){std::shared_ptr<DynamicHandle> old;{std::lock_guard<std::mutex> lock(mutex_);old.swap(active_);}}
    std::string digest()const{std::lock_guard<std::mutex> lock(mutex_);return source_digest_;}
};
// ======================================================================
// CANONICAL PROOF RECORD PARSING, RE-VALIDATION AFTER RESTART,
// PHYSICAL SENSOR INPUT AS EXACT RATIONAL SAMPLES.
// ======================================================================
static bool split_once(std::string_view input,char delim,std::string_view& a,std::string_view& b){
    size_t pos=input.find(delim);if(pos==std::string_view::npos)return false;
    a=input.substr(0,pos);b=input.substr(pos+1);return true;
}
static uint32_t parse_u32(std::string_view text){
    require(!text.empty()&&text.size()<12,"unsigned integer text invalid");
    uint64_t result=0;
    for(char c:text){require(c>='0'&&c<='9',"unsigned integer non-digit");result=result*10+(c-'0');require(result<=UINT32_MAX,"unsigned overflow");}
    return (uint32_t)result;
}
static Q parse_q(std::string_view text){
    require(!text.empty()&&text.size()<10000,"rational input limit");
    size_t slash=text.find('/');
    if(slash==std::string_view::npos)return Q(Z(std::string(text),10));
    Z numerator(std::string(text.substr(0,slash)),10);
    Z denominator(std::string(text.substr(slash+1)),10);
    require(denominator!=0,"rational denominator cannot be zero");
    Q value(numerator,denominator); value.canonicalize(); return value;
}
static Polynomial parse_canonical_polynomial(std::string_view s){
    require(s.size()>=5&&s.substr(0,2)=="Q[","polynomial header");
    size_t end=s.find("]:");require(end!=std::string_view::npos,"polynomial bracket");
    uint32_t vars=parse_u32(s.substr(2,end-2));require(vars<=16,"polynomial dimension");
    Polynomial p(vars);size_t off=end+2;
    while(off<s.size()){
        require(s[off]=='(',"polynomial term open");++off;
        size_t close=s.find(')',off);require(close!=std::string_view::npos,"polynomial term close");
        std::string_view term=s.substr(off,close-off);
        size_t comma=term.find(',');
        Q coeff=parse_q(comma==std::string_view::npos?term:term.substr(0,comma));
        Monomial m{std::vector<uint16_t>(vars)};
        size_t next=comma==std::string_view::npos?term.size():comma+1;
        for(uint32_t i=0;i<vars;++i){
            require(next<term.size(),"monomial arity truncated");
            size_t stop=term.find(',',next);
            if(stop==std::string_view::npos)stop=term.size();
            uint32_t e=parse_u32(term.substr(next,stop-next));
            require(e<=65535,"monomial exponent");m.powers[i]=(uint16_t)e;
            next=stop==term.size()?term.size():stop+1;
        }
        require(next==term.size(),"extra monomial coordinates");
        p.add_monomial(m,coeff);off=close+1;
    }
    require(p.canonical()==s,"noncanonical polynomial encoding");return p;
}
struct ExactObservation{
    std::vector<Q> state;
    std::vector<Q> time_derivative;
};
static std::vector<std::string> csv_fields(const std::string& line){
    // Deliberately restrict sensors to unquoted numeric CSV. Reject quoted
    // fields to avoid pretending to implement the full RFC4180 grammar.
    require(line.find('"')==std::string::npos,"quoted CSV not supported");
    std::vector<std::string> result;size_t pos=0;
    while(true){size_t comma=line.find(',',pos);
        if(comma==std::string::npos){result.push_back(line.substr(pos));break;}
        result.push_back(line.substr(pos,comma-pos));pos=comma+1;
    }
    for(auto& field:result){
        size_t left=field.find_first_not_of(" \t\r");
        if(left==std::string::npos){field.clear();continue;}
        size_t right=field.find_last_not_of(" \t\r");field=field.substr(left,right-left+1);
    }
    return result;
}
static Q parse_decimal_exact(std::string s){
    require(s.size()<20000&& !s.empty(),"sensor decimal length");
    auto slash=s.find('/');if(slash!=std::string::npos)return Q(s);
    size_t point=s.find('.');if(point==std::string::npos)return Q(s);
    std::string digits=s.substr(0,point)+s.substr(point+1);
    size_t decimals=s.size()-point-1;
    require(decimals<10000,"sensor decimal precision quota");
    Z numerator(digits,10);Z denominator=1;
    for(size_t i=0;i<decimals;++i)denominator*=10;
    Q result(numerator,denominator); result.canonicalize(); return result;
}
static std::vector<ExactObservation> read_sensor_csv(const std::string& path,size_t pairs){
    require(pairs>0&&pairs<=8,"sensor pairs quota");
    std::string content=read_file(path,4*1024*1024);
    std::istringstream input(content);std::string line;
    std::vector<ExactObservation> observations;
    while(std::getline(input,line)){
        if(line.empty()||line[0]=='#')continue;
        auto fields=csv_fields(line);
        require(fields.size()==4*pairs,"sensor data requires q,p,dq,dp columns");
        ExactObservation x;
        for(size_t i=0;i<2*pairs;++i)x.state.push_back(parse_decimal_exact(fields[i]));
        for(size_t i=0;i<2*pairs;++i)x.time_derivative.push_back(parse_decimal_exact(fields[2*pairs+i]));
        observations.push_back(std::move(x));
        require(observations.size()<=10000,"sensor sample quota");
    }
    require(!observations.empty(),"no sensor observations");return observations;
}
// Fit quadratic H from Hamilton's equations using exact linear algebra.
// Coefficients are Q-vector for symmetric A and b. Underdetermined systems
// choose their free coordinates to zero. Reject contradictory data.
static std::optional<QuadraticHamiltonian> infer_quadratic_hamiltonian(
    const std::vector<ExactObservation>& samples,size_t pairs){
    if(samples.empty()||pairs==0||pairs>8)return std::nullopt;
    size_t d=2*pairs;
    size_t triangle=d*(d+1)/2;
    size_t unknown=triangle+d;
    std::vector<std::pair<size_t,size_t>> pairs_index;
    for(size_t i=0;i<d;++i)for(size_t j=i;j<d;++j)pairs_index.push_back({i,j});
    std::vector<std::vector<Q>> rows;
    for(auto& sample:samples){
        require(sample.state.size()==d&&sample.time_derivative.size()==d,"sensor dimension");
        for(size_t coordinate=0;coordinate<d;++coordinate){
            size_t grad_index=coordinate<pairs?coordinate+pairs:coordinate-pairs;
            Q sign=coordinate<pairs?Q(1):Q(-1);
            std::vector<Q> row(unknown+1,0);
            for(size_t j=0;j<triangle;++j){
                auto [a,b]=pairs_index[j];
                if(a==grad_index)row[j]+=sign*sample.state[b];
                if(b==grad_index&&b!=a)row[j]+=sign*sample.state[a];
            }
            row[triangle+grad_index]=sign;
            row[unknown]=sample.time_derivative[coordinate];
            rows.push_back(std::move(row));
        }
    }
    auto rref=row_reduce(std::move(rows),unknown+1);
    for(auto& row:rref.matrix){
        bool all_zero=true;for(size_t j=0;j<unknown;++j)if(row[j]!=0){all_zero=false;break;}
        if(all_zero&&row[unknown]!=0)return std::nullopt;
    }
    std::vector<Q> coeff(unknown,0);
    for(size_t row=0;row<rref.pivot_columns.size();++row){
        size_t pivot=rref.pivot_columns[row];if(pivot<unknown)coeff[pivot]=rref.matrix[row][unknown];
    }
    QuadraticHamiltonian H(pairs);
    for(size_t j=0;j<triangle;++j){auto [a,b]=pairs_index[j];H.A[a][b]=H.A[b][a]=coeff[j];}
    for(size_t i=0;i<d;++i)H.b[i]=coeff[triangle+i];
    auto p=H.to_polynomial();
    for(auto& sample:samples){
        for(size_t i=0;i<d;++i){
            Polynomial flow=(i<pairs?p.derivative(i+pairs):-p.derivative(i-pairs));
            if(flow.evaluate(sample.state)!=sample.time_derivative[i])return std::nullopt;
        }
    }
    return H;
}

// Expression string parser used by the executable theorem corpus.
// Grammar: expression := product (('+'|'-') product)*
//          product := power ('*' power)*
//          power := unary ('^' positive_integer)?
//          unary := '-' unary | atom
//          atom := integer | fraction | xN | '(' expression ')'
#include "program_parser.hpp"
#include "lean_export.hpp"
#include "shared_memory.hpp"

static bool revalidate_record(const KnowledgeRecord& record,TrustedKernel& kernel){
    try{
        std::string category=record.category;
        if(category=="noether"){
            std::string_view left,right;
            require(split_once(record.statement,'|',left,right),"Noether archive statement structure");
            Polynomial I=parse_canonical_polynomial(left),H=parse_canonical_polynomial(right);
            auto cert=certify_noether(kernel,I,H);
            return cert.statement_hash==record.hash&&cert.proof_hash==record.proof;
        }
        if(category=="ast-improvement"){
            std::string_view prefix,vars,oldexpr,newexpr,oldcost,newcost,ring_hash,rest;
            require(split_once(record.statement,'|',prefix,rest)&&(prefix=="ASTv1"||prefix=="ASTv2"),"AST cert header");
            require(split_once(rest,'|',vars,rest)&&split_once(rest,'|',oldexpr,rest)&&
                    split_once(rest,'|',newexpr,rest)&&split_once(rest,'|',oldcost,rest)&&
                    split_once(rest,'|',newcost,ring_hash),"AST certificate structure");
            size_t count=parse_u32(vars);
            require(count>0&&count<=16,"AST certificate variable arity");
            ExpressionGraph graph;
            auto a=AlgebraParser(graph,oldexpr,count).parse();
            auto b=AlgebraParser(graph,newexpr,count).parse();
            require(graph.static_cost(a)==parse_u32(oldcost)&&
                    graph.static_cost(b)==parse_u32(newcost),"AST certificate fabricated costs");
            auto cert=certify_graph_improvement(kernel,graph,a,b,count);
            require(cert.evidence==record.statement,"AST certificate changed after normalization");
            return cert.statement_hash==record.hash&&cert.proof_hash==record.proof;
        }
        return false;
    }catch(...){return false;}
}
static std::vector<KnowledgeRecord> revalidate_archive(KnowledgeTree& store,
                                                        TrustedKernel& kernel){
    std::vector<KnowledgeRecord> accepted;
    for(auto& r:store.ordered())if(revalidate_record(r,kernel))accepted.push_back(r);
    return accepted;
}
// ======================================================================
// REGRESSION TESTS: TRUSTED COMPUTATIONS, TYPE SAFETY, ALGEBRA,
// DYNAMICS, GRAPH SEARCH, PERMANENT MEMORY, OPTIONAL NATIVE JIT.
// ======================================================================
struct TestRunner{
    unsigned passed=0,failed=0;
    void check(bool ok,const std::string& message){
        if(ok){++passed;}
        else{++failed;std::cerr<<"[FAIL] "<<message<<"\n";}
    }
    template<class F> void rejects(F&& f,const std::string& message){
        bool rejected=false;try{f();}catch(const std::exception&){rejected=true;}
        check(rejected,message);
    }
    void section(const std::string& name){std::cerr<<"[TEST] "<<name<<"\n";}
    int result()const{
        std::cout<<"[TEST] passed="<<passed<<" failed="<<failed<<"\n";
        return failed?1:0;
    }
};
static void test_blake(TestRunner& t){
    t.section("BLAKE3 known official vectors");
    t.check(blake3::hex("")=="af1349b9f5f9a1a6a0404dea36dcc9499bcb25c9adc112b7cc9a93cae41f3262","BLAKE3 empty vector");
    t.check(blake3::hex("abc")=="6437b3ac38465133ffb63b75273a8db548c558465d79db03fd359c6cd5bd9d85","BLAKE3 abc vector");
    t.check(blake3::hex(std::string(10000,'x'))==blake3::hex(std::string(10000,'x')),"BLAKE3 large deterministic tree");
    t.check(blake3::hex(std::string(1024,'x'))!=blake3::hex(std::string(1025,'x')),"BLAKE3 chunk boundary");
}
static void test_polynomials(TestRunner& t){
    t.section("GMP polynomial arithmetic and canonical encoding");
    Polynomial x=Polynomial::variable(2,0),y=Polynomial::variable(2,1);
    auto half=Q(1,2),third=Q(1,3);
    auto a=x*half+y*third;
    t.check(a.derivative(0)==Polynomial::constant(2,half),"partial derivative q");
    t.check(a.derivative(1)==Polynomial::constant(2,third),"partial derivative p");
    t.check((x+y).pow(2)==x*x+(x*y)*Q(2)+y*y,"binomial polynomial identity");
    t.check((x-y)*(x+y)==x*x-y*y,"difference of squares");
    t.check(a.evaluate({Q(6),Q(3)})==Q(4),"GMP exact rational evaluation");
    t.check((x*0).is_zero(),"zero eliminates exact coefficient");
    t.check(parse_canonical_polynomial(a.canonical())==a,"canonical polynomial round trip");
    t.rejects([&]{(void)(x*Polynomial::variable(3,0));},"reject nonmatching arity");
    t.rejects([&]{(void)rational(1,0);},"reject zero denominator");
    t.rejects([&]{(void)parse_canonical_polynomial("Q[2]:(1,0)");},"reject malformed monomial");
    Z large=1;for(int i=0;i<250;++i)large*=10;
    t.check((Polynomial::constant(2,Q(large))*Polynomial::constant(2,Q(large))).constant_value()==Q(large*large),
            "arbitrary precision GMP without int64 overflow");
}
static void test_linear_algebra(TestRunner& t){
    t.section("exact RREF and nullspace");
    auto matrix=std::vector<std::vector<Q>>{{1,1,1},{2,2,2}};
    auto reduced=row_reduce(matrix,3);
    t.check(reduced.rank()==1,"RREF rank");
    auto kernel=reduced.nullspace();t.check(kernel.size()==2,"RREF nullity");
    for(auto& vector:kernel){
        Q residual=0;for(int j=0;j<3;++j)residual+=vector[j];
        t.check(residual==0,"nullspace witness exact");
    }
    auto solution=solve_exact_linear({{2,1},{1,3}},{7,11});
    t.check(2*solution[0]+solution[1]==7&&solution[0]+3*solution[1]==11,"exact Gaussian solve");
    t.rejects([&]{(void)solve_exact_linear({{0,0},{0,0}},{1,1});},"reject singular system");
}
static void test_trusted_kernel(TestRunner& t){
    t.section("dependent type checking and rejection of invalid witnesses");
    TrustedKernel K;
    auto type=K.rational_type(),zero=K.universe(0);
    t.check(K.convertible(K.infer(type),zero),"Q : Universe 0");
    auto id=K.lambda(type,K.var(0));
    auto inferred=K.infer(id);
    auto expected=K.pi(type,type);
    t.check(K.convertible(inferred,expected),"dependent lambda identity : Pi(Q,Q)");
    auto universe=K.universe(0);
    auto poly_id=K.lambda(universe,K.lambda(K.var(0),K.var(0)));
    auto poly_type=K.pi(universe,K.pi(K.var(0),K.var(1)));
    t.check(K.convertible(K.infer(poly_id),poly_type),
            "genuinely dependent polymorphic identity: Pi(A:U0),Pi(x:A),A");
    t.rejects([&]{(void)K.infer(K.app(id,type));},"ill-typed application never accepted");
    auto refl=K.refl(type);
    t.check(K.convertible(K.infer(refl),K.equality(type,type)),"equality reflexivity");
    auto ring_a=Polynomial::variable(1,0),ring_b=ring_a+Polynomial::constant(1,0);
    auto lhs=K.polynomial(ring_a),rhs=K.polynomial(ring_b);
    auto identity=K.ring_identity(lhs,rhs);
    K.check(K.ring_witness(),identity);
    t.check(true,"universally quantified polynomial identity verified");
    auto wrong=K.polynomial(ring_a+Polynomial::constant(1,1));
    t.rejects([&]{K.check(K.ring_witness(),K.ring_identity(lhs,wrong));},"reject false ring theorem");
    K.check(K.cost_witness(),K.cost_prop(50,40));
    t.rejects([&]{K.check(K.cost_witness(),K.cost_prop(40,50));},"reject non-improving cost model");
    t.rejects([&]{K.check(K.cost_witness(),K.cost_prop(40,40));},"reject equal cost model");
    auto prop=K.ring_identity(lhs,rhs),cost=K.cost_prop(20,10);
    K.check(K.pair(K.ring_witness(),K.cost_witness()),K.sigma(prop,cost));
    t.check(true,"Curry-Howard conjunction via dependent pair");
    t.rejects([&]{K.infer(K.var(1));},"reject unbound de Bruijn variable");
    t.rejects([&]{K.infer(K.app(type,type));},"reject application of nonfunction");
    t.rejects([&]{K.infer(K.universe(32));},"reject universe escape");
    auto gc=K.collect();t.check(gc>0,"semantic GC collected temporary theorem nodes");
}
static void test_noether(TestRunner& t){
    t.section("symplectic invariants and implicit midpoint integrator");
    auto q=Polynomial::variable(2,0),p=Polynomial::variable(2,1);
    auto H=(q*q+p*p)*Q(1,2);
    t.check(poisson(H,H).is_zero(),"antisymmetry of Poisson bracket");
    t.check(poisson(q,p)==Polynomial::constant(2,1),"canonical {q,p}=1");
    t.check(poisson(p,q)==Polynomial::constant(2,-1),"canonical {p,q}=-1");
    t.check(poisson(q,H)==p,"Hamilton equation dq/dt = p");
    t.check(poisson(p,H)==-q,"Hamilton equation dp/dt = -q");
    auto invariants=discover_polynomial_invariants(H,3);
    t.check(!invariants.empty(),"discover nonconstant polynomial invariant");
    t.check(invariants.size()==1,"H and H^2 must not be counted as independent invariants");
    t.check(invariants[0].functionally_independent&&!invariants[0].jacobian_witness.empty(),
            "Jacobian rank produces exact witness of functional independence");
    TrustedKernel K;
    for(auto& hit:invariants){
        t.check(poisson(hit.invariant,H).is_zero(),"Noether candidate symbolic bracket zero");
        auto certificate=certify_noether(K,hit.invariant,H);
        t.check(certificate.verified,"Noether proof independently checked");
    }
    QuadraticHamiltonian quadratic(1);quadratic.A[0][0]=1;quadratic.A[1][1]=1;
    std::vector<Q> x{Q(1),Q(0)};
    for(int i=0;i<20;++i){
        auto next=symplectic_midpoint(quadratic,x,Q(1,10));
        t.check(H.evaluate(next)==H.evaluate(x),"implicit midpoint exactly conserves quadratic energy");
        x=std::move(next);
    }
    t.rejects([&]{(void)poisson(Polynomial::variable(3,0),Polynomial::variable(3,1));},
              "reject odd-dimensional symplectic data");
}
static void test_ast_and_mcts(TestRunner& t){
    t.section("expression AST, semantic graph rewrites and MCTS");
    ExpressionGraph g;
    auto x=g.variable(0),y=g.variable(1);
    auto id=g.multiply(g.add(x,g.constant(0)),g.add(y,g.constant(1)));
    auto root=g.add(id,g.multiply(g.constant(0),x));
    t.check(g.polynomial(root,2)==g.polynomial(id,2),"AST algebraic semantics");
    auto actions=applicable_rewrites(g,root);
    t.check(!actions.empty(),"AST rewrite enumeration");
    auto before_cost=g.static_cost(root);
    GraphNeuralNetwork neural;auto features=neural.encode(g,root);
    t.check(finite_float(features.value),"GNN finite value head");
    TrustedKernel K;
    auto report=mcts_optimize(g,neural,K,root,2,160);
    t.check(report.best_cost<before_cost,"MCTS finds genuine smaller AST");
    t.check(g.polynomial(report.best_root,2)==g.polynomial(root,2),"symbolic equivalence for all rational inputs");
    t.check(report.certificate.has_value()&&report.certificate->verified,"Curry-Howard proof for accepted search move");
    t.check(neural.updates()>0,"online GNN policy/value training");
    g.protect(report.best_root);t.check(g.collect()>0,"AST graph semantic mark sweep");
    t.rejects([&]{g.at(-1);},"AST pointer validation");
    t.rejects([&]{g.power(report.best_root,129);},"AST exponent limit");
}
static void test_knowledge(TestRunner& t){
    t.section("B-tree insertion, split, persistence and corruption checks");
    KnowledgeTree db;
    for(int i=0;i<200;++i){
        std::string content="theorem-record-"+std::to_string(i);
        auto hash=blake3::hex(content);
        t.check(db.insert({hash,"test",content,"proof-"+std::to_string(i),0,0}),"insert distinct hash");
        t.check(db.find(hash)!=nullptr,"B-tree lookup");
    }
    t.check(db.size()==200&&db.validate(),"B-tree order and depth invariants");
    t.check(!db.insert({blake3::hex("theorem-record-0"),"test","duplicate","",0,0}),"B-tree transposition deduplication");
    char temporary[]="/tmp/godel-knowledge-test-XXXXXX";
    int fd=::mkstemp(temporary);require(fd>=0,"temporary database file");::close(fd);
    t.check(db.save(temporary),"atomic authenticated B-tree snapshot");
    KnowledgeTree restored;t.check(restored.load(temporary),"B-tree snapshot reload");
    t.check(restored.validate()&&restored.size()==200,"B-tree restored structural invariants");
    auto contents=read_file(temporary);contents[contents.size()/2]^=1;
    t.check(atomic_write(temporary,contents),"test corruption injection");
    KnowledgeTree invalid;t.check(!invalid.load(temporary),"BLAKE3 rejects modified snapshot");
    ::unlink(temporary);
}
static void test_sensor(TestRunner& t){
    t.section("rational sensor inversion and exact physical model fitting");
    std::vector<ExactObservation> samples;
    for(int i=-6;i<=6;++i)for(int j=-6;j<=6;++j){
        Q q(i),p(j);
        samples.push_back({{q,p},{p,-q}});
    }
    auto fitted=infer_quadratic_hamiltonian(samples,1);
    t.check(fitted.has_value(),"infer exact quadratic Hamiltonian from q,p,dq,dp");
    if(fitted){
        auto H=fitted->to_polynomial();
        t.check(poisson(H,H).is_zero(),"inferred model has exact conservation law");
        t.check(!discover_polynomial_invariants(H,2).empty(),"Noether on inferred Hamiltonian");
    }
    samples[0].time_derivative[0]+=Q(1);
    t.check(!infer_quadratic_hamiltonian(samples,1).has_value(),"reject inconsistent observation");
    t.check(parse_decimal_exact("0.125")==Q(1,8),"decimal sensor parsed without rounding");
    t.check(parse_decimal_exact("-3.50")==Q(-7,2),"negative exact decimal sensor");
    t.rejects([&]{(void)parse_decimal_exact("1.0.3");},"reject malformed sensor value");
}
static void test_certificate_replay(TestRunner& t){
    t.section("AST certificate binding and reboot revalidation");
    ExpressionGraph graph;TrustedKernel kernel;
    auto x=graph.variable(0),y=graph.variable(1);
    auto original=graph.multiply(graph.add(x,graph.constant(0)),graph.add(y,graph.constant(1)));
    auto optimized=graph.multiply(x,graph.add(y,graph.constant(1)));
    auto cert=certify_graph_improvement(kernel,graph,original,optimized,2);
    auto record=record_from_certificate(cert,"ast-improvement",5);
    t.check(revalidate_record(record,kernel),"proof reconstructs real AST after restart");
    auto tampered=record;tampered.statement+="|fabricated";
    t.check(!revalidate_record(tampered,kernel),"cannot replay altered AST certificate");
    tampered=record;tampered.proof[1]='0';
    t.check(!revalidate_record(tampered,kernel),"cannot forge BLAKE3-attested proof");
    auto same=graph.multiply(x,graph.add(y,graph.constant(1)));
    t.rejects([&]{(void)certify_graph_improvement(kernel,graph,same,same,2);},
              "no improvement when AST costs are equal");
}
static void test_clang_graph(TestRunner& t){
    t.section("Clang AST text graph and native hot-swap");
    std::string sample="|-FunctionDecl 0x1 function1\n| `-ParmVarDecl 0x2 value\n"
                       "`-FunctionDecl 0x3 function2\n  `-ReturnStmt 0x4\n";
    auto graph=parse_clang_ast_text(sample);
    t.check(graph.functions==2,"two Clang FunctionDecl graph nodes");
    t.check(!graph.nodes.empty()&&graph.digest.size()==64,"Clang graph content digest");
    std::string error;NativeHotSwap hot;
    t.check(hot.activate(1,error),"clang++ compiles and dlopen loads optimized kernel: "+error);
    if(hot.active()){
        double A[]={1,2,3,4},B[]={5,6,7,8},C[4]={};
        hot.multiply(A,B,C,2,2,2);
        t.check(C[0]==19&&C[1]==22&&C[2]==43&&C[3]==50,"hot-swapped matrix operation");
        std::string old_digest=hot.digest();
        t.check(hot.activate(2,error),"atomic function pointer hot swap: "+error);
        t.check(hot.digest()!=old_digest,"new plugin source version activated");
    }
    hot.reset();t.check(!hot.active(),"restore built-in kernel without losing machine state");
}
// ======================================================================
// EXPLICIT, GENERATED UNIVERSAL-IDENTITY REGRESSION CORPUS
// Every entry is independently parsed into expression trees, normalized
// over the GMP rational polynomial ring, and validated through a trusted
// RingWitness. False entries MUST fail type checking. These entries are
// not training labels that can override the kernel's proof decision.
// ======================================================================
struct SymbolicCase {
    const char* id;
    const char* lhs;
    const char* rhs;
    uint8_t variables;
    bool universally_equal;
    const char* family;
};
static constexpr SymbolicCase kRegressionCatalog[]={
    {
        "RING_00000",
        "(x0+(-14))*(x1+(-15))",
        "x0*x1+(-15)*x0+(-14)*x1+(210)",
        3,
        true,
        "distributivity"
    },
    {
        "RING_00001",
        "(x0+(-7))^2",
        "x0^2+(-14)*x0+(49)",
        3,
        true,
        "binomial-square"
    },
    {
        "RING_00002",
        "(x0+(0))^3",
        "x0^3+(0)*x0^2+(0)*x0+(0)",
        3,
        true,
        "binomial-cube"
    },
    {
        "RING_00003",
        "(x0+(7))*(x1+(-13))",
        "(x1+(-13))*(x0+(7))",
        3,
        true,
        "commutativity"
    },
    {
        "RING_00004",
        "(x0+x1)+(x2+(12))",
        "x0+(x1+(x2+(12)))",
        3,
        true,
        "associativity"
    },
    {
        "RING_00005",
        "x0*x2+x1*x2+(-8)*x2",
        "(x0+x1+(-8))*x2",
        3,
        true,
        "factorization"
    },
    {
        "RING_00006",
        "(x0+(-1))*(x1+(-11))-(-11)*x0-(-1)*x1-(11)",
        "x0*x1",
        3,
        true,
        "cancellation"
    },
    {
        "RING_00007",
        "((x0+0)*(x1+1))+((x2*0)+(6)-(6))",
        "x0*x1+x0",
        3,
        true,
        "neutral-elements"
    },
    {
        "RING_00008",
        "x0*(x1+(13))-(13)*x0",
        "x0*x1",
        3,
        true,
        "distribute-cancel"
    },
    {
        "RING_00009",
        "((x0+(-9))+x1)*((x0+(-9))-x1)",
        "(x0+(-9))^2-x1^2",
        3,
        true,
        "difference-of-squares"
    },
    {
        "RING_00010",
        "(x0+(-2))^2-(x0^2+(-4)*x0+(4))",
        "0",
        3,
        true,
        "algebraic-zero"
    },
    {
        "RING_00011",
        "(x0+(5))^2",
        "x0^2+(10)*x0+(26)",
        3,
        false,
        "false-binomial"
    },
    {
        "RING_00012",
        "(x0+(12))*(x0-(12))",
        "x0^2-(144)",
        3,
        true,
        "conjugates"
    },
    {
        "RING_00013",
        "(x0+x1+(x2+(-6)))^2",
        "x0^2+x1^2+(x2+(-6))^2+2*x0*x1+2*x0*(x2+(-6))+2*x1*(x2+(-6))",
        3,
        true,
        "multivariate-square"
    },
    {
        "RING_00014",
        "((x0+(-3))^2)*(x1+(15))",
        "(x0^2+(-6)*x0+(9))*(x1+(15))",
        3,
        true,
        "product-squared"
    },
    {
        "RING_00015",
        "(4)*x0+(-5)*x0+(-7)*x0+(-7)*x0",
        "(-15)*x0",
        3,
        true,
        "coefficient-aggregation"
    },
    {
        "RING_00016",
        "(11)*(x0+x1+x2)^2",
        "(11)*(x0^2+x1^2+x2^2+2*x0*x1+2*x0*x2+2*x1*x2)",
        3,
        true,
        "quadratic-form"
    },
    {
        "RING_00017",
        "(x0+(-11))*(x1+(-14))",
        "x0*x1+(-14)*x0+(-11)*x1+(154)",
        3,
        true,
        "distributivity"
    },
    {
        "RING_00018",
        "(x0+(-4))^2",
        "x0^2+(-8)*x0+(16)",
        3,
        true,
        "binomial-square"
    },
    {
        "RING_00019",
        "(x0+(3))^3",
        "x0^3+(9)*x0^2+(27)*x0+(27)",
        3,
        true,
        "binomial-cube"
    },
    {
        "RING_00020",
        "(x0+(10))*(x1+(-12))",
        "(x1+(-12))*(x0+(10))",
        3,
        true,
        "commutativity"
    },
    {
        "RING_00021",
        "(x0+x1)+(x2+(-10))",
        "x0+(x1+(x2+(-10)))",
        3,
        true,
        "associativity"
    },
    {
        "RING_00022",
        "x0*x2+x1*x2+(-5)*x2",
        "(x0+x1+(-5))*x2",
        3,
        true,
        "factorization"
    },
    {
        "RING_00023",
        "(x0+(2))*(x1+(-10))-(-10)*x0-(2)*x1-(-20)",
        "x0*x1",
        3,
        true,
        "cancellation"
    },
    {
        "RING_00024",
        "((x0+0)*(x1+1))+((x2*0)+(9)-(9))",
        "x0*x1+x0",
        3,
        true,
        "neutral-elements"
    },
    {
        "RING_00025",
        "x0*(x1+(-13))-(-13)*x0",
        "x0*x1",
        3,
        true,
        "distribute-cancel"
    },
    {
        "RING_00026",
        "((x0+(-6))+x1)*((x0+(-6))-x1)",
        "(x0+(-6))^2-x1^2",
        3,
        true,
        "difference-of-squares"
    },
    {
        "RING_00027",
        "(x0+(1))^2-(x0^2+(2)*x0+(1))",
        "0",
        3,
        true,
        "algebraic-zero"
    },
    {
        "RING_00028",
        "(x0+(8))^2",
        "x0^2+(16)*x0+(65)",
        3,
        false,
        "false-binomial"
    },
    {
        "RING_00029",
        "(x0+(-14))*(x0-(-14))",
        "x0^2-(196)",
        3,
        true,
        "conjugates"
    },
    {
        "RING_00030",
        "(x0+x1+(x2+(-1)))^2",
        "x0^2+x1^2+(x2+(-1))^2+2*x0*x1+2*x0*(x2+(-1))+2*x1*(x2+(-1))",
        3,
        true,
        "multivariate-square"
    },
    {
        "RING_00031",
        "((x0+(0))^2)*(x1+(-15))",
        "(x0^2+(0)*x0+(0))*(x1+(-15))",
        3,
        true,
        "product-squared"
    },
    {
        "RING_00032",
        "(7)*x0+(-4)*x0+(-2)*x0+(7)*x0",
        "(8)*x0",
        3,
        true,
        "coefficient-aggregation"
    },
    {
        "RING_00033",
        "(14)*(x0+x1+x2)^2",
        "(14)*(x0^2+x1^2+x2^2+2*x0*x1+2*x0*x2+2*x1*x2)",
        3,
        true,
        "quadratic-form"
    },
    {
        "RING_00034",
        "(x0+(-8))*(x1+(-13))",
        "x0*x1+(-13)*x0+(-8)*x1+(104)",
        3,
        true,
        "distributivity"
    },
    {
        "RING_00035",
        "(x0+(-1))^2",
        "x0^2+(-2)*x0+(1)",
        3,
        true,
        "binomial-square"
    },
    {
        "RING_00036",
        "(x0+(6))^3",
        "x0^3+(18)*x0^2+(108)*x0+(216)",
        3,
        true,
        "binomial-cube"
    },
    {
        "RING_00037",
        "(x0+(13))*(x1+(-11))",
        "(x1+(-11))*(x0+(13))",
        3,
        true,
        "commutativity"
    },
    {
        "RING_00038",
        "(x0+x1)+(x2+(-5))",
        "x0+(x1+(x2+(-5)))",
        3,
        true,
        "associativity"
    },
    {
        "RING_00039",
        "x0*x2+x1*x2+(-2)*x2",
        "(x0+x1+(-2))*x2",
        3,
        true,
        "factorization"
    },
    {
        "RING_00040",
        "(x0+(5))*(x1+(-9))-(-9)*x0-(5)*x1-(-45)",
        "x0*x1",
        3,
        true,
        "cancellation"
    },
    {
        "RING_00041",
        "((x0+0)*(x1+1))+((x2*0)+(12)-(12))",
        "x0*x1+x0",
        3,
        true,
        "neutral-elements"
    },
    {
        "RING_00042",
        "x0*(x1+(-10))-(-10)*x0",
        "x0*x1",
        3,
        true,
        "distribute-cancel"
    },
    {
        "RING_00043",
        "((x0+(-3))+x1)*((x0+(-3))-x1)",
        "(x0+(-3))^2-x1^2",
        3,
        true,
        "difference-of-squares"
    },
    {
        "RING_00044",
        "(x0+(4))^2-(x0^2+(8)*x0+(16))",
        "0",
        3,
        true,
        "algebraic-zero"
    },
    {
        "RING_00045",
        "(x0+(11))^2",
        "x0^2+(22)*x0+(122)",
        3,
        false,
        "false-binomial"
    },
    {
        "RING_00046",
        "(x0+(-11))*(x0-(-11))",
        "x0^2-(121)",
        3,
        true,
        "conjugates"
    },
    {
        "RING_00047",
        "(x0+x1+(x2+(4)))^2",
        "x0^2+x1^2+(x2+(4))^2+2*x0*x1+2*x0*(x2+(4))+2*x1*(x2+(4))",
        3,
        true,
        "multivariate-square"
    },
    {
        "RING_00048",
        "((x0+(3))^2)*(x1+(-14))",
        "(x0^2+(6)*x0+(9))*(x1+(-14))",
        3,
        true,
        "product-squared"
    },
    {
        "RING_00049",
        "(10)*x0+(-3)*x0+(3)*x0+(-4)*x0",
        "(6)*x0",
        3,
        true,
        "coefficient-aggregation"
    },
    {
        "RING_00050",
        "(-12)*(x0+x1+x2)^2",
        "(-12)*(x0^2+x1^2+x2^2+2*x0*x1+2*x0*x2+2*x1*x2)",
        3,
        true,
        "quadratic-form"
    },
    {
        "RING_00051",
        "(x0+(-5))*(x1+(-12))",
        "x0*x1+(-12)*x0+(-5)*x1+(60)",
        3,
        true,
        "distributivity"
    },
    {
        "RING_00052",
        "(x0+(2))^2",
        "x0^2+(4)*x0+(4)",
        3,
        true,
        "binomial-square"
    },
    {
        "RING_00053",
        "(x0+(9))^3",
        "x0^3+(27)*x0^2+(243)*x0+(729)",
        3,
        true,
        "binomial-cube"
    },
    {
        "RING_00054",
        "(x0+(-13))*(x1+(-10))",
        "(x1+(-10))*(x0+(-13))",
        3,
        true,
        "commutativity"
    },
    {
        "RING_00055",
        "(x0+x1)+(x2+(0))",
        "x0+(x1+(x2+(0)))",
        3,
        true,
        "associativity"
    },
    {
        "RING_00056",
        "x0*x2+x1*x2+(1)*x2",
        "(x0+x1+(1))*x2",
        3,
        true,
        "factorization"
    },
    {
        "RING_00057",
        "(x0+(8))*(x1+(-8))-(-8)*x0-(8)*x1-(-64)",
        "x0*x1",
        3,
        true,
        "cancellation"
    },
    {
        "RING_00058",
        "((x0+0)*(x1+1))+((x2*0)+(-14)-(-14))",
        "x0*x1+x0",
        3,
        true,
        "neutral-elements"
    },
    {
        "RING_00059",
        "x0*(x1+(-7))-(-7)*x0",
        "x0*x1",
        3,
        true,
        "distribute-cancel"
    },
    {
        "RING_00060",
        "((x0+(0))+x1)*((x0+(0))-x1)",
        "(x0+(0))^2-x1^2",
        3,
        true,
        "difference-of-squares"
    },
    {
        "RING_00061",
        "(x0+(7))^2-(x0^2+(14)*x0+(49))",
        "0",
        3,
        true,
        "algebraic-zero"
    },
    {
        "RING_00062",
        "(x0+(14))^2",
        "x0^2+(28)*x0+(197)",
        3,
        false,
        "false-binomial"
    },
    {
        "RING_00063",
        "(x0+(-8))*(x0-(-8))",
        "x0^2-(64)",
        3,
        true,
        "conjugates"
    },
    {
        "RING_00064",
        "(x0+x1+(x2+(9)))^2",
        "x0^2+x1^2+(x2+(9))^2+2*x0*x1+2*x0*(x2+(9))+2*x1*(x2+(9))",
        3,
        true,
        "multivariate-square"
    },
    {
        "RING_00065",
        "((x0+(6))^2)*(x1+(-13))",
        "(x0^2+(12)*x0+(36))*(x1+(-13))",
        3,
        true,
        "product-squared"
    },
    {
        "RING_00066",
        "(13)*x0+(-2)*x0+(8)*x0+(10)*x0",
        "(29)*x0",
        3,
        true,
        "coefficient-aggregation"
    },
    {
        "RING_00067",
        "(-9)*(x0+x1+x2)^2",
        "(-9)*(x0^2+x1^2+x2^2+2*x0*x1+2*x0*x2+2*x1*x2)",
        3,
        true,
        "quadratic-form"
    },
    {
        "RING_00068",
        "(x0+(-2))*(x1+(-11))",
        "x0*x1+(-11)*x0+(-2)*x1+(22)",
        3,
        true,
        "distributivity"
    },
    {
        "RING_00069",
        "(x0+(5))^2",
        "x0^2+(10)*x0+(25)",
        3,
        true,
        "binomial-square"
    },
    {
        "RING_00070",
        "(x0+(12))^3",
        "x0^3+(36)*x0^2+(432)*x0+(1728)",
        3,
        true,
        "binomial-cube"
    },
    {
        "RING_00071",
        "(x0+(-10))*(x1+(-9))",
        "(x1+(-9))*(x0+(-10))",
        3,
        true,
        "commutativity"
    },
    {
        "RING_00072",
        "(x0+x1)+(x2+(5))",
        "x0+(x1+(x2+(5)))",
        3,
        true,
        "associativity"
    },
    {
        "RING_00073",
        "x0*x2+x1*x2+(4)*x2",
        "(x0+x1+(4))*x2",
        3,
        true,
        "factorization"
    },
    {
        "RING_00074",
        "(x0+(11))*(x1+(-7))-(-7)*x0-(11)*x1-(-77)",
        "x0*x1",
        3,
        true,
        "cancellation"
    },
    {
        "RING_00075",
        "((x0+0)*(x1+1))+((x2*0)+(-11)-(-11))",
        "x0*x1+x0",
        3,
        true,
        "neutral-elements"
    },
    {
        "RING_00076",
        "x0*(x1+(-4))-(-4)*x0",
        "x0*x1",
        3,
        true,
        "distribute-cancel"
    },
    {
        "RING_00077",
        "((x0+(3))+x1)*((x0+(3))-x1)",
        "(x0+(3))^2-x1^2",
        3,
        true,
        "difference-of-squares"
    },
    {
        "RING_00078",
        "(x0+(10))^2-(x0^2+(20)*x0+(100))",
        "0",
        3,
        true,
        "algebraic-zero"
    },
    {
        "RING_00079",
        "(x0+(-12))^2",
        "x0^2+(-24)*x0+(145)",
        3,
        false,
        "false-binomial"
    },
    {
        "RING_00080",
        "(x0+(-5))*(x0-(-5))",
        "x0^2-(25)",
        3,
        true,
        "conjugates"
    },
    {
        "RING_00081",
        "(x0+x1+(x2+(-13)))^2",
        "x0^2+x1^2+(x2+(-13))^2+2*x0*x1+2*x0*(x2+(-13))+2*x1*(x2+(-13))",
        3,
        true,
        "multivariate-square"
    },
    {
        "RING_00082",
        "((x0+(9))^2)*(x1+(-12))",
        "(x0^2+(18)*x0+(81))*(x1+(-12))",
        3,
        true,
        "product-squared"
    },
    {
        "RING_00083",
        "(-13)*x0+(-1)*x0+(13)*x0+(-1)*x0",
        "(-2)*x0",
        3,
        true,
        "coefficient-aggregation"
    },
    {
        "RING_00084",
        "(-6)*(x0+x1+x2)^2",
        "(-6)*(x0^2+x1^2+x2^2+2*x0*x1+2*x0*x2+2*x1*x2)",
        3,
        true,
        "quadratic-form"
    },
    {
        "RING_00085",
        "(x0+(1))*(x1+(-10))",
        "x0*x1+(-10)*x0+(1)*x1+(-10)",
        3,
        true,
        "distributivity"
    },
    {
        "RING_00086",
        "(x0+(8))^2",
        "x0^2+(16)*x0+(64)",
        3,
        true,
        "binomial-square"
    },
    {
        "RING_00087",
        "(x0+(-14))^3",
        "x0^3+(-42)*x0^2+(588)*x0+(-2744)",
        3,
        true,
        "binomial-cube"
    },
    {
        "RING_00088",
        "(x0+(-7))*(x1+(-8))",
        "(x1+(-8))*(x0+(-7))",
        3,
        true,
        "commutativity"
    },
    {
        "RING_00089",
        "(x0+x1)+(x2+(10))",
        "x0+(x1+(x2+(10)))",
        3,
        true,
        "associativity"
    },
    {
        "RING_00090",
        "x0*x2+x1*x2+(7)*x2",
        "(x0+x1+(7))*x2",
        3,
        true,
        "factorization"
    },
    {
        "RING_00091",
        "(x0+(14))*(x1+(-6))-(-6)*x0-(14)*x1-(-84)",
        "x0*x1",
        3,
        true,
        "cancellation"
    },
    {
        "RING_00092",
        "((x0+0)*(x1+1))+((x2*0)+(-8)-(-8))",
        "x0*x1+x0",
        3,
        true,
        "neutral-elements"
    },
    {
        "RING_00093",
        "x0*(x1+(-1))-(-1)*x0",
        "x0*x1",
        3,
        true,
        "distribute-cancel"
    },
    {
        "RING_00094",
        "((x0+(6))+x1)*((x0+(6))-x1)",
        "(x0+(6))^2-x1^2",
        3,
        true,
        "difference-of-squares"
    },
    {
        "RING_00095",
        "(x0+(13))^2-(x0^2+(26)*x0+(169))",
        "0",
        3,
        true,
        "algebraic-zero"
    },
    {
        "RING_00096",
        "(x0+(-9))^2",
        "x0^2+(-18)*x0+(82)",
        3,
        false,
        "false-binomial"
    },
    {
        "RING_00097",
        "(x0+(-2))*(x0-(-2))",
        "x0^2-(4)",
        3,
        true,
        "conjugates"
    },
    {
        "RING_00098",
        "(x0+x1+(x2+(-8)))^2",
        "x0^2+x1^2+(x2+(-8))^2+2*x0*x1+2*x0*(x2+(-8))+2*x1*(x2+(-8))",
        3,
        true,
        "multivariate-square"
    },
    {
        "RING_00099",
        "((x0+(12))^2)*(x1+(-11))",
        "(x0^2+(24)*x0+(144))*(x1+(-11))",
        3,
        true,
        "product-squared"
    },
    {
        "RING_00100",
        "(-10)*x0+(0)*x0+(-9)*x0+(-12)*x0",
        "(-31)*x0",
        3,
        true,
        "coefficient-aggregation"
    },
    {
        "RING_00101",
        "(-3)*(x0+x1+x2)^2",
        "(-3)*(x0^2+x1^2+x2^2+2*x0*x1+2*x0*x2+2*x1*x2)",
        3,
        true,
        "quadratic-form"
    },
    {
        "RING_00102",
        "(x0+(4))*(x1+(-9))",
        "x0*x1+(-9)*x0+(4)*x1+(-36)",
        3,
        true,
        "distributivity"
    },
    {
        "RING_00103",
        "(x0+(11))^2",
        "x0^2+(22)*x0+(121)",
        3,
        true,
        "binomial-square"
    },
    {
        "RING_00104",
        "(x0+(-11))^3",
        "x0^3+(-33)*x0^2+(363)*x0+(-1331)",
        3,
        true,
        "binomial-cube"
    },
    {
        "RING_00105",
        "(x0+(-4))*(x1+(-7))",
        "(x1+(-7))*(x0+(-4))",
        3,
        true,
        "commutativity"
    },
    {
        "RING_00106",
        "(x0+x1)+(x2+(-12))",
        "x0+(x1+(x2+(-12)))",
        3,
        true,
        "associativity"
    },
    {
        "RING_00107",
        "x0*x2+x1*x2+(10)*x2",
        "(x0+x1+(10))*x2",
        3,
        true,
        "factorization"
    },
    {
        "RING_00108",
        "(x0+(-12))*(x1+(-5))-(-5)*x0-(-12)*x1-(60)",
        "x0*x1",
        3,
        true,
        "cancellation"
    },
    {
        "RING_00109",
        "((x0+0)*(x1+1))+((x2*0)+(-5)-(-5))",
        "x0*x1+x0",
        3,
        true,
        "neutral-elements"
    },
    {
        "RING_00110",
        "x0*(x1+(2))-(2)*x0",
        "x0*x1",
        3,
        true,
        "distribute-cancel"
    },
    {
        "RING_00111",
        "((x0+(9))+x1)*((x0+(9))-x1)",
        "(x0+(9))^2-x1^2",
        3,
        true,
        "difference-of-squares"
    },
    {
        "RING_00112",
        "(x0+(-13))^2-(x0^2+(-26)*x0+(169))",
        "0",
        3,
        true,
        "algebraic-zero"
    },
    {
        "RING_00113",
        "(x0+(-6))^2",
        "x0^2+(-12)*x0+(37)",
        3,
        false,
        "false-binomial"
    },
    {
        "RING_00114",
        "(x0+(1))*(x0-(1))",
        "x0^2-(1)",
        3,
        true,
        "conjugates"
    },
    {
        "RING_00115",
        "(x0+x1+(x2+(-3)))^2",
        "x0^2+x1^2+(x2+(-3))^2+2*x0*x1+2*x0*(x2+(-3))+2*x1*(x2+(-3))",
        3,
        true,
        "multivariate-square"
    },
    {
        "RING_00116",
        "((x0+(-14))^2)*(x1+(-10))",
        "(x0^2+(-28)*x0+(196))*(x1+(-10))",
        3,
        true,
        "product-squared"
    },
    {
        "RING_00117",
        "(-7)*x0+(1)*x0+(-4)*x0+(2)*x0",
        "(-8)*x0",
        3,
        true,
        "coefficient-aggregation"
    },
    {
        "RING_00118",
        "(0)*(x0+x1+x2)^2",
        "(0)*(x0^2+x1^2+x2^2+2*x0*x1+2*x0*x2+2*x1*x2)",
        3,
        true,
        "quadratic-form"
    },
    {
        "RING_00119",
        "(x0+(7))*(x1+(-8))",
        "x0*x1+(-8)*x0+(7)*x1+(-56)",
        3,
        true,
        "distributivity"
    },
    {
        "RING_00120",
        "(x0+(14))^2",
        "x0^2+(28)*x0+(196)",
        3,
        true,
        "binomial-square"
    },
    {
        "RING_00121",
        "(x0+(-8))^3",
        "x0^3+(-24)*x0^2+(192)*x0+(-512)",
        3,
        true,
        "binomial-cube"
    },
    {
        "RING_00122",
        "(x0+(-1))*(x1+(-6))",
        "(x1+(-6))*(x0+(-1))",
        3,
        true,
        "commutativity"
    },
    {
        "RING_00123",
        "(x0+x1)+(x2+(-7))",
        "x0+(x1+(x2+(-7)))",
        3,
        true,
        "associativity"
    },
    {
        "RING_00124",
        "x0*x2+x1*x2+(13)*x2",
        "(x0+x1+(13))*x2",
        3,
        true,
        "factorization"
    },
    {
        "RING_00125",
        "(x0+(-9))*(x1+(-4))-(-4)*x0-(-9)*x1-(36)",
        "x0*x1",
        3,
        true,
        "cancellation"
    },
    {
        "RING_00126",
        "((x0+0)*(x1+1))+((x2*0)+(-2)-(-2))",
        "x0*x1+x0",
        3,
        true,
        "neutral-elements"
    },
    {
        "RING_00127",
        "x0*(x1+(5))-(5)*x0",
        "x0*x1",
        3,
        true,
        "distribute-cancel"
    },
    {
        "RING_00128",
        "((x0+(12))+x1)*((x0+(12))-x1)",
        "(x0+(12))^2-x1^2",
        3,
        true,
        "difference-of-squares"
    },
    {
        "RING_00129",
        "(x0+(-10))^2-(x0^2+(-20)*x0+(100))",
        "0",
        3,
        true,
        "algebraic-zero"
    },
    {
        "RING_00130",
        "(x0+(-3))^2",
        "x0^2+(-6)*x0+(10)",
        3,
        false,
        "false-binomial"
    },
    {
        "RING_00131",
        "(x0+(4))*(x0-(4))",
        "x0^2-(16)",
        3,
        true,
        "conjugates"
    },
    {
        "RING_00132",
        "(x0+x1+(x2+(2)))^2",
        "x0^2+x1^2+(x2+(2))^2+2*x0*x1+2*x0*(x2+(2))+2*x1*(x2+(2))",
        3,
        true,
        "multivariate-square"
    },
    {
        "RING_00133",
        "((x0+(-11))^2)*(x1+(-9))",
        "(x0^2+(-22)*x0+(121))*(x1+(-9))",
        3,
        true,
        "product-squared"
    },
    {
        "RING_00134",
        "(-4)*x0+(2)*x0+(1)*x0+(-9)*x0",
        "(-10)*x0",
        3,
        true,
        "coefficient-aggregation"
    },
    {
        "RING_00135",
        "(3)*(x0+x1+x2)^2",
        "(3)*(x0^2+x1^2+x2^2+2*x0*x1+2*x0*x2+2*x1*x2)",
        3,
        true,
        "quadratic-form"
    },
    {
        "RING_00136",
        "(x0+(10))*(x1+(-7))",
        "x0*x1+(-7)*x0+(10)*x1+(-70)",
        3,
        true,
        "distributivity"
    },
    {
        "RING_00137",
        "(x0+(-12))^2",
        "x0^2+(-24)*x0+(144)",
        3,
        true,
        "binomial-square"
    },
    {
        "RING_00138",
        "(x0+(-5))^3",
        "x0^3+(-15)*x0^2+(75)*x0+(-125)",
        3,
        true,
        "binomial-cube"
    },
    {
        "RING_00139",
        "(x0+(2))*(x1+(-5))",
        "(x1+(-5))*(x0+(2))",
        3,
        true,
        "commutativity"
    },
    {
        "RING_00140",
        "(x0+x1)+(x2+(-2))",
        "x0+(x1+(x2+(-2)))",
        3,
        true,
        "associativity"
    },
    {
        "RING_00141",
        "x0*x2+x1*x2+(-13)*x2",
        "(x0+x1+(-13))*x2",
        3,
        true,
        "factorization"
    },
    {
        "RING_00142",
        "(x0+(-6))*(x1+(-3))-(-3)*x0-(-6)*x1-(18)",
        "x0*x1",
        3,
        true,
        "cancellation"
    },
    {
        "RING_00143",
        "((x0+0)*(x1+1))+((x2*0)+(1)-(1))",
        "x0*x1+x0",
        3,
        true,
        "neutral-elements"
    },
    {
        "RING_00144",
        "x0*(x1+(8))-(8)*x0",
        "x0*x1",
        3,
        true,
        "distribute-cancel"
    },
    {
        "RING_00145",
        "((x0+(-14))+x1)*((x0+(-14))-x1)",
        "(x0+(-14))^2-x1^2",
        3,
        true,
        "difference-of-squares"
    },
    {
        "RING_00146",
        "(x0+(-7))^2-(x0^2+(-14)*x0+(49))",
        "0",
        3,
        true,
        "algebraic-zero"
    },
    {
        "RING_00147",
        "(x0+(0))^2",
        "x0^2+(0)*x0+(1)",
        3,
        false,
        "false-binomial"
    },
    {
        "RING_00148",
        "(x0+(7))*(x0-(7))",
        "x0^2-(49)",
        3,
        true,
        "conjugates"
    },
    {
        "RING_00149",
        "(x0+x1+(x2+(7)))^2",
        "x0^2+x1^2+(x2+(7))^2+2*x0*x1+2*x0*(x2+(7))+2*x1*(x2+(7))",
        3,
        true,
        "multivariate-square"
    },
    {
        "RING_00150",
        "((x0+(-8))^2)*(x1+(-8))",
        "(x0^2+(-16)*x0+(64))*(x1+(-8))",
        3,
        true,
        "product-squared"
    },
    {
        "RING_00151",
        "(-1)*x0+(3)*x0+(6)*x0+(5)*x0",
        "(13)*x0",
        3,
        true,
        "coefficient-aggregation"
    },
    {
        "RING_00152",
        "(6)*(x0+x1+x2)^2",
        "(6)*(x0^2+x1^2+x2^2+2*x0*x1+2*x0*x2+2*x1*x2)",
        3,
        true,
        "quadratic-form"
    },
    {
        "RING_00153",
        "(x0+(13))*(x1+(-6))",
        "x0*x1+(-6)*x0+(13)*x1+(-78)",
        3,
        true,
        "distributivity"
    },
    {
        "RING_00154",
        "(x0+(-9))^2",
        "x0^2+(-18)*x0+(81)",
        3,
        true,
        "binomial-square"
    },
    {
        "RING_00155",
        "(x0+(-2))^3",
        "x0^3+(-6)*x0^2+(12)*x0+(-8)",
        3,
        true,
        "binomial-cube"
    },
    {
        "RING_00156",
        "(x0+(5))*(x1+(-4))",
        "(x1+(-4))*(x0+(5))",
        3,
        true,
        "commutativity"
    },
    {
        "RING_00157",
        "(x0+x1)+(x2+(3))",
        "x0+(x1+(x2+(3)))",
        3,
        true,
        "associativity"
    },
    {
        "RING_00158",
        "x0*x2+x1*x2+(-10)*x2",
        "(x0+x1+(-10))*x2",
        3,
        true,
        "factorization"
    },
    {
        "RING_00159",
        "(x0+(-3))*(x1+(-2))-(-2)*x0-(-3)*x1-(6)",
        "x0*x1",
        3,
        true,
        "cancellation"
    },
    {
        "RING_00160",
        "((x0+0)*(x1+1))+((x2*0)+(4)-(4))",
        "x0*x1+x0",
        3,
        true,
        "neutral-elements"
    },
    {
        "RING_00161",
        "x0*(x1+(11))-(11)*x0",
        "x0*x1",
        3,
        true,
        "distribute-cancel"
    },
    {
        "RING_00162",
        "((x0+(-11))+x1)*((x0+(-11))-x1)",
        "(x0+(-11))^2-x1^2",
        3,
        true,
        "difference-of-squares"
    },
    {
        "RING_00163",
        "(x0+(-4))^2-(x0^2+(-8)*x0+(16))",
        "0",
        3,
        true,
        "algebraic-zero"
    },
    {
        "RING_00164",
        "(x0+(3))^2",
        "x0^2+(6)*x0+(10)",
        3,
        false,
        "false-binomial"
    },
    {
        "RING_00165",
        "(x0+(10))*(x0-(10))",
        "x0^2-(100)",
        3,
        true,
        "conjugates"
    },
    {
        "RING_00166",
        "(x0+x1+(x2+(12)))^2",
        "x0^2+x1^2+(x2+(12))^2+2*x0*x1+2*x0*(x2+(12))+2*x1*(x2+(12))",
        3,
        true,
        "multivariate-square"
    },
    {
        "RING_00167",
        "((x0+(-5))^2)*(x1+(-7))",
        "(x0^2+(-10)*x0+(25))*(x1+(-7))",
        3,
        true,
        "product-squared"
    },
    {
        "RING_00168",
        "(2)*x0+(4)*x0+(11)*x0+(-6)*x0",
        "(11)*x0",
        3,
        true,
        "coefficient-aggregation"
    },
    {
        "RING_00169",
        "(9)*(x0+x1+x2)^2",
        "(9)*(x0^2+x1^2+x2^2+2*x0*x1+2*x0*x2+2*x1*x2)",
        3,
        true,
        "quadratic-form"
    },
    {
        "RING_00170",
        "(x0+(-13))*(x1+(-5))",
        "x0*x1+(-5)*x0+(-13)*x1+(65)",
        3,
        true,
        "distributivity"
    },
    {
        "RING_00171",
        "(x0+(-6))^2",
        "x0^2+(-12)*x0+(36)",
        3,
        true,
        "binomial-square"
    },
    {
        "RING_00172",
        "(x0+(1))^3",
        "x0^3+(3)*x0^2+(3)*x0+(1)",
        3,
        true,
        "binomial-cube"
    },
    {
        "RING_00173",
        "(x0+(8))*(x1+(-3))",
        "(x1+(-3))*(x0+(8))",
        3,
        true,
        "commutativity"
    },
    {
        "RING_00174",
        "(x0+x1)+(x2+(8))",
        "x0+(x1+(x2+(8)))",
        3,
        true,
        "associativity"
    },
    {
        "RING_00175",
        "x0*x2+x1*x2+(-7)*x2",
        "(x0+x1+(-7))*x2",
        3,
        true,
        "factorization"
    },
    {
        "RING_00176",
        "(x0+(0))*(x1+(-1))-(-1)*x0-(0)*x1-(0)",
        "x0*x1",
        3,
        true,
        "cancellation"
    },
    {
        "RING_00177",
        "((x0+0)*(x1+1))+((x2*0)+(7)-(7))",
        "x0*x1+x0",
        3,
        true,
        "neutral-elements"
    },
    {
        "RING_00178",
        "x0*(x1+(14))-(14)*x0",
        "x0*x1",
        3,
        true,
        "distribute-cancel"
    },
    {
        "RING_00179",
        "((x0+(-8))+x1)*((x0+(-8))-x1)",
        "(x0+(-8))^2-x1^2",
        3,
        true,
        "difference-of-squares"
    },
    {
        "RING_00180",
        "(x0+(-1))^2-(x0^2+(-2)*x0+(1))",
        "0",
        3,
        true,
        "algebraic-zero"
    },
    {
        "RING_00181",
        "(x0+(6))^2",
        "x0^2+(12)*x0+(37)",
        3,
        false,
        "false-binomial"
    },
    {
        "RING_00182",
        "(x0+(13))*(x0-(13))",
        "x0^2-(169)",
        3,
        true,
        "conjugates"
    },
    {
        "RING_00183",
        "(x0+x1+(x2+(-10)))^2",
        "x0^2+x1^2+(x2+(-10))^2+2*x0*x1+2*x0*(x2+(-10))+2*x1*(x2+(-10))",
        3,
        true,
        "multivariate-square"
    },
    {
        "RING_00184",
        "((x0+(-2))^2)*(x1+(-6))",
        "(x0^2+(-4)*x0+(4))*(x1+(-6))",
        3,
        true,
        "product-squared"
    },
    {
        "RING_00185",
        "(5)*x0+(5)*x0+(-11)*x0+(8)*x0",
        "(7)*x0",
        3,
        true,
        "coefficient-aggregation"
    },
    {
        "RING_00186",
        "(12)*(x0+x1+x2)^2",
        "(12)*(x0^2+x1^2+x2^2+2*x0*x1+2*x0*x2+2*x1*x2)",
        3,
        true,
        "quadratic-form"
    },
    {
        "RING_00187",
        "(x0+(-10))*(x1+(-4))",
        "x0*x1+(-4)*x0+(-10)*x1+(40)",
        3,
        true,
        "distributivity"
    },
    {
        "RING_00188",
        "(x0+(-3))^2",
        "x0^2+(-6)*x0+(9)",
        3,
        true,
        "binomial-square"
    },
    {
        "RING_00189",
        "(x0+(4))^3",
        "x0^3+(12)*x0^2+(48)*x0+(64)",
        3,
        true,
        "binomial-cube"
    },
    {
        "RING_00190",
        "(x0+(11))*(x1+(-2))",
        "(x1+(-2))*(x0+(11))",
        3,
        true,
        "commutativity"
    },
    {
        "RING_00191",
        "(x0+x1)+(x2+(13))",
        "x0+(x1+(x2+(13)))",
        3,
        true,
        "associativity"
    },
    {
        "RING_00192",
        "x0*x2+x1*x2+(-4)*x2",
        "(x0+x1+(-4))*x2",
        3,
        true,
        "factorization"
    },
    {
        "RING_00193",
        "(x0+(3))*(x1+(0))-(0)*x0-(3)*x1-(0)",
        "x0*x1",
        3,
        true,
        "cancellation"
    },
    {
        "RING_00194",
        "((x0+0)*(x1+1))+((x2*0)+(10)-(10))",
        "x0*x1+x0",
        3,
        true,
        "neutral-elements"
    },
    {
        "RING_00195",
        "x0*(x1+(-12))-(-12)*x0",
        "x0*x1",
        3,
        true,
        "distribute-cancel"
    },
    {
        "RING_00196",
        "((x0+(-5))+x1)*((x0+(-5))-x1)",
        "(x0+(-5))^2-x1^2",
        3,
        true,
        "difference-of-squares"
    },
    {
        "RING_00197",
        "(x0+(2))^2-(x0^2+(4)*x0+(4))",
        "0",
        3,
        true,
        "algebraic-zero"
    },
    {
        "RING_00198",
        "(x0+(9))^2",
        "x0^2+(18)*x0+(82)",
        3,
        false,
        "false-binomial"
    },
    {
        "RING_00199",
        "(x0+(-13))*(x0-(-13))",
        "x0^2-(169)",
        3,
        true,
        "conjugates"
    },
    {
        "RING_00200",
        "(x0+x1+(x2+(-5)))^2",
        "x0^2+x1^2+(x2+(-5))^2+2*x0*x1+2*x0*(x2+(-5))+2*x1*(x2+(-5))",
        3,
        true,
        "multivariate-square"
    },
    {
        "RING_00201",
        "((x0+(1))^2)*(x1+(-5))",
        "(x0^2+(2)*x0+(1))*(x1+(-5))",
        3,
        true,
        "product-squared"
    },
    {
        "RING_00202",
        "(8)*x0+(6)*x0+(-6)*x0+(-3)*x0",
        "(5)*x0",
        3,
        true,
        "coefficient-aggregation"
    },
    {
        "RING_00203",
        "(-14)*(x0+x1+x2)^2",
        "(-14)*(x0^2+x1^2+x2^2+2*x0*x1+2*x0*x2+2*x1*x2)",
        3,
        true,
        "quadratic-form"
    },
    {
        "RING_00204",
        "(x0+(-7))*(x1+(-3))",
        "x0*x1+(-3)*x0+(-7)*x1+(21)",
        3,
        true,
        "distributivity"
    },
    {
        "RING_00205",
        "(x0+(0))^2",
        "x0^2+(0)*x0+(0)",
        3,
        true,
        "binomial-square"
    },
    {
        "RING_00206",
        "(x0+(7))^3",
        "x0^3+(21)*x0^2+(147)*x0+(343)",
        3,
        true,
        "binomial-cube"
    },
    {
        "RING_00207",
        "(x0+(14))*(x1+(-1))",
        "(x1+(-1))*(x0+(14))",
        3,
        true,
        "commutativity"
    },
    {
        "RING_00208",
        "(x0+x1)+(x2+(-9))",
        "x0+(x1+(x2+(-9)))",
        3,
        true,
        "associativity"
    },
    {
        "RING_00209",
        "x0*x2+x1*x2+(-1)*x2",
        "(x0+x1+(-1))*x2",
        3,
        true,
        "factorization"
    },
    {
        "RING_00210",
        "(x0+(6))*(x1+(1))-(1)*x0-(6)*x1-(6)",
        "x0*x1",
        3,
        true,
        "cancellation"
    },
    {
        "RING_00211",
        "((x0+0)*(x1+1))+((x2*0)+(13)-(13))",
        "x0*x1+x0",
        3,
        true,
        "neutral-elements"
    },
    {
        "RING_00212",
        "x0*(x1+(-9))-(-9)*x0",
        "x0*x1",
        3,
        true,
        "distribute-cancel"
    },
    {
        "RING_00213",
        "((x0+(-2))+x1)*((x0+(-2))-x1)",
        "(x0+(-2))^2-x1^2",
        3,
        true,
        "difference-of-squares"
    },
    {
        "RING_00214",
        "(x0+(5))^2-(x0^2+(10)*x0+(25))",
        "0",
        3,
        true,
        "algebraic-zero"
    },
    {
        "RING_00215",
        "(x0+(12))^2",
        "x0^2+(24)*x0+(145)",
        3,
        false,
        "false-binomial"
    },
    {
        "RING_00216",
        "(x0+(-10))*(x0-(-10))",
        "x0^2-(100)",
        3,
        true,
        "conjugates"
    },
    {
        "RING_00217",
        "(x0+x1+(x2+(0)))^2",
        "x0^2+x1^2+(x2+(0))^2+2*x0*x1+2*x0*(x2+(0))+2*x1*(x2+(0))",
        3,
        true,
        "multivariate-square"
    },
    {
        "RING_00218",
        "((x0+(4))^2)*(x1+(-4))",
        "(x0^2+(8)*x0+(16))*(x1+(-4))",
        3,
        true,
        "product-squared"
    },
    {
        "RING_00219",
        "(11)*x0+(7)*x0+(-1)*x0+(11)*x0",
        "(28)*x0",
        3,
        true,
        "coefficient-aggregation"
    },
    {
        "RING_00220",
        "(-11)*(x0+x1+x2)^2",
        "(-11)*(x0^2+x1^2+x2^2+2*x0*x1+2*x0*x2+2*x1*x2)",
        3,
        true,
        "quadratic-form"
    },
    {
        "RING_00221",
        "(x0+(-4))*(x1+(-2))",
        "x0*x1+(-2)*x0+(-4)*x1+(8)",
        3,
        true,
        "distributivity"
    },
    {
        "RING_00222",
        "(x0+(3))^2",
        "x0^2+(6)*x0+(9)",
        3,
        true,
        "binomial-square"
    },
    {
        "RING_00223",
        "(x0+(10))^3",
        "x0^3+(30)*x0^2+(300)*x0+(1000)",
        3,
        true,
        "binomial-cube"
    },
    {
        "RING_00224",
        "(x0+(-12))*(x1+(0))",
        "(x1+(0))*(x0+(-12))",
        3,
        true,
        "commutativity"
    },
    {
        "RING_00225",
        "(x0+x1)+(x2+(-4))",
        "x0+(x1+(x2+(-4)))",
        3,
        true,
        "associativity"
    },
    {
        "RING_00226",
        "x0*x2+x1*x2+(2)*x2",
        "(x0+x1+(2))*x2",
        3,
        true,
        "factorization"
    },
    {
        "RING_00227",
        "(x0+(9))*(x1+(2))-(2)*x0-(9)*x1-(18)",
        "x0*x1",
        3,
        true,
        "cancellation"
    },
    {
        "RING_00228",
        "((x0+0)*(x1+1))+((x2*0)+(-13)-(-13))",
        "x0*x1+x0",
        3,
        true,
        "neutral-elements"
    },
    {
        "RING_00229",
        "x0*(x1+(-6))-(-6)*x0",
        "x0*x1",
        3,
        true,
        "distribute-cancel"
    },
    {
        "RING_00230",
        "((x0+(1))+x1)*((x0+(1))-x1)",
        "(x0+(1))^2-x1^2",
        3,
        true,
        "difference-of-squares"
    },
    {
        "RING_00231",
        "(x0+(8))^2-(x0^2+(16)*x0+(64))",
        "0",
        3,
        true,
        "algebraic-zero"
    },
    {
        "RING_00232",
        "(x0+(-14))^2",
        "x0^2+(-28)*x0+(197)",
        3,
        false,
        "false-binomial"
    },
    {
        "RING_00233",
        "(x0+(-7))*(x0-(-7))",
        "x0^2-(49)",
        3,
        true,
        "conjugates"
    },
    {
        "RING_00234",
        "(x0+x1+(x2+(5)))^2",
        "x0^2+x1^2+(x2+(5))^2+2*x0*x1+2*x0*(x2+(5))+2*x1*(x2+(5))",
        3,
        true,
        "multivariate-square"
    },
    {
        "RING_00235",
        "((x0+(7))^2)*(x1+(-3))",
        "(x0^2+(14)*x0+(49))*(x1+(-3))",
        3,
        true,
        "product-squared"
    },
    {
        "RING_00236",
        "(14)*x0+(8)*x0+(4)*x0+(0)*x0",
        "(26)*x0",
        3,
        true,
        "coefficient-aggregation"
    },
    {
        "RING_00237",
        "(-8)*(x0+x1+x2)^2",
        "(-8)*(x0^2+x1^2+x2^2+2*x0*x1+2*x0*x2+2*x1*x2)",
        3,
        true,
        "quadratic-form"
    },
    {
        "RING_00238",
        "(x0+(-1))*(x1+(-1))",
        "x0*x1+(-1)*x0+(-1)*x1+(1)",
        3,
        true,
        "distributivity"
    },
    {
        "RING_00239",
        "(x0+(6))^2",
        "x0^2+(12)*x0+(36)",
        3,
        true,
        "binomial-square"
    },
    {
        "RING_00240",
        "(x0+(13))^3",
        "x0^3+(39)*x0^2+(507)*x0+(2197)",
        3,
        true,
        "binomial-cube"
    },
    {
        "RING_00241",
        "(x0+(-9))*(x1+(1))",
        "(x1+(1))*(x0+(-9))",
        3,
        true,
        "commutativity"
    },
    {
        "RING_00242",
        "(x0+x1)+(x2+(1))",
        "x0+(x1+(x2+(1)))",
        3,
        true,
        "associativity"
    },
    {
        "RING_00243",
        "x0*x2+x1*x2+(5)*x2",
        "(x0+x1+(5))*x2",
        3,
        true,
        "factorization"
    },
    {
        "RING_00244",
        "(x0+(12))*(x1+(3))-(3)*x0-(12)*x1-(36)",
        "x0*x1",
        3,
        true,
        "cancellation"
    },
    {
        "RING_00245",
        "((x0+0)*(x1+1))+((x2*0)+(-10)-(-10))",
        "x0*x1+x0",
        3,
        true,
        "neutral-elements"
    },
    {
        "RING_00246",
        "x0*(x1+(-3))-(-3)*x0",
        "x0*x1",
        3,
        true,
        "distribute-cancel"
    },
    {
        "RING_00247",
        "((x0+(4))+x1)*((x0+(4))-x1)",
        "(x0+(4))^2-x1^2",
        3,
        true,
        "difference-of-squares"
    },
    {
        "RING_00248",
        "(x0+(11))^2-(x0^2+(22)*x0+(121))",
        "0",
        3,
        true,
        "algebraic-zero"
    },
    {
        "RING_00249",
        "(x0+(-11))^2",
        "x0^2+(-22)*x0+(122)",
        3,
        false,
        "false-binomial"
    },
    {
        "RING_00250",
        "(x0+(-4))*(x0-(-4))",
        "x0^2-(16)",
        3,
        true,
        "conjugates"
    },
    {
        "RING_00251",
        "(x0+x1+(x2+(10)))^2",
        "x0^2+x1^2+(x2+(10))^2+2*x0*x1+2*x0*(x2+(10))+2*x1*(x2+(10))",
        3,
        true,
        "multivariate-square"
    },
    {
        "RING_00252",
        "((x0+(10))^2)*(x1+(-2))",
        "(x0^2+(20)*x0+(100))*(x1+(-2))",
        3,
        true,
        "product-squared"
    },
    {
        "RING_00253",
        "(-12)*x0+(9)*x0+(9)*x0+(-11)*x0",
        "(-5)*x0",
        3,
        true,
        "coefficient-aggregation"
    },
    {
        "RING_00254",
        "(-5)*(x0+x1+x2)^2",
        "(-5)*(x0^2+x1^2+x2^2+2*x0*x1+2*x0*x2+2*x1*x2)",
        3,
        true,
        "quadratic-form"
    },
    {
        "RING_00255",
        "(x0+(2))*(x1+(0))",
        "x0*x1+(0)*x0+(2)*x1+(0)",
        3,
        true,
        "distributivity"
    },
    {
        "RING_00256",
        "(x0+(9))^2",
        "x0^2+(18)*x0+(81)",
        3,
        true,
        "binomial-square"
    },
    {
        "RING_00257",
        "(x0+(-13))^3",
        "x0^3+(-39)*x0^2+(507)*x0+(-2197)",
        3,
        true,
        "binomial-cube"
    },
    {
        "RING_00258",
        "(x0+(-6))*(x1+(2))",
        "(x1+(2))*(x0+(-6))",
        3,
        true,
        "commutativity"
    },
    {
        "RING_00259",
        "(x0+x1)+(x2+(6))",
        "x0+(x1+(x2+(6)))",
        3,
        true,
        "associativity"
    },
    {
        "RING_00260",
        "x0*x2+x1*x2+(8)*x2",
        "(x0+x1+(8))*x2",
        3,
        true,
        "factorization"
    },
    {
        "RING_00261",
        "(x0+(-14))*(x1+(4))-(4)*x0-(-14)*x1-(-56)",
        "x0*x1",
        3,
        true,
        "cancellation"
    },
    {
        "RING_00262",
        "((x0+0)*(x1+1))+((x2*0)+(-7)-(-7))",
        "x0*x1+x0",
        3,
        true,
        "neutral-elements"
    },
    {
        "RING_00263",
        "x0*(x1+(0))-(0)*x0",
        "x0*x1",
        3,
        true,
        "distribute-cancel"
    },
    {
        "RING_00264",
        "((x0+(7))+x1)*((x0+(7))-x1)",
        "(x0+(7))^2-x1^2",
        3,
        true,
        "difference-of-squares"
    },
    {
        "RING_00265",
        "(x0+(14))^2-(x0^2+(28)*x0+(196))",
        "0",
        3,
        true,
        "algebraic-zero"
    },
    {
        "RING_00266",
        "(x0+(-8))^2",
        "x0^2+(-16)*x0+(65)",
        3,
        false,
        "false-binomial"
    },
    {
        "RING_00267",
        "(x0+(-1))*(x0-(-1))",
        "x0^2-(1)",
        3,
        true,
        "conjugates"
    },
    {
        "RING_00268",
        "(x0+x1+(x2+(-12)))^2",
        "x0^2+x1^2+(x2+(-12))^2+2*x0*x1+2*x0*(x2+(-12))+2*x1*(x2+(-12))",
        3,
        true,
        "multivariate-square"
    },
    {
        "RING_00269",
        "((x0+(13))^2)*(x1+(-1))",
        "(x0^2+(26)*x0+(169))*(x1+(-1))",
        3,
        true,
        "product-squared"
    },
    {
        "RING_00270",
        "(-9)*x0+(10)*x0+(-13)*x0+(3)*x0",
        "(-9)*x0",
        3,
        true,
        "coefficient-aggregation"
    },
    {
        "RING_00271",
        "(-2)*(x0+x1+x2)^2",
        "(-2)*(x0^2+x1^2+x2^2+2*x0*x1+2*x0*x2+2*x1*x2)",
        3,
        true,
        "quadratic-form"
    },
    {
        "RING_00272",
        "(x0+(5))*(x1+(1))",
        "x0*x1+(1)*x0+(5)*x1+(5)",
        3,
        true,
        "distributivity"
    },
    {
        "RING_00273",
        "(x0+(12))^2",
        "x0^2+(24)*x0+(144)",
        3,
        true,
        "binomial-square"
    },
    {
        "RING_00274",
        "(x0+(-10))^3",
        "x0^3+(-30)*x0^2+(300)*x0+(-1000)",
        3,
        true,
        "binomial-cube"
    },
    {
        "RING_00275",
        "(x0+(-3))*(x1+(3))",
        "(x1+(3))*(x0+(-3))",
        3,
        true,
        "commutativity"
    },
    {
        "RING_00276",
        "(x0+x1)+(x2+(11))",
        "x0+(x1+(x2+(11)))",
        3,
        true,
        "associativity"
    },
    {
        "RING_00277",
        "x0*x2+x1*x2+(11)*x2",
        "(x0+x1+(11))*x2",
        3,
        true,
        "factorization"
    },
    {
        "RING_00278",
        "(x0+(-11))*(x1+(5))-(5)*x0-(-11)*x1-(-55)",
        "x0*x1",
        3,
        true,
        "cancellation"
    },
    {
        "RING_00279",
        "((x0+0)*(x1+1))+((x2*0)+(-4)-(-4))",
        "x0*x1+x0",
        3,
        true,
        "neutral-elements"
    },
    {
        "RING_00280",
        "x0*(x1+(3))-(3)*x0",
        "x0*x1",
        3,
        true,
        "distribute-cancel"
    },
    {
        "RING_00281",
        "((x0+(10))+x1)*((x0+(10))-x1)",
        "(x0+(10))^2-x1^2",
        3,
        true,
        "difference-of-squares"
    },
    {
        "RING_00282",
        "(x0+(-12))^2-(x0^2+(-24)*x0+(144))",
        "0",
        3,
        true,
        "algebraic-zero"
    },
    {
        "RING_00283",
        "(x0+(-5))^2",
        "x0^2+(-10)*x0+(26)",
        3,
        false,
        "false-binomial"
    },
    {
        "RING_00284",
        "(x0+(2))*(x0-(2))",
        "x0^2-(4)",
        3,
        true,
        "conjugates"
    },
    {
        "RING_00285",
        "(x0+x1+(x2+(-7)))^2",
        "x0^2+x1^2+(x2+(-7))^2+2*x0*x1+2*x0*(x2+(-7))+2*x1*(x2+(-7))",
        3,
        true,
        "multivariate-square"
    },
    {
        "RING_00286",
        "((x0+(-13))^2)*(x1+(0))",
        "(x0^2+(-26)*x0+(169))*(x1+(0))",
        3,
        true,
        "product-squared"
    },
    {
        "RING_00287",
        "(-6)*x0+(11)*x0+(-8)*x0+(-8)*x0",
        "(-11)*x0",
        3,
        true,
        "coefficient-aggregation"
    },
    {
        "RING_00288",
        "(1)*(x0+x1+x2)^2",
        "(1)*(x0^2+x1^2+x2^2+2*x0*x1+2*x0*x2+2*x1*x2)",
        3,
        true,
        "quadratic-form"
    },
    {
        "RING_00289",
        "(x0+(8))*(x1+(2))",
        "x0*x1+(2)*x0+(8)*x1+(16)",
        3,
        true,
        "distributivity"
    },
    {
        "RING_00290",
        "(x0+(-14))^2",
        "x0^2+(-28)*x0+(196)",
        3,
        true,
        "binomial-square"
    },
    {
        "RING_00291",
        "(x0+(-7))^3",
        "x0^3+(-21)*x0^2+(147)*x0+(-343)",
        3,
        true,
        "binomial-cube"
    },
    {
        "RING_00292",
        "(x0+(0))*(x1+(4))",
        "(x1+(4))*(x0+(0))",
        3,
        true,
        "commutativity"
    },
    {
        "RING_00293",
        "(x0+x1)+(x2+(-11))",
        "x0+(x1+(x2+(-11)))",
        3,
        true,
        "associativity"
    },
    {
        "RING_00294",
        "x0*x2+x1*x2+(14)*x2",
        "(x0+x1+(14))*x2",
        3,
        true,
        "factorization"
    },
    {
        "RING_00295",
        "(x0+(-8))*(x1+(6))-(6)*x0-(-8)*x1-(-48)",
        "x0*x1",
        3,
        true,
        "cancellation"
    },
    {
        "RING_00296",
        "((x0+0)*(x1+1))+((x2*0)+(-1)-(-1))",
        "x0*x1+x0",
        3,
        true,
        "neutral-elements"
    },
    {
        "RING_00297",
        "x0*(x1+(6))-(6)*x0",
        "x0*x1",
        3,
        true,
        "distribute-cancel"
    },
    {
        "RING_00298",
        "((x0+(13))+x1)*((x0+(13))-x1)",
        "(x0+(13))^2-x1^2",
        3,
        true,
        "difference-of-squares"
    },
    {
        "RING_00299",
        "(x0+(-9))^2-(x0^2+(-18)*x0+(81))",
        "0",
        3,
        true,
        "algebraic-zero"
    },
    {
        "RING_00300",
        "(x0+(-2))^2",
        "x0^2+(-4)*x0+(5)",
        3,
        false,
        "false-binomial"
    },
    {
        "RING_00301",
        "(x0+(5))*(x0-(5))",
        "x0^2-(25)",
        3,
        true,
        "conjugates"
    },
    {
        "RING_00302",
        "(x0+x1+(x2+(-2)))^2",
        "x0^2+x1^2+(x2+(-2))^2+2*x0*x1+2*x0*(x2+(-2))+2*x1*(x2+(-2))",
        3,
        true,
        "multivariate-square"
    },
    {
        "RING_00303",
        "((x0+(-10))^2)*(x1+(1))",
        "(x0^2+(-20)*x0+(100))*(x1+(1))",
        3,
        true,
        "product-squared"
    },
    {
        "RING_00304",
        "(-3)*x0+(12)*x0+(-3)*x0+(6)*x0",
        "(12)*x0",
        3,
        true,
        "coefficient-aggregation"
    },
    {
        "RING_00305",
        "(4)*(x0+x1+x2)^2",
        "(4)*(x0^2+x1^2+x2^2+2*x0*x1+2*x0*x2+2*x1*x2)",
        3,
        true,
        "quadratic-form"
    },
    {
        "RING_00306",
        "(x0+(11))*(x1+(3))",
        "x0*x1+(3)*x0+(11)*x1+(33)",
        3,
        true,
        "distributivity"
    },
    {
        "RING_00307",
        "(x0+(-11))^2",
        "x0^2+(-22)*x0+(121)",
        3,
        true,
        "binomial-square"
    },
    {
        "RING_00308",
        "(x0+(-4))^3",
        "x0^3+(-12)*x0^2+(48)*x0+(-64)",
        3,
        true,
        "binomial-cube"
    },
    {
        "RING_00309",
        "(x0+(3))*(x1+(5))",
        "(x1+(5))*(x0+(3))",
        3,
        true,
        "commutativity"
    },
    {
        "RING_00310",
        "(x0+x1)+(x2+(-6))",
        "x0+(x1+(x2+(-6)))",
        3,
        true,
        "associativity"
    },
    {
        "RING_00311",
        "x0*x2+x1*x2+(-12)*x2",
        "(x0+x1+(-12))*x2",
        3,
        true,
        "factorization"
    },
    {
        "RING_00312",
        "(x0+(-5))*(x1+(7))-(7)*x0-(-5)*x1-(-35)",
        "x0*x1",
        3,
        true,
        "cancellation"
    },
    {
        "RING_00313",
        "((x0+0)*(x1+1))+((x2*0)+(2)-(2))",
        "x0*x1+x0",
        3,
        true,
        "neutral-elements"
    },
    {
        "RING_00314",
        "x0*(x1+(9))-(9)*x0",
        "x0*x1",
        3,
        true,
        "distribute-cancel"
    },
    {
        "RING_00315",
        "((x0+(-13))+x1)*((x0+(-13))-x1)",
        "(x0+(-13))^2-x1^2",
        3,
        true,
        "difference-of-squares"
    },
    {
        "RING_00316",
        "(x0+(-6))^2-(x0^2+(-12)*x0+(36))",
        "0",
        3,
        true,
        "algebraic-zero"
    },
    {
        "RING_00317",
        "(x0+(1))^2",
        "x0^2+(2)*x0+(2)",
        3,
        false,
        "false-binomial"
    },
    {
        "RING_00318",
        "(x0+(8))*(x0-(8))",
        "x0^2-(64)",
        3,
        true,
        "conjugates"
    },
    {
        "RING_00319",
        "(x0+x1+(x2+(3)))^2",
        "x0^2+x1^2+(x2+(3))^2+2*x0*x1+2*x0*(x2+(3))+2*x1*(x2+(3))",
        3,
        true,
        "multivariate-square"
    },
    {
        "RING_00320",
        "((x0+(-7))^2)*(x1+(2))",
        "(x0^2+(-14)*x0+(49))*(x1+(2))",
        3,
        true,
        "product-squared"
    },
    {
        "RING_00321",
        "(0)*x0+(13)*x0+(2)*x0+(-5)*x0",
        "(10)*x0",
        3,
        true,
        "coefficient-aggregation"
    },
    {
        "RING_00322",
        "(7)*(x0+x1+x2)^2",
        "(7)*(x0^2+x1^2+x2^2+2*x0*x1+2*x0*x2+2*x1*x2)",
        3,
        true,
        "quadratic-form"
    },
    {
        "RING_00323",
        "(x0+(14))*(x1+(4))",
        "x0*x1+(4)*x0+(14)*x1+(56)",
        3,
        true,
        "distributivity"
    },
    {
        "RING_00324",
        "(x0+(-8))^2",
        "x0^2+(-16)*x0+(64)",
        3,
        true,
        "binomial-square"
    },
    {
        "RING_00325",
        "(x0+(-1))^3",
        "x0^3+(-3)*x0^2+(3)*x0+(-1)",
        3,
        true,
        "binomial-cube"
    },
    {
        "RING_00326",
        "(x0+(6))*(x1+(6))",
        "(x1+(6))*(x0+(6))",
        3,
        true,
        "commutativity"
    },
    {
        "RING_00327",
        "(x0+x1)+(x2+(-1))",
        "x0+(x1+(x2+(-1)))",
        3,
        true,
        "associativity"
    },
    {
        "RING_00328",
        "x0*x2+x1*x2+(-9)*x2",
        "(x0+x1+(-9))*x2",
        3,
        true,
        "factorization"
    },
    {
        "RING_00329",
        "(x0+(-2))*(x1+(8))-(8)*x0-(-2)*x1-(-16)",
        "x0*x1",
        3,
        true,
        "cancellation"
    },
    {
        "RING_00330",
        "((x0+0)*(x1+1))+((x2*0)+(5)-(5))",
        "x0*x1+x0",
        3,
        true,
        "neutral-elements"
    },
    {
        "RING_00331",
        "x0*(x1+(12))-(12)*x0",
        "x0*x1",
        3,
        true,
        "distribute-cancel"
    },
    {
        "RING_00332",
        "((x0+(-10))+x1)*((x0+(-10))-x1)",
        "(x0+(-10))^2-x1^2",
        3,
        true,
        "difference-of-squares"
    },
    {
        "RING_00333",
        "(x0+(-3))^2-(x0^2+(-6)*x0+(9))",
        "0",
        3,
        true,
        "algebraic-zero"
    },
    {
        "RING_00334",
        "(x0+(4))^2",
        "x0^2+(8)*x0+(17)",
        3,
        false,
        "false-binomial"
    },
    {
        "RING_00335",
        "(x0+(11))*(x0-(11))",
        "x0^2-(121)",
        3,
        true,
        "conjugates"
    },
    {
        "RING_00336",
        "(x0+x1+(x2+(8)))^2",
        "x0^2+x1^2+(x2+(8))^2+2*x0*x1+2*x0*(x2+(8))+2*x1*(x2+(8))",
        3,
        true,
        "multivariate-square"
    },
    {
        "RING_00337",
        "((x0+(-4))^2)*(x1+(3))",
        "(x0^2+(-8)*x0+(16))*(x1+(3))",
        3,
        true,
        "product-squared"
    },
    {
        "RING_00338",
        "(3)*x0+(14)*x0+(7)*x0+(9)*x0",
        "(33)*x0",
        3,
        true,
        "coefficient-aggregation"
    },
    {
        "RING_00339",
        "(10)*(x0+x1+x2)^2",
        "(10)*(x0^2+x1^2+x2^2+2*x0*x1+2*x0*x2+2*x1*x2)",
        3,
        true,
        "quadratic-form"
    },
    {
        "RING_00340",
        "(x0+(-12))*(x1+(5))",
        "x0*x1+(5)*x0+(-12)*x1+(-60)",
        3,
        true,
        "distributivity"
    },
    {
        "RING_00341",
        "(x0+(-5))^2",
        "x0^2+(-10)*x0+(25)",
        3,
        true,
        "binomial-square"
    },
    {
        "RING_00342",
        "(x0+(2))^3",
        "x0^3+(6)*x0^2+(12)*x0+(8)",
        3,
        true,
        "binomial-cube"
    },
    {
        "RING_00343",
        "(x0+(9))*(x1+(7))",
        "(x1+(7))*(x0+(9))",
        3,
        true,
        "commutativity"
    },
    {
        "RING_00344",
        "(x0+x1)+(x2+(4))",
        "x0+(x1+(x2+(4)))",
        3,
        true,
        "associativity"
    },
    {
        "RING_00345",
        "x0*x2+x1*x2+(-6)*x2",
        "(x0+x1+(-6))*x2",
        3,
        true,
        "factorization"
    },
    {
        "RING_00346",
        "(x0+(1))*(x1+(9))-(9)*x0-(1)*x1-(9)",
        "x0*x1",
        3,
        true,
        "cancellation"
    },
    {
        "RING_00347",
        "((x0+0)*(x1+1))+((x2*0)+(8)-(8))",
        "x0*x1+x0",
        3,
        true,
        "neutral-elements"
    },
    {
        "RING_00348",
        "x0*(x1+(-14))-(-14)*x0",
        "x0*x1",
        3,
        true,
        "distribute-cancel"
    },
    {
        "RING_00349",
        "((x0+(-7))+x1)*((x0+(-7))-x1)",
        "(x0+(-7))^2-x1^2",
        3,
        true,
        "difference-of-squares"
    },
    {
        "RING_00350",
        "(x0+(0))^2-(x0^2+(0)*x0+(0))",
        "0",
        3,
        true,
        "algebraic-zero"
    },
    {
        "RING_00351",
        "(x0+(7))^2",
        "x0^2+(14)*x0+(50)",
        3,
        false,
        "false-binomial"
    },
    {
        "RING_00352",
        "(x0+(14))*(x0-(14))",
        "x0^2-(196)",
        3,
        true,
        "conjugates"
    },
    {
        "RING_00353",
        "(x0+x1+(x2+(13)))^2",
        "x0^2+x1^2+(x2+(13))^2+2*x0*x1+2*x0*(x2+(13))+2*x1*(x2+(13))",
        3,
        true,
        "multivariate-square"
    },
    {
        "RING_00354",
        "((x0+(-1))^2)*(x1+(4))",
        "(x0^2+(-2)*x0+(1))*(x1+(4))",
        3,
        true,
        "product-squared"
    },
    {
        "RING_00355",
        "(6)*x0+(15)*x0+(12)*x0+(-2)*x0",
        "(31)*x0",
        3,
        true,
        "coefficient-aggregation"
    },
    {
        "RING_00356",
        "(13)*(x0+x1+x2)^2",
        "(13)*(x0^2+x1^2+x2^2+2*x0*x1+2*x0*x2+2*x1*x2)",
        3,
        true,
        "quadratic-form"
    },
    {
        "RING_00357",
        "(x0+(-9))*(x1+(6))",
        "x0*x1+(6)*x0+(-9)*x1+(-54)",
        3,
        true,
        "distributivity"
    },
    {
        "RING_00358",
        "(x0+(-2))^2",
        "x0^2+(-4)*x0+(4)",
        3,
        true,
        "binomial-square"
    },
    {
        "RING_00359",
        "(x0+(5))^3",
        "x0^3+(15)*x0^2+(75)*x0+(125)",
        3,
        true,
        "binomial-cube"
    },
    {
        "RING_00360",
        "(x0+(12))*(x1+(8))",
        "(x1+(8))*(x0+(12))",
        3,
        true,
        "commutativity"
    },
    {
        "RING_00361",
        "(x0+x1)+(x2+(9))",
        "x0+(x1+(x2+(9)))",
        3,
        true,
        "associativity"
    },
    {
        "RING_00362",
        "x0*x2+x1*x2+(-3)*x2",
        "(x0+x1+(-3))*x2",
        3,
        true,
        "factorization"
    },
    {
        "RING_00363",
        "(x0+(4))*(x1+(10))-(10)*x0-(4)*x1-(40)",
        "x0*x1",
        3,
        true,
        "cancellation"
    },
    {
        "RING_00364",
        "((x0+0)*(x1+1))+((x2*0)+(11)-(11))",
        "x0*x1+x0",
        3,
        true,
        "neutral-elements"
    },
    {
        "RING_00365",
        "x0*(x1+(-11))-(-11)*x0",
        "x0*x1",
        3,
        true,
        "distribute-cancel"
    },
    {
        "RING_00366",
        "((x0+(-4))+x1)*((x0+(-4))-x1)",
        "(x0+(-4))^2-x1^2",
        3,
        true,
        "difference-of-squares"
    },
    {
        "RING_00367",
        "(x0+(3))^2-(x0^2+(6)*x0+(9))",
        "0",
        3,
        true,
        "algebraic-zero"
    },
    {
        "RING_00368",
        "(x0+(10))^2",
        "x0^2+(20)*x0+(101)",
        3,
        false,
        "false-binomial"
    },
    {
        "RING_00369",
        "(x0+(-12))*(x0-(-12))",
        "x0^2-(144)",
        3,
        true,
        "conjugates"
    },
    {
        "RING_00370",
        "(x0+x1+(x2+(-9)))^2",
        "x0^2+x1^2+(x2+(-9))^2+2*x0*x1+2*x0*(x2+(-9))+2*x1*(x2+(-9))",
        3,
        true,
        "multivariate-square"
    },
    {
        "RING_00371",
        "((x0+(2))^2)*(x1+(5))",
        "(x0^2+(4)*x0+(4))*(x1+(5))",
        3,
        true,
        "product-squared"
    },
    {
        "RING_00372",
        "(9)*x0+(-15)*x0+(-10)*x0+(12)*x0",
        "(-4)*x0",
        3,
        true,
        "coefficient-aggregation"
    },
    {
        "RING_00373",
        "(-13)*(x0+x1+x2)^2",
        "(-13)*(x0^2+x1^2+x2^2+2*x0*x1+2*x0*x2+2*x1*x2)",
        3,
        true,
        "quadratic-form"
    },
    {
        "RING_00374",
        "(x0+(-6))*(x1+(7))",
        "x0*x1+(7)*x0+(-6)*x1+(-42)",
        3,
        true,
        "distributivity"
    },
    {
        "RING_00375",
        "(x0+(1))^2",
        "x0^2+(2)*x0+(1)",
        3,
        true,
        "binomial-square"
    },
    {
        "RING_00376",
        "(x0+(8))^3",
        "x0^3+(24)*x0^2+(192)*x0+(512)",
        3,
        true,
        "binomial-cube"
    },
    {
        "RING_00377",
        "(x0+(-14))*(x1+(9))",
        "(x1+(9))*(x0+(-14))",
        3,
        true,
        "commutativity"
    },
    {
        "RING_00378",
        "(x0+x1)+(x2+(-13))",
        "x0+(x1+(x2+(-13)))",
        3,
        true,
        "associativity"
    },
    {
        "RING_00379",
        "x0*x2+x1*x2+(0)*x2",
        "(x0+x1+(0))*x2",
        3,
        true,
        "factorization"
    },
    {
        "RING_00380",
        "(x0+(7))*(x1+(11))-(11)*x0-(7)*x1-(77)",
        "x0*x1",
        3,
        true,
        "cancellation"
    },
    {
        "RING_00381",
        "((x0+0)*(x1+1))+((x2*0)+(14)-(14))",
        "x0*x1+x0",
        3,
        true,
        "neutral-elements"
    },
    {
        "RING_00382",
        "x0*(x1+(-8))-(-8)*x0",
        "x0*x1",
        3,
        true,
        "distribute-cancel"
    },
    {
        "RING_00383",
        "((x0+(-1))+x1)*((x0+(-1))-x1)",
        "(x0+(-1))^2-x1^2",
        3,
        true,
        "difference-of-squares"
    },
    {
        "RING_00384",
        "(x0+(6))^2-(x0^2+(12)*x0+(36))",
        "0",
        3,
        true,
        "algebraic-zero"
    },
    {
        "RING_00385",
        "(x0+(13))^2",
        "x0^2+(26)*x0+(170)",
        3,
        false,
        "false-binomial"
    },
    {
        "RING_00386",
        "(x0+(-9))*(x0-(-9))",
        "x0^2-(81)",
        3,
        true,
        "conjugates"
    },
    {
        "RING_00387",
        "(x0+x1+(x2+(-4)))^2",
        "x0^2+x1^2+(x2+(-4))^2+2*x0*x1+2*x0*(x2+(-4))+2*x1*(x2+(-4))",
        3,
        true,
        "multivariate-square"
    },
    {
        "RING_00388",
        "((x0+(5))^2)*(x1+(6))",
        "(x0^2+(10)*x0+(25))*(x1+(6))",
        3,
        true,
        "product-squared"
    },
    {
        "RING_00389",
        "(12)*x0+(-14)*x0+(-5)*x0+(1)*x0",
        "(-6)*x0",
        3,
        true,
        "coefficient-aggregation"
    },
    {
        "RING_00390",
        "(-10)*(x0+x1+x2)^2",
        "(-10)*(x0^2+x1^2+x2^2+2*x0*x1+2*x0*x2+2*x1*x2)",
        3,
        true,
        "quadratic-form"
    },
    {
        "RING_00391",
        "(x0+(-3))*(x1+(8))",
        "x0*x1+(8)*x0+(-3)*x1+(-24)",
        3,
        true,
        "distributivity"
    },
    {
        "RING_00392",
        "(x0+(4))^2",
        "x0^2+(8)*x0+(16)",
        3,
        true,
        "binomial-square"
    },
    {
        "RING_00393",
        "(x0+(11))^3",
        "x0^3+(33)*x0^2+(363)*x0+(1331)",
        3,
        true,
        "binomial-cube"
    },
    {
        "RING_00394",
        "(x0+(-11))*(x1+(10))",
        "(x1+(10))*(x0+(-11))",
        3,
        true,
        "commutativity"
    },
    {
        "RING_00395",
        "(x0+x1)+(x2+(-8))",
        "x0+(x1+(x2+(-8)))",
        3,
        true,
        "associativity"
    },
    {
        "RING_00396",
        "x0*x2+x1*x2+(3)*x2",
        "(x0+x1+(3))*x2",
        3,
        true,
        "factorization"
    },
    {
        "RING_00397",
        "(x0+(10))*(x1+(12))-(12)*x0-(10)*x1-(120)",
        "x0*x1",
        3,
        true,
        "cancellation"
    },
    {
        "RING_00398",
        "((x0+0)*(x1+1))+((x2*0)+(-12)-(-12))",
        "x0*x1+x0",
        3,
        true,
        "neutral-elements"
    },
    {
        "RING_00399",
        "x0*(x1+(-5))-(-5)*x0",
        "x0*x1",
        3,
        true,
        "distribute-cancel"
    },
    {
        "RING_00400",
        "((x0+(2))+x1)*((x0+(2))-x1)",
        "(x0+(2))^2-x1^2",
        3,
        true,
        "difference-of-squares"
    },
    {
        "RING_00401",
        "(x0+(9))^2-(x0^2+(18)*x0+(81))",
        "0",
        3,
        true,
        "algebraic-zero"
    },
    {
        "RING_00402",
        "(x0+(-13))^2",
        "x0^2+(-26)*x0+(170)",
        3,
        false,
        "false-binomial"
    },
    {
        "RING_00403",
        "(x0+(-6))*(x0-(-6))",
        "x0^2-(36)",
        3,
        true,
        "conjugates"
    },
    {
        "RING_00404",
        "(x0+x1+(x2+(1)))^2",
        "x0^2+x1^2+(x2+(1))^2+2*x0*x1+2*x0*(x2+(1))+2*x1*(x2+(1))",
        3,
        true,
        "multivariate-square"
    },
    {
        "RING_00405",
        "((x0+(8))^2)*(x1+(7))",
        "(x0^2+(16)*x0+(64))*(x1+(7))",
        3,
        true,
        "product-squared"
    },
    {
        "RING_00406",
        "(-14)*x0+(-13)*x0+(0)*x0+(-10)*x0",
        "(-37)*x0",
        3,
        true,
        "coefficient-aggregation"
    },
    {
        "RING_00407",
        "(-7)*(x0+x1+x2)^2",
        "(-7)*(x0^2+x1^2+x2^2+2*x0*x1+2*x0*x2+2*x1*x2)",
        3,
        true,
        "quadratic-form"
    },
    {
        "RING_00408",
        "(x0+(0))*(x1+(9))",
        "x0*x1+(9)*x0+(0)*x1+(0)",
        3,
        true,
        "distributivity"
    },
    {
        "RING_00409",
        "(x0+(7))^2",
        "x0^2+(14)*x0+(49)",
        3,
        true,
        "binomial-square"
    },
    {
        "RING_00410",
        "(x0+(14))^3",
        "x0^3+(42)*x0^2+(588)*x0+(2744)",
        3,
        true,
        "binomial-cube"
    },
    {
        "RING_00411",
        "(x0+(-8))*(x1+(11))",
        "(x1+(11))*(x0+(-8))",
        3,
        true,
        "commutativity"
    },
    {
        "RING_00412",
        "(x0+x1)+(x2+(-3))",
        "x0+(x1+(x2+(-3)))",
        3,
        true,
        "associativity"
    },
    {
        "RING_00413",
        "x0*x2+x1*x2+(6)*x2",
        "(x0+x1+(6))*x2",
        3,
        true,
        "factorization"
    },
    {
        "RING_00414",
        "(x0+(13))*(x1+(13))-(13)*x0-(13)*x1-(169)",
        "x0*x1",
        3,
        true,
        "cancellation"
    },
    {
        "RING_00415",
        "((x0+0)*(x1+1))+((x2*0)+(-9)-(-9))",
        "x0*x1+x0",
        3,
        true,
        "neutral-elements"
    },
    {
        "RING_00416",
        "x0*(x1+(-2))-(-2)*x0",
        "x0*x1",
        3,
        true,
        "distribute-cancel"
    },
    {
        "RING_00417",
        "((x0+(5))+x1)*((x0+(5))-x1)",
        "(x0+(5))^2-x1^2",
        3,
        true,
        "difference-of-squares"
    },
    {
        "RING_00418",
        "(x0+(12))^2-(x0^2+(24)*x0+(144))",
        "0",
        3,
        true,
        "algebraic-zero"
    },
    {
        "RING_00419",
        "(x0+(-10))^2",
        "x0^2+(-20)*x0+(101)",
        3,
        false,
        "false-binomial"
    },
    {
        "RING_00420",
        "(x0+(-3))*(x0-(-3))",
        "x0^2-(9)",
        3,
        true,
        "conjugates"
    },
    {
        "RING_00421",
        "(x0+x1+(x2+(6)))^2",
        "x0^2+x1^2+(x2+(6))^2+2*x0*x1+2*x0*(x2+(6))+2*x1*(x2+(6))",
        3,
        true,
        "multivariate-square"
    },
    {
        "RING_00422",
        "((x0+(11))^2)*(x1+(8))",
        "(x0^2+(22)*x0+(121))*(x1+(8))",
        3,
        true,
        "product-squared"
    },
    {
        "RING_00423",
        "(-11)*x0+(-12)*x0+(5)*x0+(4)*x0",
        "(-14)*x0",
        3,
        true,
        "coefficient-aggregation"
    },
    {
        "RING_00424",
        "(-4)*(x0+x1+x2)^2",
        "(-4)*(x0^2+x1^2+x2^2+2*x0*x1+2*x0*x2+2*x1*x2)",
        3,
        true,
        "quadratic-form"
    },
    {
        "RING_00425",
        "(x0+(3))*(x1+(10))",
        "x0*x1+(10)*x0+(3)*x1+(30)",
        3,
        true,
        "distributivity"
    },
    {
        "RING_00426",
        "(x0+(10))^2",
        "x0^2+(20)*x0+(100)",
        3,
        true,
        "binomial-square"
    },
    {
        "RING_00427",
        "(x0+(-12))^3",
        "x0^3+(-36)*x0^2+(432)*x0+(-1728)",
        3,
        true,
        "binomial-cube"
    },
    {
        "RING_00428",
        "(x0+(-5))*(x1+(12))",
        "(x1+(12))*(x0+(-5))",
        3,
        true,
        "commutativity"
    },
    {
        "RING_00429",
        "(x0+x1)+(x2+(2))",
        "x0+(x1+(x2+(2)))",
        3,
        true,
        "associativity"
    },
    {
        "RING_00430",
        "x0*x2+x1*x2+(9)*x2",
        "(x0+x1+(9))*x2",
        3,
        true,
        "factorization"
    },
    {
        "RING_00431",
        "(x0+(-13))*(x1+(14))-(14)*x0-(-13)*x1-(-182)",
        "x0*x1",
        3,
        true,
        "cancellation"
    },
    {
        "RING_00432",
        "((x0+0)*(x1+1))+((x2*0)+(-6)-(-6))",
        "x0*x1+x0",
        3,
        true,
        "neutral-elements"
    },
    {
        "RING_00433",
        "x0*(x1+(1))-(1)*x0",
        "x0*x1",
        3,
        true,
        "distribute-cancel"
    },
    {
        "RING_00434",
        "((x0+(8))+x1)*((x0+(8))-x1)",
        "(x0+(8))^2-x1^2",
        3,
        true,
        "difference-of-squares"
    },
    {
        "RING_00435",
        "(x0+(-14))^2-(x0^2+(-28)*x0+(196))",
        "0",
        3,
        true,
        "algebraic-zero"
    },
    {
        "RING_00436",
        "(x0+(-7))^2",
        "x0^2+(-14)*x0+(50)",
        3,
        false,
        "false-binomial"
    },
    {
        "RING_00437",
        "(x0+(0))*(x0-(0))",
        "x0^2-(0)",
        3,
        true,
        "conjugates"
    },
    {
        "RING_00438",
        "(x0+x1+(x2+(11)))^2",
        "x0^2+x1^2+(x2+(11))^2+2*x0*x1+2*x0*(x2+(11))+2*x1*(x2+(11))",
        3,
        true,
        "multivariate-square"
    },
    {
        "RING_00439",
        "((x0+(14))^2)*(x1+(9))",
        "(x0^2+(28)*x0+(196))*(x1+(9))",
        3,
        true,
        "product-squared"
    },
    {
        "RING_00440",
        "(-8)*x0+(-11)*x0+(10)*x0+(-7)*x0",
        "(-16)*x0",
        3,
        true,
        "coefficient-aggregation"
    },
    {
        "RING_00441",
        "(-1)*(x0+x1+x2)^2",
        "(-1)*(x0^2+x1^2+x2^2+2*x0*x1+2*x0*x2+2*x1*x2)",
        3,
        true,
        "quadratic-form"
    },
    {
        "RING_00442",
        "(x0+(6))*(x1+(11))",
        "x0*x1+(11)*x0+(6)*x1+(66)",
        3,
        true,
        "distributivity"
    },
    {
        "RING_00443",
        "(x0+(13))^2",
        "x0^2+(26)*x0+(169)",
        3,
        true,
        "binomial-square"
    },
    {
        "RING_00444",
        "(x0+(-9))^3",
        "x0^3+(-27)*x0^2+(243)*x0+(-729)",
        3,
        true,
        "binomial-cube"
    },
    {
        "RING_00445",
        "(x0+(-2))*(x1+(13))",
        "(x1+(13))*(x0+(-2))",
        3,
        true,
        "commutativity"
    },
    {
        "RING_00446",
        "(x0+x1)+(x2+(7))",
        "x0+(x1+(x2+(7)))",
        3,
        true,
        "associativity"
    },
    {
        "RING_00447",
        "x0*x2+x1*x2+(12)*x2",
        "(x0+x1+(12))*x2",
        3,
        true,
        "factorization"
    },
    {
        "RING_00448",
        "(x0+(-10))*(x1+(15))-(15)*x0-(-10)*x1-(-150)",
        "x0*x1",
        3,
        true,
        "cancellation"
    },
    {
        "RING_00449",
        "((x0+0)*(x1+1))+((x2*0)+(-3)-(-3))",
        "x0*x1+x0",
        3,
        true,
        "neutral-elements"
    },
    {
        "RING_00450",
        "x0*(x1+(4))-(4)*x0",
        "x0*x1",
        3,
        true,
        "distribute-cancel"
    },
    {
        "RING_00451",
        "((x0+(11))+x1)*((x0+(11))-x1)",
        "(x0+(11))^2-x1^2",
        3,
        true,
        "difference-of-squares"
    },
    {
        "RING_00452",
        "(x0+(-11))^2-(x0^2+(-22)*x0+(121))",
        "0",
        3,
        true,
        "algebraic-zero"
    },
    {
        "RING_00453",
        "(x0+(-4))^2",
        "x0^2+(-8)*x0+(17)",
        3,
        false,
        "false-binomial"
    },
    {
        "RING_00454",
        "(x0+(3))*(x0-(3))",
        "x0^2-(9)",
        3,
        true,
        "conjugates"
    },
    {
        "RING_00455",
        "(x0+x1+(x2+(-11)))^2",
        "x0^2+x1^2+(x2+(-11))^2+2*x0*x1+2*x0*(x2+(-11))+2*x1*(x2+(-11))",
        3,
        true,
        "multivariate-square"
    },
    {
        "RING_00456",
        "((x0+(-12))^2)*(x1+(10))",
        "(x0^2+(-24)*x0+(144))*(x1+(10))",
        3,
        true,
        "product-squared"
    },
    {
        "RING_00457",
        "(-5)*x0+(-10)*x0+(-12)*x0+(7)*x0",
        "(-20)*x0",
        3,
        true,
        "coefficient-aggregation"
    },
    {
        "RING_00458",
        "(2)*(x0+x1+x2)^2",
        "(2)*(x0^2+x1^2+x2^2+2*x0*x1+2*x0*x2+2*x1*x2)",
        3,
        true,
        "quadratic-form"
    },
    {
        "RING_00459",
        "(x0+(9))*(x1+(12))",
        "x0*x1+(12)*x0+(9)*x1+(108)",
        3,
        true,
        "distributivity"
    },
    {
        "RING_00460",
        "(x0+(-13))^2",
        "x0^2+(-26)*x0+(169)",
        3,
        true,
        "binomial-square"
    },
    {
        "RING_00461",
        "(x0+(-6))^3",
        "x0^3+(-18)*x0^2+(108)*x0+(-216)",
        3,
        true,
        "binomial-cube"
    },
    {
        "RING_00462",
        "(x0+(1))*(x1+(14))",
        "(x1+(14))*(x0+(1))",
        3,
        true,
        "commutativity"
    },
    {
        "RING_00463",
        "(x0+x1)+(x2+(12))",
        "x0+(x1+(x2+(12)))",
        3,
        true,
        "associativity"
    },
    {
        "RING_00464",
        "x0*x2+x1*x2+(-14)*x2",
        "(x0+x1+(-14))*x2",
        3,
        true,
        "factorization"
    },
    {
        "RING_00465",
        "(x0+(-7))*(x1+(-15))-(-15)*x0-(-7)*x1-(105)",
        "x0*x1",
        3,
        true,
        "cancellation"
    },
    {
        "RING_00466",
        "((x0+0)*(x1+1))+((x2*0)+(0)-(0))",
        "x0*x1+x0",
        3,
        true,
        "neutral-elements"
    },
    {
        "RING_00467",
        "x0*(x1+(7))-(7)*x0",
        "x0*x1",
        3,
        true,
        "distribute-cancel"
    },
    {
        "RING_00468",
        "((x0+(14))+x1)*((x0+(14))-x1)",
        "(x0+(14))^2-x1^2",
        3,
        true,
        "difference-of-squares"
    },
    {
        "RING_00469",
        "(x0+(-8))^2-(x0^2+(-16)*x0+(64))",
        "0",
        3,
        true,
        "algebraic-zero"
    },
    {
        "RING_00470",
        "(x0+(-1))^2",
        "x0^2+(-2)*x0+(2)",
        3,
        false,
        "false-binomial"
    },
    {
        "RING_00471",
        "(x0+(6))*(x0-(6))",
        "x0^2-(36)",
        3,
        true,
        "conjugates"
    },
    {
        "RING_00472",
        "(x0+x1+(x2+(-6)))^2",
        "x0^2+x1^2+(x2+(-6))^2+2*x0*x1+2*x0*(x2+(-6))+2*x1*(x2+(-6))",
        3,
        true,
        "multivariate-square"
    },
    {
        "RING_00473",
        "((x0+(-9))^2)*(x1+(11))",
        "(x0^2+(-18)*x0+(81))*(x1+(11))",
        3,
        true,
        "product-squared"
    },
    {
        "RING_00474",
        "(-2)*x0+(-9)*x0+(-7)*x0+(-4)*x0",
        "(-22)*x0",
        3,
        true,
        "coefficient-aggregation"
    },
    {
        "RING_00475",
        "(5)*(x0+x1+x2)^2",
        "(5)*(x0^2+x1^2+x2^2+2*x0*x1+2*x0*x2+2*x1*x2)",
        3,
        true,
        "quadratic-form"
    },
    {
        "RING_00476",
        "(x0+(12))*(x1+(13))",
        "x0*x1+(13)*x0+(12)*x1+(156)",
        3,
        true,
        "distributivity"
    },
    {
        "RING_00477",
        "(x0+(-10))^2",
        "x0^2+(-20)*x0+(100)",
        3,
        true,
        "binomial-square"
    },
    {
        "RING_00478",
        "(x0+(-3))^3",
        "x0^3+(-9)*x0^2+(27)*x0+(-27)",
        3,
        true,
        "binomial-cube"
    },
    {
        "RING_00479",
        "(x0+(4))*(x1+(15))",
        "(x1+(15))*(x0+(4))",
        3,
        true,
        "commutativity"
    },
    {
        "RING_00480",
        "(x0+x1)+(x2+(-10))",
        "x0+(x1+(x2+(-10)))",
        3,
        true,
        "associativity"
    },
    {
        "RING_00481",
        "x0*x2+x1*x2+(-11)*x2",
        "(x0+x1+(-11))*x2",
        3,
        true,
        "factorization"
    },
    {
        "RING_00482",
        "(x0+(-4))*(x1+(-14))-(-14)*x0-(-4)*x1-(56)",
        "x0*x1",
        3,
        true,
        "cancellation"
    },
    {
        "RING_00483",
        "((x0+0)*(x1+1))+((x2*0)+(3)-(3))",
        "x0*x1+x0",
        3,
        true,
        "neutral-elements"
    },
    {
        "RING_00484",
        "x0*(x1+(10))-(10)*x0",
        "x0*x1",
        3,
        true,
        "distribute-cancel"
    },
    {
        "RING_00485",
        "((x0+(-12))+x1)*((x0+(-12))-x1)",
        "(x0+(-12))^2-x1^2",
        3,
        true,
        "difference-of-squares"
    },
    {
        "RING_00486",
        "(x0+(-5))^2-(x0^2+(-10)*x0+(25))",
        "0",
        3,
        true,
        "algebraic-zero"
    },
    {
        "RING_00487",
        "(x0+(2))^2",
        "x0^2+(4)*x0+(5)",
        3,
        false,
        "false-binomial"
    },
    {
        "RING_00488",
        "(x0+(9))*(x0-(9))",
        "x0^2-(81)",
        3,
        true,
        "conjugates"
    },
    {
        "RING_00489",
        "(x0+x1+(x2+(-1)))^2",
        "x0^2+x1^2+(x2+(-1))^2+2*x0*x1+2*x0*(x2+(-1))+2*x1*(x2+(-1))",
        3,
        true,
        "multivariate-square"
    },
    {
        "RING_00490",
        "((x0+(-6))^2)*(x1+(12))",
        "(x0^2+(-12)*x0+(36))*(x1+(12))",
        3,
        true,
        "product-squared"
    },
    {
        "RING_00491",
        "(1)*x0+(-8)*x0+(-2)*x0+(10)*x0",
        "(1)*x0",
        3,
        true,
        "coefficient-aggregation"
    },
    {
        "RING_00492",
        "(8)*(x0+x1+x2)^2",
        "(8)*(x0^2+x1^2+x2^2+2*x0*x1+2*x0*x2+2*x1*x2)",
        3,
        true,
        "quadratic-form"
    },
    {
        "RING_00493",
        "(x0+(-14))*(x1+(14))",
        "x0*x1+(14)*x0+(-14)*x1+(-196)",
        3,
        true,
        "distributivity"
    },
    {
        "RING_00494",
        "(x0+(-7))^2",
        "x0^2+(-14)*x0+(49)",
        3,
        true,
        "binomial-square"
    },
    {
        "RING_00495",
        "(x0+(0))^3",
        "x0^3+(0)*x0^2+(0)*x0+(0)",
        3,
        true,
        "binomial-cube"
    },
    {
        "RING_00496",
        "(x0+(7))*(x1+(-15))",
        "(x1+(-15))*(x0+(7))",
        3,
        true,
        "commutativity"
    },
    {
        "RING_00497",
        "(x0+x1)+(x2+(-5))",
        "x0+(x1+(x2+(-5)))",
        3,
        true,
        "associativity"
    },
    {
        "RING_00498",
        "x0*x2+x1*x2+(-8)*x2",
        "(x0+x1+(-8))*x2",
        3,
        true,
        "factorization"
    },
    {
        "RING_00499",
        "(x0+(-1))*(x1+(-13))-(-13)*x0-(-1)*x1-(13)",
        "x0*x1",
        3,
        true,
        "cancellation"
    },
    {
        "RING_00500",
        "((x0+0)*(x1+1))+((x2*0)+(6)-(6))",
        "x0*x1+x0",
        3,
        true,
        "neutral-elements"
    },
    {
        "RING_00501",
        "x0*(x1+(13))-(13)*x0",
        "x0*x1",
        3,
        true,
        "distribute-cancel"
    },
    {
        "RING_00502",
        "((x0+(-9))+x1)*((x0+(-9))-x1)",
        "(x0+(-9))^2-x1^2",
        3,
        true,
        "difference-of-squares"
    },
    {
        "RING_00503",
        "(x0+(-2))^2-(x0^2+(-4)*x0+(4))",
        "0",
        3,
        true,
        "algebraic-zero"
    },
    {
        "RING_00504",
        "(x0+(5))^2",
        "x0^2+(10)*x0+(26)",
        3,
        false,
        "false-binomial"
    },
    {
        "RING_00505",
        "(x0+(12))*(x0-(12))",
        "x0^2-(144)",
        3,
        true,
        "conjugates"
    },
    {
        "RING_00506",
        "(x0+x1+(x2+(4)))^2",
        "x0^2+x1^2+(x2+(4))^2+2*x0*x1+2*x0*(x2+(4))+2*x1*(x2+(4))",
        3,
        true,
        "multivariate-square"
    },
    {
        "RING_00507",
        "((x0+(-3))^2)*(x1+(13))",
        "(x0^2+(-6)*x0+(9))*(x1+(13))",
        3,
        true,
        "product-squared"
    },
    {
        "RING_00508",
        "(4)*x0+(-7)*x0+(3)*x0+(-1)*x0",
        "(-1)*x0",
        3,
        true,
        "coefficient-aggregation"
    },
    {
        "RING_00509",
        "(11)*(x0+x1+x2)^2",
        "(11)*(x0^2+x1^2+x2^2+2*x0*x1+2*x0*x2+2*x1*x2)",
        3,
        true,
        "quadratic-form"
    },
    {
        "RING_00510",
        "(x0+(-11))*(x1+(15))",
        "x0*x1+(15)*x0+(-11)*x1+(-165)",
        3,
        true,
        "distributivity"
    },
    {
        "RING_00511",
        "(x0+(-4))^2",
        "x0^2+(-8)*x0+(16)",
        3,
        true,
        "binomial-square"
    },
    {
        "RING_00512",
        "(x0+(3))^3",
        "x0^3+(9)*x0^2+(27)*x0+(27)",
        3,
        true,
        "binomial-cube"
    },
    {
        "RING_00513",
        "(x0+(10))*(x1+(-14))",
        "(x1+(-14))*(x0+(10))",
        3,
        true,
        "commutativity"
    },
    {
        "RING_00514",
        "(x0+x1)+(x2+(0))",
        "x0+(x1+(x2+(0)))",
        3,
        true,
        "associativity"
    },
    {
        "RING_00515",
        "x0*x2+x1*x2+(-5)*x2",
        "(x0+x1+(-5))*x2",
        3,
        true,
        "factorization"
    },
    {
        "RING_00516",
        "(x0+(2))*(x1+(-12))-(-12)*x0-(2)*x1-(-24)",
        "x0*x1",
        3,
        true,
        "cancellation"
    },
    {
        "RING_00517",
        "((x0+0)*(x1+1))+((x2*0)+(9)-(9))",
        "x0*x1+x0",
        3,
        true,
        "neutral-elements"
    },
    {
        "RING_00518",
        "x0*(x1+(-13))-(-13)*x0",
        "x0*x1",
        3,
        true,
        "distribute-cancel"
    },
    {
        "RING_00519",
        "((x0+(-6))+x1)*((x0+(-6))-x1)",
        "(x0+(-6))^2-x1^2",
        3,
        true,
        "difference-of-squares"
    },
    {
        "RING_00520",
        "(x0+(1))^2-(x0^2+(2)*x0+(1))",
        "0",
        3,
        true,
        "algebraic-zero"
    },
    {
        "RING_00521",
        "(x0+(8))^2",
        "x0^2+(16)*x0+(65)",
        3,
        false,
        "false-binomial"
    },
    {
        "RING_00522",
        "(x0+(-14))*(x0-(-14))",
        "x0^2-(196)",
        3,
        true,
        "conjugates"
    },
    {
        "RING_00523",
        "(x0+x1+(x2+(9)))^2",
        "x0^2+x1^2+(x2+(9))^2+2*x0*x1+2*x0*(x2+(9))+2*x1*(x2+(9))",
        3,
        true,
        "multivariate-square"
    },
    {
        "RING_00524",
        "((x0+(0))^2)*(x1+(14))",
        "(x0^2+(0)*x0+(0))*(x1+(14))",
        3,
        true,
        "product-squared"
    },
    {
        "RING_00525",
        "(7)*x0+(-6)*x0+(8)*x0+(-12)*x0",
        "(-3)*x0",
        3,
        true,
        "coefficient-aggregation"
    },
    {
        "RING_00526",
        "(14)*(x0+x1+x2)^2",
        "(14)*(x0^2+x1^2+x2^2+2*x0*x1+2*x0*x2+2*x1*x2)",
        3,
        true,
        "quadratic-form"
    },
    {
        "RING_00527",
        "(x0+(-8))*(x1+(-15))",
        "x0*x1+(-15)*x0+(-8)*x1+(120)",
        3,
        true,
        "distributivity"
    },
    {
        "RING_00528",
        "(x0+(-1))^2",
        "x0^2+(-2)*x0+(1)",
        3,
        true,
        "binomial-square"
    },
    {
        "RING_00529",
        "(x0+(6))^3",
        "x0^3+(18)*x0^2+(108)*x0+(216)",
        3,
        true,
        "binomial-cube"
    },
    {
        "RING_00530",
        "(x0+(13))*(x1+(-13))",
        "(x1+(-13))*(x0+(13))",
        3,
        true,
        "commutativity"
    },
    {
        "RING_00531",
        "(x0+x1)+(x2+(5))",
        "x0+(x1+(x2+(5)))",
        3,
        true,
        "associativity"
    },
    {
        "RING_00532",
        "x0*x2+x1*x2+(-2)*x2",
        "(x0+x1+(-2))*x2",
        3,
        true,
        "factorization"
    },
    {
        "RING_00533",
        "(x0+(5))*(x1+(-11))-(-11)*x0-(5)*x1-(-55)",
        "x0*x1",
        3,
        true,
        "cancellation"
    },
    {
        "RING_00534",
        "((x0+0)*(x1+1))+((x2*0)+(12)-(12))",
        "x0*x1+x0",
        3,
        true,
        "neutral-elements"
    },
    {
        "RING_00535",
        "x0*(x1+(-10))-(-10)*x0",
        "x0*x1",
        3,
        true,
        "distribute-cancel"
    },
    {
        "RING_00536",
        "((x0+(-3))+x1)*((x0+(-3))-x1)",
        "(x0+(-3))^2-x1^2",
        3,
        true,
        "difference-of-squares"
    },
    {
        "RING_00537",
        "(x0+(4))^2-(x0^2+(8)*x0+(16))",
        "0",
        3,
        true,
        "algebraic-zero"
    },
    {
        "RING_00538",
        "(x0+(11))^2",
        "x0^2+(22)*x0+(122)",
        3,
        false,
        "false-binomial"
    },
    {
        "RING_00539",
        "(x0+(-11))*(x0-(-11))",
        "x0^2-(121)",
        3,
        true,
        "conjugates"
    },
    {
        "RING_00540",
        "(x0+x1+(x2+(-13)))^2",
        "x0^2+x1^2+(x2+(-13))^2+2*x0*x1+2*x0*(x2+(-13))+2*x1*(x2+(-13))",
        3,
        true,
        "multivariate-square"
    },
    {
        "RING_00541",
        "((x0+(3))^2)*(x1+(15))",
        "(x0^2+(6)*x0+(9))*(x1+(15))",
        3,
        true,
        "product-squared"
    },
    {
        "RING_00542",
        "(10)*x0+(-5)*x0+(13)*x0+(2)*x0",
        "(20)*x0",
        3,
        true,
        "coefficient-aggregation"
    },
    {
        "RING_00543",
        "(-12)*(x0+x1+x2)^2",
        "(-12)*(x0^2+x1^2+x2^2+2*x0*x1+2*x0*x2+2*x1*x2)",
        3,
        true,
        "quadratic-form"
    },
    {
        "RING_00544",
        "(x0+(-5))*(x1+(-14))",
        "x0*x1+(-14)*x0+(-5)*x1+(70)",
        3,
        true,
        "distributivity"
    },
    {
        "RING_00545",
        "(x0+(2))^2",
        "x0^2+(4)*x0+(4)",
        3,
        true,
        "binomial-square"
    },
    {
        "RING_00546",
        "(x0+(9))^3",
        "x0^3+(27)*x0^2+(243)*x0+(729)",
        3,
        true,
        "binomial-cube"
    },
    {
        "RING_00547",
        "(x0+(-13))*(x1+(-12))",
        "(x1+(-12))*(x0+(-13))",
        3,
        true,
        "commutativity"
    },
    {
        "RING_00548",
        "(x0+x1)+(x2+(10))",
        "x0+(x1+(x2+(10)))",
        3,
        true,
        "associativity"
    },
    {
        "RING_00549",
        "x0*x2+x1*x2+(1)*x2",
        "(x0+x1+(1))*x2",
        3,
        true,
        "factorization"
    },
    {
        "RING_00550",
        "(x0+(8))*(x1+(-10))-(-10)*x0-(8)*x1-(-80)",
        "x0*x1",
        3,
        true,
        "cancellation"
    },
    {
        "RING_00551",
        "((x0+0)*(x1+1))+((x2*0)+(-14)-(-14))",
        "x0*x1+x0",
        3,
        true,
        "neutral-elements"
    },
    {
        "RING_00552",
        "x0*(x1+(-7))-(-7)*x0",
        "x0*x1",
        3,
        true,
        "distribute-cancel"
    },
    {
        "RING_00553",
        "((x0+(0))+x1)*((x0+(0))-x1)",
        "(x0+(0))^2-x1^2",
        3,
        true,
        "difference-of-squares"
    },
    {
        "RING_00554",
        "(x0+(7))^2-(x0^2+(14)*x0+(49))",
        "0",
        3,
        true,
        "algebraic-zero"
    },
    {
        "RING_00555",
        "(x0+(14))^2",
        "x0^2+(28)*x0+(197)",
        3,
        false,
        "false-binomial"
    },
    {
        "RING_00556",
        "(x0+(-8))*(x0-(-8))",
        "x0^2-(64)",
        3,
        true,
        "conjugates"
    },
    {
        "RING_00557",
        "(x0+x1+(x2+(-8)))^2",
        "x0^2+x1^2+(x2+(-8))^2+2*x0*x1+2*x0*(x2+(-8))+2*x1*(x2+(-8))",
        3,
        true,
        "multivariate-square"
    },
    {
        "RING_00558",
        "((x0+(6))^2)*(x1+(-15))",
        "(x0^2+(12)*x0+(36))*(x1+(-15))",
        3,
        true,
        "product-squared"
    },
    {
        "RING_00559",
        "(13)*x0+(-4)*x0+(-9)*x0+(-9)*x0",
        "(-9)*x0",
        3,
        true,
        "coefficient-aggregation"
    },
    {
        "RING_00560",
        "(-9)*(x0+x1+x2)^2",
        "(-9)*(x0^2+x1^2+x2^2+2*x0*x1+2*x0*x2+2*x1*x2)",
        3,
        true,
        "quadratic-form"
    },
    {
        "RING_00561",
        "(x0+(-2))*(x1+(-13))",
        "x0*x1+(-13)*x0+(-2)*x1+(26)",
        3,
        true,
        "distributivity"
    },
    {
        "RING_00562",
        "(x0+(5))^2",
        "x0^2+(10)*x0+(25)",
        3,
        true,
        "binomial-square"
    },
    {
        "RING_00563",
        "(x0+(12))^3",
        "x0^3+(36)*x0^2+(432)*x0+(1728)",
        3,
        true,
        "binomial-cube"
    },
    {
        "RING_00564",
        "(x0+(-10))*(x1+(-11))",
        "(x1+(-11))*(x0+(-10))",
        3,
        true,
        "commutativity"
    },
    {
        "RING_00565",
        "(x0+x1)+(x2+(-12))",
        "x0+(x1+(x2+(-12)))",
        3,
        true,
        "associativity"
    },
    {
        "RING_00566",
        "x0*x2+x1*x2+(4)*x2",
        "(x0+x1+(4))*x2",
        3,
        true,
        "factorization"
    },
    {
        "RING_00567",
        "(x0+(11))*(x1+(-9))-(-9)*x0-(11)*x1-(-99)",
        "x0*x1",
        3,
        true,
        "cancellation"
    },
    {
        "RING_00568",
        "((x0+0)*(x1+1))+((x2*0)+(-11)-(-11))",
        "x0*x1+x0",
        3,
        true,
        "neutral-elements"
    },
    {
        "RING_00569",
        "x0*(x1+(-4))-(-4)*x0",
        "x0*x1",
        3,
        true,
        "distribute-cancel"
    },
    {
        "RING_00570",
        "((x0+(3))+x1)*((x0+(3))-x1)",
        "(x0+(3))^2-x1^2",
        3,
        true,
        "difference-of-squares"
    },
    {
        "RING_00571",
        "(x0+(10))^2-(x0^2+(20)*x0+(100))",
        "0",
        3,
        true,
        "algebraic-zero"
    },
    {
        "RING_00572",
        "(x0+(-12))^2",
        "x0^2+(-24)*x0+(145)",
        3,
        false,
        "false-binomial"
    },
    {
        "RING_00573",
        "(x0+(-5))*(x0-(-5))",
        "x0^2-(25)",
        3,
        true,
        "conjugates"
    },
    {
        "RING_00574",
        "(x0+x1+(x2+(-3)))^2",
        "x0^2+x1^2+(x2+(-3))^2+2*x0*x1+2*x0*(x2+(-3))+2*x1*(x2+(-3))",
        3,
        true,
        "multivariate-square"
    },
    {
        "RING_00575",
        "((x0+(9))^2)*(x1+(-14))",
        "(x0^2+(18)*x0+(81))*(x1+(-14))",
        3,
        true,
        "product-squared"
    },
    {
        "RING_00576",
        "(-13)*x0+(-3)*x0+(-4)*x0+(5)*x0",
        "(-15)*x0",
        3,
        true,
        "coefficient-aggregation"
    },
    {
        "RING_00577",
        "(-6)*(x0+x1+x2)^2",
        "(-6)*(x0^2+x1^2+x2^2+2*x0*x1+2*x0*x2+2*x1*x2)",
        3,
        true,
        "quadratic-form"
    },
    {
        "RING_00578",
        "(x0+(1))*(x1+(-12))",
        "x0*x1+(-12)*x0+(1)*x1+(-12)",
        3,
        true,
        "distributivity"
    },
    {
        "RING_00579",
        "(x0+(8))^2",
        "x0^2+(16)*x0+(64)",
        3,
        true,
        "binomial-square"
    },
    {
        "RING_00580",
        "(x0+(-14))^3",
        "x0^3+(-42)*x0^2+(588)*x0+(-2744)",
        3,
        true,
        "binomial-cube"
    },
    {
        "RING_00581",
        "(x0+(-7))*(x1+(-10))",
        "(x1+(-10))*(x0+(-7))",
        3,
        true,
        "commutativity"
    },
    {
        "RING_00582",
        "(x0+x1)+(x2+(-7))",
        "x0+(x1+(x2+(-7)))",
        3,
        true,
        "associativity"
    },
    {
        "RING_00583",
        "x0*x2+x1*x2+(7)*x2",
        "(x0+x1+(7))*x2",
        3,
        true,
        "factorization"
    },
    {
        "RING_00584",
        "(x0+(14))*(x1+(-8))-(-8)*x0-(14)*x1-(-112)",
        "x0*x1",
        3,
        true,
        "cancellation"
    },
    {
        "RING_00585",
        "((x0+0)*(x1+1))+((x2*0)+(-8)-(-8))",
        "x0*x1+x0",
        3,
        true,
        "neutral-elements"
    },
    {
        "RING_00586",
        "x0*(x1+(-1))-(-1)*x0",
        "x0*x1",
        3,
        true,
        "distribute-cancel"
    },
    {
        "RING_00587",
        "((x0+(6))+x1)*((x0+(6))-x1)",
        "(x0+(6))^2-x1^2",
        3,
        true,
        "difference-of-squares"
    },
    {
        "RING_00588",
        "(x0+(13))^2-(x0^2+(26)*x0+(169))",
        "0",
        3,
        true,
        "algebraic-zero"
    },
    {
        "RING_00589",
        "(x0+(-9))^2",
        "x0^2+(-18)*x0+(82)",
        3,
        false,
        "false-binomial"
    },
    {
        "RING_00590",
        "(x0+(-2))*(x0-(-2))",
        "x0^2-(4)",
        3,
        true,
        "conjugates"
    },
    {
        "RING_00591",
        "(x0+x1+(x2+(2)))^2",
        "x0^2+x1^2+(x2+(2))^2+2*x0*x1+2*x0*(x2+(2))+2*x1*(x2+(2))",
        3,
        true,
        "multivariate-square"
    },
    {
        "RING_00592",
        "((x0+(12))^2)*(x1+(-13))",
        "(x0^2+(24)*x0+(144))*(x1+(-13))",
        3,
        true,
        "product-squared"
    },
    {
        "RING_00593",
        "(-10)*x0+(-2)*x0+(1)*x0+(-6)*x0",
        "(-17)*x0",
        3,
        true,
        "coefficient-aggregation"
    },
    {
        "RING_00594",
        "(-3)*(x0+x1+x2)^2",
        "(-3)*(x0^2+x1^2+x2^2+2*x0*x1+2*x0*x2+2*x1*x2)",
        3,
        true,
        "quadratic-form"
    },
    {
        "RING_00595",
        "(x0+(4))*(x1+(-11))",
        "x0*x1+(-11)*x0+(4)*x1+(-44)",
        3,
        true,
        "distributivity"
    },
    {
        "RING_00596",
        "(x0+(11))^2",
        "x0^2+(22)*x0+(121)",
        3,
        true,
        "binomial-square"
    },
    {
        "RING_00597",
        "(x0+(-11))^3",
        "x0^3+(-33)*x0^2+(363)*x0+(-1331)",
        3,
        true,
        "binomial-cube"
    },
    {
        "RING_00598",
        "(x0+(-4))*(x1+(-9))",
        "(x1+(-9))*(x0+(-4))",
        3,
        true,
        "commutativity"
    },
    {
        "RING_00599",
        "(x0+x1)+(x2+(-2))",
        "x0+(x1+(x2+(-2)))",
        3,
        true,
        "associativity"
    },
    {
        "RING_00600",
        "x0*x2+x1*x2+(10)*x2",
        "(x0+x1+(10))*x2",
        3,
        true,
        "factorization"
    },
    {
        "RING_00601",
        "(x0+(-12))*(x1+(-7))-(-7)*x0-(-12)*x1-(84)",
        "x0*x1",
        3,
        true,
        "cancellation"
    },
    {
        "RING_00602",
        "((x0+0)*(x1+1))+((x2*0)+(-5)-(-5))",
        "x0*x1+x0",
        3,
        true,
        "neutral-elements"
    },
    {
        "RING_00603",
        "x0*(x1+(2))-(2)*x0",
        "x0*x1",
        3,
        true,
        "distribute-cancel"
    },
    {
        "RING_00604",
        "((x0+(9))+x1)*((x0+(9))-x1)",
        "(x0+(9))^2-x1^2",
        3,
        true,
        "difference-of-squares"
    },
    {
        "RING_00605",
        "(x0+(-13))^2-(x0^2+(-26)*x0+(169))",
        "0",
        3,
        true,
        "algebraic-zero"
    },
    {
        "RING_00606",
        "(x0+(-6))^2",
        "x0^2+(-12)*x0+(37)",
        3,
        false,
        "false-binomial"
    },
    {
        "RING_00607",
        "(x0+(1))*(x0-(1))",
        "x0^2-(1)",
        3,
        true,
        "conjugates"
    },
    {
        "RING_00608",
        "(x0+x1+(x2+(7)))^2",
        "x0^2+x1^2+(x2+(7))^2+2*x0*x1+2*x0*(x2+(7))+2*x1*(x2+(7))",
        3,
        true,
        "multivariate-square"
    },
    {
        "RING_00609",
        "((x0+(-14))^2)*(x1+(-12))",
        "(x0^2+(-28)*x0+(196))*(x1+(-12))",
        3,
        true,
        "product-squared"
    },
    {
        "RING_00610",
        "(-7)*x0+(-1)*x0+(6)*x0+(8)*x0",
        "(6)*x0",
        3,
        true,
        "coefficient-aggregation"
    },
    {
        "RING_00611",
        "(0)*(x0+x1+x2)^2",
        "(0)*(x0^2+x1^2+x2^2+2*x0*x1+2*x0*x2+2*x1*x2)",
        3,
        true,
        "quadratic-form"
    },
    {
        "RING_00612",
        "(x0+(7))*(x1+(-10))",
        "x0*x1+(-10)*x0+(7)*x1+(-70)",
        3,
        true,
        "distributivity"
    },
    {
        "RING_00613",
        "(x0+(14))^2",
        "x0^2+(28)*x0+(196)",
        3,
        true,
        "binomial-square"
    },
    {
        "RING_00614",
        "(x0+(-8))^3",
        "x0^3+(-24)*x0^2+(192)*x0+(-512)",
        3,
        true,
        "binomial-cube"
    },
    {
        "RING_00615",
        "(x0+(-1))*(x1+(-8))",
        "(x1+(-8))*(x0+(-1))",
        3,
        true,
        "commutativity"
    },
    {
        "RING_00616",
        "(x0+x1)+(x2+(3))",
        "x0+(x1+(x2+(3)))",
        3,
        true,
        "associativity"
    },
    {
        "RING_00617",
        "x0*x2+x1*x2+(13)*x2",
        "(x0+x1+(13))*x2",
        3,
        true,
        "factorization"
    },
    {
        "RING_00618",
        "(x0+(-9))*(x1+(-6))-(-6)*x0-(-9)*x1-(54)",
        "x0*x1",
        3,
        true,
        "cancellation"
    },
    {
        "RING_00619",
        "((x0+0)*(x1+1))+((x2*0)+(-2)-(-2))",
        "x0*x1+x0",
        3,
        true,
        "neutral-elements"
    },
    {
        "RING_00620",
        "x0*(x1+(5))-(5)*x0",
        "x0*x1",
        3,
        true,
        "distribute-cancel"
    },
    {
        "RING_00621",
        "((x0+(12))+x1)*((x0+(12))-x1)",
        "(x0+(12))^2-x1^2",
        3,
        true,
        "difference-of-squares"
    },
    {
        "RING_00622",
        "(x0+(-10))^2-(x0^2+(-20)*x0+(100))",
        "0",
        3,
        true,
        "algebraic-zero"
    },
    {
        "RING_00623",
        "(x0+(-3))^2",
        "x0^2+(-6)*x0+(10)",
        3,
        false,
        "false-binomial"
    },
    {
        "RING_00624",
        "(x0+(4))*(x0-(4))",
        "x0^2-(16)",
        3,
        true,
        "conjugates"
    },
    {
        "RING_00625",
        "(x0+x1+(x2+(12)))^2",
        "x0^2+x1^2+(x2+(12))^2+2*x0*x1+2*x0*(x2+(12))+2*x1*(x2+(12))",
        3,
        true,
        "multivariate-square"
    },
    {
        "RING_00626",
        "((x0+(-11))^2)*(x1+(-11))",
        "(x0^2+(-22)*x0+(121))*(x1+(-11))",
        3,
        true,
        "product-squared"
    },
    {
        "RING_00627",
        "(-4)*x0+(0)*x0+(11)*x0+(-3)*x0",
        "(4)*x0",
        3,
        true,
        "coefficient-aggregation"
    },
    {
        "RING_00628",
        "(3)*(x0+x1+x2)^2",
        "(3)*(x0^2+x1^2+x2^2+2*x0*x1+2*x0*x2+2*x1*x2)",
        3,
        true,
        "quadratic-form"
    },
    {
        "RING_00629",
        "(x0+(10))*(x1+(-9))",
        "x0*x1+(-9)*x0+(10)*x1+(-90)",
        3,
        true,
        "distributivity"
    },
    {
        "RING_00630",
        "(x0+(-12))^2",
        "x0^2+(-24)*x0+(144)",
        3,
        true,
        "binomial-square"
    },
    {
        "RING_00631",
        "(x0+(-5))^3",
        "x0^3+(-15)*x0^2+(75)*x0+(-125)",
        3,
        true,
        "binomial-cube"
    },
    {
        "RING_00632",
        "(x0+(2))*(x1+(-7))",
        "(x1+(-7))*(x0+(2))",
        3,
        true,
        "commutativity"
    },
    {
        "RING_00633",
        "(x0+x1)+(x2+(8))",
        "x0+(x1+(x2+(8)))",
        3,
        true,
        "associativity"
    },
    {
        "RING_00634",
        "x0*x2+x1*x2+(-13)*x2",
        "(x0+x1+(-13))*x2",
        3,
        true,
        "factorization"
    },
    {
        "RING_00635",
        "(x0+(-6))*(x1+(-5))-(-5)*x0-(-6)*x1-(30)",
        "x0*x1",
        3,
        true,
        "cancellation"
    },
    {
        "RING_00636",
        "((x0+0)*(x1+1))+((x2*0)+(1)-(1))",
        "x0*x1+x0",
        3,
        true,
        "neutral-elements"
    },
    {
        "RING_00637",
        "x0*(x1+(8))-(8)*x0",
        "x0*x1",
        3,
        true,
        "distribute-cancel"
    },
    {
        "RING_00638",
        "((x0+(-14))+x1)*((x0+(-14))-x1)",
        "(x0+(-14))^2-x1^2",
        3,
        true,
        "difference-of-squares"
    },
    {
        "RING_00639",
        "(x0+(-7))^2-(x0^2+(-14)*x0+(49))",
        "0",
        3,
        true,
        "algebraic-zero"
    },
    {
        "RING_00640",
        "(x0+(0))^2",
        "x0^2+(0)*x0+(1)",
        3,
        false,
        "false-binomial"
    },
    {
        "RING_00641",
        "(x0+(7))*(x0-(7))",
        "x0^2-(49)",
        3,
        true,
        "conjugates"
    },
    {
        "RING_00642",
        "(x0+x1+(x2+(-10)))^2",
        "x0^2+x1^2+(x2+(-10))^2+2*x0*x1+2*x0*(x2+(-10))+2*x1*(x2+(-10))",
        3,
        true,
        "multivariate-square"
    },
    {
        "RING_00643",
        "((x0+(-8))^2)*(x1+(-10))",
        "(x0^2+(-16)*x0+(64))*(x1+(-10))",
        3,
        true,
        "product-squared"
    },
    {
        "RING_00644",
        "(-1)*x0+(1)*x0+(-11)*x0+(11)*x0",
        "(0)*x0",
        3,
        true,
        "coefficient-aggregation"
    },
    {
        "RING_00645",
        "(6)*(x0+x1+x2)^2",
        "(6)*(x0^2+x1^2+x2^2+2*x0*x1+2*x0*x2+2*x1*x2)",
        3,
        true,
        "quadratic-form"
    },
    {
        "RING_00646",
        "(x0+(13))*(x1+(-8))",
        "x0*x1+(-8)*x0+(13)*x1+(-104)",
        3,
        true,
        "distributivity"
    },
    {
        "RING_00647",
        "(x0+(-9))^2",
        "x0^2+(-18)*x0+(81)",
        3,
        true,
        "binomial-square"
    },
    {
        "RING_00648",
        "(x0+(-2))^3",
        "x0^3+(-6)*x0^2+(12)*x0+(-8)",
        3,
        true,
        "binomial-cube"
    },
    {
        "RING_00649",
        "(x0+(5))*(x1+(-6))",
        "(x1+(-6))*(x0+(5))",
        3,
        true,
        "commutativity"
    },
    {
        "RING_00650",
        "(x0+x1)+(x2+(13))",
        "x0+(x1+(x2+(13)))",
        3,
        true,
        "associativity"
    },
    {
        "RING_00651",
        "x0*x2+x1*x2+(-10)*x2",
        "(x0+x1+(-10))*x2",
        3,
        true,
        "factorization"
    },
    {
        "RING_00652",
        "(x0+(-3))*(x1+(-4))-(-4)*x0-(-3)*x1-(12)",
        "x0*x1",
        3,
        true,
        "cancellation"
    },
    {
        "RING_00653",
        "((x0+0)*(x1+1))+((x2*0)+(4)-(4))",
        "x0*x1+x0",
        3,
        true,
        "neutral-elements"
    },
    {
        "RING_00654",
        "x0*(x1+(11))-(11)*x0",
        "x0*x1",
        3,
        true,
        "distribute-cancel"
    },
    {
        "RING_00655",
        "((x0+(-11))+x1)*((x0+(-11))-x1)",
        "(x0+(-11))^2-x1^2",
        3,
        true,
        "difference-of-squares"
    },
    {
        "RING_00656",
        "(x0+(-4))^2-(x0^2+(-8)*x0+(16))",
        "0",
        3,
        true,
        "algebraic-zero"
    },
    {
        "RING_00657",
        "(x0+(3))^2",
        "x0^2+(6)*x0+(10)",
        3,
        false,
        "false-binomial"
    },
    {
        "RING_00658",
        "(x0+(10))*(x0-(10))",
        "x0^2-(100)",
        3,
        true,
        "conjugates"
    },
    {
        "RING_00659",
        "(x0+x1+(x2+(-5)))^2",
        "x0^2+x1^2+(x2+(-5))^2+2*x0*x1+2*x0*(x2+(-5))+2*x1*(x2+(-5))",
        3,
        true,
        "multivariate-square"
    },
    {
        "RING_00660",
        "((x0+(-5))^2)*(x1+(-9))",
        "(x0^2+(-10)*x0+(25))*(x1+(-9))",
        3,
        true,
        "product-squared"
    },
    {
        "RING_00661",
        "(2)*x0+(2)*x0+(-6)*x0+(0)*x0",
        "(-2)*x0",
        3,
        true,
        "coefficient-aggregation"
    },
    {
        "RING_00662",
        "(9)*(x0+x1+x2)^2",
        "(9)*(x0^2+x1^2+x2^2+2*x0*x1+2*x0*x2+2*x1*x2)",
        3,
        true,
        "quadratic-form"
    },
    {
        "RING_00663",
        "(x0+(-13))*(x1+(-7))",
        "x0*x1+(-7)*x0+(-13)*x1+(91)",
        3,
        true,
        "distributivity"
    },
    {
        "RING_00664",
        "(x0+(-6))^2",
        "x0^2+(-12)*x0+(36)",
        3,
        true,
        "binomial-square"
    },
    {
        "RING_00665",
        "(x0+(1))^3",
        "x0^3+(3)*x0^2+(3)*x0+(1)",
        3,
        true,
        "binomial-cube"
    },
    {
        "RING_00666",
        "(x0+(8))*(x1+(-5))",
        "(x1+(-5))*(x0+(8))",
        3,
        true,
        "commutativity"
    },
    {
        "RING_00667",
        "(x0+x1)+(x2+(-9))",
        "x0+(x1+(x2+(-9)))",
        3,
        true,
        "associativity"
    },
    {
        "RING_00668",
        "x0*x2+x1*x2+(-7)*x2",
        "(x0+x1+(-7))*x2",
        3,
        true,
        "factorization"
    },
    {
        "RING_00669",
        "(x0+(0))*(x1+(-3))-(-3)*x0-(0)*x1-(0)",
        "x0*x1",
        3,
        true,
        "cancellation"
    },
    {
        "RING_00670",
        "((x0+0)*(x1+1))+((x2*0)+(7)-(7))",
        "x0*x1+x0",
        3,
        true,
        "neutral-elements"
    },
    {
        "RING_00671",
        "x0*(x1+(14))-(14)*x0",
        "x0*x1",
        3,
        true,
        "distribute-cancel"
    },
    {
        "RING_00672",
        "((x0+(-8))+x1)*((x0+(-8))-x1)",
        "(x0+(-8))^2-x1^2",
        3,
        true,
        "difference-of-squares"
    },
    {
        "RING_00673",
        "(x0+(-1))^2-(x0^2+(-2)*x0+(1))",
        "0",
        3,
        true,
        "algebraic-zero"
    },
    {
        "RING_00674",
        "(x0+(6))^2",
        "x0^2+(12)*x0+(37)",
        3,
        false,
        "false-binomial"
    },
    {
        "RING_00675",
        "(x0+(13))*(x0-(13))",
        "x0^2-(169)",
        3,
        true,
        "conjugates"
    },
    {
        "RING_00676",
        "(x0+x1+(x2+(0)))^2",
        "x0^2+x1^2+(x2+(0))^2+2*x0*x1+2*x0*(x2+(0))+2*x1*(x2+(0))",
        3,
        true,
        "multivariate-square"
    },
    {
        "RING_00677",
        "((x0+(-2))^2)*(x1+(-8))",
        "(x0^2+(-4)*x0+(4))*(x1+(-8))",
        3,
        true,
        "product-squared"
    },
    {
        "RING_00678",
        "(5)*x0+(3)*x0+(-1)*x0+(-11)*x0",
        "(-4)*x0",
        3,
        true,
        "coefficient-aggregation"
    },
    {
        "RING_00679",
        "(12)*(x0+x1+x2)^2",
        "(12)*(x0^2+x1^2+x2^2+2*x0*x1+2*x0*x2+2*x1*x2)",
        3,
        true,
        "quadratic-form"
    },
    {
        "RING_00680",
        "(x0+(-10))*(x1+(-6))",
        "x0*x1+(-6)*x0+(-10)*x1+(60)",
        3,
        true,
        "distributivity"
    },
    {
        "RING_00681",
        "(x0+(-3))^2",
        "x0^2+(-6)*x0+(9)",
        3,
        true,
        "binomial-square"
    },
    {
        "RING_00682",
        "(x0+(4))^3",
        "x0^3+(12)*x0^2+(48)*x0+(64)",
        3,
        true,
        "binomial-cube"
    },
    {
        "RING_00683",
        "(x0+(11))*(x1+(-4))",
        "(x1+(-4))*(x0+(11))",
        3,
        true,
        "commutativity"
    },
    {
        "RING_00684",
        "(x0+x1)+(x2+(-4))",
        "x0+(x1+(x2+(-4)))",
        3,
        true,
        "associativity"
    },
    {
        "RING_00685",
        "x0*x2+x1*x2+(-4)*x2",
        "(x0+x1+(-4))*x2",
        3,
        true,
        "factorization"
    },
    {
        "RING_00686",
        "(x0+(3))*(x1+(-2))-(-2)*x0-(3)*x1-(-6)",
        "x0*x1",
        3,
        true,
        "cancellation"
    },
    {
        "RING_00687",
        "((x0+0)*(x1+1))+((x2*0)+(10)-(10))",
        "x0*x1+x0",
        3,
        true,
        "neutral-elements"
    },
    {
        "RING_00688",
        "x0*(x1+(-12))-(-12)*x0",
        "x0*x1",
        3,
        true,
        "distribute-cancel"
    },
    {
        "RING_00689",
        "((x0+(-5))+x1)*((x0+(-5))-x1)",
        "(x0+(-5))^2-x1^2",
        3,
        true,
        "difference-of-squares"
    },
    {
        "RING_00690",
        "(x0+(2))^2-(x0^2+(4)*x0+(4))",
        "0",
        3,
        true,
        "algebraic-zero"
    },
    {
        "RING_00691",
        "(x0+(9))^2",
        "x0^2+(18)*x0+(82)",
        3,
        false,
        "false-binomial"
    },
    {
        "RING_00692",
        "(x0+(-13))*(x0-(-13))",
        "x0^2-(169)",
        3,
        true,
        "conjugates"
    },
    {
        "RING_00693",
        "(x0+x1+(x2+(5)))^2",
        "x0^2+x1^2+(x2+(5))^2+2*x0*x1+2*x0*(x2+(5))+2*x1*(x2+(5))",
        3,
        true,
        "multivariate-square"
    },
    {
        "RING_00694",
        "((x0+(1))^2)*(x1+(-7))",
        "(x0^2+(2)*x0+(1))*(x1+(-7))",
        3,
        true,
        "product-squared"
    },
    {
        "RING_00695",
        "(8)*x0+(4)*x0+(4)*x0+(3)*x0",
        "(19)*x0",
        3,
        true,
        "coefficient-aggregation"
    },
    {
        "RING_00696",
        "(-14)*(x0+x1+x2)^2",
        "(-14)*(x0^2+x1^2+x2^2+2*x0*x1+2*x0*x2+2*x1*x2)",
        3,
        true,
        "quadratic-form"
    },
    {
        "RING_00697",
        "(x0+(-7))*(x1+(-5))",
        "x0*x1+(-5)*x0+(-7)*x1+(35)",
        3,
        true,
        "distributivity"
    },
    {
        "RING_00698",
        "(x0+(0))^2",
        "x0^2+(0)*x0+(0)",
        3,
        true,
        "binomial-square"
    },
    {
        "RING_00699",
        "(x0+(7))^3",
        "x0^3+(21)*x0^2+(147)*x0+(343)",
        3,
        true,
        "binomial-cube"
    },
    {
        "RING_00700",
        "(x0+(14))*(x1+(-3))",
        "(x1+(-3))*(x0+(14))",
        3,
        true,
        "commutativity"
    },
    {
        "RING_00701",
        "(x0+x1)+(x2+(1))",
        "x0+(x1+(x2+(1)))",
        3,
        true,
        "associativity"
    },
    {
        "RING_00702",
        "x0*x2+x1*x2+(-1)*x2",
        "(x0+x1+(-1))*x2",
        3,
        true,
        "factorization"
    },
    {
        "RING_00703",
        "(x0+(6))*(x1+(-1))-(-1)*x0-(6)*x1-(-6)",
        "x0*x1",
        3,
        true,
        "cancellation"
    },
    {
        "RING_00704",
        "((x0+0)*(x1+1))+((x2*0)+(13)-(13))",
        "x0*x1+x0",
        3,
        true,
        "neutral-elements"
    },
    {
        "RING_00705",
        "x0*(x1+(-9))-(-9)*x0",
        "x0*x1",
        3,
        true,
        "distribute-cancel"
    },
    {
        "RING_00706",
        "((x0+(-2))+x1)*((x0+(-2))-x1)",
        "(x0+(-2))^2-x1^2",
        3,
        true,
        "difference-of-squares"
    },
    {
        "RING_00707",
        "(x0+(5))^2-(x0^2+(10)*x0+(25))",
        "0",
        3,
        true,
        "algebraic-zero"
    },
    {
        "RING_00708",
        "(x0+(12))^2",
        "x0^2+(24)*x0+(145)",
        3,
        false,
        "false-binomial"
    },
    {
        "RING_00709",
        "(x0+(-10))*(x0-(-10))",
        "x0^2-(100)",
        3,
        true,
        "conjugates"
    },
    {
        "RING_00710",
        "(x0+x1+(x2+(10)))^2",
        "x0^2+x1^2+(x2+(10))^2+2*x0*x1+2*x0*(x2+(10))+2*x1*(x2+(10))",
        3,
        true,
        "multivariate-square"
    },
    {
        "RING_00711",
        "((x0+(4))^2)*(x1+(-6))",
        "(x0^2+(8)*x0+(16))*(x1+(-6))",
        3,
        true,
        "product-squared"
    },
    {
        "RING_00712",
        "(11)*x0+(5)*x0+(9)*x0+(-8)*x0",
        "(17)*x0",
        3,
        true,
        "coefficient-aggregation"
    },
    {
        "RING_00713",
        "(-11)*(x0+x1+x2)^2",
        "(-11)*(x0^2+x1^2+x2^2+2*x0*x1+2*x0*x2+2*x1*x2)",
        3,
        true,
        "quadratic-form"
    },
    {
        "RING_00714",
        "(x0+(-4))*(x1+(-4))",
        "x0*x1+(-4)*x0+(-4)*x1+(16)",
        3,
        true,
        "distributivity"
    },
    {
        "RING_00715",
        "(x0+(3))^2",
        "x0^2+(6)*x0+(9)",
        3,
        true,
        "binomial-square"
    },
    {
        "RING_00716",
        "(x0+(10))^3",
        "x0^3+(30)*x0^2+(300)*x0+(1000)",
        3,
        true,
        "binomial-cube"
    },
    {
        "RING_00717",
        "(x0+(-12))*(x1+(-2))",
        "(x1+(-2))*(x0+(-12))",
        3,
        true,
        "commutativity"
    },
    {
        "RING_00718",
        "(x0+x1)+(x2+(6))",
        "x0+(x1+(x2+(6)))",
        3,
        true,
        "associativity"
    },
    {
        "RING_00719",
        "x0*x2+x1*x2+(2)*x2",
        "(x0+x1+(2))*x2",
        3,
        true,
        "factorization"
    },
    {
        "RING_00720",
        "(x0+(9))*(x1+(0))-(0)*x0-(9)*x1-(0)",
        "x0*x1",
        3,
        true,
        "cancellation"
    },
    {
        "RING_00721",
        "((x0+0)*(x1+1))+((x2*0)+(-13)-(-13))",
        "x0*x1+x0",
        3,
        true,
        "neutral-elements"
    },
    {
        "RING_00722",
        "x0*(x1+(-6))-(-6)*x0",
        "x0*x1",
        3,
        true,
        "distribute-cancel"
    },
    {
        "RING_00723",
        "((x0+(1))+x1)*((x0+(1))-x1)",
        "(x0+(1))^2-x1^2",
        3,
        true,
        "difference-of-squares"
    },
    {
        "RING_00724",
        "(x0+(8))^2-(x0^2+(16)*x0+(64))",
        "0",
        3,
        true,
        "algebraic-zero"
    },
    {
        "RING_00725",
        "(x0+(-14))^2",
        "x0^2+(-28)*x0+(197)",
        3,
        false,
        "false-binomial"
    },
    {
        "RING_00726",
        "(x0+(-7))*(x0-(-7))",
        "x0^2-(49)",
        3,
        true,
        "conjugates"
    },
    {
        "RING_00727",
        "(x0+x1+(x2+(-12)))^2",
        "x0^2+x1^2+(x2+(-12))^2+2*x0*x1+2*x0*(x2+(-12))+2*x1*(x2+(-12))",
        3,
        true,
        "multivariate-square"
    },
    {
        "RING_00728",
        "((x0+(7))^2)*(x1+(-5))",
        "(x0^2+(14)*x0+(49))*(x1+(-5))",
        3,
        true,
        "product-squared"
    },
    {
        "RING_00729",
        "(14)*x0+(6)*x0+(-13)*x0+(6)*x0",
        "(13)*x0",
        3,
        true,
        "coefficient-aggregation"
    },
    {
        "RING_00730",
        "(-8)*(x0+x1+x2)^2",
        "(-8)*(x0^2+x1^2+x2^2+2*x0*x1+2*x0*x2+2*x1*x2)",
        3,
        true,
        "quadratic-form"
    },
    {
        "RING_00731",
        "(x0+(-1))*(x1+(-3))",
        "x0*x1+(-3)*x0+(-1)*x1+(3)",
        3,
        true,
        "distributivity"
    },
    {
        "RING_00732",
        "(x0+(6))^2",
        "x0^2+(12)*x0+(36)",
        3,
        true,
        "binomial-square"
    },
    {
        "RING_00733",
        "(x0+(13))^3",
        "x0^3+(39)*x0^2+(507)*x0+(2197)",
        3,
        true,
        "binomial-cube"
    },
    {
        "RING_00734",
        "(x0+(-9))*(x1+(-1))",
        "(x1+(-1))*(x0+(-9))",
        3,
        true,
        "commutativity"
    },
    {
        "RING_00735",
        "(x0+x1)+(x2+(11))",
        "x0+(x1+(x2+(11)))",
        3,
        true,
        "associativity"
    },
    {
        "RING_00736",
        "x0*x2+x1*x2+(5)*x2",
        "(x0+x1+(5))*x2",
        3,
        true,
        "factorization"
    },
    {
        "RING_00737",
        "(x0+(12))*(x1+(1))-(1)*x0-(12)*x1-(12)",
        "x0*x1",
        3,
        true,
        "cancellation"
    },
    {
        "RING_00738",
        "((x0+0)*(x1+1))+((x2*0)+(-10)-(-10))",
        "x0*x1+x0",
        3,
        true,
        "neutral-elements"
    },
    {
        "RING_00739",
        "x0*(x1+(-3))-(-3)*x0",
        "x0*x1",
        3,
        true,
        "distribute-cancel"
    },
    {
        "RING_00740",
        "((x0+(4))+x1)*((x0+(4))-x1)",
        "(x0+(4))^2-x1^2",
        3,
        true,
        "difference-of-squares"
    },
    {
        "RING_00741",
        "(x0+(11))^2-(x0^2+(22)*x0+(121))",
        "0",
        3,
        true,
        "algebraic-zero"
    },
    {
        "RING_00742",
        "(x0+(-11))^2",
        "x0^2+(-22)*x0+(122)",
        3,
        false,
        "false-binomial"
    },
    {
        "RING_00743",
        "(x0+(-4))*(x0-(-4))",
        "x0^2-(16)",
        3,
        true,
        "conjugates"
    },
    {
        "RING_00744",
        "(x0+x1+(x2+(-7)))^2",
        "x0^2+x1^2+(x2+(-7))^2+2*x0*x1+2*x0*(x2+(-7))+2*x1*(x2+(-7))",
        3,
        true,
        "multivariate-square"
    },
    {
        "RING_00745",
        "((x0+(10))^2)*(x1+(-4))",
        "(x0^2+(20)*x0+(100))*(x1+(-4))",
        3,
        true,
        "product-squared"
    },
    {
        "RING_00746",
        "(-12)*x0+(7)*x0+(-8)*x0+(-5)*x0",
        "(-18)*x0",
        3,
        true,
        "coefficient-aggregation"
    },
    {
        "RING_00747",
        "(-5)*(x0+x1+x2)^2",
        "(-5)*(x0^2+x1^2+x2^2+2*x0*x1+2*x0*x2+2*x1*x2)",
        3,
        true,
        "quadratic-form"
    },
    {
        "RING_00748",
        "(x0+(2))*(x1+(-2))",
        "x0*x1+(-2)*x0+(2)*x1+(-4)",
        3,
        true,
        "distributivity"
    },
    {
        "RING_00749",
        "(x0+(9))^2",
        "x0^2+(18)*x0+(81)",
        3,
        true,
        "binomial-square"
    },
    {
        "RING_00750",
        "(x0+(-13))^3",
        "x0^3+(-39)*x0^2+(507)*x0+(-2197)",
        3,
        true,
        "binomial-cube"
    },
    {
        "RING_00751",
        "(x0+(-6))*(x1+(0))",
        "(x1+(0))*(x0+(-6))",
        3,
        true,
        "commutativity"
    },
    {
        "RING_00752",
        "(x0+x1)+(x2+(-11))",
        "x0+(x1+(x2+(-11)))",
        3,
        true,
        "associativity"
    },
    {
        "RING_00753",
        "x0*x2+x1*x2+(8)*x2",
        "(x0+x1+(8))*x2",
        3,
        true,
        "factorization"
    },
    {
        "RING_00754",
        "(x0+(-14))*(x1+(2))-(2)*x0-(-14)*x1-(-28)",
        "x0*x1",
        3,
        true,
        "cancellation"
    },
    {
        "RING_00755",
        "((x0+0)*(x1+1))+((x2*0)+(-7)-(-7))",
        "x0*x1+x0",
        3,
        true,
        "neutral-elements"
    },
    {
        "RING_00756",
        "x0*(x1+(0))-(0)*x0",
        "x0*x1",
        3,
        true,
        "distribute-cancel"
    },
    {
        "RING_00757",
        "((x0+(7))+x1)*((x0+(7))-x1)",
        "(x0+(7))^2-x1^2",
        3,
        true,
        "difference-of-squares"
    },
    {
        "RING_00758",
        "(x0+(14))^2-(x0^2+(28)*x0+(196))",
        "0",
        3,
        true,
        "algebraic-zero"
    },
    {
        "RING_00759",
        "(x0+(-8))^2",
        "x0^2+(-16)*x0+(65)",
        3,
        false,
        "false-binomial"
    },
    {
        "RING_00760",
        "(x0+(-1))*(x0-(-1))",
        "x0^2-(1)",
        3,
        true,
        "conjugates"
    },
    {
        "RING_00761",
        "(x0+x1+(x2+(-2)))^2",
        "x0^2+x1^2+(x2+(-2))^2+2*x0*x1+2*x0*(x2+(-2))+2*x1*(x2+(-2))",
        3,
        true,
        "multivariate-square"
    },
    {
        "RING_00762",
        "((x0+(13))^2)*(x1+(-3))",
        "(x0^2+(26)*x0+(169))*(x1+(-3))",
        3,
        true,
        "product-squared"
    },
    {
        "RING_00763",
        "(-9)*x0+(8)*x0+(-3)*x0+(9)*x0",
        "(5)*x0",
        3,
        true,
        "coefficient-aggregation"
    },
    {
        "RING_00764",
        "(-2)*(x0+x1+x2)^2",
        "(-2)*(x0^2+x1^2+x2^2+2*x0*x1+2*x0*x2+2*x1*x2)",
        3,
        true,
        "quadratic-form"
    },
    {
        "RING_00765",
        "(x0+(5))*(x1+(-1))",
        "x0*x1+(-1)*x0+(5)*x1+(-5)",
        3,
        true,
        "distributivity"
    },
    {
        "RING_00766",
        "(x0+(12))^2",
        "x0^2+(24)*x0+(144)",
        3,
        true,
        "binomial-square"
    },
    {
        "RING_00767",
        "(x0+(-10))^3",
        "x0^3+(-30)*x0^2+(300)*x0+(-1000)",
        3,
        true,
        "binomial-cube"
    },
    {
        "RING_00768",
        "(x0+(-3))*(x1+(1))",
        "(x1+(1))*(x0+(-3))",
        3,
        true,
        "commutativity"
    },
    {
        "RING_00769",
        "(x0+x1)+(x2+(-6))",
        "x0+(x1+(x2+(-6)))",
        3,
        true,
        "associativity"
    },
    {
        "RING_00770",
        "x0*x2+x1*x2+(11)*x2",
        "(x0+x1+(11))*x2",
        3,
        true,
        "factorization"
    },
    {
        "RING_00771",
        "(x0+(-11))*(x1+(3))-(3)*x0-(-11)*x1-(-33)",
        "x0*x1",
        3,
        true,
        "cancellation"
    },
    {
        "RING_00772",
        "((x0+0)*(x1+1))+((x2*0)+(-4)-(-4))",
        "x0*x1+x0",
        3,
        true,
        "neutral-elements"
    },
    {
        "RING_00773",
        "x0*(x1+(3))-(3)*x0",
        "x0*x1",
        3,
        true,
        "distribute-cancel"
    },
    {
        "RING_00774",
        "((x0+(10))+x1)*((x0+(10))-x1)",
        "(x0+(10))^2-x1^2",
        3,
        true,
        "difference-of-squares"
    },
    {
        "RING_00775",
        "(x0+(-12))^2-(x0^2+(-24)*x0+(144))",
        "0",
        3,
        true,
        "algebraic-zero"
    },
    {
        "RING_00776",
        "(x0+(-5))^2",
        "x0^2+(-10)*x0+(26)",
        3,
        false,
        "false-binomial"
    },
    {
        "RING_00777",
        "(x0+(2))*(x0-(2))",
        "x0^2-(4)",
        3,
        true,
        "conjugates"
    },
    {
        "RING_00778",
        "(x0+x1+(x2+(3)))^2",
        "x0^2+x1^2+(x2+(3))^2+2*x0*x1+2*x0*(x2+(3))+2*x1*(x2+(3))",
        3,
        true,
        "multivariate-square"
    },
    {
        "RING_00779",
        "((x0+(-13))^2)*(x1+(-2))",
        "(x0^2+(-26)*x0+(169))*(x1+(-2))",
        3,
        true,
        "product-squared"
    },
    {
        "RING_00780",
        "(-6)*x0+(9)*x0+(2)*x0+(-2)*x0",
        "(3)*x0",
        3,
        true,
        "coefficient-aggregation"
    },
    {
        "RING_00781",
        "(1)*(x0+x1+x2)^2",
        "(1)*(x0^2+x1^2+x2^2+2*x0*x1+2*x0*x2+2*x1*x2)",
        3,
        true,
        "quadratic-form"
    },
    {
        "RING_00782",
        "(x0+(8))*(x1+(0))",
        "x0*x1+(0)*x0+(8)*x1+(0)",
        3,
        true,
        "distributivity"
    },
    {
        "RING_00783",
        "(x0+(-14))^2",
        "x0^2+(-28)*x0+(196)",
        3,
        true,
        "binomial-square"
    },
    {
        "RING_00784",
        "(x0+(-7))^3",
        "x0^3+(-21)*x0^2+(147)*x0+(-343)",
        3,
        true,
        "binomial-cube"
    },
    {
        "RING_00785",
        "(x0+(0))*(x1+(2))",
        "(x1+(2))*(x0+(0))",
        3,
        true,
        "commutativity"
    },
    {
        "RING_00786",
        "(x0+x1)+(x2+(-1))",
        "x0+(x1+(x2+(-1)))",
        3,
        true,
        "associativity"
    },
    {
        "RING_00787",
        "x0*x2+x1*x2+(14)*x2",
        "(x0+x1+(14))*x2",
        3,
        true,
        "factorization"
    },
    {
        "RING_00788",
        "(x0+(-8))*(x1+(4))-(4)*x0-(-8)*x1-(-32)",
        "x0*x1",
        3,
        true,
        "cancellation"
    },
    {
        "RING_00789",
        "((x0+0)*(x1+1))+((x2*0)+(-1)-(-1))",
        "x0*x1+x0",
        3,
        true,
        "neutral-elements"
    },
    {
        "RING_00790",
        "x0*(x1+(6))-(6)*x0",
        "x0*x1",
        3,
        true,
        "distribute-cancel"
    },
    {
        "RING_00791",
        "((x0+(13))+x1)*((x0+(13))-x1)",
        "(x0+(13))^2-x1^2",
        3,
        true,
        "difference-of-squares"
    },
    {
        "RING_00792",
        "(x0+(-9))^2-(x0^2+(-18)*x0+(81))",
        "0",
        3,
        true,
        "algebraic-zero"
    },
    {
        "RING_00793",
        "(x0+(-2))^2",
        "x0^2+(-4)*x0+(5)",
        3,
        false,
        "false-binomial"
    },
    {
        "RING_00794",
        "(x0+(5))*(x0-(5))",
        "x0^2-(25)",
        3,
        true,
        "conjugates"
    },
    {
        "RING_00795",
        "(x0+x1+(x2+(8)))^2",
        "x0^2+x1^2+(x2+(8))^2+2*x0*x1+2*x0*(x2+(8))+2*x1*(x2+(8))",
        3,
        true,
        "multivariate-square"
    },
    {
        "RING_00796",
        "((x0+(-10))^2)*(x1+(-1))",
        "(x0^2+(-20)*x0+(100))*(x1+(-1))",
        3,
        true,
        "product-squared"
    },
    {
        "RING_00797",
        "(-3)*x0+(10)*x0+(7)*x0+(12)*x0",
        "(26)*x0",
        3,
        true,
        "coefficient-aggregation"
    },
    {
        "RING_00798",
        "(4)*(x0+x1+x2)^2",
        "(4)*(x0^2+x1^2+x2^2+2*x0*x1+2*x0*x2+2*x1*x2)",
        3,
        true,
        "quadratic-form"
    },
    {
        "RING_00799",
        "(x0+(11))*(x1+(1))",
        "x0*x1+(1)*x0+(11)*x1+(11)",
        3,
        true,
        "distributivity"
    },
    {
        "RING_00800",
        "(x0+(-11))^2",
        "x0^2+(-22)*x0+(121)",
        3,
        true,
        "binomial-square"
    },
    {
        "RING_00801",
        "(x0+(-4))^3",
        "x0^3+(-12)*x0^2+(48)*x0+(-64)",
        3,
        true,
        "binomial-cube"
    },
    {
        "RING_00802",
        "(x0+(3))*(x1+(3))",
        "(x1+(3))*(x0+(3))",
        3,
        true,
        "commutativity"
    },
    {
        "RING_00803",
        "(x0+x1)+(x2+(4))",
        "x0+(x1+(x2+(4)))",
        3,
        true,
        "associativity"
    },
    {
        "RING_00804",
        "x0*x2+x1*x2+(-12)*x2",
        "(x0+x1+(-12))*x2",
        3,
        true,
        "factorization"
    },
    {
        "RING_00805",
        "(x0+(-5))*(x1+(5))-(5)*x0-(-5)*x1-(-25)",
        "x0*x1",
        3,
        true,
        "cancellation"
    },
    {
        "RING_00806",
        "((x0+0)*(x1+1))+((x2*0)+(2)-(2))",
        "x0*x1+x0",
        3,
        true,
        "neutral-elements"
    },
    {
        "RING_00807",
        "x0*(x1+(9))-(9)*x0",
        "x0*x1",
        3,
        true,
        "distribute-cancel"
    },
    {
        "RING_00808",
        "((x0+(-13))+x1)*((x0+(-13))-x1)",
        "(x0+(-13))^2-x1^2",
        3,
        true,
        "difference-of-squares"
    },
    {
        "RING_00809",
        "(x0+(-6))^2-(x0^2+(-12)*x0+(36))",
        "0",
        3,
        true,
        "algebraic-zero"
    },
    {
        "RING_00810",
        "(x0+(1))^2",
        "x0^2+(2)*x0+(2)",
        3,
        false,
        "false-binomial"
    },
    {
        "RING_00811",
        "(x0+(8))*(x0-(8))",
        "x0^2-(64)",
        3,
        true,
        "conjugates"
    },
    {
        "RING_00812",
        "(x0+x1+(x2+(13)))^2",
        "x0^2+x1^2+(x2+(13))^2+2*x0*x1+2*x0*(x2+(13))+2*x1*(x2+(13))",
        3,
        true,
        "multivariate-square"
    },
    {
        "RING_00813",
        "((x0+(-7))^2)*(x1+(0))",
        "(x0^2+(-14)*x0+(49))*(x1+(0))",
        3,
        true,
        "product-squared"
    },
    {
        "RING_00814",
        "(0)*x0+(11)*x0+(12)*x0+(1)*x0",
        "(24)*x0",
        3,
        true,
        "coefficient-aggregation"
    },
    {
        "RING_00815",
        "(7)*(x0+x1+x2)^2",
        "(7)*(x0^2+x1^2+x2^2+2*x0*x1+2*x0*x2+2*x1*x2)",
        3,
        true,
        "quadratic-form"
    },
    {
        "RING_00816",
        "(x0+(14))*(x1+(2))",
        "x0*x1+(2)*x0+(14)*x1+(28)",
        3,
        true,
        "distributivity"
    },
    {
        "RING_00817",
        "(x0+(-8))^2",
        "x0^2+(-16)*x0+(64)",
        3,
        true,
        "binomial-square"
    },
    {
        "RING_00818",
        "(x0+(-1))^3",
        "x0^3+(-3)*x0^2+(3)*x0+(-1)",
        3,
        true,
        "binomial-cube"
    },
    {
        "RING_00819",
        "(x0+(6))*(x1+(4))",
        "(x1+(4))*(x0+(6))",
        3,
        true,
        "commutativity"
    },
    {
        "RING_00820",
        "(x0+x1)+(x2+(9))",
        "x0+(x1+(x2+(9)))",
        3,
        true,
        "associativity"
    },
    {
        "RING_00821",
        "x0*x2+x1*x2+(-9)*x2",
        "(x0+x1+(-9))*x2",
        3,
        true,
        "factorization"
    },
    {
        "RING_00822",
        "(x0+(-2))*(x1+(6))-(6)*x0-(-2)*x1-(-12)",
        "x0*x1",
        3,
        true,
        "cancellation"
    },
    {
        "RING_00823",
        "((x0+0)*(x1+1))+((x2*0)+(5)-(5))",
        "x0*x1+x0",
        3,
        true,
        "neutral-elements"
    },
    {
        "RING_00824",
        "x0*(x1+(12))-(12)*x0",
        "x0*x1",
        3,
        true,
        "distribute-cancel"
    },
    {
        "RING_00825",
        "((x0+(-10))+x1)*((x0+(-10))-x1)",
        "(x0+(-10))^2-x1^2",
        3,
        true,
        "difference-of-squares"
    },
    {
        "RING_00826",
        "(x0+(-3))^2-(x0^2+(-6)*x0+(9))",
        "0",
        3,
        true,
        "algebraic-zero"
    },
    {
        "RING_00827",
        "(x0+(4))^2",
        "x0^2+(8)*x0+(17)",
        3,
        false,
        "false-binomial"
    },
    {
        "RING_00828",
        "(x0+(11))*(x0-(11))",
        "x0^2-(121)",
        3,
        true,
        "conjugates"
    },
    {
        "RING_00829",
        "(x0+x1+(x2+(-9)))^2",
        "x0^2+x1^2+(x2+(-9))^2+2*x0*x1+2*x0*(x2+(-9))+2*x1*(x2+(-9))",
        3,
        true,
        "multivariate-square"
    },
    {
        "RING_00830",
        "((x0+(-4))^2)*(x1+(1))",
        "(x0^2+(-8)*x0+(16))*(x1+(1))",
        3,
        true,
        "product-squared"
    },
    {
        "RING_00831",
        "(3)*x0+(12)*x0+(-10)*x0+(-10)*x0",
        "(-5)*x0",
        3,
        true,
        "coefficient-aggregation"
    },
    {
        "RING_00832",
        "(10)*(x0+x1+x2)^2",
        "(10)*(x0^2+x1^2+x2^2+2*x0*x1+2*x0*x2+2*x1*x2)",
        3,
        true,
        "quadratic-form"
    },
    {
        "RING_00833",
        "(x0+(-12))*(x1+(3))",
        "x0*x1+(3)*x0+(-12)*x1+(-36)",
        3,
        true,
        "distributivity"
    },
    {
        "RING_00834",
        "(x0+(-5))^2",
        "x0^2+(-10)*x0+(25)",
        3,
        true,
        "binomial-square"
    },
    {
        "RING_00835",
        "(x0+(2))^3",
        "x0^3+(6)*x0^2+(12)*x0+(8)",
        3,
        true,
        "binomial-cube"
    },
    {
        "RING_00836",
        "(x0+(9))*(x1+(5))",
        "(x1+(5))*(x0+(9))",
        3,
        true,
        "commutativity"
    },
    {
        "RING_00837",
        "(x0+x1)+(x2+(-13))",
        "x0+(x1+(x2+(-13)))",
        3,
        true,
        "associativity"
    },
    {
        "RING_00838",
        "x0*x2+x1*x2+(-6)*x2",
        "(x0+x1+(-6))*x2",
        3,
        true,
        "factorization"
    },
    {
        "RING_00839",
        "(x0+(1))*(x1+(7))-(7)*x0-(1)*x1-(7)",
        "x0*x1",
        3,
        true,
        "cancellation"
    },
    {
        "RING_00840",
        "((x0+0)*(x1+1))+((x2*0)+(8)-(8))",
        "x0*x1+x0",
        3,
        true,
        "neutral-elements"
    },
    {
        "RING_00841",
        "x0*(x1+(-14))-(-14)*x0",
        "x0*x1",
        3,
        true,
        "distribute-cancel"
    },
    {
        "RING_00842",
        "((x0+(-7))+x1)*((x0+(-7))-x1)",
        "(x0+(-7))^2-x1^2",
        3,
        true,
        "difference-of-squares"
    },
    {
        "RING_00843",
        "(x0+(0))^2-(x0^2+(0)*x0+(0))",
        "0",
        3,
        true,
        "algebraic-zero"
    },
    {
        "RING_00844",
        "(x0+(7))^2",
        "x0^2+(14)*x0+(50)",
        3,
        false,
        "false-binomial"
    },
    {
        "RING_00845",
        "(x0+(14))*(x0-(14))",
        "x0^2-(196)",
        3,
        true,
        "conjugates"
    },
    {
        "RING_00846",
        "(x0+x1+(x2+(-4)))^2",
        "x0^2+x1^2+(x2+(-4))^2+2*x0*x1+2*x0*(x2+(-4))+2*x1*(x2+(-4))",
        3,
        true,
        "multivariate-square"
    },
    {
        "RING_00847",
        "((x0+(-1))^2)*(x1+(2))",
        "(x0^2+(-2)*x0+(1))*(x1+(2))",
        3,
        true,
        "product-squared"
    },
    {
        "RING_00848",
        "(6)*x0+(13)*x0+(-5)*x0+(4)*x0",
        "(18)*x0",
        3,
        true,
        "coefficient-aggregation"
    },
    {
        "RING_00849",
        "(13)*(x0+x1+x2)^2",
        "(13)*(x0^2+x1^2+x2^2+2*x0*x1+2*x0*x2+2*x1*x2)",
        3,
        true,
        "quadratic-form"
    },
    {
        "RING_00850",
        "(x0+(-9))*(x1+(4))",
        "x0*x1+(4)*x0+(-9)*x1+(-36)",
        3,
        true,
        "distributivity"
    },
    {
        "RING_00851",
        "(x0+(-2))^2",
        "x0^2+(-4)*x0+(4)",
        3,
        true,
        "binomial-square"
    },
    {
        "RING_00852",
        "(x0+(5))^3",
        "x0^3+(15)*x0^2+(75)*x0+(125)",
        3,
        true,
        "binomial-cube"
    },
    {
        "RING_00853",
        "(x0+(12))*(x1+(6))",
        "(x1+(6))*(x0+(12))",
        3,
        true,
        "commutativity"
    },
    {
        "RING_00854",
        "(x0+x1)+(x2+(-8))",
        "x0+(x1+(x2+(-8)))",
        3,
        true,
        "associativity"
    },
    {
        "RING_00855",
        "x0*x2+x1*x2+(-3)*x2",
        "(x0+x1+(-3))*x2",
        3,
        true,
        "factorization"
    },
    {
        "RING_00856",
        "(x0+(4))*(x1+(8))-(8)*x0-(4)*x1-(32)",
        "x0*x1",
        3,
        true,
        "cancellation"
    },
    {
        "RING_00857",
        "((x0+0)*(x1+1))+((x2*0)+(11)-(11))",
        "x0*x1+x0",
        3,
        true,
        "neutral-elements"
    },
    {
        "RING_00858",
        "x0*(x1+(-11))-(-11)*x0",
        "x0*x1",
        3,
        true,
        "distribute-cancel"
    },
    {
        "RING_00859",
        "((x0+(-4))+x1)*((x0+(-4))-x1)",
        "(x0+(-4))^2-x1^2",
        3,
        true,
        "difference-of-squares"
    },
    {
        "RING_00860",
        "(x0+(3))^2-(x0^2+(6)*x0+(9))",
        "0",
        3,
        true,
        "algebraic-zero"
    },
    {
        "RING_00861",
        "(x0+(10))^2",
        "x0^2+(20)*x0+(101)",
        3,
        false,
        "false-binomial"
    },
    {
        "RING_00862",
        "(x0+(-12))*(x0-(-12))",
        "x0^2-(144)",
        3,
        true,
        "conjugates"
    },
    {
        "RING_00863",
        "(x0+x1+(x2+(1)))^2",
        "x0^2+x1^2+(x2+(1))^2+2*x0*x1+2*x0*(x2+(1))+2*x1*(x2+(1))",
        3,
        true,
        "multivariate-square"
    },
    {
        "RING_00864",
        "((x0+(2))^2)*(x1+(3))",
        "(x0^2+(4)*x0+(4))*(x1+(3))",
        3,
        true,
        "product-squared"
    },
    {
        "RING_00865",
        "(9)*x0+(14)*x0+(0)*x0+(-7)*x0",
        "(16)*x0",
        3,
        true,
        "coefficient-aggregation"
    },
    {
        "RING_00866",
        "(-13)*(x0+x1+x2)^2",
        "(-13)*(x0^2+x1^2+x2^2+2*x0*x1+2*x0*x2+2*x1*x2)",
        3,
        true,
        "quadratic-form"
    },
    {
        "RING_00867",
        "(x0+(-6))*(x1+(5))",
        "x0*x1+(5)*x0+(-6)*x1+(-30)",
        3,
        true,
        "distributivity"
    },
    {
        "RING_00868",
        "(x0+(1))^2",
        "x0^2+(2)*x0+(1)",
        3,
        true,
        "binomial-square"
    },
    {
        "RING_00869",
        "(x0+(8))^3",
        "x0^3+(24)*x0^2+(192)*x0+(512)",
        3,
        true,
        "binomial-cube"
    },
    {
        "RING_00870",
        "(x0+(-14))*(x1+(7))",
        "(x1+(7))*(x0+(-14))",
        3,
        true,
        "commutativity"
    },
    {
        "RING_00871",
        "(x0+x1)+(x2+(-3))",
        "x0+(x1+(x2+(-3)))",
        3,
        true,
        "associativity"
    },
    {
        "RING_00872",
        "x0*x2+x1*x2+(0)*x2",
        "(x0+x1+(0))*x2",
        3,
        true,
        "factorization"
    },
    {
        "RING_00873",
        "(x0+(7))*(x1+(9))-(9)*x0-(7)*x1-(63)",
        "x0*x1",
        3,
        true,
        "cancellation"
    },
    {
        "RING_00874",
        "((x0+0)*(x1+1))+((x2*0)+(14)-(14))",
        "x0*x1+x0",
        3,
        true,
        "neutral-elements"
    },
    {
        "RING_00875",
        "x0*(x1+(-8))-(-8)*x0",
        "x0*x1",
        3,
        true,
        "distribute-cancel"
    },
    {
        "RING_00876",
        "((x0+(-1))+x1)*((x0+(-1))-x1)",
        "(x0+(-1))^2-x1^2",
        3,
        true,
        "difference-of-squares"
    },
    {
        "RING_00877",
        "(x0+(6))^2-(x0^2+(12)*x0+(36))",
        "0",
        3,
        true,
        "algebraic-zero"
    },
    {
        "RING_00878",
        "(x0+(13))^2",
        "x0^2+(26)*x0+(170)",
        3,
        false,
        "false-binomial"
    },
    {
        "RING_00879",
        "(x0+(-9))*(x0-(-9))",
        "x0^2-(81)",
        3,
        true,
        "conjugates"
    },
    {
        "RING_00880",
        "(x0+x1+(x2+(6)))^2",
        "x0^2+x1^2+(x2+(6))^2+2*x0*x1+2*x0*(x2+(6))+2*x1*(x2+(6))",
        3,
        true,
        "multivariate-square"
    },
    {
        "RING_00881",
        "((x0+(5))^2)*(x1+(4))",
        "(x0^2+(10)*x0+(25))*(x1+(4))",
        3,
        true,
        "product-squared"
    },
    {
        "RING_00882",
        "(12)*x0+(15)*x0+(5)*x0+(7)*x0",
        "(39)*x0",
        3,
        true,
        "coefficient-aggregation"
    },
    {
        "RING_00883",
        "(-10)*(x0+x1+x2)^2",
        "(-10)*(x0^2+x1^2+x2^2+2*x0*x1+2*x0*x2+2*x1*x2)",
        3,
        true,
        "quadratic-form"
    },
    {
        "RING_00884",
        "(x0+(-3))*(x1+(6))",
        "x0*x1+(6)*x0+(-3)*x1+(-18)",
        3,
        true,
        "distributivity"
    },
    {
        "RING_00885",
        "(x0+(4))^2",
        "x0^2+(8)*x0+(16)",
        3,
        true,
        "binomial-square"
    },
    {
        "RING_00886",
        "(x0+(11))^3",
        "x0^3+(33)*x0^2+(363)*x0+(1331)",
        3,
        true,
        "binomial-cube"
    },
    {
        "RING_00887",
        "(x0+(-11))*(x1+(8))",
        "(x1+(8))*(x0+(-11))",
        3,
        true,
        "commutativity"
    },
    {
        "RING_00888",
        "(x0+x1)+(x2+(2))",
        "x0+(x1+(x2+(2)))",
        3,
        true,
        "associativity"
    },
    {
        "RING_00889",
        "x0*x2+x1*x2+(3)*x2",
        "(x0+x1+(3))*x2",
        3,
        true,
        "factorization"
    },
    {
        "RING_00890",
        "(x0+(10))*(x1+(10))-(10)*x0-(10)*x1-(100)",
        "x0*x1",
        3,
        true,
        "cancellation"
    },
    {
        "RING_00891",
        "((x0+0)*(x1+1))+((x2*0)+(-12)-(-12))",
        "x0*x1+x0",
        3,
        true,
        "neutral-elements"
    },
    {
        "RING_00892",
        "x0*(x1+(-5))-(-5)*x0",
        "x0*x1",
        3,
        true,
        "distribute-cancel"
    },
    {
        "RING_00893",
        "((x0+(2))+x1)*((x0+(2))-x1)",
        "(x0+(2))^2-x1^2",
        3,
        true,
        "difference-of-squares"
    },
    {
        "RING_00894",
        "(x0+(9))^2-(x0^2+(18)*x0+(81))",
        "0",
        3,
        true,
        "algebraic-zero"
    },
    {
        "RING_00895",
        "(x0+(-13))^2",
        "x0^2+(-26)*x0+(170)",
        3,
        false,
        "false-binomial"
    },
    {
        "RING_00896",
        "(x0+(-6))*(x0-(-6))",
        "x0^2-(36)",
        3,
        true,
        "conjugates"
    },
    {
        "RING_00897",
        "(x0+x1+(x2+(11)))^2",
        "x0^2+x1^2+(x2+(11))^2+2*x0*x1+2*x0*(x2+(11))+2*x1*(x2+(11))",
        3,
        true,
        "multivariate-square"
    },
    {
        "RING_00898",
        "((x0+(8))^2)*(x1+(5))",
        "(x0^2+(16)*x0+(64))*(x1+(5))",
        3,
        true,
        "product-squared"
    },
    {
        "RING_00899",
        "(-14)*x0+(-15)*x0+(10)*x0+(-4)*x0",
        "(-23)*x0",
        3,
        true,
        "coefficient-aggregation"
    },
    {
        "RING_00900",
        "(-7)*(x0+x1+x2)^2",
        "(-7)*(x0^2+x1^2+x2^2+2*x0*x1+2*x0*x2+2*x1*x2)",
        3,
        true,
        "quadratic-form"
    },
    {
        "RING_00901",
        "(x0+(0))*(x1+(7))",
        "x0*x1+(7)*x0+(0)*x1+(0)",
        3,
        true,
        "distributivity"
    },
    {
        "RING_00902",
        "(x0+(7))^2",
        "x0^2+(14)*x0+(49)",
        3,
        true,
        "binomial-square"
    },
    {
        "RING_00903",
        "(x0+(14))^3",
        "x0^3+(42)*x0^2+(588)*x0+(2744)",
        3,
        true,
        "binomial-cube"
    },
    {
        "RING_00904",
        "(x0+(-8))*(x1+(9))",
        "(x1+(9))*(x0+(-8))",
        3,
        true,
        "commutativity"
    },
    {
        "RING_00905",
        "(x0+x1)+(x2+(7))",
        "x0+(x1+(x2+(7)))",
        3,
        true,
        "associativity"
    },
    {
        "RING_00906",
        "x0*x2+x1*x2+(6)*x2",
        "(x0+x1+(6))*x2",
        3,
        true,
        "factorization"
    },
    {
        "RING_00907",
        "(x0+(13))*(x1+(11))-(11)*x0-(13)*x1-(143)",
        "x0*x1",
        3,
        true,
        "cancellation"
    },
    {
        "RING_00908",
        "((x0+0)*(x1+1))+((x2*0)+(-9)-(-9))",
        "x0*x1+x0",
        3,
        true,
        "neutral-elements"
    },
    {
        "RING_00909",
        "x0*(x1+(-2))-(-2)*x0",
        "x0*x1",
        3,
        true,
        "distribute-cancel"
    },
    {
        "RING_00910",
        "((x0+(5))+x1)*((x0+(5))-x1)",
        "(x0+(5))^2-x1^2",
        3,
        true,
        "difference-of-squares"
    },
    {
        "RING_00911",
        "(x0+(12))^2-(x0^2+(24)*x0+(144))",
        "0",
        3,
        true,
        "algebraic-zero"
    },
    {
        "RING_00912",
        "(x0+(-10))^2",
        "x0^2+(-20)*x0+(101)",
        3,
        false,
        "false-binomial"
    },
    {
        "RING_00913",
        "(x0+(-3))*(x0-(-3))",
        "x0^2-(9)",
        3,
        true,
        "conjugates"
    },
    {
        "RING_00914",
        "(x0+x1+(x2+(-11)))^2",
        "x0^2+x1^2+(x2+(-11))^2+2*x0*x1+2*x0*(x2+(-11))+2*x1*(x2+(-11))",
        3,
        true,
        "multivariate-square"
    },
    {
        "RING_00915",
        "((x0+(11))^2)*(x1+(6))",
        "(x0^2+(22)*x0+(121))*(x1+(6))",
        3,
        true,
        "product-squared"
    },
    {
        "RING_00916",
        "(-11)*x0+(-14)*x0+(-12)*x0+(10)*x0",
        "(-27)*x0",
        3,
        true,
        "coefficient-aggregation"
    },
    {
        "RING_00917",
        "(-4)*(x0+x1+x2)^2",
        "(-4)*(x0^2+x1^2+x2^2+2*x0*x1+2*x0*x2+2*x1*x2)",
        3,
        true,
        "quadratic-form"
    },
    {
        "RING_00918",
        "(x0+(3))*(x1+(8))",
        "x0*x1+(8)*x0+(3)*x1+(24)",
        3,
        true,
        "distributivity"
    },
    {
        "RING_00919",
        "(x0+(10))^2",
        "x0^2+(20)*x0+(100)",
        3,
        true,
        "binomial-square"
    },
    {
        "RING_00920",
        "(x0+(-12))^3",
        "x0^3+(-36)*x0^2+(432)*x0+(-1728)",
        3,
        true,
        "binomial-cube"
    },
    {
        "RING_00921",
        "(x0+(-5))*(x1+(10))",
        "(x1+(10))*(x0+(-5))",
        3,
        true,
        "commutativity"
    },
    {
        "RING_00922",
        "(x0+x1)+(x2+(12))",
        "x0+(x1+(x2+(12)))",
        3,
        true,
        "associativity"
    },
    {
        "RING_00923",
        "x0*x2+x1*x2+(9)*x2",
        "(x0+x1+(9))*x2",
        3,
        true,
        "factorization"
    },
    {
        "RING_00924",
        "(x0+(-13))*(x1+(12))-(12)*x0-(-13)*x1-(-156)",
        "x0*x1",
        3,
        true,
        "cancellation"
    },
    {
        "RING_00925",
        "((x0+0)*(x1+1))+((x2*0)+(-6)-(-6))",
        "x0*x1+x0",
        3,
        true,
        "neutral-elements"
    },
    {
        "RING_00926",
        "x0*(x1+(1))-(1)*x0",
        "x0*x1",
        3,
        true,
        "distribute-cancel"
    },
    {
        "RING_00927",
        "((x0+(8))+x1)*((x0+(8))-x1)",
        "(x0+(8))^2-x1^2",
        3,
        true,
        "difference-of-squares"
    },
    {
        "RING_00928",
        "(x0+(-14))^2-(x0^2+(-28)*x0+(196))",
        "0",
        3,
        true,
        "algebraic-zero"
    },
    {
        "RING_00929",
        "(x0+(-7))^2",
        "x0^2+(-14)*x0+(50)",
        3,
        false,
        "false-binomial"
    },
    {
        "RING_00930",
        "(x0+(0))*(x0-(0))",
        "x0^2-(0)",
        3,
        true,
        "conjugates"
    },
    {
        "RING_00931",
        "(x0+x1+(x2+(-6)))^2",
        "x0^2+x1^2+(x2+(-6))^2+2*x0*x1+2*x0*(x2+(-6))+2*x1*(x2+(-6))",
        3,
        true,
        "multivariate-square"
    },
    {
        "RING_00932",
        "((x0+(14))^2)*(x1+(7))",
        "(x0^2+(28)*x0+(196))*(x1+(7))",
        3,
        true,
        "product-squared"
    },
    {
        "RING_00933",
        "(-8)*x0+(-13)*x0+(-7)*x0+(-1)*x0",
        "(-29)*x0",
        3,
        true,
        "coefficient-aggregation"
    },
    {
        "RING_00934",
        "(-1)*(x0+x1+x2)^2",
        "(-1)*(x0^2+x1^2+x2^2+2*x0*x1+2*x0*x2+2*x1*x2)",
        3,
        true,
        "quadratic-form"
    },
    {
        "RING_00935",
        "(x0+(6))*(x1+(9))",
        "x0*x1+(9)*x0+(6)*x1+(54)",
        3,
        true,
        "distributivity"
    },
    {
        "RING_00936",
        "(x0+(13))^2",
        "x0^2+(26)*x0+(169)",
        3,
        true,
        "binomial-square"
    },
    {
        "RING_00937",
        "(x0+(-9))^3",
        "x0^3+(-27)*x0^2+(243)*x0+(-729)",
        3,
        true,
        "binomial-cube"
    },
    {
        "RING_00938",
        "(x0+(-2))*(x1+(11))",
        "(x1+(11))*(x0+(-2))",
        3,
        true,
        "commutativity"
    },
    {
        "RING_00939",
        "(x0+x1)+(x2+(-10))",
        "x0+(x1+(x2+(-10)))",
        3,
        true,
        "associativity"
    },
    {
        "RING_00940",
        "x0*x2+x1*x2+(12)*x2",
        "(x0+x1+(12))*x2",
        3,
        true,
        "factorization"
    },
    {
        "RING_00941",
        "(x0+(-10))*(x1+(13))-(13)*x0-(-10)*x1-(-130)",
        "x0*x1",
        3,
        true,
        "cancellation"
    },
    {
        "RING_00942",
        "((x0+0)*(x1+1))+((x2*0)+(-3)-(-3))",
        "x0*x1+x0",
        3,
        true,
        "neutral-elements"
    },
    {
        "RING_00943",
        "x0*(x1+(4))-(4)*x0",
        "x0*x1",
        3,
        true,
        "distribute-cancel"
    },
    {
        "RING_00944",
        "((x0+(11))+x1)*((x0+(11))-x1)",
        "(x0+(11))^2-x1^2",
        3,
        true,
        "difference-of-squares"
    },
    {
        "RING_00945",
        "(x0+(-11))^2-(x0^2+(-22)*x0+(121))",
        "0",
        3,
        true,
        "algebraic-zero"
    },
    {
        "RING_00946",
        "(x0+(-4))^2",
        "x0^2+(-8)*x0+(17)",
        3,
        false,
        "false-binomial"
    },
    {
        "RING_00947",
        "(x0+(3))*(x0-(3))",
        "x0^2-(9)",
        3,
        true,
        "conjugates"
    },
    {
        "RING_00948",
        "(x0+x1+(x2+(-1)))^2",
        "x0^2+x1^2+(x2+(-1))^2+2*x0*x1+2*x0*(x2+(-1))+2*x1*(x2+(-1))",
        3,
        true,
        "multivariate-square"
    },
    {
        "RING_00949",
        "((x0+(-12))^2)*(x1+(8))",
        "(x0^2+(-24)*x0+(144))*(x1+(8))",
        3,
        true,
        "product-squared"
    },
    {
        "RING_00950",
        "(-5)*x0+(-12)*x0+(-2)*x0+(-12)*x0",
        "(-31)*x0",
        3,
        true,
        "coefficient-aggregation"
    },
    {
        "RING_00951",
        "(2)*(x0+x1+x2)^2",
        "(2)*(x0^2+x1^2+x2^2+2*x0*x1+2*x0*x2+2*x1*x2)",
        3,
        true,
        "quadratic-form"
    },
    {
        "RING_00952",
        "(x0+(9))*(x1+(10))",
        "x0*x1+(10)*x0+(9)*x1+(90)",
        3,
        true,
        "distributivity"
    },
    {
        "RING_00953",
        "(x0+(-13))^2",
        "x0^2+(-26)*x0+(169)",
        3,
        true,
        "binomial-square"
    },
    {
        "RING_00954",
        "(x0+(-6))^3",
        "x0^3+(-18)*x0^2+(108)*x0+(-216)",
        3,
        true,
        "binomial-cube"
    },
    {
        "RING_00955",
        "(x0+(1))*(x1+(12))",
        "(x1+(12))*(x0+(1))",
        3,
        true,
        "commutativity"
    },
    {
        "RING_00956",
        "(x0+x1)+(x2+(-5))",
        "x0+(x1+(x2+(-5)))",
        3,
        true,
        "associativity"
    },
    {
        "RING_00957",
        "x0*x2+x1*x2+(-14)*x2",
        "(x0+x1+(-14))*x2",
        3,
        true,
        "factorization"
    },
    {
        "RING_00958",
        "(x0+(-7))*(x1+(14))-(14)*x0-(-7)*x1-(-98)",
        "x0*x1",
        3,
        true,
        "cancellation"
    },
    {
        "RING_00959",
        "((x0+0)*(x1+1))+((x2*0)+(0)-(0))",
        "x0*x1+x0",
        3,
        true,
        "neutral-elements"
    },
    {
        "RING_00960",
        "x0*(x1+(7))-(7)*x0",
        "x0*x1",
        3,
        true,
        "distribute-cancel"
    },
    {
        "RING_00961",
        "((x0+(14))+x1)*((x0+(14))-x1)",
        "(x0+(14))^2-x1^2",
        3,
        true,
        "difference-of-squares"
    },
    {
        "RING_00962",
        "(x0+(-8))^2-(x0^2+(-16)*x0+(64))",
        "0",
        3,
        true,
        "algebraic-zero"
    },
    {
        "RING_00963",
        "(x0+(-1))^2",
        "x0^2+(-2)*x0+(2)",
        3,
        false,
        "false-binomial"
    },
    {
        "RING_00964",
        "(x0+(6))*(x0-(6))",
        "x0^2-(36)",
        3,
        true,
        "conjugates"
    },
    {
        "RING_00965",
        "(x0+x1+(x2+(4)))^2",
        "x0^2+x1^2+(x2+(4))^2+2*x0*x1+2*x0*(x2+(4))+2*x1*(x2+(4))",
        3,
        true,
        "multivariate-square"
    },
    {
        "RING_00966",
        "((x0+(-9))^2)*(x1+(9))",
        "(x0^2+(-18)*x0+(81))*(x1+(9))",
        3,
        true,
        "product-squared"
    },
    {
        "RING_00967",
        "(-2)*x0+(-11)*x0+(3)*x0+(2)*x0",
        "(-8)*x0",
        3,
        true,
        "coefficient-aggregation"
    },
    {
        "RING_00968",
        "(5)*(x0+x1+x2)^2",
        "(5)*(x0^2+x1^2+x2^2+2*x0*x1+2*x0*x2+2*x1*x2)",
        3,
        true,
        "quadratic-form"
    },
    {
        "RING_00969",
        "(x0+(12))*(x1+(11))",
        "x0*x1+(11)*x0+(12)*x1+(132)",
        3,
        true,
        "distributivity"
    },
    {
        "RING_00970",
        "(x0+(-10))^2",
        "x0^2+(-20)*x0+(100)",
        3,
        true,
        "binomial-square"
    },
    {
        "RING_00971",
        "(x0+(-3))^3",
        "x0^3+(-9)*x0^2+(27)*x0+(-27)",
        3,
        true,
        "binomial-cube"
    },
    {
        "RING_00972",
        "(x0+(4))*(x1+(13))",
        "(x1+(13))*(x0+(4))",
        3,
        true,
        "commutativity"
    },
    {
        "RING_00973",
        "(x0+x1)+(x2+(0))",
        "x0+(x1+(x2+(0)))",
        3,
        true,
        "associativity"
    },
    {
        "RING_00974",
        "x0*x2+x1*x2+(-11)*x2",
        "(x0+x1+(-11))*x2",
        3,
        true,
        "factorization"
    },
    {
        "RING_00975",
        "(x0+(-4))*(x1+(15))-(15)*x0-(-4)*x1-(-60)",
        "x0*x1",
        3,
        true,
        "cancellation"
    },
    {
        "RING_00976",
        "((x0+0)*(x1+1))+((x2*0)+(3)-(3))",
        "x0*x1+x0",
        3,
        true,
        "neutral-elements"
    },
    {
        "RING_00977",
        "x0*(x1+(10))-(10)*x0",
        "x0*x1",
        3,
        true,
        "distribute-cancel"
    },
    {
        "RING_00978",
        "((x0+(-12))+x1)*((x0+(-12))-x1)",
        "(x0+(-12))^2-x1^2",
        3,
        true,
        "difference-of-squares"
    },
    {
        "RING_00979",
        "(x0+(-5))^2-(x0^2+(-10)*x0+(25))",
        "0",
        3,
        true,
        "algebraic-zero"
    },
    {
        "RING_00980",
        "(x0+(2))^2",
        "x0^2+(4)*x0+(5)",
        3,
        false,
        "false-binomial"
    },
    {
        "RING_00981",
        "(x0+(9))*(x0-(9))",
        "x0^2-(81)",
        3,
        true,
        "conjugates"
    },
    {
        "RING_00982",
        "(x0+x1+(x2+(9)))^2",
        "x0^2+x1^2+(x2+(9))^2+2*x0*x1+2*x0*(x2+(9))+2*x1*(x2+(9))",
        3,
        true,
        "multivariate-square"
    },
    {
        "RING_00983",
        "((x0+(-6))^2)*(x1+(10))",
        "(x0^2+(-12)*x0+(36))*(x1+(10))",
        3,
        true,
        "product-squared"
    },
    {
        "RING_00984",
        "(1)*x0+(-10)*x0+(8)*x0+(-9)*x0",
        "(-10)*x0",
        3,
        true,
        "coefficient-aggregation"
    },
    {
        "RING_00985",
        "(8)*(x0+x1+x2)^2",
        "(8)*(x0^2+x1^2+x2^2+2*x0*x1+2*x0*x2+2*x1*x2)",
        3,
        true,
        "quadratic-form"
    },
    {
        "RING_00986",
        "(x0+(-14))*(x1+(12))",
        "x0*x1+(12)*x0+(-14)*x1+(-168)",
        3,
        true,
        "distributivity"
    },
    {
        "RING_00987",
        "(x0+(-7))^2",
        "x0^2+(-14)*x0+(49)",
        3,
        true,
        "binomial-square"
    },
    {
        "RING_00988",
        "(x0+(0))^3",
        "x0^3+(0)*x0^2+(0)*x0+(0)",
        3,
        true,
        "binomial-cube"
    },
    {
        "RING_00989",
        "(x0+(7))*(x1+(14))",
        "(x1+(14))*(x0+(7))",
        3,
        true,
        "commutativity"
    },
    {
        "RING_00990",
        "(x0+x1)+(x2+(5))",
        "x0+(x1+(x2+(5)))",
        3,
        true,
        "associativity"
    },
    {
        "RING_00991",
        "x0*x2+x1*x2+(-8)*x2",
        "(x0+x1+(-8))*x2",
        3,
        true,
        "factorization"
    },
    {
        "RING_00992",
        "(x0+(-1))*(x1+(-15))-(-15)*x0-(-1)*x1-(15)",
        "x0*x1",
        3,
        true,
        "cancellation"
    },
    {
        "RING_00993",
        "((x0+0)*(x1+1))+((x2*0)+(6)-(6))",
        "x0*x1+x0",
        3,
        true,
        "neutral-elements"
    },
    {
        "RING_00994",
        "x0*(x1+(13))-(13)*x0",
        "x0*x1",
        3,
        true,
        "distribute-cancel"
    },
    {
        "RING_00995",
        "((x0+(-9))+x1)*((x0+(-9))-x1)",
        "(x0+(-9))^2-x1^2",
        3,
        true,
        "difference-of-squares"
    },
    {
        "RING_00996",
        "(x0+(-2))^2-(x0^2+(-4)*x0+(4))",
        "0",
        3,
        true,
        "algebraic-zero"
    },
    {
        "RING_00997",
        "(x0+(5))^2",
        "x0^2+(10)*x0+(26)",
        3,
        false,
        "false-binomial"
    },
    {
        "RING_00998",
        "(x0+(12))*(x0-(12))",
        "x0^2-(144)",
        3,
        true,
        "conjugates"
    },
    {
        "RING_00999",
        "(x0+x1+(x2+(-13)))^2",
        "x0^2+x1^2+(x2+(-13))^2+2*x0*x1+2*x0*(x2+(-13))+2*x1*(x2+(-13))",
        3,
        true,
        "multivariate-square"
    },
    {
        "RING_01000",
        "((x0+(-3))^2)*(x1+(11))",
        "(x0^2+(-6)*x0+(9))*(x1+(11))",
        3,
        true,
        "product-squared"
    },
    {
        "RING_01001",
        "(4)*x0+(-9)*x0+(13)*x0+(5)*x0",
        "(13)*x0",
        3,
        true,
        "coefficient-aggregation"
    },
    {
        "RING_01002",
        "(11)*(x0+x1+x2)^2",
        "(11)*(x0^2+x1^2+x2^2+2*x0*x1+2*x0*x2+2*x1*x2)",
        3,
        true,
        "quadratic-form"
    },
    {
        "RING_01003",
        "(x0+(-11))*(x1+(13))",
        "x0*x1+(13)*x0+(-11)*x1+(-143)",
        3,
        true,
        "distributivity"
    },
    {
        "RING_01004",
        "(x0+(-4))^2",
        "x0^2+(-8)*x0+(16)",
        3,
        true,
        "binomial-square"
    },
    {
        "RING_01005",
        "(x0+(3))^3",
        "x0^3+(9)*x0^2+(27)*x0+(27)",
        3,
        true,
        "binomial-cube"
    },
    {
        "RING_01006",
        "(x0+(10))*(x1+(15))",
        "(x1+(15))*(x0+(10))",
        3,
        true,
        "commutativity"
    },
    {
        "RING_01007",
        "(x0+x1)+(x2+(10))",
        "x0+(x1+(x2+(10)))",
        3,
        true,
        "associativity"
    },
    {
        "RING_01008",
        "x0*x2+x1*x2+(-5)*x2",
        "(x0+x1+(-5))*x2",
        3,
        true,
        "factorization"
    },
    {
        "RING_01009",
        "(x0+(2))*(x1+(-14))-(-14)*x0-(2)*x1-(-28)",
        "x0*x1",
        3,
        true,
        "cancellation"
    },
    {
        "RING_01010",
        "((x0+0)*(x1+1))+((x2*0)+(9)-(9))",
        "x0*x1+x0",
        3,
        true,
        "neutral-elements"
    },
    {
        "RING_01011",
        "x0*(x1+(-13))-(-13)*x0",
        "x0*x1",
        3,
        true,
        "distribute-cancel"
    },
    {
        "RING_01012",
        "((x0+(-6))+x1)*((x0+(-6))-x1)",
        "(x0+(-6))^2-x1^2",
        3,
        true,
        "difference-of-squares"
    },
    {
        "RING_01013",
        "(x0+(1))^2-(x0^2+(2)*x0+(1))",
        "0",
        3,
        true,
        "algebraic-zero"
    },
    {
        "RING_01014",
        "(x0+(8))^2",
        "x0^2+(16)*x0+(65)",
        3,
        false,
        "false-binomial"
    },
    {
        "RING_01015",
        "(x0+(-14))*(x0-(-14))",
        "x0^2-(196)",
        3,
        true,
        "conjugates"
    },
    {
        "RING_01016",
        "(x0+x1+(x2+(-8)))^2",
        "x0^2+x1^2+(x2+(-8))^2+2*x0*x1+2*x0*(x2+(-8))+2*x1*(x2+(-8))",
        3,
        true,
        "multivariate-square"
    },
    {
        "RING_01017",
        "((x0+(0))^2)*(x1+(12))",
        "(x0^2+(0)*x0+(0))*(x1+(12))",
        3,
        true,
        "product-squared"
    },
    {
        "RING_01018",
        "(7)*x0+(-8)*x0+(-9)*x0+(-6)*x0",
        "(-16)*x0",
        3,
        true,
        "coefficient-aggregation"
    },
    {
        "RING_01019",
        "(14)*(x0+x1+x2)^2",
        "(14)*(x0^2+x1^2+x2^2+2*x0*x1+2*x0*x2+2*x1*x2)",
        3,
        true,
        "quadratic-form"
    },
    {
        "RING_01020",
        "(x0+(-8))*(x1+(14))",
        "x0*x1+(14)*x0+(-8)*x1+(-112)",
        3,
        true,
        "distributivity"
    },
    {
        "RING_01021",
        "(x0+(-1))^2",
        "x0^2+(-2)*x0+(1)",
        3,
        true,
        "binomial-square"
    },
    {
        "RING_01022",
        "(x0+(6))^3",
        "x0^3+(18)*x0^2+(108)*x0+(216)",
        3,
        true,
        "binomial-cube"
    },
    {
        "RING_01023",
        "(x0+(13))*(x1+(-15))",
        "(x1+(-15))*(x0+(13))",
        3,
        true,
        "commutativity"
    },
    {
        "RING_01024",
        "(x0+x1)+(x2+(-12))",
        "x0+(x1+(x2+(-12)))",
        3,
        true,
        "associativity"
    },
    {
        "RING_01025",
        "x0*x2+x1*x2+(-2)*x2",
        "(x0+x1+(-2))*x2",
        3,
        true,
        "factorization"
    },
    {
        "RING_01026",
        "(x0+(5))*(x1+(-13))-(-13)*x0-(5)*x1-(-65)",
        "x0*x1",
        3,
        true,
        "cancellation"
    },
    {
        "RING_01027",
        "((x0+0)*(x1+1))+((x2*0)+(12)-(12))",
        "x0*x1+x0",
        3,
        true,
        "neutral-elements"
    },
    {
        "RING_01028",
        "x0*(x1+(-10))-(-10)*x0",
        "x0*x1",
        3,
        true,
        "distribute-cancel"
    },
    {
        "RING_01029",
        "((x0+(-3))+x1)*((x0+(-3))-x1)",
        "(x0+(-3))^2-x1^2",
        3,
        true,
        "difference-of-squares"
    },
    {
        "RING_01030",
        "(x0+(4))^2-(x0^2+(8)*x0+(16))",
        "0",
        3,
        true,
        "algebraic-zero"
    },
    {
        "RING_01031",
        "(x0+(11))^2",
        "x0^2+(22)*x0+(122)",
        3,
        false,
        "false-binomial"
    },
    {
        "RING_01032",
        "(x0+(-11))*(x0-(-11))",
        "x0^2-(121)",
        3,
        true,
        "conjugates"
    },
    {
        "RING_01033",
        "(x0+x1+(x2+(-3)))^2",
        "x0^2+x1^2+(x2+(-3))^2+2*x0*x1+2*x0*(x2+(-3))+2*x1*(x2+(-3))",
        3,
        true,
        "multivariate-square"
    },
    {
        "RING_01034",
        "((x0+(3))^2)*(x1+(13))",
        "(x0^2+(6)*x0+(9))*(x1+(13))",
        3,
        true,
        "product-squared"
    },
    {
        "RING_01035",
        "(10)*x0+(-7)*x0+(-4)*x0+(8)*x0",
        "(7)*x0",
        3,
        true,
        "coefficient-aggregation"
    },
    {
        "RING_01036",
        "(-12)*(x0+x1+x2)^2",
        "(-12)*(x0^2+x1^2+x2^2+2*x0*x1+2*x0*x2+2*x1*x2)",
        3,
        true,
        "quadratic-form"
    },
    {
        "RING_01037",
        "(x0+(-5))*(x1+(15))",
        "x0*x1+(15)*x0+(-5)*x1+(-75)",
        3,
        true,
        "distributivity"
    },
    {
        "RING_01038",
        "(x0+(2))^2",
        "x0^2+(4)*x0+(4)",
        3,
        true,
        "binomial-square"
    },
    {
        "RING_01039",
        "(x0+(9))^3",
        "x0^3+(27)*x0^2+(243)*x0+(729)",
        3,
        true,
        "binomial-cube"
    },
    {
        "RING_01040",
        "(x0+(-13))*(x1+(-14))",
        "(x1+(-14))*(x0+(-13))",
        3,
        true,
        "commutativity"
    },
    {
        "RING_01041",
        "(x0+x1)+(x2+(-7))",
        "x0+(x1+(x2+(-7)))",
        3,
        true,
        "associativity"
    },
    {
        "RING_01042",
        "x0*x2+x1*x2+(1)*x2",
        "(x0+x1+(1))*x2",
        3,
        true,
        "factorization"
    },
    {
        "RING_01043",
        "(x0+(8))*(x1+(-12))-(-12)*x0-(8)*x1-(-96)",
        "x0*x1",
        3,
        true,
        "cancellation"
    },
    {
        "RING_01044",
        "((x0+0)*(x1+1))+((x2*0)+(-14)-(-14))",
        "x0*x1+x0",
        3,
        true,
        "neutral-elements"
    },
    {
        "RING_01045",
        "x0*(x1+(-7))-(-7)*x0",
        "x0*x1",
        3,
        true,
        "distribute-cancel"
    },
    {
        "RING_01046",
        "((x0+(0))+x1)*((x0+(0))-x1)",
        "(x0+(0))^2-x1^2",
        3,
        true,
        "difference-of-squares"
    },
    {
        "RING_01047",
        "(x0+(7))^2-(x0^2+(14)*x0+(49))",
        "0",
        3,
        true,
        "algebraic-zero"
    },
    {
        "RING_01048",
        "(x0+(14))^2",
        "x0^2+(28)*x0+(197)",
        3,
        false,
        "false-binomial"
    },
    {
        "RING_01049",
        "(x0+(-8))*(x0-(-8))",
        "x0^2-(64)",
        3,
        true,
        "conjugates"
    },
    {
        "RING_01050",
        "(x0+x1+(x2+(2)))^2",
        "x0^2+x1^2+(x2+(2))^2+2*x0*x1+2*x0*(x2+(2))+2*x1*(x2+(2))",
        3,
        true,
        "multivariate-square"
    },
    {
        "RING_01051",
        "((x0+(6))^2)*(x1+(14))",
        "(x0^2+(12)*x0+(36))*(x1+(14))",
        3,
        true,
        "product-squared"
    },
    {
        "RING_01052",
        "(13)*x0+(-6)*x0+(1)*x0+(-3)*x0",
        "(5)*x0",
        3,
        true,
        "coefficient-aggregation"
    },
    {
        "RING_01053",
        "(-9)*(x0+x1+x2)^2",
        "(-9)*(x0^2+x1^2+x2^2+2*x0*x1+2*x0*x2+2*x1*x2)",
        3,
        true,
        "quadratic-form"
    },
    {
        "RING_01054",
        "(x0+(-2))*(x1+(-15))",
        "x0*x1+(-15)*x0+(-2)*x1+(30)",
        3,
        true,
        "distributivity"
    },
    {
        "RING_01055",
        "(x0+(5))^2",
        "x0^2+(10)*x0+(25)",
        3,
        true,
        "binomial-square"
    },
    {
        "RING_01056",
        "(x0+(12))^3",
        "x0^3+(36)*x0^2+(432)*x0+(1728)",
        3,
        true,
        "binomial-cube"
    },
    {
        "RING_01057",
        "(x0+(-10))*(x1+(-13))",
        "(x1+(-13))*(x0+(-10))",
        3,
        true,
        "commutativity"
    },
    {
        "RING_01058",
        "(x0+x1)+(x2+(-2))",
        "x0+(x1+(x2+(-2)))",
        3,
        true,
        "associativity"
    },
    {
        "RING_01059",
        "x0*x2+x1*x2+(4)*x2",
        "(x0+x1+(4))*x2",
        3,
        true,
        "factorization"
    },
    {
        "RING_01060",
        "(x0+(11))*(x1+(-11))-(-11)*x0-(11)*x1-(-121)",
        "x0*x1",
        3,
        true,
        "cancellation"
    },
    {
        "RING_01061",
        "((x0+0)*(x1+1))+((x2*0)+(-11)-(-11))",
        "x0*x1+x0",
        3,
        true,
        "neutral-elements"
    },
    {
        "RING_01062",
        "x0*(x1+(-4))-(-4)*x0",
        "x0*x1",
        3,
        true,
        "distribute-cancel"
    },
    {
        "RING_01063",
        "((x0+(3))+x1)*((x0+(3))-x1)",
        "(x0+(3))^2-x1^2",
        3,
        true,
        "difference-of-squares"
    },
    {
        "RING_01064",
        "(x0+(10))^2-(x0^2+(20)*x0+(100))",
        "0",
        3,
        true,
        "algebraic-zero"
    },
    {
        "RING_01065",
        "(x0+(-12))^2",
        "x0^2+(-24)*x0+(145)",
        3,
        false,
        "false-binomial"
    },
    {
        "RING_01066",
        "(x0+(-5))*(x0-(-5))",
        "x0^2-(25)",
        3,
        true,
        "conjugates"
    },
    {
        "RING_01067",
        "(x0+x1+(x2+(7)))^2",
        "x0^2+x1^2+(x2+(7))^2+2*x0*x1+2*x0*(x2+(7))+2*x1*(x2+(7))",
        3,
        true,
        "multivariate-square"
    },
    {
        "RING_01068",
        "((x0+(9))^2)*(x1+(15))",
        "(x0^2+(18)*x0+(81))*(x1+(15))",
        3,
        true,
        "product-squared"
    },
    {
        "RING_01069",
        "(-13)*x0+(-5)*x0+(6)*x0+(11)*x0",
        "(-1)*x0",
        3,
        true,
        "coefficient-aggregation"
    },
    {
        "RING_01070",
        "(-6)*(x0+x1+x2)^2",
        "(-6)*(x0^2+x1^2+x2^2+2*x0*x1+2*x0*x2+2*x1*x2)",
        3,
        true,
        "quadratic-form"
    },
    {
        "RING_01071",
        "(x0+(1))*(x1+(-14))",
        "x0*x1+(-14)*x0+(1)*x1+(-14)",
        3,
        true,
        "distributivity"
    },
    {
        "RING_01072",
        "(x0+(8))^2",
        "x0^2+(16)*x0+(64)",
        3,
        true,
        "binomial-square"
    },
    {
        "RING_01073",
        "(x0+(-14))^3",
        "x0^3+(-42)*x0^2+(588)*x0+(-2744)",
        3,
        true,
        "binomial-cube"
    },
    {
        "RING_01074",
        "(x0+(-7))*(x1+(-12))",
        "(x1+(-12))*(x0+(-7))",
        3,
        true,
        "commutativity"
    },
    {
        "RING_01075",
        "(x0+x1)+(x2+(3))",
        "x0+(x1+(x2+(3)))",
        3,
        true,
        "associativity"
    },
    {
        "RING_01076",
        "x0*x2+x1*x2+(7)*x2",
        "(x0+x1+(7))*x2",
        3,
        true,
        "factorization"
    },
    {
        "RING_01077",
        "(x0+(14))*(x1+(-10))-(-10)*x0-(14)*x1-(-140)",
        "x0*x1",
        3,
        true,
        "cancellation"
    },
    {
        "RING_01078",
        "((x0+0)*(x1+1))+((x2*0)+(-8)-(-8))",
        "x0*x1+x0",
        3,
        true,
        "neutral-elements"
    },
    {
        "RING_01079",
        "x0*(x1+(-1))-(-1)*x0",
        "x0*x1",
        3,
        true,
        "distribute-cancel"
    },
    {
        "RING_01080",
        "((x0+(6))+x1)*((x0+(6))-x1)",
        "(x0+(6))^2-x1^2",
        3,
        true,
        "difference-of-squares"
    },
    {
        "RING_01081",
        "(x0+(13))^2-(x0^2+(26)*x0+(169))",
        "0",
        3,
        true,
        "algebraic-zero"
    },
    {
        "RING_01082",
        "(x0+(-9))^2",
        "x0^2+(-18)*x0+(82)",
        3,
        false,
        "false-binomial"
    },
    {
        "RING_01083",
        "(x0+(-2))*(x0-(-2))",
        "x0^2-(4)",
        3,
        true,
        "conjugates"
    },
    {
        "RING_01084",
        "(x0+x1+(x2+(12)))^2",
        "x0^2+x1^2+(x2+(12))^2+2*x0*x1+2*x0*(x2+(12))+2*x1*(x2+(12))",
        3,
        true,
        "multivariate-square"
    },
    {
        "RING_01085",
        "((x0+(12))^2)*(x1+(-15))",
        "(x0^2+(24)*x0+(144))*(x1+(-15))",
        3,
        true,
        "product-squared"
    },
    {
        "RING_01086",
        "(-10)*x0+(-4)*x0+(11)*x0+(0)*x0",
        "(-3)*x0",
        3,
        true,
        "coefficient-aggregation"
    },
    {
        "RING_01087",
        "(-3)*(x0+x1+x2)^2",
        "(-3)*(x0^2+x1^2+x2^2+2*x0*x1+2*x0*x2+2*x1*x2)",
        3,
        true,
        "quadratic-form"
    },
    {
        "RING_01088",
        "(x0+(4))*(x1+(-13))",
        "x0*x1+(-13)*x0+(4)*x1+(-52)",
        3,
        true,
        "distributivity"
    },
    {
        "RING_01089",
        "(x0+(11))^2",
        "x0^2+(22)*x0+(121)",
        3,
        true,
        "binomial-square"
    },
    {
        "RING_01090",
        "(x0+(-11))^3",
        "x0^3+(-33)*x0^2+(363)*x0+(-1331)",
        3,
        true,
        "binomial-cube"
    },
    {
        "RING_01091",
        "(x0+(-4))*(x1+(-11))",
        "(x1+(-11))*(x0+(-4))",
        3,
        true,
        "commutativity"
    },
    {
        "RING_01092",
        "(x0+x1)+(x2+(8))",
        "x0+(x1+(x2+(8)))",
        3,
        true,
        "associativity"
    },
    {
        "RING_01093",
        "x0*x2+x1*x2+(10)*x2",
        "(x0+x1+(10))*x2",
        3,
        true,
        "factorization"
    },
    {
        "RING_01094",
        "(x0+(-12))*(x1+(-9))-(-9)*x0-(-12)*x1-(108)",
        "x0*x1",
        3,
        true,
        "cancellation"
    },
    {
        "RING_01095",
        "((x0+0)*(x1+1))+((x2*0)+(-5)-(-5))",
        "x0*x1+x0",
        3,
        true,
        "neutral-elements"
    },
    {
        "RING_01096",
        "x0*(x1+(2))-(2)*x0",
        "x0*x1",
        3,
        true,
        "distribute-cancel"
    },
    {
        "RING_01097",
        "((x0+(9))+x1)*((x0+(9))-x1)",
        "(x0+(9))^2-x1^2",
        3,
        true,
        "difference-of-squares"
    },
    {
        "RING_01098",
        "(x0+(-13))^2-(x0^2+(-26)*x0+(169))",
        "0",
        3,
        true,
        "algebraic-zero"
    },
    {
        "RING_01099",
        "(x0+(-6))^2",
        "x0^2+(-12)*x0+(37)",
        3,
        false,
        "false-binomial"
    },
    {
        "RING_01100",
        "(x0+(1))*(x0-(1))",
        "x0^2-(1)",
        3,
        true,
        "conjugates"
    },
    {
        "RING_01101",
        "(x0+x1+(x2+(-10)))^2",
        "x0^2+x1^2+(x2+(-10))^2+2*x0*x1+2*x0*(x2+(-10))+2*x1*(x2+(-10))",
        3,
        true,
        "multivariate-square"
    },
    {
        "RING_01102",
        "((x0+(-14))^2)*(x1+(-14))",
        "(x0^2+(-28)*x0+(196))*(x1+(-14))",
        3,
        true,
        "product-squared"
    },
    {
        "RING_01103",
        "(-7)*x0+(-3)*x0+(-11)*x0+(-11)*x0",
        "(-32)*x0",
        3,
        true,
        "coefficient-aggregation"
    },
    {
        "RING_01104",
        "(0)*(x0+x1+x2)^2",
        "(0)*(x0^2+x1^2+x2^2+2*x0*x1+2*x0*x2+2*x1*x2)",
        3,
        true,
        "quadratic-form"
    },
    {
        "RING_01105",
        "(x0+(7))*(x1+(-12))",
        "x0*x1+(-12)*x0+(7)*x1+(-84)",
        3,
        true,
        "distributivity"
    },
    {
        "RING_01106",
        "(x0+(14))^2",
        "x0^2+(28)*x0+(196)",
        3,
        true,
        "binomial-square"
    },
    {
        "RING_01107",
        "(x0+(-8))^3",
        "x0^3+(-24)*x0^2+(192)*x0+(-512)",
        3,
        true,
        "binomial-cube"
    },
    {
        "RING_01108",
        "(x0+(-1))*(x1+(-10))",
        "(x1+(-10))*(x0+(-1))",
        3,
        true,
        "commutativity"
    },
    {
        "RING_01109",
        "(x0+x1)+(x2+(13))",
        "x0+(x1+(x2+(13)))",
        3,
        true,
        "associativity"
    },
    {
        "RING_01110",
        "x0*x2+x1*x2+(13)*x2",
        "(x0+x1+(13))*x2",
        3,
        true,
        "factorization"
    },
    {
        "RING_01111",
        "(x0+(-9))*(x1+(-8))-(-8)*x0-(-9)*x1-(72)",
        "x0*x1",
        3,
        true,
        "cancellation"
    },
    {
        "RING_01112",
        "((x0+0)*(x1+1))+((x2*0)+(-2)-(-2))",
        "x0*x1+x0",
        3,
        true,
        "neutral-elements"
    },
    {
        "RING_01113",
        "x0*(x1+(5))-(5)*x0",
        "x0*x1",
        3,
        true,
        "distribute-cancel"
    },
    {
        "RING_01114",
        "((x0+(12))+x1)*((x0+(12))-x1)",
        "(x0+(12))^2-x1^2",
        3,
        true,
        "difference-of-squares"
    },
    {
        "RING_01115",
        "(x0+(-10))^2-(x0^2+(-20)*x0+(100))",
        "0",
        3,
        true,
        "algebraic-zero"
    },
    {
        "RING_01116",
        "(x0+(-3))^2",
        "x0^2+(-6)*x0+(10)",
        3,
        false,
        "false-binomial"
    },
    {
        "RING_01117",
        "(x0+(4))*(x0-(4))",
        "x0^2-(16)",
        3,
        true,
        "conjugates"
    },
    {
        "RING_01118",
        "(x0+x1+(x2+(-5)))^2",
        "x0^2+x1^2+(x2+(-5))^2+2*x0*x1+2*x0*(x2+(-5))+2*x1*(x2+(-5))",
        3,
        true,
        "multivariate-square"
    },
    {
        "RING_01119",
        "((x0+(-11))^2)*(x1+(-13))",
        "(x0^2+(-22)*x0+(121))*(x1+(-13))",
        3,
        true,
        "product-squared"
    },
    {
        "RING_01120",
        "(-4)*x0+(-2)*x0+(-6)*x0+(3)*x0",
        "(-9)*x0",
        3,
        true,
        "coefficient-aggregation"
    },
    {
        "RING_01121",
        "(3)*(x0+x1+x2)^2",
        "(3)*(x0^2+x1^2+x2^2+2*x0*x1+2*x0*x2+2*x1*x2)",
        3,
        true,
        "quadratic-form"
    },
    {
        "RING_01122",
        "(x0+(10))*(x1+(-11))",
        "x0*x1+(-11)*x0+(10)*x1+(-110)",
        3,
        true,
        "distributivity"
    },
    {
        "RING_01123",
        "(x0+(-12))^2",
        "x0^2+(-24)*x0+(144)",
        3,
        true,
        "binomial-square"
    },
    {
        "RING_01124",
        "(x0+(-5))^3",
        "x0^3+(-15)*x0^2+(75)*x0+(-125)",
        3,
        true,
        "binomial-cube"
    },
    {
        "RING_01125",
        "(x0+(2))*(x1+(-9))",
        "(x1+(-9))*(x0+(2))",
        3,
        true,
        "commutativity"
    },
    {
        "RING_01126",
        "(x0+x1)+(x2+(-9))",
        "x0+(x1+(x2+(-9)))",
        3,
        true,
        "associativity"
    },
    {
        "RING_01127",
        "x0*x2+x1*x2+(-13)*x2",
        "(x0+x1+(-13))*x2",
        3,
        true,
        "factorization"
    },
    {
        "RING_01128",
        "(x0+(-6))*(x1+(-7))-(-7)*x0-(-6)*x1-(42)",
        "x0*x1",
        3,
        true,
        "cancellation"
    },
    {
        "RING_01129",
        "((x0+0)*(x1+1))+((x2*0)+(1)-(1))",
        "x0*x1+x0",
        3,
        true,
        "neutral-elements"
    },
    {
        "RING_01130",
        "x0*(x1+(8))-(8)*x0",
        "x0*x1",
        3,
        true,
        "distribute-cancel"
    },
    {
        "RING_01131",
        "((x0+(-14))+x1)*((x0+(-14))-x1)",
        "(x0+(-14))^2-x1^2",
        3,
        true,
        "difference-of-squares"
    },
    {
        "RING_01132",
        "(x0+(-7))^2-(x0^2+(-14)*x0+(49))",
        "0",
        3,
        true,
        "algebraic-zero"
    },
    {
        "RING_01133",
        "(x0+(0))^2",
        "x0^2+(0)*x0+(1)",
        3,
        false,
        "false-binomial"
    },
    {
        "RING_01134",
        "(x0+(7))*(x0-(7))",
        "x0^2-(49)",
        3,
        true,
        "conjugates"
    },
    {
        "RING_01135",
        "(x0+x1+(x2+(0)))^2",
        "x0^2+x1^2+(x2+(0))^2+2*x0*x1+2*x0*(x2+(0))+2*x1*(x2+(0))",
        3,
        true,
        "multivariate-square"
    },
    {
        "RING_01136",
        "((x0+(-8))^2)*(x1+(-12))",
        "(x0^2+(-16)*x0+(64))*(x1+(-12))",
        3,
        true,
        "product-squared"
    },
    {
        "RING_01137",
        "(-1)*x0+(-1)*x0+(-1)*x0+(-8)*x0",
        "(-11)*x0",
        3,
        true,
        "coefficient-aggregation"
    },
    {
        "RING_01138",
        "(6)*(x0+x1+x2)^2",
        "(6)*(x0^2+x1^2+x2^2+2*x0*x1+2*x0*x2+2*x1*x2)",
        3,
        true,
        "quadratic-form"
    },
    {
        "RING_01139",
        "(x0+(13))*(x1+(-10))",
        "x0*x1+(-10)*x0+(13)*x1+(-130)",
        3,
        true,
        "distributivity"
    },
    {
        "RING_01140",
        "(x0+(-9))^2",
        "x0^2+(-18)*x0+(81)",
        3,
        true,
        "binomial-square"
    },
    {
        "RING_01141",
        "(x0+(-2))^3",
        "x0^3+(-6)*x0^2+(12)*x0+(-8)",
        3,
        true,
        "binomial-cube"
    },
    {
        "RING_01142",
        "(x0+(5))*(x1+(-8))",
        "(x1+(-8))*(x0+(5))",
        3,
        true,
        "commutativity"
    },
    {
        "RING_01143",
        "(x0+x1)+(x2+(-4))",
        "x0+(x1+(x2+(-4)))",
        3,
        true,
        "associativity"
    },
    {
        "RING_01144",
        "x0*x2+x1*x2+(-10)*x2",
        "(x0+x1+(-10))*x2",
        3,
        true,
        "factorization"
    },
    {
        "RING_01145",
        "(x0+(-3))*(x1+(-6))-(-6)*x0-(-3)*x1-(18)",
        "x0*x1",
        3,
        true,
        "cancellation"
    },
    {
        "RING_01146",
        "((x0+0)*(x1+1))+((x2*0)+(4)-(4))",
        "x0*x1+x0",
        3,
        true,
        "neutral-elements"
    },
    {
        "RING_01147",
        "x0*(x1+(11))-(11)*x0",
        "x0*x1",
        3,
        true,
        "distribute-cancel"
    },
    {
        "RING_01148",
        "((x0+(-11))+x1)*((x0+(-11))-x1)",
        "(x0+(-11))^2-x1^2",
        3,
        true,
        "difference-of-squares"
    },
    {
        "RING_01149",
        "(x0+(-4))^2-(x0^2+(-8)*x0+(16))",
        "0",
        3,
        true,
        "algebraic-zero"
    },
    {
        "RING_01150",
        "(x0+(3))^2",
        "x0^2+(6)*x0+(10)",
        3,
        false,
        "false-binomial"
    },
    {
        "RING_01151",
        "(x0+(10))*(x0-(10))",
        "x0^2-(100)",
        3,
        true,
        "conjugates"
    },
    {
        "RING_01152",
        "(x0+x1+(x2+(5)))^2",
        "x0^2+x1^2+(x2+(5))^2+2*x0*x1+2*x0*(x2+(5))+2*x1*(x2+(5))",
        3,
        true,
        "multivariate-square"
    },
    {
        "RING_01153",
        "((x0+(-5))^2)*(x1+(-11))",
        "(x0^2+(-10)*x0+(25))*(x1+(-11))",
        3,
        true,
        "product-squared"
    },
    {
        "RING_01154",
        "(2)*x0+(0)*x0+(4)*x0+(6)*x0",
        "(12)*x0",
        3,
        true,
        "coefficient-aggregation"
    },
    {
        "RING_01155",
        "(9)*(x0+x1+x2)^2",
        "(9)*(x0^2+x1^2+x2^2+2*x0*x1+2*x0*x2+2*x1*x2)",
        3,
        true,
        "quadratic-form"
    },
    {
        "RING_01156",
        "(x0+(-13))*(x1+(-9))",
        "x0*x1+(-9)*x0+(-13)*x1+(117)",
        3,
        true,
        "distributivity"
    },
    {
        "RING_01157",
        "(x0+(-6))^2",
        "x0^2+(-12)*x0+(36)",
        3,
        true,
        "binomial-square"
    },
    {
        "RING_01158",
        "(x0+(1))^3",
        "x0^3+(3)*x0^2+(3)*x0+(1)",
        3,
        true,
        "binomial-cube"
    },
    {
        "RING_01159",
        "(x0+(8))*(x1+(-7))",
        "(x1+(-7))*(x0+(8))",
        3,
        true,
        "commutativity"
    },
    {
        "RING_01160",
        "(x0+x1)+(x2+(1))",
        "x0+(x1+(x2+(1)))",
        3,
        true,
        "associativity"
    },
    {
        "RING_01161",
        "x0*x2+x1*x2+(-7)*x2",
        "(x0+x1+(-7))*x2",
        3,
        true,
        "factorization"
    },
    {
        "RING_01162",
        "(x0+(0))*(x1+(-5))-(-5)*x0-(0)*x1-(0)",
        "x0*x1",
        3,
        true,
        "cancellation"
    },
    {
        "RING_01163",
        "((x0+0)*(x1+1))+((x2*0)+(7)-(7))",
        "x0*x1+x0",
        3,
        true,
        "neutral-elements"
    },
    {
        "RING_01164",
        "x0*(x1+(14))-(14)*x0",
        "x0*x1",
        3,
        true,
        "distribute-cancel"
    },
    {
        "RING_01165",
        "((x0+(-8))+x1)*((x0+(-8))-x1)",
        "(x0+(-8))^2-x1^2",
        3,
        true,
        "difference-of-squares"
    },
    {
        "RING_01166",
        "(x0+(-1))^2-(x0^2+(-2)*x0+(1))",
        "0",
        3,
        true,
        "algebraic-zero"
    },
    {
        "RING_01167",
        "(x0+(6))^2",
        "x0^2+(12)*x0+(37)",
        3,
        false,
        "false-binomial"
    },
    {
        "RING_01168",
        "(x0+(13))*(x0-(13))",
        "x0^2-(169)",
        3,
        true,
        "conjugates"
    },
    {
        "RING_01169",
        "(x0+x1+(x2+(10)))^2",
        "x0^2+x1^2+(x2+(10))^2+2*x0*x1+2*x0*(x2+(10))+2*x1*(x2+(10))",
        3,
        true,
        "multivariate-square"
    },
    {
        "RING_01170",
        "((x0+(-2))^2)*(x1+(-10))",
        "(x0^2+(-4)*x0+(4))*(x1+(-10))",
        3,
        true,
        "product-squared"
    },
    {
        "RING_01171",
        "(5)*x0+(1)*x0+(9)*x0+(-5)*x0",
        "(10)*x0",
        3,
        true,
        "coefficient-aggregation"
    },
    {
        "RING_01172",
        "(12)*(x0+x1+x2)^2",
        "(12)*(x0^2+x1^2+x2^2+2*x0*x1+2*x0*x2+2*x1*x2)",
        3,
        true,
        "quadratic-form"
    },
    {
        "RING_01173",
        "(x0+(-10))*(x1+(-8))",
        "x0*x1+(-8)*x0+(-10)*x1+(80)",
        3,
        true,
        "distributivity"
    },
    {
        "RING_01174",
        "(x0+(-3))^2",
        "x0^2+(-6)*x0+(9)",
        3,
        true,
        "binomial-square"
    },
    {
        "RING_01175",
        "(x0+(4))^3",
        "x0^3+(12)*x0^2+(48)*x0+(64)",
        3,
        true,
        "binomial-cube"
    },
    {
        "RING_01176",
        "(x0+(11))*(x1+(-6))",
        "(x1+(-6))*(x0+(11))",
        3,
        true,
        "commutativity"
    },
    {
        "RING_01177",
        "(x0+x1)+(x2+(6))",
        "x0+(x1+(x2+(6)))",
        3,
        true,
        "associativity"
    },
    {
        "RING_01178",
        "x0*x2+x1*x2+(-4)*x2",
        "(x0+x1+(-4))*x2",
        3,
        true,
        "factorization"
    },
    {
        "RING_01179",
        "(x0+(3))*(x1+(-4))-(-4)*x0-(3)*x1-(-12)",
        "x0*x1",
        3,
        true,
        "cancellation"
    },
    {
        "RING_01180",
        "((x0+0)*(x1+1))+((x2*0)+(10)-(10))",
        "x0*x1+x0",
        3,
        true,
        "neutral-elements"
    },
    {
        "RING_01181",
        "x0*(x1+(-12))-(-12)*x0",
        "x0*x1",
        3,
        true,
        "distribute-cancel"
    },
    {
        "RING_01182",
        "((x0+(-5))+x1)*((x0+(-5))-x1)",
        "(x0+(-5))^2-x1^2",
        3,
        true,
        "difference-of-squares"
    },
    {
        "RING_01183",
        "(x0+(2))^2-(x0^2+(4)*x0+(4))",
        "0",
        3,
        true,
        "algebraic-zero"
    },
    {
        "RING_01184",
        "(x0+(9))^2",
        "x0^2+(18)*x0+(82)",
        3,
        false,
        "false-binomial"
    },
    {
        "RING_01185",
        "(x0+(-13))*(x0-(-13))",
        "x0^2-(169)",
        3,
        true,
        "conjugates"
    },
    {
        "RING_01186",
        "(x0+x1+(x2+(-12)))^2",
        "x0^2+x1^2+(x2+(-12))^2+2*x0*x1+2*x0*(x2+(-12))+2*x1*(x2+(-12))",
        3,
        true,
        "multivariate-square"
    },
    {
        "RING_01187",
        "((x0+(1))^2)*(x1+(-9))",
        "(x0^2+(2)*x0+(1))*(x1+(-9))",
        3,
        true,
        "product-squared"
    },
    {
        "RING_01188",
        "(8)*x0+(2)*x0+(-13)*x0+(9)*x0",
        "(6)*x0",
        3,
        true,
        "coefficient-aggregation"
    },
    {
        "RING_01189",
        "(-14)*(x0+x1+x2)^2",
        "(-14)*(x0^2+x1^2+x2^2+2*x0*x1+2*x0*x2+2*x1*x2)",
        3,
        true,
        "quadratic-form"
    },
    {
        "RING_01190",
        "(x0+(-7))*(x1+(-7))",
        "x0*x1+(-7)*x0+(-7)*x1+(49)",
        3,
        true,
        "distributivity"
    },
    {
        "RING_01191",
        "(x0+(0))^2",
        "x0^2+(0)*x0+(0)",
        3,
        true,
        "binomial-square"
    },
    {
        "RING_01192",
        "(x0+(7))^3",
        "x0^3+(21)*x0^2+(147)*x0+(343)",
        3,
        true,
        "binomial-cube"
    },
    {
        "RING_01193",
        "(x0+(14))*(x1+(-5))",
        "(x1+(-5))*(x0+(14))",
        3,
        true,
        "commutativity"
    },
    {
        "RING_01194",
        "(x0+x1)+(x2+(11))",
        "x0+(x1+(x2+(11)))",
        3,
        true,
        "associativity"
    },
    {
        "RING_01195",
        "x0*x2+x1*x2+(-1)*x2",
        "(x0+x1+(-1))*x2",
        3,
        true,
        "factorization"
    },
    {
        "RING_01196",
        "(x0+(6))*(x1+(-3))-(-3)*x0-(6)*x1-(-18)",
        "x0*x1",
        3,
        true,
        "cancellation"
    },
    {
        "RING_01197",
        "((x0+0)*(x1+1))+((x2*0)+(13)-(13))",
        "x0*x1+x0",
        3,
        true,
        "neutral-elements"
    },
    {
        "RING_01198",
        "x0*(x1+(-9))-(-9)*x0",
        "x0*x1",
        3,
        true,
        "distribute-cancel"
    },
    {
        "RING_01199",
        "((x0+(-2))+x1)*((x0+(-2))-x1)",
        "(x0+(-2))^2-x1^2",
        3,
        true,
        "difference-of-squares"
    },
    {
        "RING_01200",
        "(x0+(5))^2-(x0^2+(10)*x0+(25))",
        "0",
        3,
        true,
        "algebraic-zero"
    },
    {
        "RING_01201",
        "(x0+(12))^2",
        "x0^2+(24)*x0+(145)",
        3,
        false,
        "false-binomial"
    },
    {
        "RING_01202",
        "(x0+(-10))*(x0-(-10))",
        "x0^2-(100)",
        3,
        true,
        "conjugates"
    },
    {
        "RING_01203",
        "(x0+x1+(x2+(-7)))^2",
        "x0^2+x1^2+(x2+(-7))^2+2*x0*x1+2*x0*(x2+(-7))+2*x1*(x2+(-7))",
        3,
        true,
        "multivariate-square"
    },
    {
        "RING_01204",
        "((x0+(4))^2)*(x1+(-8))",
        "(x0^2+(8)*x0+(16))*(x1+(-8))",
        3,
        true,
        "product-squared"
    },
    {
        "RING_01205",
        "(11)*x0+(3)*x0+(-8)*x0+(-2)*x0",
        "(4)*x0",
        3,
        true,
        "coefficient-aggregation"
    },
    {
        "RING_01206",
        "(-11)*(x0+x1+x2)^2",
        "(-11)*(x0^2+x1^2+x2^2+2*x0*x1+2*x0*x2+2*x1*x2)",
        3,
        true,
        "quadratic-form"
    },
    {
        "RING_01207",
        "(x0+(-4))*(x1+(-6))",
        "x0*x1+(-6)*x0+(-4)*x1+(24)",
        3,
        true,
        "distributivity"
    },
    {
        "RING_01208",
        "(x0+(3))^2",
        "x0^2+(6)*x0+(9)",
        3,
        true,
        "binomial-square"
    },
    {
        "RING_01209",
        "(x0+(10))^3",
        "x0^3+(30)*x0^2+(300)*x0+(1000)",
        3,
        true,
        "binomial-cube"
    },
    {
        "RING_01210",
        "(x0+(-12))*(x1+(-4))",
        "(x1+(-4))*(x0+(-12))",
        3,
        true,
        "commutativity"
    },
    {
        "RING_01211",
        "(x0+x1)+(x2+(-11))",
        "x0+(x1+(x2+(-11)))",
        3,
        true,
        "associativity"
    },
    {
        "RING_01212",
        "x0*x2+x1*x2+(2)*x2",
        "(x0+x1+(2))*x2",
        3,
        true,
        "factorization"
    },
    {
        "RING_01213",
        "(x0+(9))*(x1+(-2))-(-2)*x0-(9)*x1-(-18)",
        "x0*x1",
        3,
        true,
        "cancellation"
    },
    {
        "RING_01214",
        "((x0+0)*(x1+1))+((x2*0)+(-13)-(-13))",
        "x0*x1+x0",
        3,
        true,
        "neutral-elements"
    },
    {
        "RING_01215",
        "x0*(x1+(-6))-(-6)*x0",
        "x0*x1",
        3,
        true,
        "distribute-cancel"
    },
    {
        "RING_01216",
        "((x0+(1))+x1)*((x0+(1))-x1)",
        "(x0+(1))^2-x1^2",
        3,
        true,
        "difference-of-squares"
    },
    {
        "RING_01217",
        "(x0+(8))^2-(x0^2+(16)*x0+(64))",
        "0",
        3,
        true,
        "algebraic-zero"
    },
    {
        "RING_01218",
        "(x0+(-14))^2",
        "x0^2+(-28)*x0+(197)",
        3,
        false,
        "false-binomial"
    },
    {
        "RING_01219",
        "(x0+(-7))*(x0-(-7))",
        "x0^2-(49)",
        3,
        true,
        "conjugates"
    },
    {
        "RING_01220",
        "(x0+x1+(x2+(-2)))^2",
        "x0^2+x1^2+(x2+(-2))^2+2*x0*x1+2*x0*(x2+(-2))+2*x1*(x2+(-2))",
        3,
        true,
        "multivariate-square"
    },
    {
        "RING_01221",
        "((x0+(7))^2)*(x1+(-7))",
        "(x0^2+(14)*x0+(49))*(x1+(-7))",
        3,
        true,
        "product-squared"
    },
    {
        "RING_01222",
        "(14)*x0+(4)*x0+(-3)*x0+(12)*x0",
        "(27)*x0",
        3,
        true,
        "coefficient-aggregation"
    },
    {
        "RING_01223",
        "(-8)*(x0+x1+x2)^2",
        "(-8)*(x0^2+x1^2+x2^2+2*x0*x1+2*x0*x2+2*x1*x2)",
        3,
        true,
        "quadratic-form"
    },
    {
        "RING_01224",
        "(x0+(-1))*(x1+(-5))",
        "x0*x1+(-5)*x0+(-1)*x1+(5)",
        3,
        true,
        "distributivity"
    },
    {
        "RING_01225",
        "(x0+(6))^2",
        "x0^2+(12)*x0+(36)",
        3,
        true,
        "binomial-square"
    },
    {
        "RING_01226",
        "(x0+(13))^3",
        "x0^3+(39)*x0^2+(507)*x0+(2197)",
        3,
        true,
        "binomial-cube"
    },
    {
        "RING_01227",
        "(x0+(-9))*(x1+(-3))",
        "(x1+(-3))*(x0+(-9))",
        3,
        true,
        "commutativity"
    },
    {
        "RING_01228",
        "(x0+x1)+(x2+(-6))",
        "x0+(x1+(x2+(-6)))",
        3,
        true,
        "associativity"
    },
    {
        "RING_01229",
        "x0*x2+x1*x2+(5)*x2",
        "(x0+x1+(5))*x2",
        3,
        true,
        "factorization"
    },
    {
        "RING_01230",
        "(x0+(12))*(x1+(-1))-(-1)*x0-(12)*x1-(-12)",
        "x0*x1",
        3,
        true,
        "cancellation"
    },
    {
        "RING_01231",
        "((x0+0)*(x1+1))+((x2*0)+(-10)-(-10))",
        "x0*x1+x0",
        3,
        true,
        "neutral-elements"
    },
    {
        "RING_01232",
        "x0*(x1+(-3))-(-3)*x0",
        "x0*x1",
        3,
        true,
        "distribute-cancel"
    },
    {
        "RING_01233",
        "((x0+(4))+x1)*((x0+(4))-x1)",
        "(x0+(4))^2-x1^2",
        3,
        true,
        "difference-of-squares"
    },
    {
        "RING_01234",
        "(x0+(11))^2-(x0^2+(22)*x0+(121))",
        "0",
        3,
        true,
        "algebraic-zero"
    },
    {
        "RING_01235",
        "(x0+(-11))^2",
        "x0^2+(-22)*x0+(122)",
        3,
        false,
        "false-binomial"
    },
    {
        "RING_01236",
        "(x0+(-4))*(x0-(-4))",
        "x0^2-(16)",
        3,
        true,
        "conjugates"
    },
    {
        "RING_01237",
        "(x0+x1+(x2+(3)))^2",
        "x0^2+x1^2+(x2+(3))^2+2*x0*x1+2*x0*(x2+(3))+2*x1*(x2+(3))",
        3,
        true,
        "multivariate-square"
    },
    {
        "RING_01238",
        "((x0+(10))^2)*(x1+(-6))",
        "(x0^2+(20)*x0+(100))*(x1+(-6))",
        3,
        true,
        "product-squared"
    },
    {
        "RING_01239",
        "(-12)*x0+(5)*x0+(2)*x0+(1)*x0",
        "(-4)*x0",
        3,
        true,
        "coefficient-aggregation"
    },
    {
        "RING_01240",
        "(-5)*(x0+x1+x2)^2",
        "(-5)*(x0^2+x1^2+x2^2+2*x0*x1+2*x0*x2+2*x1*x2)",
        3,
        true,
        "quadratic-form"
    },
    {
        "RING_01241",
        "(x0+(2))*(x1+(-4))",
        "x0*x1+(-4)*x0+(2)*x1+(-8)",
        3,
        true,
        "distributivity"
    },
    {
        "RING_01242",
        "(x0+(9))^2",
        "x0^2+(18)*x0+(81)",
        3,
        true,
        "binomial-square"
    },
    {
        "RING_01243",
        "(x0+(-13))^3",
        "x0^3+(-39)*x0^2+(507)*x0+(-2197)",
        3,
        true,
        "binomial-cube"
    },
    {
        "RING_01244",
        "(x0+(-6))*(x1+(-2))",
        "(x1+(-2))*(x0+(-6))",
        3,
        true,
        "commutativity"
    },
    {
        "RING_01245",
        "(x0+x1)+(x2+(-1))",
        "x0+(x1+(x2+(-1)))",
        3,
        true,
        "associativity"
    },
    {
        "RING_01246",
        "x0*x2+x1*x2+(8)*x2",
        "(x0+x1+(8))*x2",
        3,
        true,
        "factorization"
    },
    {
        "RING_01247",
        "(x0+(-14))*(x1+(0))-(0)*x0-(-14)*x1-(0)",
        "x0*x1",
        3,
        true,
        "cancellation"
    },
    {
        "RING_01248",
        "((x0+0)*(x1+1))+((x2*0)+(-7)-(-7))",
        "x0*x1+x0",
        3,
        true,
        "neutral-elements"
    },
    {
        "RING_01249",
        "x0*(x1+(0))-(0)*x0",
        "x0*x1",
        3,
        true,
        "distribute-cancel"
    },
    {
        "RING_01250",
        "((x0+(7))+x1)*((x0+(7))-x1)",
        "(x0+(7))^2-x1^2",
        3,
        true,
        "difference-of-squares"
    },
    {
        "RING_01251",
        "(x0+(14))^2-(x0^2+(28)*x0+(196))",
        "0",
        3,
        true,
        "algebraic-zero"
    },
    {
        "RING_01252",
        "(x0+(-8))^2",
        "x0^2+(-16)*x0+(65)",
        3,
        false,
        "false-binomial"
    },
    {
        "RING_01253",
        "(x0+(-1))*(x0-(-1))",
        "x0^2-(1)",
        3,
        true,
        "conjugates"
    },
    {
        "RING_01254",
        "(x0+x1+(x2+(8)))^2",
        "x0^2+x1^2+(x2+(8))^2+2*x0*x1+2*x0*(x2+(8))+2*x1*(x2+(8))",
        3,
        true,
        "multivariate-square"
    },
    {
        "RING_01255",
        "((x0+(13))^2)*(x1+(-5))",
        "(x0^2+(26)*x0+(169))*(x1+(-5))",
        3,
        true,
        "product-squared"
    },
    {
        "RING_01256",
        "(-9)*x0+(6)*x0+(7)*x0+(-10)*x0",
        "(-6)*x0",
        3,
        true,
        "coefficient-aggregation"
    },
    {
        "RING_01257",
        "(-2)*(x0+x1+x2)^2",
        "(-2)*(x0^2+x1^2+x2^2+2*x0*x1+2*x0*x2+2*x1*x2)",
        3,
        true,
        "quadratic-form"
    },
    {
        "RING_01258",
        "(x0+(5))*(x1+(-3))",
        "x0*x1+(-3)*x0+(5)*x1+(-15)",
        3,
        true,
        "distributivity"
    },
    {
        "RING_01259",
        "(x0+(12))^2",
        "x0^2+(24)*x0+(144)",
        3,
        true,
        "binomial-square"
    },
    {
        "RING_01260",
        "(x0+(-10))^3",
        "x0^3+(-30)*x0^2+(300)*x0+(-1000)",
        3,
        true,
        "binomial-cube"
    },
    {
        "RING_01261",
        "(x0+(-3))*(x1+(-1))",
        "(x1+(-1))*(x0+(-3))",
        3,
        true,
        "commutativity"
    },
    {
        "RING_01262",
        "(x0+x1)+(x2+(4))",
        "x0+(x1+(x2+(4)))",
        3,
        true,
        "associativity"
    },
    {
        "RING_01263",
        "x0*x2+x1*x2+(11)*x2",
        "(x0+x1+(11))*x2",
        3,
        true,
        "factorization"
    },
    {
        "RING_01264",
        "(x0+(-11))*(x1+(1))-(1)*x0-(-11)*x1-(-11)",
        "x0*x1",
        3,
        true,
        "cancellation"
    },
    {
        "RING_01265",
        "((x0+0)*(x1+1))+((x2*0)+(-4)-(-4))",
        "x0*x1+x0",
        3,
        true,
        "neutral-elements"
    },
    {
        "RING_01266",
        "x0*(x1+(3))-(3)*x0",
        "x0*x1",
        3,
        true,
        "distribute-cancel"
    },
    {
        "RING_01267",
        "((x0+(10))+x1)*((x0+(10))-x1)",
        "(x0+(10))^2-x1^2",
        3,
        true,
        "difference-of-squares"
    },
    {
        "RING_01268",
        "(x0+(-12))^2-(x0^2+(-24)*x0+(144))",
        "0",
        3,
        true,
        "algebraic-zero"
    },
    {
        "RING_01269",
        "(x0+(-5))^2",
        "x0^2+(-10)*x0+(26)",
        3,
        false,
        "false-binomial"
    },
    {
        "RING_01270",
        "(x0+(2))*(x0-(2))",
        "x0^2-(4)",
        3,
        true,
        "conjugates"
    },
    {
        "RING_01271",
        "(x0+x1+(x2+(13)))^2",
        "x0^2+x1^2+(x2+(13))^2+2*x0*x1+2*x0*(x2+(13))+2*x1*(x2+(13))",
        3,
        true,
        "multivariate-square"
    },
    {
        "RING_01272",
        "((x0+(-13))^2)*(x1+(-4))",
        "(x0^2+(-26)*x0+(169))*(x1+(-4))",
        3,
        true,
        "product-squared"
    },
    {
        "RING_01273",
        "(-6)*x0+(7)*x0+(12)*x0+(4)*x0",
        "(17)*x0",
        3,
        true,
        "coefficient-aggregation"
    },
    {
        "RING_01274",
        "(1)*(x0+x1+x2)^2",
        "(1)*(x0^2+x1^2+x2^2+2*x0*x1+2*x0*x2+2*x1*x2)",
        3,
        true,
        "quadratic-form"
    },
    {
        "RING_01275",
        "(x0+(8))*(x1+(-2))",
        "x0*x1+(-2)*x0+(8)*x1+(-16)",
        3,
        true,
        "distributivity"
    },
    {
        "RING_01276",
        "(x0+(-14))^2",
        "x0^2+(-28)*x0+(196)",
        3,
        true,
        "binomial-square"
    },
    {
        "RING_01277",
        "(x0+(-7))^3",
        "x0^3+(-21)*x0^2+(147)*x0+(-343)",
        3,
        true,
        "binomial-cube"
    },
    {
        "RING_01278",
        "(x0+(0))*(x1+(0))",
        "(x1+(0))*(x0+(0))",
        3,
        true,
        "commutativity"
    },
    {
        "RING_01279",
        "(x0+x1)+(x2+(9))",
        "x0+(x1+(x2+(9)))",
        3,
        true,
        "associativity"
    },
    {
        "RING_01280",
        "x0*x2+x1*x2+(14)*x2",
        "(x0+x1+(14))*x2",
        3,
        true,
        "factorization"
    },
    {
        "RING_01281",
        "(x0+(-8))*(x1+(2))-(2)*x0-(-8)*x1-(-16)",
        "x0*x1",
        3,
        true,
        "cancellation"
    },
    {
        "RING_01282",
        "((x0+0)*(x1+1))+((x2*0)+(-1)-(-1))",
        "x0*x1+x0",
        3,
        true,
        "neutral-elements"
    },
    {
        "RING_01283",
        "x0*(x1+(6))-(6)*x0",
        "x0*x1",
        3,
        true,
        "distribute-cancel"
    },
    {
        "RING_01284",
        "((x0+(13))+x1)*((x0+(13))-x1)",
        "(x0+(13))^2-x1^2",
        3,
        true,
        "difference-of-squares"
    },
    {
        "RING_01285",
        "(x0+(-9))^2-(x0^2+(-18)*x0+(81))",
        "0",
        3,
        true,
        "algebraic-zero"
    },
    {
        "RING_01286",
        "(x0+(-2))^2",
        "x0^2+(-4)*x0+(5)",
        3,
        false,
        "false-binomial"
    },
    {
        "RING_01287",
        "(x0+(5))*(x0-(5))",
        "x0^2-(25)",
        3,
        true,
        "conjugates"
    },
    {
        "RING_01288",
        "(x0+x1+(x2+(-9)))^2",
        "x0^2+x1^2+(x2+(-9))^2+2*x0*x1+2*x0*(x2+(-9))+2*x1*(x2+(-9))",
        3,
        true,
        "multivariate-square"
    },
    {
        "RING_01289",
        "((x0+(-10))^2)*(x1+(-3))",
        "(x0^2+(-20)*x0+(100))*(x1+(-3))",
        3,
        true,
        "product-squared"
    },
    {
        "RING_01290",
        "(-3)*x0+(8)*x0+(-10)*x0+(-7)*x0",
        "(-12)*x0",
        3,
        true,
        "coefficient-aggregation"
    },
    {
        "RING_01291",
        "(4)*(x0+x1+x2)^2",
        "(4)*(x0^2+x1^2+x2^2+2*x0*x1+2*x0*x2+2*x1*x2)",
        3,
        true,
        "quadratic-form"
    },
    {
        "RING_01292",
        "(x0+(11))*(x1+(-1))",
        "x0*x1+(-1)*x0+(11)*x1+(-11)",
        3,
        true,
        "distributivity"
    },
    {
        "RING_01293",
        "(x0+(-11))^2",
        "x0^2+(-22)*x0+(121)",
        3,
        true,
        "binomial-square"
    },
    {
        "RING_01294",
        "(x0+(-4))^3",
        "x0^3+(-12)*x0^2+(48)*x0+(-64)",
        3,
        true,
        "binomial-cube"
    },
    {
        "RING_01295",
        "(x0+(3))*(x1+(1))",
        "(x1+(1))*(x0+(3))",
        3,
        true,
        "commutativity"
    },
    {
        "RING_01296",
        "(x0+x1)+(x2+(-13))",
        "x0+(x1+(x2+(-13)))",
        3,
        true,
        "associativity"
    },
    {
        "RING_01297",
        "x0*x2+x1*x2+(-12)*x2",
        "(x0+x1+(-12))*x2",
        3,
        true,
        "factorization"
    },
    {
        "RING_01298",
        "(x0+(-5))*(x1+(3))-(3)*x0-(-5)*x1-(-15)",
        "x0*x1",
        3,
        true,
        "cancellation"
    },
    {
        "RING_01299",
        "((x0+0)*(x1+1))+((x2*0)+(2)-(2))",
        "x0*x1+x0",
        3,
        true,
        "neutral-elements"
    },
    {
        "RING_01300",
        "x0*(x1+(9))-(9)*x0",
        "x0*x1",
        3,
        true,
        "distribute-cancel"
    },
    {
        "RING_01301",
        "((x0+(-13))+x1)*((x0+(-13))-x1)",
        "(x0+(-13))^2-x1^2",
        3,
        true,
        "difference-of-squares"
    },
    {
        "RING_01302",
        "(x0+(-6))^2-(x0^2+(-12)*x0+(36))",
        "0",
        3,
        true,
        "algebraic-zero"
    },
    {
        "RING_01303",
        "(x0+(1))^2",
        "x0^2+(2)*x0+(2)",
        3,
        false,
        "false-binomial"
    },
    {
        "RING_01304",
        "(x0+(8))*(x0-(8))",
        "x0^2-(64)",
        3,
        true,
        "conjugates"
    },
    {
        "RING_01305",
        "(x0+x1+(x2+(-4)))^2",
        "x0^2+x1^2+(x2+(-4))^2+2*x0*x1+2*x0*(x2+(-4))+2*x1*(x2+(-4))",
        3,
        true,
        "multivariate-square"
    },
    {
        "RING_01306",
        "((x0+(-7))^2)*(x1+(-2))",
        "(x0^2+(-14)*x0+(49))*(x1+(-2))",
        3,
        true,
        "product-squared"
    },
    {
        "RING_01307",
        "(0)*x0+(9)*x0+(-5)*x0+(7)*x0",
        "(11)*x0",
        3,
        true,
        "coefficient-aggregation"
    },
    {
        "RING_01308",
        "(7)*(x0+x1+x2)^2",
        "(7)*(x0^2+x1^2+x2^2+2*x0*x1+2*x0*x2+2*x1*x2)",
        3,
        true,
        "quadratic-form"
    },
    {
        "RING_01309",
        "(x0+(14))*(x1+(0))",
        "x0*x1+(0)*x0+(14)*x1+(0)",
        3,
        true,
        "distributivity"
    },
    {
        "RING_01310",
        "(x0+(-8))^2",
        "x0^2+(-16)*x0+(64)",
        3,
        true,
        "binomial-square"
    },
    {
        "RING_01311",
        "(x0+(-1))^3",
        "x0^3+(-3)*x0^2+(3)*x0+(-1)",
        3,
        true,
        "binomial-cube"
    },
    {
        "RING_01312",
        "(x0+(6))*(x1+(2))",
        "(x1+(2))*(x0+(6))",
        3,
        true,
        "commutativity"
    },
    {
        "RING_01313",
        "(x0+x1)+(x2+(-8))",
        "x0+(x1+(x2+(-8)))",
        3,
        true,
        "associativity"
    },
    {
        "RING_01314",
        "x0*x2+x1*x2+(-9)*x2",
        "(x0+x1+(-9))*x2",
        3,
        true,
        "factorization"
    },
    {
        "RING_01315",
        "(x0+(-2))*(x1+(4))-(4)*x0-(-2)*x1-(-8)",
        "x0*x1",
        3,
        true,
        "cancellation"
    },
    {
        "RING_01316",
        "((x0+0)*(x1+1))+((x2*0)+(5)-(5))",
        "x0*x1+x0",
        3,
        true,
        "neutral-elements"
    },
    {
        "RING_01317",
        "x0*(x1+(12))-(12)*x0",
        "x0*x1",
        3,
        true,
        "distribute-cancel"
    },
    {
        "RING_01318",
        "((x0+(-10))+x1)*((x0+(-10))-x1)",
        "(x0+(-10))^2-x1^2",
        3,
        true,
        "difference-of-squares"
    },
    {
        "RING_01319",
        "(x0+(-3))^2-(x0^2+(-6)*x0+(9))",
        "0",
        3,
        true,
        "algebraic-zero"
    },
    {
        "RING_01320",
        "(x0+(4))^2",
        "x0^2+(8)*x0+(17)",
        3,
        false,
        "false-binomial"
    },
    {
        "RING_01321",
        "(x0+(11))*(x0-(11))",
        "x0^2-(121)",
        3,
        true,
        "conjugates"
    },
    {
        "RING_01322",
        "(x0+x1+(x2+(1)))^2",
        "x0^2+x1^2+(x2+(1))^2+2*x0*x1+2*x0*(x2+(1))+2*x1*(x2+(1))",
        3,
        true,
        "multivariate-square"
    },
    {
        "RING_01323",
        "((x0+(-4))^2)*(x1+(-1))",
        "(x0^2+(-8)*x0+(16))*(x1+(-1))",
        3,
        true,
        "product-squared"
    },
    {
        "RING_01324",
        "(3)*x0+(10)*x0+(0)*x0+(-4)*x0",
        "(9)*x0",
        3,
        true,
        "coefficient-aggregation"
    },
    {
        "RING_01325",
        "(10)*(x0+x1+x2)^2",
        "(10)*(x0^2+x1^2+x2^2+2*x0*x1+2*x0*x2+2*x1*x2)",
        3,
        true,
        "quadratic-form"
    },
    {
        "RING_01326",
        "(x0+(-12))*(x1+(1))",
        "x0*x1+(1)*x0+(-12)*x1+(-12)",
        3,
        true,
        "distributivity"
    },
    {
        "RING_01327",
        "(x0+(-5))^2",
        "x0^2+(-10)*x0+(25)",
        3,
        true,
        "binomial-square"
    },
    {
        "RING_01328",
        "(x0+(2))^3",
        "x0^3+(6)*x0^2+(12)*x0+(8)",
        3,
        true,
        "binomial-cube"
    },
    {
        "RING_01329",
        "(x0+(9))*(x1+(3))",
        "(x1+(3))*(x0+(9))",
        3,
        true,
        "commutativity"
    },
    {
        "RING_01330",
        "(x0+x1)+(x2+(-3))",
        "x0+(x1+(x2+(-3)))",
        3,
        true,
        "associativity"
    },
    {
        "RING_01331",
        "x0*x2+x1*x2+(-6)*x2",
        "(x0+x1+(-6))*x2",
        3,
        true,
        "factorization"
    },
    {
        "RING_01332",
        "(x0+(1))*(x1+(5))-(5)*x0-(1)*x1-(5)",
        "x0*x1",
        3,
        true,
        "cancellation"
    },
    {
        "RING_01333",
        "((x0+0)*(x1+1))+((x2*0)+(8)-(8))",
        "x0*x1+x0",
        3,
        true,
        "neutral-elements"
    },
    {
        "RING_01334",
        "x0*(x1+(-14))-(-14)*x0",
        "x0*x1",
        3,
        true,
        "distribute-cancel"
    },
    {
        "RING_01335",
        "((x0+(-7))+x1)*((x0+(-7))-x1)",
        "(x0+(-7))^2-x1^2",
        3,
        true,
        "difference-of-squares"
    },
    {
        "RING_01336",
        "(x0+(0))^2-(x0^2+(0)*x0+(0))",
        "0",
        3,
        true,
        "algebraic-zero"
    },
    {
        "RING_01337",
        "(x0+(7))^2",
        "x0^2+(14)*x0+(50)",
        3,
        false,
        "false-binomial"
    },
    {
        "RING_01338",
        "(x0+(14))*(x0-(14))",
        "x0^2-(196)",
        3,
        true,
        "conjugates"
    },
    {
        "RING_01339",
        "(x0+x1+(x2+(6)))^2",
        "x0^2+x1^2+(x2+(6))^2+2*x0*x1+2*x0*(x2+(6))+2*x1*(x2+(6))",
        3,
        true,
        "multivariate-square"
    },
    {
        "RING_01340",
        "((x0+(-1))^2)*(x1+(0))",
        "(x0^2+(-2)*x0+(1))*(x1+(0))",
        3,
        true,
        "product-squared"
    },
    {
        "RING_01341",
        "(6)*x0+(11)*x0+(5)*x0+(10)*x0",
        "(32)*x0",
        3,
        true,
        "coefficient-aggregation"
    },
    {
        "RING_01342",
        "(13)*(x0+x1+x2)^2",
        "(13)*(x0^2+x1^2+x2^2+2*x0*x1+2*x0*x2+2*x1*x2)",
        3,
        true,
        "quadratic-form"
    },
    {
        "RING_01343",
        "(x0+(-9))*(x1+(2))",
        "x0*x1+(2)*x0+(-9)*x1+(-18)",
        3,
        true,
        "distributivity"
    },
    {
        "RING_01344",
        "(x0+(-2))^2",
        "x0^2+(-4)*x0+(4)",
        3,
        true,
        "binomial-square"
    },
    {
        "RING_01345",
        "(x0+(5))^3",
        "x0^3+(15)*x0^2+(75)*x0+(125)",
        3,
        true,
        "binomial-cube"
    },
    {
        "RING_01346",
        "(x0+(12))*(x1+(4))",
        "(x1+(4))*(x0+(12))",
        3,
        true,
        "commutativity"
    },
    {
        "RING_01347",
        "(x0+x1)+(x2+(2))",
        "x0+(x1+(x2+(2)))",
        3,
        true,
        "associativity"
    },
    {
        "RING_01348",
        "x0*x2+x1*x2+(-3)*x2",
        "(x0+x1+(-3))*x2",
        3,
        true,
        "factorization"
    },
    {
        "RING_01349",
        "(x0+(4))*(x1+(6))-(6)*x0-(4)*x1-(24)",
        "x0*x1",
        3,
        true,
        "cancellation"
    },
    {
        "RING_01350",
        "((x0+0)*(x1+1))+((x2*0)+(11)-(11))",
        "x0*x1+x0",
        3,
        true,
        "neutral-elements"
    },
    {
        "RING_01351",
        "x0*(x1+(-11))-(-11)*x0",
        "x0*x1",
        3,
        true,
        "distribute-cancel"
    },
    {
        "RING_01352",
        "((x0+(-4))+x1)*((x0+(-4))-x1)",
        "(x0+(-4))^2-x1^2",
        3,
        true,
        "difference-of-squares"
    },
    {
        "RING_01353",
        "(x0+(3))^2-(x0^2+(6)*x0+(9))",
        "0",
        3,
        true,
        "algebraic-zero"
    },
    {
        "RING_01354",
        "(x0+(10))^2",
        "x0^2+(20)*x0+(101)",
        3,
        false,
        "false-binomial"
    },
    {
        "RING_01355",
        "(x0+(-12))*(x0-(-12))",
        "x0^2-(144)",
        3,
        true,
        "conjugates"
    },
    {
        "RING_01356",
        "(x0+x1+(x2+(11)))^2",
        "x0^2+x1^2+(x2+(11))^2+2*x0*x1+2*x0*(x2+(11))+2*x1*(x2+(11))",
        3,
        true,
        "multivariate-square"
    },
    {
        "RING_01357",
        "((x0+(2))^2)*(x1+(1))",
        "(x0^2+(4)*x0+(4))*(x1+(1))",
        3,
        true,
        "product-squared"
    },
    {
        "RING_01358",
        "(9)*x0+(12)*x0+(10)*x0+(-1)*x0",
        "(30)*x0",
        3,
        true,
        "coefficient-aggregation"
    },
    {
        "RING_01359",
        "(-13)*(x0+x1+x2)^2",
        "(-13)*(x0^2+x1^2+x2^2+2*x0*x1+2*x0*x2+2*x1*x2)",
        3,
        true,
        "quadratic-form"
    },
    {
        "RING_01360",
        "(x0+(-6))*(x1+(3))",
        "x0*x1+(3)*x0+(-6)*x1+(-18)",
        3,
        true,
        "distributivity"
    },
    {
        "RING_01361",
        "(x0+(1))^2",
        "x0^2+(2)*x0+(1)",
        3,
        true,
        "binomial-square"
    },
    {
        "RING_01362",
        "(x0+(8))^3",
        "x0^3+(24)*x0^2+(192)*x0+(512)",
        3,
        true,
        "binomial-cube"
    },
    {
        "RING_01363",
        "(x0+(-14))*(x1+(5))",
        "(x1+(5))*(x0+(-14))",
        3,
        true,
        "commutativity"
    },
    {
        "RING_01364",
        "(x0+x1)+(x2+(7))",
        "x0+(x1+(x2+(7)))",
        3,
        true,
        "associativity"
    },
    {
        "RING_01365",
        "x0*x2+x1*x2+(0)*x2",
        "(x0+x1+(0))*x2",
        3,
        true,
        "factorization"
    },
    {
        "RING_01366",
        "(x0+(7))*(x1+(7))-(7)*x0-(7)*x1-(49)",
        "x0*x1",
        3,
        true,
        "cancellation"
    },
    {
        "RING_01367",
        "((x0+0)*(x1+1))+((x2*0)+(14)-(14))",
        "x0*x1+x0",
        3,
        true,
        "neutral-elements"
    },
    {
        "RING_01368",
        "x0*(x1+(-8))-(-8)*x0",
        "x0*x1",
        3,
        true,
        "distribute-cancel"
    },
    {
        "RING_01369",
        "((x0+(-1))+x1)*((x0+(-1))-x1)",
        "(x0+(-1))^2-x1^2",
        3,
        true,
        "difference-of-squares"
    },
    {
        "RING_01370",
        "(x0+(6))^2-(x0^2+(12)*x0+(36))",
        "0",
        3,
        true,
        "algebraic-zero"
    },
    {
        "RING_01371",
        "(x0+(13))^2",
        "x0^2+(26)*x0+(170)",
        3,
        false,
        "false-binomial"
    },
    {
        "RING_01372",
        "(x0+(-9))*(x0-(-9))",
        "x0^2-(81)",
        3,
        true,
        "conjugates"
    },
    {
        "RING_01373",
        "(x0+x1+(x2+(-11)))^2",
        "x0^2+x1^2+(x2+(-11))^2+2*x0*x1+2*x0*(x2+(-11))+2*x1*(x2+(-11))",
        3,
        true,
        "multivariate-square"
    },
    {
        "RING_01374",
        "((x0+(5))^2)*(x1+(2))",
        "(x0^2+(10)*x0+(25))*(x1+(2))",
        3,
        true,
        "product-squared"
    },
    {
        "RING_01375",
        "(12)*x0+(13)*x0+(-12)*x0+(-12)*x0",
        "(1)*x0",
        3,
        true,
        "coefficient-aggregation"
    },
    {
        "RING_01376",
        "(-10)*(x0+x1+x2)^2",
        "(-10)*(x0^2+x1^2+x2^2+2*x0*x1+2*x0*x2+2*x1*x2)",
        3,
        true,
        "quadratic-form"
    },
    {
        "RING_01377",
        "(x0+(-3))*(x1+(4))",
        "x0*x1+(4)*x0+(-3)*x1+(-12)",
        3,
        true,
        "distributivity"
    },
    {
        "RING_01378",
        "(x0+(4))^2",
        "x0^2+(8)*x0+(16)",
        3,
        true,
        "binomial-square"
    },
    {
        "RING_01379",
        "(x0+(11))^3",
        "x0^3+(33)*x0^2+(363)*x0+(1331)",
        3,
        true,
        "binomial-cube"
    },
    {
        "RING_01380",
        "(x0+(-11))*(x1+(6))",
        "(x1+(6))*(x0+(-11))",
        3,
        true,
        "commutativity"
    },
    {
        "RING_01381",
        "(x0+x1)+(x2+(12))",
        "x0+(x1+(x2+(12)))",
        3,
        true,
        "associativity"
    },
    {
        "RING_01382",
        "x0*x2+x1*x2+(3)*x2",
        "(x0+x1+(3))*x2",
        3,
        true,
        "factorization"
    },
    {
        "RING_01383",
        "(x0+(10))*(x1+(8))-(8)*x0-(10)*x1-(80)",
        "x0*x1",
        3,
        true,
        "cancellation"
    },
    {
        "RING_01384",
        "((x0+0)*(x1+1))+((x2*0)+(-12)-(-12))",
        "x0*x1+x0",
        3,
        true,
        "neutral-elements"
    },
    {
        "RING_01385",
        "x0*(x1+(-5))-(-5)*x0",
        "x0*x1",
        3,
        true,
        "distribute-cancel"
    },
    {
        "RING_01386",
        "((x0+(2))+x1)*((x0+(2))-x1)",
        "(x0+(2))^2-x1^2",
        3,
        true,
        "difference-of-squares"
    },
    {
        "RING_01387",
        "(x0+(9))^2-(x0^2+(18)*x0+(81))",
        "0",
        3,
        true,
        "algebraic-zero"
    },
    {
        "RING_01388",
        "(x0+(-13))^2",
        "x0^2+(-26)*x0+(170)",
        3,
        false,
        "false-binomial"
    },
    {
        "RING_01389",
        "(x0+(-6))*(x0-(-6))",
        "x0^2-(36)",
        3,
        true,
        "conjugates"
    },
    {
        "RING_01390",
        "(x0+x1+(x2+(-6)))^2",
        "x0^2+x1^2+(x2+(-6))^2+2*x0*x1+2*x0*(x2+(-6))+2*x1*(x2+(-6))",
        3,
        true,
        "multivariate-square"
    },
    {
        "RING_01391",
        "((x0+(8))^2)*(x1+(3))",
        "(x0^2+(16)*x0+(64))*(x1+(3))",
        3,
        true,
        "product-squared"
    },
    {
        "RING_01392",
        "(-14)*x0+(14)*x0+(-7)*x0+(2)*x0",
        "(-5)*x0",
        3,
        true,
        "coefficient-aggregation"
    },
    {
        "RING_01393",
        "(-7)*(x0+x1+x2)^2",
        "(-7)*(x0^2+x1^2+x2^2+2*x0*x1+2*x0*x2+2*x1*x2)",
        3,
        true,
        "quadratic-form"
    },
    {
        "RING_01394",
        "(x0+(0))*(x1+(5))",
        "x0*x1+(5)*x0+(0)*x1+(0)",
        3,
        true,
        "distributivity"
    },
    {
        "RING_01395",
        "(x0+(7))^2",
        "x0^2+(14)*x0+(49)",
        3,
        true,
        "binomial-square"
    },
    {
        "RING_01396",
        "(x0+(14))^3",
        "x0^3+(42)*x0^2+(588)*x0+(2744)",
        3,
        true,
        "binomial-cube"
    },
    {
        "RING_01397",
        "(x0+(-8))*(x1+(7))",
        "(x1+(7))*(x0+(-8))",
        3,
        true,
        "commutativity"
    },
    {
        "RING_01398",
        "(x0+x1)+(x2+(-10))",
        "x0+(x1+(x2+(-10)))",
        3,
        true,
        "associativity"
    },
    {
        "RING_01399",
        "x0*x2+x1*x2+(6)*x2",
        "(x0+x1+(6))*x2",
        3,
        true,
        "factorization"
    },
    {
        "RING_01400",
        "(x0+(13))*(x1+(9))-(9)*x0-(13)*x1-(117)",
        "x0*x1",
        3,
        true,
        "cancellation"
    },
    {
        "RING_01401",
        "((x0+0)*(x1+1))+((x2*0)+(-9)-(-9))",
        "x0*x1+x0",
        3,
        true,
        "neutral-elements"
    },
    {
        "RING_01402",
        "x0*(x1+(-2))-(-2)*x0",
        "x0*x1",
        3,
        true,
        "distribute-cancel"
    },
    {
        "RING_01403",
        "((x0+(5))+x1)*((x0+(5))-x1)",
        "(x0+(5))^2-x1^2",
        3,
        true,
        "difference-of-squares"
    },
    {
        "RING_01404",
        "(x0+(12))^2-(x0^2+(24)*x0+(144))",
        "0",
        3,
        true,
        "algebraic-zero"
    },
    {
        "RING_01405",
        "(x0+(-10))^2",
        "x0^2+(-20)*x0+(101)",
        3,
        false,
        "false-binomial"
    },
    {
        "RING_01406",
        "(x0+(-3))*(x0-(-3))",
        "x0^2-(9)",
        3,
        true,
        "conjugates"
    },
    {
        "RING_01407",
        "(x0+x1+(x2+(-1)))^2",
        "x0^2+x1^2+(x2+(-1))^2+2*x0*x1+2*x0*(x2+(-1))+2*x1*(x2+(-1))",
        3,
        true,
        "multivariate-square"
    },
    {
        "RING_01408",
        "((x0+(11))^2)*(x1+(4))",
        "(x0^2+(22)*x0+(121))*(x1+(4))",
        3,
        true,
        "product-squared"
    },
    {
        "RING_01409",
        "(-11)*x0+(15)*x0+(-2)*x0+(-9)*x0",
        "(-7)*x0",
        3,
        true,
        "coefficient-aggregation"
    },
    {
        "RING_01410",
        "(-4)*(x0+x1+x2)^2",
        "(-4)*(x0^2+x1^2+x2^2+2*x0*x1+2*x0*x2+2*x1*x2)",
        3,
        true,
        "quadratic-form"
    },
    {
        "RING_01411",
        "(x0+(3))*(x1+(6))",
        "x0*x1+(6)*x0+(3)*x1+(18)",
        3,
        true,
        "distributivity"
    },
    {
        "RING_01412",
        "(x0+(10))^2",
        "x0^2+(20)*x0+(100)",
        3,
        true,
        "binomial-square"
    },
    {
        "RING_01413",
        "(x0+(-12))^3",
        "x0^3+(-36)*x0^2+(432)*x0+(-1728)",
        3,
        true,
        "binomial-cube"
    },
    {
        "RING_01414",
        "(x0+(-5))*(x1+(8))",
        "(x1+(8))*(x0+(-5))",
        3,
        true,
        "commutativity"
    },
    {
        "RING_01415",
        "(x0+x1)+(x2+(-5))",
        "x0+(x1+(x2+(-5)))",
        3,
        true,
        "associativity"
    },
    {
        "RING_01416",
        "x0*x2+x1*x2+(9)*x2",
        "(x0+x1+(9))*x2",
        3,
        true,
        "factorization"
    },
    {
        "RING_01417",
        "(x0+(-13))*(x1+(10))-(10)*x0-(-13)*x1-(-130)",
        "x0*x1",
        3,
        true,
        "cancellation"
    },
    {
        "RING_01418",
        "((x0+0)*(x1+1))+((x2*0)+(-6)-(-6))",
        "x0*x1+x0",
        3,
        true,
        "neutral-elements"
    },
    {
        "RING_01419",
        "x0*(x1+(1))-(1)*x0",
        "x0*x1",
        3,
        true,
        "distribute-cancel"
    },
    {
        "RING_01420",
        "((x0+(8))+x1)*((x0+(8))-x1)",
        "(x0+(8))^2-x1^2",
        3,
        true,
        "difference-of-squares"
    },
    {
        "RING_01421",
        "(x0+(-14))^2-(x0^2+(-28)*x0+(196))",
        "0",
        3,
        true,
        "algebraic-zero"
    },
    {
        "RING_01422",
        "(x0+(-7))^2",
        "x0^2+(-14)*x0+(50)",
        3,
        false,
        "false-binomial"
    },
    {
        "RING_01423",
        "(x0+(0))*(x0-(0))",
        "x0^2-(0)",
        3,
        true,
        "conjugates"
    },
    {
        "RING_01424",
        "(x0+x1+(x2+(4)))^2",
        "x0^2+x1^2+(x2+(4))^2+2*x0*x1+2*x0*(x2+(4))+2*x1*(x2+(4))",
        3,
        true,
        "multivariate-square"
    },
    {
        "RING_01425",
        "((x0+(14))^2)*(x1+(5))",
        "(x0^2+(28)*x0+(196))*(x1+(5))",
        3,
        true,
        "product-squared"
    },
    {
        "RING_01426",
        "(-8)*x0+(-15)*x0+(3)*x0+(5)*x0",
        "(-15)*x0",
        3,
        true,
        "coefficient-aggregation"
    },
    {
        "RING_01427",
        "(-1)*(x0+x1+x2)^2",
        "(-1)*(x0^2+x1^2+x2^2+2*x0*x1+2*x0*x2+2*x1*x2)",
        3,
        true,
        "quadratic-form"
    },
    {
        "RING_01428",
        "(x0+(6))*(x1+(7))",
        "x0*x1+(7)*x0+(6)*x1+(42)",
        3,
        true,
        "distributivity"
    },
    {
        "RING_01429",
        "(x0+(13))^2",
        "x0^2+(26)*x0+(169)",
        3,
        true,
        "binomial-square"
    },
    {
        "RING_01430",
        "(x0+(-9))^3",
        "x0^3+(-27)*x0^2+(243)*x0+(-729)",
        3,
        true,
        "binomial-cube"
    },
    {
        "RING_01431",
        "(x0+(-2))*(x1+(9))",
        "(x1+(9))*(x0+(-2))",
        3,
        true,
        "commutativity"
    },
    {
        "RING_01432",
        "(x0+x1)+(x2+(0))",
        "x0+(x1+(x2+(0)))",
        3,
        true,
        "associativity"
    },
    {
        "RING_01433",
        "x0*x2+x1*x2+(12)*x2",
        "(x0+x1+(12))*x2",
        3,
        true,
        "factorization"
    },
    {
        "RING_01434",
        "(x0+(-10))*(x1+(11))-(11)*x0-(-10)*x1-(-110)",
        "x0*x1",
        3,
        true,
        "cancellation"
    },
    {
        "RING_01435",
        "((x0+0)*(x1+1))+((x2*0)+(-3)-(-3))",
        "x0*x1+x0",
        3,
        true,
        "neutral-elements"
    },
    {
        "RING_01436",
        "x0*(x1+(4))-(4)*x0",
        "x0*x1",
        3,
        true,
        "distribute-cancel"
    },
    {
        "RING_01437",
        "((x0+(11))+x1)*((x0+(11))-x1)",
        "(x0+(11))^2-x1^2",
        3,
        true,
        "difference-of-squares"
    },
    {
        "RING_01438",
        "(x0+(-11))^2-(x0^2+(-22)*x0+(121))",
        "0",
        3,
        true,
        "algebraic-zero"
    },
    {
        "RING_01439",
        "(x0+(-4))^2",
        "x0^2+(-8)*x0+(17)",
        3,
        false,
        "false-binomial"
    },
    {
        "RING_01440",
        "(x0+(3))*(x0-(3))",
        "x0^2-(9)",
        3,
        true,
        "conjugates"
    },
    {
        "RING_01441",
        "(x0+x1+(x2+(9)))^2",
        "x0^2+x1^2+(x2+(9))^2+2*x0*x1+2*x0*(x2+(9))+2*x1*(x2+(9))",
        3,
        true,
        "multivariate-square"
    },
    {
        "RING_01442",
        "((x0+(-12))^2)*(x1+(6))",
        "(x0^2+(-24)*x0+(144))*(x1+(6))",
        3,
        true,
        "product-squared"
    },
    {
        "RING_01443",
        "(-5)*x0+(-14)*x0+(8)*x0+(-6)*x0",
        "(-17)*x0",
        3,
        true,
        "coefficient-aggregation"
    },
    {
        "RING_01444",
        "(2)*(x0+x1+x2)^2",
        "(2)*(x0^2+x1^2+x2^2+2*x0*x1+2*x0*x2+2*x1*x2)",
        3,
        true,
        "quadratic-form"
    },
    {
        "RING_01445",
        "(x0+(9))*(x1+(8))",
        "x0*x1+(8)*x0+(9)*x1+(72)",
        3,
        true,
        "distributivity"
    },
    {
        "RING_01446",
        "(x0+(-13))^2",
        "x0^2+(-26)*x0+(169)",
        3,
        true,
        "binomial-square"
    },
    {
        "RING_01447",
        "(x0+(-6))^3",
        "x0^3+(-18)*x0^2+(108)*x0+(-216)",
        3,
        true,
        "binomial-cube"
    },
    {
        "RING_01448",
        "(x0+(1))*(x1+(10))",
        "(x1+(10))*(x0+(1))",
        3,
        true,
        "commutativity"
    },
    {
        "RING_01449",
        "(x0+x1)+(x2+(5))",
        "x0+(x1+(x2+(5)))",
        3,
        true,
        "associativity"
    },
    {
        "RING_01450",
        "x0*x2+x1*x2+(-14)*x2",
        "(x0+x1+(-14))*x2",
        3,
        true,
        "factorization"
    },
    {
        "RING_01451",
        "(x0+(-7))*(x1+(12))-(12)*x0-(-7)*x1-(-84)",
        "x0*x1",
        3,
        true,
        "cancellation"
    },
    {
        "RING_01452",
        "((x0+0)*(x1+1))+((x2*0)+(0)-(0))",
        "x0*x1+x0",
        3,
        true,
        "neutral-elements"
    },
    {
        "RING_01453",
        "x0*(x1+(7))-(7)*x0",
        "x0*x1",
        3,
        true,
        "distribute-cancel"
    },
    {
        "RING_01454",
        "((x0+(14))+x1)*((x0+(14))-x1)",
        "(x0+(14))^2-x1^2",
        3,
        true,
        "difference-of-squares"
    },
    {
        "RING_01455",
        "(x0+(-8))^2-(x0^2+(-16)*x0+(64))",
        "0",
        3,
        true,
        "algebraic-zero"
    },
    {
        "RING_01456",
        "(x0+(-1))^2",
        "x0^2+(-2)*x0+(2)",
        3,
        false,
        "false-binomial"
    },
    {
        "RING_01457",
        "(x0+(6))*(x0-(6))",
        "x0^2-(36)",
        3,
        true,
        "conjugates"
    },
    {
        "RING_01458",
        "(x0+x1+(x2+(-13)))^2",
        "x0^2+x1^2+(x2+(-13))^2+2*x0*x1+2*x0*(x2+(-13))+2*x1*(x2+(-13))",
        3,
        true,
        "multivariate-square"
    },
    {
        "RING_01459",
        "((x0+(-9))^2)*(x1+(7))",
        "(x0^2+(-18)*x0+(81))*(x1+(7))",
        3,
        true,
        "product-squared"
    },
    {
        "RING_01460",
        "(-2)*x0+(-13)*x0+(13)*x0+(8)*x0",
        "(6)*x0",
        3,
        true,
        "coefficient-aggregation"
    },
    {
        "RING_01461",
        "(5)*(x0+x1+x2)^2",
        "(5)*(x0^2+x1^2+x2^2+2*x0*x1+2*x0*x2+2*x1*x2)",
        3,
        true,
        "quadratic-form"
    },
    {
        "RING_01462",
        "(x0+(12))*(x1+(9))",
        "x0*x1+(9)*x0+(12)*x1+(108)",
        3,
        true,
        "distributivity"
    },
    {
        "RING_01463",
        "(x0+(-10))^2",
        "x0^2+(-20)*x0+(100)",
        3,
        true,
        "binomial-square"
    },
    {
        "RING_01464",
        "(x0+(-3))^3",
        "x0^3+(-9)*x0^2+(27)*x0+(-27)",
        3,
        true,
        "binomial-cube"
    },
    {
        "RING_01465",
        "(x0+(4))*(x1+(11))",
        "(x1+(11))*(x0+(4))",
        3,
        true,
        "commutativity"
    },
    {
        "RING_01466",
        "(x0+x1)+(x2+(10))",
        "x0+(x1+(x2+(10)))",
        3,
        true,
        "associativity"
    },
    {
        "RING_01467",
        "x0*x2+x1*x2+(-11)*x2",
        "(x0+x1+(-11))*x2",
        3,
        true,
        "factorization"
    },
    {
        "RING_01468",
        "(x0+(-4))*(x1+(13))-(13)*x0-(-4)*x1-(-52)",
        "x0*x1",
        3,
        true,
        "cancellation"
    },
    {
        "RING_01469",
        "((x0+0)*(x1+1))+((x2*0)+(3)-(3))",
        "x0*x1+x0",
        3,
        true,
        "neutral-elements"
    },
    {
        "RING_01470",
        "x0*(x1+(10))-(10)*x0",
        "x0*x1",
        3,
        true,
        "distribute-cancel"
    },
    {
        "RING_01471",
        "((x0+(-12))+x1)*((x0+(-12))-x1)",
        "(x0+(-12))^2-x1^2",
        3,
        true,
        "difference-of-squares"
    },
    {
        "RING_01472",
        "(x0+(-5))^2-(x0^2+(-10)*x0+(25))",
        "0",
        3,
        true,
        "algebraic-zero"
    },
    {
        "RING_01473",
        "(x0+(2))^2",
        "x0^2+(4)*x0+(5)",
        3,
        false,
        "false-binomial"
    },
    {
        "RING_01474",
        "(x0+(9))*(x0-(9))",
        "x0^2-(81)",
        3,
        true,
        "conjugates"
    },
    {
        "RING_01475",
        "(x0+x1+(x2+(-8)))^2",
        "x0^2+x1^2+(x2+(-8))^2+2*x0*x1+2*x0*(x2+(-8))+2*x1*(x2+(-8))",
        3,
        true,
        "multivariate-square"
    },
    {
        "RING_01476",
        "((x0+(-6))^2)*(x1+(8))",
        "(x0^2+(-12)*x0+(36))*(x1+(8))",
        3,
        true,
        "product-squared"
    },
    {
        "RING_01477",
        "(1)*x0+(-12)*x0+(-9)*x0+(-3)*x0",
        "(-23)*x0",
        3,
        true,
        "coefficient-aggregation"
    },
    {
        "RING_01478",
        "(8)*(x0+x1+x2)^2",
        "(8)*(x0^2+x1^2+x2^2+2*x0*x1+2*x0*x2+2*x1*x2)",
        3,
        true,
        "quadratic-form"
    },
    {
        "RING_01479",
        "(x0+(-14))*(x1+(10))",
        "x0*x1+(10)*x0+(-14)*x1+(-140)",
        3,
        true,
        "distributivity"
    },
    {
        "RING_01480",
        "(x0+(-7))^2",
        "x0^2+(-14)*x0+(49)",
        3,
        true,
        "binomial-square"
    },
    {
        "RING_01481",
        "(x0+(0))^3",
        "x0^3+(0)*x0^2+(0)*x0+(0)",
        3,
        true,
        "binomial-cube"
    },
    {
        "RING_01482",
        "(x0+(7))*(x1+(12))",
        "(x1+(12))*(x0+(7))",
        3,
        true,
        "commutativity"
    },
    {
        "RING_01483",
        "(x0+x1)+(x2+(-12))",
        "x0+(x1+(x2+(-12)))",
        3,
        true,
        "associativity"
    },
    {
        "RING_01484",
        "x0*x2+x1*x2+(-8)*x2",
        "(x0+x1+(-8))*x2",
        3,
        true,
        "factorization"
    },
    {
        "RING_01485",
        "(x0+(-1))*(x1+(14))-(14)*x0-(-1)*x1-(-14)",
        "x0*x1",
        3,
        true,
        "cancellation"
    },
    {
        "RING_01486",
        "((x0+0)*(x1+1))+((x2*0)+(6)-(6))",
        "x0*x1+x0",
        3,
        true,
        "neutral-elements"
    },
    {
        "RING_01487",
        "x0*(x1+(13))-(13)*x0",
        "x0*x1",
        3,
        true,
        "distribute-cancel"
    },
    {
        "RING_01488",
        "((x0+(-9))+x1)*((x0+(-9))-x1)",
        "(x0+(-9))^2-x1^2",
        3,
        true,
        "difference-of-squares"
    },
    {
        "RING_01489",
        "(x0+(-2))^2-(x0^2+(-4)*x0+(4))",
        "0",
        3,
        true,
        "algebraic-zero"
    },
    {
        "RING_01490",
        "(x0+(5))^2",
        "x0^2+(10)*x0+(26)",
        3,
        false,
        "false-binomial"
    },
    {
        "RING_01491",
        "(x0+(12))*(x0-(12))",
        "x0^2-(144)",
        3,
        true,
        "conjugates"
    },
    {
        "RING_01492",
        "(x0+x1+(x2+(-3)))^2",
        "x0^2+x1^2+(x2+(-3))^2+2*x0*x1+2*x0*(x2+(-3))+2*x1*(x2+(-3))",
        3,
        true,
        "multivariate-square"
    },
    {
        "RING_01493",
        "((x0+(-3))^2)*(x1+(9))",
        "(x0^2+(-6)*x0+(9))*(x1+(9))",
        3,
        true,
        "product-squared"
    },
    {
        "RING_01494",
        "(4)*x0+(-11)*x0+(-4)*x0+(11)*x0",
        "(0)*x0",
        3,
        true,
        "coefficient-aggregation"
    },
    {
        "RING_01495",
        "(11)*(x0+x1+x2)^2",
        "(11)*(x0^2+x1^2+x2^2+2*x0*x1+2*x0*x2+2*x1*x2)",
        3,
        true,
        "quadratic-form"
    },
    {
        "RING_01496",
        "(x0+(-11))*(x1+(11))",
        "x0*x1+(11)*x0+(-11)*x1+(-121)",
        3,
        true,
        "distributivity"
    },
    {
        "RING_01497",
        "(x0+(-4))^2",
        "x0^2+(-8)*x0+(16)",
        3,
        true,
        "binomial-square"
    },
    {
        "RING_01498",
        "(x0+(3))^3",
        "x0^3+(9)*x0^2+(27)*x0+(27)",
        3,
        true,
        "binomial-cube"
    },
    {
        "RING_01499",
        "(x0+(10))*(x1+(13))",
        "(x1+(13))*(x0+(10))",
        3,
        true,
        "commutativity"
    },
    {
        "RING_01500",
        "(x0+x1)+(x2+(-7))",
        "x0+(x1+(x2+(-7)))",
        3,
        true,
        "associativity"
    },
    {
        "RING_01501",
        "x0*x2+x1*x2+(-5)*x2",
        "(x0+x1+(-5))*x2",
        3,
        true,
        "factorization"
    },
    {
        "RING_01502",
        "(x0+(2))*(x1+(15))-(15)*x0-(2)*x1-(30)",
        "x0*x1",
        3,
        true,
        "cancellation"
    },
    {
        "RING_01503",
        "((x0+0)*(x1+1))+((x2*0)+(9)-(9))",
        "x0*x1+x0",
        3,
        true,
        "neutral-elements"
    },
    {
        "RING_01504",
        "x0*(x1+(-13))-(-13)*x0",
        "x0*x1",
        3,
        true,
        "distribute-cancel"
    },
    {
        "RING_01505",
        "((x0+(-6))+x1)*((x0+(-6))-x1)",
        "(x0+(-6))^2-x1^2",
        3,
        true,
        "difference-of-squares"
    },
    {
        "RING_01506",
        "(x0+(1))^2-(x0^2+(2)*x0+(1))",
        "0",
        3,
        true,
        "algebraic-zero"
    },
    {
        "RING_01507",
        "(x0+(8))^2",
        "x0^2+(16)*x0+(65)",
        3,
        false,
        "false-binomial"
    },
    {
        "RING_01508",
        "(x0+(-14))*(x0-(-14))",
        "x0^2-(196)",
        3,
        true,
        "conjugates"
    },
    {
        "RING_01509",
        "(x0+x1+(x2+(2)))^2",
        "x0^2+x1^2+(x2+(2))^2+2*x0*x1+2*x0*(x2+(2))+2*x1*(x2+(2))",
        3,
        true,
        "multivariate-square"
    },
    {
        "RING_01510",
        "((x0+(0))^2)*(x1+(10))",
        "(x0^2+(0)*x0+(0))*(x1+(10))",
        3,
        true,
        "product-squared"
    },
    {
        "RING_01511",
        "(7)*x0+(-10)*x0+(1)*x0+(0)*x0",
        "(-2)*x0",
        3,
        true,
        "coefficient-aggregation"
    },
    {
        "RING_01512",
        "(14)*(x0+x1+x2)^2",
        "(14)*(x0^2+x1^2+x2^2+2*x0*x1+2*x0*x2+2*x1*x2)",
        3,
        true,
        "quadratic-form"
    },
    {
        "RING_01513",
        "(x0+(-8))*(x1+(12))",
        "x0*x1+(12)*x0+(-8)*x1+(-96)",
        3,
        true,
        "distributivity"
    },
    {
        "RING_01514",
        "(x0+(-1))^2",
        "x0^2+(-2)*x0+(1)",
        3,
        true,
        "binomial-square"
    },
    {
        "RING_01515",
        "(x0+(6))^3",
        "x0^3+(18)*x0^2+(108)*x0+(216)",
        3,
        true,
        "binomial-cube"
    },
    {
        "RING_01516",
        "(x0+(13))*(x1+(14))",
        "(x1+(14))*(x0+(13))",
        3,
        true,
        "commutativity"
    },
    {
        "RING_01517",
        "(x0+x1)+(x2+(-2))",
        "x0+(x1+(x2+(-2)))",
        3,
        true,
        "associativity"
    },
    {
        "RING_01518",
        "x0*x2+x1*x2+(-2)*x2",
        "(x0+x1+(-2))*x2",
        3,
        true,
        "factorization"
    },
    {
        "RING_01519",
        "(x0+(5))*(x1+(-15))-(-15)*x0-(5)*x1-(-75)",
        "x0*x1",
        3,
        true,
        "cancellation"
    },
    {
        "RING_01520",
        "((x0+0)*(x1+1))+((x2*0)+(12)-(12))",
        "x0*x1+x0",
        3,
        true,
        "neutral-elements"
    },
    {
        "RING_01521",
        "x0*(x1+(-10))-(-10)*x0",
        "x0*x1",
        3,
        true,
        "distribute-cancel"
    },
    {
        "RING_01522",
        "((x0+(-3))+x1)*((x0+(-3))-x1)",
        "(x0+(-3))^2-x1^2",
        3,
        true,
        "difference-of-squares"
    },
    {
        "RING_01523",
        "(x0+(4))^2-(x0^2+(8)*x0+(16))",
        "0",
        3,
        true,
        "algebraic-zero"
    },
    {
        "RING_01524",
        "(x0+(11))^2",
        "x0^2+(22)*x0+(122)",
        3,
        false,
        "false-binomial"
    },
    {
        "RING_01525",
        "(x0+(-11))*(x0-(-11))",
        "x0^2-(121)",
        3,
        true,
        "conjugates"
    },
    {
        "RING_01526",
        "(x0+x1+(x2+(7)))^2",
        "x0^2+x1^2+(x2+(7))^2+2*x0*x1+2*x0*(x2+(7))+2*x1*(x2+(7))",
        3,
        true,
        "multivariate-square"
    },
    {
        "RING_01527",
        "((x0+(3))^2)*(x1+(11))",
        "(x0^2+(6)*x0+(9))*(x1+(11))",
        3,
        true,
        "product-squared"
    },
    {
        "RING_01528",
        "(10)*x0+(-9)*x0+(6)*x0+(-11)*x0",
        "(-4)*x0",
        3,
        true,
        "coefficient-aggregation"
    },
    {
        "RING_01529",
        "(-12)*(x0+x1+x2)^2",
        "(-12)*(x0^2+x1^2+x2^2+2*x0*x1+2*x0*x2+2*x1*x2)",
        3,
        true,
        "quadratic-form"
    },
    {
        "RING_01530",
        "(x0+(-5))*(x1+(13))",
        "x0*x1+(13)*x0+(-5)*x1+(-65)",
        3,
        true,
        "distributivity"
    },
    {
        "RING_01531",
        "(x0+(2))^2",
        "x0^2+(4)*x0+(4)",
        3,
        true,
        "binomial-square"
    },
    {
        "RING_01532",
        "(x0+(9))^3",
        "x0^3+(27)*x0^2+(243)*x0+(729)",
        3,
        true,
        "binomial-cube"
    },
    {
        "RING_01533",
        "(x0+(-13))*(x1+(15))",
        "(x1+(15))*(x0+(-13))",
        3,
        true,
        "commutativity"
    },
    {
        "RING_01534",
        "(x0+x1)+(x2+(3))",
        "x0+(x1+(x2+(3)))",
        3,
        true,
        "associativity"
    },
    {
        "RING_01535",
        "x0*x2+x1*x2+(1)*x2",
        "(x0+x1+(1))*x2",
        3,
        true,
        "factorization"
    },
    {
        "RING_01536",
        "(x0+(8))*(x1+(-14))-(-14)*x0-(8)*x1-(-112)",
        "x0*x1",
        3,
        true,
        "cancellation"
    },
    {
        "RING_01537",
        "((x0+0)*(x1+1))+((x2*0)+(-14)-(-14))",
        "x0*x1+x0",
        3,
        true,
        "neutral-elements"
    },
    {
        "RING_01538",
        "x0*(x1+(-7))-(-7)*x0",
        "x0*x1",
        3,
        true,
        "distribute-cancel"
    },
    {
        "RING_01539",
        "((x0+(0))+x1)*((x0+(0))-x1)",
        "(x0+(0))^2-x1^2",
        3,
        true,
        "difference-of-squares"
    },
    {
        "RING_01540",
        "(x0+(7))^2-(x0^2+(14)*x0+(49))",
        "0",
        3,
        true,
        "algebraic-zero"
    },
    {
        "RING_01541",
        "(x0+(14))^2",
        "x0^2+(28)*x0+(197)",
        3,
        false,
        "false-binomial"
    },
    {
        "RING_01542",
        "(x0+(-8))*(x0-(-8))",
        "x0^2-(64)",
        3,
        true,
        "conjugates"
    },
    {
        "RING_01543",
        "(x0+x1+(x2+(12)))^2",
        "x0^2+x1^2+(x2+(12))^2+2*x0*x1+2*x0*(x2+(12))+2*x1*(x2+(12))",
        3,
        true,
        "multivariate-square"
    },
    {
        "RING_01544",
        "((x0+(6))^2)*(x1+(12))",
        "(x0^2+(12)*x0+(36))*(x1+(12))",
        3,
        true,
        "product-squared"
    },
    {
        "RING_01545",
        "(13)*x0+(-8)*x0+(11)*x0+(3)*x0",
        "(19)*x0",
        3,
        true,
        "coefficient-aggregation"
    },
    {
        "RING_01546",
        "(-9)*(x0+x1+x2)^2",
        "(-9)*(x0^2+x1^2+x2^2+2*x0*x1+2*x0*x2+2*x1*x2)",
        3,
        true,
        "quadratic-form"
    },
    {
        "RING_01547",
        "(x0+(-2))*(x1+(14))",
        "x0*x1+(14)*x0+(-2)*x1+(-28)",
        3,
        true,
        "distributivity"
    },
    {
        "RING_01548",
        "(x0+(5))^2",
        "x0^2+(10)*x0+(25)",
        3,
        true,
        "binomial-square"
    },
    {
        "RING_01549",
        "(x0+(12))^3",
        "x0^3+(36)*x0^2+(432)*x0+(1728)",
        3,
        true,
        "binomial-cube"
    },
    {
        "RING_01550",
        "(x0+(-10))*(x1+(-15))",
        "(x1+(-15))*(x0+(-10))",
        3,
        true,
        "commutativity"
    },
    {
        "RING_01551",
        "(x0+x1)+(x2+(8))",
        "x0+(x1+(x2+(8)))",
        3,
        true,
        "associativity"
    },
    {
        "RING_01552",
        "x0*x2+x1*x2+(4)*x2",
        "(x0+x1+(4))*x2",
        3,
        true,
        "factorization"
    },
    {
        "RING_01553",
        "(x0+(11))*(x1+(-13))-(-13)*x0-(11)*x1-(-143)",
        "x0*x1",
        3,
        true,
        "cancellation"
    },
    {
        "RING_01554",
        "((x0+0)*(x1+1))+((x2*0)+(-11)-(-11))",
        "x0*x1+x0",
        3,
        true,
        "neutral-elements"
    },
    {
        "RING_01555",
        "x0*(x1+(-4))-(-4)*x0",
        "x0*x1",
        3,
        true,
        "distribute-cancel"
    },
    {
        "RING_01556",
        "((x0+(3))+x1)*((x0+(3))-x1)",
        "(x0+(3))^2-x1^2",
        3,
        true,
        "difference-of-squares"
    },
    {
        "RING_01557",
        "(x0+(10))^2-(x0^2+(20)*x0+(100))",
        "0",
        3,
        true,
        "algebraic-zero"
    },
    {
        "RING_01558",
        "(x0+(-12))^2",
        "x0^2+(-24)*x0+(145)",
        3,
        false,
        "false-binomial"
    },
    {
        "RING_01559",
        "(x0+(-5))*(x0-(-5))",
        "x0^2-(25)",
        3,
        true,
        "conjugates"
    },
    {
        "RING_01560",
        "(x0+x1+(x2+(-10)))^2",
        "x0^2+x1^2+(x2+(-10))^2+2*x0*x1+2*x0*(x2+(-10))+2*x1*(x2+(-10))",
        3,
        true,
        "multivariate-square"
    },
    {
        "RING_01561",
        "((x0+(9))^2)*(x1+(13))",
        "(x0^2+(18)*x0+(81))*(x1+(13))",
        3,
        true,
        "product-squared"
    },
    {
        "RING_01562",
        "(-13)*x0+(-7)*x0+(-11)*x0+(-8)*x0",
        "(-39)*x0",
        3,
        true,
        "coefficient-aggregation"
    },
    {
        "RING_01563",
        "(-6)*(x0+x1+x2)^2",
        "(-6)*(x0^2+x1^2+x2^2+2*x0*x1+2*x0*x2+2*x1*x2)",
        3,
        true,
        "quadratic-form"
    },
    {
        "RING_01564",
        "(x0+(1))*(x1+(15))",
        "x0*x1+(15)*x0+(1)*x1+(15)",
        3,
        true,
        "distributivity"
    },
    {
        "RING_01565",
        "(x0+(8))^2",
        "x0^2+(16)*x0+(64)",
        3,
        true,
        "binomial-square"
    },
    {
        "RING_01566",
        "(x0+(-14))^3",
        "x0^3+(-42)*x0^2+(588)*x0+(-2744)",
        3,
        true,
        "binomial-cube"
    },
    {
        "RING_01567",
        "(x0+(-7))*(x1+(-14))",
        "(x1+(-14))*(x0+(-7))",
        3,
        true,
        "commutativity"
    },
    {
        "RING_01568",
        "(x0+x1)+(x2+(13))",
        "x0+(x1+(x2+(13)))",
        3,
        true,
        "associativity"
    },
    {
        "RING_01569",
        "x0*x2+x1*x2+(7)*x2",
        "(x0+x1+(7))*x2",
        3,
        true,
        "factorization"
    },
    {
        "RING_01570",
        "(x0+(14))*(x1+(-12))-(-12)*x0-(14)*x1-(-168)",
        "x0*x1",
        3,
        true,
        "cancellation"
    },
    {
        "RING_01571",
        "((x0+0)*(x1+1))+((x2*0)+(-8)-(-8))",
        "x0*x1+x0",
        3,
        true,
        "neutral-elements"
    },
    {
        "RING_01572",
        "x0*(x1+(-1))-(-1)*x0",
        "x0*x1",
        3,
        true,
        "distribute-cancel"
    },
    {
        "RING_01573",
        "((x0+(6))+x1)*((x0+(6))-x1)",
        "(x0+(6))^2-x1^2",
        3,
        true,
        "difference-of-squares"
    },
    {
        "RING_01574",
        "(x0+(13))^2-(x0^2+(26)*x0+(169))",
        "0",
        3,
        true,
        "algebraic-zero"
    },
    {
        "RING_01575",
        "(x0+(-9))^2",
        "x0^2+(-18)*x0+(82)",
        3,
        false,
        "false-binomial"
    },
    {
        "RING_01576",
        "(x0+(-2))*(x0-(-2))",
        "x0^2-(4)",
        3,
        true,
        "conjugates"
    },
    {
        "RING_01577",
        "(x0+x1+(x2+(-5)))^2",
        "x0^2+x1^2+(x2+(-5))^2+2*x0*x1+2*x0*(x2+(-5))+2*x1*(x2+(-5))",
        3,
        true,
        "multivariate-square"
    },
    {
        "RING_01578",
        "((x0+(12))^2)*(x1+(14))",
        "(x0^2+(24)*x0+(144))*(x1+(14))",
        3,
        true,
        "product-squared"
    },
    {
        "RING_01579",
        "(-10)*x0+(-6)*x0+(-6)*x0+(6)*x0",
        "(-16)*x0",
        3,
        true,
        "coefficient-aggregation"
    },
    {
        "RING_01580",
        "(-3)*(x0+x1+x2)^2",
        "(-3)*(x0^2+x1^2+x2^2+2*x0*x1+2*x0*x2+2*x1*x2)",
        3,
        true,
        "quadratic-form"
    },
    {
        "RING_01581",
        "(x0+(4))*(x1+(-15))",
        "x0*x1+(-15)*x0+(4)*x1+(-60)",
        3,
        true,
        "distributivity"
    },
    {
        "RING_01582",
        "(x0+(11))^2",
        "x0^2+(22)*x0+(121)",
        3,
        true,
        "binomial-square"
    },
    {
        "RING_01583",
        "(x0+(-11))^3",
        "x0^3+(-33)*x0^2+(363)*x0+(-1331)",
        3,
        true,
        "binomial-cube"
    },
    {
        "RING_01584",
        "(x0+(-4))*(x1+(-13))",
        "(x1+(-13))*(x0+(-4))",
        3,
        true,
        "commutativity"
    },
    {
        "RING_01585",
        "(x0+x1)+(x2+(-9))",
        "x0+(x1+(x2+(-9)))",
        3,
        true,
        "associativity"
    },
    {
        "RING_01586",
        "x0*x2+x1*x2+(10)*x2",
        "(x0+x1+(10))*x2",
        3,
        true,
        "factorization"
    },
    {
        "RING_01587",
        "(x0+(-12))*(x1+(-11))-(-11)*x0-(-12)*x1-(132)",
        "x0*x1",
        3,
        true,
        "cancellation"
    },
    {
        "RING_01588",
        "((x0+0)*(x1+1))+((x2*0)+(-5)-(-5))",
        "x0*x1+x0",
        3,
        true,
        "neutral-elements"
    },
    {
        "RING_01589",
        "x0*(x1+(2))-(2)*x0",
        "x0*x1",
        3,
        true,
        "distribute-cancel"
    },
    {
        "RING_01590",
        "((x0+(9))+x1)*((x0+(9))-x1)",
        "(x0+(9))^2-x1^2",
        3,
        true,
        "difference-of-squares"
    },
    {
        "RING_01591",
        "(x0+(-13))^2-(x0^2+(-26)*x0+(169))",
        "0",
        3,
        true,
        "algebraic-zero"
    },
    {
        "RING_01592",
        "(x0+(-6))^2",
        "x0^2+(-12)*x0+(37)",
        3,
        false,
        "false-binomial"
    },
    {
        "RING_01593",
        "(x0+(1))*(x0-(1))",
        "x0^2-(1)",
        3,
        true,
        "conjugates"
    },
    {
        "RING_01594",
        "(x0+x1+(x2+(0)))^2",
        "x0^2+x1^2+(x2+(0))^2+2*x0*x1+2*x0*(x2+(0))+2*x1*(x2+(0))",
        3,
        true,
        "multivariate-square"
    },
    {
        "RING_01595",
        "((x0+(-14))^2)*(x1+(15))",
        "(x0^2+(-28)*x0+(196))*(x1+(15))",
        3,
        true,
        "product-squared"
    },
    {
        "RING_01596",
        "(-7)*x0+(-5)*x0+(-1)*x0+(-5)*x0",
        "(-18)*x0",
        3,
        true,
        "coefficient-aggregation"
    },
    {
        "RING_01597",
        "(0)*(x0+x1+x2)^2",
        "(0)*(x0^2+x1^2+x2^2+2*x0*x1+2*x0*x2+2*x1*x2)",
        3,
        true,
        "quadratic-form"
    },
    {
        "RING_01598",
        "(x0+(7))*(x1+(-14))",
        "x0*x1+(-14)*x0+(7)*x1+(-98)",
        3,
        true,
        "distributivity"
    },
    {
        "RING_01599",
        "(x0+(14))^2",
        "x0^2+(28)*x0+(196)",
        3,
        true,
        "binomial-square"
    },
    {
        "RING_01600",
        "(x0+(-8))^3",
        "x0^3+(-24)*x0^2+(192)*x0+(-512)",
        3,
        true,
        "binomial-cube"
    },
    {
        "RING_01601",
        "(x0+(-1))*(x1+(-12))",
        "(x1+(-12))*(x0+(-1))",
        3,
        true,
        "commutativity"
    },
    {
        "RING_01602",
        "(x0+x1)+(x2+(-4))",
        "x0+(x1+(x2+(-4)))",
        3,
        true,
        "associativity"
    },
    {
        "RING_01603",
        "x0*x2+x1*x2+(13)*x2",
        "(x0+x1+(13))*x2",
        3,
        true,
        "factorization"
    },
    {
        "RING_01604",
        "(x0+(-9))*(x1+(-10))-(-10)*x0-(-9)*x1-(90)",
        "x0*x1",
        3,
        true,
        "cancellation"
    },
    {
        "RING_01605",
        "((x0+0)*(x1+1))+((x2*0)+(-2)-(-2))",
        "x0*x1+x0",
        3,
        true,
        "neutral-elements"
    },
    {
        "RING_01606",
        "x0*(x1+(5))-(5)*x0",
        "x0*x1",
        3,
        true,
        "distribute-cancel"
    },
    {
        "RING_01607",
        "((x0+(12))+x1)*((x0+(12))-x1)",
        "(x0+(12))^2-x1^2",
        3,
        true,
        "difference-of-squares"
    },
    {
        "RING_01608",
        "(x0+(-10))^2-(x0^2+(-20)*x0+(100))",
        "0",
        3,
        true,
        "algebraic-zero"
    },
    {
        "RING_01609",
        "(x0+(-3))^2",
        "x0^2+(-6)*x0+(10)",
        3,
        false,
        "false-binomial"
    },
    {
        "RING_01610",
        "(x0+(4))*(x0-(4))",
        "x0^2-(16)",
        3,
        true,
        "conjugates"
    },
    {
        "RING_01611",
        "(x0+x1+(x2+(5)))^2",
        "x0^2+x1^2+(x2+(5))^2+2*x0*x1+2*x0*(x2+(5))+2*x1*(x2+(5))",
        3,
        true,
        "multivariate-square"
    },
    {
        "RING_01612",
        "((x0+(-11))^2)*(x1+(-15))",
        "(x0^2+(-22)*x0+(121))*(x1+(-15))",
        3,
        true,
        "product-squared"
    },
    {
        "RING_01613",
        "(-4)*x0+(-4)*x0+(4)*x0+(9)*x0",
        "(5)*x0",
        3,
        true,
        "coefficient-aggregation"
    },
    {
        "RING_01614",
        "(3)*(x0+x1+x2)^2",
        "(3)*(x0^2+x1^2+x2^2+2*x0*x1+2*x0*x2+2*x1*x2)",
        3,
        true,
        "quadratic-form"
    },
    {
        "RING_01615",
        "(x0+(10))*(x1+(-13))",
        "x0*x1+(-13)*x0+(10)*x1+(-130)",
        3,
        true,
        "distributivity"
    },
    {
        "RING_01616",
        "(x0+(-12))^2",
        "x0^2+(-24)*x0+(144)",
        3,
        true,
        "binomial-square"
    },
    {
        "RING_01617",
        "(x0+(-5))^3",
        "x0^3+(-15)*x0^2+(75)*x0+(-125)",
        3,
        true,
        "binomial-cube"
    },
    {
        "RING_01618",
        "(x0+(2))*(x1+(-11))",
        "(x1+(-11))*(x0+(2))",
        3,
        true,
        "commutativity"
    },
    {
        "RING_01619",
        "(x0+x1)+(x2+(1))",
        "x0+(x1+(x2+(1)))",
        3,
        true,
        "associativity"
    },
    {
        "RING_01620",
        "x0*x2+x1*x2+(-13)*x2",
        "(x0+x1+(-13))*x2",
        3,
        true,
        "factorization"
    },
    {
        "RING_01621",
        "(x0+(-6))*(x1+(-9))-(-9)*x0-(-6)*x1-(54)",
        "x0*x1",
        3,
        true,
        "cancellation"
    },
    {
        "RING_01622",
        "((x0+0)*(x1+1))+((x2*0)+(1)-(1))",
        "x0*x1+x0",
        3,
        true,
        "neutral-elements"
    },
    {
        "RING_01623",
        "x0*(x1+(8))-(8)*x0",
        "x0*x1",
        3,
        true,
        "distribute-cancel"
    },
    {
        "RING_01624",
        "((x0+(-14))+x1)*((x0+(-14))-x1)",
        "(x0+(-14))^2-x1^2",
        3,
        true,
        "difference-of-squares"
    },
    {
        "RING_01625",
        "(x0+(-7))^2-(x0^2+(-14)*x0+(49))",
        "0",
        3,
        true,
        "algebraic-zero"
    },
    {
        "RING_01626",
        "(x0+(0))^2",
        "x0^2+(0)*x0+(1)",
        3,
        false,
        "false-binomial"
    },
    {
        "RING_01627",
        "(x0+(7))*(x0-(7))",
        "x0^2-(49)",
        3,
        true,
        "conjugates"
    },
    {
        "RING_01628",
        "(x0+x1+(x2+(10)))^2",
        "x0^2+x1^2+(x2+(10))^2+2*x0*x1+2*x0*(x2+(10))+2*x1*(x2+(10))",
        3,
        true,
        "multivariate-square"
    },
    {
        "RING_01629",
        "((x0+(-8))^2)*(x1+(-14))",
        "(x0^2+(-16)*x0+(64))*(x1+(-14))",
        3,
        true,
        "product-squared"
    },
    {
        "RING_01630",
        "(-1)*x0+(-3)*x0+(9)*x0+(-2)*x0",
        "(3)*x0",
        3,
        true,
        "coefficient-aggregation"
    },
    {
        "RING_01631",
        "(6)*(x0+x1+x2)^2",
        "(6)*(x0^2+x1^2+x2^2+2*x0*x1+2*x0*x2+2*x1*x2)",
        3,
        true,
        "quadratic-form"
    },
    {
        "RING_01632",
        "(x0+(13))*(x1+(-12))",
        "x0*x1+(-12)*x0+(13)*x1+(-156)",
        3,
        true,
        "distributivity"
    },
    {
        "RING_01633",
        "(x0+(-9))^2",
        "x0^2+(-18)*x0+(81)",
        3,
        true,
        "binomial-square"
    },
    {
        "RING_01634",
        "(x0+(-2))^3",
        "x0^3+(-6)*x0^2+(12)*x0+(-8)",
        3,
        true,
        "binomial-cube"
    },
    {
        "RING_01635",
        "(x0+(5))*(x1+(-10))",
        "(x1+(-10))*(x0+(5))",
        3,
        true,
        "commutativity"
    },
    {
        "RING_01636",
        "(x0+x1)+(x2+(6))",
        "x0+(x1+(x2+(6)))",
        3,
        true,
        "associativity"
    },
    {
        "RING_01637",
        "x0*x2+x1*x2+(-10)*x2",
        "(x0+x1+(-10))*x2",
        3,
        true,
        "factorization"
    },
    {
        "RING_01638",
        "(x0+(-3))*(x1+(-8))-(-8)*x0-(-3)*x1-(24)",
        "x0*x1",
        3,
        true,
        "cancellation"
    },
    {
        "RING_01639",
        "((x0+0)*(x1+1))+((x2*0)+(4)-(4))",
        "x0*x1+x0",
        3,
        true,
        "neutral-elements"
    },
    {
        "RING_01640",
        "x0*(x1+(11))-(11)*x0",
        "x0*x1",
        3,
        true,
        "distribute-cancel"
    },
    {
        "RING_01641",
        "((x0+(-11))+x1)*((x0+(-11))-x1)",
        "(x0+(-11))^2-x1^2",
        3,
        true,
        "difference-of-squares"
    },
    {
        "RING_01642",
        "(x0+(-4))^2-(x0^2+(-8)*x0+(16))",
        "0",
        3,
        true,
        "algebraic-zero"
    },
    {
        "RING_01643",
        "(x0+(3))^2",
        "x0^2+(6)*x0+(10)",
        3,
        false,
        "false-binomial"
    },
    {
        "RING_01644",
        "(x0+(10))*(x0-(10))",
        "x0^2-(100)",
        3,
        true,
        "conjugates"
    },
    {
        "RING_01645",
        "(x0+x1+(x2+(-12)))^2",
        "x0^2+x1^2+(x2+(-12))^2+2*x0*x1+2*x0*(x2+(-12))+2*x1*(x2+(-12))",
        3,
        true,
        "multivariate-square"
    },
    {
        "RING_01646",
        "((x0+(-5))^2)*(x1+(-13))",
        "(x0^2+(-10)*x0+(25))*(x1+(-13))",
        3,
        true,
        "product-squared"
    },
    {
        "RING_01647",
        "(2)*x0+(-2)*x0+(-13)*x0+(12)*x0",
        "(-1)*x0",
        3,
        true,
        "coefficient-aggregation"
    },
    {
        "RING_01648",
        "(9)*(x0+x1+x2)^2",
        "(9)*(x0^2+x1^2+x2^2+2*x0*x1+2*x0*x2+2*x1*x2)",
        3,
        true,
        "quadratic-form"
    },
    {
        "RING_01649",
        "(x0+(-13))*(x1+(-11))",
        "x0*x1+(-11)*x0+(-13)*x1+(143)",
        3,
        true,
        "distributivity"
    },
    {
        "RING_01650",
        "(x0+(-6))^2",
        "x0^2+(-12)*x0+(36)",
        3,
        true,
        "binomial-square"
    },
    {
        "RING_01651",
        "(x0+(1))^3",
        "x0^3+(3)*x0^2+(3)*x0+(1)",
        3,
        true,
        "binomial-cube"
    },
    {
        "RING_01652",
        "(x0+(8))*(x1+(-9))",
        "(x1+(-9))*(x0+(8))",
        3,
        true,
        "commutativity"
    },
    {
        "RING_01653",
        "(x0+x1)+(x2+(11))",
        "x0+(x1+(x2+(11)))",
        3,
        true,
        "associativity"
    },
    {
        "RING_01654",
        "x0*x2+x1*x2+(-7)*x2",
        "(x0+x1+(-7))*x2",
        3,
        true,
        "factorization"
    },
    {
        "RING_01655",
        "(x0+(0))*(x1+(-7))-(-7)*x0-(0)*x1-(0)",
        "x0*x1",
        3,
        true,
        "cancellation"
    },
    {
        "RING_01656",
        "((x0+0)*(x1+1))+((x2*0)+(7)-(7))",
        "x0*x1+x0",
        3,
        true,
        "neutral-elements"
    },
    {
        "RING_01657",
        "x0*(x1+(14))-(14)*x0",
        "x0*x1",
        3,
        true,
        "distribute-cancel"
    },
    {
        "RING_01658",
        "((x0+(-8))+x1)*((x0+(-8))-x1)",
        "(x0+(-8))^2-x1^2",
        3,
        true,
        "difference-of-squares"
    },
    {
        "RING_01659",
        "(x0+(-1))^2-(x0^2+(-2)*x0+(1))",
        "0",
        3,
        true,
        "algebraic-zero"
    },
    {
        "RING_01660",
        "(x0+(6))^2",
        "x0^2+(12)*x0+(37)",
        3,
        false,
        "false-binomial"
    },
    {
        "RING_01661",
        "(x0+(13))*(x0-(13))",
        "x0^2-(169)",
        3,
        true,
        "conjugates"
    },
    {
        "RING_01662",
        "(x0+x1+(x2+(-7)))^2",
        "x0^2+x1^2+(x2+(-7))^2+2*x0*x1+2*x0*(x2+(-7))+2*x1*(x2+(-7))",
        3,
        true,
        "multivariate-square"
    },
    {
        "RING_01663",
        "((x0+(-2))^2)*(x1+(-12))",
        "(x0^2+(-4)*x0+(4))*(x1+(-12))",
        3,
        true,
        "product-squared"
    },
    {
        "RING_01664",
        "(5)*x0+(-1)*x0+(-8)*x0+(1)*x0",
        "(-3)*x0",
        3,
        true,
        "coefficient-aggregation"
    },
    {
        "RING_01665",
        "(12)*(x0+x1+x2)^2",
        "(12)*(x0^2+x1^2+x2^2+2*x0*x1+2*x0*x2+2*x1*x2)",
        3,
        true,
        "quadratic-form"
    },
    {
        "RING_01666",
        "(x0+(-10))*(x1+(-10))",
        "x0*x1+(-10)*x0+(-10)*x1+(100)",
        3,
        true,
        "distributivity"
    },
    {
        "RING_01667",
        "(x0+(-3))^2",
        "x0^2+(-6)*x0+(9)",
        3,
        true,
        "binomial-square"
    },
    {
        "RING_01668",
        "(x0+(4))^3",
        "x0^3+(12)*x0^2+(48)*x0+(64)",
        3,
        true,
        "binomial-cube"
    },
    {
        "RING_01669",
        "(x0+(11))*(x1+(-8))",
        "(x1+(-8))*(x0+(11))",
        3,
        true,
        "commutativity"
    },
    {
        "RING_01670",
        "(x0+x1)+(x2+(-11))",
        "x0+(x1+(x2+(-11)))",
        3,
        true,
        "associativity"
    },
    {
        "RING_01671",
        "x0*x2+x1*x2+(-4)*x2",
        "(x0+x1+(-4))*x2",
        3,
        true,
        "factorization"
    },
    {
        "RING_01672",
        "(x0+(3))*(x1+(-6))-(-6)*x0-(3)*x1-(-18)",
        "x0*x1",
        3,
        true,
        "cancellation"
    },
    {
        "RING_01673",
        "((x0+0)*(x1+1))+((x2*0)+(10)-(10))",
        "x0*x1+x0",
        3,
        true,
        "neutral-elements"
    },
    {
        "RING_01674",
        "x0*(x1+(-12))-(-12)*x0",
        "x0*x1",
        3,
        true,
        "distribute-cancel"
    },
    {
        "RING_01675",
        "((x0+(-5))+x1)*((x0+(-5))-x1)",
        "(x0+(-5))^2-x1^2",
        3,
        true,
        "difference-of-squares"
    },
    {
        "RING_01676",
        "(x0+(2))^2-(x0^2+(4)*x0+(4))",
        "0",
        3,
        true,
        "algebraic-zero"
    },
    {
        "RING_01677",
        "(x0+(9))^2",
        "x0^2+(18)*x0+(82)",
        3,
        false,
        "false-binomial"
    },
    {
        "RING_01678",
        "(x0+(-13))*(x0-(-13))",
        "x0^2-(169)",
        3,
        true,
        "conjugates"
    },
    {
        "RING_01679",
        "(x0+x1+(x2+(-2)))^2",
        "x0^2+x1^2+(x2+(-2))^2+2*x0*x1+2*x0*(x2+(-2))+2*x1*(x2+(-2))",
        3,
        true,
        "multivariate-square"
    },
    {
        "RING_01680",
        "((x0+(1))^2)*(x1+(-11))",
        "(x0^2+(2)*x0+(1))*(x1+(-11))",
        3,
        true,
        "product-squared"
    },
    {
        "RING_01681",
        "(8)*x0+(0)*x0+(-3)*x0+(-10)*x0",
        "(-5)*x0",
        3,
        true,
        "coefficient-aggregation"
    },
    {
        "RING_01682",
        "(-14)*(x0+x1+x2)^2",
        "(-14)*(x0^2+x1^2+x2^2+2*x0*x1+2*x0*x2+2*x1*x2)",
        3,
        true,
        "quadratic-form"
    },
    {
        "RING_01683",
        "(x0+(-7))*(x1+(-9))",
        "x0*x1+(-9)*x0+(-7)*x1+(63)",
        3,
        true,
        "distributivity"
    },
    {
        "RING_01684",
        "(x0+(0))^2",
        "x0^2+(0)*x0+(0)",
        3,
        true,
        "binomial-square"
    },
    {
        "RING_01685",
        "(x0+(7))^3",
        "x0^3+(21)*x0^2+(147)*x0+(343)",
        3,
        true,
        "binomial-cube"
    },
    {
        "RING_01686",
        "(x0+(14))*(x1+(-7))",
        "(x1+(-7))*(x0+(14))",
        3,
        true,
        "commutativity"
    },
    {
        "RING_01687",
        "(x0+x1)+(x2+(-6))",
        "x0+(x1+(x2+(-6)))",
        3,
        true,
        "associativity"
    },
    {
        "RING_01688",
        "x0*x2+x1*x2+(-1)*x2",
        "(x0+x1+(-1))*x2",
        3,
        true,
        "factorization"
    },
    {
        "RING_01689",
        "(x0+(6))*(x1+(-5))-(-5)*x0-(6)*x1-(-30)",
        "x0*x1",
        3,
        true,
        "cancellation"
    },
    {
        "RING_01690",
        "((x0+0)*(x1+1))+((x2*0)+(13)-(13))",
        "x0*x1+x0",
        3,
        true,
        "neutral-elements"
    },
    {
        "RING_01691",
        "x0*(x1+(-9))-(-9)*x0",
        "x0*x1",
        3,
        true,
        "distribute-cancel"
    },
    {
        "RING_01692",
        "((x0+(-2))+x1)*((x0+(-2))-x1)",
        "(x0+(-2))^2-x1^2",
        3,
        true,
        "difference-of-squares"
    },
    {
        "RING_01693",
        "(x0+(5))^2-(x0^2+(10)*x0+(25))",
        "0",
        3,
        true,
        "algebraic-zero"
    },
    {
        "RING_01694",
        "(x0+(12))^2",
        "x0^2+(24)*x0+(145)",
        3,
        false,
        "false-binomial"
    },
    {
        "RING_01695",
        "(x0+(-10))*(x0-(-10))",
        "x0^2-(100)",
        3,
        true,
        "conjugates"
    },
    {
        "RING_01696",
        "(x0+x1+(x2+(3)))^2",
        "x0^2+x1^2+(x2+(3))^2+2*x0*x1+2*x0*(x2+(3))+2*x1*(x2+(3))",
        3,
        true,
        "multivariate-square"
    },
    {
        "RING_01697",
        "((x0+(4))^2)*(x1+(-10))",
        "(x0^2+(8)*x0+(16))*(x1+(-10))",
        3,
        true,
        "product-squared"
    },
    {
        "RING_01698",
        "(11)*x0+(1)*x0+(2)*x0+(4)*x0",
        "(18)*x0",
        3,
        true,
        "coefficient-aggregation"
    },
    {
        "RING_01699",
        "(-11)*(x0+x1+x2)^2",
        "(-11)*(x0^2+x1^2+x2^2+2*x0*x1+2*x0*x2+2*x1*x2)",
        3,
        true,
        "quadratic-form"
    },
};
static size_t run_symbolic_regression_catalog(TestRunner& tests,bool verbose=false){
    ExpressionGraph graph;TrustedKernel kernel;
    size_t rejected=0,proven=0;
    for(const auto& entry:kRegressionCatalog){
        std::string label=std::string(entry.family)+":"+entry.id;
        try {
            int32_t a=AlgebraParser(graph,entry.lhs,entry.variables).parse();
            int32_t b=AlgebraParser(graph,entry.rhs,entry.variables).parse();
            Polynomial lhs=graph.polynomial(a,entry.variables);
            Polynomial rhs=graph.polynomial(b,entry.variables);
            int32_t left=kernel.polynomial(lhs),right=kernel.polynomial(rhs);
            int32_t proposition=kernel.ring_identity(left,right);
            bool theorem_valid=false;
            try{kernel.check(kernel.ring_witness(),proposition);theorem_valid=true;}
            catch(const std::exception&){theorem_valid=false;}
            tests.check(theorem_valid==entry.universally_equal,label);
            if(theorem_valid)++proven;else ++rejected;
        }catch(const std::exception& e){
            if(verbose)std::cerr<<"[CATALOG ERROR] "<<label<<" "<<e.what()<<"\n";
            tests.check(false,label+" parser or algebra error");
        }
    }
    if(verbose)std::cerr<<"[CATALOG] total="<<(sizeof(kRegressionCatalog)/sizeof(kRegressionCatalog[0]))
                         <<" proven="<<proven<<" rejected="<<rejected<<"\n";
    return proven;
}
static int run_self_test(bool all){
    TestRunner tests;
    test_blake(tests);
    test_polynomials(tests);
    test_linear_algebra(tests);
    test_trusted_kernel(tests);
    test_noether(tests);
    test_ast_and_mcts(tests);
    test_knowledge(tests);
    test_sensor(tests);
    test_certificate_replay(tests);
    if(all)test_clang_graph(tests);
    tests.section("explicit symbolic theorem regression catalog");
    run_symbolic_regression_catalog(tests,true);
    return tests.result();
}
// ======================================================================
// INTEGRATED EPISTEMIC ENGINE AND COMMAND LINE
// State lives across JIT function hot swaps. Source AST introspection is
// separate from symbolic proof checking and cannot silently extend trust.
// ======================================================================
class GodelEngine {
    TrustedKernel kernel_;
    ExpressionGraph expression_;
    std::unique_ptr<GraphNeuralNetwork> intuition_;
    KnowledgeTree knowledge_;
    NativeHotSwap hot_swap_;
    std::string knowledge_path_="godel.knowledge.bt";
    std::string lean_output_="LeanML/Generated";
    uint64_t generation_=0;
public:
    void lean_output(std::string path){lean_output_=std::move(path);}
    void knowledge_path(std::string path){require(path.size()<PATH_MAX,"knowledge path too long");knowledge_path_=std::move(path);}
    void restore(){
        if(knowledge_.load(knowledge_path_)){
            auto certified=revalidate_archive(knowledge_,kernel_);
            std::cout<<"[MEMORY] stored="<<knowledge_.size()<<" independently revalidated="<<certified.size()<<"\n";
            if(certified.size()!=knowledge_.size())
                std::cerr<<"[MEMORY] WARNING: uncertified or malformed records are ignored\n";
        }
    }
    bool persist(){return knowledge_.save(knowledge_path_);}
    void store(const ProofCertificate& cert,const std::string& category){
        require(cert.verified,"cannot store failed theorem");
        if(category=="ast-improvement")std::cout<<"[LEAN] "<<export_ast_certificate(cert,lean_output_)<<" (pending kernel check)\n";
        KnowledgeRecord record=record_from_certificate(cert,category,generation_);
        if(!knowledge_.find(record.hash))knowledge_.insert(std::move(record));
    }
    void discover(size_t pairs=1,unsigned degree=4){
        require(pairs>=1&&pairs<=4,"discovery dimensions 1..4");
        Polynomial H(2*pairs);
        for(size_t i=0;i<pairs;++i){
            auto q=Polynomial::variable(2*pairs,i);
            auto p=Polynomial::variable(2*pairs,pairs+i);
            H=H+(q*q+p*p)*Q(1,2);
        }
        discover_hamiltonian(H,degree);
    }
    void discover_hamiltonian(const Polynomial& H,unsigned degree){
        std::cout<<"[PHYSICS] H="<<polynomial_nice(H)<<"\n";
        auto hits=discover_polynomial_invariants(H,degree,128);
        for(auto& h:hits){
            auto cert=certify_noether(kernel_,h.invariant,H);
            store(cert,"noether");
            std::cout<<"[NOETHER] Q="<<polynomial_nice(h.invariant)<<"\n"
                     <<"          {Q,H}=0  proof="<<cert.proof_hash.substr(0,24)<<"...\n";
        }
        std::cout<<"[PHYSICS] certified invariants="<<hits.size()<<"\n";
        if(!persist())std::cerr<<"[WARNING] knowledge persistence failed\n";
    }
    void discover_csv(const std::string& filename,size_t pairs,unsigned degree){
        auto observations=read_sensor_csv(filename,pairs);
        auto H=infer_quadratic_hamiltonian(observations,pairs);
        require(H.has_value(),"inconsistent data: no exact quadratic Hamiltonian fits all samples");
        std::cout<<"[SENSOR] exact samples="<<observations.size()<<"\n";
        discover_hamiltonian(H->to_polynomial(),degree);
    }
    void evolve(unsigned generations){
        require(generations<=kMaxSearchIterations,"generation limit");
        // The source expression is deliberately redundant. Search operates
        // on a compositional AST and never confuses finite tests with proof.
        int32_t x=expression_.variable(0),y=expression_.variable(1);
        int32_t source=expression_.add(
            expression_.multiply(expression_.add(x,expression_.constant(0)),
                expression_.add(y,expression_.constant(1))),
            expression_.add(expression_.multiply(expression_.constant(0),x),
                            expression_.add(expression_.constant(0),expression_.constant(0))));
        expression_.protect(source);
        std::cout<<"[MCTS] initial="<<expression_.repr(source)<<"\n"
                 <<"       static_cost="<<expression_.static_cost(source)<<"\n";
        if(!intuition_)intuition_=std::make_unique<GraphNeuralNetwork>();
        auto result=mcts_optimize(expression_,*intuition_,kernel_,source,2,generations);
        generation_+=result.simulations;
        std::cout<<"[MCTS] evaluations="<<result.simulations
                 <<" unique_states="<<result.proposals
                 <<" certified_improvements="<<result.verified<<"\n"
                 <<"       optimized="<<result.best_expression<<"\n"
                 <<"       cost="<<result.start_cost<<" -> "<<result.best_cost<<"\n";
        if(result.certificate){
            store(*result.certificate,"ast-improvement");
            std::cout<<"[PROOF] "<<result.certificate->domain<<"\n"
                     <<"        BLAKE3="<<result.certificate->proof_hash<<"\n";
            expression_.protect(result.best_root);
        }
        if(!persist())std::cerr<<"[WARNING] knowledge persistence failed\n";
        std::cout<<"[GNN] online_updates="<<intuition_->updates()<<"\n";
    }
    bool hot_swap(unsigned variant){
        std::string diagnostic;
        if(!hot_swap_.activate(variant,diagnostic)){
            std::cerr<<"[JIT] failure: "<<diagnostic<<"\n";return false;
        }
        std::cout<<"[JIT] clang++ compiled .so, dlopen + dlsym switched active kernel\n"
                 <<"      source_BLAKE3="<<hot_swap_.digest()<<"\n"
                 <<"      (native code empirically validated, not formally proved)\n";
        return true;
    }
    void inspect(const std::string& filename,const std::string& filter){
        std::string source=read_file(filename);
        std::cout<<"[SELF] bytes="<<source.size()<<" BLAKE3="<<blake3::hex(source)<<"\n";
        SourceGraph g=inspect_cpp_file(filename,filter);
        std::cout<<"[CLANG AST] nodes="<<g.nodes.size()<<" functions="<<g.functions
                 <<" methods="<<g.methods<<" templates="<<g.templates<<"\n"
                 <<"            representation="<<g.digest<<"\n";
        size_t shown=0;for(auto& n:g.nodes)if(n.kind=="FunctionDecl"&&shown++<12)
            std::cout<<"            "<<n.raw.substr(0,160)<<"\n";
    }
    size_t knowledge_size()const{return knowledge_.size();}
};
static void print_help(const char* name){
    std::cout<<"GODEL RESEARCH ENGINE / C++17 / GMP / symbolic dependent proofs\n"
     <<"Build: g++ -std=c++17 -O2 godel.cpp -lgmpxx -lgmp -ldl -o godel\n"
     <<"Usage: "<<name<<" [--knowledge path] command\n"
     <<"  --self-test              Fast self-tests + universal symbolic theorem catalog\n"
     <<"  --self-test-all          Also test live Clang / dlopen hot swapping\n"
     <<"  --discover [pairs] [d]  Discover polynomial Noether invariants\n"
     <<"  --infer-csv path n [d]   Fit rational quadratic Hamiltonian to q,p,dq,dp CSV\n"
     <<"  --certify n before after Exact DSL equivalence + automatic Lean export\n"
     <<"  --optimize n expr steps  Local GNN proposals with exact verification\n"
     <<"  --ipc-optimize /name n expr timeout-ms  External shared-memory proposals\n"
     <<"  --lean-out directory     Generated Lean/JSON directory (default LeanML/Generated)\n"
     <<"  --evolve N               GNN-guided MCTS / typed AST rewrite certificates\n"
     <<"  --hot-swap [variant]     Compile, validate and load native matrix kernel\n"
     <<"  --inspect-self path [f] Clang native C++ AST dump and graph\n"
     <<"  --emit-ir src dest       Ask Clang for LLVM IR (.ll)\n"
     <<"  --catalog                Independently validate regression theorems\n"
     <<"  --help                   This text\n"
     <<"NOTES: Native JIT and full C++ AST are not covered by the type checker.\n"
     <<"       The kernel checks a small calculus and exact polynomial identities,\n"
     <<"       not full CIC, LLVM ORC verification, or arbitrary C++ equivalence.\n";
}
} // namespace godel

int main(int argc,char** argv){
    using namespace godel;
    try{
        if(argc<2){print_help(argv[0]);return 0;}
        std::vector<std::string> args;
        for(int i=1;i<argc;++i)args.emplace_back(argv[i]);
        GodelEngine engine;
        std::string lean_output="LeanML/Generated";
        for(size_t i=0;i<args.size();){
            if(args[i]=="--lean-out"){
                require(i+1<args.size(),"missing --lean-out directory");
                lean_output=args[i+1];engine.lean_output(lean_output);
                args.erase(args.begin()+i,args.begin()+i+2);
            }else if(args[i]=="--knowledge"){
                require(i+1<args.size(),"missing --knowledge path");
                engine.knowledge_path(args[i+1]);
                args.erase(args.begin()+i,args.begin()+i+2);
            }else ++i;
        }
        if(args.empty()){print_help(argv[0]);return 0;}
        auto cmd=args[0];
        if(cmd=="--self-test")return run_self_test(false);
        if(cmd=="--self-test-all")return run_self_test(true);
        if(cmd=="--catalog"){
            TestRunner test;run_symbolic_regression_catalog(test,true);return test.result();
        }
        if(cmd=="--help"||cmd=="-h"){print_help(argv[0]);return 0;}
        if(cmd=="--inspect-self"){
            require(args.size()>1,"--inspect-self requires source path");
            engine.inspect(args[1],args.size()>2?args[2]:"godel::");return 0;
        }
        if(cmd=="--emit-ir"){
            require(args.size()>2,"--emit-ir requires source and output paths");
            std::cout<<"[LLVM] "<<emit_llvm_ir(args[1],args[2])<<"\n";return 0;
        }
        if(cmd=="--hot-swap"){
            unsigned variant=args.size()>1?parse_u32(args[1]):1;
            return engine.hot_swap(variant)?0:1;
        }
        if(cmd=="--certify"){
            require(args.size()==4,"--certify requires variables, before, after");
            size_t vars=parse_u32(args[1]);ExpressionGraph graph;TrustedKernel kernel;
            auto a=AlgebraParser(graph,args[2],vars).parse(),b=AlgebraParser(graph,args[3],vars).parse();
            auto cert=certify_graph_improvement(kernel,graph,a,b,vars);
            std::cout<<export_lean(kernel,graph,a,b,vars,cert,lean_output)<<"\n";return 0;
        }
        if(cmd=="--optimize"){
            require(args.size()==4,"--optimize requires variables, program, iterations");
            size_t vars=parse_u32(args[1]);ExpressionGraph graph;TrustedKernel kernel;GraphNeuralNetwork planner;
            auto root=AlgebraParser(graph,args[2],vars).parse();
            auto report=mcts_optimize(graph,planner,kernel,root,vars,parse_u32(args[3]));
            require(report.certificate.has_value(),"no strict improvement found within search budget");
            std::cout<<export_lean(kernel,graph,root,report.best_root,vars,*report.certificate,lean_output)<<"\n";return 0;
        }
        if(cmd=="--ipc-optimize"){
            require(args.size()==5,"--ipc-optimize requires shm-name, variables, source, timeout-ms");
            return ipc_optimize(args[1],parse_u32(args[2]),args[3],parse_u32(args[4]),lean_output);
        }
        engine.restore();
        if(cmd=="--evolve"){
            unsigned count=args.size()>1?parse_u32(args[1]):200;
            engine.evolve(count);return 0;
        }
        if(cmd=="--discover"){
            size_t pairs=args.size()>1?parse_u32(args[1]):1;
            unsigned degree=args.size()>2?parse_u32(args[2]):4;
            engine.discover(pairs,degree);return 0;
        }
        if(cmd=="--infer-csv"){
            require(args.size()>2,"--infer-csv requires path and number of pairs");
            engine.discover_csv(args[1],parse_u32(args[2]),args.size()>3?parse_u32(args[3]):4);
            return 0;
        }
        std::cerr<<"Unknown command: "<<cmd<<"\n";print_help(argv[0]);return 2;
    }catch(const std::exception& e){std::cerr<<"[ERROR] "<<e.what()<<"\n";return 1;}
}
