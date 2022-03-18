#include <iostream>
#include <cmath>
#include <cstdint>
#include <cfenv>
#include <cassert>
#include <vector>
#include <deque>

#include <boost/algorithm/string.hpp>
#include <iomanip>

extern "C" {
  #include "../gencode/test_avx512f_ops.h"
}

static_assert(sizeof(uint32_t) == sizeof(float),"float size");
static_assert(sizeof(uint64_t) == sizeof(double),"double size");


using namespace std;

[[noreturn]] void error(std::string msg) {
  std::cerr<<msg<<std::endl;
  exit(1);
}

template< typename T >
std::string int_to_hex( T i )
{
  std::stringstream stream;
  stream << "0x"
         << std::setfill ('0') << std::setw(sizeof(T)*2)
         << std::hex << i;
  return stream.str();
}

string to_hex(float x) {
  return int_to_hex(*(uint32_t*)&x);
}

string to_hex(double x) {
  return int_to_hex(*(uint64_t*)&x);
}


float stof32(string s) {
  assert(s.size()==10);
  uint64_t x = stoul(s,0,16);
  assert(x<=UINT32_MAX);
  uint32_t xx = x;
  return *(float*)&xx;
}

double stof64(string s) {
  assert(s.size()==18);
  uint64_t x = stoul(s,0,16);
  return *(double*)&x;
}

string popc(deque<string> &v) {
  if (!v.size()) error("Too few operands");
  string res=v.front();
  v.pop_front();
  return res;
}

float rd32(deque<string> &v) {
  return stof32(popc(v));
}

float rd32o(deque<string> &v) {
  if (!v.size()) return 0;
  return rd32(v);
}

double rd64(deque<string> &v) {
  return stof64(popc(v));
}

double rd64o(deque<string> &v) {
  if (!v.size()) return 0;
  return rd64(v);
}

const uint64_t TO_NEAREST = 0;
const uint64_t TO_PINF = 1;
const uint64_t TO_NINF = 2;
const uint64_t TO_ZERO = 3;

uint64_t rdrm(deque<string> &v) {
  string rm = popc(v);
  if (rm == "=0") return TO_NEAREST;
  else if (rm == ">") return TO_PINF;
  else if (rm == "<") return TO_NINF;
  else if (rm == "0") return TO_ZERO;
  else error("rounding mode " + rm);
}

inline void setrm(uint64_t rm) {
  if (rm == TO_NEAREST) std::fesetround(FE_TONEAREST);
  else if (rm == TO_PINF) std::fesetround(FE_UPWARD);
  else if (rm == TO_NINF) std::fesetround(FE_DOWNWARD);
  else if (rm == TO_ZERO) std::fesetround(FE_TOWARDZERO);
  else error("roundmode enc/dec");
}

string current_op;


enum output_mode {
  OUT_REGRESSION, // fail on any mismatches
  OUT_GOOD,       // only echo non-failing triples
  OUT_BAD,        // only echo failing triples
  OUT_FIX         // echo all triples, fix mismatches
};

output_mode output_mode = OUT_REGRESSION;
bool output_dbg=false;


bool fpeq(float a, float b) {
  if (isnan(a) && isnan(b)) return true;
  return ((*(uint32_t*)&a) == (*(uint32_t*)&b));
}

bool fpeq(double a, double b) {
  if (isnan(a) && isnan(b)) return true;
  return ((*(uint64_t*)&a) == (*(uint64_t*)&b));
}

void test(string s) {
  deque<string> fs;
  boost::trim(s);
  boost::split(fs, s, [](char c){return c == ' ';});

  vector<string> orig_fs(fs.begin(),fs.end());


  current_op=s;

  auto ty = popc(fs);
  auto fun = popc(fs);
  auto rm = rdrm(fs);

  size_t n = fs.size();


  bool match_c_res=false;   // C result matches default
  bool match_isa_res=false; // Isa result matches default
  bool match_c_isa=false; // Isa and C results match

  string cres_str;


  if (ty=="b32") {
    float a=rd32o(fs);
    float b=rd32o(fs);
    float c=rd32o(fs);
    float d=rd32o(fs);

    float cres=0;
    float isares=0;
    float res=0;

    { // Execute with C

      setrm(rm);

           if (fun=="+") {assert(n==3);  cres = a+b; res=c; }
      else if (fun=="-") {assert(n==3);  cres = a-b; res=c; }
      else if (fun=="*") {assert(n==3);  cres = a*b; res=c; }
      else if (fun=="/") {assert(n==3);  cres = a/b; res=c; }
      else if (fun=="V") {assert(n==2);  cres = sqrtf(a); res=b; }
      else if (fun=="*+") {assert(n==4); cres = std::fmaf(a,b,c); res=d; }
      else error("Unknown op");

      match_c_res = fpeq(cres, res);
    }

    { // Test Isabelle-LLVM generated AVX512f

           if (fun=="+")  {assert(n==3);  isares = avx512_32_add(rm,a,b); }
      else if (fun=="-")  {assert(n==3);  isares = avx512_32_sub(rm,a,b); }
      else if (fun=="*")  {assert(n==3);  isares = avx512_32_mul(rm,a,b); }
      else if (fun=="/")  {assert(n==3);  isares = avx512_32_div(rm,a,b); }
      else if (fun=="V")  {assert(n==2);  isares = avx512_32_sqrt(rm,a); }
      else if (fun=="*+") {assert(n==4); isares = avx512_32_fmadd(rm,a,b,c); }
      else error("Unknown op");

      match_isa_res = fpeq(isares, res);
    }

    cres_str = to_hex(cres);


    match_c_isa = fpeq(cres,isares);

    if (!match_c_isa && !match_c_res && !match_isa_res && output_dbg) {
      cerr<<endl;
      cerr<<"DBG: "<<current_op<<endl;
      cerr<<"DBG: "<<hexfloat<<a<<" "<<b<<" "<<c<<" "<<d<<" "<<endl;
      cerr<<"DBG: res = "<<res<<endl;
      cerr<<"DBG: c   = "<<cres<<endl;
      cerr<<"DBG: isa = "<<isares<<endl;
      cerr<<"DBG: Mismatch"<<endl;
    }

  }
  else
  if (ty=="b64") {
    double a=rd64o(fs);
    double b=rd64o(fs);
    double c=rd64o(fs);
    double d=rd64o(fs);

    double cres=0;
    double isares=0;
    double res=0;

    { // Execute with C

      setrm(rm);

           if (fun=="+") {assert(n==3);  cres = a+b; res=c; }
      else if (fun=="-") {assert(n==3);  cres = a-b; res=c; }
      else if (fun=="*") {assert(n==3);  cres = a*b; res=c; }
      else if (fun=="/") {assert(n==3);  cres = a/b; res=c; }
      else if (fun=="V") {assert(n==2);  cres = sqrt(a); res=b; }
      else if (fun=="*+") {assert(n==4); cres = std::fma(a,b,c); res=d; }
      else error("Unknown op");

      match_c_res = fpeq(cres, res);
    }

    { // Test Isabelle-LLVM generated AVX512f

           if (fun=="+")  {assert(n==3);  isares = avx512_64_add(rm,a,b); }
      else if (fun=="-")  {assert(n==3);  isares = avx512_64_sub(rm,a,b); }
      else if (fun=="*")  {assert(n==3);  isares = avx512_64_mul(rm,a,b); }
      else if (fun=="/")  {assert(n==3);  isares = avx512_64_div(rm,a,b); }
      else if (fun=="V")  {assert(n==2);  isares = avx512_64_sqrt(rm,a); }
      else if (fun=="*+") {assert(n==4); isares = avx512_64_fmadd(rm,a,b,c); }
      else error("Unknown op");

      match_isa_res = fpeq(isares, res);
    }

    match_c_isa = fpeq(cres,isares);

    cres_str = to_hex(cres);

    if (!match_c_isa && !match_c_res && !match_isa_res && output_dbg) {
      cerr<<endl;
      cerr<<"DBG: "<<current_op<<endl;
      cerr<<"DBG: "<<hexfloat<<a<<" "<<b<<" "<<c<<" "<<d<<" "<<endl;
      cerr<<"DBG: res = "<<res<<endl;
      cerr<<"DBG: c   = "<<cres<<endl;
      cerr<<"DBG: isa = "<<isares<<endl;
      cerr<<"DBG: Mismatch"<<endl;
    }
  }


  if (!match_c_isa) error("Mismatch between C and ISA!");

  assert(match_c_res == match_isa_res);

  if (output_mode == OUT_REGRESSION) {
    if (!match_c_res) error("Mismatch between C/ISA and RES");
  }

  if (output_mode == OUT_GOOD && match_c_res) cout<<current_op<<endl;

  if (output_mode == OUT_BAD && !match_c_res) cout<<current_op<<endl;

  if (output_mode == OUT_FIX) {
    string fixed=current_op;
    if (!match_c_res) {
      orig_fs.back() = cres_str;
      fixed = boost::join(orig_fs, " ");
    }

    cout<<fixed<<endl;
  }

}


int main(int argc, char **argv) {
  string l;
  size_t count=0;
  bool output_progress=false;

  for (int i=1;i<argc;++i) {
    if (string(argv[i]) == "good") output_mode=OUT_GOOD;
    else if (string(argv[i]) == "bad") output_mode=OUT_BAD;
    else if (string(argv[i]) == "regr") output_mode=OUT_REGRESSION;
    else if (string(argv[i]) == "fix") output_mode=OUT_FIX;
    else if (string(argv[i]) == "dbg") output_dbg=true;
    else if (string(argv[i]) == "progress") output_progress=true;
    else error(string("Unknown command line argument: ") + argv[i]);
  }

  while (getline(cin,l)) {
    ++count;
    try {
      test(l);
    } catch (...) {
      cerr<<endl<<l<<endl;
      cerr<<"Unhandled exception at # "<<count<<endl;
      throw;
    }

    if (count % 1000 == 0 && output_progress) {cerr<<".";cerr.flush();}
  }


  cerr<<"Did "<<count<<" tests."<<endl;

  return 0;
}







