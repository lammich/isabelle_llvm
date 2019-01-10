#include <vector>
#include <iostream>   // std::cout
#include <string>     // std::string, std::stoi


int main(int argc, char** argv) {
  int64_t n = std::stol(argv[1]);
  
  auto v = std::vector<int64_t>();
  
  for (int64_t i=n;i>0;--i) v.push_back(i);
  
  int64_t s=0;
  
  while (n>0) {
    --n;
    s+=v[n];
  }
  
  std::cout<<"result = "<<s<<std::endl;
  return 0;
}  


