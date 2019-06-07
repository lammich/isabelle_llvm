#include <iostream>
#include <string>
#include <vector>
#include <fstream>
#include <streambuf>
#include <cerrno>
#include <ctime>


using namespace std;

// From https://gist.github.com/gongzhitaao/5e9d8f80aaba60e14a2c
int64_t kmp(const string &T, const string &P) {
  if (P.empty()) return 0;

  vector<int64_t> pi(P.size(), 0);
  for (int64_t i = 1, k = 0; i < P.size(); ++i) {
    while (k && P[k] != P[i]) k = pi[k - 1];
    if (P[k] == P[i]) ++k;
    pi[i] = k;
  }

  for (int64_t i = 0, k = 0; i < T.size(); ++i) {
    while (k && P[k] != T[i]) k = pi[k - 1];
    if (P[k] == T[i]) ++k;
    if (k == P.size()) return i - k + 1;
  }

  return -1;
}


/// from https://gist.github.com/yongpitt/5704216
int* getPrefixFunction(string str)
{
  if(str=="")
		return NULL;
	int n=str.size();
	int k=0;
	int *A = new int[n];
	A[0] = 0;
	for(int i=1; i<n; i++){
		while(k&&str[k]!=str[i])  //this loop is to find the k-1
			k = A[k-1];          //The condition str[k]!=str[i] makes sure it finds 
		if(str[i]==str[k])
			k = k+1;
		A[i] = k;
	}
	return A;
}

bool kmp2(string text, string pattern)
{
	if(pattern=="") return true;
	if(text=="") return false;
	int n = text.size();
	int p = pattern.size();
	int *sf = getPrefixFunction(pattern);
	int localMatch = 0;
	for(int i=0; i<=n-p; i++){
		for(int j=localMatch, k=0; j<p; j++,k++){
			if(text[i+k]==pattern[j])
				localMatch++;
			else{
				localMatch = sf[localMatch];
				i=i+(localMatch-sf[localMatch])+sf[localMatch]; //I previous put this before the above statement.
				break;
			}
		}
		if(localMatch==p)
			return true;
	}
	return false;
}

std::string get_file_contents(const char *filename)
{
  std::ifstream in(filename, std::ios::in | std::ios::binary);
  if (in)
  {
    std::string contents;
    in.seekg(0, std::ios::end);
    contents.resize(in.tellg());
    in.seekg(0, std::ios::beg);
    in.read(&contents[0], contents.size());
    in.close();
    return(contents);
  }
  throw(errno);
}

int main(int argc, char **argv) {
  if (argc != 4) {
    cout<<"Usage: kmp n s t"<<endl;
    exit(-1);
  }
  
  int n = stoi(argv[1]);
  string s = argv[2];
  string t = get_file_contents(argv[3]);

  auto time = clock();
  
  for (int i=1;i<n;++i) kmp2(t,s);
  int res = kmp2(t,s);

  time = clock() - time;
  
  int mtime = (int) (((double)time)/CLOCKS_PER_SEC * 1000000 / n);
  
  
  cout<<"Result: "<<res<<endl;
  cout<<"Time: "<<mtime<<"us"<<endl;
  
  cout<<"@("<<n<<") '"<<s<<"': "<<mtime<<endl;
  
  return 0;
}

