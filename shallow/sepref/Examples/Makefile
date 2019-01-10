all: kmp

kmp: kmpcli.c lib_isabelle_llvm.c kmp.ll
	llvm-as -disable-output kmp.ll
	clang -O3 kmpcli.c lib_isabelle_llvm.c kmp.ll -o kmp

lorem.txt: lorem0.txt
	rm -f lorem.txt
	bash -c 'for ((i=0;$$i<100;++i)); do cat lorem0.txt >> lorem.txt; done'

bench: kmp lorem.txt
	time -v ./kmp 200 'not a latin text' 'lorem.txt'
