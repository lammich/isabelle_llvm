all: kmp bs

kmp: kmpcli.c ../../../src/lib_isabelle_llvm.c kmp.ll
	llvm-as -disable-output kmp.ll
	clang -Wall -O3 kmpcli.c "../../../src/lib_isabelle_llvm.c" kmp.ll -o kmp

bs: bin_search_cli.c bin_search.ll
	llvm-as -disable-output bin_search.ll
	clang -Wall -O3 bin_search_cli.c bin_search.ll -o bs
