
all: test_open_list test_bin_search test_kmp test_sorting test_float test_double test_avx512f test_float_ops

.PHONY: test_open_list test_bin_search test_kmp test_sorting test_float test_double test_avx512f test_float_ops

BIN=../bin
CC= clang   -O3 -g -I "../gencode" -Wall -lpthread                                      ../../src/lib_isabelle_llvm.c
CPP=clang++ -O3 -g -I "../gencode" -Wall -lpthread -std=c++20  -flto  ../../src/lib_isabelle_llvm.cpp ../../src/lib_isabelle_llvm_par.cpp

VG=valgrind -q --leak-check=full --error-exitcode=2


$(BIN)/open_list: open_list.c ../gencode/open_list.h ../gencode/open_list.ll
	$(CC) open_list.c ../gencode/open_list.ll -o $(BIN)/open_list

test_open_list: $(BIN)/open_list
	$(BIN)/open_list
	$(VG) $(BIN)/open_list

$(BIN)/bin_search: bin_search.c ../gencode/bin_search.h ../gencode/bin_search.ll
	$(CC) bin_search.c ../gencode/bin_search.ll -o $(BIN)/bin_search

test_bin_search: $(BIN)/bin_search
	$(BIN)/bin_search
	$(VG) $(BIN)/bin_search

$(BIN)/kmp: kmp.c ../gencode/kmp.h ../gencode/kmp.ll
	$(CC) kmp.c ../gencode/kmp.ll -o $(BIN)/kmp

test_kmp: $(BIN)/kmp
	$(BIN)/kmp
	$(VG) $(BIN)/kmp

$(BIN)/test_float: test_float.c double_lib.c ../gencode/test_float.h ../gencode/test_float.ll
	$(CC) -lm -ffp-contract=off -ffp-model=strict test_float.c ../gencode/test_float.ll -o $(BIN)/test_float

test_float: $(BIN)/test_float
	$(BIN)/test_float
	$(VG) $(BIN)/test_float

$(BIN)/test_double: test_double.c double_lib.c ../gencode/test_double.h ../gencode/test_double.ll
	$(CC) -lm -ffp-contract=off -ffp-model=strict test_double.c ../gencode/test_double.ll -o $(BIN)/test_double

test_double: $(BIN)/test_double
	$(BIN)/test_double
	$(VG) $(BIN)/test_double

$(BIN)/test_avx512f: test_avx512f.c double_lib.c ../gencode/test_avx512f.h ../gencode/test_avx512f.ll
	$(CC) -lm -march=x86-64 -mavx512f -ffp-contract=off test_avx512f.c ../gencode/test_avx512f.ll -o $(BIN)/test_avx512f

test_avx512f: $(BIN)/test_avx512f
	sde -- $(BIN)/test_avx512f
# 	$(VG) $(BIN)/test_avx512f


$(BIN)/test_float_ops: test_float_ops.cpp ../gencode/test_avx512f_ops.h ../gencode/test_avx512f_ops.ll
	$(CPP) -lm -march=x86-64 -mavx512f -ffp-model=strict test_float_ops.cpp ../gencode/test_avx512f_ops.ll -o $(BIN)/test_float_ops

test_float_ops: $(BIN)/test_float_ops
	sde -- $(BIN)/test_float_ops regr <../floating_point/fixed_tests.txt
# 	$(VG) $(BIN)/test_float_ops

$(BIN)/sorting: sorting.cpp ../gencode/sorting.h ../gencode/sorting.ll
	$(CPP) -stdlib=libstdc++  sorting.cpp ../gencode/sorting.ll -o $(BIN)/sorting

test_sorting: $(BIN)/sorting
	$(BIN)/sorting
	$(VG) $(BIN)/sorting

clean:
	@ rm -f $(BIN)/open_list $(BIN)/bin_search $(BIN)/kmp $(BIN)/sorting

