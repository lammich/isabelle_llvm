
all: test_open_list test_bin_search test_kmp test_sorting

BIN=../bin
CC=clang -O3 -I "../gencode" ../../src/lib_isabelle_llvm.c
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

$(BIN)/sorting: sorting.c ../gencode/sorting.h ../gencode/sorting.ll
	$(CC) sorting.c ../gencode/sorting.ll -o $(BIN)/sorting

test_sorting: $(BIN)/sorting
	$(BIN)/sorting
	$(VG) $(BIN)/sorting

clean:
	@ rm -f $(BIN)/open_list $(BIN)/bin_search $(BIN)/kmp $(BIN)/sorting

