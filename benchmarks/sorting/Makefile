default: do_benchmark do_benchmark_gcc

gcode=../../thys/examples/code
libs=../../src/lib_isabelle_llvm.cpp ../../src/lib_isabelle_llvm.c
cflags=-std=c++11 -stdlib=libstdc++ -Wall -Wno-unused-function -O3 -flto -I${HOME}/include -I$(gcode) ../../src/lib_isabelle_llvm.cpp
# cflags=-std=c++11 -stdlib=libstdc++ -march=native -w -Wall -fexceptions -O3 -I${HOME}/include -I$(gcode) -s
# -mllvm -inline-threshold=100000 -flto

compile=clang++ $(cflags)
compile_gcc=g++ -std=c++11 -Wall -Wno-unused-function -flto -O4 -I${HOME}/include

file_generator: file_generator.cpp Makefile
	$(compile) ./file_generator.cpp -o file_generator

do_benchmark: do_benchmark.cpp $(gcode)/introsort.ll $(libs) Makefile
	$(compile) ./do_benchmark.cpp $(gcode)/introsort.ll -o do_benchmark

do_benchmark_gcc: do_benchmark.cpp  Makefile
	$(compile_gcc) -DNO_LLVM do_benchmark.cpp -o do_benchmark_gcc

benchmark_numbers: benchmark_numbers.cpp $(gcode)/introsort.ll $(libs) Makefile
	$(compile) ./benchmark_numbers.cpp $(gcode)/introsort.ll -o benchmark_numbers

benchmark_numbersXXX: benchmark_numbers.cpp $(gcode)/introsortXXXOO.ll $(libs) Makefile
	$(compile) ./benchmark_numbers.cpp $(gcode)/introsortXXXOO.ll -o benchmark_numbersXXX

benchmark_numbersUGI: benchmark_numbers.cpp $(gcode)/introsortUGI.ll $(libs) Makefile
	$(compile) ./benchmark_numbers.cpp $(gcode)/introsortUGI.ll -o benchmark_numbersUGI

benchmark_strings: benchmark_strings.cpp $(gcode)/introsort.ll $(libs) Makefile
	$(compile) ./benchmark_strings.cpp $(gcode)/introsort.ll -o benchmark_strings

stest: stest.cpp introsort_instr.ll Makefile
#	$(compile) stest.cpp introsort_instr.ll -o stest
	$(compile) stest.cpp $(gcode)/heapsort.ll -o stest

.PHONY: run

input.bin: file_generator Makefile
	./file_generator input.bin 125000000

run: do_benchmark input.bin all_benchmarks.sh
	./all_benchmarks.sh
