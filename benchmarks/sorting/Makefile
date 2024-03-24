default: do_benchmark # do_benchmark_gcc sexplore

gcode=../../thys/examples/code
libs=../../src/lib_isabelle_llvm.cpp ../../src/lib_isabelle_llvm.c par_aux.ll
cflags=-std=c++20 -stdlib=libstdc++ -Wall -Wno-unused-function -lpthread -ggdb -ltbb -O3 -flto -I${HOME}/include -I$(gcode) ../../src/lib_isabelle_llvm.cpp
# cflags=-std=c++11 -stdlib=libstdc++ -march=native -w -Wall -fexceptions -O3 -I${HOME}/include -I$(gcode) -s
# -mllvm -inline-threshold=100000 -flto

compile=clang++ $(cflags)
compile_gcc=g++ -std=c++20 -Wall -Wno-unused-function -flto -pthread -ltbb -O4 -I${HOME}/include

sexplore: sexplore.cpp
	$(compile) ./sexplore.cpp -o sexplore

file_generator: file_generator.cpp
	$(compile) ./file_generator.cpp -o file_generator

do_benchmark: do_benchmark.cpp $(gcode)/introsort.ll $(libs)
	$(compile) ./do_benchmark.cpp $(gcode)/introsort.ll -o do_benchmark

do_benchmark_gcc: do_benchmark.cpp
	$(compile_gcc) -DNO_LLVM do_benchmark.cpp -o do_benchmark_gcc

benchmark_numbers: benchmark_numbers.cpp $(gcode)/introsort.ll $(libs)
	$(compile) ./benchmark_numbers.cpp $(gcode)/introsort.ll -o benchmark_numbers

benchmark_numbersXXX: benchmark_numbers.cpp $(gcode)/introsortXXXOO.ll $(libs)
	$(compile) ./benchmark_numbers.cpp $(gcode)/introsortXXXOO.ll -o benchmark_numbersXXX

benchmark_numbersUGI: benchmark_numbers.cpp $(gcode)/introsortUGI.ll $(libs)
	$(compile) ./benchmark_numbers.cpp $(gcode)/introsortUGI.ll -o benchmark_numbersUGI

benchmark_strings: benchmark_strings.cpp $(gcode)/introsort.ll $(libs)
	$(compile) ./benchmark_strings.cpp $(gcode)/introsort.ll -o benchmark_strings

stest: stest.cpp introsort_instr.ll
#	$(compile) stest.cpp introsort_instr.ll -o stest
	$(compile) stest.cpp $(gcode)/heapsort.ll -o stest

.PHONY: run

input.bin: file_generator
	./file_generator input.bin 125000000

log/sortbench-latest.log: do_benchmark input.bin distr_benchmarks.sh
	./distr_benchmarks.sh

log/sortbench-speedup-latest.log: do_benchmark input.bin speedup_benchmarks.sh
	./speedup_benchmarks.sh

log/sortbench-smallarrays-latest.log: do_benchmark input.bin ./smallarrays_benchmarks.sh
	./smallarrays_benchmarks.sh

log/sortbench-latest.pdf: log/sortbench-latest.log
	./eval_benchmark.sh

log/sortbench-speedup-latest.pdf: log/sortbench-speedup-latest.log
	./eval_speedup.sh

log/sortbench-smallarrays-latest.pdf: log/sortbench-smallarrays-latest.log
	./eval_smallarrays.sh

run: log/sortbench-latest.log log/sortbench-speedup-latest.log log/sortbench-smallarrays-latest.log

report: log/sortbench-latest.pdf log/sortbench-speedup-latest.pdf log/sortbench-smallarrays-latest.pdf
