default: benchmark_numbers stest

gcode=../../thys/examples/code
cflags=-std=c++11 -stdlib=libstdc++ -Wall -Wno-unused-function -O3 -I${HOME}/include -I$(gcode)
# cflags=-std=c++11 -stdlib=libstdc++ -march=native -w -Wall -fexceptions -O3 -I${HOME}/include -I$(gcode) -s
# -mllvm -inline-threshold=100000

compile=clang++ $(cflags)

file_generator: file_generator.cpp
	$(compile) ./file_generator.cpp -o file_generator

benchmark_numbers: benchmark_numbers.cpp $(gcode)/introsort.ll
	$(compile) ./benchmark_numbers.cpp $(gcode)/introsort.ll -o benchmark_numbers

stest: stest.cpp introsort_instr.ll
	$(compile) stest.cpp introsort_instr.ll -o stest

.PHONY: run

input.bin: file_generator
	./file_generator input.bin 125000000

run: benchmark_numbers input.bin
	./benchmark_numbers
