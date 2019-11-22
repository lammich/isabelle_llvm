#!/bin/bash
./do_benchmark uint64 isabelle::sort almost-sorted-50 100000000 10
./do_benchmark uint64 std::sort sorted-middle-10 100000000 10
./do_benchmark llstring isabelle::sort random-boolean 10000000 10
