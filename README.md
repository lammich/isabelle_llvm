# Isabelle-LLVM

Isabelle-LLVM is a verification framework for Isabelle/HOL that targets LLVM as backend.

## Prerequisites
  * To compile the LLVM code: Working installation of [LLVM](http://releases.llvm.org/) version >= 6.0.0.
  * To compile the functional code: An [MLton](http://mlton.org/) compiler version >= 20100608.
  * To re-check the proofs: Working installation of [Isabelle/HOL](https://isabelle.in.tum.de) 
    with the [Archive of Formal Proofs](https://www.isa-afp.org) installed 
    as as described on [https://www.isa-afp.org/using.shtml](https://www.isa-afp.org/using.shtml). 
    We require version = Isabelle-2019, which, at the time of writing, is the current version.

## Compiling and running benchmarks
  To compile and run the benchmarks

    cd benchmarks
    ./bench_bs.sh -r
    ./bench_kmp.sh -r

  Warning: We have only tested this on a Linux x86_64 platform so far. 
  We do not (yet) know how LLVM will digest our code on other platforms.
    
## Re-Checking the Proofs
  To re-check the proofs, run

      cd thys 
      isabelle build -D.
      
  Here, <code>isabelle</isabelle> must refer to <code>/your/path/to/Isabelle2019/bin/isabelle</code> from your Isabelle installation.
  This will invoke Isabelle to check all proofs and re-generate the exported code.

