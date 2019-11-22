# Isabelle-LLVM (Introsort Case Study)

Isabelle-LLVM is a verification framework for Isabelle/HOL that targets LLVM as backend.

This archive contains the version where we amended the Introsort case study in folder thys/examples/sorting, and
the corresponding benchmarks in benchmarks/sorting.

## Prerequisites
  * To compile the LLVM code: Working installation of [LLVM](http://releases.llvm.org/) version >= 6.0.0.
  * To re-check the proofs: Working installation of [Isabelle/HOL](https://isabelle.in.tum.de) 
    with the [Archive of Formal Proofs](https://www.isa-afp.org) installed 
    as as described on [https://www.isa-afp.org/using.shtml](https://www.isa-afp.org/using.shtml). 
    We require version = Isabelle-2019, which, at the time of writing, is the current version.

## Compiling and running benchmarks
  To compile and run the benchmarks

    cd benchmarks/sorting
    make run

    
## Re-Checking the Proofs
  To re-check the proofs, run

      cd thys 
      isabelle build -D.
      
  Here, <code>isabelle</isabelle> must refer to <code>/your/path/to/Isabelle2019/bin/isabelle</code> from your Isabelle installation.
  This will invoke Isabelle to check all proofs and re-generate the exported code.

