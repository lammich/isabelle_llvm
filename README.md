# Isabelle-LLVM

## Download
  [Isabelle-LLVM 0.1](isabelle_llvm.tgz)

## Prerequisites
  * To compile the LLVM code: Working installation of [LLVM](http://releases.llvm.org/) version >= 6.0.0.
  * To compile the functional code: An [MLton](http://mlton.org/) compiler version >= 20100608.
  * To re-check the proofs: Working installation of [Isabelle/HOL](https://isabelle.in.tum.de) 
    with the [Archive of Formal Proofs](https://www.isa-afp.org) installed 
    as as described on [https://www.isa-afp.org/using.shtml](https://www.isa-afp.org/using.shtml). 
    We require version = Isabelle-2018, which, at the time of writing, is the current version.

## Compiling and running the LLVM benchmark  
  To compile and run the KMP benchmark in LLVM
  
    cd shallow/sepref/Examples
    make bench
  
  This will compile the KMP algorithm together with a command line interface, and then
  run it 200 times on 8.6 MiB of lorem ipsum, with the search string 'not a latin text', 
  which is not contained in the text.
  
  Warning: We have only tested this on a Linux x86_64 platform so far. 
  We do not (yet) know how LLVM will digest our code on other platforms.
    
## Compiling and running the Standard-ML Benchmark
  To compile and run the KMP algorithm from the original AFP entry:
  
    cd paper/origKMPtest
    make bench  
  
  This compiles the original KMP algorithm from the AFP with a command line interface,
  and runs it 200 times on the same 8.6 MiB of lorem ipsum, with the search string 
  'not a latin text', which is not contained in the text.
    
      
## Re-Checking the Proofs
  To re-check the proofs, run
  
      cd shallow 
      isabelle build -D.
      
  Here, <code>isabelle</isabelle> must refer to <code>/your/path/to/Isabelle2018/bin/isabelle</code> from your Isabelle installation.
  This will invoke Isabelle to check all proofs and re-generate the exported code, 
  which is written to <code>sepref/Examples/kmp.ll</code>

  
  