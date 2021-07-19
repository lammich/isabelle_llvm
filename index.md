# ![Isabelle-LLVM Logo](logo_200.png) Isabelle-LLVM

Isabelle-LLVM is a verification framework for Isabelle/HOL that targets LLVM as backend.
The main features are:

  * Shallowly embedded semantics of fragment of LLVM
  * Code generator, to export LLVM code
  * Generation of header files for interfacing the code from C/C++
  * Separation logic based VCG
  * Support for stepwise refinement based verification

## News
  * Updated to work with new Isabelle 2021 version
  * June 2021: released version 2.0. New features:
    * support of arbitrary structures, and pointers to structure itself (required for, e.g., linked lists)
    * faster export_llvm for big code



## Getting Started
  You can [browse the theories](Isabelle_LLVM/) or [download](dist.tgz) the files.

  Warning: the .thy files in the download are best viewed with the [Isabelle/HOL](https://isabelle.in.tum.de) IDE.

### Git Repository
  The project is hosted on github [https://github.com/lammich/isabelle_llvm](https://github.com/lammich/isabelle_llvm)

### Starting Points for Browsing
  Here are some default starting points for browsing the theories

#### Verified Algorithms
  [Introsort](Isabelle_LLVM/Sorting_Introsort.html)

  [PDQ Sort](Isabelle_LLVM/Sorting_PDQ.html)

  [Knuth Morris Pratt String Search](Isabelle_LLVM/KMP.html)

#### Isabelle-LLVM
  [IICF (Isabelle-LLVM + Refinement Framework + Collection Framework)](Isabelle_LLVM/IICF.html)

  [Shallow Embedding of LLVM Semantics](Isabelle_LLVM/LLVM_Shallow.html)


## Prerequisites
  * To compile the LLVM code: Working installation of [LLVM](http://releases.llvm.org/) version >= 6.0.0.
  * To compile the functional code: An [MLton](http://mlton.org/) compiler version >= 20100608.
  * To re-check the proofs: Working installation of [Isabelle/HOL](https://isabelle.in.tum.de) 
    with the [Archive of Formal Proofs](https://www.isa-afp.org) installed 
    as as described on [https://www.isa-afp.org/using.shtml](https://www.isa-afp.org/using.shtml). 
    We require version = Isabelle-2021, which, at the time of writing, is the current version.
  * To run the regression tests: [Valgrind](https://www.valgrind.org/) version >= 3.0.0

## Compiling and running benchmarks
  To compile and run the benchmarks

    cd benchmarks
    ./bench_bs.sh -r
    ./bench_kmp.sh -r
    cd sorting
    make run

  This will run the binary search, KMP, and sorting benchmarks.
  Warning: We have only tested this on a Linux x86_64 platform so far. 
  We do not (yet) know how LLVM will digest our code on other platforms.
    
## Re-Checking the Proofs
  To re-check the proofs, run

      cd thys 
      isabelle build -D.

  Here, <code>isabelle</code> must refer to <code>/your/path/to/Isabelle2021/bin/isabelle</code> from your Isabelle installation.
  This will invoke Isabelle to check all proofs and re-generate the exported code.

### Regression Test Script
  To run a quick regression test script

      cd regression
      make

  This will re-check the proofs, export a few example programs,
  link them with C wrappers, and execute them under Valgrind's memcheck,
  to detect ABI problems with header file generation and interfacing exported code from C.


## Talks and Publications
  [IJCAR'2020 Paper](paper_IJCAR2020.pdf) [Slides](slides_IJCAR2020.pdf)

  [ITP'2019 Paper](paper_ITP2019.pdf) [Slides](slides_ITP2019.pdf)


  [May 2021 Talk in Enschede](enschede2021.pdf)

  [Short Presentation of the Isabelle Refinement Framework](RF_pres.pdf)

  [Mar 2020 Talk in Enschede](enschede2020.pdf)

  [Dec 2019 Talk in Rennes](rennes2019.pdf)


## Old Versions
  [Isabelle-LLVM 1.0 for Isabelle-2020](dist-2020.tgz)

  [Isabelle-LLVM 1.1 for Isabelle-2021](dist-v1.1.tgz)

