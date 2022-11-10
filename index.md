<!--
  IMPORTANT: If you landed here from a downloaded archive file, go to html/index.html to view this page in a browsable form!
-->
# ![Isabelle-LLVM Logo](logo_200.png) Isabelle-LLVM

Isabelle-LLVM is a verification framework for Isabelle/HOL that targets LLVM as backend.
The main features are:

  * Shallowly embedded semantics of fragment of LLVM
  * Code generator, to export LLVM code
  * Generation of header files for interfacing the code from C/C++
  * Separation logic based VCG
  * Support for stepwise refinement based verification
  * Support for parallel programs

## News
  * November 2022: ported to Isabelle 2022
  * June 2022: added support for unions
  * April 22: added support for floating point numbers
  * October 2021: added support for parallel programs
  * July 2021: [ISASAT](https://m-fleury.github.io/isasat/isasat.html), a fully verified SAT solver that uses Isabelle-LLVM, has won the [2021 EDA](https://www.eda-ai.org/) Fixed CNF Encoding Race.
  * June 2021: released version 2.0. New features:
    * support of arbitrary structures, and pointers to structure itself (required for, e.g., linked lists)
    * faster export_llvm for big code
  * Updated to work with new Isabelle 2021 version



## Getting Started
  You can [browse the theories](Isabelle_LLVM/) or [download](dist.tgz) the files. (The download link won't work if you are browsing this from inside the downloaded archive!)

  Warning: the .thy files in the download are best viewed with the [Isabelle/HOL](https://isabelle.in.tum.de) IDE.

### Git Repository
  The project is hosted on github [github.com/lammich/isabelle_llvm](https://github.com/lammich/isabelle_llvm)

### Starting Points for Browsing
  Here are some default starting points for browsing the theories

#### Parallel Paper
  Some starting points, structured according to the parallel paper:

  [NE Monad](Isabelle_LLVM/NEMonad.html)
  
  [M Monad](Isabelle_LLVM/MMonad.html) Includes the parallel combinator
  
  [Memory Model](Isabelle_LLVM/Generic_Memory.html) Including access reports
  
  [LLVM Values stored in Memory](Isabelle_LLVM/Simple_Memory.html)

  [LLVM Instructions](Isabelle_LLVM/LLVM_Shallow.html)
  
  [Code Generator](Isabelle_LLVM/LLVM_Codegen.html) Including the [template for translating llc_par](Isabelle_LLVM/files/par_wrapper.tmpl.ml.html)

  [Separation Logic and VCG](Isabelle_LLVM/LLVM_VCG_Main.html) A bit more general than described in paper, parameterized over memory model.
    The general rules are proved in [Sep_Generic_Wp.thy](Isabelle_LLVM/Sep_Generic_Wp.html), e.g. lemma ht_par for the parallel rule.
    The instantiated parallel rule is ht_llc_par in [Sepref_Parallel.thy](Isabelle_LLVM/Sepref_Parallel.html).

  [Sepref Tool](Isabelle_LLVM/Sepref.html) Including the parallel setup in [Sepref_Parallel.thy](Isabelle_LLVM/Sepref_Parallel.html).

  [Sorting Algorithms](Isabelle_LLVM/Sorting_Export_Code.html) Contains the code export to LLVM, and the final correctness theorem.
  Our parallel quicksort algorithm is in [Sorting_Parsort.thy](Isabelle_LLVM/Sorting_Parsort.html)
  and the sampling partitioner is in [Sorting_Sample_Partition.thy](Isabelle_LLVM/Sorting_Sample_Partition.html).


#### Verified Algorithms
  [Parallel Quicksort](Isabelle_LLVM/Sorting_Parsort.html)
  
  [Introsort](Isabelle_LLVM/Sorting_Introsort.html)

  [PDQ Sort](Isabelle_LLVM/Sorting_PDQ.html)

  [Knuth Morris Pratt String Search](Isabelle_LLVM/KMP.html)

  [Binary Search](Isabelle_LLVM/Bin_Search.html)
  
  For the ISA-SAT verified SAT solver, see its own [homepage](https://m-fleury.github.io/isasat/isasat.html)
  
#### Isabelle-LLVM
  [IICF (Isabelle-LLVM + Refinement Framework + Collection Framework)](Isabelle_LLVM/IICF.html)

  [Shallow Embedding of LLVM Semantics](Isabelle_LLVM/LLVM_Shallow.html)


## Prerequisites
  * To compile the LLVM code: Working installation of [LLVM](http://releases.llvm.org/) version >= 10.0.0.
  * To compile the functional code: An [MLton](http://mlton.org/) compiler version >= 20100608.
  * To re-check the proofs: Working installation of [Isabelle/HOL](https://isabelle.in.tum.de) 
    with the [Archive of Formal Proofs](https://www.isa-afp.org) installed 
    as as described on [https://www.isa-afp.org/using.shtml](https://www.isa-afp.org/using.shtml). 
    We require version = Isabelle-2021-1, which, at the time of writing, is the current version.
  * To run the regression tests: [Valgrind](https://www.valgrind.org/) version >= 3.0.0

## Compiling and running benchmarks
  To compile and run the benchmarks

    cd benchmarks
    ./bench_bs.sh -r
    ./bench_kmp.sh -r
    cd sorting
    make run

  This will run the binary search, KMP, and parallel sorting benchmarks.
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
  [ITP'22 Paper](paper_ITP2022.pdf) [Slides](slides_ITP2022.pdf)

  [IJCAR'2020 Paper](paper_IJCAR2020.pdf) [Slides](slides_IJCAR2020.pdf)

  [ITP'2019 Paper](paper_ITP2019.pdf) [Slides](slides_ITP2019.pdf)


  [May 2021 Talk in Enschede](enschede2021.pdf)

  [Short Presentation of the Isabelle Refinement Framework](RF_pres.pdf)

  [Mar 2020 Talk in Enschede](enschede2020.pdf)

  [Dec 2019 Talk in Rennes](rennes2019.pdf)


## Old Versions
  The download links won't work if you are browsing this from inside a downloaded archive!

  [Isabelle-LLVM 1.0 for Isabelle-2020](dist-2020.tgz)

  [Isabelle-LLVM 1.1 for Isabelle-2021](dist-v1.1.tgz)

  [Isabelle-LLVM 2.0 for Isabelle-2021](dist-v2.0.tgz)



