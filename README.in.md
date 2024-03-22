# Isabelle-LLVM Parallel

Note: this distribution has been copied and adapted from the original Isabelle-LLVM framework.

Isabelle-LLVM Parallel is a verification framework for Isabelle/HOL that targets LLVM as backend.
It adds parallel execution to the original [Isabelle LLVM](http://www21.in.tum.de/~lammich/isabelle_llvm/).

For build instructions and starting points to browse the theories, see [HTML:(index.html)].

# Regression Test

The regression test can be run using `make` in the [regression](regression) directory. The following commands must be available.
- [Valgrind](https://valgrind.org/) as `valgrind` 
- clang as `clang`
- Intel's [intruction set emulator](https://www.intel.com/content/www/us/en/developer/articles/tool/software-development-emulator.html) as `sde`
