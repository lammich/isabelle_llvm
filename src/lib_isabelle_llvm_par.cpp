/*
 * Isabelle LLVM Parallel support library
 */
#include <future>
extern "C" {
  void isabelle_llvm_parallel(void (*f1)(void*), void (*f2)(void*), void *x1, void *x2) {
    auto s1 = std::async(std::launch::async, f1,x1);
    f2(x2);
    s1.get();
  }
}
