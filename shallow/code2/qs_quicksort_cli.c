#include <stdint.h>
#include <stdlib.h>
#include <stdio.h>


int64_t qs_quicksort(int64_t*, int64_t, int64_t);


int main (int argc, char** argv) {
  
  if (argc != 2) {printf("Expecting one argument\n"); exit(1);}

  int64_t n = strtoul(argv[1],NULL,10);

  int64_t *A = malloc (n * sizeof(int64_t));
  
  srand(192);
  
  for (int64_t i=0; i<n; ++i) A[i] = rand() % (2*n);

  for (int64_t i=0; i<n; ++i) printf ("%ld ",A[i]);
  printf("\n");
    
  qs_quicksort(A,0,n-1);
  
  for (int64_t i=0; i<n; ++i) printf ("%ld ",A[i]);
  printf("\n");
  
}



