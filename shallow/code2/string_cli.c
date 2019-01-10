#include <stdint.h>
#include <stdlib.h>
#include <stdio.h>


int64_t my_strlen(char *);
char streq(char *, char *);


int main (int argc, char** argv) {
  
  if (argc != 3) {printf("Expecting two arguments\n"); exit(1);}

  if (streq(argv[1],argv[2])) printf("Equal\n");
  else if (my_strlen(argv[1]) == my_strlen(argv[2])) printf("Not equal (but eq len) %ld\n", my_strlen(argv[1]));
  else printf("Not equal, len not equal %ld != %ld\n",my_strlen(argv[1]),my_strlen(argv[2]));
}



