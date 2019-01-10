#include <stdint.h>
#include <stdlib.h>
#include <stdio.h>
#include <string.h>


typedef struct {
  int64_t len;
  char *str;
} string;

int64_t kmp(string,string);


string string_of_str(char *s) { string r = {strlen(s),s}; return r;}

void error(char * msg) {
  printf("Error: %s\n",msg);
  exit(1);
}


string string_of_file(char *fname) {
  // code snippet found on fundza.com
  /* declare a file pointer */
  FILE    *infile;
  char    *buffer;
  int64_t numbytes;
  
  /* open an existing file for reading */
  infile = fopen(fname, "r");
  
  /* quit if the file does not exist */
  if(infile == NULL) error("No such file");
  
  /* Get the number of bytes */
  fseek(infile, 0L, SEEK_END);
  numbytes = ftell(infile);
  
  /* reset the file position indicator to 
  the beginning of the file */
  fseek(infile, 0L, SEEK_SET);	
  
  /* grab sufficient memory for the 
  buffer to hold the text */
  buffer = (char*)calloc(numbytes, sizeof(char));	
  
  /* memory error */
  if(buffer == NULL) error("Out of memory");
  
  /* copy all the text into the buffer */
  fread(buffer, sizeof(char), numbytes, infile);
  fclose(infile);
  
  string res = {numbytes,buffer};
  return res;
}

void free_string(string s) { free (s.str); }



int main (int argc, char** argv) {
  
  if (argc != 4) {printf("usage: kmp <num-iterations> <search-string> <textfile>\n"); exit(1);}
  
  int n = strtol(argv[1],NULL,10);
  string s1 = string_of_str(argv[2]);
  string s2 = string_of_file(argv[3]);
  
  for (int i=1;i<n;++i) kmp(s1,s2);
  int64_t res = kmp(s1,s2);
  
  printf("result (%d iterations) = %ld\n", n, res);
  
  free_string(s2);
  
  return 0;
}
