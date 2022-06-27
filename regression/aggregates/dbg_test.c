#include "aggr_test_common.h"

typedef union {
    int16_t f0;
    struct {
      double f0;
    }f1;
    union {
      int32_t*f0;
      float f1;
      float f2;
    }f2;
    double f3;
    union {
      float f0;
    }f4;
    union {
      union {
        int64_t*f0;
        float f1;
        float f2;
        double f3;
        double f4;
        struct {
          int32_t f0;
          int64_t f1;
          int16_t f2;
        }f5;
        int16_t*f6;
        int8_t*f7;
      }f0;
    }f5;
    double f6;
    int16_t f7;
    int32_t*f8;
  } testu_t;


typedef struct {
  double f0;
  testu_t f1;
  int64_t*f2;
  double f3;
  int32_t f4;
  int16_t*f5;
}test_t;

typedef struct {
  int32_t f1; int64_t f2; int16_t f3;
} testuc_t;

int main() {
  size_t s1 = sizeof(testuc_t);

  testuc_t* p=0;
  size_t s2 = (size_t)((void*)(p+1));

  printf("%zd %zd\n",s1,s2);


  return 0;
}



