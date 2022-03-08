#include <stdlib.h>
#include <stdint.h>
#include <assert.h>
#include <math.h>

_Static_assert(sizeof(double) == sizeof(uint64_t),"sizeof(double) == sizeof(uint64_t)");
_Static_assert(sizeof(float) == sizeof(uint32_t),"sizeof(float) == sizeof(uint32_t)");

double i2d(uint64_t i) {
  double r;
  *(uint64_t*)(&r) = i;
  return r;
}

uint64_t d2i(double i) {
  uint64_t r;
  *(double*)(&r) = i;
  return r;
}

double nd(double x) {
  if (isnan(x)) return 0; else return x;
}

double rd() {
  return rand() * 42.0 / ((double)RAND_MAX);
}

float i2f(uint32_t i) {
  float r;
  *(uint32_t*)(&r) = i;
  return r;
}

uint32_t f2i(float i) {
  uint32_t r;
  *(float*)(&r) = i;
  return r;
}

float nf(float x) {
  if (isnan(x)) return 0; else return x;
}

float rf() {
  return rand() * 42.0 / ((float)RAND_MAX);
}


uint16_t ru16() {
  return rand() % 0xFFFF; // poor quality random numbers (sigh!)
}

uint32_t ru32() {
  return (((uint32_t)ru16())<<16) | ru16();
}

uint64_t ru64() {
  return (((uint64_t)ru32())<<32) | ru32();
}

double rd1() {
  return i2d(ru64());
}

double rd2() {
  double x;

  do {
    x = rd1();
  } while (isnan(x));

  return x;
}

float rf1() {
  return i2f(ru32());
}

float rf2() {
  float x;

  do {
    x = rf1();
  } while (isnan(x));

  return x;
}


