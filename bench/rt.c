/* SPDX-License-Identifier: AGPL-3.0-only */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <inttypes.h>
#include <math.h>

void minimbt_main(void);

__attribute__((weak))
int
main() {
  minimbt_main();
}

__attribute__((weak))
void
minimbt_main(void) {
}

void *
minimbt_malloc(int32_t size) {
  return malloc(size);
}

int32_t
minimbt_read_int(void) {
  int32_t i;
  scanf("%" SCNi32, &i);
  return i;
}

void
minimbt_print_int(int32_t i) {
  printf("%" PRId32 "\n", i);
}

void
minimbt_print_endline(void) {
  printf("\n");
}

int32_t
minimbt_int_of_float(double f) {
  if (f != f)
    return 0;
  if (f >= 0x1.fffffffcp+30)
    return 2147483647;
  if (f <= -0x1p+31)
    return -2147483648;
  return (int32_t)f;
}

double
minimbt_float_of_int(int32_t i) {
  return (double)i;
}

int32_t
minimbt_truncate(double f) {
  return minimbt_int_of_float(f);
}

double
minimbt_abs_float(double f) {
  return fabs(f);
}

double
minimbt_sqrt(double f) {
  return sqrt(f);
}

double
minimbt_sin(double f) {
  return sin(f);
}

double
minimbt_cos(double f) {
  return cos(f);
}

double
minimbt_atan(double f) {
  return atan(f);
}


int32_t *
minimbt_create_array(int32_t n, int32_t init) {
  int32_t *result = malloc(sizeof(int32_t)*n);
  for (int32_t i=0; i<n; ++i)
    result[i] = init;
  return result;
}

double *
minimbt_create_float_array(int32_t n, double init) {
  double *result = malloc(sizeof(double)*n);
  for (int32_t i=0; i<n; ++i)
    result[i] = init;
  return result;
}

void **
minimbt_create_ptr_array(int32_t n, void *init) {
  void **result = malloc(sizeof(void*)*n);
  for (int32_t i=0; i<n; ++i)
    result[i] = init;
  return result;
}
