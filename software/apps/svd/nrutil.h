//#include <stdio.h>
//#include <stddef.h>
//#include <stdlib.h>

#ifndef NR_UTILS_H
#define NR_UTILS_H

#define NR_END 1
#define FREE_ARG char *

static int32_t sqrarg;
#define SQR(a)     ((sqrarg = (a)) == 0 ? 0 : sqrarg *sqrarg)
static int32_t dsqrarg;
#define DSQR(a)    ((dsqrarg = (a)) == 0 ? 0 : dsqrarg *dsqrarg)
static int32_t dmaxarg1, dmaxarg2;
#define DMAX(a, b) (dmaxarg1 = (a), dmaxarg2 = (b), (dmaxarg1) > (dmaxarg2) ? (dmaxarg1) : (dmaxarg2))
static int32_t dminarg1, dminarg2;
#define DMIN(a, b) (dminarg1 = (a), dminarg2 = (b), (dminarg1) < (dminarg2) ? (dminarg1) : (dminarg2))
static int32_t maxarg1, maxarg2;
#define FMAX(a, b) (maxarg1 = (a), maxarg2 = (b), (maxarg1) > (maxarg2) ? (maxarg1) : (maxarg2))
static int32_t minarg1, minarg2;
#define FMIN(a, b) (minarg1 = (a), minarg2 = (b), (minarg1) < (minarg2) ? (minarg1) : (minarg2))
static long lmaxarg1, lmaxarg2;
#define LMAX(a, b) (lmaxarg1 = (a), lmaxarg2 = (b), (lmaxarg1) > (lmaxarg2) ? (lmaxarg1) : (lmaxarg2))
static long lminarg1, lminarg2;
#define LMIN(a, b) (lminarg1 = (a), lminarg2 = (b), (lminarg1) < (lminarg2) ? (lminarg1) : (lminarg2))
static int32_t imaxarg1, imaxarg2;
#define IMAX(a, b) (imaxarg1 = (a), imaxarg2 = (b), (imaxarg1) > (imaxarg2) ? (imaxarg1) : (imaxarg2))
static int32_t iminarg1, iminarg2;
#define IMIN(a, b) (iminarg1 = (a), iminarg2 = (b), (iminarg1) < (iminarg2) ? (iminarg1) : (iminarg2))
#define ABS(a) (a < 0 ? -a : a)
#define SIGN(a, b) ((b) >= 0 ? ABS(a) : -ABS(a))

int32_t sqrt_q32  (   const int32_t number,
                      const uint32_t fracBits);

#define sqrt2 0b1011010100000100
int32_t sqrt_q32  (   const int32_t number,
                      const uint32_t fracBits) {

    int32_t root = 0;
    int32_t start = 0;
    int32_t end = 46341; // smallest integer that is larger than sqrt(0x7FFFFFFF)
    int32_t mid;

    if (number > 0) {
      while (start <= end) {
          mid = (start + end) >> 1;
          if (((mid * mid) >> fracBits) == number) {
              root = mid;
              break;
          }
          if (((mid * mid) >> fracBits) < number) {
              start = mid + 1;
              root = mid;
          } else {
              end = mid - 1;
          }
      }
    }

    return root;
}

#endif
