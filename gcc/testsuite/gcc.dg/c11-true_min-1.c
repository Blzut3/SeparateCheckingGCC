/* { dg-do run } */
/* { dg-options "-std=c11" } */

/* Test that the smallest positive value is not 0. This needs to be true
   even when denormals are not supported, so we do not pass any flag
   like -mieee.  If it fails on alpha, see PR 58757.  */

#include <float.h>

int main(){
  volatile float f = FLT_TRUE_MIN;
  volatile double d = DBL_TRUE_MIN;
  volatile long double l = LDBL_TRUE_MIN;
  if (f == 0 || d == 0 || l == 0)
    __builtin_abort ();
  return 0;
}
