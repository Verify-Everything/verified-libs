#include <limits.h>
/*@ ensures \result == (a > UINT_MAX - b ? UINT_MAX : a + b);
    assigns \nothing; */
unsigned add_sat(unsigned a, unsigned b) {
  if (a > UINT_MAX - b) return UINT_MAX;
  return a + b;
}

/*@ requires n >= 0 && \valid_read(s + (0 .. n-1));
    assigns \nothing;
    ensures 0 <= \result <= n; */
int count_nonzero(const char *s, int n) {
  int c = 0;
  /*@ loop invariant 0 <= i <= n && 0 <= c <= i;
      loop assigns i, c;
      loop variant n - i; */
  for (int i = 0; i < n; i++) if (s[i]) c++;
  return c;
}
