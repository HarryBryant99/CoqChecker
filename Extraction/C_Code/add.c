#include <stdio.h>

#include <stdbool.h> /* for bool, true and false */
#include <stdint.h> /* uint64_t */
#include <stddef.h> /* size_t */
#include <stdlib.h> /* malloc */
#include <stdio.h> /* perror */
#include <assert.h> /* assert */
#include <inttypes.h> /* PRIu64 */

typedef uint64_t nat;
#define nat_succ(n) ((n)+1)
#define nat_pred(n) ((n)-1)

#define nat_add(x,y) ((x) + (y))
#define nat_sub(x,y) ((x) - (y))
#define nat_mul(x,y) ((x) * (y))
#define nat_div(x,y) ((x) / (y))
#define nat_mod(x,y) ((x) % (y))

#define sw_nat(n) ((n) == 0)
#define S_tag 0
#define S_get_member_0(n) ((n) - 1)
#define S(n) ((n) + 1)

nat my_add(nat v1_n, nat v2_m)
{
  nat v3_p;
  nat v4_n;
  entry_my_add:
  switch (sw_nat(v1_n))
  {
    default:
      return v2_m;
    case S_tag:
      v3_p = S_get_member_0(v1_n);
      v4_n = S(v2_m);
      v1_n = v3_p;
      v2_m = v4_n;
      goto entry_my_add;
  }
}

int main() {
    // Write C code here
    printf("%d",my_add(3,4));
    return 0;
}