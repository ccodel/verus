#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn loop_simple(n: u32) -> u32
    requires n >= 0
{
    let mut sum: u32 = 0;
    let mut i: u32 = 0;
    while i < n
        invariant i <= n && (i * (i - 1)) / 2 == sum,
        decreases n - i
    {
        sum = sum + i;
        i = i + 1;
    }
    assert((n * (n - 1)) / 2 == sum);
    assert(i == n);
    sum
}

fn main() {
}

} // verus!

/* program Boogie;

procedure loopSimple (n: int) returns (r: int)
spec {
  requires (n >= 0);
}
{
  var sum : int;
  var i : int;

  sum := 0;
  i := 0;
  while(i < n)
    invariant (i <= n && ((i * (i-1)) div 2 == sum));
  {
    sum := sum + i;
    i := i + 1;
  }
  assert [sum_assert]: ((n * (n-1)) div 2 == sum);
  assert [neg_cond]: (i == n);
  r := sum;
};
 */
