use vstd::prelude::*;

verus! {

proof fn lean_test(x: int, y: int, z:int, m: int) by (lean_proof)
  requires ((x-y) % m == 0)
  ensures (x*z- y*z) % m == 0
{}

proof fn assert_lean_test(x:int, y:int)
{
  assert(x == y ==> y == x) by (lean_proof as a1);
  assert(x + y == y + x) by (lean_proof as a2);
}

proof fn assert_lean_jumble(x:int, y:int, z:bool, a:u32)
{
  assert(x + y < y + x + x) by (lean_proof as a1);
  assert(x * y < y / x) by (lean_proof as a2);
  assert(!a & (a ^ a) == (a << 1) | (a >> 1)) by (lean_proof as a3);
}

fn main() 
{}

}
