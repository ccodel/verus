use vstd::prelude::*;

verus! {

proof fn assert_lean_array(x: [u32; 3]) {
  assert(1 == 1) by (lean);
  assert(false == false) by (lean);
  assert(x == x) by (lean);
  let a: [u32; 3] = [3, 3, 0];
  let b: [u32; 3] = [3, 3, 1];
  assert(a != b) by (lean);
  assert(x == a) by (lean);
}

fn main() {
  assert(true);
}

}
