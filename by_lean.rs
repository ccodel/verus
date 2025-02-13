use vstd::prelude::*;

verus! {

spec fn add_one(i: int) -> int {
  i + 1
}

spec fn add(x: int, y: int) -> int {
  x + y
}

// proof fn test_this(i: int) {
  // assert(i != i + 1);
  // assert(forall|x:int| x != #[trigger] (x + 1)) by (lean);
  // assert(exists|x:int| x != #[trigger] (x + 1)) by (lean);
  // assert(add_one(i + 1) == i + 2) by (lean);
  // assert(let j := i + 1 in
    // j + j + j != i) by (lean);
// }

// proof fn test_that() {
//   assert(forall|x:int, y:nat| x + y == #[trigger] (y + x)) by (lean);
//   assert(forall|x:int, y:nat| x+y != #[trigger] (x+y+1)) by (lean);
// }

proof fn assert_add_one(x: int) {
  assert(add_one(x) + 1 == x + 2) by (lean);
}

proof fn assert_add(x: int, y: int) {
  assert(add(x, y) == x + y) by (lean);
}

// proof fn assert_forall() {
//   assert(forall|i: u32| 0 <= i <= 10 ==> add_one(i) == i+1) by (lean);
// }

/*
proof fn lean_test(x: int, y: int, z:int, m: int) by(lean)
  requires ((x-y) % m == 0)
  ensures (x*z- y*z) % m == 0
{}

proof fn assert_lean_test(x:int, y:int) {
  assert(x == y ==> y == x) by (lean);
  assert(x + y == y + x) by (lean);
}

proof fn assert_lean_jumble(x:int, y:int, z:bool, a:u32) {
  assert(x + y < y + x + x) by (lean);
  assert(x * y < y / x) by (lean);
  assert(!a & (a ^ a) == (a << 1) | (a >> 1)) by (lean);
}
 */
/*
proof fn assert_lean_array(x: [u32; 3]) {
  assert(1 == 1) by (lean);
  assert(false == false) by (lean);
  // assert(x == x) by (lean);
  // assert([3, 3, 0] != [3, 3, 1]) by (lean);
  // let a: [u32; 3] = [3, 3, 0];
  // assert(x != a) by (lean);
}
 */
fn main() {
  assert(true);
}

}
