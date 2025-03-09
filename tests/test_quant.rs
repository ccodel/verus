use vstd::prelude::*;

verus! {

proof fn assert_forall(i: int) {
  assert(i != i + 1) by (lean);
  assert(forall|x:int| x != #[trigger] (x + 1)) by (lean);
  assert(forall|x:int, y:nat| x + y == #[trigger] (y + x)) by (lean);
  assert(forall|x:int, y:nat| x + y != #[trigger] (x + y + 1)) by (lean);
}

spec fn add_one(i: int) -> int {
  i + 1
}

spec fn add(x: int, y: int) -> int {
  x + y
}

proof fn assert_forall_specfn() {
  assert(forall|i:int| 0 <= i <= 10 ==> add_one(i) == i + 1) by (lean);
  assert(forall|x:int, y:int| add(x, y) == add(y, x)) by (lean);
}

proof fn assert_exists() {
  assert(exists|x:int| x != #[trigger] (x + 1)) by (lean);
}

fn main() {
  assert(true);
}

}
