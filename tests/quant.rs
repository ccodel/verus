use vstd::prelude::*;

verus! {

proof fn simple_forall(i: int) {
  // global variable, bound by function
  assert(i != i + 1) by (lean);
  // simple forall statement
  assert(forall|x:int| x != #[trigger] (x + 1)) by (lean);
  // double forall statement
  assert(forall|x:int, y:nat| x + y == #[trigger] (y + x)) by (lean);
  // refer to global variable inside the body
  assert(forall|x:int, y:nat| x + y + i != #[trigger] (x + y + i + 1)) by (lean);
}

spec fn add_one(i: int) -> int {
  i + 1
}

spec fn add(x: int, y: int) -> int {
  x + y
}

proof fn forall_with_specfn(i: int) {
  // standard commutativity
  assert(forall|x:int, y:int| add(x, y) == add(y, x)) by (lean);
  // shadowing
  assert(forall|i:int| 0 <= i <= 10 ==> add_one(i) == i + 1) by (lean);
}

proof fn simple_exists() {
  assert(exists|x:int| x != #[trigger] (x + 1)) by (lean);
}

fn main() {
}

}
