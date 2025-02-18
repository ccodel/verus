use vstd::prelude::*;

verus! {

spec fn add_one(i: int) -> int {
  i + 1
}

spec fn add(x: int, y: int) -> int {
  x + y
}

spec fn minus(x: int, y: int) -> int {
  x - y
}

proof fn assert_add_one(i: int) {
  assert(add_one(i) == i + 1) by (lean);
  assert(add_one(i + 1) == i + 2) by (lean);
  assert(add_one(i) + 1 == i + 2) by (lean);
}

proof fn assert_add(x: int, y: int) {
  assert(add(x, y) == x + y) by (lean);
  assert(add(x, y) == add(y, x)) by (lean);
  assert(add(x, 1) == add_one(x)) by (lean);
}

proof fn assert_minus(x: int, y: int) {
  assert(minus(x, y) == x - y) by (lean);
}

fn main() {
  assert(true);
}

}
