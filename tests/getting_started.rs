use vstd::prelude::*;

verus! {

spec fn min(x: int, y: int) -> int {
    if x <= y {
        x
    } else {
        y
    }
}

fn main() {
    assert(min(10, 20) == 10) by (lean);
    assert(min(-10, -20) == -20) by (lean);
    assert(forall|i: int, j: int| min(i, j) <= i && min(i, j) <= j) by (lean);
    assert(forall|i: int, j: int| min(i, j) == i || min(i, j) == j) by (lean);
    assert(forall|i: int, j: int| min(i, j) == min(j, i)) by (lean);
}

} // verus!
