#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

// This doesn't get serialized, since it isn't used anywhere
struct Worthless {
    x: bool,
    y: nat,
}

// Standard Euclidean point
struct Point {
    x: int,
    y: int,
}

spec fn rotate_90(p : Point) -> Point
{
    Point { x: -p.y, y: p.x }
}

proof fn spec_for_rotate_90(p: Point)
{
    let o = Point { x: -p.y, y: p.x };
    let z = Point { x: 0, y: 0 };

    // Impossible to prove in Lean, not enough context
    // assert(o == rotate_90(p)) by (lean);

    // We can prove this, though
    assert(o == Point { x: -p.y, y: p.x} ==> o == rotate_90(p)) by (lean);
}

////////////////////////////////////////////////////////////////////////////////

enum Syrup {
    Cola { size: nat },
    RootBeer,
    Orange,
    LemonLime,
    Syrup,
}

enum Beverage {
    Coffee { creamers: nat, sugar: bool },
    Soda { flavor: Syrup },
    Water { ice: bool },
}

proof fn test_beverage(bev: Beverage) 
{
    // Simple equality between enums
    assert(Syrup::RootBeer != Syrup::Syrup) by (lean);
    // Equality between enums with values
    assert(Beverage::Coffee { creamers: 0, sugar:  true } != Beverage::Soda { flavor : Syrup::Cola { size: 5 } }) by (lean);
    // Match statements in Lean
    assert(bev is Soda ==> bev !is Coffee) by (lean);
}

////////////////////////////////////////////////////////////////////////////////

enum Life {
    Mammal { legs: int, has_pocket: bool },
    Arthropod { legs: int, wings: int },
    Plant { leaves: int },
}

// (4/27) these currently fail due to `match` translations from Verus to Lean

/* use Life::*;

spec fn is_insect(l: Life) -> bool
{
    l is Arthropod && l->Arthropod_legs == 6
}

spec fn cuddly(l: Life) -> bool
{
    ||| l matches Mammal { legs, .. } && legs == 4
    ||| l matches Arthropod { legs, wings } && legs == 8 && wings == 0
} */


fn main()
{
    // assert(!is_insect(Life::Mammal { legs: 4, has_pocket: true })) by (lean);
    // assert(cuddly(Life::Mammal { legs: 4, has_pocket: true })) by (lean);
}

} // verus!
