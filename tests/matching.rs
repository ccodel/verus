#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

  enum Sport {
    Soccer { num_players: nat, team_id: int },
    Running { distance: nat },
    Swimming { num_laps: nat, is_relay : bool },
  }

  enum NatBox {
    Nat(nat),
  }

  use crate::Sport::*;
  use crate::NatBox::*;

  spec fn sport_nat(s: Sport) -> nat
  {
    match s {
      Soccer { num_players, team_id } => num_players,
      Running { distance } => distance,
      Swimming { num_laps, is_relay } => num_laps,
    }
  }

  spec fn get_data_in_box(b: NatBox) -> nat
  {
    match b {
      Nat(n) => n,
    }
  }

  proof fn req_ens(s: Sport)
  {
    assert(sport_nat(s) >= 0) by (lean_proof as a1);
  }

  proof fn box_test(b : NatBox)
  {
    assert(get_data_in_box(b) >= 0) by (lean_proof as a1);
  }

  fn main() 
  {
  }
}