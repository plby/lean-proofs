/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

namespace Erdos476

def restrictedSumset {R : Type*} [Add R] [DecidableEq R] (A : Finset R) : Finset R :=
  (A.product A).filter (fun x => x.1 ≠ x.2) |>.image (fun x => x.1 + x.2)

theorem erdos_476 (p : ℕ) [Fact p.Prime] (A : Finset (ZMod p)) :
    (restrictedSumset A).card ≥ min (2 * A.card - 3) p := by
  sorry

end Erdos476
