/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

namespace Erdos368b

def P_plus (m : ℕ) : ℕ :=
  match (Nat.primeFactorsList m).maximum with
  | some p => p
  | none => 1

theorem erdos_368 :
    Filter.Tendsto (fun n => P_plus (n * (n + 1))) Filter.atTop Filter.atTop := by
  sorry

end Erdos368b
