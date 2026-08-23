/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

namespace Erdos397

def is_solution (M N : List ℕ) : Prop :=
  (M ++ N).Nodup ∧
  (M.map Nat.centralBinom).prod = (N.map Nat.centralBinom).prod
end Erdos397

open Erdos397

namespace Erdos397

open scoped Classical in
theorem infinite_solutions : Set.Infinite { s : List ℕ × List ℕ | is_solution s.1 s.2 } := by
  sorry

end Erdos397
