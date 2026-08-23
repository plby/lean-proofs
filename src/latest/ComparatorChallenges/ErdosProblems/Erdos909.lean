/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open Set Topology

noncomputable section

namespace Erdos909

open scoped Classical in
theorem erdos_909 (n : ℕ) (hn : 2 ≤ n) :
    ∃ (S : Type) (_ : TopologicalSpace S),
      smallInductiveDimension S = n ∧
      smallInductiveDimension (S × S) = n := by
  sorry

end Erdos909

end
