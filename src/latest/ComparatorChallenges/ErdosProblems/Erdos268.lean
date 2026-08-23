/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

namespace Erdos268

open Set Filter Topology Matrix
open scoped BigOperators

def harmonicSubseriesSet : Set (Fin 3 → ℝ) :=
  { p | ∃ A : Set ℕ, A.Infinite ∧ (∀ n ∈ A, 0 < n) ∧
    Summable (fun (n : A) => (1 : ℝ) / (n : ℕ)) ∧
    ∀ i : Fin 3, p i = ∑' (n : A), 1 / (((n : ℕ) : ℝ) + ((i : ℕ) : ℝ)) }
noncomputable section

end

noncomputable section

end
end Erdos268


open Set Filter Topology Matrix
open scoped BigOperators

namespace Erdos268

open scoped Classical in
theorem harmonicSubseriesSet_interior_nonempty :
    (interior harmonicSubseriesSet).Nonempty := by
  sorry

end Erdos268
