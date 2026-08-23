/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib



open SimpleGraph

namespace Erdos923

open scoped Classical in
theorem erdos923 {V : Type*} (n : ℕ) :
    ∃ k : ℕ, ∀ G : SimpleGraph V, k ≤ G.chromaticNumber →
    ∃ H ≤ G, n ≤ H.chromaticNumber ∧ H.CliqueFree 3 := by
  sorry

end Erdos923
