/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

namespace Erdos923

theorem erdos_923 {V : Type*} (n : ℕ) :
    ∃ k : ℕ, ∀ G : SimpleGraph V, k ≤ G.chromaticNumber →
    ∃ H ≤ G, n ≤ H.chromaticNumber ∧ H.CliqueFree 3 := by
  sorry

end Erdos923
