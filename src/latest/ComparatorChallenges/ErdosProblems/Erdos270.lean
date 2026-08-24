/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open Filter

namespace Erdos270

noncomputable def productTerm (n k : ℕ) : ℝ :=
  ((n + 2).ascFactorial k : ℝ)⁻¹

theorem not_erdos_270 :
    ¬ (∀ f : ℕ → ℕ,
      (∀ n, 0 < f n) →
      Tendsto f atTop atTop →
      Irrational (∑' n, productTerm n (f (n + 1)))) := by
  sorry

end Erdos270
