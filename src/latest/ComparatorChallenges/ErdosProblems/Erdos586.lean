/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

noncomputable section

namespace Erdos586

open scoped Classical in
theorem erdos_586 (A : List (ℤ × ℕ))
    (hnontrivial : ∀ i : Fin A.length, 1 < (A.get i).2)
    (hcover : ∀ z : ℤ, ∃ i : Fin A.length,
      z ≡ (A.get i).1 [ZMOD (A.get i).2]) :
    ∃ i j : Fin A.length,
      i ≠ j ∧ (A.get i).2 ∣ (A.get j).2 := by
  sorry

end Erdos586

end
