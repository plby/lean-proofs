import Mathlib

noncomputable section

attribute [local instance] Classical.propDecidable

namespace Erdos586

theorem erdos_586 (A : List (ℤ × ℕ))
    (hnontrivial : ∀ i : Fin A.length, 1 < (A.get i).2)
    (hcover : ∀ z : ℤ, ∃ i : Fin A.length,
      z ≡ (A.get i).1 [ZMOD (A.get i).2]) :
    ∃ i j : Fin A.length,
      i ≠ j ∧ (A.get i).2 ∣ (A.get j).2 := by
  sorry

end Erdos586

end
