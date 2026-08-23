import Mathlib

open Finset
open scoped Pointwise

noncomputable section


namespace Erdos806

open scoped Classical in
def Erdos806Statement : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∀ᶠ n : ℕ in Filter.atTop,
      ∀ A : Finset ℕ, A ⊆ Finset.Icc 1 n →
        (A.card : ℝ) ≤ Real.sqrt n →
        ∃ B : Finset ℤ,
          A.map (Nat.castEmbedding : ℕ ↪ ℤ) ⊆ B + B ∧
          (B.card : ℝ) ≤ ε * Real.sqrt n

end Erdos806

namespace Erdos806

open scoped Classical in
theorem erdos_806 : Erdos806Statement := by
  sorry

end Erdos806

end
