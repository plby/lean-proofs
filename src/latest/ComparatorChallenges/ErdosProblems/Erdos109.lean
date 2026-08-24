/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open Filter
open scoped Pointwise

namespace Set

noncomputable abbrev partialDensity {β : Type*} [Preorder β] [LocallyFiniteOrderBot β]
    (S : Set β) (A : Set β := Set.univ) (b : β) : ℝ :=
  ((S ∩ A) ∩ Iio b).ncard / (A ∩ Iio b).ncard

noncomputable def upperDensity {β : Type*} [Preorder β] [LocallyFiniteOrderBot β]
    (S : Set β) (A : Set β := Set.univ) : ℝ :=
  atTop.limsup fun (b : β) ↦ S.partialDensity A b

end Set

namespace Erdos109

theorem erdos_109 (A : Set ℕ) (hA : A.upperDensity > 0) :
    ∃ B C : Set ℕ, B.Infinite ∧ C.Infinite ∧ B + C ⊆ A := by
  sorry

end Erdos109
