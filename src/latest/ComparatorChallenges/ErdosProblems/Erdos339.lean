/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open Filter Function
open scoped Pointwise BigOperators

noncomputable section

namespace Set

variable {M : Type*} [AddCommMonoid M]

open scoped Classical in
def IsAsymptoticAddBasisOfOrder (A : Set M) (o : ℕ) : Prop :=
  ∀ᶠ m in cofinite, m ∈ o • A

end Set

namespace Erdos339

open scoped Classical in
def restrictedSums (r : ℕ) (A : Set ℕ) : Set ℕ :=
  {n | ∃ f : Fin r → ℕ, Injective f ∧ (∀ i, f i ∈ A) ∧ ∑ i, f i = n}

end Erdos339

namespace Set

open scoped Classical in
noncomputable abbrev partialDensity {β : Type*} [Preorder β] [LocallyFiniteOrderBot β]
    (S : Set β) (A : Set β := Set.univ) (b : β) : ℝ :=
  ((S ∩ A) ∩ Iio b).ncard / (A ∩ Iio b).ncard

end Set

namespace Set

open scoped Classical in
noncomputable def lowerDensity {β : Type*} [Preorder β] [LocallyFiniteOrderBot β]
    (S : Set β) (A : Set β := Set.univ) : ℝ :=
  atTop.liminf fun (b : β) ↦ S.partialDensity A b

end Set

namespace Erdos339

open scoped Classical in
theorem erdos_339 {A : Set ℕ} {r : ℕ} (hA : A.IsAsymptoticAddBasisOfOrder r) :
    0 < (restrictedSums r A).lowerDensity := by
  sorry

end Erdos339

end
