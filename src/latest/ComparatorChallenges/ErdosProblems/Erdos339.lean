import Mathlib

open Filter Function
open scoped Pointwise BigOperators

noncomputable section

attribute [local instance] Classical.propDecidable

namespace Set

variable {M : Type*} [AddCommMonoid M]

def IsAsymptoticAddBasisOfOrder (A : Set M) (o : ℕ) : Prop :=
  ∀ᶠ m in cofinite, m ∈ o • A

end Set

namespace Erdos339

def restrictedSums (r : ℕ) (A : Set ℕ) : Set ℕ :=
  {n | ∃ f : Fin r → ℕ, Injective f ∧ (∀ i, f i ∈ A) ∧ ∑ i, f i = n}

end Erdos339

namespace Set

noncomputable abbrev partialDensity {β : Type*} [Preorder β] [LocallyFiniteOrderBot β]
    (S : Set β) (A : Set β := Set.univ) (b : β) : ℝ :=
  ((S ∩ A) ∩ Iio b).ncard / (A ∩ Iio b).ncard

end Set

namespace Set

noncomputable def lowerDensity {β : Type*} [Preorder β] [LocallyFiniteOrderBot β]
    (S : Set β) (A : Set β := Set.univ) : ℝ :=
  atTop.liminf fun (b : β) ↦ S.partialDensity A b

end Set

namespace Erdos339

theorem erdos_339 {A : Set ℕ} {r : ℕ} (hA : A.IsAsymptoticAddBasisOfOrder r) :
    0 < (restrictedSums r A).lowerDensity := by
  sorry

end Erdos339

end
