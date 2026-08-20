import Mathlib

open scoped Pointwise
open Filter

noncomputable section

attribute [local instance] Classical.propDecidable

def IsSidon {α : Type*} [AddCommMonoid α] (A : Set α) : Prop :=
  ∀ᵉ (i₁ ∈ A) (j₁ ∈ A) (i₂ ∈ A) (j₂ ∈ A),
    i₁ + i₂ = j₁ + j₂ → (i₁ = j₁ ∧ i₂ = j₂) ∨ (i₁ = j₂ ∧ i₂ = j₁)

namespace Finset

instance (A : Finset α) [AddCommMonoid α] [DecidableEq α] :
    Decidable (IsSidon (A : Set α)) := by
  refine decidable_of_iff (∀ᵉ (i₁ ∈ A) (j₁ ∈ A) (i₂ ∈ A) (j₂ ∈ A),
    i₁ + i₂ = j₁ + j₂ → (i₁ = j₁ ∧ i₂ = j₂) ∨ (i₁ = j₂ ∧ i₂ = j₁)) ?_
  rfl

def maxSidonSubsetCard {α : Type*} [AddCommMonoid α]
    (A : Finset α) [DecidableEq α] : ℕ :=
  (A.powerset.filter fun B : Finset α ↦ IsSidon (B : Set α)).sup Finset.card

end Finset

namespace Erdos43

noncomputable abbrev f (N : ℕ) : ℕ :=
  Finset.maxSidonSubsetCard (Finset.Icc 1 N)

end Erdos43

namespace Erdos43.erdos_43.parts

theorem i : False ↔
    ∃ C : ℝ, ∀ᶠ N in Filter.atTop, ∀ (A B : Finset ℕ),
      A ⊆ Finset.Icc 1 N →
      B ⊆ Finset.Icc 1 N →
      IsSidon (A : Set ℕ) →
      IsSidon (B : Set ℕ) →
      (A - A) ∩ (B - B) = {0} →
      ((A.card.choose 2 + B.card.choose 2 : ℕ) : ℝ) ≤ ((f N).choose 2 : ℝ) + C := by
  sorry

end Erdos43.erdos_43.parts

namespace Erdos43.erdos_43.parts

theorem ii : False ↔
    ∃ᵉ (c > 0), ∃ o : ℕ → ℝ, o =o[Filter.atTop] (1 : ℕ → ℝ) ∧
    ∀ᶠ N in Filter.atTop, ∀ (A B : Finset ℕ),
      A ⊆ Finset.Icc 1 N →
      B ⊆ Finset.Icc 1 N →
      IsSidon (A : Set ℕ) →
      IsSidon (B : Set ℕ) →
      A.card = B.card →
      (A - A) ∩ (B - B) = {0} →
      ((A.card.choose 2 + B.card.choose 2 : ℕ) : ℝ) ≤
        (1 - c + o N) * ((f N).choose 2 : ℝ) := by
  sorry

end Erdos43.erdos_43.parts

end
