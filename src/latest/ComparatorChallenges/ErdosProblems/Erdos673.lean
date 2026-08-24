/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open Filter Asymptotics
open scoped Topology

namespace Set

noncomputable abbrev partialDensity {β : Type*} [Preorder β] [LocallyFiniteOrderBot β]
    (S : Set β) (A : Set β := Set.univ) (b : β) : ℝ :=
  ((S ∩ A) ∩ Iio b).ncard / (A ∩ Iio b).ncard

def HasDensity {β : Type*} [Preorder β] [LocallyFiniteOrderBot β]
    (S : Set β) (α : ℝ) (A : Set β := Set.univ) : Prop :=
  Tendsto (fun (b : β) => S.partialDensity A b) atTop (𝓝 α)

end Set

namespace Erdos673

def TendsToInfinityAlmostAll (f : ℕ → ℝ) : Prop :=
  ∀ C : ℝ, {n : ℕ | C < f n}.HasDensity 1

def divisorSequence (n : ℕ) : Fin n.divisors.card ↪o ℕ :=
  n.divisors.orderEmbOfFin rfl

noncomputable def G (n : ℕ) : ℝ :=
  ∑ i : Fin (n.divisors.card - 1),
    ((divisorSequence n ⟨i.1, by omega⟩ : ℕ) : ℝ) /
      ((divisorSequence n ⟨i.1 + 1, by omega⟩ : ℕ) : ℝ)

noncomputable def GSum (X : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 X, G n

theorem erdos_673 :
    TendsToInfinityAlmostAll G ∧
      (fun X : ℕ ↦ GSum X) ~[atTop]
        (fun X : ℕ ↦ (X : ℝ) * Real.log X) ∧
      Tendsto (fun X : ℕ ↦ GSum X / (X : ℝ)) atTop atTop := by
  sorry

end Erdos673
