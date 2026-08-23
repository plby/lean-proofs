/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open Filter
open scoped Topology

namespace Set

@[inline]
noncomputable abbrev partialDensity {β : Type*} [Preorder β] [LocallyFiniteOrderBot β]
    (S : Set β) (A : Set β := Set.univ) (b : β) : ℝ :=
  ((S ∩ A) ∩ Iio b).ncard / (A ∩ Iio b).ncard

def HasDensity {β : Type*} [Preorder β] [LocallyFiniteOrderBot β]
    (S : Set β) (α : ℝ) (A : Set β := Set.univ) : Prop :=
  Tendsto (fun (b : β) => S.partialDensity A b) atTop (𝓝 α)

end Set

namespace Erdos448

def tauPlus (n : ℕ) : ℕ :=
  (n.divisors.image (Nat.log 2)).card

/-- Erdős Problem 448 has a negative answer: for some positive threshold,
the exceptional set has upper density strictly smaller than one. -/

theorem erdos_448 :
    ¬ ∀ ε : ℝ, 0 < ε →
      {n : ℕ | (tauPlus n : ℝ) <
        ε * (n.divisors.card : ℝ)}.HasDensity 1 := by
  sorry
