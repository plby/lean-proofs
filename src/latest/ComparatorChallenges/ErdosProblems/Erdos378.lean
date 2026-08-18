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

namespace Erdos378

def squarefreeBinomialIndices (n : ℕ) : Finset ℕ :=
  (Finset.Ico 1 n).filter fun k ↦ Squarefree (Nat.choose n k)

def squarefreeBinomialCount (n : ℕ) : ℕ :=
  (squarefreeBinomialIndices n).card

def atLeastCountSet (r : ℕ) : Set ℕ :=
  {n | r ≤ squarefreeBinomialCount n}

theorem erdos378 :
    ∀ r : ℕ, ∃ d : ℝ, 0 < d ∧ (atLeastCountSet r).HasDensity d := by
  sorry

end Erdos378
