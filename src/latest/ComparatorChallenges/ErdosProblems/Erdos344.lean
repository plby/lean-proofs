import Mathlib

namespace Erdos344

open BigOperators Filter Set
open scoped Pointwise Topology

attribute [local instance] Classical.propDecidable
noncomputable local instance (A : Set ℕ) : DecidablePred A := Classical.decPred A

def subsetSums (A : Set ℕ) : Set ℕ :=
  {n | ∃ B : Finset ℕ, ↑B ⊆ A ∧ n = ∑ b ∈ B, b}

noncomputable def counting (A : Set ℕ) (N : ℕ) : ℕ :=
  by
    classical
    exact ((Finset.Icc 1 N).filter (· ∈ A)).card

def SqrtDense (C : ℝ) (A : Set ℕ) : Prop :=
  ∀ᶠ N : ℕ in atTop, C * Real.sqrt (N : ℝ) ≤ (counting A N : ℝ)

def ContainsInfiniteAP (S : Set ℕ) : Prop :=
  ∃ a d : ℕ, 0 < d ∧ ∀ i : ℕ, a + i * d ∈ S

theorem erdos_344 :
    ∃ C : ℝ, 0 < C ∧ ∀ A : Set ℕ,
      SqrtDense C A → ContainsInfiniteAP (subsetSums A) := by
  sorry

end Erdos344
