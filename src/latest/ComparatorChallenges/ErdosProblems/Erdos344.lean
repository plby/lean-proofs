/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open Filter

namespace Erdos344

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
