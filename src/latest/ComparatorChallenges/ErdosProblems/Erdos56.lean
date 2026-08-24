/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

namespace Erdos56

def WeaklyDivisible (k : ℕ) (A : Finset ℕ) : Prop :=
    ∀ s ∈ A.powersetCard (k + 1), ¬ Set.Pairwise s Nat.Coprime

noncomputable def MaxWeaklyDivisible (N k : ℕ) : ℕ :=
  sSup { n : ℕ |
    ∃ A : Finset ℕ,
      A ⊆ Finset.Icc 1 N ∧
      WeaklyDivisible k A ∧
      A.card = n }

noncomputable def FirstPrimesMultiples (N k : ℕ) : Finset ℕ :=
    (Finset.Icc 1 N).filter fun i => ∃ j < k, (j.nth Nat.Prime ∣ i)

theorem not_erdos_56 :
    ¬ ((∀ᵉ (N ≥ 2) (k > 0),
          N ≥ k.nth Nat.Prime →
          MaxWeaklyDivisible N k = (FirstPrimesMultiples N k).card)) := by
  sorry

end Erdos56
