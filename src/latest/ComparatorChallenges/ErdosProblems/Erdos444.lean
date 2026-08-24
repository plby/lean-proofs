/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open Filter

namespace Erdos444

noncomputable def positiveBelow (x : ℝ) : Finset ℕ :=
  Finset.Ico 1 ⌈x⌉₊

noncomputable def divisorCount (A : Set ℕ) (n : ℕ) : ℕ := by
  classical
  exact (n.divisors.filter fun d ↦ d ∈ A).card

noncomputable def maxDivisorCount (A : Set ℕ) (x : ℝ) : ℕ :=
  (positiveBelow x).sup (divisorCount A)

noncomputable def reciprocalMass (A : Set ℕ) (x : ℝ) : ℝ := by
  classical
  exact ∑ a ∈ (positiveBelow x).filter (fun a ↦ a ∈ A), (a : ℝ)⁻¹

noncomputable def ratio (A : Set ℕ) (k : ℕ) (x : ℝ) : ℝ :=
  (maxDivisorCount A x : ℝ) / (reciprocalMass A x) ^ k

theorem erdos_444 :
    ∀ (A : Set ℕ), A.Infinite → ∀ k : ℕ,
      atTop.limsup (fun x : ℝ ↦ (ratio A k x : EReal)) = ⊤ := by
  sorry

end Erdos444
