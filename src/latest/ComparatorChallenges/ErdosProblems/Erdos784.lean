/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open Finset

namespace Erdos784

/-! ## Exact finite formulations -/

/-- Reciprocal mass of a finite set of positive integers. -/
noncomputable def reciprocalMass (A : Finset ℕ) : ℝ :=
  ∑ a ∈ A, (a : ℝ)⁻¹

/-- Positive integers at most `N` which are divisible by no member of `A`. -/
def unsieved (N : ℕ) (A : Finset ℕ) : Finset ℕ :=
  (Icc 1 N).filter fun n => ∀ a ∈ A, ¬a ∣ n

/-- The hypotheses in the problem exactly as printed, allowing `1 ∈ A`. -/
def LiteralAdmissible (C : ℝ) (N : ℕ) (A : Finset ℕ) : Prop :=
  A ⊆ Icc 1 N ∧ reciprocalMass A ≤ C

/-- The polynomial-logarithmic lower bound asked for in Problem 784, with
all constants and the phrase "sufficiently large" made explicit. -/
def HasPolylogLowerBound
    (admissible : ℝ → ℕ → Finset ℕ → Prop) (C : ℝ) : Prop :=
  ∃ c K : ℝ, 0 < c ∧ 0 < K ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
    ∀ A : Finset ℕ, admissible C N A →
      K * (N : ℝ) / Real.rpow (Real.log (N : ℝ)) c ≤ (unsieved N A).card

/-- The literal assertion from the displayed question. -/
abbrev LiteralAnswer (C : ℝ) : Prop :=
  HasPolylogLowerBound LiteralAdmissible C

theorem erdos_784 {C : ℝ} (_hC : 0 < C) :
    LiteralAnswer C ↔ C < 1 := by
  sorry

end Erdos784
