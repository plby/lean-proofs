/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import Mathlib

/-!
# Erdős Problem 784

This file formalizes the small-sieve question both as literally printed and
with the intended condition that the sifting set not contain `1`.  The
detailed mathematical proof and the correspondence with the declarations
below are in `tex/784.tex`.
-/

open scoped BigOperators Topology
open Filter Finset

namespace Erdos784

noncomputable section

attribute [local instance] Classical.propDecidable

/-! ## Exact finite formulations -/

/-- Reciprocal mass of a finite set of positive integers. -/
def reciprocalMass (A : Finset ℕ) : ℝ :=
  ∑ a ∈ A, (a : ℝ)⁻¹

/-- Positive integers at most `N` which are divisible by no member of `A`. -/
def unsieved (N : ℕ) (A : Finset ℕ) : Finset ℕ :=
  (Icc 1 N).filter fun n => ∀ a ∈ A, ¬a ∣ n

/-- Integers in the positive prefix removed by at least one modulus. -/
def covered (N : ℕ) (A : Finset ℕ) : Finset ℕ :=
  (Icc 1 N).filter fun n => ∃ a ∈ A, a ∣ n

@[simp] lemma mem_unsieved {N n : ℕ} {A : Finset ℕ} :
    n ∈ unsieved N A ↔ 1 ≤ n ∧ n ≤ N ∧ ∀ a ∈ A, ¬a ∣ n := by
  simp only [unsieved, mem_filter, mem_Icc]
  tauto

@[simp] lemma mem_covered {N n : ℕ} {A : Finset ℕ} :
    n ∈ covered N A ↔ 1 ≤ n ∧ n ≤ N ∧ ∃ a ∈ A, a ∣ n := by
  simp only [covered, mem_filter, mem_Icc]
  tauto

/-- The hypotheses in the problem exactly as printed, allowing `1 ∈ A`. -/
def LiteralAdmissible (C : ℝ) (N : ℕ) (A : Finset ℕ) : Prop :=
  A ⊆ Icc 1 N ∧ reciprocalMass A ≤ C

/-- The intended hypotheses, in which the sifting set is contained in
`{2, ..., N}`. -/
def Admissible (C : ℝ) (N : ℕ) (A : Finset ℕ) : Prop :=
  A ⊆ Icc 2 N ∧ reciprocalMass A ≤ C

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

/-- The customary corrected assertion with `1 ∉ A`. -/
abbrev CorrectedAnswer (C : ℝ) : Prop :=
  HasPolylogLowerBound Admissible C

/-! ## The elementary union bound -/

open scoped ArithmeticFunction.Omega

theorem erdos_784_literal {C : ℝ} (_hC : 0 < C) :
    LiteralAnswer C ↔ C < 1 := by
  sorry

end

end Erdos784
