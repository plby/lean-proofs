/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos185.Definitions
import ErdosProblems.Erdos185.Geometry

/-!
# The density-Hales--Jewett corollary for Erdős Problem 185

This file isolates the short final deduction from the density Hales--Jewett
theorem for the ternary alphabet.  `DensityHalesJewettThree` is a proposition;
the theorem below takes a proof of it as an ordinary local hypothesis.  A
later file can therefore supply the unconditional proof without putting any
unproved declaration in the environment.
-/

namespace Erdos185

open Filter
open scoped Topology

noncomputable section

/-- The exact specialization of density Hales--Jewett needed for Problem 185:
every sufficiently high-dimensional subset of the ternary cube of density at
least `δ` contains a proper combinatorial line. -/
def DensityHalesJewettThree : Prop :=
  ∀ δ : ℝ, 0 < δ →
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ A : Finset (Word n),
        δ * (3 : ℝ) ^ n ≤ (A.card : ℝ) →
          ContainsCombinatorialLine A

/-- Density Hales--Jewett for the three-letter alphabet implies that the
maximum size of a geometric-line-free subset of the ternary cube is little-o
of the size of the cube. -/
theorem f3_isLittleO_three_pow_of_densityHalesJewettThree
    (hDHJ : DensityHalesJewettThree) :
    Asymptotics.IsLittleO Filter.atTop
      (fun n : ℕ ↦ (f3 n : ℝ))
      (fun n : ℕ ↦ (3 : ℝ) ^ n) := by
  rw [Asymptotics.isLittleO_iff]
  intro δ hδ
  obtain ⟨N, hN⟩ := hDHJ δ hδ
  filter_upwards [eventually_ge_atTop N] with n hn
  obtain ⟨A, hA, hcard⟩ := exists_isMoserSet_card_eq_f3 n
  have hnotDense : ¬ δ * (3 : ℝ) ^ n ≤ (A.card : ℝ) := by
    intro hDense
    exact hA.not_containsCombinatorialLine (hN n hn A hDense)
  have hbound : (f3 n : ℝ) ≤ δ * (3 : ℝ) ^ n := by
    rw [← hcard]
    exact le_of_not_ge hnotDense
  have hf : |(f3 n : ℝ)| = (f3 n : ℝ) :=
    abs_of_nonneg (show (0 : ℝ) ≤ (f3 n : ℝ) from Nat.cast_nonneg _)
  have hg : |(3 : ℝ) ^ n| = (3 : ℝ) ^ n :=
    abs_of_nonneg (pow_nonneg (by norm_num) n)
  simpa only [Real.norm_eq_abs, hf, hg] using hbound

end

end Erdos185
