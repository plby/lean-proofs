/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SourceAllLocalDegreeTailDecay

/-! # Canonical local-degree cutoffs and their density-normalized sum -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

def sourceLocalDegreeCutoff (ell j j' t n : ℕ) (p y : ℝ≥0) : ℝ≥0 :=
  t * (sourceNibbleMomentCoefficient ell j' 2 * y * p ^ (3 * (j - 3)) *
    (n : ℝ≥0) ^ (j - 3))

theorem sourceLocalDegreeCutoff_sum
    (ell j q t n : ℕ) (p : ℝ≥0) (y : ℕ → ℝ≥0) :
    (∑ j' ∈ Icc j q, sourceLocalDegreeCutoff ell j j' t n p (y j')) =
      ((t : ℝ≥0) * ∑ j' ∈ Icc j q, sourceNibbleMomentCoefficient ell j' 2 * y j') *
        (p ^ 3) ^ (j - 3) * (n : ℝ≥0) ^ (j - 3) := by
  unfold sourceLocalDegreeCutoff
  rw [pow_mul]
  simp only [mul_sum, sum_mul]
  apply sum_congr rfl
  intro j' hj'
  ring

theorem sourceLocalDegree_kappa_one_le
    (ell j j' n : ℕ) (p y : ℝ≥0) (hy : 1 ≤ y) (hdensity : 1 ≤ p ^ 3 * n) :
    1 ≤ sourceNibbleMomentCoefficient ell j' 2 * y * p ^ (3 * (j - 3)) *
      (n : ℝ≥0) ^ (j - 3) := by
  have hcoeff := sourceNibbleMomentCoefficient_one_le ell j' 2 (by norm_num)
  have hscale : 1 ≤ (p ^ 3 * n) ^ (j - 3) := one_le_pow₀ hdensity
  have h := one_le_mul_of_one_le_of_one_le
    (one_le_mul_of_one_le_of_one_le hcoeff hy) hscale
  simpa only [mul_pow, ← pow_mul, mul_assoc] using h

theorem sourceLocalDegreeCutoff_one_le
    (ell j j' t n : ℕ) (p y : ℝ≥0) (ht : 1 ≤ t)
    (hy : 1 ≤ y) (hdensity : 1 ≤ p ^ 3 * n) :
    1 ≤ sourceLocalDegreeCutoff ell j j' t n p y := by
  exact one_le_mul_of_one_le_of_one_le (by exact_mod_cast ht)
    (sourceLocalDegree_kappa_one_le ell j j' n p y hy hdensity)

theorem eventually_sourceAllLocalCanonicalTail_le
    (ell j q R D s : ℕ) (C B epsilon : ℝ≥0)
    (hs : 3 * R + 1 ≤ s) (hepsilon : 0 < epsilon) :
    ∃ T : ℕ, 1 ≤ T ∧ ∀ t : ℕ, T ≤ t →
      ∀ (N n : ℕ) (p b : ℝ≥0) (y : ℕ → ℝ≥0),
      N ≤ t ^ R → 1 ≤ p ^ 3 * n → (∀ j' ∈ Icc j q, 1 ≤ y j') →
      b ≤ B * (t : ℝ≥0) ^ D * (1 / 2 : ℝ≥0) ^ t →
      (∑ j' ∈ Icc j q, sourceLocalDegreeTailBudget ell j j' s N n p C b (y j')
        (sourceLocalDegreeCutoff ell j j' t n p (y j'))) ≤ epsilon := by
  obtain ⟨T, hT1, hT⟩ := eventually_sourceAllLocalDegreeTailBudget_le ell j q R D s C B epsilon
    hs hepsilon
  refine ⟨T, hT1, fun t ht N n p b y hN hdensity hy hb ↦ ?_⟩
  apply hT t ht N n p b y (fun j' ↦ sourceLocalDegreeCutoff ell j j' t n p (y j')) hN
  · exact fun j' hj' ↦ zero_lt_one.trans_le
      (sourceLocalDegree_kappa_one_le ell j j' n p (y j') (hy j' hj') hdensity)
  · exact fun j' hj' ↦ le_rfl
  · exact fun j' hj' ↦ sourceLocalDegreeCutoff_one_le ell j j' t n p (y j')
      (hT1.trans ht) (hy j' hj') hdensity
  · exact hb

end

end Erdos207
