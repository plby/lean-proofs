/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SourceLocalDegreeTailDecay

/-! # One eventual failure threshold for all source configuration orders -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

theorem eventually_sourceAllLocalDegreeTailBudget_le
    (ell j q R D s : ℕ) (C B epsilon : ℝ≥0)
    (hs : 3 * R + 1 ≤ s) (hepsilon : 0 < epsilon) :
    ∃ T : ℕ, 1 ≤ T ∧ ∀ t : ℕ, T ≤ t →
      ∀ (N n : ℕ) (p b : ℝ≥0) (y K : ℕ → ℝ≥0),
      N ≤ t ^ R →
      (∀ j' ∈ Icc j q,
        0 < sourceNibbleMomentCoefficient ell j' 2 * y j' * p ^ (3 * (j - 3)) *
          (n : ℝ≥0) ^ (j - 3)) →
      (∀ j' ∈ Icc j q,
        (t : ℝ≥0) * (sourceNibbleMomentCoefficient ell j' 2 * y j' * p ^ (3 * (j - 3)) *
          (n : ℝ≥0) ^ (j - 3)) ≤ K j') →
      (∀ j' ∈ Icc j q, 1 ≤ K j') →
      b ≤ B * (t : ℝ≥0) ^ D * (1 / 2 : ℝ≥0) ^ t →
      (∑ j' ∈ Icc j q, sourceLocalDegreeTailBudget ell j j' s N n p C b (y j') (K j')) ≤
        epsilon := by
  classical
  let eps := epsilon / (q + 1 : ℝ≥0)
  have heps : 0 < eps := div_pos hepsilon (by positivity)
  have hsingle := fun j' ↦ eventually_sourceLocalDegreeTailBudget_lt ell j j' R D s C B eps hs heps
  let threshold : ℕ → ℕ := fun j' ↦ (hsingle j').choose
  let T := max 1 ((Icc j q).sup threshold)
  refine ⟨T, le_max_left _ _, fun t ht N n p b y K hN hkappa hK hK1 hb ↦ ?_⟩
  have hpoint (j' : ℕ) (hj' : j' ∈ Icc j q) :
      sourceLocalDegreeTailBudget ell j j' s N n p C b (y j') (K j') ≤ eps := by
    have hthreshold : threshold j' ≤ t :=
      (le_sup (f := threshold) hj').trans ((le_max_right 1 _).trans ht)
    exact ((hsingle j').choose_spec.2 t hthreshold N n p (y j') b (K j') hN
      (hkappa j' hj') (hK j' hj') (hK1 j' hj') hb).le
  have hcard : ((Icc j q).card : ℝ≥0) ≤ q + 1 := by
    exact_mod_cast (show (Icc j q).card ≤ q + 1 by rw [Nat.card_Icc]; omega)
  calc
    _ ≤ ∑ _j' ∈ Icc j q, eps := sum_le_sum hpoint
    _ = ((Icc j q).card : ℝ≥0) * eps := by rw [sum_const, nsmul_eq_mul]
    _ ≤ (q + 1 : ℝ≥0) * eps := mul_le_mul_of_nonneg_right hcard zero_le
    _ = epsilon := by dsimp only [eps]; field_simp

end

end Erdos207
