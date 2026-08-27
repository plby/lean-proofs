/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SourceRegularizedCoefficientBound

/-! # Absorbing stage constants before choosing the fixed trajectory envelope -/

namespace Erdos207

open scoped NNReal

noncomputable section

theorem source_regularized_degree_scale_bound_uniform (d : ℕ) (t p tau n C ratio : ℝ≥0)
    (hd : 1 ≤ d) (ht : 1 ≤ t) (hC : 1 ≤ C) (hsmall : C * t * p ≤ tau)
    (hratio : p ^ 2 * tau * n / 24 ≤ ratio) :
    9 * t * C * (p ^ 3 * n) ^ d ≤ (9 * 24 ^ d) * ratio ^ d := by
  have h := source_regularized_degree_scale_bound d (C * t) p tau n 1 ratio hd
    (one_le_mul_of_one_le_of_one_le hC ht) hsmall hratio
  calc
    _ = 9 * (C * t) * 1 * (p ^ 3 * n) ^ d := by ring
    _ ≤ (9 * 1 * 24 ^ d) * ratio ^ d := h
    _ = _ := by ring

theorem regularizedTrajectoryCoefficient_source_uniform_bound
    {I : Type*} [Fintype I] [DecidableEq I] (Lstar : ℕ → Finset (Finset I))
    (A E : ℝ) (d : ℕ) (t p tau n C : ℝ≥0) (hA : 0 < A) (hE : 0 < E)
    (hd : 1 ≤ d) (ht : 1 ≤ t) (hC : 1 ≤ C) (hsmall : C * t * p ≤ tau)
    (hratio : (p : ℝ) ^ 2 * tau * n / 24 ≤ A / E)
    (hdegree : (finiteHypergraphMaxDegree (Lstar (d + 3)) : ℝ≥0) ≤ 9 * t * C * (p ^ 3 * n) ^ d) :
    regularizedTrajectoryCoefficient Lstar A d * E ^ d ≤ (9 * 24 ^ d : ℝ) := by
  let ratio : ℝ≥0 := ⟨A / E, (div_pos hA hE).le⟩
  have hr : p ^ 2 * tau * n / 24 ≤ ratio := by exact_mod_cast hratio
  have hbound := hdegree.trans
    (source_regularized_degree_scale_bound_uniform d t p tau n C ratio hd ht hC hsmall hr)
  apply regularizedTrajectoryCoefficient_scaled_le Lstar A E (9 * 24 ^ d) d hA hE
  exact_mod_cast hbound

end

end Erdos207
