/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SourceSparseProcessCrude
import ErdosProblems.Erdos207.PreparedLocalDegreeLaw
import ErdosProblems.Erdos207.FiniteBackwardErrorSchedule

/-! # The actual local moment penalties fit a finite global backward error schedule -/

namespace Erdos207

open Finset
open scoped NNReal

def sourceStageRequiredError (q c R m : ℕ) : ℕ :=
  max m (max (3*R+(R*(3*q))*(3*R+3*c)+3*c)
    (6*R+(6*q*R)*(6*R+(c*m+3*c))+(c*m+3*c)))

theorem sourceStageRequiredError_bounds (q c R m : ℕ) :
    m ≤ sourceStageRequiredError q c R m ∧
      3*R+(R*(3*q))*(3*R+3*c)+3*c ≤ sourceStageRequiredError q c R m ∧
      6*R+(6*q*R)*(6*R+(c*m+3*c))+(c*m+3*c) ≤ sourceStageRequiredError q c R m := by
  exact ⟨le_max_left _ _, (le_max_left _ _).trans (le_max_right _ _),
    (le_max_right _ _).trans (le_max_right _ _)⟩

theorem cross_scale_incoming_error
    (t u beta B0 : ℝ≥0) (e required : ℕ) (hu : 1 ≤ u) (hut : u ≤ t)
    (he : required ≤ e) (hbeta : beta ≤ B0/t^e) : beta ≤ B0/u^required := by
  have hu0 := zero_lt_one.trans_le hu
  exact hbeta.trans ((div_le_div_of_nonneg_left zero_le (pow_pos hu0 _) (pow_le_pow_left' hut e)).trans
    (polynomial_incoming_error_budget u B0 e required hu he))

theorem cross_scale_fresh_error
    (t u : ℝ≥0) (c m : ℕ) (ht : 0 < t) (hscale : t ≤ u^c) :
    1/u^(c*m) ≤ 1/t^m := by
  apply one_div_le_one_div_of_le (pow_pos ht m)
  simpa only [pow_mul] using pow_le_pow_left' hscale m

theorem cross_scale_coefficient_error
    (t u coefficient : ℝ≥0) (c decay : ℕ) (hu : 0 < u) (ht : 0 < t)
    (hscale : t ≤ u^c) (hcoefficient : coefficient ≤ u^c) :
    coefficient/u^(c*decay+c) ≤ 1/t^decay := by
  calc
    _ ≤ u^c/u^(c*decay+c) := div_le_div_of_nonneg_right hcoefficient zero_le
    _ = 1/u^(c*decay) := by rw [pow_add]; field_simp
    _ ≤ _ := cross_scale_fresh_error t u c decay ht hscale

theorem cross_scale_auxiliary_degree_failure
    (q s u c : ℕ) (C B0 t : ℝ≥0) (hu : 0 < u) (ht : 0 < t)
    (hscale : t ≤ (u : ℝ≥0)^c)
    (hcoefficient : (∑ j ∈ Icc 4 q, ∑ j' ∈ Icc j q, sourceLocalPolynomialTailCoefficient j' s C B0) ≤
      (u : ℝ≥0)^c) : sourceAllAuxiliaryDegreeFailure q s u (3*c) C B0 ≤ 1/t^2 := by
  have heq : 3*c = c*2+c := by omega
  rw [sourceAllAuxiliaryDegreeFailure, heq]
  exact cross_scale_coefficient_error t u _ c 2 (by exact_mod_cast hu) ht hscale hcoefficient

theorem cross_scale_sparse_prior_failure
    (q s familyCount u c m : ℕ) (C B0 bandError t : ℝ≥0) (hu : 0 < u) (ht : 0 < t)
    (hscale : t ≤ (u : ℝ≥0)^c)
    (hband : bandError ≤ 1/(u : ℝ≥0)^(c*m+3*c))
    (hcoefficient : (familyCount : ℝ≥0)+1+
      (256*(q+1 : ℝ≥0)^2)*(4*C)^(s*(2*q))*
        ((boundedIntersectionMomentCoefficient (2*q) s : ℝ≥0)^s+
          B0*(sourceCrudeUniformWitnessFactor q familyCount*(2 : ℝ≥0)^(6*q))^s) ≤ (u : ℝ≥0)^c) :
    ((familyCount : ℝ≥0)/(u : ℝ≥0)^(c*m+3*c)+bandError+
      sourceSparseCrudeFailure q s familyCount u (c*m+3*c) C B0)/(1/(u : ℝ≥0)^(c*m)) ≤ 1/t^2 := by
  let coefficient : ℝ≥0 := (familyCount : ℝ≥0)+1+
    (256*(q+1 : ℝ≥0)^2)*(4*C)^(s*(2*q))*
      ((boundedIntersectionMomentCoefficient (2*q) s : ℝ≥0)^s+
        B0*(sourceCrudeUniformWitnessFactor q familyCount*(2 : ℝ≥0)^(6*q))^s)
  have hu0 : (0 : ℝ≥0) < u := by exact_mod_cast hu
  have hnum : (familyCount : ℝ≥0)/(u : ℝ≥0)^(c*m+3*c)+bandError+
      sourceSparseCrudeFailure q s familyCount u (c*m+3*c) C B0 ≤
      coefficient/(u : ℝ≥0)^(c*m+3*c) := by
    dsimp only [coefficient, sourceSparseCrudeFailure]
    rw [add_div, add_div]
    exact add_le_add (add_le_add le_rfl hband) le_rfl
  calc
    _ ≤ (coefficient/(u : ℝ≥0)^(c*m+3*c))/(1/(u : ℝ≥0)^(c*m)) :=
      div_le_div_of_nonneg_right hnum zero_le
    _ = coefficient/(u : ℝ≥0)^(c*2+c) := by
      rw [show c*m+3*c = c*m+(c*2+c) by omega, pow_add]
      field_simp
    _ ≤ _ := cross_scale_coefficient_error t u coefficient c 2 hu0 ht hscale hcoefficient

end Erdos207
