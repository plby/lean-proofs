/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos407.AdelicMinimaProduct

/-!
# Coarse individual bounds for adelic successive minima

The product estimates control the successive minima collectively.  The
finite exponent boxing in the exterior-power argument also needs a uniform
polynomial lower bound for each individual minimum.  This file records the
one-vector estimate behind that bound.  It is just the restricted product
formula for a nonzero coordinate, after reconstructing that coordinate from
the local form basis at each of the three places.
-/

namespace Erdos407.PadicSubspace

open scoped BigOperators Matrix

namespace AdelicMinima

open Erdos407 HeightBoxes

/-- A positive, coordinate-independent bound for the coefficients of the
inverse local form matrix at one place. -/
noncomputable def pointLocalConstant {n : ℕ} (L : LocalForms n)
    (v : Place23) : ℝ :=
  1 + ∑ i, ∑ k, realPlaceNorm v (Erdos407.RankDrop.dualCoefficientVector L v i k)

/-- Product of the three local inverse-form constants. -/
noncomputable def pointGlobalConstant {n : ℕ} (L : LocalForms n) : ℝ :=
  ∏ v, pointLocalConstant L v

theorem pointLocalConstant_pos {n : ℕ} (L : LocalForms n) (v : Place23) :
    0 < pointLocalConstant L v := by
  apply add_pos_of_pos_of_nonneg zero_lt_one
  exact Finset.sum_nonneg fun i _ ↦
    Finset.sum_nonneg fun k _ ↦ realPlaceNorm_nonneg v _

theorem pointGlobalConstant_pos {n : ℕ} (L : LocalForms n) :
    0 < pointGlobalConstant L := by
  exact Finset.prod_pos fun v _ ↦ pointLocalConstant_pos L v

/-- Reconstruct one standard coordinate from the values of a nonsingular
local form basis. -/
theorem coordinate_eq_sum_dual {n : ℕ} (L : LocalForms n)
    (hL : IsNonsingularFamily L) (v : Place23) (y : RatVector n)
    (k : Fin n) :
    y k = ∑ i,
      Erdos407.RankDrop.dualCoefficientVector L v i k * L v i y := by
  classical
  let e : RatVector n := Pi.single k 1
  have hrecon := Erdos407.RankDrop.dual_reconstruction L hL v e
  calc
    y k = y ⬝ᵥ e := by simp [e, dotProduct, Pi.single_apply]
    _ = y ⬝ᵥ (∑ i,
        (Erdos407.RankDrop.dualCoefficientVector L v i ⬝ᵥ e) •
          coefficientVector (L v i)) :=
      congrArg (fun u ↦ y ⬝ᵥ u) hrecon.symm
    _ = ∑ i,
        Erdos407.RankDrop.dualCoefficientVector L v i k * L v i y := by
      rw [dotProduct_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [dotProduct_smul]
      simp only [smul_eq_mul]
      rw [dotProduct_comm y, linearForm_eq_dotProduct]
      simp [e, dotProduct, Pi.single_apply]

/-- One-place coordinate bound.  If all row exponents are at most `M`, a
point in the local box has every standard coordinate bounded by the fixed
inverse-form constant times the local minimum factor and `Q^M`. -/
theorem realPlaceNorm_coordinate_le {n : ℕ}
    (L : LocalForms n) (hL : IsNonsingularFamily L)
    {Q : ℕ} (hQ : 1 ≤ Q) (c : LocalConstants n) {M : ℝ}
    (hc : ∀ v i, c v i ≤ M) {y : RatVector n} {lambda : ℝ}
    (hlambda : 0 ≤ lambda)
    (hy : ∀ v i, realPlaceNorm v (L v i y) ≤
      placeScale v lambda * exponentRadius (Q : ℝ) c v i)
    (v : Place23) (k : Fin n) :
    realPlaceNorm v (y k) ≤
      pointLocalConstant L v * placeScale v lambda * (Q : ℝ) ^ M := by
  classical
  rw [coordinate_eq_sum_dual L hL v y k]
  let abv : AbsoluteValue ℚ ℚ :=
    IsAbsoluteValue.toAbsoluteValue (placeNorm v)
  have hsumQ : placeNorm v
      (∑ i, Erdos407.RankDrop.dualCoefficientVector L v i k * L v i y) ≤
      ∑ i, placeNorm v
        (Erdos407.RankDrop.dualCoefficientVector L v i k * L v i y) := by
    exact abv.sum_le Finset.univ _
  have hsumR : realPlaceNorm v
      (∑ i, Erdos407.RankDrop.dualCoefficientVector L v i k * L v i y) ≤
      ∑ i, realPlaceNorm v
        (Erdos407.RankDrop.dualCoefficientVector L v i k * L v i y) := by
    change ((placeNorm v (∑ i,
      Erdos407.RankDrop.dualCoefficientVector L v i k * L v i y) : ℚ) : ℝ) ≤
      ∑ i, ((placeNorm v
        (Erdos407.RankDrop.dualCoefficientVector L v i k * L v i y) : ℚ) : ℝ)
    rw [← Rat.cast_sum]
    exact Rat.cast_le.mpr hsumQ
  calc
    realPlaceNorm v
        (∑ i, Erdos407.RankDrop.dualCoefficientVector L v i k * L v i y) ≤
        ∑ i, realPlaceNorm v
          (Erdos407.RankDrop.dualCoefficientVector L v i k * L v i y) := hsumR
    _ = ∑ i, realPlaceNorm v
          (Erdos407.RankDrop.dualCoefficientVector L v i k) *
            realPlaceNorm v (L v i y) := by
      apply Finset.sum_congr rfl
      intro i _
      exact Erdos407.RankDrop.realPlaceNorm_mul _ _ _
    _ ≤ ∑ i, realPlaceNorm v
          (Erdos407.RankDrop.dualCoefficientVector L v i k) *
            (placeScale v lambda * (Q : ℝ) ^ M) := by
      apply Finset.sum_le_sum
      intro i _
      apply mul_le_mul_of_nonneg_left _ (realPlaceNorm_nonneg v _)
      exact (hy v i).trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hQ) (hc v i))
        (placeScale_nonneg v hlambda))
    _ = (∑ i, realPlaceNorm v
          (Erdos407.RankDrop.dualCoefficientVector L v i k)) *
            (placeScale v lambda * (Q : ℝ) ^ M) := by
      rw [Finset.sum_mul]
    _ ≤ pointLocalConstant L v *
          (placeScale v lambda * (Q : ℝ) ^ M) := by
      apply mul_le_mul_of_nonneg_right _
        (mul_nonneg (placeScale_nonneg v hlambda)
          (Real.rpow_nonneg (Nat.cast_nonneg Q) M))
      dsimp [pointLocalConstant]
      have hk : (∑ i, realPlaceNorm v
          (Erdos407.RankDrop.dualCoefficientVector L v i k)) ≤
          ∑ i, ∑ k, realPlaceNorm v
            (Erdos407.RankDrop.dualCoefficientVector L v i k) := by
        apply Finset.sum_le_sum
        intro i _
        exact Finset.single_le_sum
          (fun j _ ↦ realPlaceNorm_nonneg v _) (Finset.mem_univ k)
      linarith
    _ = pointLocalConstant L v * placeScale v lambda * (Q : ℝ) ^ M := by
      ring

/-- Restricted-product lower estimate for one nonzero `S`-integral point.
The exponent `3 * M` comes from the three retained places. -/
theorem one_le_pointGlobalConstant_mul_lambda {n : ℕ}
    (L : LocalForms n) (hL : IsNonsingularFamily L)
    {Q : ℕ} (hQ : 1 ≤ Q) (c : LocalConstants n) {M : ℝ}
    (hc : ∀ v i, c v i ≤ M) {y : RatVector n} (hy0 : y ≠ 0)
    (hyS : AdelicMinkowski.InZOneSix y) {lambda : ℝ}
    (hlambda : 0 ≤ lambda)
    (hy : ∀ v i, realPlaceNorm v (L v i y) ≤
      placeScale v lambda * exponentRadius (Q : ℝ) c v i) :
    1 ≤ pointGlobalConstant L * lambda * (Q : ℝ) ^ (3 * M) := by
  classical
  obtain ⟨k, hk⟩ : ∃ k, y k ≠ 0 := by
    simpa [funext_iff] using hy0
  have hS := Erdos407.RankDrop.SIntegerSix.of_inZOneSix_coordinate hyS k
  have hproduct : (1 : ℝ) ≤
      ∏ v, realPlaceNorm v (y k) := by
    rw [Erdos407.RankDrop.prod_realPlaceNorm_eq_normProduct23]
    exact_mod_cast Erdos407.RankDrop.SIntegerSix.one_le_normProduct23 hS hk
  have hlocal (v : Place23) :
      realPlaceNorm v (y k) ≤
        pointLocalConstant L v * placeScale v lambda * (Q : ℝ) ^ M :=
    realPlaceNorm_coordinate_le L hL hQ c hc hlambda hy v k
  have hprod : (∏ v, realPlaceNorm v (y k)) ≤
      ∏ v, (pointLocalConstant L v * placeScale v lambda * (Q : ℝ) ^ M) := by
    apply Finset.prod_le_prod
    · intro v _
      exact realPlaceNorm_nonneg v _
    · intro v _
      exact hlocal v
  apply hproduct.trans (hprod.trans_eq ?_)
  simp only [Finset.prod_mul_distrib, pointGlobalConstant]
  rw [prod_placeScale]
  simp only [Finset.prod_const]
  rw [show Finset.univ.card = 3 by decide]
  rw [← Real.rpow_natCast]
  have hQpos : (0 : ℝ) < Q := by exact_mod_cast Nat.zero_lt_of_lt hQ
  rw [← Real.rpow_mul hQpos.le]
  ring

/-- Division form of `one_le_pointGlobalConstant_mul_lambda`. -/
theorem lambda_lower_of_local_bounds {n : ℕ}
    (L : LocalForms n) (hL : IsNonsingularFamily L)
    {Q : ℕ} (hQ : 1 ≤ Q) (c : LocalConstants n) {M : ℝ}
    (hc : ∀ v i, c v i ≤ M) {y : RatVector n} (hy0 : y ≠ 0)
    (hyS : AdelicMinkowski.InZOneSix y) {lambda : ℝ}
    (hlambda : 0 ≤ lambda)
    (hy : ∀ v i, realPlaceNorm v (L v i y) ≤
      placeScale v lambda * exponentRadius (Q : ℝ) c v i) :
    (pointGlobalConstant L * (Q : ℝ) ^ (3 * M))⁻¹ ≤ lambda := by
  have hcore := one_le_pointGlobalConstant_mul_lambda
    L hL hQ c hc hy0 hyS hlambda hy
  have hpos : 0 < pointGlobalConstant L * (Q : ℝ) ^ (3 * M) :=
    mul_pos (pointGlobalConstant_pos L)
      (Real.rpow_pos_of_pos (by exact_mod_cast Nat.zero_lt_of_lt hQ) _)
  apply (inv_le_iff_one_le_mul₀' hpos).2
  simpa [mul_assoc, mul_left_comm, mul_comm] using hcore

end AdelicMinima

end Erdos407.PadicSubspace
