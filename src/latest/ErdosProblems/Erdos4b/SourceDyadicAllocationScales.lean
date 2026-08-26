/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.SourceDyadicArithmetic

/-!
# Dyadic scale bounds for allocating all cofactor intervals

The logarithmic principal cost is bounded by an absolute multiple of
the primary frontier. The total rounding and common-slack cost vanishes
relative to that frontier for every fixed multiplier.
-/

namespace Erdos4b.SmoothParameters

noncomputable section

open Filter
open scoped Topology

theorem log_scaledResidualCofactorCutoff {D r : ℕ} (hD : 0 < D) (hr : 0 < r) :
    Real.log (D * fullResidualCofactorCutoff r : ℕ) =
      Real.log D + (r : ℝ) * Real.log 2 + (2 : ℝ) ^ r * Real.log 2 + Real.log r := by
  have hDr : (0 : ℝ) < D := by exact_mod_cast hD
  have hrr : (0 : ℝ) < r := by exact_mod_cast hr
  have hcore : (0 : ℝ) < core r := by exact_mod_cast core_pos r
  simp only [fullResidualCofactorCutoff, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  rw [Real.log_mul hDr.ne' (by positivity), Real.log_mul (by positivity) hrr.ne',
    Real.log_mul (by positivity) hcore.ne', Real.log_pow, log_core]
  ring

theorem eventually_log_scaledResidualCofactorCutoff_le {D : ℕ} (hD : 0 < D) :
    ∀ᶠ r in atTop, 1 + Real.log (D * fullResidualCofactorCutoff r : ℕ) ≤ 5 * (2 : ℝ) ^ r := by
  have hpow : Tendsto (fun r : ℕ ↦ (2 : ℝ) ^ r) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  filter_upwards [eventually_ge_atTop 1, hpow.eventually_ge_atTop (1 + Real.log D)] with r hr hconst
  have hrr : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  have hrpow : (r : ℝ) ≤ (2 : ℝ) ^ r := by exact_mod_cast r.lt_two_pow_self.le
  have hlogr : Real.log r ≤ r := (Real.log_le_sub_one_of_pos hrr).trans (by linarith)
  have hlog2 : Real.log 2 ≤ 1 := by
    simpa only [show (2 : ℝ) - 1 = 1 by norm_num] using
      Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
  have hrterm : (r : ℝ) * Real.log 2 ≤ (2 : ℝ) ^ r :=
    (mul_le_of_le_one_right hrr.le hlog2).trans hrpow
  have hpowterm : (2 : ℝ) ^ r * Real.log 2 ≤ (2 : ℝ) ^ r :=
    mul_le_of_le_one_right (by positivity) hlog2
  rw [log_scaledResidualCofactorCutoff hD (by omega)]
  linarith [show (0 : ℝ) ≤ (2 : ℝ) ^ r by positivity]

theorem dyadicInterval_div_companion {r : ℕ} (hr : 0 < r) (a : ℕ) :
    (intervalLength a r : ℝ) / dyadicCompanionScale r =
      (primaryFrontier a r : ℝ) / ((2 : ℝ) ^ r * Real.log 2) := by
  have hrr : (0 : ℝ) < r := by exact_mod_cast hr
  have hcore : (0 : ℝ) < core r := by exact_mod_cast core_pos r
  have hlog : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  simp only [intervalLength, dyadicCompanionScale_eq, smoothExponent, rankinDenominator,
    Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  field_simp

theorem eventually_dyadicAllocationPrincipalScale_le (a : ℕ) {D : ℕ} (hD : 0 < D) :
    ∀ᶠ r in atTop,
      (intervalLength a r : ℝ) * (1 + Real.log (D * fullResidualCofactorCutoff r : ℕ)) /
        dyadicCompanionScale r ≤ 10 * (primaryFrontier a r : ℝ) := by
  filter_upwards [eventually_ge_atTop 1, eventually_log_scaledResidualCofactorCutoff_le hD]
    with r hr hlog
  have hL : 0 < dyadicCompanionScale r := dyadicCompanionScale_pos (by omega)
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  calc
    _ = ((intervalLength a r : ℝ) / dyadicCompanionScale r) *
        (1 + Real.log (D * fullResidualCofactorCutoff r : ℕ)) := by ring
    _ ≤ ((intervalLength a r : ℝ) / dyadicCompanionScale r) * (5 * (2 : ℝ) ^ r) :=
      mul_le_mul_of_nonneg_left hlog (by positivity)
    _ = 5 * (primaryFrontier a r : ℝ) / Real.log 2 := by
      rw [dyadicInterval_div_companion (by omega)]
      field_simp
    _ ≤ 10 * (primaryFrontier a r : ℝ) := (div_le_iff₀ hlog2).mpr (by
      nlinarith [mul_le_mul_of_nonneg_left half_le_log_two
        (show (0 : ℝ) ≤ primaryFrontier a r from Nat.cast_nonneg _)])

theorem scaledResidualCofactorCutoff_mul_log_two (D r : ℕ) :
    (D * fullResidualCofactorCutoff r : ℕ) * Real.log 2 = (D : ℝ) * dyadicCompanionScale r := by
  simp only [fullResidualCofactorCutoff, dyadicCompanionScale_eq, smoothExponent,
    rankinDenominator, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  ring

theorem eventually_dyadicAllocationSlack_le (a D : ℕ) :
    ∀ᶠ r in atTop,
      (D * fullResidualCofactorCutoff r : ℕ) *
          ((primaryFrontier a r : ℝ) / dyadicAmbientScale a r ^ 2 + 1) ≤
        (primaryFrontier a r : ℝ) / 8 := by
  have hV := tendsto_dyadicAmbientScale_atTop a
  have hX : Tendsto (fun r ↦ (primaryFrontier a r : ℝ)) atTop atTop := by
    apply (Real.tendsto_exp_atTop.comp hV).congr
    intro r
    exact Real.exp_log (by exact_mod_cast primaryFrontier_pos a r)
  have hfirst : Tendsto (fun r ↦ 2 * (D : ℝ) / dyadicAmbientScale a r) atTop (𝓝 0) := by
    simpa only [mul_zero, div_eq_mul_inv, Function.comp_def] using
      (tendsto_inv_atTop_zero.comp hV).const_mul (2 * (D : ℝ))
  have hsecond : Tendsto
      (fun r ↦ 2 * (D : ℝ) * dyadicAmbientScale a r / (primaryFrontier a r : ℝ)) atTop (𝓝 0) := by
    simpa only [mul_zero, Function.comp_def, dyadicAmbientScale, id_eq, mul_div_assoc] using
      (Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp hX).const_mul (2 * (D : ℝ))
  have hsmall : ∀ᶠ r in atTop, 2 * (D : ℝ) / dyadicAmbientScale a r +
      2 * (D : ℝ) * dyadicAmbientScale a r / (primaryFrontier a r : ℝ) ≤ 1 / 8 := by
    have h := hfirst.add hsecond
    simp only [add_zero] at h
    exact (h.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 8))).mono fun _ hx ↦ hx.le
  filter_upwards [hsmall, eventually_dyadicCompanionScale_small a 1] with r hr hLsmall
  have hVpos : 0 < dyadicAmbientScale a r := lt_of_lt_of_le (by norm_num)
    (one_le_dyadicAmbientScale a r)
  have hXpos : (0 : ℝ) < primaryFrontier a r := by exact_mod_cast primaryFrontier_pos a r
  have hLV : dyadicCompanionScale r ≤ dyadicAmbientScale a r := by
    simp only [Nat.cast_one, one_mul] at hLsmall
    linarith
  have hcof : ((D * fullResidualCofactorCutoff r : ℕ) : ℝ) ≤
      2 * (D : ℝ) * dyadicAmbientScale a r := by
    have hscale := scaledResidualCofactorCutoff_mul_log_two D r
    have hlo := mul_le_mul_of_nonneg_left half_le_log_two
      (show (0 : ℝ) ≤ (D * fullResidualCofactorCutoff r : ℕ) from Nat.cast_nonneg _)
    have hhi := mul_le_mul_of_nonneg_left hLV (Nat.cast_nonneg (α := ℝ) D)
    nlinarith
  calc
    _ ≤ (2 * (D : ℝ) * dyadicAmbientScale a r) *
        ((primaryFrontier a r : ℝ) / dyadicAmbientScale a r ^ 2 + 1) :=
      mul_le_mul_of_nonneg_right hcof (by positivity)
    _ = (primaryFrontier a r : ℝ) * (2 * (D : ℝ) / dyadicAmbientScale a r +
        2 * (D : ℝ) * dyadicAmbientScale a r / (primaryFrontier a r : ℝ)) := by
      field_simp
    _ ≤ (primaryFrontier a r : ℝ) * (1 / 8) := mul_le_mul_of_nonneg_left hr hXpos.le
    _ = _ := by ring

end

end Erdos4b.SmoothParameters
