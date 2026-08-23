/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos1166.Erdos1166HLOZEventIdentity
import ErdosProblems.Erdos1166.Erdos1166HLOZNearCriticalBridge

/-!
The deterministic and analytic time-change argument in Hao--Li--Okada--Zheng,
Lemma 2.6.  The only probabilistic input is the precisely named
Proposition-1.3 lower-deviation inequality.  This file proves the pathwise
stopping-time inclusion, controls the floor in the integer comparison horizon,
checks the powers and constants, and supplies both the pointwise and finite
union probability bounds.

The source application uses a small positive `δ`.  We work in the full range
`0 < δ < 2/5`, where the correction in (2.20) is lower order than its leading
term; this includes the parameter `δ = 7/5 - 4κ₁` used with
`κ₁ ∈ (1/3, 7/20)` in Propositions 4.4 and 4.5.
-/

namespace Erdos1166
namespace HLOZTimeChange

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

/-- The leading term `sqrt(π m)` in `log ψ_m`. -/
noncomputable def leadingLogTerm (m : ℕ) : ℝ :=
  Real.pi ^ ((1 : ℝ) / 2) * (m : ℝ) ^ ((1 : ℝ) / 2)

/-- The correction term in HLOZ (2.20). -/
noncomputable def correctionLogTerm (d : ℝ) (m : ℕ) : ℝ :=
  Real.pi ^ ((13 : ℝ) / 10 + d / 2) *
    (m : ℝ) ^ ((3 : ℝ) / 10 + d / 2)

/-- The exponent `8/5 + δ` in Proposition 1.3. -/
noncomputable def lowerDeviationExponent (d : ℝ) : ℝ := (8 : ℝ) / 5 + d

/-- The cross term produced by squaring `log ψ_m`. -/
noncomputable def crossTerm (d : ℝ) (m : ℕ) : ℝ :=
  Real.pi ^ ((4 : ℝ) / 5 + d / 2) *
    (m : ℝ) ^ ((4 : ℝ) / 5 + d / 2)

/-- The logarithm of the real horizon `ψ_m(δ)` from HLOZ (2.20). -/
noncomputable def lemma26LogHorizon (d : ℝ) (m : ℕ) : ℝ :=
  leadingLogTerm m + correctionLogTerm d m

/-- The floor of the real horizon `ψ_m(δ)`, appropriate for discrete time. -/
noncomputable def lemma26Horizon (d : ℝ) (m : ℕ) : ℕ := ⌊Real.exp (lemma26LogHorizon d m)⌋₊

/-- The lower-deviation threshold in Proposition 1.3. -/
noncomputable def proposition13Threshold (d : ℝ) (n : ℕ) : ℝ :=
  Real.log (n : ℝ) ^ 2 / Real.pi -
    Real.log (n : ℝ) ^ lowerDeviationExponent d

lemma leadingLogTerm_sq_div_pi (m : ℕ) (hm : 0 < m) : leadingLogTerm m ^ 2 / Real.pi = (m : ℝ) := by
  rw [leadingLogTerm, mul_pow]
  have hm0 : 0 < (m : ℝ) := by exact_mod_cast hm
  rw [pow_two (Real.pi ^ ((1 : ℝ) / 2)),
    pow_two ((m : ℝ) ^ ((1 : ℝ) / 2)),
    ← Real.rpow_add Real.pi_pos, ← Real.rpow_add hm0]
  rw [show ((1 : ℝ) / 2) + 1 / 2 = 1 by norm_num]
  rw [Real.rpow_one, Real.rpow_one]
  field_simp

lemma leading_mul_correction_div_pi (d : ℝ) (m : ℕ) (hm : 0 < m) :
    leadingLogTerm m * correctionLogTerm d m / Real.pi = crossTerm d m := by
  rw [leadingLogTerm, correctionLogTerm, crossTerm]
  have hpi : 0 < Real.pi := Real.pi_pos
  have hm0 : 0 < (m : ℝ) := by exact_mod_cast hm
  rw [mul_mul_mul_comm]
  rw [← Real.rpow_add hpi, ← Real.rpow_add hm0]
  rw [div_eq_mul_inv]
  calc
    _ = (Real.pi ^ ((1 : ℝ) / 2 + (13 / 10 + d / 2)) * Real.pi⁻¹) *
        (m : ℝ) ^ ((1 : ℝ) / 2 + (3 / 10 + d / 2)) := by ring
    _ = (Real.pi ^ ((1 : ℝ) / 2 + (13 / 10 + d / 2)) *
        Real.pi ^ (-(1 : ℝ))) *
        (m : ℝ) ^ ((1 : ℝ) / 2 + (3 / 10 + d / 2)) := by
      rw [Real.rpow_neg hpi.le, Real.rpow_one]
    _ = _ := by
      rw [← Real.rpow_add hpi]
      congr 1 <;> ring_nf

lemma leading_rpow_lowerDeviationExponent (d : ℝ) (m : ℕ) (hm : 0 < m) :
    leadingLogTerm m ^ lowerDeviationExponent d = crossTerm d m := by
  rw [leadingLogTerm, crossTerm, Real.mul_rpow (Real.rpow_nonneg _ _) (Real.rpow_nonneg _ _)]
  have hpi : 0 ≤ Real.pi := Real.pi_pos.le
  have hm0 : 0 ≤ (m : ℝ) := by positivity
  rw [← Real.rpow_mul hpi, ← Real.rpow_mul hm0]
  congr 1 <;> rw [lowerDeviationExponent] <;> ring_nf
  all_goals positivity

lemma correction_div_leading_tendsto (d : ℝ) (hd : d < 2 / 5) :
    Tendsto (fun m : ℕ ↦ correctionLogTerm d m / leadingLogTerm m) atTop (nhds 0) := by
  have he : (3 : ℝ) / 10 + d / 2 - 1 / 2 < 0 := by linarith
  have ht : Tendsto
      (fun m : ℕ ↦ (m : ℝ) ^ ((3 : ℝ) / 10 + d / 2 - 1 / 2))
      atTop (nhds 0) := by
    have ht0 := (tendsto_rpow_neg_atTop (by linarith :
      0 < (1 : ℝ) / 5 - d / 2)).comp tendsto_natCast_atTop_atTop
    convert ht0 using 1
    funext m
    congr 1
    ring
  have hc : Tendsto
      (fun _m : ℕ ↦ Real.pi ^ ((13 : ℝ) / 10 + d / 2 - 1 / 2))
      atTop (nhds (Real.pi ^ ((13 : ℝ) / 10 + d / 2 - 1 / 2))) :=
    tendsto_const_nhds
  have hmul := hc.mul ht
  rw [mul_zero] at hmul
  apply hmul.congr'
  filter_upwards [eventually_gt_atTop 0] with m hm
  have hm0 : 0 < (m : ℝ) := by exact_mod_cast hm
  rw [leadingLogTerm, correctionLogTerm, mul_div_mul_comm]
  rw [← Real.rpow_sub Real.pi_pos, ← Real.rpow_sub hm0]

lemma leadingLogTerm_tendsto : Tendsto leadingLogTerm atTop atTop := by
  unfold leadingLogTerm
  exact (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp
    tendsto_natCast_atTop_atTop |>.const_mul_atTop
      (Real.rpow_pos_of_pos Real.pi_pos _)

lemma eventually_log_lemma26Horizon_between (d : ℝ) : ∀ᶠ m : ℕ in atTop,
    lemma26LogHorizon d m - 1 ≤ Real.log (lemma26Horizon d m : ℝ) ∧
      Real.log (lemma26Horizon d m : ℝ) ≤ lemma26LogHorizon d m := by
  have hA : Tendsto leadingLogTerm atTop atTop := by
    unfold leadingLogTerm
    exact (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp
      tendsto_natCast_atTop_atTop |>.const_mul_atTop
        (Real.rpow_pos_of_pos Real.pi_pos _)
  filter_upwards [hA.eventually_gt_atTop 1, eventually_gt_atTop 0] with m hA1 hm
  have hm0 : 0 < (m : ℝ) := by exact_mod_cast hm
  have hB0 : 0 < correctionLogTerm d m := by
    exact mul_pos (Real.rpow_pos_of_pos Real.pi_pos _)
      (Real.rpow_pos_of_pos hm0 _)
  have hL1 : 1 < lemma26LogHorizon d m := by rw [lemma26LogHorizon]; linarith
  have hexp2 : 2 < Real.exp (lemma26LogHorizon d m) :=
    Real.exp_one_gt_two.trans_le (Real.exp_le_exp.mpr hL1.le)
  have hfloorPos : 0 < lemma26Horizon d m := by
    rw [lemma26Horizon, Nat.floor_pos]
    linarith
  have hfloorUpper : ((lemma26Horizon d m : ℕ) : ℝ) ≤ Real.exp (lemma26LogHorizon d m) := by
    exact Nat.floor_le (Real.exp_pos _).le
  have hfloorLower : Real.exp (lemma26LogHorizon d m) / 2 ≤ ((lemma26Horizon d m : ℕ) : ℝ) := by
    have hlt : Real.exp (lemma26LogHorizon d m) - 1 < ((lemma26Horizon d m : ℕ) : ℝ) := by
      have := Nat.lt_floor_add_one (Real.exp (lemma26LogHorizon d m))
      change Real.exp (lemma26LogHorizon d m) < ((lemma26Horizon d m : ℕ) : ℝ) + 1 at this
      linarith
    have : Real.exp (lemma26LogHorizon d m) / 2 ≤ Real.exp (lemma26LogHorizon d m) - 1 := by linarith
    exact this.trans hlt.le
  constructor
  · rw [Real.le_log_iff_exp_le (by positivity : (0 : ℝ) < lemma26Horizon d m)]
    calc
      Real.exp (lemma26LogHorizon d m - 1) = Real.exp (lemma26LogHorizon d m) / Real.exp 1 := by
        rw [Real.exp_sub]
      _ ≤ Real.exp (lemma26LogHorizon d m) / 2 := by
        exact div_le_div_of_nonneg_left (Real.exp_pos _).le (by norm_num)
          Real.exp_one_gt_two.le
      _ ≤ _ := hfloorLower
  · simpa only [Real.log_exp] using
      Real.log_le_log (by positivity : (0 : ℝ) < lemma26Horizon d m) hfloorUpper

lemma eventually_level_lt_proposition13Threshold (d : ℝ) (hd0 : 0 < d) (hd2 : d < 2 / 5) :
    ∀ᶠ m : ℕ in atTop, (m : ℝ) < proposition13Threshold d (lemma26Horizon d m) := by
  have hr1 : 1 < lowerDeviationExponent d := by rw [lowerDeviationExponent]; linarith
  have hr2 : lowerDeviationExponent d < 2 := by rw [lowerDeviationExponent]; linarith
  have hratio := correction_div_leading_tendsto d hd2
  have hbsmall : ∀ᶠ m : ℕ in atTop, correctionLogTerm d m / leadingLogTerm m < (1 : ℝ) / 4 :=
    hratio.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4))
  have hArpow : Tendsto (fun m : ℕ ↦ leadingLogTerm m ^ (lowerDeviationExponent d - 1)) atTop atTop :=
    (tendsto_rpow_atTop (by linarith : 0 < lowerDeviationExponent d - 1)).comp leadingLogTerm_tendsto
  have hDlarge : ∀ᶠ m : ℕ in atTop, 4 * leadingLogTerm m ≤ crossTerm d m := by
    filter_upwards [hArpow.eventually_gt_atTop 4, eventually_gt_atTop 0] with m hpow hm
    have hA0 : 0 < leadingLogTerm m := by
      exact mul_pos (Real.rpow_pos_of_pos Real.pi_pos _)
        (Real.rpow_pos_of_pos (by exact_mod_cast hm) _)
    rw [← leading_rpow_lowerDeviationExponent d m hm]
    rw [show lowerDeviationExponent d = (lowerDeviationExponent d - 1) + 1 by ring, Real.rpow_add hA0,
      Real.rpow_one]
    nlinarith
  filter_upwards [eventually_log_lemma26Horizon_between d, hbsmall, hDlarge,
    leadingLogTerm_tendsto.eventually_gt_atTop 4, eventually_gt_atTop 0] with
      m hlog hbsmall hDlarge hA4 hm
  have hm0 : 0 < (m : ℝ) := by exact_mod_cast hm
  have hA0 : 0 < leadingLogTerm m := by
    exact mul_pos (Real.rpow_pos_of_pos Real.pi_pos _)
      (Real.rpow_pos_of_pos hm0 _)
  have hB0 : 0 < correctionLogTerm d m := by
    exact mul_pos (Real.rpow_pos_of_pos Real.pi_pos _)
      (Real.rpow_pos_of_pos hm0 _)
  have hBsmall : correctionLogTerm d m ≤ leadingLogTerm m / 4 := by
    have := (div_lt_iff₀ hA0).mp hbsmall
    linarith
  have hL0 : 0 < lemma26LogHorizon d m := by rw [lemma26LogHorizon]; positivity
  have hLupper : lemma26LogHorizon d m ≤ (5 / 4 : ℝ) * leadingLogTerm m := by
    rw [lemma26LogHorizon]
    linarith
  have hlog0 : 0 < Real.log (lemma26Horizon d m : ℝ) := by
    exact lt_of_lt_of_le (by rw [lemma26LogHorizon]; linarith : 0 < lemma26LogHorizon d m - 1) hlog.1
  have hpowFive : (5 / 4 : ℝ) ^ lowerDeviationExponent d ≤ (25 / 16 : ℝ) := by
    calc
      (5 / 4 : ℝ) ^ lowerDeviationExponent d ≤ (5 / 4 : ℝ) ^ (2 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) hr2.le
      _ = 25 / 16 := by norm_num [Real.rpow_def_of_pos]
  have hLpow : lemma26LogHorizon d m ^ lowerDeviationExponent d ≤ (25 / 16 : ℝ) * crossTerm d m := by
    calc
      lemma26LogHorizon d m ^ lowerDeviationExponent d ≤ ((5 / 4 : ℝ) * leadingLogTerm m) ^ lowerDeviationExponent d :=
        Real.rpow_le_rpow hL0.le hLupper (by linarith)
      _ = (5 / 4 : ℝ) ^ lowerDeviationExponent d * (leadingLogTerm m ^ lowerDeviationExponent d) := by
        rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 5 / 4) hA0.le]
      _ ≤ (25 / 16 : ℝ) * crossTerm d m := by
        rw [leading_rpow_lowerDeviationExponent d m hm]
        exact mul_le_mul_of_nonneg_right hpowFive (by unfold crossTerm; positivity)
  have hlogPow : Real.log (lemma26Horizon d m : ℝ) ^ lowerDeviationExponent d ≤
      (25 / 16 : ℝ) * crossTerm d m := by
    exact (Real.rpow_le_rpow hlog0.le hlog.2 (by linarith)).trans hLpow
  have hsqLower : (lemma26LogHorizon d m - 1) ^ 2 / Real.pi ≤
      Real.log (lemma26Horizon d m : ℝ) ^ 2 / Real.pi := by
    have hLm1 : 0 ≤ lemma26LogHorizon d m - 1 := by rw [lemma26LogHorizon]; linarith
    have hsquare : (lemma26LogHorizon d m - 1) ^ 2 ≤ Real.log (lemma26Horizon d m : ℝ) ^ 2 := by
      have hprod : 0 ≤
          (Real.log (lemma26Horizon d m : ℝ) - (lemma26LogHorizon d m - 1)) *
            (Real.log (lemma26Horizon d m : ℝ) + (lemma26LogHorizon d m - 1)) := by
        exact mul_nonneg (sub_nonneg.mpr hlog.1) (add_nonneg hlog0.le hLm1)
      nlinarith
    exact div_le_div_of_nonneg_right hsquare Real.pi_pos.le
  have hLsq : lemma26LogHorizon d m ^ 2 / Real.pi =
      (m : ℝ) + 2 * crossTerm d m + correctionLogTerm d m ^ 2 / Real.pi := by
    rw [lemma26LogHorizon]
    calc
      (leadingLogTerm m + correctionLogTerm d m) ^ 2 / Real.pi =
          leadingLogTerm m ^ 2 / Real.pi + 2 * (leadingLogTerm m * correctionLogTerm d m / Real.pi) +
            correctionLogTerm d m ^ 2 / Real.pi := by ring
      _ = _ := by rw [leadingLogTerm_sq_div_pi m hm, leading_mul_correction_div_pi d m hm]
  have hloss : 2 * lemma26LogHorizon d m / Real.pi ≤ (5 / 4 : ℝ) * leadingLogTerm m := by
    calc
      2 * lemma26LogHorizon d m / Real.pi ≤ lemma26LogHorizon d m := by
        rw [div_le_iff₀ Real.pi_pos]
        nlinarith [Real.two_le_pi, hL0.le]
      _ ≤ _ := hLupper
  have hlossD : 2 * lemma26LogHorizon d m / Real.pi ≤ (5 / 16 : ℝ) * crossTerm d m := by
    nlinarith
  rw [proposition13Threshold]
  have hBsq : 0 ≤ correctionLogTerm d m ^ 2 / Real.pi := div_nonneg (sq_nonneg _) Real.pi_pos.le
  have honePi : 0 ≤ (1 : ℝ) / Real.pi := by positivity
  have hLm1sq : (lemma26LogHorizon d m - 1) ^ 2 / Real.pi =
      lemma26LogHorizon d m ^ 2 / Real.pi - 2 * lemma26LogHorizon d m / Real.pi + 1 / Real.pi := by ring
  calc
    (m : ℝ) < (lemma26LogHorizon d m - 1) ^ 2 / Real.pi -
        (25 / 16 : ℝ) * crossTerm d m := by
      rw [hLm1sq, hLsq]
      nlinarith
    _ ≤ Real.log (lemma26Horizon d m : ℝ) ^ 2 / Real.pi -
        Real.log (lemma26Horizon d m : ℝ) ^ lowerDeviationExponent d := by
      linarith

lemma eventually_prop13_tail_le_exp_neg_level (d C : ℝ) (hC : 0 < C) :
    ∀ᶠ m : ℕ in atTop,
      C * Real.exp (-Real.exp (Real.log (lemma26Horizon d m : ℝ) ^ ((3 : ℝ) / 5))) ≤
        Real.exp (-(m : ℝ)) := by
  have hx : Tendsto (fun m : ℕ ↦ leadingLogTerm m - 1) atTop atTop := by
    rw [tendsto_atTop]
    intro b
    filter_upwards [leadingLogTerm_tendsto.eventually_ge_atTop (b + 1)] with m hm
    linarith
  have hy : Tendsto (fun m : ℕ ↦ (leadingLogTerm m - 1) ^ ((3 : ℝ) / 5)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 3 / 5)).comp hx
  have hratio : Tendsto
      (fun m : ℕ ↦ Real.exp ((leadingLogTerm m - 1) ^ ((3 : ℝ) / 5)) /
        ((leadingLogTerm m - 1) ^ ((3 : ℝ) / 5)) ^ ((10 : ℝ) / 3))
      atTop atTop := (tendsto_exp_div_rpow_atTop ((10 : ℝ) / 3)).comp hy
  filter_upwards [eventually_log_lemma26Horizon_between d, hx.eventually_gt_atTop 1,
    hratio.eventually_gt_atTop 3,
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 2)).comp hx
      |>.eventually_gt_atTop C,
    eventually_gt_atTop 0] with m hlog hx1 hratio3 hxSqC hm
  have hm0 : 0 < (m : ℝ) := by exact_mod_cast hm
  have hA0 : 0 < leadingLogTerm m := by
    exact mul_pos (Real.rpow_pos_of_pos Real.pi_pos _)
      (Real.rpow_pos_of_pos hm0 _)
  have hx0 : 0 < leadingLogTerm m - 1 := by linarith
  have hy0 : 0 < (leadingLogTerm m - 1) ^ ((3 : ℝ) / 5) :=
    Real.rpow_pos_of_pos hx0 _
  have hypow : ((leadingLogTerm m - 1) ^ ((3 : ℝ) / 5)) ^ ((10 : ℝ) / 3) =
      (leadingLogTerm m - 1) ^ 2 := by
    rw [← Real.rpow_mul hx0.le]
    norm_num
  rw [hypow] at hratio3
  have hxSq : C ≤ (leadingLogTerm m - 1) ^ 2 := by
    exact le_of_lt (by simpa [Real.rpow_natCast] using hxSqC)
  have hmLe : (m : ℝ) ≤ 2 * (leadingLogTerm m - 1) ^ 2 := by
    have hAsq := leadingLogTerm_sq_div_pi m hm
    have hpi2 := Real.two_le_pi
    rw [div_eq_iff Real.pi_ne_zero] at hAsq
    have hAupper : leadingLogTerm m ≤ 2 * (leadingLogTerm m - 1) := by linarith
    have hsqUpper : leadingLogTerm m ^ 2 ≤ 4 * (leadingLogTerm m - 1) ^ 2 := by nlinarith
    nlinarith
  have hExpLarge : (m : ℝ) + C ≤
      Real.exp ((leadingLogTerm m - 1) ^ ((3 : ℝ) / 5)) := by
    have hdenPos : 0 < (leadingLogTerm m - 1) ^ 2 := sq_pos_of_pos hx0
    have := (lt_div_iff₀ hdenPos).mp hratio3
    nlinarith
  have hlogC : Real.log C ≤ C := Real.log_le_self hC.le
  have hpowMono : (leadingLogTerm m - 1) ^ ((3 : ℝ) / 5) ≤
      Real.log (lemma26Horizon d m : ℝ) ^ ((3 : ℝ) / 5) := by
    have hAxLog : leadingLogTerm m - 1 ≤ Real.log (lemma26Horizon d m : ℝ) := by
      have hB0 : 0 < correctionLogTerm d m := by
        exact mul_pos (Real.rpow_pos_of_pos Real.pi_pos _)
          (Real.rpow_pos_of_pos hm0 _)
      have : leadingLogTerm m - 1 ≤ lemma26LogHorizon d m - 1 := by rw [lemma26LogHorizon]; linarith
      exact this.trans hlog.1
    exact Real.rpow_le_rpow hx0.le hAxLog (by norm_num)
  have hExpMono : Real.exp ((leadingLogTerm m - 1) ^ ((3 : ℝ) / 5)) ≤
      Real.exp (Real.log (lemma26Horizon d m : ℝ) ^ ((3 : ℝ) / 5)) :=
    Real.exp_le_exp.mpr hpowMono
  have hexponent : Real.log C -
      Real.exp (Real.log (lemma26Horizon d m : ℝ) ^ ((3 : ℝ) / 5)) ≤ -(m : ℝ) := by
    linarith
  calc
    C * Real.exp (-Real.exp (Real.log (lemma26Horizon d m : ℝ) ^ ((3 : ℝ) / 5))) =
        Real.exp (Real.log C) *
          Real.exp (-Real.exp (Real.log (lemma26Horizon d m : ℝ) ^ ((3 : ℝ) / 5))) := by
      rw [Real.exp_log hC]
    _ = Real.exp (Real.log C +
          -Real.exp (Real.log (lemma26Horizon d m : ℝ) ^ ((3 : ℝ) / 5))) := by
      rw [Real.exp_add]
    _ =
        Real.exp (Real.log C -
          Real.exp (Real.log (lemma26Horizon d m : ℝ) ^ ((3 : ℝ) / 5))) := by
      congr 1
    _ ≤ Real.exp (-(m : ℝ)) := Real.exp_le_exp.mpr hexponent

/-- The precise lower-deviation estimate from HLOZ Proposition 1.3, isolated
as the sole probabilistic input to the time-change argument. -/
def Prop13LowerDeviationBound (d C : ℝ) : Prop :=
  ∀ n : ℕ,
    simpleRandomWalkLaw
        {s | (maxLocalTime s n : ℝ) < proposition13Threshold d n} ≤
      ENNReal.ofReal
        (C * Real.exp
          (-Real.exp (Real.log (n : ℝ) ^ ((3 : ℝ) / 5))))

/-- The integer-time form of HLOZ's event
`{T_m^k > psi_m(d)} inter M_m^k`.  Since `T_m^k` is integer-valued,
`T_m^k > psi_m(d)` is exactly `floor(psi_m(d)) < T_m^k`. -/
def lateThresholdOnLevel (d : ℝ) (m k : ℕ) : Set (ℕ → Site) :=
  {s | (lemma26Horizon d m : WithTop ℕ) < firstKSitesReachLevel m k s} ∩
    hlozThresholdTimeEventK m k

/-- On the late-threshold event, the maximal local time at the comparison
horizon has not yet exceeded `m`. -/
theorem lateThresholdOnLevel_subset_maxLocalTime_le (d : ℝ) (m k : ℕ) :
    lateThresholdOnLevel d m k ⊆
      {s | maxLocalTime s (lemma26Horizon d m) ≤ m} := by
  intro s hs
  rcases hs with ⟨hlate, hM⟩
  change (lemma26Horizon d m : WithTop ℕ) < firstKSitesReachLevel m k s at hlate
  change firstKSitesReachLevel m k s <
    firstKSitesReachLevel (m + 1) 1 s at hM
  have hbefore : (lemma26Horizon d m : WithTop ℕ) <
      firstKSitesReachLevel (m + 1) 1 s := hlate.trans hM
  have hnot :
      (sitesAtLeastLevel s (lemma26Horizon d m) (m + 1)).card ∉ Set.Ici 1 := by
    exact notMem_of_lt_hittingAfter
      (u := fun n s => (sitesAtLeastLevel s n (m + 1)).card)
      (s := Set.Ici 1) (n := 0) (ω := s) hbefore (Nat.zero_le _)
  have hzero : (sitesAtLeastLevel s (lemma26Horizon d m) (m + 1)).card = 0 := by
    simp only [Set.mem_Ici, not_le] at hnot
    omega
  have hmaxlt : maxLocalTime s (lemma26Horizon d m) < m + 1 :=
    (card_sitesAtLeastLevel_eq_zero_iff_max_lt s (lemma26Horizon d m) (m + 1)).mp hzero
  change maxLocalTime s (lemma26Horizon d m) ≤ m
  omega

/-- Eventual, uniform-in-`k` form of HLOZ Lemma 2.6.  Proposition 1.3 is
the only probabilistic hypothesis; all time-change and interpolation steps are
proved in this file. -/
theorem hlozLemma26_eventually_of_prop13
    (d C : ℝ) (hd : 0 < d) (hdUpper : d < (2 : ℝ) / 5)
    (hC : 0 < C) (hProp13 : Prop13LowerDeviationBound d C) :
    ∀ᶠ m in atTop, ∀ k : ℕ, 1 ≤ k →
      simpleRandomWalkLaw (lateThresholdOnLevel d m k) ≤
        ENNReal.ofReal (Real.exp (-(m : ℝ))) := by
  filter_upwards [eventually_level_lt_proposition13Threshold d hd hdUpper,
    eventually_prop13_tail_le_exp_neg_level d C hC] with m hthreshold htail
  intro k _hk
  calc
    simpleRandomWalkLaw (lateThresholdOnLevel d m k) ≤
        simpleRandomWalkLaw {s | maxLocalTime s (lemma26Horizon d m) ≤ m} :=
      measure_mono (lateThresholdOnLevel_subset_maxLocalTime_le d m k)
    _ ≤ simpleRandomWalkLaw
        {s | (maxLocalTime s (lemma26Horizon d m) : ℝ) < proposition13Threshold d (lemma26Horizon d m)} := by
      apply measure_mono
      intro s hs
      exact lt_of_le_of_lt (by exact_mod_cast hs) hthreshold
    _ ≤ ENNReal.ofReal
        (C * Real.exp
          (-Real.exp (Real.log (lemma26Horizon d m : ℝ) ^ ((3 : ℝ) / 5)))) :=
      hProp13 (lemma26Horizon d m)
    _ ≤ ENNReal.ofReal (Real.exp (-(m : ℝ))) :=
      ENNReal.ofReal_le_ofReal htail

/-- Quantified-tail form of `hlozLemma26_eventually_of_prop13`. -/
theorem hlozLemma26_of_prop13
    (d C : ℝ) (hd : 0 < d) (hdUpper : d < (2 : ℝ) / 5)
    (hC : 0 < C) (hProp13 : Prop13LowerDeviationBound d C) :
    ∃ M : ℕ, ∀ m k : ℕ, M ≤ m → 1 ≤ k →
      simpleRandomWalkLaw (lateThresholdOnLevel d m k) ≤
        ENNReal.ofReal (Real.exp (-(m : ℝ))) := by
  have h := hlozLemma26_eventually_of_prop13 d C hd hdUpper hC hProp13
  rw [eventually_atTop] at h
  obtain ⟨M, hM⟩ := h
  exact ⟨M, fun m k hm hk => hM m hm k hk⟩

/-- A finite-union version of Lemma 2.6, supplying the union-bound form used
when finitely many threshold indices are screened simultaneously. -/
theorem hlozLemma26_finite_union_eventually_of_prop13
    (r : ℕ) (d C : ℝ) (hd : 0 < d) (hdUpper : d < (2 : ℝ) / 5)
    (hC : 0 < C) (hProp13 : Prop13LowerDeviationBound d C) :
    ∀ᶠ m in atTop,
      simpleRandomWalkLaw
          (⋃ i : Fin r, lateThresholdOnLevel d m (i + 1)) ≤
        r * ENNReal.ofReal (Real.exp (-(m : ℝ))) := by
  filter_upwards [hlozLemma26_eventually_of_prop13
    d C hd hdUpper hC hProp13] with m hm
  calc
    simpleRandomWalkLaw
        (⋃ i : Fin r, lateThresholdOnLevel d m (i + 1)) ≤
        ∑ i : Fin r,
          simpleRandomWalkLaw (lateThresholdOnLevel d m (i + 1)) :=
      measure_iUnion_fintype_le simpleRandomWalkLaw _
    _ ≤ ∑ _i : Fin r,
        ENNReal.ofReal (Real.exp (-(m : ℝ))) := by
      exact Finset.sum_le_sum fun i _ => hm (i + 1) (by omega)
    _ = r * ENNReal.ofReal (Real.exp (-(m : ℝ))) := by simp

/-- The summable-error form of Lemma 2.6 consumed by the subsequent
Borel--Cantelli and finite-union arguments. -/
theorem hlozLemma26_tsum_ne_top_of_prop13
    (d C : ℝ) (hd : 0 < d) (hdUpper : d < (2 : ℝ) / 5)
    (hC : 0 < C) (hProp13 : Prop13LowerDeviationBound d C)
    (k : ℕ) (hk : 1 ≤ k) :
    (∑' m : ℕ,
      simpleRandomWalkLaw (lateThresholdOnLevel d m k)) ≠ ∞ := by
  obtain ⟨M, hM⟩ := hlozLemma26_of_prop13 d C hd hdUpper hC hProp13
  have hdom : ∀ m : ℕ,
      simpleRandomWalkLaw (lateThresholdOnLevel d m k) ≤
        ENNReal.ofReal
          (Real.exp (M : ℝ) * Real.exp (-(m : ℝ))) := by
    intro m
    by_cases hm : M ≤ m
    · calc
        simpleRandomWalkLaw (lateThresholdOnLevel d m k) ≤
            ENNReal.ofReal (Real.exp (-(m : ℝ))) := hM m k hm hk
        _ ≤ ENNReal.ofReal
            (Real.exp (M : ℝ) * Real.exp (-(m : ℝ))) := by
          apply ENNReal.ofReal_le_ofReal
          have hfactor : 1 ≤ Real.exp (M : ℝ) := by
            simpa only [Real.exp_zero] using
              Real.exp_le_exp.mpr (show (0 : ℝ) ≤ M by positivity)
          nlinarith [Real.exp_pos (-(m : ℝ))]
    · calc
        simpleRandomWalkLaw (lateThresholdOnLevel d m k) ≤
            simpleRandomWalkLaw Set.univ := measure_mono (Set.subset_univ _)
        _ = 1 := measure_univ
        _ ≤ ENNReal.ofReal
            (Real.exp (M : ℝ) * Real.exp (-(m : ℝ))) := by
          rw [← ENNReal.ofReal_one]
          apply ENNReal.ofReal_le_ofReal
          rw [← Real.exp_add]
          have hmm : (m : ℝ) ≤ M := by
            exact_mod_cast (Nat.le_of_lt (by omega : m < M))
          simpa only [← Real.exp_zero] using
            Real.exp_le_exp.mpr
              (by linarith : (0 : ℝ) ≤ (M : ℝ) + -(m : ℝ))
  have hsum : Summable
      (fun m : ℕ => Real.exp (M : ℝ) * Real.exp (-(m : ℝ))) :=
    Real.summable_exp_neg_nat.mul_left (Real.exp (M : ℝ))
  exact ne_top_of_le_ne_top hsum.tsum_ofReal_ne_top
    (ENNReal.tsum_le_tsum hdom)

theorem source_log_horizon_eq_nearCriticalLogHorizon (m : ℕ) :
    lemma26LogHorizon HLOZNearCriticalBridge.lowerTailDelta m =
      HLOZNearCriticalBridge.nearCriticalLogHorizon m := by
  rw [lemma26LogHorizon, leadingLogTerm, correctionLogTerm,
    HLOZNearCriticalBridge.nearCriticalLogHorizon, HLOZNearCriticalBridge.horizonCoefficient_eq,
    HLOZNearCriticalBridge.horizonExponent_eq, HLOZNearCriticalBridge.lowerTailDelta_eq, Real.sqrt_eq_rpow]
  rw [Real.sqrt_eq_rpow]
  norm_num

theorem source_floor_horizon_le_nearCriticalHorizon (m : ℕ) :
    lemma26Horizon HLOZNearCriticalBridge.lowerTailDelta m ≤ HLOZNearCriticalBridge.nearCriticalHorizon m := by
  rw [lemma26Horizon, source_log_horizon_eq_nearCriticalLogHorizon,
    HLOZNearCriticalBridge.nearCriticalHorizon]
  exact Nat.floor_le_ceil _

theorem proposition13Threshold_source_eq_nearCritical (n : ℕ) :
    proposition13Threshold HLOZNearCriticalBridge.lowerTailDelta n =
      HLOZNearCriticalBridge.proposition13Threshold n := by
  rw [proposition13Threshold, HLOZNearCriticalBridge.proposition13Threshold,
    lowerDeviationExponent, HLOZNearCriticalBridge.lowerTailExponent,
    div_eq_mul_inv]
  ring

theorem prop13LowerTailEvent_source_eq_nearCritical (n : ℕ) :
    {s | (maxLocalTime s n : ℝ) <
      proposition13Threshold HLOZNearCriticalBridge.lowerTailDelta n} =
      HLOZNearCriticalBridge.proposition13LowerTailEvent n := by
  ext s
  change (maxLocalTime s n : ℝ) <
      proposition13Threshold HLOZNearCriticalBridge.lowerTailDelta n ↔
    (maxLocalTime s n : ℝ) <
      HLOZNearCriticalBridge.proposition13Threshold n
  rw [proposition13Threshold_source_eq_nearCritical]

theorem eventually_nearCritical_prop13_tail_le_exp_neg_level
    (C : ℝ) (hC : 0 < C) :
    ∀ᶠ m : ℕ in atTop,
      C * Real.exp
          (-Real.exp
            (Real.log (HLOZNearCriticalBridge.nearCriticalHorizon m : ℝ) ^ ((3 : ℝ) / 5))) ≤
        Real.exp (-(m : ℝ)) := by
  filter_upwards [eventually_prop13_tail_le_exp_neg_level
    HLOZNearCriticalBridge.lowerTailDelta C hC,
    eventually_log_lemma26Horizon_between HLOZNearCriticalBridge.lowerTailDelta,
    leadingLogTerm_tendsto.eventually_gt_atTop 2,
    eventually_ge_atTop 1] with m htail hfloorlog hlead hm
  have hmpos : 0 < (m : ℝ) := by exact_mod_cast hm
  have hcorrection : 0 < correctionLogTerm HLOZNearCriticalBridge.lowerTailDelta m := by
    exact mul_pos (Real.rpow_pos_of_pos Real.pi_pos _)
      (Real.rpow_pos_of_pos hmpos _)
  have hfloorLogPos :
      0 < Real.log (lemma26Horizon HLOZNearCriticalBridge.lowerTailDelta m : ℝ) := by
    have : 0 < lemma26LogHorizon HLOZNearCriticalBridge.lowerTailDelta m - 1 := by
      rw [lemma26LogHorizon]
      linarith
    exact this.trans_le hfloorlog.1
  have hfloorPos : (0 : ℝ) < lemma26Horizon HLOZNearCriticalBridge.lowerTailDelta m := by
    exact (Real.log_pos_iff (by positivity)).mp hfloorLogPos |>.trans' zero_lt_one
  have hhorizonCast :
      (lemma26Horizon HLOZNearCriticalBridge.lowerTailDelta m : ℝ) ≤
        HLOZNearCriticalBridge.nearCriticalHorizon m := by
    exact_mod_cast source_floor_horizon_le_nearCriticalHorizon m
  have hlogle :
      Real.log (lemma26Horizon HLOZNearCriticalBridge.lowerTailDelta m : ℝ) ≤
        Real.log (HLOZNearCriticalBridge.nearCriticalHorizon m : ℝ) :=
    Real.log_le_log hfloorPos hhorizonCast
  have hpowle :
      Real.log (lemma26Horizon HLOZNearCriticalBridge.lowerTailDelta m : ℝ) ^ ((3 : ℝ) / 5) ≤
        Real.log (HLOZNearCriticalBridge.nearCriticalHorizon m : ℝ) ^ ((3 : ℝ) / 5) :=
    Real.rpow_le_rpow hfloorLogPos.le hlogle (by norm_num)
  have hexple :
      Real.exp
          (-Real.exp
            (Real.log (HLOZNearCriticalBridge.nearCriticalHorizon m : ℝ) ^ ((3 : ℝ) / 5))) ≤
        Real.exp
          (-Real.exp
            (Real.log (lemma26Horizon HLOZNearCriticalBridge.lowerTailDelta m : ℝ) ^
              ((3 : ℝ) / 5))) := by
    exact Real.exp_le_exp.mpr (neg_le_neg (Real.exp_le_exp.mpr hpowle))
  exact (mul_le_mul_of_nonneg_left hexple hC.le).trans htail

/-- Proposition 1.3 sampled at the corrected near-critical horizons, with a
summable exponential majorant. -/
theorem eventually_nearCritical_prop13_bound_of_prop13
    (C : ℝ) (hC : 0 < C)
    (hProp13 : Prop13LowerDeviationBound
      HLOZNearCriticalBridge.lowerTailDelta C) :
    ∀ᶠ m : ℕ in atTop,
      simpleRandomWalkLaw
          (HLOZNearCriticalBridge.proposition13LowerTailEvent
            (HLOZNearCriticalBridge.nearCriticalHorizon m)) ≤
        ENNReal.ofReal (Real.exp (-(m : ℝ))) := by
  filter_upwards [eventually_nearCritical_prop13_tail_le_exp_neg_level C hC]
    with m htail
  calc
    simpleRandomWalkLaw
        (HLOZNearCriticalBridge.proposition13LowerTailEvent
          (HLOZNearCriticalBridge.nearCriticalHorizon m)) =
        simpleRandomWalkLaw
          {s | (maxLocalTime s (HLOZNearCriticalBridge.nearCriticalHorizon m) : ℝ) <
            proposition13Threshold HLOZNearCriticalBridge.lowerTailDelta
              (HLOZNearCriticalBridge.nearCriticalHorizon m)} := by
      rw [prop13LowerTailEvent_source_eq_nearCritical]
    _ ≤ ENNReal.ofReal
        (C * Real.exp
          (-Real.exp
            (Real.log (HLOZNearCriticalBridge.nearCriticalHorizon m : ℝ) ^
              ((3 : ℝ) / 5)))) :=
      hProp13 (HLOZNearCriticalBridge.nearCriticalHorizon m)
    _ ≤ ENNReal.ofReal (Real.exp (-(m : ℝ))) :=
      ENNReal.ofReal_le_ofReal htail

/-- The sampled Proposition-1.3 lower-tail events are summable. -/
theorem nearCritical_prop13_tsum_ne_top_of_prop13
    (C : ℝ) (hC : 0 < C)
    (hProp13 : Prop13LowerDeviationBound
      HLOZNearCriticalBridge.lowerTailDelta C) :
    (∑' m : ℕ, simpleRandomWalkLaw
      (HLOZNearCriticalBridge.proposition13LowerTailEvent
        (HLOZNearCriticalBridge.nearCriticalHorizon m))) ≠ ∞ := by
  exact HLOZNearCriticalBridge.tsum_proposition13LowerTailEvent_of_eventually_bound
    simpleRandomWalkLaw HLOZNearCriticalBridge.nearCriticalHorizon
    (fun m => ENNReal.ofReal (Real.exp (-(m : ℝ))))
    (eventually_nearCritical_prop13_bound_of_prop13 C hC hProp13)
    Real.summable_exp_neg_nat.tsum_ofReal_ne_top

theorem nearCritical_late_subset_source_floor_late (m k : ℕ) :
    HLOZNearCriticalBridge.lateOnThresholdEvent
        HLOZNearCriticalBridge.nearCriticalHorizon m k ⊆
      lateThresholdOnLevel HLOZNearCriticalBridge.lowerTailDelta m k := by
  intro s hs
  rcases hs with ⟨hlate, hM⟩
  constructor
  · change (HLOZNearCriticalBridge.nearCriticalHorizon m : WithTop ℕ) <
      firstKSitesReachLevel m k s at hlate
    change (lemma26Horizon HLOZNearCriticalBridge.lowerTailDelta m :
      WithTop ℕ) < firstKSitesReachLevel m k s
    have hle :
        (lemma26Horizon HLOZNearCriticalBridge.lowerTailDelta m :
          WithTop ℕ) ≤
          (HLOZNearCriticalBridge.nearCriticalHorizon m : WithTop ℕ) := by
      exact_mod_cast source_floor_horizon_le_nearCriticalHorizon m
    exact hle.trans_lt hlate
  · exact hM

theorem nearCritical_late_tsum_ne_top_of_prop13
    (C : ℝ) (hC : 0 < C)
    (hProp13 : Prop13LowerDeviationBound
      HLOZNearCriticalBridge.lowerTailDelta C) (k : ℕ) (hk : 1 ≤ k) :
    (∑' m : ℕ, simpleRandomWalkLaw
      (HLOZNearCriticalBridge.lateOnThresholdEvent
        HLOZNearCriticalBridge.nearCriticalHorizon m k)) ≠ ∞ := by
  have hsource := hlozLemma26_tsum_ne_top_of_prop13
    HLOZNearCriticalBridge.lowerTailDelta C
    (by rw [HLOZNearCriticalBridge.lowerTailDelta_eq]; norm_num)
    (by rw [HLOZNearCriticalBridge.lowerTailDelta_eq]; norm_num)
    hC hProp13 k hk
  exact ne_top_of_le_ne_top hsource
    (ENNReal.tsum_le_tsum fun m =>
      measure_mono (nearCritical_late_subset_source_floor_late m k))

theorem ae_eventually_threshold_le_nearCriticalHorizon_on_M_of_prop13
    (C : ℝ) (hC : 0 < C)
    (hProp13 : Prop13LowerDeviationBound
      HLOZNearCriticalBridge.lowerTailDelta C) (k : ℕ) (_hk : 1 ≤ k) :
    ∀ᵐ s ∂simpleRandomWalkLaw, ∀ᶠ m : ℕ in atTop,
      s ∈ HLOZNearCriticalBridge.thresholdTimeEventK m k →
        firstKSitesReachLevel m k s ≤
          (HLOZNearCriticalBridge.nearCriticalHorizon m : WithTop ℕ) := by
  exact
    HLOZNearCriticalBridge.ae_eventually_threshold_le_nearCriticalHorizon_of_eventually_prop13_bound
      k (fun m => ENNReal.ofReal (Real.exp (-(m : ℝ))))
      (eventually_nearCritical_prop13_bound_of_prop13 C hC hProp13)
      Real.summable_exp_neg_nat.tsum_ofReal_ne_top

theorem ae_eventually_fourth_threshold_le_nearCriticalHorizon_of_prop13
    (C : ℝ) (hC : 0 < C)
    (hProp13 : Prop13LowerDeviationBound
      HLOZNearCriticalBridge.lowerTailDelta C) :
    ∀ᵐ s ∂simpleRandomWalkLaw, ∀ᶠ m : ℕ in atTop,
      s ∈ hlozThresholdTimeEvent m →
        firstKSitesReachLevel m 4 s ≤
          (HLOZNearCriticalBridge.nearCriticalHorizon m : WithTop ℕ) := by
  simpa only [HLOZNearCriticalBridge.thresholdTimeEventK_four] using
    ae_eventually_threshold_le_nearCriticalHorizon_on_M_of_prop13
      C hC hProp13 4 (by omega)


end HLOZTimeChange
end Erdos1166
