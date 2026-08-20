import ErdosProblems.Erdos515.Prawitz
import ErdosProblems.Erdos515.KoebeDistortion
import ErdosProblems.Erdos515.HardyCircle
import ErdosProblems.Erdos515.External.Ray.Analytic.Log
import ErdosProblems.Erdos515.External.Ray.Hartogs.FubiniBall
import ErdosProblems.Erdos515.External.Ray.Misc.Circle
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.MeasureTheory.Function.Jacobian

/-!
# Prawitz's quarter-power integral inequality

This file discharges the analytic `PrawitzQuarterBound` interface used in the
Lewis--Rossi--Weitsman argument.
-/

open Metric Set MeasureTheory
open scoped ENNReal NNReal Real

noncomputable section

namespace Erdos515.PrawitzProof

variable {G : ℂ → ℂ} {z : ℂ}

private lemma zero_mem_unitBall : (0 : ℂ) ∈ ball 0 1 := by simp

private lemma integral_circleMap_pow_eight {f : ℂ → ℝ}
    (hcont : Continuous (fun θ : ℝ ↦ f (circleMap 0 1 θ))) :
    (∫ θ in (0 : ℝ)..2 * Real.pi, f ((circleMap 0 1 θ) ^ 8)) =
      ∫ θ in (0 : ℝ)..2 * Real.pi, f (circleMap 0 1 θ) := by
  let g : ℝ → ℝ := fun θ ↦ f (circleMap 0 1 θ)
  have hpow : ∀ θ : ℝ, f ((circleMap 0 1 θ) ^ 8) = g (8 * θ) := by
    intro θ
    simp only [g, circleMap, zero_add, Complex.ofReal_one, one_mul]
    apply congrArg f
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hperiodic : Function.Periodic g (2 * Real.pi) := by
    intro θ
    simp only [g, circleMap, zero_add, Complex.ofReal_one, one_mul,
      Complex.ofReal_add, add_mul, Complex.exp_add]
    rw [show ((2 * Real.pi : ℝ) : ℂ) * Complex.I =
      2 * Real.pi * Complex.I by push_cast; rfl, Complex.exp_two_pi_mul_I, mul_one]
  have hint : ∀ a c : ℝ, IntervalIntegrable g volume a c := by
    intro a c
    simpa only [g] using hcont.intervalIntegrable (a := a) (b := c)
  rw [intervalIntegral.integral_congr (fun θ _ ↦ hpow θ)]
  rw [intervalIntegral.integral_comp_mul_left g (by norm_num : (8 : ℝ) ≠ 0)]
  have hmany := hperiodic.intervalIntegral_add_zsmul_eq (8 : ℤ) 0 hint
  norm_num at hmany ⊢
  rw [hmany]
  simp only [g]
  ring

/-- The normalized-univalent data used in the quarter-power argument. -/
structure NormalizedUnivalent (G : ℂ → ℂ) : Prop where
  analytic : AnalyticOnNhd ℂ G (ball 0 1)
  inj : InjOn G (ball 0 1)
  map_zero : G 0 = 0
  deriv_zero : deriv G 0 = 1

namespace NormalizedUnivalent

variable (b : NormalizedUnivalent G)

/-- The analytic removable quotient `G z / z`. -/
noncomputable def quotient (_b : NormalizedUnivalent G) : ℂ → ℂ := dslope G 0

lemma analytic_quotient : AnalyticOnNhd ℂ b.quotient (ball 0 1) :=
  fun z hz ↦ (b.analytic z hz).dslope

lemma map_eq_z_mul_quotient : G z = z * b.quotient z := by
  by_cases hz : z = 0
  · simp [hz, b.map_zero]
  · simp [quotient, dslope_of_ne _ hz, slope, hz, b.map_zero]

@[simp] lemma quotient_zero : b.quotient 0 = 1 := by
  simp [quotient, b.deriv_zero]

lemma quotient_ne_zero (hz : z ∈ ball (0 : ℂ) 1) : b.quotient z ≠ 0 := by
  by_cases h0 : z = 0
  · simp [h0]
  · have hGz : G z ≠ 0 := by
      intro h
      have := b.inj hz zero_mem_unitBall
      exact h0 (this (h.trans b.map_zero.symm))
    simp [quotient, dslope_of_ne _ h0, slope, h0, b.map_zero, hGz]

/-- A normalized analytic eighth root of `G z / z` (with the removable value at zero). -/
def existsEighthRoot :
    ∃ H : ℂ → ℂ, AnalyticOnNhd ℂ H (ball 0 1) ∧ H 0 = 1 ∧
      ∀ z ∈ ball (0 : ℂ) 1, b.quotient z = H z ^ 8 := by
  obtain ⟨H, hH, hH0, hpow⟩ :=
    b.analytic_quotient.exists_root (fun z hz ↦ b.quotient_ne_zero hz) (n := 8) (by norm_num)
  refine ⟨H, hH, ?_, hpow⟩
  simpa using hH0

noncomputable def H : ℂ → ℂ := Classical.choose b.existsEighthRoot

lemma analytic_H : AnalyticOnNhd ℂ b.H (ball 0 1) :=
  (Classical.choose_spec b.existsEighthRoot).1

@[simp] lemma H_zero : b.H 0 = 1 :=
  (Classical.choose_spec b.existsEighthRoot).2.1

lemma quotient_eq_H_pow (hz : z ∈ ball (0 : ℂ) 1) : b.quotient z = b.H z ^ 8 :=
  (Classical.choose_spec b.existsEighthRoot).2.2 z hz

lemma H_ne_zero (hz : z ∈ ball (0 : ℂ) 1) : b.H z ≠ 0 := by
  intro h
  have hq := b.quotient_eq_H_pow hz
  rw [h, zero_pow (by norm_num : 8 ≠ 0)] at hq
  exact b.quotient_ne_zero hz hq

lemma G_eq_z_mul_H_pow (hz : z ∈ ball (0 : ℂ) 1) :
    G z = z * b.H z ^ 8 := by
  rw [b.map_eq_z_mul_quotient, b.quotient_eq_H_pow hz]

/-- The Prawitz eighth-root lift `z ↦ z H(z⁸)`. -/
noncomputable def eighthLift (z : ℂ) : ℂ := z * b.H (z ^ 8)

private lemma pow_eight_mem_unitBall (hz : z ∈ ball (0 : ℂ) 1) :
    z ^ 8 ∈ ball (0 : ℂ) 1 := by
  simpa only [mem_ball, dist_zero_right, norm_pow] using
    (pow_lt_one₀ (norm_nonneg z) (by simpa only [mem_ball, dist_zero_right] using hz)
      (by norm_num : 8 ≠ 0))

lemma analytic_eighthLift : AnalyticOnNhd ℂ b.eighthLift (ball 0 1) := by
  intro z hz
  change AnalyticAt ℂ (fun w : ℂ ↦ w * b.H (w ^ 8)) z
  have hp : AnalyticAt ℂ (fun w : ℂ ↦ w ^ 8) z := analyticAt_id.pow 8
  exact analyticAt_id.mul
    (AnalyticAt.comp (b.analytic_H _ (pow_eight_mem_unitBall hz)) hp)

lemma eighthLift_pow (hz : z ∈ ball (0 : ℂ) 1) :
    b.eighthLift z ^ 8 = G (z ^ 8) := by
  rw [b.G_eq_z_mul_H_pow (pow_eight_mem_unitBall hz)]
  simp only [eighthLift, mul_pow]

lemma norm_eighthLift_sq (hz : z ∈ ball (0 : ℂ) 1) :
    ‖b.eighthLift z‖ ^ 2 = ‖G (z ^ 8)‖ ^ ((1 : ℝ) / 4) := by
  have hnorm : ‖b.eighthLift z‖ ^ 8 = ‖G (z ^ 8)‖ := by
    rw [← b.eighthLift_pow hz, norm_pow]
  rw [← hnorm]
  let a : ℝ := ‖b.eighthLift z‖
  change a ^ 2 = (a ^ 8) ^ ((1 : ℝ) / 4)
  calc
    a ^ 2 = a ^ (2 : ℝ) := (Real.rpow_natCast a 2).symm
    _ = a ^ ((8 : ℕ) * ((1 : ℝ) / 4)) := by norm_num
    _ = (a ^ 8) ^ ((1 : ℝ) / 4) :=
      Real.rpow_natCast_mul (norm_nonneg _) 8 ((1 : ℝ) / 4)

lemma inj_eighthLift : InjOn b.eighthLift (ball 0 1) := by
  intro z hz w hw heq
  have hp := congrArg (fun u : ℂ ↦ u ^ 8) heq
  rw [b.eighthLift_pow hz, b.eighthLift_pow hw] at hp
  have hpow : z ^ 8 = w ^ 8 :=
    b.inj (pow_eight_mem_unitBall hz) (pow_eight_mem_unitBall hw) hp
  change z * b.H (z ^ 8) = w * b.H (w ^ 8) at heq
  rw [hpow] at heq
  exact mul_right_cancel₀ (b.H_ne_zero (pow_eight_mem_unitBall hw)) heq

/-- Taylor coefficients of the eighth root. -/
noncomputable def coeff (n : ℕ) : ℂ :=
  iteratedDeriv n b.H 0 / n.factorial

/-- The eighth root is represented by its Taylor series throughout the unit disk. -/
lemma hasFPowerSeriesOnBall_H :
    HasFPowerSeriesOnBall b.H (.ofScalars ℂ b.coeff) 0 1 := by
  have h0 := (b.analytic_H 0 zero_mem_unitBall).hasFPowerSeriesAt
  obtain ⟨p, hp⟩ := (analyticOnNhd_ball_iff_hasFPowerSeriesOnBall (by norm_num)).mp
    (Metric.eball_ofReal (α := ℂ) ▸ b.analytic_H)
  have pe := h0.eq_formalMultilinearSeries hp.hasFPowerSeriesAt
  unfold coeff
  simp only [h0.eq_formalMultilinearSeries hp.hasFPowerSeriesAt] at h0 ⊢
  simpa using hp

/-- Taylor coefficients after radial rescaling to the unit circle. -/
noncomputable def radialCoeff (r : ℝ) (n : ℕ) : ℂ :=
  b.coeff n * (r : ℂ) ^ n

lemma summable_norm_radialCoeff {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Summable (fun n ↦ ‖b.radialCoeff r n‖) := by
  let rr : ℝ≥0 := ⟨r, hr0⟩
  have hrr : (rr : ℝ≥0∞) <
      (FormalMultilinearSeries.ofScalars ℂ b.coeff).radius :=
    lt_of_lt_of_le (by
      rw [ENNReal.coe_lt_one_iff]
      exact_mod_cast hr1)
      b.hasFPowerSeriesOnBall_H.r_le
  have hs :=
    (FormalMultilinearSeries.ofScalars ℂ b.coeff).summable_norm_mul_pow hrr
  have hs' : Summable (fun n ↦ ‖b.coeff n‖ * r ^ n) := by
    refine hs.congr (fun n ↦ ?_)
    simp only [FormalMultilinearSeries.ofScalars_norm]
    rw [show (rr : ℝ) = r by rfl]
  simpa only [radialCoeff, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hr0, FormalMultilinearSeries.ofScalars_norm, rr] using hs'

lemma H_eq_hardySum_radialCoeff {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    {w : ℂ} (hw : ‖w‖ ≤ 1) :
    b.H ((r : ℂ) * w) = Prawitz.HardyCircle.hardySum (b.radialCoeff r) w := by
  have hrw : ‖(r : ℂ) * w‖ < 1 := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0]
    calc
      r * ‖w‖ ≤ r * 1 := mul_le_mul_of_nonneg_left hw hr0
      _ < 1 := by simpa using hr1
  have hsum := b.hasFPowerSeriesOnBall_H.hasSum (y := (r : ℂ) * w) (by
    rw [Metric.mem_eball, edist_dist, ENNReal.ofReal_lt_one]
    simpa only [dist_zero_right] using hrw)
  have heval :
      (∑' n, (FormalMultilinearSeries.ofScalars ℂ b.coeff n) fun _ ↦ (r : ℂ) * w) =
        b.H ((r : ℂ) * w) := by
    simpa only [zero_add] using hsum.tsum_eq
  rw [Prawitz.HardyCircle.hardySum]
  rw [← heval]
  apply tsum_congr
  intro n
  simp only [FormalMultilinearSeries.ofScalars_apply_eq, radialCoeff, mul_pow, smul_eq_mul]
  ac_rfl

/-- Parseval for the analytic eighth root, at an arbitrary radius below one. -/
lemma circleAverage_norm_H_sq {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Real.circleAverage (fun w ↦ ‖b.H ((r : ℂ) * w)‖ ^ 2) 0 1 =
      ∑' n, ‖b.radialCoeff r n‖ ^ 2 := by
  have hparseval := Prawitz.HardyCircle.infinite_norm_parseval
    (b.summable_norm_radialCoeff hr0 hr1)
  convert hparseval using 1
  apply Real.circleAverage_congr_sphere
  intro w hw
  have hw_eq : ‖w‖ = 1 := by simpa only [mem_sphere, dist_zero_right, abs_one] using hw
  have hw' : ‖w‖ ≤ 1 := hw_eq.le
  change ‖b.H ((r : ℂ) * w)‖ ^ 2 =
    ‖Prawitz.HardyCircle.hardySum (b.radialCoeff r) w‖ ^ 2
  rw [b.H_eq_hardySum_radialCoeff hr0 hr1 hw']

/-- Taylor coefficients of the derivative of the eighth root. -/
noncomputable def derivCoeff (n : ℕ) : ℂ :=
  iteratedDeriv n (deriv b.H) 0 / n.factorial

lemma hasFPowerSeriesOnBall_deriv_H :
    HasFPowerSeriesOnBall (deriv b.H) (.ofScalars ℂ b.derivCoeff) 0 1 := by
  have ha : AnalyticOnNhd ℂ (deriv b.H) (ball 0 1) := b.analytic_H.deriv
  have h0 := (ha 0 zero_mem_unitBall).hasFPowerSeriesAt
  obtain ⟨p, hp⟩ := (analyticOnNhd_ball_iff_hasFPowerSeriesOnBall (by norm_num)).mp
    (Metric.eball_ofReal (α := ℂ) ▸ ha)
  unfold derivCoeff
  simp only [h0.eq_formalMultilinearSeries hp.hasFPowerSeriesAt] at h0 ⊢
  simpa using hp

lemma derivCoeff_eq (n : ℕ) :
    b.derivCoeff n = ((n + 1 : ℕ) : ℂ) * b.coeff (n + 1) := by
  simp only [derivCoeff, coeff, ← iteratedDeriv_succ', Nat.factorial_succ]
  push_cast
  field_simp

/-- Radially rescaled derivative coefficients. -/
noncomputable def radialDerivCoeff (r : ℝ) (n : ℕ) : ℂ :=
  b.derivCoeff n * (r : ℂ) ^ n

lemma summable_norm_radialDerivCoeff {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Summable (fun n ↦ ‖b.radialDerivCoeff r n‖) := by
  let rr : ℝ≥0 := ⟨r, hr0⟩
  have hrr : (rr : ℝ≥0∞) <
      (FormalMultilinearSeries.ofScalars ℂ b.derivCoeff).radius :=
    lt_of_lt_of_le (by rw [ENNReal.coe_lt_one_iff]; exact_mod_cast hr1)
      b.hasFPowerSeriesOnBall_deriv_H.r_le
  have hs :=
    (FormalMultilinearSeries.ofScalars ℂ b.derivCoeff).summable_norm_mul_pow hrr
  have hs' : Summable (fun n ↦ ‖b.derivCoeff n‖ * r ^ n) := by
    refine hs.congr (fun n ↦ ?_)
    simp only [FormalMultilinearSeries.ofScalars_norm]
    rw [show (rr : ℝ) = r by rfl]
  simpa only [radialDerivCoeff, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hr0, FormalMultilinearSeries.ofScalars_norm, rr] using hs'

lemma deriv_H_eq_hardySum_radialDerivCoeff {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    {w : ℂ} (hw : ‖w‖ ≤ 1) :
    deriv b.H ((r : ℂ) * w) = Prawitz.HardyCircle.hardySum (b.radialDerivCoeff r) w := by
  have hrw : ‖(r : ℂ) * w‖ < 1 := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0]
    exact (mul_le_mul_of_nonneg_left hw hr0).trans_lt (by simpa using hr1)
  have hsum := b.hasFPowerSeriesOnBall_deriv_H.hasSum (y := (r : ℂ) * w) (by
    rw [Metric.mem_eball, edist_dist, ENNReal.ofReal_lt_one]
    simpa only [dist_zero_right] using hrw)
  have heval :
      (∑' n, (FormalMultilinearSeries.ofScalars ℂ b.derivCoeff n)
        fun _ ↦ (r : ℂ) * w) = deriv b.H ((r : ℂ) * w) := by
    simpa only [zero_add] using hsum.tsum_eq
  rw [Prawitz.HardyCircle.hardySum, ← heval]
  apply tsum_congr
  intro n
  simp only [FormalMultilinearSeries.ofScalars_apply_eq, radialDerivCoeff, mul_pow,
    smul_eq_mul]
  ac_rfl

lemma circleAverage_norm_deriv_H_sq {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Real.circleAverage (fun w ↦ ‖deriv b.H ((r : ℂ) * w)‖ ^ 2) 0 1 =
      ∑' n, ‖b.radialDerivCoeff r n‖ ^ 2 := by
  have hparseval := Prawitz.HardyCircle.infinite_norm_parseval
    (b.summable_norm_radialDerivCoeff hr0 hr1)
  convert hparseval using 1
  apply Real.circleAverage_congr_sphere
  intro w hw
  have hw_eq : ‖w‖ = 1 := by simpa only [mem_sphere, dist_zero_right, abs_one] using hw
  change ‖deriv b.H ((r : ℂ) * w)‖ ^ 2 =
    ‖Prawitz.HardyCircle.hardySum (b.radialDerivCoeff r) w‖ ^ 2
  rw [b.deriv_H_eq_hardySum_radialDerivCoeff hr0 hr1 hw_eq.le]

/-- The Euler derivative of the eighth root; after composing with `z ↦ z⁸` this is the
derivative of the Prawitz lift. -/
noncomputable def prawitzDerivative (z : ℂ) : ℂ :=
  b.H z + 8 * z * deriv b.H z

lemma analytic_prawitzDerivative :
    AnalyticOnNhd ℂ b.prawitzDerivative (ball 0 1) := by
  intro z hz
  exact (b.analytic_H z hz).add
    (analyticAt_const.mul analyticAt_id |>.mul ((b.analytic_H z hz).deriv))

private lemma iteratedDeriv_mul_deriv_H (n : ℕ) :
    iteratedDeriv n (fun z : ℂ ↦ z * deriv b.H z) 0 =
      (n : ℂ) * iteratedDeriv n b.H 0 := by
  rcases n with _ | n
  · simp
  have hH0 : AnalyticAt ℂ b.H 0 := b.analytic_H 0 zero_mem_unitBall
  have hid : ContDiffAt ℂ ((n + 1 : ℕ) : ℕ∞) (id : ℂ → ℂ) 0 := contDiffAt_id
  rw [show (fun z : ℂ ↦ z * deriv b.H z) = id * deriv b.H by rfl]
  rw [iteratedDeriv_mul hid hH0.deriv.contDiffAt]
  rw [Finset.sum_eq_single 1]
  · simp [iteratedDeriv_id, ← iteratedDeriv_succ']
  · intro i hi hne
    simp only [Finset.mem_range] at hi
    have hi' : i = 0 ∨ 2 ≤ i := by omega
    rcases hi' with rfl | hi2
    · simp [iteratedDeriv_id]
    · simp [iteratedDeriv_id, (show i ≠ 0 by omega), (show i ≠ 1 by omega)]
  · simp

lemma iteratedDeriv_prawitzDerivative (n : ℕ) :
    iteratedDeriv n b.prawitzDerivative 0 =
      ((8 * n + 1 : ℕ) : ℂ) * iteratedDeriv n b.H 0 := by
  have hH0 : AnalyticAt ℂ b.H 0 := b.analytic_H 0 zero_mem_unitBall
  have hmul : AnalyticAt ℂ (fun z : ℂ ↦ z * deriv b.H z) 0 :=
    analyticAt_id.mul hH0.deriv
  unfold prawitzDerivative
  rw [show (fun z : ℂ ↦ b.H z + 8 * z * deriv b.H z) =
      b.H + fun z : ℂ ↦ (8 : ℂ) * (z * deriv b.H z) by
    funext z
    simp only [Pi.add_apply]
    ring]
  rw [show (fun z : ℂ ↦ (8 : ℂ) * (z * deriv b.H z)) =
      (fun _ : ℂ ↦ (8 : ℂ)) * (fun z : ℂ ↦ z * deriv b.H z) by rfl]
  rw [iteratedDeriv_add hH0.contDiffAt
    ((analyticAt_const.mul hmul).contDiffAt)]
  rw [show ((fun _ : ℂ ↦ (8 : ℂ)) * (fun z : ℂ ↦ z * deriv b.H z)) =
      (fun z : ℂ ↦ (8 : ℂ) * (z * deriv b.H z)) by rfl]
  have hc : iteratedDeriv n (fun z : ℂ ↦ (8 : ℂ) * (z * deriv b.H z)) 0 =
      (8 : ℂ) * iteratedDeriv n (fun z : ℂ ↦ z * deriv b.H z) 0 := by
    exact iteratedDeriv_const_mul (8 : ℂ) hmul.contDiffAt
  rw [hc, iteratedDeriv_mul_deriv_H]
  push_cast
  ring

/-- Taylor coefficients of the Euler derivative. -/
noncomputable def prawitzCoeff (n : ℕ) : ℂ :=
  iteratedDeriv n b.prawitzDerivative 0 / n.factorial

lemma prawitzCoeff_eq (n : ℕ) :
    b.prawitzCoeff n = ((8 * n + 1 : ℕ) : ℂ) * b.coeff n := by
  rw [prawitzCoeff, b.iteratedDeriv_prawitzDerivative, coeff]
  ring

lemma hasFPowerSeriesOnBall_prawitzDerivative :
    HasFPowerSeriesOnBall b.prawitzDerivative (.ofScalars ℂ b.prawitzCoeff) 0 1 := by
  have ha := b.analytic_prawitzDerivative
  have h0 := (ha 0 zero_mem_unitBall).hasFPowerSeriesAt
  obtain ⟨p, hp⟩ := (analyticOnNhd_ball_iff_hasFPowerSeriesOnBall (by norm_num)).mp
    (Metric.eball_ofReal (α := ℂ) ▸ ha)
  unfold prawitzCoeff
  simp only [h0.eq_formalMultilinearSeries hp.hasFPowerSeriesAt] at h0 ⊢
  simpa using hp

noncomputable def radialPrawitzCoeff (r : ℝ) (n : ℕ) : ℂ :=
  b.prawitzCoeff n * (r : ℂ) ^ n

lemma summable_norm_radialPrawitzCoeff {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Summable (fun n ↦ ‖b.radialPrawitzCoeff r n‖) := by
  let rr : ℝ≥0 := ⟨r, hr0⟩
  have hrr : (rr : ℝ≥0∞) <
      (FormalMultilinearSeries.ofScalars ℂ b.prawitzCoeff).radius :=
    lt_of_lt_of_le (by rw [ENNReal.coe_lt_one_iff]; exact_mod_cast hr1)
      b.hasFPowerSeriesOnBall_prawitzDerivative.r_le
  have hs :=
    (FormalMultilinearSeries.ofScalars ℂ b.prawitzCoeff).summable_norm_mul_pow hrr
  have hs' : Summable (fun n ↦ ‖b.prawitzCoeff n‖ * r ^ n) := by
    refine hs.congr (fun n ↦ ?_)
    simp only [FormalMultilinearSeries.ofScalars_norm]
    rw [show (rr : ℝ) = r by rfl]
  simpa only [radialPrawitzCoeff, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hr0, FormalMultilinearSeries.ofScalars_norm, rr] using hs'

lemma prawitzDerivative_eq_hardySum {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    {w : ℂ} (hw : ‖w‖ ≤ 1) :
    b.prawitzDerivative ((r : ℂ) * w) =
      Prawitz.HardyCircle.hardySum (b.radialPrawitzCoeff r) w := by
  have hrw : ‖(r : ℂ) * w‖ < 1 := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0]
    exact (mul_le_mul_of_nonneg_left hw hr0).trans_lt (by simpa using hr1)
  have hsum := b.hasFPowerSeriesOnBall_prawitzDerivative.hasSum
    (y := (r : ℂ) * w) (by
      rw [Metric.mem_eball, edist_dist, ENNReal.ofReal_lt_one]
      simpa only [dist_zero_right] using hrw)
  have heval :
      (∑' n, (FormalMultilinearSeries.ofScalars ℂ b.prawitzCoeff n)
        fun _ ↦ (r : ℂ) * w) = b.prawitzDerivative ((r : ℂ) * w) := by
    simpa only [zero_add] using hsum.tsum_eq
  rw [Prawitz.HardyCircle.hardySum, ← heval]
  apply tsum_congr
  intro n
  simp only [FormalMultilinearSeries.ofScalars_apply_eq, radialPrawitzCoeff, mul_pow,
    smul_eq_mul]
  ac_rfl

lemma circleAverage_norm_prawitzDerivative_sq {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Real.circleAverage (fun w ↦ ‖b.prawitzDerivative ((r : ℂ) * w)‖ ^ 2) 0 1 =
      ∑' n, ‖b.radialPrawitzCoeff r n‖ ^ 2 := by
  have hparseval := Prawitz.HardyCircle.infinite_norm_parseval
    (b.summable_norm_radialPrawitzCoeff hr0 hr1)
  convert hparseval using 1
  apply Real.circleAverage_congr_sphere
  intro w hw
  have hw_eq : ‖w‖ = 1 := by simpa only [mem_sphere, dist_zero_right, abs_one] using hw
  change ‖b.prawitzDerivative ((r : ℂ) * w)‖ ^ 2 =
    ‖Prawitz.HardyCircle.hardySum (b.radialPrawitzCoeff r) w‖ ^ 2
  rw [b.prawitzDerivative_eq_hardySum hr0 hr1 hw_eq.le]

lemma summable_sq_radialPrawitzCoeff {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Summable (fun n ↦ ‖b.radialPrawitzCoeff r n‖ ^ 2) := by
  have hs := b.summable_norm_radialPrawitzCoeff hr0 hr1
  have h := Prawitz.HardyCircle.summable_re_mul_conj hs hs
  have hreal (x : ℝ) : (((x : ℂ) ^ 2).re) = x ^ 2 := by
    simp only [pow_two, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
      sub_zero]
  simpa only [Complex.mul_conj', hreal] using h

lemma radialPrawitzCoeff_sq_mono {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) (n : ℕ) :
    ‖b.radialPrawitzCoeff (x ^ 8) n‖ ^ 2 ≤
      ‖b.radialPrawitzCoeff (y ^ 8) n‖ ^ 2 := by
  simp only [radialPrawitzCoeff, norm_mul, norm_pow, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hx 8)]
  gcongr

lemma deriv_eighthLift (hz : z ∈ ball (0 : ℂ) 1) :
    deriv b.eighthLift z = b.prawitzDerivative (z ^ 8) := by
  have hH := b.analytic_H _ (pow_eight_mem_unitBall hz)
  have hp : HasDerivAt (fun w : ℂ ↦ w ^ 8) (8 * z ^ 7) z := by
    simpa using hasDerivAt_pow 8 z
  have hcomp := hH.differentiableAt.hasDerivAt.comp z hp
  have hprod := (hasDerivAt_id z).mul hcomp
  rw [show b.eighthLift = id * (b.H ∘ fun w : ℂ ↦ w ^ 8) by rfl]
  rw [hprod.deriv]
  simp only [prawitzDerivative, Function.comp_apply, id_eq]
  ring

/-- The area of the lift image is the Dirichlet integral of its complex derivative. -/
lemma volume_image_closedBall_eighthLift {R : ℝ} (hR0 : 0 ≤ R) (hR1 : R < 1) :
    volume.real (b.eighthLift '' closedBall (0 : ℂ) R) =
      ∫ z in closedBall (0 : ℂ) R, ‖deriv b.eighthLift z‖ ^ 2 := by
  have hsub : closedBall (0 : ℂ) R ⊆ ball 0 1 := by
    intro z hz
    rw [mem_closedBall, dist_zero_right] at hz
    rw [mem_ball, dist_zero_right]
    exact hz.trans_lt hR1
  have ha := b.analytic_eighthLift.mono hsub
  have hd : ∀ z ∈ closedBall (0 : ℂ) R,
      HasFDerivWithinAt b.eighthLift (fderiv ℝ b.eighthLift z)
        (closedBall (0 : ℂ) R) z := fun z hz ↦
    (ha z hz).restrictScalars.hasStrictFDerivAt.hasFDerivAt.hasFDerivWithinAt
  have hdet : ∀ z ∈ closedBall (0 : ℂ) R,
      |(fderiv ℝ b.eighthLift z).det| = ‖deriv b.eighthLift z‖ ^ 2 := fun z hz ↦ by
    simp only [Complex.fderiv_det (ha z hz).differentiableAt, abs_sq]
  have hone : ∫ z in b.eighthLift '' closedBall (0 : ℂ) R, (1 : ℝ) =
      volume.real (b.eighthLift '' closedBall (0 : ℂ) R) := by
    simpa only [Measure.real, smul_eq_mul, mul_one] using
      (MeasureTheory.setIntegral_const (μ := volume)
        (s := b.eighthLift '' closedBall (0 : ℂ) R) (1 : ℝ))
  rw [← hone]
  rw [MeasureTheory.integral_image_eq_integral_abs_det_fderiv_smul volume
    measurableSet_closedBall hd (b.inj_eighthLift.mono hsub)]
  apply setIntegral_congr_fun measurableSet_closedBall
  intro z hz
  simp only [Pi.one_apply, smul_eq_mul, mul_one, hdet z hz]

private lemma intervalIntegral_eq_two_pi_mul_circleAverage {f : ℂ → ℝ} :
    (∫ θ in (0 : ℝ)..2 * Real.pi, f (circleMap 0 1 θ)) =
      (2 * Real.pi) * Real.circleAverage f 0 1 := by
  rw [Real.circleAverage_def]
  simp only [smul_eq_mul]
  field_simp [Real.pi_ne_zero]

/-- Parseval on circles for the derivative of the Prawitz lift. -/
lemma integral_circle_deriv_eighthLift_sq {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    (∫ θ in Ioc (0 : ℝ) (2 * Real.pi),
        ‖deriv b.eighthLift (circleMap 0 t θ)‖ ^ 2) =
      (2 * Real.pi) *
        ∑' n, ‖b.radialPrawitzCoeff (t ^ 8) n‖ ^ 2 := by
  have ht8 : 0 ≤ t ^ 8 := by positivity
  have ht81 : t ^ 8 < 1 := pow_lt_one₀ ht0 ht1 (by norm_num)
  have hpoint (θ : ℝ) : circleMap 0 t θ ∈ ball (0 : ℂ) 1 := by
    simp only [circleMap, zero_add, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg ht0, Complex.norm_exp_ofReal_mul_I, mul_one, mem_ball, dist_zero_right]
    exact ht1
  have hrewrite (θ : ℝ) :
      ‖deriv b.eighthLift (circleMap 0 t θ)‖ ^ 2 =
        ‖b.prawitzDerivative ((t ^ 8 : ℝ) * (circleMap 0 1 θ) ^ 8)‖ ^ 2 := by
    rw [b.deriv_eighthLift (hpoint θ)]
    congr 2
    simp only [circleMap, zero_add, Complex.ofReal_one, one_mul, mul_pow]
    push_cast
    rfl
  have hfcont : Continuous (fun θ : ℝ ↦
      ‖b.prawitzDerivative (((t ^ 8 : ℝ) : ℂ) * circleMap 0 1 θ)‖ ^ 2) := by
    rw [continuous_iff_continuousAt]
    intro θ
    have hm : ((t ^ 8 : ℝ) : ℂ) * circleMap 0 1 θ ∈ ball (0 : ℂ) 1 := by
      simp only [mem_ball, dist_zero_right, circleMap, zero_add, Complex.ofReal_one,
        one_mul, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg ht0, Complex.norm_exp_ofReal_mul_I, mul_one]
      exact ht81
    have hinner : ContinuousAt
        (fun φ : ℝ ↦ ((t ^ 8 : ℝ) : ℂ) * circleMap 0 1 φ) θ :=
      continuousAt_const.mul (continuous_circleMap 0 1).continuousAt
    have hout : ContinuousAt b.prawitzDerivative
        (((t ^ 8 : ℝ) : ℂ) * circleMap 0 1 θ) :=
      (b.analytic_prawitzDerivative _ hm).continuousAt
    have hc := ContinuousAt.comp
      (f := fun φ : ℝ ↦ ((t ^ 8 : ℝ) : ℂ) * circleMap 0 1 φ)
      (g := b.prawitzDerivative) hout hinner
    change ContinuousAt
      ((fun φ : ℝ ↦ ‖b.prawitzDerivative
        (((t ^ 8 : ℝ) : ℂ) * circleMap 0 1 φ)‖) ^ 2) θ
    exact hc.norm.pow 2
  rw [← intervalIntegral.integral_of_le Real.two_pi_pos.le]
  rw [intervalIntegral.integral_congr (fun θ _ ↦ hrewrite θ)]
  rw [integral_circleMap_pow_eight (f := fun w ↦
    ‖b.prawitzDerivative (((t ^ 8 : ℝ) : ℂ) * w)‖ ^ 2) hfcont]
  rw [intervalIntegral_eq_two_pi_mul_circleAverage
    (f := fun w ↦ ‖b.prawitzDerivative (((t ^ 8 : ℝ) : ℂ) * w)‖ ^ 2)]
  rw [b.circleAverage_norm_prawitzDerivative_sq ht8 ht81]

lemma volume_image_closedBall_eq_integral_tsum {R : ℝ} (hR0 : 0 ≤ R) (hR1 : R < 1) :
    volume.real (b.eighthLift '' closedBall (0 : ℂ) R) =
      ∫ t in Ioc (0 : ℝ) R,
        t * ((2 * Real.pi) *
          ∑' n, ‖b.radialPrawitzCoeff (t ^ 8) n‖ ^ 2) := by
  rw [b.volume_image_closedBall_eighthLift hR0 hR1]
  have hsub : closedBall (0 : ℂ) R ⊆ ball 0 1 := by
    intro z hz
    rw [mem_closedBall, dist_zero_right] at hz
    rw [mem_ball, dist_zero_right]
    exact hz.trans_lt hR1
  have hc : ContinuousOn (fun z : ℂ ↦ ‖deriv b.eighthLift z‖ ^ 2)
      (closedBall (0 : ℂ) R) := by
    intro z hz
    exact ((b.analytic_eighthLift.deriv z (hsub hz)).continuousAt.norm.pow 2).continuousWithinAt
  rw [fubini_ball hc]
  apply setIntegral_congr_fun measurableSet_Ioc
  intro t ht
  simp only [smul_eq_mul]
  rw [b.integral_circle_deriv_eighthLift_sq ht.1.le (ht.2.trans_lt hR1)]

lemma integrableOn_areaDensity {R : ℝ} (hR0 : 0 ≤ R) (hR1 : R < 1) :
    IntegrableOn
      (fun t : ℝ ↦ t * ((2 * Real.pi) *
        ∑' n, ‖b.radialPrawitzCoeff (t ^ 8) n‖ ^ 2))
      (Ioc (0 : ℝ) R) := by
  let q : ℝ := (R + 1) / 2
  have hq0 : 0 ≤ q := by dsimp [q]; linarith
  have hRq : R ≤ q := by dsimp [q]; linarith
  have hq1 : q < 1 := by dsimp [q]; linarith
  have hq81 : q ^ 8 < 1 := pow_lt_one₀ hq0 hq1 (by norm_num)
  have hqsum := b.summable_sq_radialPrawitzCoeff (by positivity : 0 ≤ q ^ 8) hq81
  have hterm : ∀ n, Measurable (fun t : ℝ ↦
      ‖b.radialPrawitzCoeff (t ^ 8) n‖ ^ 2) := by
    intro n
    unfold radialPrawitzCoeff
    fun_prop
  have hmeas : Measurable (fun t : ℝ ↦ t * ((2 * Real.pi) *
      ∑' n, ‖b.radialPrawitzCoeff (t ^ 8) n‖ ^ 2)) :=
    measurable_id.mul (measurable_const.mul (Measurable.tsum hterm))
  apply IntegrableOn.of_bound measure_Ioc_lt_top hmeas.aestronglyMeasurable
    (R * ((2 * Real.pi) *
      ∑' n, ‖b.radialPrawitzCoeff (q ^ 8) n‖ ^ 2))
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  have ht0 : 0 ≤ t := ht.1.le
  have htq : t ≤ q := ht.2.trans hRq
  have ht1 : t < 1 := ht.2.trans_lt hR1
  have ht81 : t ^ 8 < 1 := pow_lt_one₀ ht0 ht1 (by norm_num)
  have htsum := b.summable_sq_radialPrawitzCoeff (by positivity : 0 ≤ t ^ 8) ht81
  have hsum : (∑' n, ‖b.radialPrawitzCoeff (t ^ 8) n‖ ^ 2) ≤
      ∑' n, ‖b.radialPrawitzCoeff (q ^ 8) n‖ ^ 2 :=
    htsum.tsum_le_tsum (fun n ↦ b.radialPrawitzCoeff_sq_mono ht0 htq n) hqsum
  have hsum0 : 0 ≤ ∑' n, ‖b.radialPrawitzCoeff (t ^ 8) n‖ ^ 2 :=
    tsum_nonneg fun _ ↦ sq_nonneg _
  have hqsum0 : 0 ≤ ∑' n, ‖b.radialPrawitzCoeff (q ^ 8) n‖ ^ 2 :=
    tsum_nonneg fun _ ↦ sq_nonneg _
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg ht0
    (mul_nonneg (by positivity) hsum0))]
  exact mul_le_mul ht.2
    (mul_le_mul_of_nonneg_left hsum (by positivity))
    (mul_nonneg (by positivity) hsum0)
    hR0

lemma integral_areaTerm {R : ℝ} (hR0 : 0 ≤ R) (n : ℕ) :
    (∫ t in Ioc (0 : ℝ) R,
      t * ((2 * Real.pi) * ‖b.radialPrawitzCoeff (t ^ 8) n‖ ^ 2)) =
      Real.pi * (8 * n + 1) * ‖b.coeff n‖ ^ 2 * R ^ (16 * n + 2) := by
  rw [← intervalIntegral.integral_of_le hR0]
  simp only [radialPrawitzCoeff, b.prawitzCoeff_eq, norm_mul, Complex.norm_natCast,
    norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (by positivity) 8)]
  rw [intervalIntegral.integral_congr (fun t ht ↦ by
    rw [abs_of_nonneg]
    have ht' : t ∈ Icc (0 : ℝ) R := by simpa [uIcc_of_le hR0] using ht
    exact ht'.1)]
  have hpoint : (fun t : ℝ ↦
      t * ((2 * Real.pi) *
        (((8 * n + 1 : ℕ) : ℝ) * ‖b.coeff n‖ * (t ^ 8) ^ n) ^ 2)) =
      fun t : ℝ ↦
        (2 * Real.pi * (((8 * n + 1 : ℕ) : ℝ)) ^ 2 * ‖b.coeff n‖ ^ 2) *
          t ^ (16 * n + 1) := by
    funext t
    rw [← pow_mul]
    ring
  rw [hpoint, intervalIntegral.integral_const_mul, integral_pow]
  simp only [zero_pow (by omega : 16 * n + 2 ≠ 0), sub_zero]
  push_cast
  field_simp
  ring

/-- Each finite weighted coefficient sum is bounded by the area of the lift image. -/
lemma partial_coeff_area_le {R : ℝ} (hR0 : 0 ≤ R) (hR1 : R < 1) (N : ℕ) :
    (∑ n ∈ Finset.range N,
      Real.pi * (8 * n + 1) * ‖b.coeff n‖ ^ 2 * R ^ (16 * n + 2)) ≤
      volume.real (b.eighthLift '' closedBall (0 : ℂ) R) := by
  rw [b.volume_image_closedBall_eq_integral_tsum hR0 hR1]
  calc
    (∑ n ∈ Finset.range N,
        Real.pi * (8 * n + 1) * ‖b.coeff n‖ ^ 2 * R ^ (16 * n + 2)) =
        ∑ n ∈ Finset.range N, (∫ t in Ioc (0 : ℝ) R,
          t * ((2 * Real.pi) * ‖b.radialPrawitzCoeff (t ^ 8) n‖ ^ 2)) := by
      apply Finset.sum_congr rfl
      intro n _
      exact (b.integral_areaTerm hR0 n).symm
    _ = ∫ t in Ioc (0 : ℝ) R,
        ∑ n ∈ Finset.range N,
          t * ((2 * Real.pi) * ‖b.radialPrawitzCoeff (t ^ 8) n‖ ^ 2) := by
      rw [MeasureTheory.integral_finset_sum]
      intro n hn
      have hc : Continuous (fun t : ℝ ↦
          t * ((2 * Real.pi) * ‖b.radialPrawitzCoeff (t ^ 8) n‖ ^ 2)) := by
        unfold radialPrawitzCoeff
        fun_prop
      exact (hc.integrableOn_Icc.mono Ioc_subset_Icc_self le_rfl)
    _ = ∫ t in Ioc (0 : ℝ) R,
        t * ((2 * Real.pi) *
          ∑ n ∈ Finset.range N, ‖b.radialPrawitzCoeff (t ^ 8) n‖ ^ 2) := by
      apply setIntegral_congr_fun measurableSet_Ioc
      intro t _
      simp only [mul_assoc, Finset.mul_sum]
    _ ≤ ∫ t in Ioc (0 : ℝ) R,
        t * ((2 * Real.pi) *
          ∑' n, ‖b.radialPrawitzCoeff (t ^ 8) n‖ ^ 2) := by
      apply setIntegral_mono_of_nonneg
      · intro t ht
        exact mul_nonneg ht.1.le (mul_nonneg (by positivity)
          (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _))
      · intro t ht
        have ht0 : 0 ≤ t := ht.1.le
        have ht1 : t < 1 := ht.2.trans_lt hR1
        have ht81 : t ^ 8 < 1 := pow_lt_one₀ ht0 ht1 (by norm_num)
        have hs := b.summable_sq_radialPrawitzCoeff (by positivity : 0 ≤ t ^ 8) ht81
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left
            (hs.sum_le_tsum (Finset.range N) (fun _ _ ↦ sq_nonneg _)) (by positivity)) ht0
      · exact b.integrableOn_areaDensity hR0 hR1

lemma norm_G_le_growth (b : NormalizedUnivalent G) (hz : z ∈ ball (0 : ℂ) 1) :
    ‖G z‖ ≤ ‖z‖ / (1 - ‖z‖) ^ 2 := by
  by_cases hzero : z = 0
  · simp [hzero, b.map_zero]
  · let r : ℝ := ‖z‖
    let ζ : ℂ := z / (r : ℂ)
    have hr0 : 0 ≤ r := norm_nonneg z
    have hrpos : 0 < r := norm_pos_iff.mpr hzero
    have hr1 : r < 1 := by simpa only [r, mem_ball, dist_zero_right] using hz
    have hζ : ‖ζ‖ = 1 := by simp [ζ, r, hrpos.ne']
    have hzrepr : (r : ℂ) * ζ = z := by
      simp only [ζ, ← mul_div_assoc]
      exact mul_div_cancel_left₀ z (Complex.ofReal_ne_zero.mpr hrpos.ne')
    have hg := Erdos515.KoebeDistortion.radial_growth_le
      b.analytic b.inj b.map_zero b.deriv_zero hr0 hr1 hζ
    change ‖G ((r : ℂ) * ζ)‖ ≤ r / (1 - r) ^ 2 at hg
    simpa only [hzrepr, r] using hg

private lemma growth_mono {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) (hy1 : y < 1) :
    x / (1 - x) ^ 2 ≤ y / (1 - y) ^ 2 := by
  apply div_le_div₀ (hx.trans hxy) hxy (sq_pos_of_pos (sub_pos.mpr hy1))
  nlinarith [sq_nonneg (y - x)]

/-- Koebe growth for `G`, transferred through the eighth-power identity, bounds the area of the
lift image. -/
lemma volume_image_closedBall_eighthLift_le {R : ℝ} (hR0 : 0 ≤ R) (hR1 : R < 1) :
    volume.real (b.eighthLift '' closedBall (0 : ℂ) R) ≤
      Real.pi * (R ^ 8 / (1 - R ^ 8) ^ 2) ^ ((1 : ℝ) / 4) := by
  have hR81 : R ^ 8 < 1 := pow_lt_one₀ hR0 hR1 (by norm_num)
  let U : ℝ := (R ^ 8 / (1 - R ^ 8) ^ 2) ^ ((1 : ℝ) / 4)
  have hgrowth0 : 0 ≤ R ^ 8 / (1 - R ^ 8) ^ 2 :=
    div_nonneg (by positivity) (sq_nonneg _)
  have hU0 : 0 ≤ U := Real.rpow_nonneg hgrowth0 _
  have hsub : b.eighthLift '' closedBall (0 : ℂ) R ⊆ closedBall 0 (Real.sqrt U) := by
    rintro y ⟨z, hz, rfl⟩
    have hzNorm : ‖z‖ ≤ R := by simpa only [mem_closedBall, dist_zero_right] using hz
    have hzBall : z ∈ ball (0 : ℂ) 1 := by
      rw [mem_ball, dist_zero_right]
      exact hzNorm.trans_lt hR1
    have hz8Ball : z ^ 8 ∈ ball (0 : ℂ) 1 := pow_eight_mem_unitBall hzBall
    have hnorm8 : ‖z ^ 8‖ ≤ R ^ 8 := by
      rw [norm_pow]
      exact pow_le_pow_left₀ (norm_nonneg z) hzNorm 8
    have hGgrowth := (b.norm_G_le_growth hz8Ball).trans
      (growth_mono (norm_nonneg (z ^ 8)) hnorm8 hR81)
    have hsq : ‖b.eighthLift z‖ ^ 2 ≤ U := by
      rw [b.norm_eighthLift_sq hzBall]
      exact Real.rpow_le_rpow (norm_nonneg _) hGgrowth (by norm_num)
    rw [mem_closedBall, dist_zero_right]
    exact (Real.le_sqrt (norm_nonneg _) hU0).2 hsq
  calc
    volume.real (b.eighthLift '' closedBall (0 : ℂ) R) ≤
        volume.real (closedBall (0 : ℂ) (Real.sqrt U)) :=
      measureReal_mono hsub measure_closedBall_lt_top.ne
    _ = Real.pi * (Real.sqrt U) ^ 2 := Complex.volume_closedBall' (Real.sqrt_nonneg U)
    _ = Real.pi * U := by rw [Real.sq_sqrt hU0]
    _ = Real.pi * (R ^ 8 / (1 - R ^ 8) ^ 2) ^ ((1 : ℝ) / 4) := rfl

private lemma eighthRoot_pow_linear {s : ℝ} (hs : 0 ≤ s) (n : ℕ) :
    (s ^ ((8 : ℝ)⁻¹)) ^ (16 * n + 2) =
      s ^ ((2 * n : ℕ) + (1 : ℝ) / 4) := by
  rw [← Real.rpow_natCast]
  rw [← Real.rpow_mul hs]
  congr 1
  push_cast
  ring

private lemma growth_quarter_eq_kernel_factor {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    (s / (1 - s) ^ 2) ^ ((1 : ℝ) / 4) =
      s ^ ((1 : ℝ) / 4) * (1 - s) ^ (-(1 : ℝ) / 2) := by
  have hb : 0 ≤ 1 - s := sub_nonneg.mpr hs1
  rw [Real.div_rpow hs0 (sq_nonneg _) ((1 : ℝ) / 4)]
  rw [← Real.rpow_natCast_mul hb 2 ((1 : ℝ) / 4)]
  norm_num
  rw [Real.rpow_neg hb]
  simp only [div_eq_mul_inv]

/-- The finite-coefficient form of Prawitz's pointwise area inequality. -/
lemma partial_coeff_prawitz_pointwise {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (N : ℕ) :
    (∑ n ∈ Finset.range N,
      Real.pi * (8 * n + 1) * ‖b.coeff n‖ ^ 2 *
        s ^ ((2 * n : ℕ) + (1 : ℝ) / 4)) ≤
      Real.pi * s ^ ((1 : ℝ) / 4) * (1 - s) ^ (-(1 : ℝ) / 2) := by
  let R : ℝ := s ^ ((8 : ℝ)⁻¹)
  have hR0 : 0 ≤ R := Real.rpow_nonneg hs0.le _
  have hR1 : R < 1 := Real.rpow_lt_one hs0.le hs1 (by positivity)
  have hR8 : R ^ 8 = s := by
    exact Real.rpow_inv_natCast_pow hs0.le (by norm_num)
  calc
    (∑ n ∈ Finset.range N,
        Real.pi * (8 * n + 1) * ‖b.coeff n‖ ^ 2 *
          s ^ ((2 * n : ℕ) + (1 : ℝ) / 4)) =
        ∑ n ∈ Finset.range N,
          Real.pi * (8 * n + 1) * ‖b.coeff n‖ ^ 2 * R ^ (16 * n + 2) := by
      apply Finset.sum_congr rfl
      intro n _
      rw [eighthRoot_pow_linear hs0.le n]
    _ ≤ volume.real (b.eighthLift '' closedBall (0 : ℂ) R) :=
      b.partial_coeff_area_le hR0 hR1 N
    _ ≤ Real.pi * (R ^ 8 / (1 - R ^ 8) ^ 2) ^ ((1 : ℝ) / 4) :=
      b.volume_image_closedBall_eighthLift_le hR0 hR1
    _ = Real.pi * s ^ ((1 : ℝ) / 4) * (1 - s) ^ (-(1 : ℝ) / 2) := by
      rw [hR8, growth_quarter_eq_kernel_factor hs0.le hs1.le]
      ring

lemma partial_coeff_kernel_pointwise {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (N : ℕ) :
    (∑ n ∈ Finset.range N,
      (8 * n + 1) * ‖b.coeff n‖ ^ 2 *
        s ^ ((2 * n : ℕ) - (3 : ℝ) / 4)) ≤ Prawitz.koebeQuarterKernel s := by
  have hp := b.partial_coeff_prawitz_pointwise hs0 hs1 N
  have hfac : 0 < Real.pi * s := mul_pos Real.pi_pos hs0
  apply (mul_le_mul_iff_of_pos_left hfac).mp
  calc
    Real.pi * s *
        (∑ n ∈ Finset.range N,
          (8 * n + 1) * ‖b.coeff n‖ ^ 2 *
            s ^ ((2 * n : ℕ) - (3 : ℝ) / 4)) =
        ∑ n ∈ Finset.range N,
          Real.pi * (8 * n + 1) * ‖b.coeff n‖ ^ 2 *
            s ^ ((2 * n : ℕ) + (1 : ℝ) / 4) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n _
      have hpow : s * s ^ (((2 * n : ℕ) : ℝ) - 3 / 4) =
          s ^ (((2 * n : ℕ) : ℝ) + 1 / 4) := by
        calc
          s * s ^ (((2 * n : ℕ) : ℝ) - 3 / 4) =
              s ^ (1 : ℝ) * s ^ (((2 * n : ℕ) : ℝ) - 3 / 4) := by
            rw [Real.rpow_one]
          _ = s ^ ((1 : ℝ) + (((2 * n : ℕ) : ℝ) - 3 / 4)) :=
            (Real.rpow_add hs0 _ _).symm
          _ = s ^ (((2 * n : ℕ) : ℝ) + 1 / 4) := by congr 1 <;> ring
      rw [show Real.pi * s *
          ((8 * n + 1) * ‖b.coeff n‖ ^ 2 *
            s ^ ((2 * n : ℕ) - (3 : ℝ) / 4)) =
          Real.pi * (8 * n + 1) * ‖b.coeff n‖ ^ 2 *
            (s * s ^ (((2 * n : ℕ) : ℝ) - 3 / 4)) by push_cast; ring,
        hpow]
    _ ≤ Real.pi * s ^ ((1 : ℝ) / 4) * (1 - s) ^ (-(1 : ℝ) / 2) := hp
    _ = Real.pi * s * Prawitz.koebeQuarterKernel s := by
      rw [Prawitz.koebeQuarterKernel]
      have hpow : s * s ^ (-(3 : ℝ) / 4) = s ^ ((1 : ℝ) / 4) := by
        calc
          s * s ^ (-(3 : ℝ) / 4) = s ^ (1 : ℝ) * s ^ (-(3 : ℝ) / 4) := by
            rw [Real.rpow_one]
          _ = s ^ ((1 : ℝ) + (-(3 : ℝ) / 4)) := (Real.rpow_add hs0 _ _).symm
          _ = s ^ ((1 : ℝ) / 4) := by congr 1 <;> ring
      rw [show Real.pi * s *
          (s ^ (-(3 : ℝ) / 4) * (1 - s) ^ (-(1 : ℝ) / 2)) =
          Real.pi * (s * s ^ (-(3 : ℝ) / 4)) *
            (1 - s) ^ (-(1 : ℝ) / 2) by ring, hpow]

lemma integral_kernel_coeff_term {r : ℝ} (hr0 : 0 ≤ r) (n : ℕ) :
    (∫ s in Ioc (0 : ℝ) r,
      (8 * n + 1) * ‖b.coeff n‖ ^ 2 *
        s ^ ((2 * n : ℕ) - (3 : ℝ) / 4)) =
      4 * ‖b.coeff n‖ ^ 2 *
        r ^ ((2 * n : ℕ) + (1 : ℝ) / 4) := by
  rw [← intervalIntegral.integral_of_le hr0]
  rw [intervalIntegral.integral_const_mul]
  rw [integral_rpow (Or.inl (by
    have hn : (0 : ℝ) ≤ (2 * n : ℕ) := by positivity
    linarith))]
  have hexp : 0 < (2 * n : ℕ) + (1 : ℝ) / 4 := by positivity
  have heq : ((2 * n : ℕ) : ℝ) - 3 / 4 + 1 =
      ((2 * n : ℕ) : ℝ) + 1 / 4 := by ring
  rw [heq, Real.zero_rpow hexp.ne', sub_zero]
  push_cast
  field_simp
  ring

lemma partial_coeff_integral_le {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) (N : ℕ) :
    4 * (∑ n ∈ Finset.range N,
      ‖b.coeff n‖ ^ 2 * r ^ ((2 * n : ℕ) + (1 : ℝ) / 4)) ≤
      ∫ s in Ioc (0 : ℝ) r, Prawitz.koebeQuarterKernel s := by
  have hkInt : IntegrableOn Prawitz.koebeQuarterKernel (Ioc (0 : ℝ) r) :=
    Prawitz.integrableOn_koebeQuarterKernel.mono
      (Ioc_subset_Ioc_right hr1.le) le_rfl
  have htermInt : ∀ n ∈ Finset.range N, IntegrableOn
      (fun s : ℝ ↦ (8 * n + 1) * ‖b.coeff n‖ ^ 2 *
        s ^ ((2 * n : ℕ) - (3 : ℝ) / 4)) (Ioc (0 : ℝ) r) := by
    intro n hn
    apply hkInt.mono'
    · exact (by fun_prop : Measurable (fun s : ℝ ↦
          (8 * n + 1) * ‖b.coeff n‖ ^ 2 *
            s ^ ((2 * n : ℕ) - (3 : ℝ) / 4))).aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
      have hs1 : s < 1 := hs.2.trans_lt hr1
      have hnonneg : 0 ≤ (8 * n + 1) * ‖b.coeff n‖ ^ 2 *
          s ^ ((2 * n : ℕ) - (3 : ℝ) / 4) :=
        mul_nonneg (mul_nonneg (by positivity) (sq_nonneg _))
          (Real.rpow_nonneg hs.1.le _)
      rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
      calc
        (8 * n + 1) * ‖b.coeff n‖ ^ 2 *
            s ^ ((2 * n : ℕ) - (3 : ℝ) / 4) ≤
            ∑ k ∈ Finset.range (n + 1),
              (8 * k + 1) * ‖b.coeff k‖ ^ 2 *
                s ^ ((2 * k : ℕ) - (3 : ℝ) / 4) := by
          refine Finset.single_le_sum
            (f := fun k ↦ (8 * k + 1) * ‖b.coeff k‖ ^ 2 *
              s ^ ((2 * k : ℕ) - (3 : ℝ) / 4))
            (s := Finset.range (n + 1)) (a := n) ?_
            (Finset.mem_range.mpr (Nat.lt_succ_self n))
          intro k hk
          exact mul_nonneg (mul_nonneg (by positivity) (sq_nonneg _))
            (Real.rpow_nonneg hs.1.le _)
        _ ≤ Prawitz.koebeQuarterKernel s :=
          b.partial_coeff_kernel_pointwise hs.1 hs1 (n + 1)
  calc
    4 * (∑ n ∈ Finset.range N,
        ‖b.coeff n‖ ^ 2 * r ^ ((2 * n : ℕ) + (1 : ℝ) / 4)) =
        ∑ n ∈ Finset.range N,
          (∫ s in Ioc (0 : ℝ) r,
            (8 * n + 1) * ‖b.coeff n‖ ^ 2 *
              s ^ ((2 * n : ℕ) - (3 : ℝ) / 4)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n _
      rw [b.integral_kernel_coeff_term hr0.le n]
      ring
    _ = ∫ s in Ioc (0 : ℝ) r,
        ∑ n ∈ Finset.range N,
          (8 * n + 1) * ‖b.coeff n‖ ^ 2 *
            s ^ ((2 * n : ℕ) - (3 : ℝ) / 4) := by
      rw [MeasureTheory.integral_finset_sum]
      exact htermInt
    _ ≤ ∫ s in Ioc (0 : ℝ) r, Prawitz.koebeQuarterKernel s := by
      apply setIntegral_mono_of_nonneg
      · intro s hs
        exact Finset.sum_nonneg fun n _ ↦
          mul_nonneg (mul_nonneg (by positivity) (sq_nonneg _))
            (Real.rpow_nonneg hs.1.le _)
      · intro s hs
        exact b.partial_coeff_kernel_pointwise hs.1 (hs.2.trans_lt hr1) N
      · exact hkInt

lemma norm_radialCoeff_sq {r : ℝ} (hr : 0 ≤ r) (n : ℕ) :
    ‖b.radialCoeff r n‖ ^ 2 =
      ‖b.coeff n‖ ^ 2 * r ^ ((2 * n : ℕ) : ℝ) := by
  simp only [radialCoeff, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hr, mul_pow]
  rw [Real.rpow_natCast]
  rw [← pow_mul]
  congr 1
  simp [Nat.mul_comm]

lemma tsum_radialCoeff_sq_le {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    (∑' n, ‖b.radialCoeff r n‖ ^ 2) ≤
      (∫ s in Ioc (0 : ℝ) r, Prawitz.koebeQuarterKernel s) /
        (4 * r ^ ((1 : ℝ) / 4)) := by
  apply Real.tsum_le_of_sum_range_le (fun n ↦ sq_nonneg _)
  intro N
  have hden : 0 < 4 * r ^ ((1 : ℝ) / 4) :=
    mul_pos (by norm_num) (Real.rpow_pos_of_pos hr _)
  apply (le_div_iff₀ hden).2
  calc
    (∑ n ∈ Finset.range N, ‖b.radialCoeff r n‖ ^ 2) *
        (4 * r ^ ((1 : ℝ) / 4)) =
      4 * ∑ n ∈ Finset.range N,
        ‖b.coeff n‖ ^ 2 * r ^ ((2 * n : ℕ) + (1 : ℝ) / 4) := by
      rw [Finset.sum_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n _
      rw [b.norm_radialCoeff_sq hr.le]
      rw [Real.rpow_add hr]
      ring
    _ ≤ ∫ s in Ioc (0 : ℝ) r, Prawitz.koebeQuarterKernel s :=
      b.partial_coeff_integral_le hr hr1 N

lemma radialQuotient_quarter_eq_norm_H_sq {r θ : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    Prawitz.radialQuotient G r θ ^ Prawitz.quarter =
      ‖b.H (Prawitz.circlePoint r θ)‖ ^ 2 := by
  have hzmem : Prawitz.circlePoint r θ ∈ ball (0 : ℂ) 1 := by
    simp only [Prawitz.circlePoint, mem_ball, dist_zero_right, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hr, Complex.norm_exp, Complex.mul_re, Complex.ofReal_re,
      Complex.I_re, mul_zero, Complex.ofReal_im, Complex.I_im, zero_mul, sub_zero,
      Real.exp_zero, mul_one]
    exact hr1
  have hznorm : ‖Prawitz.circlePoint r θ‖ = r := by
    simp only [Prawitz.circlePoint, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr,
      Complex.norm_exp, Complex.mul_re, Complex.ofReal_re, Complex.I_re, mul_zero,
      Complex.ofReal_im, Complex.I_im, zero_mul, sub_zero, Real.exp_zero, mul_one]
  rw [Prawitz.radialQuotient, b.G_eq_z_mul_H_pow hzmem, norm_mul, hznorm, norm_pow]
  rw [mul_div_cancel_left₀ _ hr.ne']
  simp only [Prawitz.quarter]
  rw [← Real.rpow_natCast]
  rw [← Real.rpow_mul (norm_nonneg (b.H (Prawitz.circlePoint r θ)))]
  norm_num [Real.rpow_two]

lemma angularIntegral_norm_H_sq {r : ℝ} :
    (∫ θ in Prawitz.angularInterval,
        ‖b.H (Prawitz.circlePoint r θ)‖ ^ 2) =
      (2 * Real.pi) *
        Real.circleAverage (fun w ↦ ‖b.H ((r : ℂ) * w)‖ ^ 2) 0 1 := by
  rw [Prawitz.angularInterval,
    ← intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ 2 * Real.pi)]
  rw [Real.circleAverage_def]
  simp only [smul_eq_mul, circleMap, zero_add, Complex.ofReal_one, one_mul,
    Prawitz.circlePoint]
  field_simp [Real.pi_ne_zero]
  apply intervalIntegral.integral_congr
  intro θ _
  change ‖b.H ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))‖ ^ 2 =
    ‖b.H ((r : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))‖ ^ 2
  rw [mul_comm (θ : ℂ) Complex.I]

/-- Prawitz's quarter-power inequality for normalized univalent disk maps. -/
theorem prawitzQuarterBound (b : NormalizedUnivalent G) :
    Prawitz.PrawitzQuarterBound G := by
  intro r hr hr1
  have htsum := tsum_radialCoeff_sq_le (b := b) hr hr1
  calc
    (∫ θ in Prawitz.angularInterval,
        Prawitz.radialQuotient G r θ ^ Prawitz.quarter) =
        ∫ θ in Prawitz.angularInterval,
          ‖b.H (Prawitz.circlePoint r θ)‖ ^ 2 := by
      apply setIntegral_congr_fun measurableSet_Ioc
      intro θ _
      exact b.radialQuotient_quarter_eq_norm_H_sq hr hr1
    _ = (2 * Real.pi) *
        Real.circleAverage (fun w ↦ ‖b.H ((r : ℂ) * w)‖ ^ 2) 0 1 :=
      b.angularIntegral_norm_H_sq
    _ = (2 * Real.pi) * ∑' n, ‖b.radialCoeff r n‖ ^ 2 := by
      rw [b.circleAverage_norm_H_sq hr.le hr1]
    _ ≤ (2 * Real.pi) *
        ((∫ s in Ioc (0 : ℝ) r, Prawitz.koebeQuarterKernel s) /
          (4 * r ^ ((1 : ℝ) / 4))) :=
      mul_le_mul_of_nonneg_left htsum (mul_nonneg (by norm_num) Real.pi_pos.le)
    _ = r ^ (-Prawitz.quarter) * (Real.pi / 2) *
        ∫ s in Ioc (0 : ℝ) r, Prawitz.koebeQuarterKernel s := by
      have hrpow : r ^ ((1 : ℝ) / 4) ≠ 0 := (Real.rpow_pos_of_pos hr _).ne'
      rw [Prawitz.quarter, Real.rpow_neg hr.le]
      field_simp [hrpow]
      ring

end NormalizedUnivalent

/-- Prawitz's quarter-power inequality for every normalized univalent disk map. -/
theorem prawitzQuarterBound_of_normalized_univalent {G : ℂ → ℂ}
    (hG : AnalyticOnNhd ℂ G (ball 0 1)) (hinj : InjOn G (ball 0 1))
    (hG0 : G 0 = 0) (hdG0 : deriv G 0 = 1) :
    Prawitz.PrawitzQuarterBound G :=
  NormalizedUnivalent.prawitzQuarterBound (NormalizedUnivalent.mk hG hinj hG0 hdG0)

/-- The normalized-univalent Hardy `1/4` estimate used in the LRW short-path argument. -/
theorem hardyQuarterBound_of_normalized_univalent {G : ℂ → ℂ}
    (hG : AnalyticOnNhd ℂ G (ball 0 1)) (hinj : InjOn G (ball 0 1))
    (hG0 : G 0 = 0) (hdG0 : deriv G 0 = 1) :
    Prawitz.HardyQuarterBound G Prawitz.hardyQuarterConstant := by
  exact Prawitz.hardy_quarter_of_prawitz G
    (prawitzQuarterBound_of_normalized_univalent hG hinj hG0 hdG0)
    (KoebeDistortion.koebeUpperBound_of_normalized_univalent hG hinj hG0 hdG0)

end Erdos515.PrawitzProof
