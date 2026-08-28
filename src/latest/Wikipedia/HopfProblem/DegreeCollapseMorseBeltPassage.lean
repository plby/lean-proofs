import Wikipedia.SmoothSixDPoincare.MorseBeltFaceFlow
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Exact model passage from either side of a one-handle belt

For positive normal size s, the upper-level point with coordinates
(rho s u, rho sqrt(1+s^2) v) flows to the lower-level point
(rho sqrt(1+s^2) u, rho s v). The whole segment lies in the standard
closed Morse block. As s tends to zero, the lower point tends to the
actual attaching core in direction u.
-/

noncomputable section

open Set Function Metric
open scoped ContDiff
open Wikipedia.SmoothSixDPoincare

namespace Wikipedia.HopfProblem.DegreeCollapse.BeltPassage

def time (s : ℝ) : ℝ := Real.log (Real.sqrt (1 + s ^ 2) / s)

theorem time_nonneg {s : ℝ} (hs : 0 < s) : 0 ≤ time s := by
  have hroot := Real.sqrt_nonneg (1 + s ^ 2)
  have hsquare := Real.sq_sqrt (show 0 ≤ 1 + s ^ 2 by positivity)
  apply Real.log_nonneg
  apply (le_div_iff₀ hs).mpr
  nlinarith

theorem exp_time {s : ℝ} (hs : 0 < s) :
    Real.exp (time s) = Real.sqrt (1 + s ^ 2) / s :=
  Real.exp_log (div_pos (Real.sqrt_pos.mpr (by positivity)) hs)

variable {N P : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N]
  [NormedAddCommGroup P] [NormedSpace ℝ P]

def upper (ρ s : ℝ) (u : N) (v : P) : N × P :=
  ((ρ * s) • u, (ρ * Real.sqrt (1 + s ^ 2)) • v)

def lower (ρ s : ℝ) (u : N) (v : P) : N × P :=
  ((ρ * Real.sqrt (1 + s ^ 2)) • u, (ρ * s) • v)

theorem descentFlow_time (ρ : ℝ) {s : ℝ} (hs : 0 < s) (u : N) (v : P) :
    MorseHandle.descentFlow (time s) (upper ρ s u v) = lower ρ s u v := by
  have hr : Real.sqrt (1 + s ^ 2) ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
  apply Prod.ext
  · change Real.exp (time s) • ((ρ * s) • u) = (ρ * Real.sqrt (1 + s ^ 2)) • u
    rw [exp_time hs, smul_smul]
    congr 1
    field_simp
  · change Real.exp (-time s) • ((ρ * Real.sqrt (1 + s ^ 2)) • v) = (ρ * s) • v
    rw [Real.exp_neg, exp_time hs, smul_smul]
    congr 1
    field_simp

theorem descentFlow_mem_block {ρ s : ℝ} (hρ : 0 < ρ) (hs : 0 < s) (hs₁ : s ≤ 1)
    {u : N} (hu : ‖u‖ = 1) {v : P} (hv : ‖v‖ = 1) {t : ℝ}
    (ht : t ∈ Icc 0 (time s)) :
    MorseHandle.descentFlow t (upper ρ s u v) ∈
      closedBall (0 : N) (2 * ρ) ×ˢ closedBall (0 : P) (2 * ρ) := by
  have hrpos : 0 < Real.sqrt (1 + s ^ 2) := Real.sqrt_pos.mpr (by positivity)
  have hr : Real.sqrt (1 + s ^ 2) ≤ 2 :=
    Real.sqrt_le_iff.mpr ⟨by norm_num, by nlinarith⟩
  have hpos : 0 ≤ ρ * s := (mul_pos hρ hs).le
  constructor
  · rw [mem_closedBall_zero_iff, MorseHandle.norm_descentFlow_fst]
    change Real.exp t * ‖(ρ * s) • u‖ ≤ 2 * ρ
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hpos, hu, mul_one]
    calc
      _ ≤ Real.exp (time s) * (ρ * s) := mul_le_mul_of_nonneg_right
        (Real.exp_le_exp.mpr ht.2) hpos
      _ = ρ * Real.sqrt (1 + s ^ 2) := by rw [exp_time hs]; field_simp
      _ ≤ ρ * 2 := mul_le_mul_of_nonneg_left hr hρ.le
      _ = 2 * ρ := mul_comm _ _
  · rw [mem_closedBall_zero_iff, MorseHandle.norm_descentFlow_snd]
    change Real.exp (-t) * ‖(ρ * Real.sqrt (1 + s ^ 2)) • v‖ ≤ 2 * ρ
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (mul_pos hρ hrpos), hv, mul_one]
    calc
      _ ≤ ρ * Real.sqrt (1 + s ^ 2) := mul_le_of_le_one_left (mul_pos hρ hrpos).le
        (Real.exp_le_one_iff.mpr (neg_nonpos.mpr ht.1))
      _ ≤ ρ * 2 := mul_le_mul_of_nonneg_left hr hρ.le
      _ = 2 * ρ := mul_comm _ _

theorem contDiff_lower (ρ : ℝ) (u : N) (v : P) : ContDiff ℝ ∞ (fun s => lower ρ s u v) :=
  ((contDiff_const.mul ((contDiff_const.add (contDiff_id.pow 2)).sqrt
    (fun _ => by positivity))).smul contDiff_const).prodMk
      ((contDiff_const.mul contDiff_id).smul contDiff_const)

theorem lower_zero (ρ : ℝ) (u : N) (v : P) : lower ρ 0 u v = (ρ • u, 0) := by
  simp only [lower, zero_pow (by decide : 2 ≠ 0), add_zero, Real.sqrt_one, mul_one,
    mul_zero, zero_smul]

theorem upper_neg (ρ s : ℝ) (u : N) (v : P) :
    upper ρ (-s) u v = upper ρ s (-u) v := by
  simp only [upper, neg_sq, mul_neg, neg_smul, smul_neg]

theorem upper_height (ρ s : ℝ) {u : N} (hu : ‖u‖ = 1) {v : P} (hv : ‖v‖ = 1) :
    MorseHandle.quadratic (upper ρ s u v) = ρ ^ 2 := by
  simp only [MorseHandle.quadratic, upper, norm_smul, Real.norm_eq_abs, hu, hv, mul_one,
    sq_abs, mul_pow, Real.sq_sqrt (show 0 ≤ 1 + s ^ 2 by positivity)]
  ring

theorem contDiff_upper (ρ : ℝ) (u : N) (v : P) : ContDiff ℝ ∞ (fun s => upper ρ s u v) :=
  ((contDiff_const.mul contDiff_id).smul contDiff_const).prodMk
    ((contDiff_const.mul ((contDiff_const.add (contDiff_id.pow 2)).sqrt
      (fun _ => by positivity))).smul contDiff_const)

theorem upper_zero (ρ : ℝ) (u : N) (v : P) : upper ρ 0 u v = (0, ρ • v) := by
  simp only [upper, zero_pow (by decide : 2 ≠ 0), add_zero, Real.sqrt_one, mul_one,
    mul_zero, zero_smul]

theorem upper_mem_block {ρ s : ℝ} (hρ : 0 < ρ) (hs : |s| ≤ 1)
    {u : N} (hu : ‖u‖ = 1) {v : P} (hv : ‖v‖ = 1) :
    upper ρ s u v ∈ closedBall (0 : N) (2 * ρ) ×ˢ closedBall (0 : P) (2 * ρ) := by
  have hrpos : 0 < Real.sqrt (1 + s ^ 2) := Real.sqrt_pos.mpr (by positivity)
  have hr : Real.sqrt (1 + s ^ 2) ≤ 2 := Real.sqrt_le_iff.mpr
    ⟨by norm_num, by nlinarith [sq_abs s, abs_nonneg s]⟩
  constructor
  · rw [mem_closedBall_zero_iff]
    change ‖(ρ * s) • u‖ ≤ 2 * ρ
    rw [norm_smul, Real.norm_eq_abs, hu, mul_one, abs_mul, abs_of_pos hρ]
    have hh := mul_le_mul_of_nonneg_left hs hρ.le
    linarith
  · rw [mem_closedBall_zero_iff]
    change ‖(ρ * Real.sqrt (1 + s ^ 2)) • v‖ ≤ 2 * ρ
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (mul_pos hρ hrpos), hv, mul_one]
    exact (mul_le_mul_of_nonneg_left hr hρ.le).trans_eq (mul_comm _ _)

end Wikipedia.HopfProblem.DegreeCollapse.BeltPassage
