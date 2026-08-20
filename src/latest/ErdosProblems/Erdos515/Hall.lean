/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos515.Subharmonic

/-!
# Hall's radial lemma: explicit kernel and proved analytic interface

This file formalizes the potential-theoretic core used in the Lewis--Rossi--Weitsman
resolution of Erdős Problem 515. Mathlib currently has no subharmonic/Riesz-decomposition API,
so the two genuinely analytic projection estimates remain ordinary theorem arguments of
`hall_radial`. Everything after those estimates—including the good-direction set, the exact
inner/outer split, angular measure bookkeeping, and extraction of a good ray—is proved here.

The file also proves the explicit disk Green-kernel identities and both estimates used in Hall's
argument. The disjoint-radial-arcs theorem discharges the complete dyadic summation from its
far- and near-shell hypotheses. The inner theorem performs the Riesz-kernel/Tonelli/Chebyshev
steps from explicit measurability, one-kernel, threshold, and logarithmic-mass hypotheses.
No declaration in this file introduces an unproved constant.
-/

open Filter InnerProductSpace MeasureTheory Set
open scoped ENNReal NNReal Topology BigOperators

namespace Erdos515

def unitDisk : Set ℂ := Metric.ball 0 1

/-! ### The superharmonic normalization used by Hall -/

/-- A finite continuous real-valued function is superharmonic on `U` when its negative is
subharmonic there.  Keeping this definition tied to `SubharmonicOn` makes the hypotheses of the
Hall lemma use the same circle-submean notion as the rest of the development. -/
def SuperharmonicOn (v : ℂ → ℝ) (U : Set ℂ) : Prop :=
  SubharmonicOn (fun z ↦ -v z) U

namespace SuperharmonicOn

variable {v : ℂ → ℝ} {U V : Set ℂ}

lemma isOpen (hv : SuperharmonicOn v U) : IsOpen U :=
  SubharmonicOn.isOpen hv

lemma continuousOn (hv : SuperharmonicOn v U) : ContinuousOn v U := by
  convert (SubharmonicOn.continuousOn hv).neg using 1
  ext z
  simp

/-- Circle-supermean inequality, in the sign convention used for the positive function
`ψ = 1 - w` in Hall's proof. -/
lemma supermean (hv : SuperharmonicOn v U) {c : ℂ} (hc : c ∈ U) {R : ℝ} (hR : 0 < R)
    (hball : Metric.closedBall c R ⊆ U) :
    Real.circleAverage v c R ≤ v c := by
  have hi : CircleIntegrable v c R :=
    (hv.continuousOn.mono (Metric.sphere_subset_closedBall.trans hball)).circleIntegrable hR.le
  have hneg := SubharmonicOn.submean hv hc hR hball
  have havg : Real.circleAverage (fun z ↦ -v z) c R =
      -Real.circleAverage v c R := by
    simpa using (Real.circleAverage_fun_smul (a := (-1 : ℝ)) (f := v) (c := c) (R := R))
  rw [havg] at hneg
  linarith

lemma mono (hv : SuperharmonicOn v U) (hV : IsOpen V) (hVU : V ⊆ U) :
    SuperharmonicOn v V :=
  SubharmonicOn.mono hv hV hVU

end SuperharmonicOn

/-- Passing from Hall's bounded subharmonic function `w` to `ψ = 1 - w` produces a
superharmonic function. -/
lemma superharmonicOn_one_sub {w : ℂ → ℝ} {U : Set ℂ}
    (hw : SubharmonicOn w U) :
    SuperharmonicOn (fun z ↦ 1 - w z) U := by
  unfold SuperharmonicOn
  convert hw.affine (a := (1 : ℝ)) (b := -1) (by norm_num) using 1
  ext z
  ring

/-- The elementary normalization facts for the positive superharmonic function in Hall's
argument. -/
lemma hall_superharmonic_normalization {w : ℂ → ℝ} {δ : ℝ}
    (hw : SubharmonicOn w unitDisk)
    (hw_le_one : ∀ z ∈ unitDisk, w z ≤ 1)
    (hw_center : w 0 = 1 - δ) :
    SuperharmonicOn (fun z ↦ 1 - w z) unitDisk ∧
      (∀ z ∈ unitDisk, 0 ≤ 1 - w z) ∧ (1 - w 0 = δ) := by
  refine ⟨superharmonicOn_one_sub hw, ?_, ?_⟩
  · intro z hz
    linarith [hw_le_one z hz]
  · rw [hw_center]
    ring

noncomputable def diskGreen (z ζ : ℂ) : ℝ :=
  Real.log (‖1 - (starRingEnd ℂ) ζ * z‖ / ‖z - ζ‖)

/-- Symmetry of the disk Green kernel. -/
lemma diskGreen_comm (z ζ : ℂ) : diskGreen z ζ = diskGreen ζ z := by
  have hnum : ‖1 - (starRingEnd ℂ) ζ * z‖ =
      ‖1 - (starRingEnd ℂ) z * ζ‖ := by
    rw [← Complex.norm_conj]
    congr 1
    simp only [map_sub, map_one, map_mul, starRingEnd_self_apply]
    ring
  simp only [diskGreen, hnum, norm_sub_rev]

/-- The nonnegative extended-real Green kernel, with its genuine logarithmic pole on the
diagonal. The real-valued `diskGreen` is used for off-diagonal algebra. -/
noncomputable def diskGreenENNReal (z ζ : ℂ) : ℝ≥0∞ :=
  if z = ζ then ⊤ else ENNReal.ofReal (diskGreen z ζ)

@[simp] lemma diskGreenENNReal_self (z : ℂ) : diskGreenENNReal z z = ⊤ := by
  simp [diskGreenENNReal]

lemma diskGreenENNReal_of_ne {z ζ : ℂ} (h : z ≠ ζ) :
    diskGreenENNReal z ζ = ENNReal.ofReal (diskGreen z ζ) := by
  simp [diskGreenENNReal, h]

lemma diskGreen_normSq_identity (z ζ : ℂ) :
    ‖1 - (starRingEnd ℂ) ζ * z‖ ^ 2 - ‖z - ζ‖ ^ 2 =
      (1 - ‖z‖ ^ 2) * (1 - ‖ζ‖ ^ 2) := by
  simpa only [Complex.normSq_eq_norm_sq] using
    (show Complex.normSq (1 - (starRingEnd ℂ) ζ * z) - Complex.normSq (z - ζ) =
      (1 - Complex.normSq z) * (1 - Complex.normSq ζ) by
      rw [Complex.normSq_sub, Complex.normSq_sub, Complex.normSq_mul,
        Complex.normSq_conj]
      norm_num [map_one, map_mul, map_star]
      ring)

lemma norm_sub_le_norm_one_sub_conj_mul {z ζ : ℂ}
    (hz : ‖z‖ < 1) (hζ : ‖ζ‖ < 1) :
    ‖z - ζ‖ ≤ ‖1 - (starRingEnd ℂ) ζ * z‖ := by
  rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)]
  have hz' : 0 ≤ 1 - ‖z‖ ^ 2 := by
    nlinarith [mul_nonneg (show 0 ≤ 1 - ‖z‖ by linarith) (show 0 ≤ 1 + ‖z‖ by positivity)]
  have hζ' : 0 ≤ 1 - ‖ζ‖ ^ 2 := by
    nlinarith [mul_nonneg (show 0 ≤ 1 - ‖ζ‖ by linarith) (show 0 ≤ 1 + ‖ζ‖ by positivity)]
  nlinarith [diskGreen_normSq_identity z ζ, mul_nonneg hz' hζ']

lemma diskGreen_nonneg {z ζ : ℂ} (hz : ‖z‖ < 1) (hζ : ‖ζ‖ < 1)
    (hne : z ≠ ζ) : 0 ≤ diskGreen z ζ := by
  apply Real.log_nonneg
  rw [one_le_div (norm_pos_iff.mpr (sub_ne_zero.mpr hne))]
  exact norm_sub_le_norm_one_sub_conj_mul hz hζ

lemma diskGreen_sq_ratio {z ζ : ℂ} (hne : z ≠ ζ) :
    (‖1 - (starRingEnd ℂ) ζ * z‖ / ‖z - ζ‖) ^ 2 =
      1 + ((1 - ‖z‖ ^ 2) * (1 - ‖ζ‖ ^ 2)) / ‖z - ζ‖ ^ 2 := by
  have hd : ‖z - ζ‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hne)
  rw [div_pow]
  apply (div_eq_iff (pow_ne_zero 2 hd)).mpr
  rw [add_mul, one_mul, div_mul_cancel₀ _ (pow_ne_zero 2 hd)]
  linarith [diskGreen_normSq_identity z ζ]

lemma diskGreen_le_greenQuotient {z ζ : ℂ}
    (hz : ‖z‖ < 1) (hζ : ‖ζ‖ < 1) (hne : z ≠ ζ) :
    diskGreen z ζ ≤
      ((1 - ‖z‖ ^ 2) * (1 - ‖ζ‖ ^ 2)) / (2 * ‖z - ζ‖ ^ 2) := by
  let q : ℝ := ‖1 - (starRingEnd ℂ) ζ * z‖ / ‖z - ζ‖
  let x : ℝ := ((1 - ‖z‖ ^ 2) * (1 - ‖ζ‖ ^ 2)) / ‖z - ζ‖ ^ 2
  have hd : 0 < ‖z - ζ‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  have hn : 0 < ‖1 - (starRingEnd ℂ) ζ * z‖ :=
    lt_of_lt_of_le hd (norm_sub_le_norm_one_sub_conj_mul hz hζ)
  have hq : 0 < q := div_pos hn hd
  have hzsq : 0 ≤ 1 - ‖z‖ ^ 2 := by
    nlinarith [mul_nonneg (show 0 ≤ 1 - ‖z‖ by linarith) (show 0 ≤ 1 + ‖z‖ by positivity)]
  have hζsq : 0 ≤ 1 - ‖ζ‖ ^ 2 := by
    nlinarith [mul_nonneg (show 0 ≤ 1 - ‖ζ‖ by linarith) (show 0 ≤ 1 + ‖ζ‖ by positivity)]
  have hx0 : 0 ≤ x := by
    apply div_nonneg
    · exact mul_nonneg hzsq hζsq
    · positivity
  have hsq : q ^ 2 = 1 + x := by
    simpa [q, x] using diskGreen_sq_ratio (z := z) (ζ := ζ) hne
  have hlog : Real.log (1 + x) ≤ x := by
    have : 0 < 1 + x := by positivity
    simpa using Real.log_le_sub_one_of_pos this
  have htwo : 2 * diskGreen z ζ = Real.log (1 + x) := by
    rw [← hsq, Real.log_pow]
    simp [diskGreen, q]
  rw [show ((1 - ‖z‖ ^ 2) * (1 - ‖ζ‖ ^ 2)) /
      (2 * ‖z - ζ‖ ^ 2) = x / 2 by simp [x, div_eq_mul_inv]; ring]
  nlinarith

lemma diskGreen_le_two_mul {z ζ : ℂ}
    (hz : ‖z‖ < 1) (hζ : ‖ζ‖ < 1) (hne : z ≠ ζ) :
    diskGreen z ζ ≤
      2 * (1 - ‖z‖) * (1 - ‖ζ‖) / ‖z - ζ‖ ^ 2 := by
  have hbase := diskGreen_le_greenQuotient hz hζ hne
  have hd : 0 < ‖z - ζ‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hne))
  have hz0 : 0 ≤ ‖z‖ := norm_nonneg _
  have hζ0 : 0 ≤ ‖ζ‖ := norm_nonneg _
  have hnum : (1 - ‖z‖ ^ 2) * (1 - ‖ζ‖ ^ 2) ≤
      4 * (1 - ‖z‖) * (1 - ‖ζ‖) := by
    have hzfac : 1 - ‖z‖ ^ 2 = (1 - ‖z‖) * (1 + ‖z‖) := by ring
    have hζfac : 1 - ‖ζ‖ ^ 2 = (1 - ‖ζ‖) * (1 + ‖ζ‖) := by ring
    rw [hzfac, hζfac]
    have h1z : 0 ≤ 1 - ‖z‖ := by linarith
    have h1ζ : 0 ≤ 1 - ‖ζ‖ := by linarith
    calc
      (1 - ‖z‖) * (1 + ‖z‖) * ((1 - ‖ζ‖) * (1 + ‖ζ‖)) =
          ((1 - ‖z‖) * (1 - ‖ζ‖)) * ((1 + ‖z‖) * (1 + ‖ζ‖)) := by ring
      _ ≤ ((1 - ‖z‖) * (1 - ‖ζ‖)) * 4 := by
        apply mul_le_mul_of_nonneg_left
        · have hzplus : 1 + ‖z‖ ≤ (2 : ℝ) := by linarith
          have hζplus : 1 + ‖ζ‖ ≤ (2 : ℝ) := by linarith
          have hp := mul_le_mul hzplus hζplus
            (show 0 ≤ 1 + ‖ζ‖ by positivity) (show 0 ≤ (2 : ℝ) by norm_num)
          norm_num at hp ⊢
          exact hp
        · exact mul_nonneg h1z h1ζ
      _ = 4 * (1 - ‖z‖) * (1 - ‖ζ‖) := by ring
  apply hbase.trans
  rw [div_le_div_iff₀ (by positivity : 0 < 2 * ‖z - ζ‖ ^ 2) hd]
  nlinarith

lemma diskGreen_zero (ζ : ℂ) :
    diskGreen 0 ζ = Real.log (1 / ‖ζ‖) := by
  simp [diskGreen, norm_neg]

lemma diskGreen_boundary {z ζ : ℂ} (hz : ‖z‖ = 1) (hζ : ‖ζ‖ < 1) :
    diskGreen z ζ = 0 := by
  have hne : z ≠ ζ := by intro h; subst z; linarith
  have hid := diskGreen_normSq_identity z ζ
  rw [hz, one_pow, sub_self, zero_mul] at hid
  have hsquares : ‖1 - (starRingEnd ℂ) ζ * z‖ ^ 2 = ‖z - ζ‖ ^ 2 :=
    sub_eq_zero.mp hid
  have hnorm : ‖1 - (starRingEnd ℂ) ζ * z‖ = ‖z - ζ‖ :=
    (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsquares
  simp [diskGreen, hnorm]

lemma continuousAt_diskGreen_left {z ζ : ℂ} (hne : z ≠ ζ)
    (hnum : 1 - (starRingEnd ℂ) ζ * z ≠ 0) :
    ContinuousAt (fun w ↦ diskGreen w ζ) z := by
  apply ContinuousAt.log
  · exact (ContinuousAt.norm (continuousAt_const.sub
      ((continuousAt_const.mul continuousAt_id)))).div
      (ContinuousAt.norm (continuousAt_id.sub continuousAt_const))
      (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hne))
  · exact div_ne_zero (norm_ne_zero_iff.mpr hnum)
      (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hne))

lemma diskGreen_tendsto_boundary {z ζ : ℂ} (hz : ‖z‖ = 1) (hζ : ‖ζ‖ < 1) :
    Tendsto (fun w ↦ diskGreen w ζ) (𝓝 z) (𝓝 0) := by
  have hne : z ≠ ζ := by intro h; subst z; linarith
  have hnum : 1 - (starRingEnd ℂ) ζ * z ≠ 0 := by
    intro h
    have hn0 : ‖1 - (starRingEnd ℂ) ζ * z‖ = 0 := norm_eq_zero.mpr h
    have hden0 : ‖z - ζ‖ = 0 := by
      have hid := diskGreen_normSq_identity z ζ
      rw [hz, one_pow, sub_self, zero_mul, hn0, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] at hid
      nlinarith
    exact hne (sub_eq_zero.mp (norm_eq_zero.mp hden0))
  rw [← diskGreen_boundary hz hζ]
  exact continuousAt_diskGreen_left hne hnum

/-- Away from its pole, the disk Green kernel is harmonic in the first variable. The
nonvanishing numerator is automatic when both variables lie in the open unit disk. -/
lemma harmonicAt_diskGreen_left {z ζ : ℂ} (hz : ‖z‖ < 1) (hζ : ‖ζ‖ < 1)
    (hne : z ≠ ζ) :
    HarmonicAt (fun w ↦ diskGreen w ζ) z := by
  have hden : z - ζ ≠ 0 := sub_ne_zero.mpr hne
  have hnum : 1 - (starRingEnd ℂ) ζ * z ≠ 0 := by
    intro hzero
    have hprod : ‖ζ‖ * ‖z‖ = 1 := by
      have hone : (starRingEnd ℂ) ζ * z = 1 := (sub_eq_zero.mp hzero).symm
      have := congrArg norm hone
      simpa [norm_mul, Complex.norm_conj] using this
    have hlt : ‖ζ‖ * ‖z‖ < 1 := by
      calc
        ‖ζ‖ * ‖z‖ ≤ ‖ζ‖ * 1 :=
          mul_le_mul_of_nonneg_left hz.le (norm_nonneg ζ)
        _ < 1 := by simpa using hζ
    linarith
  have hnumH : HarmonicAt
      (fun w : ℂ ↦ Real.log ‖1 - (starRingEnd ℂ) ζ * w‖) z :=
    (show AnalyticAt ℂ (fun w : ℂ ↦ 1 - (starRingEnd ℂ) ζ * w) z by
      fun_prop).harmonicAt_log_norm hnum
  have hdenH : HarmonicAt (fun w : ℂ ↦ Real.log ‖w - ζ‖) z :=
    (show AnalyticAt ℂ (fun w : ℂ ↦ w - ζ) z by
      fun_prop).harmonicAt_log_norm hden
  have heq : (fun w ↦ diskGreen w ζ) =ᶠ[𝓝 z] (fun w : ℂ ↦
      Real.log ‖1 - (starRingEnd ℂ) ζ * w‖ - Real.log ‖w - ζ‖) := by
    filter_upwards
      [(continuousAt_const.sub (continuousAt_const.mul continuousAt_id)).norm.eventually_ne
        (norm_ne_zero_iff.mpr hnum),
       (continuousAt_id.sub continuousAt_const).norm.eventually_ne
        (norm_ne_zero_iff.mpr hden)] with w hwn hwd
    exact Real.log_div hwn hwd
  rw [harmonicAt_congr_nhds heq]
  exact hnumH.sub hdenH

/-- Mean-value formula for the Green kernel on a closed disk avoiding its pole. -/
lemma circleAverage_diskGreen_left {c ζ : ℂ} {R : ℝ} (hR : 0 < R)
    (hball : Metric.closedBall c R ⊆ unitDisk) (hζ : ζ ∈ unitDisk)
    (hpole : ζ ∉ Metric.closedBall c R) :
    Real.circleAverage (fun z ↦ diskGreen z ζ) c R = diskGreen c ζ := by
  apply InnerProductSpace.HarmonicOnNhd.circleAverage_eq
  intro z hz
  exact harmonicAt_diskGreen_left (z := z) (ζ := ζ)
    (by simpa [unitDisk] using hball (by simpa [abs_of_pos hR] using hz))
    (by simpa [unitDisk] using hζ)
    (by
      intro h
      exact hpole (by simpa [abs_of_pos hR, h] using hz))


lemma norm_one_sub_conj_mul_le_three_boundaryDist {z ζ : ℂ}
    (hz : ‖z‖ < 1) (hclose : ‖z - ζ‖ ≤ (1 - ‖z‖) / 2) :
    ‖1 - (starRingEnd ℂ) ζ * z‖ ≤ 3 * (1 - ‖z‖) := by
  have hz0 : 0 ≤ ‖z‖ := norm_nonneg _
  have hgap : 0 ≤ 1 - ‖z‖ := by linarith
  have hsq : 0 ≤ 1 - ‖z‖ ^ 2 := by
    nlinarith [mul_nonneg hgap (show 0 ≤ 1 + ‖z‖ by positivity)]
  have hdecomp : 1 - (starRingEnd ℂ) ζ * z =
      (1 - (starRingEnd ℂ) z * z) +
        (((starRingEnd ℂ) z - (starRingEnd ℂ) ζ) * z) := by ring
  rw [hdecomp]
  calc
    ‖(1 - (starRingEnd ℂ) z * z) +
        (((starRingEnd ℂ) z - (starRingEnd ℂ) ζ) * z)‖ ≤
        ‖1 - (starRingEnd ℂ) z * z‖ +
          ‖((starRingEnd ℂ) z - (starRingEnd ℂ) ζ) * z‖ := norm_add_le _ _
    _ = (1 - ‖z‖ ^ 2) + ‖z - ζ‖ * ‖z‖ := by
      rw [Complex.conj_mul']
      simp only [norm_mul, ← map_sub, Complex.norm_conj]
      rw [← Complex.ofReal_pow, ← Complex.ofReal_one, ← Complex.ofReal_sub,
        Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hsq]
    _ ≤ 3 * (1 - ‖z‖) := by
      nlinarith [mul_nonneg hgap (show 0 ≤ 1 + ‖z‖ by positivity),
        mul_le_mul_of_nonneg_right hclose hz0]

lemma diskGreen_le_localLog {z ζ : ℂ}
    (hz : ‖z‖ < 1) (hne : z ≠ ζ)
    (hclose : ‖z - ζ‖ ≤ (1 - ‖z‖) / 2) :
    diskGreen z ζ ≤ Real.log (3 * (1 - ‖z‖) / ‖z - ζ‖) := by
  have hd : 0 < ‖z - ζ‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  have hn : 0 < 3 * (1 - ‖z‖) := by positivity
  have hζ : ‖ζ‖ < 1 := by
    calc
      ‖ζ‖ = ‖z - (z - ζ)‖ := by congr 1; ring
      _ ≤ ‖z‖ + ‖z - ζ‖ := norm_sub_le _ _
      _ ≤ ‖z‖ + (1 - ‖z‖) / 2 := by gcongr
      _ < 1 := by linarith
  have hnum : 0 < ‖1 - (starRingEnd ℂ) ζ * z‖ :=
    lt_of_lt_of_le hd (norm_sub_le_norm_one_sub_conj_mul hz hζ)
  apply Real.strictMonoOn_log.monotoneOn
  · exact div_pos hnum hd
  · exact div_pos hn hd
  · exact div_le_div_of_nonneg_right
      (norm_one_sub_conj_mul_le_three_boundaryDist hz hclose) hd.le


/-- The point of radius `r` and angle `θ`. -/
noncomputable def radialPoint (r θ : ℝ) : ℂ :=
  (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)

structure CircularArc where
  radius : ℝ
  angles : Set ℝ
  radius_pos : 0 < radius
  radius_lt_one : radius < 1
  measurableSet_angles : MeasurableSet angles

namespace CircularArc

def carrier (a : CircularArc) : Set ℂ := radialPoint a.radius '' a.angles

noncomputable def weightedMeasure (a : CircularArc) : Measure ℂ :=
  ENNReal.ofReal (a.radius / (1 - a.radius)) •
    Measure.map (fun θ ↦ radialPoint a.radius θ) (volume.restrict a.angles)

end CircularArc

structure DisjointRadialArcs where
  n : ℕ
  arc : Fin n → CircularArc
  angle_disjoint : Set.Pairwise Set.univ fun i j ↦ Disjoint (arc i).angles (arc j).angles

namespace DisjointRadialArcs

noncomputable def measure (A : DisjointRadialArcs) : Measure ℂ :=
  ∑ i, (A.arc i).weightedMeasure

def carrier (A : DisjointRadialArcs) : Set ℂ := ⋃ i, (A.arc i).carrier

end DisjointRadialArcs

noncomputable def greenPotentialReal (ν : Measure ℂ) (z : ℂ) : ℝ :=
  ∫ ζ, diskGreen z ζ ∂ν

noncomputable def greenPotential (ν : Measure ℂ) (z : ℂ) : ℝ≥0∞ :=
  ∫⁻ ζ, diskGreenENNReal z ζ ∂ν

lemma greenPotential_mono_measure {μ ν : Measure ℂ} (hμν : μ ≤ ν) (z : ℂ) :
    greenPotential μ z ≤ greenPotential ν z := by
  exact MeasureTheory.lintegral_mono' hμν (fun _ ↦ le_rfl)

lemma hasSum_dyadic_weighted :
    HasSum (fun n : ℕ ↦ ((n : ℝ) + 1) * ((1 : ℝ) / 2) ^ n) 4 := by
  have hn : HasSum (fun n : ℕ ↦ (n : ℝ) * ((1 : ℝ) / 2) ^ n) 2 := by
    have h := hasSum_coe_mul_geometric_of_norm_lt_one (𝕜 := ℝ)
      (r := (1 : ℝ) / 2) (by norm_num)
    have hv : ((1 : ℝ) / 2) / (1 - (1 : ℝ) / 2) ^ 2 = 2 := by norm_num
    rw [hv] at h
    simpa using h
  convert hn.add hasSum_geometric_two using 1 <;> ring_nf

/-- The dyadic summation step in the disjoint-radial-arcs argument. The two pointwise
hypotheses are exactly the far-shell and near-shell estimates; the conclusion is the uniform
potential bound, with all infinite-series bookkeeping discharged. -/
theorem greenPotential_disjointArcs_le (A : DisjointRadialArcs) (z : ℂ)
    (far near : ℕ → ℝ) (Cfar Cnear : ℝ)
    (hfar : ∀ j, 0 ≤ far j ∧ far j ≤ Cfar * ((1 : ℝ) / 2) ^ j)
    (hnear : ∀ j, 0 ≤ near j ∧
      near j ≤ Cnear * ((j : ℝ) + 1) * ((1 : ℝ) / 2) ^ j)
    (hdecomp : greenPotentialReal A.measure z ≤ (∑' j, far j) + ∑' j, near j) :
    greenPotentialReal A.measure z ≤ 2 * Cfar + 4 * Cnear := by
  have hgeom : HasSum (fun n : ℕ ↦ ((1 : ℝ) / 2) ^ n) 2 := hasSum_geometric_two
  have sfC : Summable (fun j : ℕ ↦ Cfar * ((1 : ℝ) / 2) ^ j) :=
    hgeom.summable.mul_left Cfar
  have snC : Summable (fun j : ℕ ↦
      Cnear * (((j : ℝ) + 1) * ((1 : ℝ) / 2) ^ j)) :=
    hasSum_dyadic_weighted.summable.mul_left Cnear
  have sf : Summable far := Summable.of_nonneg_of_le
    (fun j ↦ (hfar j).1) (fun j ↦ (hfar j).2) sfC
  have sn : Summable near := Summable.of_nonneg_of_le
    (fun j ↦ (hnear j).1) (fun j ↦ by simpa [mul_assoc] using (hnear j).2) snC
  have hf := sf.tsum_le_tsum (fun j ↦ (hfar j).2) sfC
  have hn := sn.tsum_le_tsum
    (fun j ↦ by simpa [mul_assoc] using (hnear j).2) snC
  rw [tsum_mul_left, hgeom.tsum_eq] at hf
  rw [tsum_mul_left, hasSum_dyadic_weighted.tsum_eq] at hn
  linarith

/-- Comparison at the origin converts the uniformly bounded slit potential into the outer
radial-projection estimate. This is the maximum-principle endgame of Hall's outer argument. -/
theorem hall_outer_projection_of_potential {S : Set ℝ} {ν : Measure ℂ}
    {ψ : ℂ → ℝ} {Cproj Ccomp δ : ℝ}
    (hproj : (volume S).toReal ≤ Cproj * greenPotentialReal ν 0)
    (hcomp : greenPotentialReal ν 0 ≤ Ccomp * ψ 0)
    (hcenter : ψ 0 = δ)
    (hCproj : 0 ≤ Cproj) :
    (volume S).toReal ≤ Cproj * Ccomp * δ := by
  calc
    (volume S).toReal ≤ Cproj * greenPotentialReal ν 0 := hproj
    _ ≤ Cproj * (Ccomp * ψ 0) := mul_le_mul_of_nonneg_left hcomp hCproj
    _ = Cproj * Ccomp * δ := by rw [hcenter]; ring


/-! ### The inner Riesz/maximal-function stage -/

def innerDisk : Set ℂ := Metric.ball 0 (1 / 4 : ℝ)
def innerRadii : Set ℝ := Icc (0 : ℝ) (1 / 2)
def angleDomain : Set ℝ := Ico 0 (2 * Real.pi)

noncomputable def localLogKernel (ζ z : ℂ) : ℝ≥0∞ :=
  if z = ζ then ⊤ else ENNReal.ofReal (Real.log (4 / ‖z - ζ‖))

/-- Pointwise radial supremum of the local logarithmic kernel from (17). -/
noncomputable def radialLogKernel (ζ : ℂ) (θ : ℝ) : ℝ≥0∞ :=
  ⨆ r : innerRadii, localLogKernel ζ (radialPoint r.1 θ)

/-- Tonelli majorant for the radial maximal function of the inner Riesz potential. -/
noncomputable def innerRieszMajorant (μ : Measure ℂ) (θ : ℝ) : ℝ≥0∞ :=
  ∫⁻ ζ in innerDisk, radialLogKernel ζ θ ∂μ

/-- Logarithmic moment of the inner part of a Riesz measure. -/
noncomputable def innerRieszMass (μ : Measure ℂ) : ℝ≥0∞ :=
  ∫⁻ ζ in innerDisk, localLogKernel ζ 0 ∂μ

lemma measurable_localLogKernel_zero : Measurable (fun ζ ↦ localLogKernel ζ 0) := by
  unfold localLogKernel
  apply Measurable.ite
  · exact measurableSet_eq_fun measurable_const measurable_id
  · fun_prop
  · fun_prop

/-- Equation (18) from the writeup, isolated at its exact trust boundary. The only analytic
input is the one-kernel angular estimate (17) and measurability of the radial supremum; Tonelli
and integration of the pointwise estimate are proved here. -/
theorem innerRieszMajorant_integral {μ : Measure ℂ} [SFinite μ] (C : ℝ≥0∞)
    (hmeas : AEMeasurable (Function.uncurry radialLogKernel)
      ((μ.restrict innerDisk).prod (volume.restrict angleDomain)))
    (hkernel : ∀ ζ ∈ innerDisk,
      ∫⁻ θ in angleDomain, radialLogKernel ζ θ ≤ C * localLogKernel ζ 0) :
    ∫⁻ θ in angleDomain, innerRieszMajorant μ θ ≤ C * innerRieszMass μ := by
  change (∫⁻ θ, (∫⁻ ζ, radialLogKernel ζ θ ∂(μ.restrict innerDisk))
      ∂(volume.restrict angleDomain)) ≤ _
  rw [← MeasureTheory.lintegral_lintegral_swap hmeas]
  calc
    (∫⁻ ζ, (∫⁻ θ, radialLogKernel ζ θ ∂(volume.restrict angleDomain))
        ∂(μ.restrict innerDisk)) ≤
        ∫⁻ ζ, C * localLogKernel ζ 0 ∂(μ.restrict innerDisk) := by
      apply MeasureTheory.lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_ball] with ζ hζ
      exact hkernel ζ hζ
    _ = C * innerRieszMass μ := by
      rw [MeasureTheory.lintegral_const_mul C measurable_localLogKernel_zero]
      rfl

/-- Chebyshev's inequality in precisely the form used after the Riesz decomposition. -/
theorem innerRadialMax_projection_bound {S : Set ℝ} {η : ℝ → ℝ≥0∞}
    {ε M : ℝ≥0∞} (hSmeas : MeasurableSet S) (hS : S ⊆ angleDomain)
    (hη : AEMeasurable η (volume.restrict angleDomain))
    (hlarge : S ⊆ {θ | ε ≤ η θ}) (hε0 : ε ≠ 0) (hεtop : ε ≠ ⊤)
    (hint : ∫⁻ θ in angleDomain, η θ ≤ M) :
    volume S ≤ M / ε := by
  have hmarkov := MeasureTheory.meas_ge_le_lintegral_div hη hε0 hεtop
  have hmono : (volume.restrict angleDomain) S ≤
      (volume.restrict angleDomain) {θ | ε ≤ η θ} := measure_mono hlarge
  have hrestrict : (volume.restrict angleDomain) S = volume S := by
    rw [Measure.restrict_apply hSmeas, inter_eq_left.mpr hS]
  rw [hrestrict] at hmono
  exact hmono.trans (hmarkov.trans (ENNReal.div_le_div_right hint ε))

/-- The complete inner-projection estimate: Riesz/Tonelli controls the maximal function and
Chebyshev converts a uniform threshold on bad directions into angular measure. -/
theorem hall_inner_projection {μ : Measure ℂ} [SFinite μ] {S : Set ℝ}
    {ε C K δ : ℝ≥0∞}
    (hSmeas : MeasurableSet S) (hS : S ⊆ angleDomain)
    (hmeasK : AEMeasurable (Function.uncurry radialLogKernel)
      ((μ.restrict innerDisk).prod (volume.restrict angleDomain)))
    (hkernel : ∀ ζ ∈ innerDisk,
      ∫⁻ θ in angleDomain, radialLogKernel ζ θ ≤ C * localLogKernel ζ 0)
    (hmeasMax : AEMeasurable (innerRieszMajorant μ) (volume.restrict angleDomain))
    (hlarge : S ⊆ {θ | ε ≤ innerRieszMajorant μ θ})
    (hε0 : ε ≠ 0) (hεtop : ε ≠ ⊤)
    (hmass : innerRieszMass μ ≤ K * δ) :
    volume S ≤ (C * (K * δ)) / ε := by
  apply innerRadialMax_projection_bound hSmeas hS hmeasMax hlarge hε0 hεtop
  exact (innerRieszMajorant_integral C hmeasK hkernel).trans
    (mul_le_mul_of_nonneg_left hmass bot_le)

def goodDirections (w : ℂ → ℝ) : Set ℝ :=
  {θ | θ ∈ angleDomain ∧ ∀ r ∈ Ico (0 : ℝ) 1, 0 < w (radialPoint r θ)}
def innerBadDirections (w : ℂ → ℝ) : Set ℝ :=
  {θ | θ ∈ angleDomain ∧ ∃ r ∈ Icc (0 : ℝ) (1 / 4), w (radialPoint r θ) ≤ 0}
def outerBadDirections (w : ℂ → ℝ) : Set ℝ :=
  {θ | θ ∈ angleDomain ∧ ∃ r ∈ Ioo (1 / 4 : ℝ) 1, w (radialPoint r θ) ≤ 0}

/-! ### Measurability of Hall's direction sets -/

/-- Project rational radii onto a fixed compact interval.  The range remains dense, so these
radii suffice to detect a nonpositive value of a continuous radial function after taking a
countable family of positive thresholds. -/
noncomputable def rationalRadius (a b : ℝ) (hab : a ≤ b) (q : ℚ) : Set.Icc a b :=
  Set.projIcc a b hab (q : ℝ)

lemma denseRange_rationalRadius (a b : ℝ) (hab : a ≤ b) :
    DenseRange (rationalRadius a b hab) := by
  change DenseRange (Set.projIcc a b hab ∘ ((↑) : ℚ → ℝ))
  exact (Set.projIcc_surjective hab).denseRange.comp Rat.denseRange_cast continuous_projIcc

noncomputable def rationalBadApprox
    (w : ℂ → ℝ) (a b : ℝ) (hab : a ≤ b) (n : ℕ) : Set ℝ :=
  ⋃ q : ℚ, { θ | w (radialPoint (rationalRadius a b hab q).1 θ) < 1 / (n + 1 : ℝ) }

lemma continuous_rational_radial_value {w : ℂ → ℝ}
    (hw : ContinuousOn w unitDisk) {a b : ℝ} (hab : a ≤ b)
    (ha : 0 ≤ a) (hb : b < 1) (q : ℚ) :
    Continuous (fun θ ↦ w (radialPoint (rationalRadius a b hab q).1 θ)) := by
  apply hw.comp_continuous
  · unfold radialPoint
    fun_prop
  · intro θ
    change radialPoint (rationalRadius a b hab q).1 θ ∈ Metric.ball (0 : ℂ) 1
    rw [Metric.mem_ball, dist_zero_right]
    simp only [radialPoint, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      Complex.norm_exp]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, mul_zero, mul_one, sub_self, Real.exp_zero, mul_one]
    rw [abs_of_nonneg (ha.trans (rationalRadius a b hab q).2.1)]
    exact (rationalRadius a b hab q).2.2.trans_lt hb

lemma measurableSet_rationalBadApprox {w : ℂ → ℝ}
    (hw : ContinuousOn w unitDisk) {a b : ℝ} (hab : a ≤ b)
    (ha : 0 ≤ a) (hb : b < 1) (n : ℕ) :
    MeasurableSet (rationalBadApprox w a b hab n) := by
  unfold rationalBadApprox
  apply MeasurableSet.iUnion
  intro q
  exact measurableSet_lt
    (continuous_rational_radial_value hw hab ha hb q).measurable measurable_const

lemma exists_radial_le_zero_iff_rationalBadApprox {w : ℂ → ℝ}
    (hw : ContinuousOn w unitDisk) {a b : ℝ} (hab : a ≤ b)
    (ha : 0 ≤ a) (hb : b < 1) (θ : ℝ) :
    (∃ r ∈ Icc a b, w (radialPoint r θ) ≤ 0) ↔
      θ ∈ ⋂ n : ℕ, rationalBadApprox w a b hab n := by
  let K := Set.Icc a b
  let F : K → ℝ := fun r ↦ w (radialPoint r.1 θ)
  have hradial_mem : ∀ r : K, radialPoint r.1 θ ∈ unitDisk := by
    intro r
    change radialPoint r.1 θ ∈ Metric.ball (0 : ℂ) 1
    rw [Metric.mem_ball, dist_zero_right]
    simp only [radialPoint, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      Complex.norm_exp]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, mul_zero, mul_one, sub_self, Real.exp_zero, mul_one]
    rw [abs_of_nonneg (ha.trans r.2.1)]
    exact r.2.2.trans_lt hb
  have hF : Continuous F := by
    apply hw.comp_continuous
    · unfold radialPoint
      fun_prop
    · exact hradial_mem
  have hKcompact : IsCompact (Set.univ : Set K) := isCompact_univ
  have hKnonempty : (Set.univ : Set K).Nonempty := by
    exact ⟨⟨a, left_mem_Icc.mpr hab⟩, Set.mem_univ _⟩
  constructor
  · rintro ⟨r, hr, hrw⟩
    rw [mem_iInter]
    intro n
    have ht : w (radialPoint r θ) < 1 / (n + 1 : ℝ) := by
      exact lt_of_le_of_lt hrw (by positivity)
    let rK : K := ⟨r, hr⟩
    have hopen : IsOpen {x : K | F x < 1 / (n + 1 : ℝ)} :=
      isOpen_lt hF continuous_const
    have hne : ({x : K | F x < 1 / (n + 1 : ℝ)} : Set K).Nonempty := by
      exact ⟨rK, ht⟩
    obtain ⟨q, hq⟩ := (denseRange_rationalRadius a b hab).exists_mem_open hopen hne
    rw [rationalBadApprox, mem_iUnion]
    exact ⟨q, hq⟩
  · intro h
    have himgCompact : IsCompact (F '' (Set.univ : Set K)) :=
      hKcompact.image hF
    have himgNonempty : (F '' (Set.univ : Set K)).Nonempty := hKnonempty.image F
    obtain ⟨r, _hr, hrmin⟩ :=
      hKcompact.exists_sInf_image_eq hKnonempty hF.continuousOn
    refine ⟨r.1, r.2, ?_⟩
    change F r ≤ 0
    rw [← hrmin]
    by_contra hnot
    have hminpos : 0 < sInf (F '' (Set.univ : Set K)) := lt_of_not_ge hnot
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hminpos
    have hnmem := mem_iInter.mp h n
    rw [rationalBadApprox, mem_iUnion] at hnmem
    obtain ⟨q, hq⟩ := hnmem
    change F (rationalRadius a b hab q) < 1 / (n + 1 : ℝ) at hq
    have hminle : sInf (F '' (Set.univ : Set K)) ≤ F (rationalRadius a b hab q) :=
      (himgCompact.isLeast_sInf himgNonempty).2
        ⟨rationalRadius a b hab q, Set.mem_univ _, rfl⟩
    linarith

lemma measurableSet_exists_radial_le_zero_Icc {w : ℂ → ℝ}
    (hw : ContinuousOn w unitDisk) {a b : ℝ} (hab : a ≤ b)
    (ha : 0 ≤ a) (hb : b < 1) :
    MeasurableSet { θ | ∃ r ∈ Icc a b, w (radialPoint r θ) ≤ 0 } := by
  have heq : { θ | ∃ r ∈ Icc a b, w (radialPoint r θ) ≤ 0 } =
      ⋂ n : ℕ, rationalBadApprox w a b hab n := by
    ext θ
    exact exists_radial_le_zero_iff_rationalBadApprox hw hab ha hb θ
  rw [heq]
  exact MeasurableSet.iInter (measurableSet_rationalBadApprox hw hab ha hb)

lemma measurableSet_innerBadDirections {w : ℂ → ℝ}
    (hw : ContinuousOn w unitDisk) :
    MeasurableSet (innerBadDirections w) := by
  change MeasurableSet (angleDomain ∩
    { θ | ∃ r ∈ Icc (0 : ℝ) (1 / 4), w (radialPoint r θ) ≤ 0 })
  exact measurableSet_Ico.inter
    (measurableSet_exists_radial_le_zero_Icc hw (by norm_num) (by norm_num) (by norm_num))

/-- A countable compact exhaustion of the open outer-radius interval. -/
noncomputable def outerCompactInterval (n : ℕ) : Set ℝ :=
  Icc (1 / 4 + 1 / (n + 4 : ℝ)) (1 - 1 / (n + 4 : ℝ))

lemma outerCompactInterval_nonempty (n : ℕ) :
    1 / 4 + 1 / (n + 4 : ℝ) ≤ 1 - 1 / (n + 4 : ℝ) := by
  have hd : (4 : ℝ) ≤ n + 4 := by exact_mod_cast Nat.le_add_left 4 n
  have hinv : 1 / (n + 4 : ℝ) ≤ 1 / 4 :=
    one_div_le_one_div_of_le (by norm_num) hd
  linarith

lemma outerCompactInterval_lower_nonneg (n : ℕ) :
    0 ≤ 1 / 4 + 1 / (n + 4 : ℝ) := by positivity

lemma outerCompactInterval_upper_lt_one (n : ℕ) :
    1 - 1 / (n + 4 : ℝ) < 1 := by
  have : 0 < 1 / (n + 4 : ℝ) := by positivity
  linarith

lemma Ioo_quarter_one_eq_iUnion_outerCompactInterval :
    Ioo (1 / 4 : ℝ) 1 = ⋃ n : ℕ, outerCompactInterval n := by
  ext r
  constructor
  · rintro ⟨hr0, hr1⟩
    have hgap : 0 < min (r - 1 / 4) (1 - r) := lt_min (sub_pos.mpr hr0) (sub_pos.mpr hr1)
    obtain ⟨m, hm⟩ := exists_nat_one_div_lt hgap
    have hden : (m + 1 : ℝ) ≤ m + 4 := by norm_num
    have hone : 1 / (m + 4 : ℝ) ≤ 1 / (m + 1 : ℝ) :=
      one_div_le_one_div_of_le (by positivity) hden
    have hsmall : 1 / (m + 4 : ℝ) < min (r - 1 / 4) (1 - r) :=
      hone.trans_lt hm
    rw [mem_iUnion]
    refine ⟨m, ?_⟩
    exact ⟨by linarith [hsmall.trans_le (min_le_left _ _)],
      by linarith [hsmall.trans_le (min_le_right _ _)]⟩
  · rw [mem_iUnion]
    rintro ⟨n, hr0, hr1⟩
    have hinv : 0 < 1 / (n + 4 : ℝ) := by positivity
    exact ⟨by linarith, by linarith⟩

lemma measurableSet_outerBadDirections {w : ℂ → ℝ}
    (hw : ContinuousOn w unitDisk) :
    MeasurableSet (outerBadDirections w) := by
  have hrad : MeasurableSet
      { θ | ∃ r ∈ Ioo (1 / 4 : ℝ) 1, w (radialPoint r θ) ≤ 0 } := by
    have heq : { θ | ∃ r ∈ Ioo (1 / 4 : ℝ) 1, w (radialPoint r θ) ≤ 0 } =
        ⋃ n : ℕ, { θ | ∃ r ∈ outerCompactInterval n,
          w (radialPoint r θ) ≤ 0 } := by
      ext θ
      simp only [mem_setOf_eq, mem_iUnion]
      constructor
      · rintro ⟨r, hr, hrw⟩
        rw [Ioo_quarter_one_eq_iUnion_outerCompactInterval, mem_iUnion] at hr
        obtain ⟨n, hn⟩ := hr
        exact ⟨n, r, hn, hrw⟩
      · rintro ⟨n, r, hr, hrw⟩
        refine ⟨r, ?_, hrw⟩
        rw [Ioo_quarter_one_eq_iUnion_outerCompactInterval, mem_iUnion]
        exact ⟨n, hr⟩
    rw [heq]
    apply MeasurableSet.iUnion
    intro n
    exact measurableSet_exists_radial_le_zero_Icc hw
      (outerCompactInterval_nonempty n) (outerCompactInterval_lower_nonneg n)
      (outerCompactInterval_upper_lt_one n)
  change MeasurableSet (angleDomain ∩
    { θ | ∃ r ∈ Ioo (1 / 4 : ℝ) 1, w (radialPoint r θ) ≤ 0 })
  exact measurableSet_Ico.inter hrad

lemma measurableSet_goodDirections {w : ℂ → ℝ}
    (hw : ContinuousOn w unitDisk) :
    MeasurableSet (goodDirections w) := by
  have hbad : { θ | ∃ r ∈ Ico (0 : ℝ) 1, w (radialPoint r θ) ≤ 0 } =
      { θ | ∃ r ∈ Icc (0 : ℝ) (1 / 4), w (radialPoint r θ) ≤ 0 } ∪
      { θ | ∃ r ∈ Ioo (1 / 4 : ℝ) 1, w (radialPoint r θ) ≤ 0 } := by
    ext θ
    constructor
    · rintro ⟨r, ⟨hr0, hr1⟩, hrw⟩
      by_cases hr : r ≤ (1 / 4 : ℝ)
      · exact Or.inl ⟨r, ⟨hr0, hr⟩, hrw⟩
      · exact Or.inr ⟨r, ⟨lt_of_not_ge hr, hr1⟩, hrw⟩
    · rintro (h | h)
      · obtain ⟨r, ⟨hr0, hr1⟩, hrw⟩ := h
        exact ⟨r, ⟨hr0, hr1.trans_lt (by norm_num)⟩, hrw⟩
      · obtain ⟨r, ⟨hr0, hr1⟩, hrw⟩ := h
        exact ⟨r, ⟨(by norm_num : (0 : ℝ) < 1 / 4).le.trans hr0.le, hr1⟩, hrw⟩
  have hinnerRaw : MeasurableSet
      { θ | ∃ r ∈ Icc (0 : ℝ) (1 / 4), w (radialPoint r θ) ≤ 0 } :=
    measurableSet_exists_radial_le_zero_Icc hw (by norm_num) (by norm_num) (by norm_num)
  have houterRaw : MeasurableSet
      { θ | ∃ r ∈ Ioo (1 / 4 : ℝ) 1, w (radialPoint r θ) ≤ 0 } := by
    have heq : { θ | ∃ r ∈ Ioo (1 / 4 : ℝ) 1, w (radialPoint r θ) ≤ 0 } =
        ⋃ n : ℕ, { θ | ∃ r ∈ outerCompactInterval n,
          w (radialPoint r θ) ≤ 0 } := by
      ext θ
      simp only [mem_setOf_eq, mem_iUnion]
      constructor
      · rintro ⟨r, hr, hrw⟩
        rw [Ioo_quarter_one_eq_iUnion_outerCompactInterval, mem_iUnion] at hr
        obtain ⟨n, hn⟩ := hr
        exact ⟨n, r, hn, hrw⟩
      · rintro ⟨n, r, hr, hrw⟩
        refine ⟨r, ?_, hrw⟩
        rw [Ioo_quarter_one_eq_iUnion_outerCompactInterval, mem_iUnion]
        exact ⟨n, hr⟩
    rw [heq]
    apply MeasurableSet.iUnion
    intro n
    exact measurableSet_exists_radial_le_zero_Icc hw
      (outerCompactInterval_nonempty n) (outerCompactInterval_lower_nonneg n)
      (outerCompactInterval_upper_lt_one n)
  change MeasurableSet (angleDomain ∩
    { θ | ∀ r ∈ Ico (0 : ℝ) 1, 0 < w (radialPoint r θ) })
  have hcompl : { θ | ∀ r ∈ Ico (0 : ℝ) 1, 0 < w (radialPoint r θ) } =
      { θ | ∃ r ∈ Ico (0 : ℝ) 1, w (radialPoint r θ) ≤ 0 }ᶜ := by
    ext θ
    simp only [mem_setOf_eq, mem_compl_iff, not_exists, not_and, not_le]
  rw [hcompl, hbad]
  exact measurableSet_Ico.inter (hinnerRaw.union houterRaw).compl

lemma angleDomain_subset_good_union_bad (w : ℂ → ℝ) :
    angleDomain ⊆ goodDirections w ∪ (innerBadDirections w ∪ outerBadDirections w) := by
  intro θ hθ
  by_cases hg : θ ∈ goodDirections w
  · exact Or.inl hg
  right
  have hall : ¬ ∀ r ∈ Ico (0 : ℝ) 1, 0 < w (radialPoint r θ) := by
    intro h
    exact hg ⟨hθ, h⟩
  simp only [not_forall, not_lt] at hall
  obtain ⟨r, ⟨hr0, hr1⟩, hrw⟩ := hall
  by_cases hr : r ≤ (1 / 4 : ℝ)
  · left
    exact ⟨hθ, r, ⟨hr0, hr⟩, hrw⟩
  · right
    exact ⟨hθ, r, ⟨lt_of_not_ge hr, hr1⟩, hrw⟩

lemma volume_angleDomain : volume angleDomain = ENNReal.ofReal (2 * Real.pi) := by
  simp [angleDomain, Real.volume_Ico]

lemma hall_measure_lower_bound (w : ℂ → ℝ) (Binner Bouter : ℝ≥0∞)
    (hinner : volume (innerBadDirections w) ≤ Binner)
    (houter : volume (outerBadDirections w) ≤ Bouter) :
    ENNReal.ofReal (2 * Real.pi) - (Binner + Bouter) ≤ volume (goodDirections w) := by
  rw [← volume_angleDomain]
  rw [tsub_le_iff_right]
  calc
    volume angleDomain ≤ volume (goodDirections w ∪
        (innerBadDirections w ∪ outerBadDirections w)) :=
      measure_mono (angleDomain_subset_good_union_bad w)
    _ ≤ volume (goodDirections w) +
        volume (innerBadDirections w ∪ outerBadDirections w) := measure_union_le _ _
    _ ≤ volume (goodDirections w) +
        (volume (innerBadDirections w) + volume (outerBadDirections w)) := by
      gcongr
      exact measure_union_le _ _
    _ ≤ volume (goodDirections w) + (Binner + Bouter) := by gcongr

lemma goodDirections_positive_measure (w : ℂ → ℝ) (Binner Bouter : ℝ≥0∞)
    (hinner : volume (innerBadDirections w) ≤ Binner)
    (houter : volume (outerBadDirections w) ≤ Bouter)
    (hsmall : Binner + Bouter < ENNReal.ofReal (2 * Real.pi)) :
    0 < volume (goodDirections w) := by
  have hlower := hall_measure_lower_bound w Binner Bouter hinner houter
  exact lt_of_lt_of_le (tsub_pos_iff_lt.mpr hsmall) hlower

lemma exists_goodDirection_of_pos (w : ℂ → ℝ)
    (hpos : 0 < volume (goodDirections w)) :
    ∃ θ ∈ angleDomain, ∀ r ∈ Ico (0 : ℝ) 1, 0 < w (radialPoint r θ) := by
  have hne : goodDirections w ≠ ∅ := by
    intro h
    rw [h] at hpos
    simp at hpos
  obtain ⟨θ, hθ⟩ := Set.nonempty_iff_ne_empty.mpr hne
  exact ⟨θ, hθ.1, hθ.2⟩

lemma radialPoint_mem_unitDisk {r θ : ℝ} (hr : r ∈ Ico (0 : ℝ) 1) :
    radialPoint r θ ∈ Metric.ball (0 : ℂ) 1 := by
  rw [Metric.mem_ball, dist_zero_right]
  simp [radialPoint, abs_of_nonneg hr.1, hr.2]

@[simp] lemma radialPoint_zero (θ : ℝ) : radialPoint 0 θ = 0 := by simp [radialPoint]

theorem hall_radial (w : ℂ → ℝ) (δ : ℝ) (Cinner Couter : ℝ≥0∞)
    (_hw_nonneg : ∀ z ∈ Metric.ball (0 : ℂ) 1, 0 ≤ w z)
    (_hw_le_one : ∀ z ∈ Metric.ball (0 : ℂ) 1, w z ≤ 1)
    (_hw_center : w 0 = 1 - δ)
    (hinner : volume (innerBadDirections w) ≤ Cinner * ENNReal.ofReal δ)
    (houter : volume (outerBadDirections w) ≤ Couter * ENNReal.ofReal δ)
    (hsmall : Cinner * ENNReal.ofReal δ + Couter * ENNReal.ofReal δ <
      ENNReal.ofReal (2 * Real.pi)) :
    0 < volume (goodDirections w) :=
  goodDirections_positive_measure w _ _ hinner houter hsmall

theorem exists_hall_good_direction (w : ℂ → ℝ) (δ : ℝ)
    (Cinner Couter : ℝ≥0∞)
    (hw_nonneg : ∀ z ∈ Metric.ball (0 : ℂ) 1, 0 ≤ w z)
    (hw_le_one : ∀ z ∈ Metric.ball (0 : ℂ) 1, w z ≤ 1)
    (hw_center : w 0 = 1 - δ)
    (hinner : volume (innerBadDirections w) ≤ Cinner * ENNReal.ofReal δ)
    (houter : volume (outerBadDirections w) ≤ Couter * ENNReal.ofReal δ)
    (hsmall : Cinner * ENNReal.ofReal δ + Couter * ENNReal.ofReal δ <
      ENNReal.ofReal (2 * Real.pi)) :
    ∃ θ ∈ angleDomain, ∀ r ∈ Ico (0 : ℝ) 1, 0 < w (radialPoint r θ) := by
  apply exists_goodDirection_of_pos w
  exact hall_radial w δ Cinner Couter hw_nonneg hw_le_one hw_center
    hinner houter hsmall

end Erdos515
