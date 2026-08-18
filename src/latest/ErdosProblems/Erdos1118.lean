/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib
import ErdosProblems.Erdos1115
import ErdosProblems.Erdos1118.Erdos1118Construction
import ErdosProblems.Erdos1118.Erdos1118Sharp

/-!
# Erdős Problem 1118

This file fixes the precise Mathlib formulations of the exceptional-area
set, the maximum modulus, Camera's growth condition, and Gol'dberg's
threshold set.  It proves the measure-theoretic and logical consequences
used by the published resolution.
-/

open MeasureTheory Set Filter Laplacian InnerProductSpace
open scoped ENNReal Topology Pointwise InnerProductSpace

namespace Erdos1118

/-- An entire function in the sense used in Erdős Problem 1118. -/
def IsEntire (f : ℂ → ℂ) : Prop :=
  Differentiable ℂ f

/-- The function is entire and nonconstant. -/
def IsNonconstantEntire (f : ℂ → ℂ) : Prop :=
  IsEntire f ∧ ∃ x y, f x ≠ f y

/-- The strict large-value set `E_f(c) = {z : ‖f z‖ > c}`. -/
def exceptionalSet (f : ℂ → ℂ) (c : ℝ) : Set ℂ :=
  {z | c < ‖f z‖}

/-- `E_f(c)` has finite two-dimensional Lebesgue measure. -/
def HasFiniteArea (f : ℂ → ℂ) (c : ℝ) : Prop :=
  volume (exceptionalSet f c) ≠ ∞

theorem isOpen_exceptionalSet {f : ℂ → ℂ} (hf : Continuous f) (c : ℝ) :
    IsOpen (exceptionalSet f c) := by
  exact isOpen_lt continuous_const hf.norm

theorem measurableSet_exceptionalSet {f : ℂ → ℂ} (hf : Continuous f) (c : ℝ) :
    MeasurableSet (exceptionalSet f c) :=
  (isOpen_exceptionalSet hf c).measurableSet

/-- Two-dimensional Lebesgue measure of the complex plane is infinite. -/
theorem volume_univ_complex : volume (Set.univ : Set ℂ) = ∞ := by
  by_contra htop
  obtain ⟨n, hn⟩ := ENNReal.exists_nat_gt htop
  have hnpos : 0 < n := by
    exact_mod_cast (show (0 : ℝ≥0∞) < n from
      (bot_le : (0 : ℝ≥0∞) ≤ volume (Set.univ : Set ℂ)).trans_lt hn)
  have hnball : (n : ℝ≥0∞) ≤ volume (Metric.ball (0 : ℂ) n) := by
    rw [Complex.volume_ball]
    norm_num only [ENNReal.ofReal_natCast]
    have hnone : (1 : ℝ≥0∞) ≤ n := by exact_mod_cast hnpos
    have hpiReal : (1 : ℝ) ≤ Real.pi := by linarith [Real.one_le_pi_div_two]
    have hpi : (1 : NNReal) ≤ NNReal.pi := by exact_mod_cast hpiReal
    calc
      (n : ℝ≥0∞) = n * 1 := by simp
      _ ≤ n * n := by gcongr
      _ = n ^ 2 := by ring
      _ ≤ n ^ 2 * (NNReal.pi : ℝ≥0∞) := by
        simpa [mul_comm] using
          (mul_le_mul_left (ENNReal.coe_le_coe.mpr hpi) (n ^ 2 : ℝ≥0∞))
  exact (not_lt_of_ge (hnball.trans (measure_mono (Set.subset_univ _)))) hn

theorem volume_compl_eq_top_of_ne_top {s : Set ℂ} (hs : volume s ≠ ∞) :
    volume sᶜ = ∞ := by
  by_contra hsc
  have hadd : volume s + volume sᶜ ≠ ∞ := ENNReal.add_ne_top.mpr ⟨hs, hsc⟩
  have hle : volume (Set.univ : Set ℂ) ≤ volume s + volume sᶜ := by
    simpa only [Set.union_compl_self] using (measure_union_le s sᶜ)
  rw [volume_univ_complex] at hle
  exact hadd (top_unique hle)

/-- The zero set of a nonconstant entire function is countable. -/
theorem countable_zero_set {f : ℂ → ℂ} (hf : IsNonconstantEntire f) :
    (f ⁻¹' {0}).Countable := by
  obtain ⟨x, hx⟩ : ∃ x, f x ≠ 0 := by
    obtain ⟨x, y, hxy⟩ := hf.2
    by_cases hx : f x = 0
    · exact ⟨y, by simpa [hx] using hxy.symm⟩
    · exact ⟨x, hx⟩
  have ha : AnalyticOnNhd ℂ f Set.univ :=
    Complex.analyticOnNhd_univ_iff_differentiable.mpr hf.1
  have hcod : (f ⁻¹' {0})ᶜ ∈ codiscrete ℂ := by
    simpa only [Set.preimage_compl] using ha.preimage_zero_mem_codiscrete hx
  obtain ⟨hclosed, hdisc⟩ := compl_mem_codiscrete_iff.mp hcod
  exact (isLindelof_univ.of_isClosed_subset hclosed
    (Set.subset_univ _)).countable_of_isDiscrete hdisc

/-- The strict zero-level superlevel set has infinite area. -/
theorem volume_exceptionalSet_zero {f : ℂ → ℂ} (hf : IsNonconstantEntire f) :
    volume (exceptionalSet f 0) = ∞ := by
  have heq : exceptionalSet f 0 = (f ⁻¹' {0})ᶜ := by
    ext z
    simp [exceptionalSet, norm_pos_iff]
  have hzmeasure : volume ((f ⁻¹' {0})ᶜ)ᶜ = 0 := by
    simpa using (countable_zero_set hf).measure_zero volume
  rw [heq, measure_of_measure_compl_eq_zero hzmeasure, volume_univ_complex]

/-- For a nonconstant entire function, a finite-area strict superlevel must have positive level.
Thus positivity of the `c` in the original problem is a consequence, not an extra hypothesis. -/
theorem positive_level_of_hasFiniteArea {f : ℂ → ℂ} {c : ℝ}
    (hf : IsNonconstantEntire f) (harea : HasFiniteArea f c) : 0 < c := by
  by_contra hc
  have hc0 : c ≤ 0 := le_of_not_gt hc
  have hmono : volume (exceptionalSet f 0) ≤ volume (exceptionalSet f c) := by
    apply measure_mono
    intro z hz
    exact hc0.trans_lt hz
  rw [volume_exceptionalSet_zero hf] at hmono
  exact harea (top_unique hmono)

/-- The maximum modulus.  The supremum is attained for continuous `f`. -/
noncomputable def maximumModulus (f : ℂ → ℂ) (r : ℝ) : ℝ :=
  sSup ((fun z : ℂ ↦ ‖f z‖) '' Metric.sphere (0 : ℂ) r)

/-- Reparametrize the radius-`r` circle by the unit circle. -/
theorem maximumModulus_eq_sSup_unit_sphere (f : ℂ → ℂ) {r : ℝ} (hr : 0 ≤ r) :
    maximumModulus f r =
      sSup ((fun w : ℂ ↦ ‖f ((r : ℂ) * w)‖) '' Metric.sphere (0 : ℂ) 1) := by
  unfold maximumModulus
  have hsphere : Metric.sphere (0 : ℂ) r =
      (r : ℂ) • Metric.sphere (0 : ℂ) 1 := by
    rw [_root_.smul_sphere (c := (r : ℂ)) (x := (0 : ℂ)) zero_le_one]
    simp [Complex.norm_real, abs_of_nonneg hr]
  rw [hsphere, ← Set.image_smul, Set.image_image]
  rfl

/-- The maximum modulus of a continuous function varies continuously with every nonnegative
radius. -/
theorem continuousOn_maximumModulus {f : ℂ → ℂ} (hf : Continuous f) :
    ContinuousOn (maximumModulus f) (Set.Ici 0) := by
  let F : ℝ → ℝ := fun r ↦
    sSup ((fun w : ℂ ↦ ‖f ((r : ℂ) * w)‖) '' Metric.sphere (0 : ℂ) 1)
  have hF : Continuous F := by
    apply (isCompact_sphere (0 : ℂ) 1).continuous_sSup
    fun_prop
  apply hF.continuousOn.congr
  intro r hr
  exact maximumModulus_eq_sSup_unit_sphere f hr

/-- On every circle of nonnegative radius, the supremum in `maximumModulus` is attained.
The maximizing point and its universal property are recorded explicitly because both are used
throughout the growth argument. -/
theorem exists_maximumModulus_eq {f : ℂ → ℂ} (hf : Continuous f) {r : ℝ}
    (hr : 0 ≤ r) :
    ∃ z : ℂ, ‖z‖ = r ∧ maximumModulus f r = ‖f z‖ ∧
      ∀ w : ℂ, ‖w‖ = r → ‖f w‖ ≤ ‖f z‖ := by
  obtain ⟨z, hz, hM, hmax⟩ :=
    (isCompact_sphere (0 : ℂ) r).exists_sSup_image_eq_and_ge
      (NormedSpace.sphere_nonempty.mpr hr) hf.norm.continuousOn
  refine ⟨z, ?_, hM, ?_⟩
  · simpa only [mem_sphere_iff_norm, sub_zero] using hz
  · intro w hw
    apply hmax w
    simpa only [mem_sphere_iff_norm, sub_zero] using hw

theorem maximumModulus_nonneg {f : ℂ → ℂ} (hf : Continuous f) {r : ℝ}
    (hr : 0 ≤ r) : 0 ≤ maximumModulus f r := by
  obtain ⟨z, -, hM, -⟩ := exists_maximumModulus_eq hf hr
  rw [hM]
  exact norm_nonneg _

theorem norm_le_maximumModulus {f : ℂ → ℂ} (hf : Continuous f) {r : ℝ}
    (hr : 0 ≤ r) {z : ℂ} (hz : ‖z‖ = r) : ‖f z‖ ≤ maximumModulus f r := by
  obtain ⟨w, -, hM, hmax⟩ := exists_maximumModulus_eq hf hr
  rw [hM]
  exact hmax z hz

/-- The maximum-modulus principle, in the exact form needed below: the circle maximum controls
the whole closed disk. -/
theorem norm_le_maximumModulus_of_norm_le {f : ℂ → ℂ} (hf : IsEntire f) {r : ℝ}
    (hr : 0 ≤ r) {z : ℂ} (hz : ‖z‖ ≤ r) : ‖f z‖ ≤ maximumModulus f r := by
  by_cases hr0 : r = 0
  · have hz0 : z = 0 := norm_eq_zero.mp (le_antisymm (hr0 ▸ hz) (norm_nonneg z))
    subst z
    exact norm_le_maximumModulus hf.continuous hr (by simp [hr0])
  · apply Complex.norm_le_of_forall_mem_frontier_norm_le
      (Metric.isBounded_ball (x := (0 : ℂ)) (r := r))
      hf.diffContOnCl (C := maximumModulus f r)
    · intro w hw
      apply norm_le_maximumModulus hf.continuous hr
      have hws : w ∈ Metric.sphere (0 : ℂ) r := Metric.frontier_ball_subset_sphere hw
      simpa only [mem_sphere_iff_norm, sub_zero] using hws
    · rw [closure_ball (0 : ℂ) hr0]
      simpa only [mem_closedBall_iff_norm, sub_zero] using hz

/-- For an entire function, the maximum modulus is monotone on nonnegative radii. -/
theorem maximumModulus_mono {f : ℂ → ℂ} (hf : IsEntire f) {r s : ℝ}
    (hr : 0 ≤ r) (hrs : r ≤ s) : maximumModulus f r ≤ maximumModulus f s := by
  have hs : 0 ≤ s := hr.trans hrs
  obtain ⟨z, hz, hM, -⟩ := exists_maximumModulus_eq hf.continuous hr
  rw [hM]
  exact norm_le_maximumModulus_of_norm_le hf hs (hz.le.trans hrs)

/-- Maximum modulus commutes with multiplication by a constant. -/
theorem maximumModulus_const_mul {f : ℂ → ℂ} (hf : Continuous f) (a : ℂ)
    {r : ℝ} (hr : 0 ≤ r) :
    maximumModulus (fun z ↦ a * f z) r = ‖a‖ * maximumModulus f r := by
  have hg : Continuous (fun z ↦ a * f z) := continuous_const.mul hf
  obtain ⟨z, hz, hMf, hmaxf⟩ := exists_maximumModulus_eq hf hr
  obtain ⟨w, hw, hMg, hmaxg⟩ :=
    exists_maximumModulus_eq hg hr
  apply le_antisymm
  · rw [hMg, norm_mul]
    exact mul_le_mul_of_nonneg_left (by simpa [hMf] using hmaxf w hw) (norm_nonneg a)
  · rw [hMf, ← norm_mul, hMg]
    exact hmaxg z hz

/-- A nonconstant entire function has maximum modulus tending to infinity. -/
theorem maximumModulus_tendsto_atTop {f : ℂ → ℂ} (hf : IsNonconstantEntire f) :
    Tendsto (maximumModulus f) atTop atTop := by
  have hunbdd : ¬ Bornology.IsBounded (Set.range f) := by
    intro hbdd
    obtain ⟨x, y, hxy⟩ := hf.2
    exact hxy (hf.1.apply_eq_apply_of_bounded hbdd x y)
  have hlarge : ∀ B : ℝ, ∃ z : ℂ, B < ‖f z‖ := by
    intro B
    by_contra h
    push Not at h
    apply hunbdd
    exact isBounded_iff_forall_norm_le.mpr ⟨B, by
      rintro _ ⟨z, rfl⟩
      exact h z⟩
  refine tendsto_atTop.mpr fun B ↦ ?_
  obtain ⟨z, hz⟩ := hlarge B
  filter_upwards [eventually_ge_atTop ‖z‖] with r hr
  have hzM : ‖f z‖ ≤ maximumModulus f ‖z‖ :=
    norm_le_maximumModulus hf.1.continuous (norm_nonneg z) rfl
  exact hz.le.trans (hzM.trans (maximumModulus_mono hf.1 (norm_nonneg z) hr))

theorem log_log_maximumModulus_tendsto_atTop {f : ℂ → ℂ}
    (hf : IsNonconstantEntire f) :
    Tendsto (fun r ↦ Real.log (Real.log (maximumModulus f r))) atTop atTop :=
  Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp
    (maximumModulus_tendsto_atTop hf))

theorem eventually_pos_log_log_maximumModulus {f : ℂ → ℂ}
    (hf : IsNonconstantEntire f) :
    ∃ R > 0, ∀ r, R ≤ r → 0 < Real.log (Real.log (maximumModulus f r)) := by
  obtain ⟨R, hR⟩ := eventually_atTop.mp
    ((log_log_maximumModulus_tendsto_atTop hf).eventually_gt_atTop 0)
  refine ⟨max R 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro r hr
  exact hR r ((le_max_left _ _).trans hr)

/-- Multiplying the maximum modulus by a fixed positive constant changes its double logarithm
by at most a factor two on a sufficiently large tail.  This quantitative version is used to
transport the Camera integral through normalization of the level. -/
theorem eventually_log_log_const_mul_le_two {f : ℂ → ℂ}
    (hf : IsNonconstantEntire f) {a : ℝ} (ha : 0 < a) :
    ∃ R > 0, ∀ r, R ≤ r →
      0 < Real.log (Real.log (maximumModulus f r)) ∧
      0 < Real.log (Real.log (a * maximumModulus f r)) ∧
      Real.log (Real.log (a * maximumModulus f r)) ≤
        2 * Real.log (Real.log (maximumModulus f r)) := by
  let K : ℝ := max 4 (2 * |Real.log a|)
  have hlogM : Tendsto (fun r ↦ Real.log (maximumModulus f r)) atTop atTop :=
    Real.tendsto_log_atTop.comp (maximumModulus_tendsto_atTop hf)
  obtain ⟨R, hR⟩ := eventually_atTop.mp (hlogM.eventually_ge_atTop K)
  refine ⟨max R 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro r hr
  have hL : K ≤ Real.log (maximumModulus f r) :=
    hR r ((le_max_left _ _).trans hr)
  have hL4 : 4 ≤ Real.log (maximumModulus f r) :=
    (le_max_left _ _).trans hL
  have habs : 2 * |Real.log a| ≤ Real.log (maximumModulus f r) :=
    (le_max_right _ _).trans hL
  have hMne : maximumModulus f r ≠ 0 := by
    intro hzero
    simp [hzero] at hL4
    linarith
  have hlogmul : Real.log (a * maximumModulus f r) =
      Real.log a + Real.log (maximumModulus f r) :=
    Real.log_mul ha.ne' hMne
  have hlower : 1 < Real.log (a * maximumModulus f r) := by
    rw [hlogmul]
    have hnegabs : -|Real.log a| ≤ Real.log a := neg_abs_le _
    nlinarith [abs_nonneg (Real.log a)]
  have hupper : Real.log (a * maximumModulus f r) ≤
      (Real.log (maximumModulus f r)) ^ 2 := by
    rw [hlogmul]
    have habsupper : Real.log a ≤ |Real.log a| := le_abs_self _
    nlinarith [abs_nonneg (Real.log a)]
  refine ⟨Real.log_pos (by linarith), Real.log_pos hlower, ?_⟩
  calc
    Real.log (Real.log (a * maximumModulus f r))
        ≤ Real.log ((Real.log (maximumModulus f r)) ^ 2) :=
          Real.log_le_log (lt_trans zero_lt_one hlower) hupper
    _ = 2 * Real.log (Real.log (maximumModulus f r)) := by
      rw [Real.log_pow]
      norm_num

/-! ## Polar area decomposition -/

/-- The point with polar coordinates `(r, θ)`.  We use angles in `(-π, π)`, matching
Mathlib's `Complex.polarCoord`. -/
noncomputable def polarPoint (r θ : ℝ) : ℂ :=
  Complex.polarCoord.symm (r, θ)

/-- The angular section of `s` at radius `r`, restricted to the standard argument interval. -/
def angularSection (s : Set ℂ) (r : ℝ) : Set ℝ :=
  {θ | θ ∈ Set.Ioo (-Real.pi) Real.pi ∧ polarPoint r θ ∈ s}

/-- The measurable subset of radius-angle space whose fibers are `angularSection s r`. -/
def polarSectionSet (s : Set ℂ) : Set (ℝ × ℝ) :=
  {p | p.2 ∈ Set.Ioo (-Real.pi) Real.pi ∧ polarPoint p.1 p.2 ∈ s}

/-- Angular sections of open planar sets are open. -/
theorem isOpen_angularSection {s : Set ℂ} (hs : IsOpen s) (r : ℝ) :
    IsOpen (angularSection s r) := by
  change IsOpen
    (Set.Ioo (-Real.pi) Real.pi ∩ (fun θ : ℝ ↦ polarPoint r θ) ⁻¹' s)
  apply isOpen_Ioo.inter
  apply hs.preimage
  have h : Continuous (fun θ : ℝ ↦
      (r : ℂ) * (Real.cos θ + Real.sin θ * Complex.I)) := by fun_prop
  convert h using 1
  funext θ
  simp [polarPoint]

theorem measurableSet_polarSectionSet {s : Set ℂ} (hs : MeasurableSet s) :
    MeasurableSet (polarSectionSet s) := by
  change MeasurableSet
    ((fun p : ℝ × ℝ ↦ p.2) ⁻¹' Set.Ioo (-Real.pi) Real.pi ∩
      (fun p : ℝ × ℝ ↦ polarPoint p.1 p.2) ⁻¹' s)
  apply (measurable_snd measurableSet_Ioo).inter
  apply hs.preimage
  have h : Measurable (fun p : ℝ × ℝ ↦
      (p.1 : ℂ) * (Real.cos p.2 + Real.sin p.2 * Complex.I)) := by fun_prop
  convert h using 1
  funext p
  simp [polarPoint]

theorem angularSection_eq_prodMk_preimage (s : Set ℂ) (r : ℝ) :
    angularSection s r = Prod.mk r ⁻¹' polarSectionSet s := by
  rfl

/-- The angular width, as an `ENNReal`, is measurable as a function of the radius. -/
theorem measurable_volume_angularSection {s : Set ℂ} (hs : MeasurableSet s) :
    Measurable (fun r : ℝ ↦ volume (angularSection s r)) := by
  simpa only [angularSection_eq_prodMk_preimage] using
    measurable_measure_prodMk_left (measurableSet_polarSectionSet hs)

theorem measurableSet_angularSection {s : Set ℂ} (hs : MeasurableSet s) (r : ℝ) :
    MeasurableSet (angularSection s r) := by
  apply measurableSet_Ioo.inter
  apply hs.preimage
  have h : Measurable (fun θ : ℝ ↦
      (r : ℂ) * (Real.cos θ + Real.sin θ * Complex.I)) := by fun_prop
  convert h using 1
  funext θ
  simp [polarPoint]

/-- Every angular section has finite one-dimensional measure, since it is contained in the
bounded standard argument interval. -/
theorem volume_angularSection_ne_top (s : Set ℂ) (r : ℝ) :
    volume (angularSection s r) ≠ ∞ := by
  apply ne_top_of_le_ne_top
    (ne_of_lt (measure_Ioo_lt_top :
      volume (Set.Ioo (-Real.pi) Real.pi) < ∞))
  apply measure_mono
  intro θ hθ
  exact hθ.1

/-- The real-valued angular width of `s` at radius `r`.  Finiteness of angular sections makes
this an exact real encoding of their `ENNReal` measure, rather than a truncated quantity. -/
noncomputable def angularWidth (s : Set ℂ) (r : ℝ) : ℝ :=
  (volume (angularSection s r)).toReal

theorem angularWidth_nonneg (s : Set ℂ) (r : ℝ) :
    0 ≤ angularWidth s r :=
  ENNReal.toReal_nonneg

theorem angularWidth_le_two_pi (s : Set ℂ) (r : ℝ) :
    angularWidth s r ≤ 2 * Real.pi := by
  have hsub : angularSection s r ⊆ Set.Ioo (-Real.pi) Real.pi := fun _ h ↦ h.1
  have htop : volume (Set.Ioo (-Real.pi) Real.pi) ≠ ∞ :=
    ne_of_lt measure_Ioo_lt_top
  calc
    angularWidth s r = volume.real (angularSection s r) := rfl
    _ ≤ volume.real (Set.Ioo (-Real.pi) Real.pi) := measureReal_mono hsub htop
    _ = 2 * Real.pi := by
      rw [measureReal_def, Real.volume_Ioo]
      simp only [sub_neg_eq_add,
        ENNReal.toReal_ofReal (by positivity : 0 ≤ Real.pi + Real.pi)]
      ring

theorem measurable_angularWidth {s : Set ℂ} (hs : MeasurableSet s) :
    Measurable (angularWidth s) := by
  exact (measurable_volume_angularSection hs).ennreal_toReal

theorem ofReal_angularWidth (s : Set ℂ) (r : ℝ) :
    ENNReal.ofReal (angularWidth s r) = volume (angularSection s r) := by
  exact ENNReal.ofReal_toReal (volume_angularSection_ne_top s r)

/-- Polar Tonelli formula for the area of a measurable planar set.  The missing nonpositive
radius and the omitted argument ray are null sets, as encoded in Mathlib's polar-coordinate
change-of-variables theorem. -/
theorem volume_eq_lintegral_polar {s : Set ℂ} (hs : MeasurableSet s) :
    volume s = ∫⁻ r in Set.Ioi (0 : ℝ),
      ENNReal.ofReal r * volume (angularSection s r) := by
  rw [← lintegral_indicator_one hs, ← Complex.lintegral_comp_polarCoord_symm]
  change (∫⁻ p in Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-Real.pi) Real.pi,
    ENNReal.ofReal p.1 • s.indicator 1 (Complex.polarCoord.symm p)) = _
  rw [Measure.volume_eq_prod]
  rw [MeasureTheory.setLIntegral_prod]
  · apply lintegral_congr
    intro r
    simp only [smul_eq_mul]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    rw [← setLIntegral_one (angularSection s r)]
    apply congrArg (fun x : ℝ≥0∞ ↦ ENNReal.ofReal r * x)
    calc
      ∫⁻ (a : ℝ) in Ioo (-Real.pi) Real.pi,
          s.indicator 1 (Complex.polarCoord.symm (r, a))
          = ∫⁻ (a : ℝ) in Ioo (-Real.pi) Real.pi,
              (angularSection s r).indicator 1 a := by
              apply setLIntegral_congr_fun measurableSet_Ioo
              intro θ hθ
              change s.indicator 1 (polarPoint r θ) =
                (angularSection s r).indicator 1 θ
              by_cases h : polarPoint r θ ∈ s
              · have ha : θ ∈ angularSection s r := ⟨hθ, h⟩
                simp only [indicator_of_mem h, indicator_of_mem ha]
                rfl
              · have ha : θ ∉ angularSection s r := fun ha ↦ h ha.2
                simp only [indicator_of_notMem h, indicator_of_notMem ha]
      _ = ∫⁻ (a : ℝ) in angularSection s r ∩ Ioo (-Real.pi) Real.pi, 1 :=
        setLIntegral_indicator (measurableSet_angularSection hs r) _
      _ = ∫⁻ (a : ℝ) in angularSection s r, 1 := by
        rw [inter_eq_left.mpr]
        intro θ hθ
        exact hθ.1
  · have hpolar : AEMeasurable (fun p : ℝ × ℝ ↦ Complex.polarCoord.symm p)
        (((volume : Measure ℝ).prod volume).restrict Complex.polarCoord.target) :=
      Complex.polarCoord.symm.continuousOn.aemeasurable
        Complex.polarCoord.open_target.measurableSet
    have hind : AEMeasurable
        (fun p : ℝ × ℝ ↦ s.indicator 1 (Complex.polarCoord.symm p))
        (((volume : Measure ℝ).prod volume).restrict Complex.polarCoord.target) :=
      ((measurable_indicator_const_iff (1 : ℝ≥0∞)).mpr hs).comp_aemeasurable hpolar
    have hr : AEMeasurable (fun p : ℝ × ℝ ↦ ENNReal.ofReal p.1)
        (((volume : Measure ℝ).prod volume).restrict Complex.polarCoord.target) :=
      (ENNReal.measurable_ofReal.comp measurable_fst).aemeasurable.restrict
    rw [Complex.polarCoord_target] at hr hind
    refine (hr.mul hind).congr (Eventually.of_forall fun p ↦ ?_)
    simp only [Pi.mul_apply, smul_eq_mul]

/-- Real-valued version of the polar Tonelli formula. -/
theorem volume_eq_lintegral_angularWidth {s : Set ℂ} (hs : MeasurableSet s) :
    volume s = ∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal (r * angularWidth s r) := by
  rw [volume_eq_lintegral_polar hs]
  apply setLIntegral_congr_fun measurableSet_Ioi
  intro r hr
  change ENNReal.ofReal r * volume (angularSection s r) =
    ENNReal.ofReal (r * angularWidth s r)
  rw [ENNReal.ofReal_mul hr.le, ofReal_angularWidth]

/-- Finite planar area is exactly the hypothesis needed to make the radius-weighted angular
width Bochner-integrable. -/
theorem integrableOn_radius_mul_angularWidth {s : Set ℂ} (hs : MeasurableSet s)
    (hfinite : volume s ≠ ∞) :
    IntegrableOn (fun r : ℝ ↦ r * angularWidth s r) (Set.Ioi 0) := by
  refine ⟨(measurable_id.mul (measurable_angularWidth hs)).aestronglyMeasurable.restrict, ?_⟩
  have hnonneg : 0 ≤ᵐ[(volume : Measure ℝ).restrict (Set.Ioi 0)]
      (fun r : ℝ ↦ r * angularWidth s r) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    exact mul_nonneg hr.le (angularWidth_nonneg s r)
  rw [hasFiniteIntegral_iff_ofReal hnonneg]
  apply lt_top_iff_ne_top.mpr
  rw [← volume_eq_lintegral_angularWidth hs]
  exact hfinite

/-! ## Dyadic interval bookkeeping -/

/-- Positive dyadic half-open intervals partition a positive ray. -/
theorem iUnion_dyadic_Ico {R : ℝ} (hR : 0 < R) :
    (⋃ n : ℕ, Set.Ico (R * (2 : ℝ) ^ n) (R * (2 : ℝ) ^ (n + 1))) =
      Set.Ici R := by
  ext x
  constructor
  · intro hx
    simp only [Set.mem_iUnion, Set.mem_Ico] at hx
    obtain ⟨n, hnlow, -⟩ := hx
    have hone : (1 : ℝ) ≤ (2 : ℝ) ^ n := by
      exact one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
    exact Set.mem_Ici.mpr (le_trans (by simpa using mul_le_mul_of_nonneg_left hone hR.le) hnlow)
  · intro hx
    have hratio : 1 ≤ x / R := by
      apply (le_div_iff₀ hR).mpr
      simpa only [one_mul] using Set.mem_Ici.mp hx
    obtain ⟨n, hnlow, hnup⟩ := exists_nat_pow_near hratio (by norm_num : (1 : ℝ) < 2)
    simp only [Set.mem_iUnion, Set.mem_Ico]
    refine ⟨n, ?_, ?_⟩
    · simpa [mul_comm] using (le_div_iff₀ hR).mp hnlow
    · simpa [mul_comm] using (div_lt_iff₀ hR).mp hnup

theorem pairwise_disjoint_dyadic_Ico {R : ℝ} (hR : 0 < R) :
    ∀ ⦃m n : ℕ⦄, m ≠ n →
      Disjoint (Set.Ico (R * (2 : ℝ) ^ m) (R * (2 : ℝ) ^ (m + 1)))
        (Set.Ico (R * (2 : ℝ) ^ n) (R * (2 : ℝ) ^ (n + 1))) := by
  intro m n hmn
  rcases lt_or_gt_of_ne hmn with hlt | hgt
  · apply Set.disjoint_left.mpr
    intro x hxm hxn
    have hp : (2 : ℝ) ^ (m + 1) ≤ (2 : ℝ) ^ n :=
      pow_le_pow_right₀ (by norm_num) (Nat.succ_le_iff.mpr hlt)
    have hub : R * (2 : ℝ) ^ (m + 1) ≤ x :=
      (mul_le_mul_of_nonneg_left hp hR.le).trans hxn.1
    exact (not_lt_of_ge hub) hxm.2
  · apply Set.disjoint_left.mpr
    intro x hxm hxn
    have hp : (2 : ℝ) ^ (n + 1) ≤ (2 : ℝ) ^ m :=
      pow_le_pow_right₀ (by norm_num) (Nat.succ_le_iff.mpr hgt)
    have hub : R * (2 : ℝ) ^ (n + 1) ≤ x :=
      (mul_le_mul_of_nonneg_left hp hR.le).trans hxm.1
    exact (not_lt_of_ge hub) hxn.2

/-- A comparison estimate on every dyadic interval can be summed to a global tail
integrability statement.  This is the final abstract summation step in Camera's argument. -/
theorem integrableOn_Ici_of_dyadic_bounds {w g : ℝ → ℝ} {R C : ℝ}
    (hR : 0 < R)
    (hw : IntegrableOn w (Set.Ici R))
    (hw_nonneg : ∀ x, R ≤ x → 0 ≤ w x)
    (hg : ∀ n : ℕ,
      IntegrableOn g (Set.Ico (R * (2 : ℝ) ^ n) (R * (2 : ℝ) ^ (n + 1))))
    (hbound : ∀ n : ℕ,
      (∫ x in Set.Ico (R * (2 : ℝ) ^ n) (R * (2 : ℝ) ^ (n + 1)), ‖g x‖) ≤
        C * ∫ x in Set.Ico (R * (2 : ℝ) ^ n) (R * (2 : ℝ) ^ (n + 1)), w x) :
    IntegrableOn g (Set.Ici R) := by
  let I : ℕ → Set ℝ := fun n ↦
    Set.Ico (R * (2 : ℝ) ^ n) (R * (2 : ℝ) ^ (n + 1))
  have hIunion : (⋃ n, I n) = Set.Ici R := by
    simpa only [I] using iUnion_dyadic_Ico hR
  have hIdisjoint : ∀ ⦃m n : ℕ⦄, m ≠ n → Disjoint (I m) (I n) := by
    simpa only [I] using pairwise_disjoint_dyadic_Ico hR
  have hsumw : HasSum (fun n ↦ ∫ x in I n, w x) (∫ x in Set.Ici R, w x) := by
    rw [← hIunion]
    exact hasSum_integral_iUnion (fun _ ↦ measurableSet_Ico) hIdisjoint
      (by simpa only [hIunion] using hw)
  have hmass_nonneg : ∀ n, 0 ≤ ∫ x in I n, w x := by
    intro n
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ico] with x hx
    apply hw_nonneg x
    have hone : (1 : ℝ) ≤ (2 : ℝ) ^ n := one_le_pow₀ (by norm_num)
    simpa only [mul_one] using (mul_le_mul_of_nonneg_left hone hR.le).trans hx.1
  have hmajorant : Summable (fun n ↦ C * ∫ x in I n, w x) :=
    hsumw.summable.mul_left C
  have hnormsum : Summable (fun n ↦ ∫ x in I n, ‖g x‖) := by
    apply hmajorant.of_nonneg_of_le
    · intro n
      exact integral_nonneg_of_ae (Eventually.of_forall fun _ ↦ norm_nonneg _)
    · intro n
      simpa only [I] using hbound n
  rw [← hIunion]
  exact integrableOn_iUnion_of_summable_integral_norm hg hnormsum

/-- A one-annulus-shifted version of the dyadic summation lemma.  This is the indexing
that arises in Camera's proof: area from the annulus `[q,2q)` controls the growth
integrand on `[2q,4q)`. -/
theorem integrableOn_Ici_two_mul_of_shifted_dyadic_bounds
    {w g : ℝ → ℝ} {R C : ℝ}
    (hR : 0 < R)
    (hw : IntegrableOn w (Set.Ici R))
    (hg : ∀ n : ℕ,
      IntegrableOn g
        (Set.Ico (R * (2 : ℝ) ^ (n + 1)) (R * (2 : ℝ) ^ (n + 2))))
    (hbound : ∀ n : ℕ,
      (∫ x in Set.Ico (R * (2 : ℝ) ^ (n + 1)) (R * (2 : ℝ) ^ (n + 2)), ‖g x‖) ≤
        C * ∫ x in Set.Ico (R * (2 : ℝ) ^ n) (R * (2 : ℝ) ^ (n + 1)), w x) :
    IntegrableOn g (Set.Ici (2 * R)) := by
  let I : ℕ → Set ℝ := fun n ↦
    Set.Ico (R * (2 : ℝ) ^ n) (R * (2 : ℝ) ^ (n + 1))
  have hIunion : (⋃ n, I n) = Set.Ici R := by
    simpa only [I] using iUnion_dyadic_Ico hR
  have hIdisjoint : ∀ ⦃m n : ℕ⦄, m ≠ n → Disjoint (I m) (I n) := by
    simpa only [I] using pairwise_disjoint_dyadic_Ico hR
  have hshift (n : ℕ) :
      I (n + 1) =
        Set.Ico ((2 * R) * (2 : ℝ) ^ n) ((2 * R) * (2 : ℝ) ^ (n + 1)) := by
    simp only [I, pow_succ]
    congr 1 <;> ring
  have hshiftUnion : (⋃ n, I (n + 1)) = Set.Ici (2 * R) := by
    simp_rw [hshift]
    exact iUnion_dyadic_Ico (mul_pos (by norm_num) hR)
  have hsumw : HasSum (fun n ↦ ∫ x in I n, w x) (∫ x in Set.Ici R, w x) := by
    rw [← hIunion]
    exact hasSum_integral_iUnion (fun _ ↦ measurableSet_Ico) hIdisjoint
      (by simpa only [hIunion] using hw)
  have hmajorant : Summable (fun n ↦ C * ∫ x in I n, w x) :=
    hsumw.summable.mul_left C
  have hnormsum : Summable (fun n ↦ ∫ x in I (n + 1), ‖g x‖) := by
    apply hmajorant.of_nonneg_of_le
    · intro n
      exact integral_nonneg_of_ae (Eventually.of_forall fun _ ↦ norm_nonneg _)
    · intro n
      simpa only [I, Nat.add_assoc, Nat.reduceAdd] using hbound n
  rw [← hshiftUnion]
  apply integrableOn_iUnion_of_summable_integral_norm
  · intro n
    simpa only [I, Nat.add_assoc, Nat.reduceAdd] using hg n
  · exact hnormsum

/-- The two-annulus-shifted summation needed by the endpoint-stable Tsuji estimate.  Area on
`[q,2q)` controls the growth integrand on `[4q,8q)`, and summing therefore gives integrability
on the tail starting at `4R`. -/
theorem integrableOn_Ici_four_mul_of_two_shifted_dyadic_bounds
    {w g : ℝ → ℝ} {R C : ℝ}
    (hR : 0 < R)
    (hw : IntegrableOn w (Set.Ici R))
    (hg : ∀ n : ℕ,
      IntegrableOn g
        (Set.Ico (R * (2 : ℝ) ^ (n + 2)) (R * (2 : ℝ) ^ (n + 3))))
    (hbound : ∀ n : ℕ,
      (∫ x in Set.Ico (R * (2 : ℝ) ^ (n + 2)) (R * (2 : ℝ) ^ (n + 3)), ‖g x‖) ≤
        C * ∫ x in Set.Ico (R * (2 : ℝ) ^ n) (R * (2 : ℝ) ^ (n + 1)), w x) :
    IntegrableOn g (Set.Ici (4 * R)) := by
  let I : ℕ → Set ℝ := fun n ↦
    Set.Ico (R * (2 : ℝ) ^ n) (R * (2 : ℝ) ^ (n + 1))
  have hIunion : (⋃ n, I n) = Set.Ici R := by
    simpa only [I] using iUnion_dyadic_Ico hR
  have hIdisjoint : ∀ ⦃m n : ℕ⦄, m ≠ n → Disjoint (I m) (I n) := by
    simpa only [I] using pairwise_disjoint_dyadic_Ico hR
  have hshift (n : ℕ) :
      I (n + 2) =
        Set.Ico ((4 * R) * (2 : ℝ) ^ n) ((4 * R) * (2 : ℝ) ^ (n + 1)) := by
    simp only [I, pow_succ]
    congr 1 <;> ring
  have hshiftUnion : (⋃ n, I (n + 2)) = Set.Ici (4 * R) := by
    simp_rw [hshift]
    exact iUnion_dyadic_Ico (mul_pos (by norm_num) hR)
  have hsumw : HasSum (fun n ↦ ∫ x in I n, w x) (∫ x in Set.Ici R, w x) := by
    rw [← hIunion]
    exact hasSum_integral_iUnion (fun _ ↦ measurableSet_Ico) hIdisjoint
      (by simpa only [hIunion] using hw)
  have hmajorant : Summable (fun n ↦ C * ∫ x in I n, w x) :=
    hsumw.summable.mul_left C
  have hnormsum : Summable (fun n ↦ ∫ x in I (n + 2), ‖g x‖) := by
    apply hmajorant.of_nonneg_of_le
    · intro n
      exact integral_nonneg_of_ae (Eventually.of_forall fun _ ↦ norm_nonneg _)
    · intro n
      simpa only [I, Nat.add_assoc, Nat.reduceAdd] using hbound n
  rw [← hshiftUnion]
  apply integrableOn_iUnion_of_summable_integral_norm
  · intro n
    simpa only [I, Nat.add_assoc, Nat.reduceAdd] using hg n
  · exact hnormsum

/-- The polar Tonelli formula applied to the exceptional set of a continuous function. -/
theorem volume_exceptionalSet_eq_lintegral_polar {f : ℂ → ℂ} (hf : Continuous f)
    (c : ℝ) :
    volume (exceptionalSet f c) = ∫⁻ r in Set.Ioi (0 : ℝ),
      ENNReal.ofReal r * volume (angularSection (exceptionalSet f c) r) :=
  volume_eq_lintegral_polar (measurableSet_exceptionalSet hf c)

/-- Finite exceptional area gives the finite weighted angular-section integral used as the
measure-theoretic input to Camera's argument. -/
theorem polar_exceptional_integral_ne_top {f : ℂ → ℂ} {c : ℝ}
    (hf : Continuous f) (harea : HasFiniteArea f c) :
    (∫⁻ r in Set.Ioi (0 : ℝ),
      ENNReal.ofReal r * volume (angularSection (exceptionalSet f c) r)) ≠ ∞ := by
  rw [← volume_exceptionalSet_eq_lintegral_polar hf c]
  exact harea

theorem integrableOn_exceptional_radius_mul_angularWidth {f : ℂ → ℂ} {c : ℝ}
    (hf : Continuous f) (harea : HasFiniteArea f c) :
    IntegrableOn
      (fun r : ℝ ↦ r * angularWidth (exceptionalSet f c) r) (Set.Ioi 0) :=
  integrableOn_radius_mul_angularWidth (measurableSet_exceptionalSet hf c) harea

/-! ## The logarithmic subharmonic reduction -/

/-- For real exponents greater than `3`, the real norm power is twice continuously
differentiable.  Mathlib currently supplies the `C¹` statement; differentiating its explicit
Fréchet derivative once more gives the `C²` version needed for a smooth positive part. -/
theorem contDiff_two_norm_rpow_real {p : ℝ} (hp : 3 < p) :
    ContDiff ℝ 2 (fun x : ℝ ↦ ‖x‖ ^ p) := by
  have h : ContDiff ℝ ((1 : ℕ∞) + 1) (fun x : ℝ ↦ ‖x‖ ^ p) := by
    rw [contDiff_succ_iff_fderiv]
    refine ⟨differentiable_norm_rpow (by linarith), by norm_num, ?_⟩
    rw [show fderiv ℝ (fun x : ℝ ↦ ‖x‖ ^ p) =
        (fun x ↦ (p * ‖x‖ ^ (p - 2)) • innerSL ℝ x) from
      funext fun x ↦ fderiv_norm_rpow x (by linarith : 1 < p)]
    exact (contDiff_const.mul (contDiff_norm_rpow (by linarith : 1 < p - 2))).smul
      (innerSL ℝ).contDiff
  convert h using 1
  norm_num

/-- A global `C²` replacement for the positive part.  The odd fifth power makes the
algebraic formula equal to `(max x 0)⁵` while retaining two continuous derivatives at zero. -/
noncomputable def smoothPositivePart (x : ℝ) : ℝ :=
  (x ^ 5 + ‖x‖ ^ (5 : ℝ)) / 2

theorem smoothPositivePart_eq_max (x : ℝ) :
    smoothPositivePart x = (max x 0) ^ 5 := by
  unfold smoothPositivePart
  have hr : ‖x‖ ^ (5 : ℝ) = ‖x‖ ^ (5 : ℕ) := by
    convert Real.rpow_natCast ‖x‖ 5 using 1
    norm_num
  rw [hr]
  by_cases hx : 0 ≤ x
  · rw [Real.norm_eq_abs, abs_of_nonneg hx, max_eq_left hx]
    ring
  · have hx' : x ≤ 0 := le_of_not_ge hx
    rw [Real.norm_eq_abs, abs_of_nonpos hx', max_eq_right hx']
    ring

theorem contDiff_smoothPositivePart : ContDiff ℝ 2 smoothPositivePart := by
  unfold smoothPositivePart
  exact ((contDiff_id.pow 5).add
    (contDiff_two_norm_rpow_real (p := 5) (by norm_num))).div_const 2

theorem smoothPositivePart_nonneg (x : ℝ) : 0 ≤ smoothPositivePart x := by
  rw [smoothPositivePart_eq_max]
  positivity

theorem smoothPositivePart_pos_iff (x : ℝ) :
    0 < smoothPositivePart x ↔ 0 < x := by
  rw [smoothPositivePart_eq_max]
  constructor
  · intro h
    have hm : 0 < max x 0 :=
      (Odd.pow_pos_iff (R := ℝ) (a := max x 0) (by norm_num : Odd 5)).mp h
    exact (lt_max_iff.mp hm).resolve_right (lt_irrefl 0)
  · intro hx
    have hm : 0 < max x 0 := lt_of_lt_of_le hx (le_max_left _ _)
    positivity

theorem monotone_smoothPositivePart : Monotone smoothPositivePart := by
  intro x y hxy
  rw [smoothPositivePart_eq_max, smoothPositivePart_eq_max]
  exact pow_le_pow_left₀ (le_max_right x 0) (max_le_max hxy le_rfl) 5

theorem convexOn_smoothPositivePart : ConvexOn ℝ Set.univ smoothPositivePart := by
  have hmax : ConvexOn ℝ Set.univ (fun x : ℝ ↦ max x 0) := by
    refine ⟨convex_univ, ?_⟩
    intro x _ y _ a b ha hb _
    simp only [smul_eq_mul]
    apply max_le
    · exact add_le_add (mul_le_mul_of_nonneg_left (le_max_left x 0) ha)
        (mul_le_mul_of_nonneg_left (le_max_left y 0) hb)
    · positivity
  have hpow : ConvexOn ℝ Set.univ (fun x : ℝ ↦ (max x 0) ^ 5) :=
    hmax.pow (fun x _ ↦ le_max_right x 0) 5
  exact hpow.congr fun x _ ↦ (smoothPositivePart_eq_max x).symm

theorem deriv_smoothPositivePart_nonneg (x : ℝ) :
    0 ≤ deriv smoothPositivePart x :=
  monotone_smoothPositivePart.deriv_nonneg

theorem iteratedDeriv_two_smoothPositivePart_nonneg (x : ℝ) :
    0 ≤ iteratedDeriv 2 smoothPositivePart x := by
  have hmono : Monotone (deriv smoothPositivePart) := by
    intro a b hab
    exact convexOn_smoothPositivePart.monotoneOn_deriv
      (fun _ _ ↦ contDiff_smoothPositivePart.differentiable two_ne_zero _)
      (Set.mem_univ a) (Set.mem_univ b) hab
  rw [show iteratedDeriv 2 smoothPositivePart = deriv (deriv smoothPositivePart) by
    rw [show (2 : ℕ) = 1 + 1 by norm_num, iteratedDeriv_succ, iteratedDeriv_one]]
  exact hmono.deriv_nonneg

/-- The second directional derivative along an affine real line agrees with the second
Fréchet derivative.  This local version is needed because `log ‖f‖` is smooth only away from
the zeros of `f`. -/
theorem iteratedDeriv_two_line_at {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : E → ℝ} {x : E} (hF : ContDiffAt ℝ 2 F x) (v : E) :
    iteratedDeriv 2 (fun t : ℝ ↦ F (x + t • v)) 0 =
      iteratedFDeriv ℝ 2 F x ![v, v] := by
  let q : ℝ → ℝ := fun t ↦ F (x + t • v)
  have hline : Tendsto (fun t : ℝ ↦ x + t • v) (nhds 0) (nhds x) := by
    exact (show Continuous (fun t : ℝ ↦ x + t • v) by fun_prop).tendsto' 0 x (by simp)
  have hev : ∀ᶠ t : ℝ in nhds (0 : ℝ), ContDiffAt ℝ 2 F (x + t • v) :=
    hline.eventually (hF.eventually (by norm_num))
  have hderiv : deriv q =ᶠ[nhds 0]
      (fun t ↦ fderiv ℝ F (x + t • v) v) := by
    filter_upwards [hev] with t ht
    exact ht.differentiableAt two_ne_zero |>.deriv_comp_add_smul
  rw [show iteratedDeriv 2 q 0 = deriv (deriv q) 0 by
    rw [show (2 : ℕ) = 1 + 1 by norm_num, iteratedDeriv_succ, iteratedDeriv_one]]
  rw [hderiv.deriv_eq]
  have hF' : ContDiffAt ℝ ((1 : ℕ∞) + 1) F x := by
    convert hF using 1
    norm_num
  have hF₀ : ContDiffAt ℝ ((1 : ℕ∞) + 1) F (x + (0 : ℝ) • v) := by
    simpa using hF'
  have hsecond := hF₀.deriv_fderiv_add_smul (n := 1) (y := v) (t := (0 : ℝ))
  simp only [zero_smul, add_zero] at hsecond
  have hsecond' : deriv (fun t : ℝ ↦ fderiv ℝ F (x + t • v) v) 0 =
      iteratedFDeriv ℝ 2 F x (fun _ ↦ v) := by
    simpa only [iteratedFDeriv_one_apply, Nat.reduceAdd] using hsecond
  rw [hsecond']
  congr 1
  funext i
  fin_cases i <;> rfl

/-- The preceding affine-line identity at an arbitrary parameter value. -/
theorem iteratedDeriv_two_affine_line_at
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : E → ℝ} {x v : E} {t : ℝ} (hF : ContDiffAt ℝ 2 F (x + t • v)) :
    iteratedDeriv 2 (fun s : ℝ ↦ F (x + s • v)) t =
      iteratedFDeriv ℝ 2 F (x + t • v) ![v, v] := by
  let q : ℝ → ℝ := fun s ↦ F (x + s • v)
  have hline : Tendsto (fun s : ℝ ↦ x + s • v) (nhds t) (nhds (x + t • v)) :=
    (show Continuous (fun s : ℝ ↦ x + s • v) by fun_prop).tendsto t
  have hev : ∀ᶠ s : ℝ in nhds t, ContDiffAt ℝ 2 F (x + s • v) :=
    hline.eventually (hF.eventually (by norm_num))
  have hderiv : deriv q =ᶠ[nhds t]
      (fun s ↦ fderiv ℝ F (x + s • v) v) := by
    filter_upwards [hev] with s hs
    exact hs.differentiableAt two_ne_zero |>.deriv_comp_add_smul
  rw [show iteratedDeriv 2 q t = deriv (deriv q) t by
    rw [show (2 : ℕ) = 1 + 1 by norm_num, iteratedDeriv_succ, iteratedDeriv_one]]
  rw [hderiv.deriv_eq]
  have hF' : ContDiffAt ℝ ((1 : ℕ∞) + 1) F (x + t • v) := by
    convert hF using 1
    norm_num
  have hsecond := hF'.deriv_fderiv_add_smul (n := 1) (x := x) (y := v) (t := t)
  have hsecond' : deriv (fun s : ℝ ↦ fderiv ℝ F (x + s • v) v) t =
      iteratedFDeriv ℝ 2 F (x + t • v) (fun _ ↦ v) := by
    simpa only [iteratedFDeriv_one_apply, Nat.reduceAdd] using hsecond
  rw [hsecond']
  congr 1
  funext i
  fin_cases i <;> rfl

/-- Chain rule for the planar Laplacian of a scalar composition. -/
theorem laplacian_comp_real_at {P : ℝ → ℝ} {g : ℂ → ℝ} {z : ℂ}
    (hP : ContDiffAt ℝ 2 P (g z)) (hg : ContDiffAt ℝ 2 g z) :
    Δ (P ∘ g) z =
      iteratedDeriv 2 P (g z) *
          ((fderiv ℝ g z 1) ^ 2 + (fderiv ℝ g z Complex.I) ^ 2) +
        deriv P (g z) * Δ g z := by
  rw [congrFun (laplacian_eq_iteratedFDeriv_complexPlane (P ∘ g)) z]
  rw [← iteratedDeriv_two_line_at (hP.comp z hg) (1 : ℂ)]
  rw [← iteratedDeriv_two_line_at (hP.comp z hg) Complex.I]
  let q₁ : ℝ → ℝ := fun t ↦ g (z + t • (1 : ℂ))
  let qI : ℝ → ℝ := fun t ↦ g (z + t • Complex.I)
  have hq₁ : ContDiffAt ℝ 2 q₁ 0 := by
    have hin : ContDiffAt ℝ 2 (fun t : ℝ ↦ z + t • (1 : ℂ)) 0 :=
      contDiffAt_const.add (contDiffAt_id.smul_const (1 : ℂ))
    have hg' : ContDiffAt ℝ 2 g ((fun t : ℝ ↦ z + t • (1 : ℂ)) 0) := by
      simpa using hg
    exact hg'.comp 0 hin
  have hqI : ContDiffAt ℝ 2 qI 0 := by
    have hin : ContDiffAt ℝ 2 (fun t : ℝ ↦ z + t • Complex.I) 0 :=
      contDiffAt_const.add (contDiffAt_id.smul_const Complex.I)
    have hg' : ContDiffAt ℝ 2 g ((fun t : ℝ ↦ z + t • Complex.I) 0) := by
      simpa using hg
    exact hg'.comp 0 hin
  have hPq₁ : ContDiffAt ℝ 2 P (q₁ 0) := by simpa [q₁] using hP
  have hPqI : ContDiffAt ℝ 2 P (qI 0) := by simpa [qI] using hP
  rw [show (fun t : ℝ ↦ (P ∘ g) (z + t • (1 : ℂ))) = P ∘ q₁ by rfl]
  rw [show (fun t : ℝ ↦ (P ∘ g) (z + t • Complex.I)) = P ∘ qI by rfl]
  rw [iteratedDeriv_comp_two hPq₁ hq₁]
  rw [iteratedDeriv_comp_two hPqI hqI]
  have hd₁ : deriv q₁ 0 = fderiv ℝ g z 1 := by
    have hg' : DifferentiableAt ℝ g (z + (0 : ℝ) • (1 : ℂ)) := by
      simpa using hg.differentiableAt two_ne_zero
    simpa only [q₁, zero_smul, add_zero] using
      hg'.deriv_comp_add_smul (x := z) (y := (1 : ℂ)) (t := (0 : ℝ))
  have hdI : deriv qI 0 = fderiv ℝ g z Complex.I := by
    have hg' : DifferentiableAt ℝ g (z + (0 : ℝ) • Complex.I) := by
      simpa using hg.differentiableAt two_ne_zero
    simpa only [qI, zero_smul, add_zero] using
      hg'.deriv_comp_add_smul (x := z) (y := Complex.I) (t := (0 : ℝ))
  have hdd₁ : iteratedDeriv 2 q₁ 0 =
      iteratedFDeriv ℝ 2 g z ![(1 : ℂ), 1] := by
    simpa only [q₁] using iteratedDeriv_two_line_at hg (1 : ℂ)
  have hddI : iteratedDeriv 2 qI 0 =
      iteratedFDeriv ℝ 2 g z ![Complex.I, Complex.I] := by
    simpa only [qI] using iteratedDeriv_two_line_at hg Complex.I
  rw [show q₁ 0 = g z by simp [q₁], show qI 0 = g z by simp [qI], hd₁, hdI,
    hdd₁, hddI]
  rw [congrFun (laplacian_eq_iteratedFDeriv_complexPlane g) z]
  ring

/-- The derivative of complex exponentiation along a real affine line. -/
theorem hasDerivAt_cexp_affine_real (w v : ℂ) (t : ℝ) :
    HasDerivAt (fun s : ℝ ↦ Complex.exp (w + (s : ℂ) * v))
      (Complex.exp (w + (t : ℂ) * v) * v) t := by
  simpa using (((hasDerivAt_id t).ofReal_comp.mul_const v).const_add w).cexp

theorem deriv_cexp_affine_real (w v : ℂ) (t : ℝ) :
    deriv (fun s : ℝ ↦ Complex.exp (w + (s : ℂ) * v)) t =
      Complex.exp (w + (t : ℂ) * v) * v :=
  (hasDerivAt_cexp_affine_real w v t).deriv

theorem iteratedDeriv_two_cexp_affine_real (w v : ℂ) (t : ℝ) :
    iteratedDeriv 2 (fun s : ℝ ↦ Complex.exp (w + (s : ℂ) * v)) t =
      Complex.exp (w + (t : ℂ) * v) * v ^ 2 := by
  rw [show iteratedDeriv 2 (fun s : ℝ ↦ Complex.exp (w + (s : ℂ) * v)) =
      deriv (deriv (fun s : ℝ ↦ Complex.exp (w + (s : ℂ) * v))) by
    rw [show (2 : ℕ) = 1 + 1 by norm_num, iteratedDeriv_succ, iteratedDeriv_one]]
  rw [show deriv (fun s : ℝ ↦ Complex.exp (w + (s : ℂ) * v)) =
      (fun s : ℝ ↦ Complex.exp (w + (s : ℂ) * v) * v) from
    funext (deriv_cexp_affine_real w v)]
  convert ((hasDerivAt_cexp_affine_real w v t).mul_const v).deriv using 1
  ring

/-- Complex exponentiation along a real affine line is `C²`.  This real-variable proof
also fixes the ambient real normed-space instance, avoiding any typeclass diamond between
the complex normed-algebra and inner-product-space structures. -/
theorem contDiff_cexp_affine_real (w v : ℂ) :
    ContDiff ℝ 2 (fun s : ℝ ↦ Complex.exp (w + (s : ℂ) * v)) := by
  change ContDiff ℝ (1 + 1) (fun s : ℝ ↦ Complex.exp (w + (s : ℂ) * v))
  rw [contDiff_succ_iff_deriv]
  refine ⟨fun t ↦ (hasDerivAt_cexp_affine_real w v t).differentiableAt, by simp, ?_⟩
  rw [show deriv (fun s : ℝ ↦ Complex.exp (w + (s : ℂ) * v)) =
      (fun s : ℝ ↦ Complex.exp (w + (s : ℂ) * v) * v) from
    funext (deriv_cexp_affine_real w v)]
  rw [contDiff_one_iff_deriv]
  refine ⟨fun t ↦ ((hasDerivAt_cexp_affine_real w v t).mul_const v).differentiableAt, ?_⟩
  rw [show deriv (fun s : ℝ ↦ Complex.exp (w + (s : ℂ) * v) * v) =
      (fun s : ℝ ↦ Complex.exp (w + (s : ℂ) * v) * v * v) from
    funext fun t ↦ ((hasDerivAt_cexp_affine_real w v t).mul_const v).deriv]
  have hinner : Continuous (fun s : ℝ ↦ w + (s : ℂ) * v) :=
    continuous_const.add ((Complex.continuous_ofReal.comp continuous_id).mul continuous_const)
  exact ((Complex.continuous_exp.comp hinner).mul continuous_const).mul continuous_const

/-- The Euclidean trace of a symmetric real-bilinear form scales by `‖a‖²` under
multiplication of both orthonormal basis vectors by a complex number `a`. -/
theorem symmetric_bilinear_complex_trace
    (B : ℂ →ₗ[ℝ] ℂ →ₗ[ℝ] ℝ) (hB : ∀ x y, B x y = B y x) (a : ℂ) :
    B a a + B (a * Complex.I) (a * Complex.I) =
      ‖a‖ ^ 2 * (B 1 1 + B Complex.I Complex.I) := by
  have ha : a = a.re • (1 : ℂ) + a.im • Complex.I := by
    apply Complex.ext <;> simp
  have haI : a * Complex.I = (-a.im) • (1 : ℂ) + a.re • Complex.I := by
    apply Complex.ext <;> simp
  rw [haI, ha]
  simp only [map_add, map_smul, smul_eq_mul]
  simp
  rw [hB Complex.I 1]
  rw [Complex.sq_norm, Complex.normSq_apply]
  ring

/-- The conformal covariance formula for the planar Laplacian under the exponential map.
This is the analytic bridge from polar coordinates to the flat logarithmic cylinder. -/
theorem laplacian_comp_cexp_at {u : ℂ → ℝ} {w : ℂ}
    (hu : ContDiffAt ℝ 2 u (Complex.exp w)) :
    Δ (u ∘ Complex.exp) w = ‖Complex.exp w‖ ^ 2 * Δ u (Complex.exp w) := by
  have hexp : ContDiffAt ℝ 2 Complex.exp w :=
    (Complex.contDiff_exp (𝕜 := ℝ)).contDiffAt
  rw [congrFun (laplacian_eq_iteratedFDeriv_complexPlane (u ∘ Complex.exp)) w]
  rw [← iteratedDeriv_two_line_at (hu.comp w hexp) (1 : ℂ)]
  rw [← iteratedDeriv_two_line_at (hu.comp w hexp) Complex.I]
  let q₁ : ℝ → ℂ := fun t ↦ Complex.exp (w + (t : ℂ) * (1 : ℂ))
  let qI : ℝ → ℂ := fun t ↦ Complex.exp (w + (t : ℂ) * Complex.I)
  have hq₁ : ContDiffAt ℝ 2 q₁ 0 := by
    exact (contDiff_cexp_affine_real w 1).contDiffAt
  have hqI : ContDiffAt ℝ 2 qI 0 := by
    exact (contDiff_cexp_affine_real w Complex.I).contDiffAt
  have huq₁ : ContDiffAt ℝ 2 u (q₁ 0) := by simpa [q₁] using hu
  have huqI : ContDiffAt ℝ 2 u (qI 0) := by simpa [qI] using hu
  rw [show (fun t : ℝ ↦ (u ∘ Complex.exp) (w + t • (1 : ℂ))) = u ∘ q₁ by
    funext t
    simp [q₁]]
  rw [show (fun t : ℝ ↦ (u ∘ Complex.exp) (w + t • Complex.I)) = u ∘ qI by
    funext t
    simp [qI]]
  rw [iteratedDeriv_vcomp_two huq₁ hq₁]
  rw [iteratedDeriv_vcomp_two huqI hqI]
  rw [deriv_cexp_affine_real w 1 0, deriv_cexp_affine_real w Complex.I 0]
  rw [iteratedDeriv_two_cexp_affine_real w 1 0,
    iteratedDeriv_two_cexp_affine_real w Complex.I 0]
  simp only [q₁, qI, Complex.ofReal_zero, zero_mul, add_zero, mul_one, one_pow,
    Complex.I_sq]
  rw [show Complex.exp w * -1 = -(Complex.exp w) by ring, map_neg]
  ring_nf
  have hv₁ : (fun _ : Fin 2 ↦ Complex.exp w) = ![Complex.exp w, Complex.exp w] := by
    funext i
    fin_cases i <;> rfl
  have hvI : (fun _ : Fin 2 ↦ Complex.exp w * Complex.I) =
      ![Complex.exp w * Complex.I, Complex.exp w * Complex.I] := by
    funext i
    fin_cases i <;> rfl
  rw [hv₁, hvI]
  rw [← bilinearIteratedFDerivTwo_eq_iteratedFDeriv u (Complex.exp w)
      (Complex.exp w) (Complex.exp w)]
  rw [← bilinearIteratedFDerivTwo_eq_iteratedFDeriv u (Complex.exp w)
      (Complex.exp w * Complex.I) (Complex.exp w * Complex.I)]
  have hsym : ∀ x y, bilinearIteratedFDerivTwo ℝ u (Complex.exp w) x y =
      bilinearIteratedFDerivTwo ℝ u (Complex.exp w) y x := by
    intro x y
    simpa [bilinearIteratedFDerivTwo] using
      (hu.isSymmSndFDerivAt (by simp)).eq x y
  rw [symmetric_bilinear_complex_trace
    (bilinearIteratedFDerivTwo ℝ u (Complex.exp w)) hsym]
  rw [congrFun (laplacian_eq_iteratedFDeriv_complexPlane u) (Complex.exp w)]
  rw [← bilinearIteratedFDerivTwo_eq_iteratedFDeriv u (Complex.exp w) 1 1]
  rw [← bilinearIteratedFDerivTwo_eq_iteratedFDeriv u (Complex.exp w)
    Complex.I Complex.I]

/-- A globally `C²` level made from the harmonic function `log ‖f‖` off the zero set.
Near a zero of `f` it is identically zero, so the definition remains smooth there. -/
noncomputable def harmonicLogarithmicLevel (f : ℂ → ℂ) (z : ℂ) : ℝ :=
  smoothPositivePart (Real.log ‖f z‖)

theorem harmonicLogarithmicLevel_pos_iff (f : ℂ → ℂ) (z : ℂ) :
    0 < harmonicLogarithmicLevel f z ↔ 1 < ‖f z‖ := by
  rw [harmonicLogarithmicLevel, smoothPositivePart_pos_iff,
    Real.log_pos_iff (norm_nonneg _)]

theorem positiveSet_harmonicLogarithmicLevel (f : ℂ → ℂ) :
    {z | 0 < harmonicLogarithmicLevel f z} = exceptionalSet f 1 := by
  ext z
  exact harmonicLogarithmicLevel_pos_iff f z

theorem contDiff_harmonicLogarithmicLevel {f : ℂ → ℂ} (hf : IsEntire f) :
    ContDiff ℝ 2 (harmonicLogarithmicLevel f) := by
  rw [contDiff_iff_contDiffAt]
  intro z
  by_cases hz : f z = 0
  · have htend : Tendsto (fun y ↦ ‖f y‖) (nhds z) (nhds 0) :=
      hf.continuous.norm.tendsto' z 0 (by simp [hz])
    have hev : ∀ᶠ y in nhds z, ‖f y‖ < 1 := htend.eventually_lt_const one_pos
    have heq : harmonicLogarithmicLevel f =ᶠ[nhds z] (fun _ ↦ 0) := by
      filter_upwards [hev] with y hy
      unfold harmonicLogarithmicLevel
      rw [smoothPositivePart_eq_max, max_eq_right
        (Real.log_nonpos (norm_nonneg _) hy.le)]
      norm_num
    exact contDiffAt_const.congr_of_eventuallyEq heq
  · have hlog := (hf.analyticAt z).harmonicAt_log_norm hz
    exact contDiff_smoothPositivePart.contDiffAt.comp z hlog.1

/-- The smooth harmonic logarithmic level is subharmonic in the classical differential sense. -/
theorem laplacian_harmonicLogarithmicLevel_nonneg {f : ℂ → ℂ} (hf : IsEntire f)
    (z : ℂ) : 0 ≤ Δ (harmonicLogarithmicLevel f) z := by
  by_cases hz : f z = 0
  · have htend : Tendsto (fun y ↦ ‖f y‖) (nhds z) (nhds 0) :=
      hf.continuous.norm.tendsto' z 0 (by simp [hz])
    have hev : ∀ᶠ y in nhds z, ‖f y‖ < 1 := htend.eventually_lt_const one_pos
    have heq : harmonicLogarithmicLevel f =ᶠ[nhds z] (fun _ ↦ 0) := by
      filter_upwards [hev] with y hy
      unfold harmonicLogarithmicLevel
      rw [smoothPositivePart_eq_max, max_eq_right
        (Real.log_nonpos (norm_nonneg _) hy.le)]
      norm_num
    have hlap : Δ (harmonicLogarithmicLevel f) z = 0 := by
      simpa using (laplacian_congr_nhds heq).eq_of_nhds
    rw [hlap]
  · have hlog := (hf.analyticAt z).harmonicAt_log_norm hz
    change 0 ≤ Δ (smoothPositivePart ∘ (fun w : ℂ ↦ Real.log ‖f w‖)) z
    rw [laplacian_comp_real_at contDiff_smoothPositivePart.contDiffAt hlog.1]
    have hzero : Δ (fun w : ℂ ↦ Real.log ‖f w‖) z = 0 := hlog.2.eq_of_nhds
    rw [hzero, mul_zero, add_zero]
    exact mul_nonneg (iteratedDeriv_two_smoothPositivePart_nonneg _)
      (add_nonneg (sq_nonneg _) (sq_nonneg _))

/-- Camera's smooth logarithmic level pulled back to the logarithmic plane.  Its real
coordinate is `log r` and its imaginary coordinate is the polar angle. -/
noncomputable def logPolarLevel (f : ℂ → ℂ) : ℂ → ℝ :=
  harmonicLogarithmicLevel f ∘ Complex.exp

theorem contDiff_logPolarLevel {f : ℂ → ℂ} (hf : IsEntire f) :
    ContDiff ℝ 2 (logPolarLevel f) := by
  exact (contDiff_harmonicLogarithmicLevel hf).comp (Complex.contDiff_exp (𝕜 := ℝ))

/-- In logarithmic polar coordinates the smooth level remains subharmonic.  This is
the pointwise differential inequality `Uₓₓ + Uₜₜ ≥ 0` on the cylinder. -/
theorem laplacian_logPolarLevel_nonneg {f : ℂ → ℂ} (hf : IsEntire f) (w : ℂ) :
    0 ≤ Δ (logPolarLevel f) w := by
  unfold logPolarLevel
  rw [laplacian_comp_cexp_at (contDiff_harmonicLogarithmicLevel hf).contDiffAt]
  exact mul_nonneg (sq_nonneg _) (laplacian_harmonicLogarithmicLevel_nonneg hf _)

theorem logPolarLevel_pos_iff (f : ℂ → ℂ) (w : ℂ) :
    0 < logPolarLevel f w ↔ 1 < ‖f (Complex.exp w)‖ := by
  exact harmonicLogarithmicLevel_pos_iff f (Complex.exp w)

/-- The point `x + iθ` of the logarithmic plane. -/
noncomputable def logPolarPoint (x θ : ℝ) : ℂ :=
  (x : ℂ) + (θ : ℂ) * Complex.I

theorem exp_logPolarPoint (x θ : ℝ) :
    Complex.exp (logPolarPoint x θ) = polarPoint (Real.exp x) θ := by
  simp [logPolarPoint, polarPoint, Complex.exp_add, Complex.exp_mul_I]

/-- A horizontal angular slice of the logarithmic-polar level. -/
noncomputable def logPolarSlice (f : ℂ → ℂ) (x θ : ℝ) : ℝ :=
  logPolarLevel f (logPolarPoint x θ)

theorem logPolarSlice_pos_iff (f : ℂ → ℂ) (x θ : ℝ) :
    0 < logPolarSlice f x θ ↔
      polarPoint (Real.exp x) θ ∈ exceptionalSet f 1 := by
  rw [logPolarSlice, logPolarLevel_pos_iff, exp_logPolarPoint]
  rfl

/-- The positive angular support of the cylindrical slice has exactly the angular section
whose measure enters the polar area formula. -/
theorem positive_logPolarSlice_set (f : ℂ → ℂ) (x : ℝ) :
    {θ | θ ∈ Set.Ioo (-Real.pi) Real.pi ∧ 0 < logPolarSlice f x θ} =
      angularSection (exceptionalSet f 1) (Real.exp x) := by
  ext θ
  simp only [angularSection, Set.mem_ofPred_eq, and_congr_right_iff]
  intro _
  exact logPolarSlice_pos_iff f x θ

theorem logPolarSlice_periodic (f : ℂ → ℂ) (x θ : ℝ) :
    logPolarSlice f x (θ + 2 * Real.pi) = logPolarSlice f x θ := by
  change harmonicLogarithmicLevel f
      (Complex.exp (logPolarPoint x (θ + 2 * Real.pi))) =
    harmonicLogarithmicLevel f (Complex.exp (logPolarPoint x θ))
  rw [exp_logPolarPoint, exp_logPolarPoint]
  apply congrArg
  simp [polarPoint]

theorem contDiff_logPolarSlice_fst {f : ℂ → ℂ} (hf : IsEntire f) (θ : ℝ) :
    ContDiff ℝ 2 (fun x : ℝ ↦ logPolarSlice f x θ) := by
  have hin : ContDiff ℝ 2 (fun x : ℝ ↦ (θ : ℂ) * Complex.I + x • (1 : ℂ)) :=
    contDiff_const.add (contDiff_id.smul_const (1 : ℂ))
  have h := (contDiff_logPolarLevel hf).comp hin
  convert h using 1
  funext x
  simp [logPolarSlice, logPolarPoint, add_comm]

theorem contDiff_logPolarSlice_snd {f : ℂ → ℂ} (hf : IsEntire f) (x : ℝ) :
    ContDiff ℝ 2 (logPolarSlice f x) := by
  have hin : ContDiff ℝ 2 (fun θ : ℝ ↦ (x : ℂ) + θ • Complex.I) :=
    contDiff_const.add (contDiff_id.smul_const Complex.I)
  exact (contDiff_logPolarLevel hf).comp hin

/-- The coordinate second derivatives of the cylindrical slice sum to its planar
Laplacian. -/
theorem logPolarSlice_second_derivatives_add {f : ℂ → ℂ}
    (hf : IsEntire f) (x θ : ℝ) :
    iteratedDeriv 2 (fun s : ℝ ↦ logPolarSlice f s θ) x +
        iteratedDeriv 2 (logPolarSlice f x) θ =
      Δ (logPolarLevel f) (logPolarPoint x θ) := by
  rw [congrFun (laplacian_eq_iteratedFDeriv_complexPlane (logPolarLevel f))
    (logPolarPoint x θ)]
  rw [show (fun s : ℝ ↦ logPolarSlice f s θ) =
      (fun s : ℝ ↦ logPolarLevel f ((θ : ℂ) * Complex.I + s • (1 : ℂ))) by
    funext s
    simp [logPolarSlice, logPolarPoint, add_comm]]
  rw [show logPolarSlice f x =
      (fun s : ℝ ↦ logPolarLevel f ((x : ℂ) + s • Complex.I)) by
    funext s
    simp [logPolarSlice, logPolarPoint]]
  have hx := iteratedDeriv_two_affine_line_at
    (F := logPolarLevel f) (x := (θ : ℂ) * Complex.I) (v := (1 : ℂ)) (t := x)
    (contDiff_logPolarLevel hf).contDiffAt
  have hx' : iteratedDeriv 2
      (fun s : ℝ ↦ logPolarLevel f ((θ : ℂ) * Complex.I + s • (1 : ℂ))) x =
      iteratedFDeriv ℝ 2 (logPolarLevel f) (logPolarPoint x θ) ![(1 : ℂ), 1] := by
    simpa [logPolarPoint, add_comm] using hx
  have hθ := iteratedDeriv_two_affine_line_at
    (F := logPolarLevel f) (x := (x : ℂ)) (v := Complex.I) (t := θ)
    (contDiff_logPolarLevel hf).contDiffAt
  have hθ' : iteratedDeriv 2
      (fun s : ℝ ↦ logPolarLevel f ((x : ℂ) + s • Complex.I)) θ =
      iteratedFDeriv ℝ 2 (logPolarLevel f) (logPolarPoint x θ)
        ![Complex.I, Complex.I] := by
    simpa [logPolarPoint] using hθ
  rw [hx', hθ']

/-- The pointwise cylindrical differential inequality used in the energy argument. -/
theorem logPolarSlice_second_derivatives_add_nonneg {f : ℂ → ℂ}
    (hf : IsEntire f) (x θ : ℝ) :
    0 ≤ iteratedDeriv 2 (fun s : ℝ ↦ logPolarSlice f s θ) x +
        iteratedDeriv 2 (logPolarSlice f x) θ := by
  rw [logPolarSlice_second_derivatives_add hf]
  exact laplacian_logPolarLevel_nonneg hf _

/-- A compact-parameter differentiation-under-the-integral lemma.  Joint continuity supplies
the local uniform derivative bound automatically by compactness of a rectangle. -/
theorem hasDerivAt_intervalIntegral_of_continuous_partial
    {F F' : ℝ → ℝ → ℝ} {a b x₀ : ℝ}
    (hF : Continuous (Function.uncurry F))
    (hF' : Continuous (Function.uncurry F'))
    (hdiff : ∀ x t, HasDerivAt (fun y ↦ F y t) (F' x t) x) :
    HasDerivAt (fun x ↦ ∫ t in a..b, F x t) (∫ t in a..b, F' x₀ t) x₀ := by
  let s : Set ℝ := Set.Ioo (x₀ - 1) (x₀ + 1)
  let K : Set (ℝ × ℝ) := Set.Icc (x₀ - 1) (x₀ + 1) ×ˢ Set.uIcc a b
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod isCompact_uIcc).exists_bound_of_continuousOn
    hF'.continuousOn
  have hs : s ∈ nhds x₀ := by
    exact Ioo_mem_nhds (by linarith) (by linarith)
  have hF_meas : ∀ᶠ x in nhds x₀,
      AEStronglyMeasurable (F x) (volume.restrict (Set.uIoc a b)) := by
    filter_upwards with x
    exact (hF.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable.restrict
  have hF_int : IntervalIntegrable (F x₀) volume a b :=
    (hF.comp (continuous_const.prodMk continuous_id)).intervalIntegrable _ _
  have hF'_meas : AEStronglyMeasurable (F' x₀) (volume.restrict (Set.uIoc a b)) :=
    (hF'.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable.restrict
  have hbound : ∀ᵐ t ∂volume, t ∈ Set.uIoc a b →
      ∀ x ∈ s, ‖F' x t‖ ≤ C := by
    filter_upwards with t
    intro ht x hx
    apply hC (x, t)
    exact ⟨⟨hx.1.le, hx.2.le⟩, Set.uIoc_subset_uIcc ht⟩
  have hdiff' : ∀ᵐ t ∂volume, t ∈ Set.uIoc a b →
      ∀ x ∈ s, HasDerivAt (fun y ↦ F y t) (F' x t) x := by
    filter_upwards with t
    exact fun _ x _ ↦ hdiff x t
  exact (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := F) (F' := F') (bound := fun _ ↦ C) hs hF_meas hF_int hF'_meas hbound
      intervalIntegrable_const hdiff').2

/-- The square energy of a real-valued function on a horizontal cylinder slice. -/
noncomputable def cylindricalSquareEnergy (U : ℝ → ℝ → ℝ) (a b x : ℝ) : ℝ :=
  ∫ t in a..b, U x t ^ 2

theorem hasDerivAt_cylindricalSquareEnergy {U Ux : ℝ → ℝ → ℝ}
    (hU : Continuous (Function.uncurry U))
    (hUx : Continuous (Function.uncurry Ux))
    (hdiff : ∀ x t, HasDerivAt (fun y ↦ U y t) (Ux x t) x)
    (a b x : ℝ) :
    HasDerivAt (cylindricalSquareEnergy U a b)
      (∫ t in a..b, 2 * (U x t * Ux x t)) x := by
  apply hasDerivAt_intervalIntegral_of_continuous_partial
      (F := fun y t ↦ U y t ^ 2)
      (F' := fun y t ↦ 2 * (U y t * Ux y t))
  · exact hU.pow 2
  · exact continuous_const.mul (hU.mul hUx)
  · intro y t
    have hu := hdiff y t
    convert hu.pow 2 using 1 <;>
      first | with_reducible_and_instances rfl | ring

theorem iteratedDeriv_two_cylindricalSquareEnergy {U Ux Uxx : ℝ → ℝ → ℝ}
    (hU : Continuous (Function.uncurry U))
    (hUx : Continuous (Function.uncurry Ux))
    (hUxx : Continuous (Function.uncurry Uxx))
    (hdiff : ∀ x t, HasDerivAt (fun y ↦ U y t) (Ux x t) x)
    (hdiffx : ∀ x t, HasDerivAt (fun y ↦ Ux y t) (Uxx x t) x)
    (a b x : ℝ) :
    iteratedDeriv 2 (cylindricalSquareEnergy U a b) x =
      ∫ t in a..b, 2 * (Ux x t ^ 2 + U x t * Uxx x t) := by
  rw [show iteratedDeriv 2 (cylindricalSquareEnergy U a b) x =
      deriv (deriv (cylindricalSquareEnergy U a b)) x by
    rw [show (2 : ℕ) = 1 + 1 by norm_num, iteratedDeriv_succ, iteratedDeriv_one]]
  rw [show deriv (cylindricalSquareEnergy U a b) =
      (fun y ↦ ∫ t in a..b, 2 * (U y t * Ux y t)) from
    funext fun y ↦ (hasDerivAt_cylindricalSquareEnergy hU hUx hdiff a b y).deriv]
  apply HasDerivAt.deriv
  apply hasDerivAt_intervalIntegral_of_continuous_partial
      (F := fun y t ↦ 2 * (U y t * Ux y t))
      (F' := fun y t ↦ 2 * (Ux y t ^ 2 + U y t * Uxx y t))
  · exact continuous_const.mul (hU.mul hUx)
  · exact continuous_const.mul ((hUx.pow 2).add (hU.mul hUxx))
  · intro y t
    simpa [pow_two] using ((hdiff y t).mul (hdiffx y t)).const_mul (2 : ℝ)

/-- Periodic integration by parts in the exact form needed for the angular energy. -/
theorem intervalIntegral_mul_second_eq_neg_sq
    {u u' u'' : ℝ → ℝ} {a b : ℝ}
    (hu : ∀ t, HasDerivAt u (u' t) t)
    (hu' : ∀ t, HasDerivAt u' (u'' t) t)
    (hu'cont : Continuous u') (hu''cont : Continuous u'')
    (hboundary : u b * u' b = u a * u' a) :
    (∫ t in a..b, u t * u'' t) = -(∫ t in a..b, u' t ^ 2) := by
  have h := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (a := a) (b := b) (u := u) (v := u') (u' := u') (v' := u'')
    (fun t _ ↦ hu t) (fun t _ ↦ hu' t)
    (hu'cont.intervalIntegrable _ _) (hu''cont.intervalIntegrable _ _)
  rw [hboundary, sub_self, zero_sub] at h
  simpa only [pow_two] using h

/-- The central Carleman energy inequality.  A nonnegative subharmonic cylindrical function
has square-energy curvature at least twice its full Dirichlet energy. -/
theorem cylindricalSquareEnergy_second_deriv_ge_dirichlet
    {U Ux Uxx Ut Utt : ℝ → ℝ → ℝ}
    (hU : Continuous (Function.uncurry U))
    (hUx : Continuous (Function.uncurry Ux))
    (hUxx : Continuous (Function.uncurry Uxx))
    (hUt : Continuous (Function.uncurry Ut))
    (hUtt : Continuous (Function.uncurry Utt))
    (hdiff : ∀ x t, HasDerivAt (fun y ↦ U y t) (Ux x t) x)
    (hdiffx : ∀ x t, HasDerivAt (fun y ↦ Ux y t) (Uxx x t) x)
    (hdifft : ∀ x t, HasDerivAt (U x) (Ut x t) t)
    (hdifftt : ∀ x t, HasDerivAt (Ut x) (Utt x t) t)
    (hU_nonneg : ∀ x t, 0 ≤ U x t)
    (hsubharmonic : ∀ x t, 0 ≤ Uxx x t + Utt x t)
    {a b x : ℝ} (hab : a ≤ b)
    (hboundary : U x b * Ut x b = U x a * Ut x a) :
    2 * ((∫ t in a..b, Ux x t ^ 2) + ∫ t in a..b, Ut x t ^ 2) ≤
      iteratedDeriv 2 (cylindricalSquareEnergy U a b) x := by
  have hU_x : Continuous (U x) :=
    hU.comp (continuous_const.prodMk continuous_id)
  have hUx_x : Continuous (Ux x) :=
    hUx.comp (continuous_const.prodMk continuous_id)
  have hUxx_x : Continuous (Uxx x) :=
    hUxx.comp (continuous_const.prodMk continuous_id)
  have hUt_x : Continuous (Ut x) :=
    hUt.comp (continuous_const.prodMk continuous_id)
  have hUtt_x : Continuous (Utt x) :=
    hUtt.comp (continuous_const.prodMk continuous_id)
  have hibp : (∫ t in a..b, U x t * Utt x t) =
      -(∫ t in a..b, Ut x t ^ 2) :=
    intervalIntegral_mul_second_eq_neg_sq (hdifft x) (hdifftt x)
      hUt_x hUtt_x hboundary
  have hneg_int : IntervalIntegrable (fun t ↦ -(U x t * Utt x t)) volume a b :=
    (hU_x.mul hUtt_x).neg.intervalIntegrable _ _
  have hxx_int : IntervalIntegrable (fun t ↦ U x t * Uxx x t) volume a b :=
    (hU_x.mul hUxx_x).intervalIntegrable _ _
  have hmono : (∫ t in a..b, -(U x t * Utt x t)) ≤
      ∫ t in a..b, U x t * Uxx x t := by
    apply intervalIntegral.integral_mono_on hab hneg_int hxx_int
    intro t _
    have hmul := mul_nonneg (hU_nonneg x t) (hsubharmonic x t)
    nlinarith
  have ht_le_hxx : (∫ t in a..b, Ut x t ^ 2) ≤
      ∫ t in a..b, U x t * Uxx x t := by
    rw [intervalIntegral.integral_neg, hibp] at hmono
    simpa only [neg_neg] using hmono
  rw [iteratedDeriv_two_cylindricalSquareEnergy hU hUx hUxx hdiff hdiffx]
  have hUx2 : IntervalIntegrable (fun t ↦ Ux x t ^ 2) volume a b :=
    (hUx_x.pow 2).intervalIntegrable _ _
  have hUUxx : IntervalIntegrable (fun t ↦ U x t * Uxx x t) volume a b :=
    (hU_x.mul hUxx_x).intervalIntegrable _ _
  rw [intervalIntegral.integral_const_mul]
  rw [intervalIntegral.integral_add hUx2 hUUxx]
  exact mul_le_mul_of_nonneg_left (add_le_add le_rfl ht_le_hxx) (by norm_num)

/-! ### Instantiation of the cylinder energy inequality -/

noncomputable def logPolarX (f : ℂ → ℂ) (x θ : ℝ) : ℝ :=
  fderiv ℝ (logPolarLevel f) (logPolarPoint x θ) 1

noncomputable def logPolarTheta (f : ℂ → ℂ) (x θ : ℝ) : ℝ :=
  fderiv ℝ (logPolarLevel f) (logPolarPoint x θ) Complex.I

noncomputable def logPolarXX (f : ℂ → ℂ) (x θ : ℝ) : ℝ :=
  iteratedFDeriv ℝ 2 (logPolarLevel f) (logPolarPoint x θ) ![(1 : ℂ), 1]

noncomputable def logPolarThetaTheta (f : ℂ → ℂ) (x θ : ℝ) : ℝ :=
  iteratedFDeriv ℝ 2 (logPolarLevel f) (logPolarPoint x θ) ![Complex.I, Complex.I]

theorem continuous_logPolarPoint_uncurry :
    Continuous (Function.uncurry logPolarPoint) := by
  have h : Continuous (fun p : ℝ × ℝ ↦
      p.1 • (1 : ℂ) + p.2 • Complex.I) :=
    (continuous_fst.smul continuous_const).add (continuous_snd.smul continuous_const)
  convert h using 1
  funext p
  dsimp only [Function.uncurry]
  simp [logPolarPoint]

theorem continuous_logPolarX {f : ℂ → ℂ} (hf : IsEntire f) :
    Continuous (Function.uncurry (logPolarX f)) := by
  unfold logPolarX Function.uncurry
  exact ((contDiff_logPolarLevel hf).continuous_fderiv (by norm_num) |>.comp
    continuous_logPolarPoint_uncurry).clm_apply continuous_const

theorem continuous_logPolarTheta {f : ℂ → ℂ} (hf : IsEntire f) :
    Continuous (Function.uncurry (logPolarTheta f)) := by
  unfold logPolarTheta Function.uncurry
  exact ((contDiff_logPolarLevel hf).continuous_fderiv (by norm_num) |>.comp
    continuous_logPolarPoint_uncurry).clm_apply continuous_const

theorem continuous_logPolarXX {f : ℂ → ℂ} (hf : IsEntire f) :
    Continuous (Function.uncurry (logPolarXX f)) := by
  unfold logPolarXX Function.uncurry
  have hi : Continuous (fun p : ℝ × ℝ ↦
      iteratedFDeriv ℝ 2 (logPolarLevel f) (logPolarPoint p.1 p.2)) :=
    ((contDiff_logPolarLevel hf).continuous_iteratedFDeriv (by norm_num)).comp
      continuous_logPolarPoint_uncurry
  fun_prop

theorem continuous_logPolarThetaTheta {f : ℂ → ℂ} (hf : IsEntire f) :
    Continuous (Function.uncurry (logPolarThetaTheta f)) := by
  unfold logPolarThetaTheta Function.uncurry
  have hi : Continuous (fun p : ℝ × ℝ ↦
      iteratedFDeriv ℝ 2 (logPolarLevel f) (logPolarPoint p.1 p.2)) :=
    ((contDiff_logPolarLevel hf).continuous_iteratedFDeriv (by norm_num)).comp
      continuous_logPolarPoint_uncurry
  fun_prop

theorem deriv_logPolarSlice_fst {f : ℂ → ℂ} (hf : IsEntire f) (x θ : ℝ) :
    deriv (fun y : ℝ ↦ logPolarSlice f y θ) x = logPolarX f x θ := by
  rw [show (fun y : ℝ ↦ logPolarSlice f y θ) =
      (fun y : ℝ ↦ logPolarLevel f ((θ : ℂ) * Complex.I + y • (1 : ℂ))) by
    funext y
    simp [logPolarSlice, logPolarPoint, add_comm]]
  have hd := (contDiff_logPolarLevel hf).differentiable (by norm_num)
    ((θ : ℂ) * Complex.I + x • (1 : ℂ)) |>.deriv_comp_add_smul
  simpa [logPolarX, logPolarPoint, add_comm] using hd

theorem deriv_logPolarSlice_snd {f : ℂ → ℂ} (hf : IsEntire f) (x θ : ℝ) :
    deriv (logPolarSlice f x) θ = logPolarTheta f x θ := by
  rw [show logPolarSlice f x =
      (fun t : ℝ ↦ logPolarLevel f ((x : ℂ) + t • Complex.I)) by
    funext t
    simp [logPolarSlice, logPolarPoint]]
  have hd := (contDiff_logPolarLevel hf).differentiable (by norm_num)
    ((x : ℂ) + θ • Complex.I) |>.deriv_comp_add_smul
  simpa [logPolarTheta, logPolarPoint] using hd

theorem hasDerivAt_logPolarSlice_fst {f : ℂ → ℂ} (hf : IsEntire f) (x θ : ℝ) :
    HasDerivAt (fun y : ℝ ↦ logPolarSlice f y θ) (logPolarX f x θ) x := by
  rw [← deriv_logPolarSlice_fst hf x θ]
  exact hasDerivAt_deriv_iff.mpr
    ((contDiff_logPolarSlice_fst hf θ).differentiable (by norm_num) x)

theorem hasDerivAt_logPolarSlice_snd {f : ℂ → ℂ} (hf : IsEntire f) (x θ : ℝ) :
    HasDerivAt (logPolarSlice f x) (logPolarTheta f x θ) θ := by
  rw [← deriv_logPolarSlice_snd hf x θ]
  exact hasDerivAt_deriv_iff.mpr
    ((contDiff_logPolarSlice_snd hf x).differentiable (by norm_num) θ)

theorem iteratedDeriv_two_logPolarSlice_fst {f : ℂ → ℂ}
    (hf : IsEntire f) (x θ : ℝ) :
    iteratedDeriv 2 (fun y : ℝ ↦ logPolarSlice f y θ) x = logPolarXX f x θ := by
  rw [show (fun y : ℝ ↦ logPolarSlice f y θ) =
      (fun y : ℝ ↦ logPolarLevel f ((θ : ℂ) * Complex.I + y • (1 : ℂ))) by
    funext y
    simp [logPolarSlice, logPolarPoint, add_comm]]
  simpa [logPolarXX, logPolarPoint, add_comm] using
    (iteratedDeriv_two_affine_line_at
      (F := logPolarLevel f) (x := (θ : ℂ) * Complex.I) (v := (1 : ℂ)) (t := x)
      (contDiff_logPolarLevel hf).contDiffAt)

theorem iteratedDeriv_two_logPolarSlice_snd {f : ℂ → ℂ}
    (hf : IsEntire f) (x θ : ℝ) :
    iteratedDeriv 2 (logPolarSlice f x) θ = logPolarThetaTheta f x θ := by
  rw [show logPolarSlice f x =
      (fun t : ℝ ↦ logPolarLevel f ((x : ℂ) + t • Complex.I)) by
    funext t
    simp [logPolarSlice, logPolarPoint]]
  simpa [logPolarThetaTheta, logPolarPoint] using
    (iteratedDeriv_two_affine_line_at
      (F := logPolarLevel f) (x := (x : ℂ)) (v := Complex.I) (t := θ)
      (contDiff_logPolarLevel hf).contDiffAt)

theorem hasDerivAt_logPolarX_fst {f : ℂ → ℂ} (hf : IsEntire f) (x θ : ℝ) :
    HasDerivAt (fun y : ℝ ↦ logPolarX f y θ) (logPolarXX f x θ) x := by
  rw [show (fun y : ℝ ↦ logPolarX f y θ) =
      deriv (fun y : ℝ ↦ logPolarSlice f y θ) from
    funext fun y ↦ (deriv_logPolarSlice_fst hf y θ).symm]
  rw [← iteratedDeriv_two_logPolarSlice_fst hf x θ]
  rw [show iteratedDeriv 2 (fun y : ℝ ↦ logPolarSlice f y θ) x =
      deriv (deriv (fun y : ℝ ↦ logPolarSlice f y θ)) x by
    rw [show (2 : ℕ) = 1 + 1 by norm_num, iteratedDeriv_succ, iteratedDeriv_one]]
  have hslice : ContDiff ℝ (1 + 1) (fun y : ℝ ↦ logPolarSlice f y θ) := by
    simpa only [one_add_one_eq_two] using contDiff_logPolarSlice_fst hf θ
  exact hasDerivAt_deriv_iff.mpr
    ((contDiff_succ_iff_deriv.mp hslice).2.2.differentiable one_ne_zero x)

theorem hasDerivAt_logPolarTheta_snd {f : ℂ → ℂ} (hf : IsEntire f) (x θ : ℝ) :
    HasDerivAt (logPolarTheta f x) (logPolarThetaTheta f x θ) θ := by
  rw [show logPolarTheta f x = deriv (logPolarSlice f x) from
    funext fun t ↦ (deriv_logPolarSlice_snd hf x t).symm]
  rw [← iteratedDeriv_two_logPolarSlice_snd hf x θ]
  rw [show iteratedDeriv 2 (logPolarSlice f x) θ =
      deriv (deriv (logPolarSlice f x)) θ by
    rw [show (2 : ℕ) = 1 + 1 by norm_num, iteratedDeriv_succ, iteratedDeriv_one]]
  have hslice : ContDiff ℝ (1 + 1) (logPolarSlice f x) := by
    simpa only [one_add_one_eq_two] using contDiff_logPolarSlice_snd hf x
  exact hasDerivAt_deriv_iff.mpr
    ((contDiff_succ_iff_deriv.mp hslice).2.2.differentiable one_ne_zero θ)

theorem deriv_periodic {u : ℝ → ℝ} {T t : ℝ}
    (hu : Differentiable ℝ u) (hp : Function.Periodic u T) :
    deriv u (t + T) = deriv u t := by
  have hinner : HasDerivAt (fun s : ℝ ↦ s + T) 1 t :=
    (hasDerivAt_id t).add_const T
  have hcomp := (hasDerivAt_deriv_iff.mpr (hu (t + T))).comp t hinner
  have hfun : u ∘ (fun s : ℝ ↦ s + T) = u := by
    funext s
    exact hp s
  rw [hfun] at hcomp
  have hcomp' : HasDerivAt u (deriv u (t + T)) t := by simpa using hcomp
  exact hcomp'.unique (hasDerivAt_deriv_iff.mpr (hu t))

theorem continuous_uncurry_logPolarSlice {f : ℂ → ℂ} (hf : IsEntire f) :
    Continuous (Function.uncurry (logPolarSlice f)) := by
  exact (contDiff_logPolarLevel hf).continuous.comp continuous_logPolarPoint_uncurry

theorem logPolarSlice_nonneg (f : ℂ → ℂ) (x θ : ℝ) :
    0 ≤ logPolarSlice f x θ := by
  exact smoothPositivePart_nonneg _

theorem logPolar_second_fields_nonneg {f : ℂ → ℂ}
    (hf : IsEntire f) (x θ : ℝ) :
    0 ≤ logPolarXX f x θ + logPolarThetaTheta f x θ := by
  rw [← iteratedDeriv_two_logPolarSlice_fst hf x θ,
    ← iteratedDeriv_two_logPolarSlice_snd hf x θ]
  exact logPolarSlice_second_derivatives_add_nonneg hf x θ

theorem logPolarSlice_endpoint_eq (f : ℂ → ℂ) (x : ℝ) :
    logPolarSlice f x Real.pi = logPolarSlice f x (-Real.pi) := by
  have hp := logPolarSlice_periodic f x (-Real.pi)
  have harg : -Real.pi + 2 * Real.pi = Real.pi := by ring
  rw [harg] at hp
  exact hp

theorem logPolarTheta_endpoint_eq {f : ℂ → ℂ} (hf : IsEntire f) (x : ℝ) :
    logPolarTheta f x Real.pi = logPolarTheta f x (-Real.pi) := by
  have hp : Function.Periodic (logPolarSlice f x) (2 * Real.pi) :=
    logPolarSlice_periodic f x
  have hd := deriv_periodic
    ((contDiff_logPolarSlice_snd hf x).differentiable (by norm_num)) hp (t := -Real.pi)
  rw [deriv_logPolarSlice_snd hf x, deriv_logPolarSlice_snd hf x] at hd
  have harg : -Real.pi + 2 * Real.pi = Real.pi := by ring
  rw [harg] at hd
  exact hd

/-- The abstract energy inequality specialized completely to Camera's logarithmic level. -/
theorem logPolar_energy_second_deriv_ge {f : ℂ → ℂ}
    (hf : IsEntire f) (x : ℝ) :
    2 * ((∫ θ in -Real.pi..Real.pi, logPolarX f x θ ^ 2) +
        ∫ θ in -Real.pi..Real.pi, logPolarTheta f x θ ^ 2) ≤
      iteratedDeriv 2
        (cylindricalSquareEnergy (logPolarSlice f) (-Real.pi) Real.pi) x := by
  apply cylindricalSquareEnergy_second_deriv_ge_dirichlet
      (hU := continuous_uncurry_logPolarSlice hf)
      (hUx := continuous_logPolarX hf)
      (hUxx := continuous_logPolarXX hf)
      (hUt := continuous_logPolarTheta hf)
      (hUtt := continuous_logPolarThetaTheta hf)
      (hdiff := hasDerivAt_logPolarSlice_fst hf)
      (hdiffx := hasDerivAt_logPolarX_fst hf)
      (hdifft := hasDerivAt_logPolarSlice_snd hf)
      (hdifftt := hasDerivAt_logPolarTheta_snd hf)
      (hU_nonneg := logPolarSlice_nonneg f)
      (hsubharmonic := logPolar_second_fields_nonneg hf)
  · linarith [Real.pi_pos]
  · rw [logPolarSlice_endpoint_eq f x, logPolarTheta_endpoint_eq hf x]

/-- Cauchy--Schwarz for a function supported on a finite-measure set, in the real square form
used by the angular-support Poincaré estimate. -/
theorem setIntegral_sq_le_measure_mul_setIntegral_sq
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {s : Set α} {g : α → ℝ}
    (hs : μ s ≠ ∞)
    (hg_meas : AEStronglyMeasurable g (μ.restrict s))
    (hg_sq : Integrable (fun x ↦ g x ^ 2) (μ.restrict s))
    (hg_nonneg : ∀ᵐ x ∂μ.restrict s, 0 ≤ g x) :
    (∫ x in s, g x ∂μ) ^ 2 ≤
      μ.real s * ∫ x in s, g x ^ 2 ∂μ := by
  let ν : Measure α := μ.restrict s
  have hν : ν Set.univ ≠ ∞ := by
    simpa [ν] using hs
  let _ : IsFiniteMeasure ν := ⟨lt_top_iff_ne_top.mpr hν⟩
  have hone : MemLp (fun _ : α ↦ (1 : ℝ)) 2 ν := memLp_const 1
  have hg : MemLp g 2 ν :=
    (memLp_two_iff_integrable_sq hg_meas).mpr hg_sq
  have hholder := integral_mul_le_Lp_mul_Lq_of_nonneg
    (μ := ν) (f := fun _ : α ↦ (1 : ℝ)) (g := g)
    Real.HolderConjugate.two_two (ae_of_all ν fun _ ↦ zero_le_one) hg_nonneg
    (by simpa using hone) (by simpa using hg)
  change (∫ x, (1 : ℝ) * g x ∂ν) ≤
      (∫ _ : α, (1 : ℝ) ^ (2 : ℝ) ∂ν) ^ (1 / (2 : ℝ)) *
        (∫ x, g x ^ (2 : ℝ) ∂ν) ^ (1 / (2 : ℝ)) at hholder
  simp only [one_mul, Real.one_rpow, integral_const, smul_eq_mul, mul_one] at hholder
  rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow] at hholder
  have hholder' : (∫ x, g x ∂ν) ≤
      √(ν.real Set.univ) * √(∫ x, g x ^ 2 ∂ν) := by
    simpa only [Real.rpow_two] using hholder
  have hmeasure_nonneg : 0 ≤ ν.real Set.univ := measureReal_nonneg
  have hgint_nonneg : 0 ≤ ∫ x, g x ^ 2 ∂ν := by
    apply integral_nonneg_of_ae
    exact ae_of_all ν fun x ↦ sq_nonneg (g x)
  have hsquare : (∫ x, g x ∂ν) ^ 2 ≤
      (√(ν.real Set.univ) * √(∫ x, g x ^ 2 ∂ν)) ^ 2 :=
    (sq_le_sq₀ (integral_nonneg_of_ae hg_nonneg)
      (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))).mpr hholder'
  rw [mul_pow, Real.sq_sqrt hmeasure_nonneg, Real.sq_sqrt hgint_nonneg] at hsquare
  simpa only [ν, measureReal_restrict_apply_univ] using hsquare

/-- If a differentiable function vanishes at one point of an interval, its absolute value
everywhere on that interval is bounded by the total variation of its derivative. -/
theorem abs_le_intervalIntegral_abs_deriv
    {u u' : ℝ → ℝ} {a b z t : ℝ}
    (hu : ∀ x, HasDerivAt u (u' x) x) (hu' : Continuous u')
    (hz : z ∈ Set.Icc a b) (hz0 : u z = 0) (ht : t ∈ Set.Icc a b) :
    |u t| ≤ ∫ x in a..b, |u' x| := by
  have hdu : deriv u = u' := funext fun x ↦ (hu x).deriv
  have habsint : IntervalIntegrable (fun x ↦ |u' x|) volume a b :=
    hu'.abs.intervalIntegrable _ _
  rcases le_total z t with hzt | htz
  · have heq := intervalIntegral.integral_deriv_eq_sub' u hdu
      (fun x _ ↦ (hu x).differentiableAt) hu'.continuousOn (a := z) (b := t)
    rw [hz0, sub_zero] at heq
    rw [← heq, ← Real.norm_eq_abs]
    calc
      ‖∫ x in z..t, u' x‖ ≤ ∫ x in z..t, ‖u' x‖ :=
        intervalIntegral.norm_integral_le_integral_norm hzt
      _ ≤ ∫ x in a..b, ‖u' x‖ := intervalIntegral.integral_mono_interval
        hz.1 hzt ht.2 (ae_of_all _ fun x ↦ norm_nonneg _) habsint
  · have heq := intervalIntegral.integral_deriv_eq_sub' u hdu
      (fun x _ ↦ (hu x).differentiableAt) hu'.continuousOn (a := t) (b := z)
    rw [hz0, zero_sub] at heq
    rw [← Real.norm_eq_abs, ← norm_neg (u t), ← heq]
    calc
      ‖∫ x in t..z, u' x‖ ≤ ∫ x in t..z, ‖u' x‖ :=
        intervalIntegral.norm_integral_le_integral_norm htz
      _ ≤ ∫ x in a..b, ‖u' x‖ := intervalIntegral.integral_mono_interval
        ht.1 htz hz.2 (ae_of_all _ fun x ↦ norm_nonneg _) habsint

/-- One-dimensional Poincaré inequality with the measure of the strict positive support as
constant.  This is the quantitative angular-width estimate used in Carleman's method. -/
theorem intervalIntegral_sq_le_supportMeasure_sq_mul_deriv_sq
    {u u' : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hucont : Continuous u) (hu'cont : Continuous u')
    (hderiv : ∀ x, HasDerivAt u (u' x) x)
    (hunonneg : ∀ x, 0 ≤ u x)
    (hproper : volume.real (Set.Ioc a b ∩ {x | 0 < u x}) < volume.real (Set.Ioc a b)) :
    (∫ x in a..b, u x ^ 2) ≤
      (volume.real (Set.Ioc a b ∩ {x | 0 < u x})) ^ 2 *
        ∫ x in a..b, u' x ^ 2 := by
  let s : Set ℝ := Set.Ioc a b ∩ {x | 0 < u x}
  have hs_sub : s ⊆ Set.Ioc a b := inter_subset_left
  have hI_top : volume (Set.Ioc a b) ≠ ∞ := by
    simp [Real.volume_Ioc]
  have hs_top : volume s ≠ ∞ :=
    ne_top_of_le_ne_top hI_top (measure_mono hs_sub)
  have hnsub : ¬ Set.Ioc a b ⊆ s := by
    intro hsub
    exact (not_le_of_gt hproper) (measureReal_mono hsub hs_top)
  obtain ⟨z, hzI, hzs⟩ := Set.not_subset.mp hnsub
  have hz0 : u z = 0 := by
    have hnpos : ¬ 0 < u z := by
      intro hp
      exact hzs ⟨hzI, hp⟩
    exact le_antisymm (le_of_not_gt hnpos) (hunonneg z)
  have hzIcc : z ∈ Set.Icc a b := ⟨hzI.1.le, hzI.2⟩
  have hzero : ∀ y ∈ Set.Ioc a b \ s, u y = 0 := by
    intro y hy
    have hnpos : ¬ 0 < u y := by
      intro hp
      exact hy.2 ⟨hy.1, hp⟩
    exact le_antisymm (le_of_not_gt hnpos) (hunonneg y)
  have hderivzero : ∀ y ∈ Set.Ioc a b \ s, u' y = 0 := by
    intro y hy
    have hlocal : IsLocalMin u y := by
      filter_upwards with q
      rw [hzero y hy]
      exact hunonneg q
    have hd0 := hlocal.deriv_eq_zero
    rw [(hderiv y).deriv] at hd0
    exact hd0
  have hs_meas : MeasurableSet s := by
    exact measurableSet_Ioc.inter (isOpen_lt continuous_const hucont).measurableSet
  have habseq : (∫ x in a..b, |u' x|) = ∫ x in s, |u' x| := by
    rw [intervalIntegral.integral_of_le hab]
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioc hs_sub
    intro y hy
    rw [hderivzero y hy, abs_zero]
  have hderivsqeq : (∫ x in a..b, u' x ^ 2) = ∫ x in s, |u' x| ^ 2 := by
    rw [intervalIntegral.integral_of_le hab]
    calc
      (∫ x in Set.Ioc a b, u' x ^ 2) = ∫ x in Set.Ioc a b, |u' x| ^ 2 := by
        apply integral_congr_ae
        filter_upwards with y
        rw [sq_abs]
      _ = ∫ x in s, |u' x| ^ 2 := by
        apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioc hs_sub
        intro y hy
        rw [hderivzero y hy, abs_zero, zero_pow two_ne_zero]
  have hUsqeq : (∫ x in a..b, u x ^ 2) = ∫ x in s, u x ^ 2 := by
    rw [intervalIntegral.integral_of_le hab]
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioc hs_sub
    intro y hy
    rw [hzero y hy, zero_pow two_ne_zero]
  let J : ℝ := ∫ x in s, |u' x|
  have hpoint : ∀ y ∈ s, u y ^ 2 ≤ J ^ 2 := by
    intro y hy
    have hyIcc : y ∈ Set.Icc a b := ⟨hy.1.1.le, hy.1.2⟩
    have habs := abs_le_intervalIntegral_abs_deriv hderiv hu'cont hzIcc hz0 hyIcc
    rw [habseq] at habs
    exact (sq_le_sq₀ (hunonneg y) (by
      dsimp only [J]
      apply integral_nonneg_of_ae
      exact ae_of_all _ fun q ↦ abs_nonneg _)).mpr (by
        simpa [abs_of_nonneg (hunonneg y), J] using habs)
  have hUsq_int : IntegrableOn (fun y ↦ u y ^ 2) s :=
    (hucont.pow 2).integrableOn_Icc.mono_set (hs_sub.trans Set.Ioc_subset_Icc_self)
  have hconst_int : IntegrableOn (fun _ : ℝ ↦ J ^ 2) s := by
    exact integrableOn_const hs_top (by simp)
  have hU_le : (∫ y in s, u y ^ 2) ≤ volume.real s * J ^ 2 := by
    calc
      (∫ y in s, u y ^ 2) ≤ ∫ _ in s, J ^ 2 := by
        apply setIntegral_mono_on hUsq_int hconst_int hs_meas
        exact hpoint
      _ = volume.real s * J ^ 2 := by rw [setIntegral_const, smul_eq_mul]
  have hJ : J ^ 2 ≤ volume.real s * ∫ x in s, |u' x| ^ 2 := by
    apply setIntegral_sq_le_measure_mul_setIntegral_sq hs_top
    · exact hu'cont.abs.aestronglyMeasurable.restrict
    · exact (hu'cont.abs.pow 2).integrableOn_Icc.mono_set
        (hs_sub.trans Set.Ioc_subset_Icc_self)
    · exact ae_of_all _ fun y ↦ abs_nonneg _
  rw [hUsqeq, hderivsqeq]
  calc
    (∫ x in s, u x ^ 2) ≤ volume.real s * J ^ 2 := hU_le
    _ ≤ volume.real s * (volume.real s * ∫ x in s, |u' x| ^ 2) :=
      mul_le_mul_of_nonneg_left hJ measureReal_nonneg
    _ = (volume.real s) ^ 2 * ∫ x in s, |u' x| ^ 2 := by ring

/-- In logarithmic polar coordinates, the measure of the strict positive support on a
period is exactly the angular width of the normalized exceptional set. -/
theorem logPolar_support_measure_eq_angularWidth (f : ℂ → ℂ) (x : ℝ) :
    volume.real (Set.Ioc (-Real.pi) Real.pi ∩
      ({θ | 0 < logPolarSlice f x θ} : Set ℝ)) =
      angularWidth (exceptionalSet f 1) (Real.exp x) := by
  have hbase : Set.Ioo (-Real.pi) Real.pi =ᵐ[volume]
      Set.Ioc (-Real.pi) Real.pi := Ioo_ae_eq_Ioc
  have hae : ∀ᵐ θ ∂volume,
      θ ∈ Set.Ioc (-Real.pi) Real.pi ∩ ({θ | 0 < logPolarSlice f x θ} : Set ℝ) ↔
      θ ∈ Set.Ioo (-Real.pi) Real.pi ∩ ({θ | 0 < logPolarSlice f x θ} : Set ℝ) := by
    filter_upwards [hbase.symm] with θ hθ
    constructor
    · rintro ⟨hI, hp⟩
      have hI' : Set.Ioc (-Real.pi) Real.pi θ := hI
      have hI'' : Set.Ioo (-Real.pi) Real.pi θ := hθ ▸ hI'
      exact ⟨hI'', hp⟩
    · rintro ⟨hI, hp⟩
      have hI' : Set.Ioo (-Real.pi) Real.pi θ := hI
      have hI'' : Set.Ioc (-Real.pi) Real.pi θ := hθ.symm ▸ hI'
      exact ⟨hI'', hp⟩
  have hm : volume (Set.Ioc (-Real.pi) Real.pi ∩
      ({θ | 0 < logPolarSlice f x θ} : Set ℝ)) =
      volume (Set.Ioo (-Real.pi) Real.pi ∩
        ({θ | 0 < logPolarSlice f x θ} : Set ℝ)) :=
    measure_congr (hae.mono fun _ h ↦ propext h)
  rw [measureReal_def, hm]
  have hs : Set.Ioo (-Real.pi) Real.pi ∩
      ({θ | 0 < logPolarSlice f x θ} : Set ℝ) =
      angularSection (exceptionalSet f 1) (Real.exp x) := by
    ext θ
    simpa only [Set.mem_inter_iff, Set.mem_ofPred_eq] using
      Set.ext_iff.mp (positive_logPolarSlice_set f x) θ
  rw [hs]
  rfl

theorem volumeReal_Ioc_neg_pi_pi :
    volume.real (Set.Ioc (-Real.pi) Real.pi) = 2 * Real.pi := by
  rw [measureReal_def, Real.volume_Ioc]
  simp only [sub_neg_eq_add, ENNReal.toReal_ofReal (by positivity : 0 ≤ Real.pi + Real.pi)]
  ring

/-- The angular Poincaré estimate for the smooth logarithmic level.  The only excluded
case is a full positive circle, which is treated separately in Carleman's argument. -/
theorem logPolar_poincare {f : ℂ → ℂ} (hf : IsEntire f) (x : ℝ)
    (hwidth : angularWidth (exceptionalSet f 1) (Real.exp x) < 2 * Real.pi) :
    cylindricalSquareEnergy (logPolarSlice f) (-Real.pi) Real.pi x ≤
      (angularWidth (exceptionalSet f 1) (Real.exp x)) ^ 2 *
        ∫ θ in -Real.pi..Real.pi, logPolarTheta f x θ ^ 2 := by
  unfold cylindricalSquareEnergy
  have htcont : Continuous (logPolarTheta f x) :=
    (continuous_logPolarTheta hf).comp (continuous_const.prodMk continuous_id)
  have hproper : volume.real
      (Set.Ioc (-Real.pi) Real.pi ∩ ({θ | 0 < logPolarSlice f x θ} : Set ℝ)) <
      volume.real (Set.Ioc (-Real.pi) Real.pi) := by
    rw [logPolar_support_measure_eq_angularWidth, volumeReal_Ioc_neg_pi_pi]
    exact hwidth
  have h := intervalIntegral_sq_le_supportMeasure_sq_mul_deriv_sq
      (u := logPolarSlice f x) (u' := logPolarTheta f x)
      (a := -Real.pi) (b := Real.pi) (by linarith [Real.pi_pos])
      (contDiff_logPolarSlice_snd hf x).continuous htcont
      (hasDerivAt_logPolarSlice_snd hf x) (logPolarSlice_nonneg f x) hproper
  rw [logPolar_support_measure_eq_angularWidth] at h
  exact h

/-- The Poincaré estimate and the cylindrical energy identity combine to give the
differential inequality at the heart of the Tsuji--Carleman comparison. -/
theorem logPolar_energy_width_differential {f : ℂ → ℂ}
    (hf : IsEntire f) (x : ℝ)
    (hwidth : angularWidth (exceptionalSet f 1) (Real.exp x) < 2 * Real.pi) :
    2 * cylindricalSquareEnergy (logPolarSlice f) (-Real.pi) Real.pi x ≤
      (angularWidth (exceptionalSet f 1) (Real.exp x)) ^ 2 *
        iteratedDeriv 2
          (cylindricalSquareEnergy (logPolarSlice f) (-Real.pi) Real.pi) x := by
  let Ex : ℝ := ∫ θ in -Real.pi..Real.pi, logPolarX f x θ ^ 2
  let Et : ℝ := ∫ θ in -Real.pi..Real.pi, logPolarTheta f x θ ^ 2
  let H : ℝ → ℝ := cylindricalSquareEnergy
    (logPolarSlice f) (-Real.pi) Real.pi
  let Θ : ℝ := angularWidth (exceptionalSet f 1) (Real.exp x)
  have hEx : 0 ≤ Ex := by
    apply intervalIntegral.integral_nonneg (by linarith [Real.pi_pos])
    intro θ _
    exact sq_nonneg _
  have hp : H x ≤ Θ ^ 2 * Et := by
    simpa only [H, Θ, Et] using logPolar_poincare hf x hwidth
  have he : 2 * (Ex + Et) ≤ iteratedDeriv 2 H x := by
    simpa only [H, Ex, Et] using logPolar_energy_second_deriv_ge hf x
  have het : 2 * Et ≤ iteratedDeriv 2 H x := by
    calc
      2 * Et ≤ 2 * (Ex + Et) := by nlinarith
      _ ≤ iteratedDeriv 2 H x := he
  calc
    2 * H x ≤ 2 * (Θ ^ 2 * Et) := mul_le_mul_of_nonneg_left hp (by norm_num)
    _ = Θ ^ 2 * (2 * Et) := by ring
    _ ≤ Θ ^ 2 * iteratedDeriv 2 H x :=
      mul_le_mul_of_nonneg_left het (sq_nonneg Θ)

/-- The interval form of Cauchy--Schwarz, squared to avoid square roots. -/
theorem intervalIntegral_mul_sq_le_mul_sq
    {u v : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hu : Continuous u) (hv : Continuous v) :
    (∫ t in a..b, u t * v t) ^ 2 ≤
      (∫ t in a..b, u t ^ 2) * (∫ t in a..b, v t ^ 2) := by
  rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hab,
    intervalIntegral.integral_of_le hab]
  let ν : Measure ℝ := volume.restrict (Set.Ioc a b)
  have hu_meas : AEStronglyMeasurable u ν := hu.aestronglyMeasurable.restrict
  have hv_meas : AEStronglyMeasurable v ν := hv.aestronglyMeasurable.restrict
  have hu_sq : Integrable (fun t ↦ u t ^ 2) ν := by
    exact (hu.pow 2).integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
  have hv_sq : Integrable (fun t ↦ v t ^ 2) ν := by
    exact (hv.pow 2).integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
  have hνu : MemLp u 2 ν :=
    (memLp_two_iff_integrable_sq hu_meas).mpr hu_sq
  have hνv : MemLp v 2 ν :=
    (memLp_two_iff_integrable_sq hv_meas).mpr hv_sq
  have hholder := integral_mul_norm_le_Lp_mul_Lq
    (f := u) (g := v) (p := (2 : ℝ)) (q := (2 : ℝ)) (μ := ν)
    Real.HolderConjugate.two_two (by simpa using hνu) (by simpa using hνv)
  change (∫ t, |u t| * |v t| ∂ν) ≤
      (∫ t, |u t| ^ (2 : ℝ) ∂ν) ^ (1 / (2 : ℝ)) *
        (∫ t, |v t| ^ (2 : ℝ) ∂ν) ^ (1 / (2 : ℝ)) at hholder
  have hu_abs_sq : (∫ t, |u t| ^ (2 : ℝ) ∂ν) = ∫ t, u t ^ 2 ∂ν := by
    apply integral_congr_ae
    filter_upwards with t
    rw [Real.rpow_two, sq_abs]
  have hv_abs_sq : (∫ t, |v t| ^ (2 : ℝ) ∂ν) = ∫ t, v t ^ 2 ∂ν := by
    apply integral_congr_ae
    filter_upwards with t
    rw [Real.rpow_two, sq_abs]
  rw [hu_abs_sq, hv_abs_sq, ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow] at hholder
  have hnorm : |∫ t, u t * v t ∂ν| ≤ ∫ t, |u t| * |v t| ∂ν := by
    calc
      |∫ t, u t * v t ∂ν| = ‖∫ t, u t * v t ∂ν‖ := by rw [Real.norm_eq_abs]
      _ ≤ ∫ t, ‖u t * v t‖ ∂ν := norm_integral_le_integral_norm _
      _ = ∫ t, |u t| * |v t| ∂ν := by
        apply integral_congr_ae
        filter_upwards with t
        rw [Real.norm_eq_abs, abs_mul]
  have hroot : |∫ t, u t * v t ∂ν| ≤
      √(∫ t, u t ^ 2 ∂ν) * √(∫ t, v t ^ 2 ∂ν) := hnorm.trans hholder
  have hu_nonneg : 0 ≤ ∫ t, u t ^ 2 ∂ν :=
    integral_nonneg_of_ae (ae_of_all _ fun t ↦ sq_nonneg _)
  have hv_nonneg : 0 ≤ ∫ t, v t ^ 2 ∂ν :=
    integral_nonneg_of_ae (ae_of_all _ fun t ↦ sq_nonneg _)
  have hsquare := (sq_le_sq₀ (abs_nonneg (∫ t, u t * v t ∂ν))
    (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))).mpr hroot
  rw [sq_abs, mul_pow, Real.sq_sqrt hu_nonneg, Real.sq_sqrt hv_nonneg] at hsquare
  simpa only [ν] using hsquare

/-- The derivative of the cylindrical square energy satisfies the companion
Cauchy--Schwarz estimate used when differentiating its square root. -/
theorem logPolar_energy_deriv_sq_le {f : ℂ → ℂ}
    (hf : IsEntire f) (x : ℝ) :
    (deriv (cylindricalSquareEnergy
      (logPolarSlice f) (-Real.pi) Real.pi) x) ^ 2 ≤
      4 * cylindricalSquareEnergy
          (logPolarSlice f) (-Real.pi) Real.pi x *
        ∫ θ in -Real.pi..Real.pi, logPolarX f x θ ^ 2 := by
  let H : ℝ → ℝ := cylindricalSquareEnergy
    (logPolarSlice f) (-Real.pi) Real.pi
  let J : ℝ := ∫ θ in -Real.pi..Real.pi,
    logPolarSlice f x θ * logPolarX f x θ
  have hderiv : deriv H x = 2 * J := by
    have h := (hasDerivAt_cylindricalSquareEnergy
      (continuous_uncurry_logPolarSlice hf) (continuous_logPolarX hf)
      (hasDerivAt_logPolarSlice_fst hf) (-Real.pi) Real.pi x).deriv
    dsimp only [H]
    rw [h, intervalIntegral.integral_const_mul]
  have hcs : J ^ 2 ≤
      H x * ∫ θ in -Real.pi..Real.pi, logPolarX f x θ ^ 2 := by
    dsimp only [J, H, cylindricalSquareEnergy]
    apply intervalIntegral_mul_sq_le_mul_sq (by linarith [Real.pi_pos])
    · exact (contDiff_logPolarSlice_snd hf x).continuous
    · exact (continuous_logPolarX hf).comp (continuous_const.prodMk continuous_id)
  rw [hderiv]
  nlinarith

/-- The exact second-derivative formula for the square root of a positive twice
differentiable real function, stated using explicit first- and second-derivative fields. -/
theorem iteratedDeriv_two_sqrt
    {H H₁ H₂ : ℝ → ℝ}
    (hH : ∀ y, HasDerivAt H (H₁ y) y)
    (hH₁ : ∀ y, HasDerivAt H₁ (H₂ y) y)
    {x : ℝ} (hx : 0 < H x) :
    iteratedDeriv 2 (fun y ↦ √(H y)) x =
      H₂ x / (2 * √(H x)) - H₁ x ^ 2 / (4 * (√(H x)) ^ 3) := by
  let F : ℝ → ℝ := fun y ↦ √(H y)
  let G : ℝ → ℝ := fun y ↦ H₁ y / (2 * F y)
  let D : ℝ := H₂ x / (2 * F x) - H₁ x ^ 2 / (4 * (F x) ^ 3)
  have hFne : F x ≠ 0 := by
    dsimp only [F]
    exact (Real.sqrt_ne_zero').mpr hx
  have hF : HasDerivAt F (H₁ x / (2 * F x)) x := by
    dsimp only [F]
    simpa only using (hH x).sqrt hx.ne'
  have hG : HasDerivAt G D x := by
    have hraw := (hH₁ x).div (hF.const_mul 2) (mul_ne_zero two_ne_zero hFne)
    have hval :
        (H₂ x * (2 * F x) - H₁ x * (2 * (H₁ x / (2 * F x)))) /
            (2 * F x) ^ 2 = D := by
      dsimp only [D]
      field_simp [hFne]
      ring
    rw [hval] at hraw
    change HasDerivAt (fun y ↦ H₁ y / (2 * F y)) D x at hraw
    exact hraw
  have hHcont : Continuous H := continuous_iff_continuousAt.mpr fun y ↦ (hH y).continuousAt
  have hne : ∀ᶠ y in nhds x, H y ≠ 0 := by
    exact (isOpen_compl_singleton.preimage hHcont).mem_nhds hx.ne'
  have hderiv_eq : deriv F =ᶠ[nhds x] G := by
    filter_upwards [hne] with y hy
    dsimp only [F, G]
    rw [deriv_sqrt (hH y).differentiableAt hy, (hH y).deriv]
  have hd : HasDerivAt (deriv F) D x := hG.congr_of_eventuallyEq hderiv_eq
  rw [show iteratedDeriv 2 F x = deriv (deriv F) x by
    rw [show (2 : ℕ) = 1 + 1 by norm_num, iteratedDeriv_succ, iteratedDeriv_one]]
  simpa only [F, D] using hd.deriv

/-- The derivative of the explicit first-derivative field for `√H`. -/
theorem hasDerivAt_sqrt_first_field
    {H H₁ H₂ : ℝ → ℝ}
    (hH : ∀ y, HasDerivAt H (H₁ y) y)
    (hH₁ : ∀ y, HasDerivAt H₁ (H₂ y) y)
    {x : ℝ} (hx : 0 < H x) :
    HasDerivAt (fun y ↦ H₁ y / (2 * √(H y)))
      (H₂ x / (2 * √(H x)) - H₁ x ^ 2 / (4 * (√(H x)) ^ 3)) x := by
  have hroot : 0 < √(H x) := Real.sqrt_pos.2 hx
  have hF : HasDerivAt (fun y ↦ √(H y))
      (H₁ x / (2 * √(H x))) x := (hH x).sqrt hx.ne'
  have hraw := (hH₁ x).div (hF.const_mul 2)
    (mul_ne_zero two_ne_zero hroot.ne')
  have hval :
      (H₂ x * (2 * √(H x)) -
          H₁ x * (2 * (H₁ x / (2 * √(H x))))) /
          (2 * √(H x)) ^ 2 =
        H₂ x / (2 * √(H x)) - H₁ x ^ 2 / (4 * (√(H x)) ^ 3) := by
    field_simp [hroot.ne']
    ring
  rw [hval] at hraw
  change HasDerivAt (fun y ↦ H₁ y / (2 * √(H y))) _ x at hraw
  exact hraw

/-- Scalar Carleman comparison on one interval.  The elementary inequality
`2q ≤ F'/F + F''/F'` is integrated as two logarithmic derivatives. -/
theorem intervalIntegral_carleman_log_bound
    {F F₁ F₂ q : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hF : ∀ x ∈ Set.Icc a b, HasDerivAt F (F₁ x) x)
    (hF₁ : ∀ x ∈ Set.Icc a b, HasDerivAt F₁ (F₂ x) x)
    (hFcont : ContinuousOn F (Set.Icc a b))
    (hF₁cont : ContinuousOn F₁ (Set.Icc a b))
    (hF₂cont : ContinuousOn F₂ (Set.Icc a b))
    (hFpos : ∀ x ∈ Set.Icc a b, 0 < F x)
    (hF₁pos : ∀ x ∈ Set.Icc a b, 0 < F₁ x)
    (hqmeas : AEStronglyMeasurable q volume)
    (hqnonneg : ∀ x ∈ Set.Icc a b, 0 ≤ q x)
    (hcurv : ∀ x ∈ Set.Icc a b, q x ^ 2 * F x ≤ F₂ x) :
    IntervalIntegrable q volume a b ∧
      2 * ∫ x in a..b, q x ≤
        (Real.log (F b) - Real.log (F a)) +
          (Real.log (F₁ b) - Real.log (F₁ a)) := by
  let g : ℝ → ℝ := fun x ↦ F₁ x / F x + F₂ x / F₁ x
  have hpoint : ∀ x ∈ Set.Icc a b, 2 * q x ≤ g x := by
    intro x hx
    have hFp := hFpos x hx
    have hF₁p := hF₁pos x hx
    have hid : F₁ x / F x + q x ^ 2 * F x / F₁ x - 2 * q x =
        (F₁ x - q x * F x) ^ 2 / (F x * F₁ x) := by
      field_simp [hFp.ne', hF₁p.ne']
      ring
    have ham : 2 * q x ≤ F₁ x / F x + q x ^ 2 * F x / F₁ x := by
      rw [← sub_nonneg, hid]
      positivity
    have hc : q x ^ 2 * F x / F₁ x ≤ F₂ x / F₁ x :=
      div_le_div_of_nonneg_right (hcurv x hx) hF₁p.le
    dsimp only [g]
    linarith
  have hgcont : ContinuousOn g (Set.Icc a b) := by
    have hg₁ : ContinuousOn (fun x ↦ F₁ x / F x) (Set.Icc a b) := by
      exact hF₁cont.div hFcont fun x hx ↦
        (hFpos x hx).ne'
    have hg₂ : ContinuousOn (fun x ↦ F₂ x / F₁ x) (Set.Icc a b) := by
      exact hF₂cont.div hF₁cont fun x hx ↦
        (hF₁pos x hx).ne'
    exact hg₁.add hg₂
  have hgint : IntegrableOn g (Set.Icc a b) := hgcont.integrableOn_Icc
  have hqintOn : IntegrableOn q (Set.Icc a b) := by
    apply hgint.mono' hqmeas.restrict
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (hqnonneg x hx)]
    exact (le_mul_of_one_le_left (hqnonneg x hx) (by norm_num : (1 : ℝ) ≤ 2)).trans
      (hpoint x hx)
  have hqint : IntervalIntegrable q volume a b := by
    rw [intervalIntegrable_iff, uIoc_of_le hab]
    exact hqintOn.mono_set Set.Ioc_subset_Icc_self
  have hgintI : IntervalIntegrable g volume a b := by
    rw [intervalIntegrable_iff, uIoc_of_le hab]
    exact hgint.mono_set Set.Ioc_subset_Icc_self
  have hmono : 2 * ∫ x in a..b, q x ≤ ∫ x in a..b, g x := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_mono_on hab (hqint.const_mul 2) hgintI
    exact hpoint
  have hlogF : (∫ x in a..b, F₁ x / F x) =
      Real.log (F b) - Real.log (F a) := by
    calc
      (∫ x in a..b, F₁ x / F x) =
          ∫ x in a..b, deriv (fun y ↦ Real.log (F y)) x := by
        apply intervalIntegral.integral_congr
        intro x hx
        have hx' : x ∈ Set.Icc a b := by simpa [uIcc_of_le hab] using hx
        exact ((hF x hx').log (hFpos x hx').ne').deriv.symm
      _ = Real.log (F b) - Real.log (F a) := by
        apply intervalIntegral.integral_deriv_eq_sub' _ rfl
        · intro x hx
          have hx' : x ∈ Set.Icc a b := by simpa [uIcc_of_le hab] using hx
          exact ((hF x hx').log (hFpos x hx').ne').differentiableAt
        · have hc : ContinuousOn (fun x ↦ F₁ x / F x) (uIcc a b) := by
            rw [uIcc_of_le hab]
            apply ContinuousOn.div hF₁cont hFcont
            intro x hx
            exact (hFpos x hx).ne'
          apply hc.congr
          intro x hx
          have hx' : x ∈ Set.Icc a b := by simpa [uIcc_of_le hab] using hx
          exact ((hF x hx').log (hFpos x hx').ne').deriv
  have hlogF₁ : (∫ x in a..b, F₂ x / F₁ x) =
      Real.log (F₁ b) - Real.log (F₁ a) := by
    calc
      (∫ x in a..b, F₂ x / F₁ x) =
          ∫ x in a..b, deriv (fun y ↦ Real.log (F₁ y)) x := by
        apply intervalIntegral.integral_congr
        intro x hx
        have hx' : x ∈ Set.Icc a b := by simpa [uIcc_of_le hab] using hx
        exact ((hF₁ x hx').log (hF₁pos x hx').ne').deriv.symm
      _ = Real.log (F₁ b) - Real.log (F₁ a) := by
        apply intervalIntegral.integral_deriv_eq_sub' _ rfl
        · intro x hx
          have hx' : x ∈ Set.Icc a b := by simpa [uIcc_of_le hab] using hx
          exact ((hF₁ x hx').log (hF₁pos x hx').ne').differentiableAt
        · have hc : ContinuousOn (fun x ↦ F₂ x / F₁ x) (uIcc a b) := by
            rw [uIcc_of_le hab]
            apply ContinuousOn.div hF₂cont hF₁cont
            intro x hx
            exact (hF₁pos x hx).ne'
          apply hc.congr
          intro x hx
          have hx' : x ∈ Set.Icc a b := by simpa [uIcc_of_le hab] using hx
          exact ((hF₁ x hx').log (hF₁pos x hx').ne').deriv
  refine ⟨hqint, hmono.trans_eq ?_⟩
  change (∫ x in a..b, F₁ x / F x + F₂ x / F₁ x) = _
  have hr₁ : IntervalIntegrable (fun x ↦ F₁ x / F x) volume a b := by
    rw [intervalIntegrable_iff, uIoc_of_le hab]
    apply (hF₁cont.div hFcont (fun x hx ↦
      (hFpos x hx).ne')).integrableOn_Icc.mono_set
    exact Set.Ioc_subset_Icc_self
  have hr₂ : IntervalIntegrable (fun x ↦ F₂ x / F₁ x) volume a b := by
    rw [intervalIntegrable_iff, uIoc_of_le hab]
    apply (hF₂cont.div hF₁cont (fun x hx ↦
      (hF₁pos x hx).ne')).integrableOn_Icc.mono_set
    exact Set.Ioc_subset_Icc_self
  rw [intervalIntegral.integral_add hr₁ hr₂, hlogF, hlogF₁]

/-- A smooth logarithmic core with the same normalized strict superlevel as `log ‖f‖`.
Unlike `log ‖f‖`, it is smooth through the zeros of `f`. -/
noncomputable def smoothLogarithmicCore (f : ℂ → ℂ) (z : ℂ) : ℝ :=
  Real.log ((1 + ‖f z‖ ^ 2) / 2)

theorem contDiff_smoothLogarithmicCore {f : ℂ → ℂ} (hf : IsEntire f) :
    ContDiff ℝ 2 (smoothLogarithmicCore f) := by
  have hfR : ContDiff ℝ 2 f := by
    rw [contDiff_iff_contDiffAt]
    intro z
    exact (hf.analyticAt z).restrictScalars.contDiffAt
  unfold smoothLogarithmicCore
  apply (contDiff_const.add (hfR.norm_sq ℂ)).div_const 2 |>.log
  intro z
  positivity

theorem smoothLogarithmicCore_pos_iff (f : ℂ → ℂ) (z : ℂ) :
    0 < smoothLogarithmicCore f z ↔ 1 < ‖f z‖ := by
  unfold smoothLogarithmicCore
  rw [Real.log_pos_iff (by positivity)]
  constructor
  · intro h
    have hn : 0 ≤ ‖f z‖ := norm_nonneg _
    nlinarith [sq_nonneg (‖f z‖ - 1)]
  · intro h
    nlinarith [sq_nonneg (‖f z‖ - 1)]

/-- The `C²` nonnegative logarithmic level used for the differential form of the
Tsuji--Carleman argument. -/
noncomputable def smoothLogarithmicLevel (f : ℂ → ℂ) (z : ℂ) : ℝ :=
  smoothPositivePart (smoothLogarithmicCore f z)

theorem contDiff_smoothLogarithmicLevel {f : ℂ → ℂ} (hf : IsEntire f) :
    ContDiff ℝ 2 (smoothLogarithmicLevel f) := by
  exact contDiff_smoothPositivePart.comp (contDiff_smoothLogarithmicCore hf)

theorem smoothLogarithmicLevel_nonneg (f : ℂ → ℂ) (z : ℂ) :
    0 ≤ smoothLogarithmicLevel f z :=
  smoothPositivePart_nonneg _

theorem smoothLogarithmicLevel_pos_iff (f : ℂ → ℂ) (z : ℂ) :
    0 < smoothLogarithmicLevel f z ↔ 1 < ‖f z‖ := by
  rw [smoothLogarithmicLevel, smoothPositivePart_pos_iff, smoothLogarithmicCore_pos_iff]

theorem positiveSet_smoothLogarithmicLevel (f : ℂ → ℂ) :
    {z | 0 < smoothLogarithmicLevel f z} = exceptionalSet f 1 := by
  ext z
  exact smoothLogarithmicLevel_pos_iff f z

/-- The continuous positive logarithmic level used in Camera's reduction.  Mathlib's
`Real.log⁺` is the continuous extension of `max 0 (log x)` through zero. -/
noncomputable def logarithmicLevel (f : ℂ → ℂ) (c : ℝ) (z : ℂ) : ℝ :=
  Real.posLog (‖f z‖ / c)

theorem continuous_logarithmicLevel {f : ℂ → ℂ} (hf : Continuous f) (c : ℝ) :
    Continuous (logarithmicLevel f c) := by
  unfold logarithmicLevel
  exact Real.continuous_posLog.comp (hf.norm.div_const c)

theorem logarithmicLevel_nonneg (f : ℂ → ℂ) (c : ℝ) (z : ℂ) :
    0 ≤ logarithmicLevel f c z := by
  exact Real.posLog_nonneg

/-- The positive set of the logarithmic reduction is exactly the exceptional set. -/
theorem logarithmicLevel_pos_iff {f : ℂ → ℂ} {c : ℝ} (hc : 0 < c) (z : ℂ) :
    0 < logarithmicLevel f c z ↔ c < ‖f z‖ := by
  have hx : 0 ≤ ‖f z‖ / c := div_nonneg (norm_nonneg _) hc.le
  constructor
  · intro hpos
    have hnot : ¬ |‖f z‖ / c| ≤ 1 := by
      intro hle
      exact (ne_of_gt hpos) ((Real.posLog_eq_zero_iff _).2 hle)
    have hone : 1 < ‖f z‖ / c := by
      simpa only [abs_of_nonneg hx, not_le] using hnot
    exact (one_lt_div hc).mp hone
  · intro h
    have hone : 1 < ‖f z‖ / c := (one_lt_div hc).mpr h
    have hlog : 0 < Real.log (‖f z‖ / c) := (Real.log_pos_iff hx).mpr hone
    simpa only [logarithmicLevel, Real.posLog_apply, max_eq_right hlog.le] using hlog

theorem positiveSet_logarithmicLevel {f : ℂ → ℂ} {c : ℝ} (hc : 0 < c) :
    {z | 0 < logarithmicLevel f c z} = exceptionalSet f c := by
  ext z
  exact logarithmicLevel_pos_iff hc z

/-- The circular maximum of the logarithmic reduction, written in terms of `M_f`. -/
noncomputable def logarithmicMaximum (f : ℂ → ℂ) (c r : ℝ) : ℝ :=
  Real.posLog (maximumModulus f r / c)

theorem logarithmicMaximum_one_mono {f : ℂ → ℂ} (hf : IsEntire f)
    {r s : ℝ} (hr : 0 ≤ r) (hrs : r ≤ s) :
    logarithmicMaximum f 1 r ≤ logarithmicMaximum f 1 s := by
  unfold logarithmicMaximum
  simp only [div_one]
  exact Real.posLog_le_posLog (maximumModulus_nonneg hf.continuous hr)
    (maximumModulus_mono hf hr hrs)

theorem log_logarithmicMaximum_one_mono {f : ℂ → ℂ} (hf : IsEntire f)
    {r s : ℝ} (hr : 0 ≤ r) (hrs : r ≤ s)
    (hB : 0 < logarithmicMaximum f 1 r) :
    Real.log (logarithmicMaximum f 1 r) ≤
      Real.log (logarithmicMaximum f 1 s) :=
  Real.log_le_log hB (logarithmicMaximum_one_mono hf hr hrs)

theorem logCounting_top_eq_zero_of_entire {f : ℂ → ℂ} (hf : IsEntire f) :
    ValueDistribution.logCounting f ⊤ = 0 := by
  have ha : AnalyticOnNhd ℂ f Set.univ :=
    Complex.analyticOnNhd_univ_iff_differentiable.mpr hf
  have hneg : (MeromorphicOn.divisor f Set.univ)⁻ = 0 :=
    negPart_eq_zero.mpr (MeromorphicOn.AnalyticOnNhd.divisor_nonneg ha)
  rw [ValueDistribution.logCounting_top, hneg]
  exact map_zero _

/-- For an entire function the Nevanlinna proximity to infinity, equivalently the circular
average of `log⁺ ‖f‖`, is monotone in the radius. -/
theorem proximity_top_monoOn_of_entire {f : ℂ → ℂ} (hf : IsEntire f) :
    MonotoneOn (ValueDistribution.proximity f ⊤) (Set.Ioi 0) := by
  have hm : Meromorphic f := fun z ↦ (hf.analyticAt z).meromorphicAt
  have hc := ValueDistribution.characteristic_monotoneOn hm
  have hcount := logCounting_top_eq_zero_of_entire hf
  intro r hr s hs hrs
  have h := hc hr hs hrs
  simp only [ValueDistribution.characteristic, Pi.add_apply, hcount, Pi.zero_apply,
    add_zero] at h
  exact h

theorem logarithmicLevel_le_logarithmicMaximum {f : ℂ → ℂ} (hf : Continuous f)
    {c r : ℝ} (hc : 0 < c) (hr : 0 ≤ r) {z : ℂ} (hz : ‖z‖ = r) :
    logarithmicLevel f c z ≤ logarithmicMaximum f c r := by
  unfold logarithmicLevel logarithmicMaximum
  apply Real.posLog_le_posLog
  · exact div_nonneg (norm_nonneg _) hc.le
  · exact div_le_div_of_nonneg_right (norm_le_maximumModulus hf hr hz) hc.le

theorem exists_logarithmicMaximum_eq {f : ℂ → ℂ} (hf : Continuous f)
    {c r : ℝ} (hc : 0 < c) (hr : 0 ≤ r) :
    ∃ z : ℂ, ‖z‖ = r ∧ logarithmicMaximum f c r = logarithmicLevel f c z ∧
      ∀ w : ℂ, ‖w‖ = r → logarithmicLevel f c w ≤ logarithmicLevel f c z := by
  obtain ⟨z, hz, hM, hmax⟩ := exists_maximumModulus_eq hf hr
  refine ⟨z, hz, ?_, ?_⟩
  · simp only [logarithmicMaximum, logarithmicLevel, hM]
  · intro w hw
    unfold logarithmicLevel
    apply Real.posLog_le_posLog
    · exact div_nonneg (norm_nonneg _) hc.le
    · exact div_le_div_of_nonneg_right (hmax w hw) hc.le

/-- If the normalized logarithmic maximum is larger than `1`, then the strict exceptional
set occupies a nonempty open arc on that circle.  The closure argument handles the omitted
negative-real-axis angle in the standard polar chart. -/
theorem angularSection_exceptional_nonempty_of_one_lt_logarithmicMaximum
    {f : ℂ → ℂ} (hf : Continuous f) {r : ℝ} (hr : 0 < r)
    (hB : 1 < logarithmicMaximum f 1 r) :
    (angularSection (exceptionalSet f 1) r).Nonempty := by
  obtain ⟨z, hz, hmax, -⟩ :=
    exists_logarithmicMaximum_eq hf one_pos hr.le
  have hzlevel : 0 < logarithmicLevel f 1 z := by
    rw [← hmax]
    exact one_pos.trans hB
  have hzexceptional : z ∈ exceptionalSet f 1 :=
    (logarithmicLevel_pos_iff one_pos z).mp hzlevel
  let θ₀ : ℝ := Complex.arg z
  let U : Set ℝ := (fun θ ↦ polarPoint r θ) ⁻¹' exceptionalSet f 1
  have hpolar : polarPoint r θ₀ = z := by
    unfold polarPoint θ₀
    simp only [Complex.polarCoord_symm_apply]
    rw [← hz]
    simp [Complex.norm_mul_cos_add_sin_mul_I z]
  have hUopen : IsOpen U := by
    apply (isOpen_exceptionalSet hf 1).preimage
    have h : Continuous (fun θ : ℝ ↦
        (r : ℂ) * (Real.cos θ + Real.sin θ * Complex.I)) := by fun_prop
    convert h using 1
    funext θ
    simp [polarPoint]
  have hθU : θ₀ ∈ U := by
    change polarPoint r θ₀ ∈ exceptionalSet f 1
    simpa only [hpolar] using hzexceptional
  have hθclosure : θ₀ ∈ closure (Set.Ioo (-Real.pi) Real.pi) := by
    rw [closure_Ioo (by linarith [Real.pi_pos] : -Real.pi ≠ Real.pi)]
    exact ⟨(Complex.neg_pi_lt_arg z).le, Complex.arg_le_pi z⟩
  obtain ⟨θ, hθU', hθrange⟩ :=
    (mem_closure_iff.mp hθclosure) U hUopen hθU
  exact ⟨θ, hθrange, hθU'⟩

theorem proximity_top_pos_of_one_lt_logarithmicMaximum {f : ℂ → ℂ}
    (hf : IsEntire f) {r : ℝ} (hr : 0 < r)
    (hB : 1 < logarithmicMaximum f 1 r) :
    0 < ValueDistribution.proximity f ⊤ r := by
  let u : ℝ → ℝ := fun θ ↦ Real.posLog ‖f (polarPoint r θ)‖
  have hucont : Continuous u := by
    have hp : Continuous (fun θ : ℝ ↦
        (r : ℂ) * (Real.cos θ + Real.sin θ * Complex.I)) := by fun_prop
    have hp' : Continuous (polarPoint r) := by
      convert hp using 1
      funext θ
      simp [polarPoint]
    exact Real.continuous_posLog.comp
      ((hf.continuous.comp hp').norm)
  obtain ⟨θ, hθI, hθE⟩ :=
    angularSection_exceptional_nonempty_of_one_lt_logarithmicMaximum
      hf.continuous hr hB
  have hθpos : 0 < u θ := by
    have hn : 1 < ‖f (polarPoint r θ)‖ := hθE
    dsimp only [u]
    rw [Real.posLog_eq_log (by simpa [abs_of_nonneg (norm_nonneg _)] using hn.le)]
    exact Real.log_pos hn
  let P : Set ℝ := Set.Ioo (-Real.pi) Real.pi ∩ {t | 0 < u t}
  have hPopen : IsOpen P :=
    isOpen_Ioo.inter (isOpen_lt continuous_const hucont)
  have hPne : P.Nonempty := ⟨θ, hθI, hθpos⟩
  have hPpos : 0 < volume P := hPopen.measure_pos volume hPne
  have hPsub : P ⊆ Function.support u ∩ Set.Ioc (-Real.pi) Real.pi := by
    intro t ht
    exact ⟨Function.mem_support.mpr ht.2.ne', Set.Ioo_subset_Ioc_self ht.1⟩
  have hintpos : 0 < ∫ t in -Real.pi..Real.pi, u t := by
    rw [intervalIntegral.integral_of_le (by linarith [Real.pi_pos])]
    apply (setIntegral_pos_iff_support_of_nonneg_ae
      (ae_of_all _ fun t ↦ Real.posLog_nonneg)
      (hucont.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self)).mpr
    exact hPpos.trans_le (measure_mono hPsub)
  have hperiod : Function.Periodic u (2 * Real.pi) := by
    intro t
    dsimp only [u]
    congr 3
    simp [polarPoint]
  have hshift := hperiod.intervalIntegral_add_eq (t := 0) (s := -Real.pi)
  have hends : -Real.pi + 2 * Real.pi = Real.pi := by ring
  rw [zero_add, hends] at hshift
  rw [ValueDistribution.proximity_top, Real.circleAverage_def]
  change 0 < (2 * Real.pi)⁻¹ *
    ∫ t in 0..2 * Real.pi, Real.posLog ‖f (circleMap 0 r t)‖
  have hcircle : (fun t ↦ Real.posLog ‖f (circleMap 0 r t)‖) = u := by
    funext t
    congr 3
    simp [circleMap, polarPoint, Complex.exp_mul_I]
  rw [hcircle, hshift]
  exact mul_pos (inv_pos.mpr (by positivity)) hintpos

theorem eventually_pos_log_logarithmicMaximum_one {f : ℂ → ℂ}
    (hf : IsNonconstantEntire f) :
    ∃ R > 0, ∀ r, R ≤ r →
      0 < Real.log (logarithmicMaximum f 1 r) := by
  have hev : ∀ᶠ r in atTop,
      0 < Real.log (Real.log (maximumModulus f r)) ∧
        1 < maximumModulus f r := by
    filter_upwards
      [(log_log_maximumModulus_tendsto_atTop hf).eventually_gt_atTop 0,
        (maximumModulus_tendsto_atTop hf).eventually_gt_atTop 1] with r hlog hM
    exact ⟨hlog, hM⟩
  obtain ⟨R, hR⟩ := eventually_atTop.mp hev
  refine ⟨max R 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro r hr
  obtain ⟨hlog, hM⟩ := hR r ((le_max_left _ _).trans hr)
  have hMnonneg : 0 ≤ maximumModulus f r := hM.le.trans' zero_le_one
  have heq : logarithmicMaximum f 1 r = Real.log (maximumModulus f r) := by
    unfold logarithmicMaximum
    rw [div_one, Real.posLog_eq_log]
    simpa [abs_of_nonneg hMnonneg] using hM.le
  rwa [heq]

theorem proximity_top_eq_polar_posLog_set_average (f : ℂ → ℂ) (r : ℝ) :
    ValueDistribution.proximity f ⊤ r =
      (2 * Real.pi)⁻¹ *
        ∫ θ in Set.Ioc (-Real.pi) Real.pi,
          Real.posLog ‖f (polarPoint r θ)‖ := by
  let u : ℝ → ℝ := fun θ ↦ Real.posLog ‖f (polarPoint r θ)‖
  have hperiod : Function.Periodic u (2 * Real.pi) := by
    intro t
    dsimp only [u]
    congr 3
    simp [polarPoint]
  have hshift := hperiod.intervalIntegral_add_eq (t := 0) (s := -Real.pi)
  have hends : -Real.pi + 2 * Real.pi = Real.pi := by ring
  rw [zero_add, hends] at hshift
  rw [ValueDistribution.proximity_top, Real.circleAverage_def]
  have hcircle : (fun t ↦ Real.posLog ‖f (circleMap 0 r t)‖) = u := by
    funext t
    congr 3
    simp [circleMap, polarPoint, Complex.exp_mul_I]
  rw [hcircle, hshift, intervalIntegral.integral_of_le (by linarith [Real.pi_pos])]
  rfl

/-- Jensen's inequality for the fifth power on a standard angular period. -/
theorem angular_set_average_pow_five_le {u : ℝ → ℝ} (hu : Continuous u)
    (hun : ∀ x, 0 ≤ u x) :
    (((2 * Real.pi)⁻¹ * ∫ x in Set.Ioc (-Real.pi) Real.pi, u x) ^ 5) ≤
      (2 * Real.pi)⁻¹ * ∫ x in Set.Ioc (-Real.pi) Real.pi, u x ^ 5 := by
  let I : Set ℝ := Set.Ioc (-Real.pi) Real.pi
  have h0 : volume I ≠ 0 := by
    change volume (Set.Ioc (-Real.pi) Real.pi) ≠ 0
    rw [Real.volume_Ioc, ne_eq, ENNReal.ofReal_eq_zero]
    linarith [Real.pi_pos]
  have ht : volume I ≠ ∞ := ne_of_lt measure_Ioc_lt_top
  have hJ := (convexOn_pow 5 :
      ConvexOn ℝ (Set.Ici 0) (fun x : ℝ ↦ x ^ 5)).map_set_average_le
    (continuousOn_pow 5) isClosed_Ici h0 ht
    (ae_of_all _ fun x ↦ hun x)
    (hu.integrableOn_Icc.mono_set fun x hx ↦ ⟨hx.1.le, hx.2⟩)
    ((hu.pow 5).integrableOn_Icc.mono_set fun x hx ↦ ⟨hx.1.le, hx.2⟩)
  have hmeasure : volume.real I = 2 * Real.pi := by
    simpa only [I] using volumeReal_Ioc_neg_pi_pi
  simpa only [I, MeasureTheory.average_eq,
    MeasureTheory.measureReal_restrict_apply_univ, smul_eq_mul,
    Function.comp_apply, hmeasure] using hJ

/-- The angular width of the strict exceptional set is positive on every positive circle
where the normalized logarithmic maximum exceeds `1`. -/
theorem angularWidth_exceptional_pos_of_one_lt_logarithmicMaximum
    {f : ℂ → ℂ} (hf : Continuous f) {r : ℝ} (hr : 0 < r)
    (hB : 1 < logarithmicMaximum f 1 r) :
    0 < angularWidth (exceptionalSet f 1) r := by
  unfold angularWidth
  apply ENNReal.toReal_pos
  · exact ((isOpen_angularSection (isOpen_exceptionalSet hf 1) r).measure_pos volume
      (angularSection_exceptional_nonempty_of_one_lt_logarithmicMaximum hf hr hB)).ne'
  · exact volume_angularSection_ne_top _ _

/-- Positivity of `log B(r)` supplies the positive polar area density needed for reciprocal
angular-width estimates. -/
theorem radius_mul_angularWidth_exceptional_pos_of_log_logarithmicMaximum
    {f : ℂ → ℂ} (hf : Continuous f) {r : ℝ} (hr : 0 < r)
    (hlog : 0 < Real.log (logarithmicMaximum f 1 r)) :
    0 < r * angularWidth (exceptionalSet f 1) r := by
  have hB : 1 < logarithmicMaximum f 1 r :=
    (Real.log_pos_iff Real.posLog_nonneg).mp hlog
  exact mul_pos hr
    (angularWidth_exceptional_pos_of_one_lt_logarithmicMaximum hf hr hB)

/-- Positivity of the normalized logarithmic maximum makes the cylindrical square energy
strictly positive. -/
theorem logPolar_energy_pos_of_log_max_pos {f : ℂ → ℂ}
    (hf : IsEntire f) (x : ℝ)
    (hlog : 0 < Real.log (logarithmicMaximum f 1 (Real.exp x))) :
    0 < cylindricalSquareEnergy
      (logPolarSlice f) (-Real.pi) Real.pi x := by
  have hr : 0 < Real.exp x := Real.exp_pos x
  have hB : 1 < logarithmicMaximum f 1 (Real.exp x) :=
    (Real.log_pos_iff Real.posLog_nonneg).mp hlog
  obtain ⟨θ, hθI, hθE⟩ :=
    angularSection_exceptional_nonempty_of_one_lt_logarithmicMaximum
      hf.continuous hr hB
  have hθpos : 0 < logPolarSlice f x θ := by
    have hs := Set.ext_iff.mp (positive_logPolarSlice_set f x) θ
    exact (hs.mpr ⟨hθI, hθE⟩).2
  let P : Set ℝ := Set.Ioo (-Real.pi) Real.pi ∩
    {t | 0 < logPolarSlice f x t}
  have hPopen : IsOpen P := by
    exact isOpen_Ioo.inter
      (isOpen_lt continuous_const (contDiff_logPolarSlice_snd hf x).continuous)
  have hPne : P.Nonempty := ⟨θ, hθI, hθpos⟩
  have hPpos : 0 < volume P := hPopen.measure_pos volume hPne
  have hPsub : P ⊆ Function.support (fun t ↦ logPolarSlice f x t ^ 2) ∩
      Set.Ioc (-Real.pi) Real.pi := by
    intro t ht
    refine ⟨?_, Set.Ioo_subset_Ioc_self ht.1⟩
    exact Function.mem_support.mpr (sq_pos_of_pos ht.2).ne'
  unfold cylindricalSquareEnergy
  rw [intervalIntegral.integral_of_le (by linarith [Real.pi_pos])]
  apply (setIntegral_pos_iff_support_of_nonneg_ae
    (ae_of_all _ fun t ↦ sq_nonneg _)
    ((contDiff_logPolarSlice_snd hf x).continuous.pow 2
      |>.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self)).mpr
  exact hPpos.trans_le (measure_mono hPsub)

/-- After taking the square root of the cylindrical energy, the angular-width estimate
becomes the scalar Sturm inequality `F / Θ² ≤ F''`. -/
theorem logPolar_sqrt_energy_second_deriv_ge {f : ℂ → ℂ}
    (hf : IsEntire f) (x : ℝ)
    (hlog : 0 < Real.log (logarithmicMaximum f 1 (Real.exp x)))
    (hwidth : angularWidth (exceptionalSet f 1) (Real.exp x) < 2 * Real.pi) :
    √(cylindricalSquareEnergy
          (logPolarSlice f) (-Real.pi) Real.pi x) /
        (angularWidth (exceptionalSet f 1) (Real.exp x)) ^ 2 ≤
      iteratedDeriv 2
        (fun y ↦ √(cylindricalSquareEnergy
          (logPolarSlice f) (-Real.pi) Real.pi y)) x := by
  let H : ℝ → ℝ := cylindricalSquareEnergy
    (logPolarSlice f) (-Real.pi) Real.pi
  let H₁ : ℝ → ℝ := fun y ↦ ∫ θ in -Real.pi..Real.pi,
    2 * (logPolarSlice f y θ * logPolarX f y θ)
  let H₂ : ℝ → ℝ := fun y ↦ ∫ θ in -Real.pi..Real.pi,
    2 * (logPolarX f y θ ^ 2 + logPolarSlice f y θ * logPolarXX f y θ)
  let Ex : ℝ := ∫ θ in -Real.pi..Real.pi, logPolarX f x θ ^ 2
  let Et : ℝ := ∫ θ in -Real.pi..Real.pi, logPolarTheta f x θ ^ 2
  let Θ : ℝ := angularWidth (exceptionalSet f 1) (Real.exp x)
  let F : ℝ := √(H x)
  have hH : ∀ y, HasDerivAt H (H₁ y) y := by
    intro y
    simpa only [H, H₁] using hasDerivAt_cylindricalSquareEnergy
      (continuous_uncurry_logPolarSlice hf) (continuous_logPolarX hf)
      (hasDerivAt_logPolarSlice_fst hf) (-Real.pi) Real.pi y
  have hH₁ : ∀ y, HasDerivAt H₁ (H₂ y) y := by
    intro y
    apply hasDerivAt_intervalIntegral_of_continuous_partial
        (F := fun s t ↦ 2 * (logPolarSlice f s t * logPolarX f s t))
        (F' := fun s t ↦
          2 * (logPolarX f s t ^ 2 + logPolarSlice f s t * logPolarXX f s t))
    · exact continuous_const.mul
        ((continuous_uncurry_logPolarSlice hf).mul (continuous_logPolarX hf))
    · exact continuous_const.mul
        ((continuous_logPolarX hf).pow 2 |>.add
          ((continuous_uncurry_logPolarSlice hf).mul (continuous_logPolarXX hf)))
    · intro s t
      simpa [pow_two] using
        ((hasDerivAt_logPolarSlice_fst hf s t).mul
          (hasDerivAt_logPolarX_fst hf s t)).const_mul (2 : ℝ)
  have hHpos : 0 < H x := by
    simpa only [H] using logPolar_energy_pos_of_log_max_pos hf x hlog
  have hFpos : 0 < F := by
    dsimp only [F]
    exact Real.sqrt_pos.2 hHpos
  have hΘpos : 0 < Θ := by
    apply angularWidth_exceptional_pos_of_one_lt_logarithmicMaximum hf.continuous
      (Real.exp_pos x)
    exact (Real.log_pos_iff Real.posLog_nonneg).mp hlog
  have hF2 : F ^ 2 = H x := by
    dsimp only [F]
    exact Real.sq_sqrt hHpos.le
  have hsecond : iteratedDeriv 2 (fun y ↦ √(H y)) x =
      H₂ x / (2 * F) - H₁ x ^ 2 / (4 * F ^ 3) := by
    simpa only [F] using iteratedDeriv_two_sqrt hH hH₁ hHpos
  have hH2 : H₂ x = iteratedDeriv 2 H x := by
    symm
    simpa only [H, H₂] using iteratedDeriv_two_cylindricalSquareEnergy
      (continuous_uncurry_logPolarSlice hf) (continuous_logPolarX hf)
      (continuous_logPolarXX hf) (hasDerivAt_logPolarSlice_fst hf)
      (hasDerivAt_logPolarX_fst hf) (-Real.pi) Real.pi x
  have henergy : 2 * (Ex + Et) ≤ H₂ x := by
    rw [hH2]
    simpa only [H, Ex, Et] using logPolar_energy_second_deriv_ge hf x
  have hcs : H₁ x ^ 2 ≤ 4 * H x * Ex := by
    have h := logPolar_energy_deriv_sq_le hf x
    rw [(hH x).deriv] at h
    simpa only [H, H₁, Ex] using h
  have hp : H x ≤ Θ ^ 2 * Et := by
    simpa only [H, Θ, Et] using logPolar_poincare hf x hwidth
  have henergy' : 2 * (Ex + Et) * (2 * F ^ 2 * Θ ^ 2) ≤
      H₂ x * (2 * F ^ 2 * Θ ^ 2) :=
    mul_le_mul_of_nonneg_right henergy
      (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg F)) (sq_nonneg Θ))
  have hcs' : H₁ x ^ 2 * Θ ^ 2 ≤ (4 * H x * Ex) * Θ ^ 2 :=
    mul_le_mul_of_nonneg_right hcs (sq_nonneg Θ)
  have hp' : 4 * H x * H x ≤ 4 * H x * (Θ ^ 2 * Et) :=
    mul_le_mul_of_nonneg_left hp (mul_nonneg (by norm_num) hHpos.le)
  have hF4 : F ^ 4 = (H x) ^ 2 := by
    calc
      F ^ 4 = (F ^ 2) ^ 2 := by ring
      _ = (H x) ^ 2 := by rw [hF2]
  have hleft : 4 * F ^ 4 + H₁ x ^ 2 * Θ ^ 2 ≤
      4 * F ^ 2 * Θ ^ 2 * (Ex + Et) := by
    calc
      4 * F ^ 4 + H₁ x ^ 2 * Θ ^ 2 =
          4 * H x * H x + H₁ x ^ 2 * Θ ^ 2 := by rw [hF4]; ring
      _ ≤ 4 * H x * (Θ ^ 2 * Et) + (4 * H x * Ex) * Θ ^ 2 :=
        add_le_add hp' hcs'
      _ = 4 * F ^ 2 * Θ ^ 2 * (Ex + Et) := by rw [hF2]; ring
  have hright : 4 * F ^ 2 * Θ ^ 2 * (Ex + Et) ≤
      2 * H₂ x * F ^ 2 * Θ ^ 2 := by
    calc
      4 * F ^ 2 * Θ ^ 2 * (Ex + Et) =
          2 * (Ex + Et) * (2 * F ^ 2 * Θ ^ 2) := by ring
      _ ≤ H₂ x * (2 * F ^ 2 * Θ ^ 2) := henergy'
      _ = 2 * H₂ x * F ^ 2 * Θ ^ 2 := by ring
  have hpoly : 0 ≤
      2 * H₂ x * F ^ 2 * Θ ^ 2 - H₁ x ^ 2 * Θ ^ 2 - 4 * F ^ 4 := by
    nlinarith [hleft.trans hright]
  have hid : H₂ x / (2 * F) - H₁ x ^ 2 / (4 * F ^ 3) - F / Θ ^ 2 =
      (2 * H₂ x * F ^ 2 * Θ ^ 2 - H₁ x ^ 2 * Θ ^ 2 -
        4 * F ^ 4) / (4 * F ^ 3 * Θ ^ 2) := by
    field_simp [hFpos.ne', hΘpos.ne']
    ring
  change F / Θ ^ 2 ≤ iteratedDeriv 2 (fun y ↦ √(H y)) x
  rw [hsecond]
  apply le_of_sub_nonneg
  rw [hid]
  exact div_nonneg hpoly (by positivity)

/-- The square-root energy is convex wherever the logarithmic maximum is positive,
including the full-circle case omitted from the angular Poincaré inequality. -/
theorem logPolar_sqrt_energy_second_deriv_nonneg {f : ℂ → ℂ}
    (hf : IsEntire f) (x : ℝ)
    (hlog : 0 < Real.log (logarithmicMaximum f 1 (Real.exp x))) :
    0 ≤ iteratedDeriv 2
      (fun y ↦ √(cylindricalSquareEnergy
        (logPolarSlice f) (-Real.pi) Real.pi y)) x := by
  let H : ℝ → ℝ := cylindricalSquareEnergy
    (logPolarSlice f) (-Real.pi) Real.pi
  let H₁ : ℝ → ℝ := fun y ↦ ∫ θ in -Real.pi..Real.pi,
    2 * (logPolarSlice f y θ * logPolarX f y θ)
  let H₂ : ℝ → ℝ := fun y ↦ ∫ θ in -Real.pi..Real.pi,
    2 * (logPolarX f y θ ^ 2 + logPolarSlice f y θ * logPolarXX f y θ)
  let Ex : ℝ := ∫ θ in -Real.pi..Real.pi, logPolarX f x θ ^ 2
  let Et : ℝ := ∫ θ in -Real.pi..Real.pi, logPolarTheta f x θ ^ 2
  let F : ℝ := √(H x)
  have hH : ∀ y, HasDerivAt H (H₁ y) y := by
    intro y
    simpa only [H, H₁] using hasDerivAt_cylindricalSquareEnergy
      (continuous_uncurry_logPolarSlice hf) (continuous_logPolarX hf)
      (hasDerivAt_logPolarSlice_fst hf) (-Real.pi) Real.pi y
  have hH₁ : ∀ y, HasDerivAt H₁ (H₂ y) y := by
    intro y
    apply hasDerivAt_intervalIntegral_of_continuous_partial
        (F := fun s t ↦ 2 * (logPolarSlice f s t * logPolarX f s t))
        (F' := fun s t ↦
          2 * (logPolarX f s t ^ 2 + logPolarSlice f s t * logPolarXX f s t))
    · exact continuous_const.mul
        ((continuous_uncurry_logPolarSlice hf).mul (continuous_logPolarX hf))
    · exact continuous_const.mul
        ((continuous_logPolarX hf).pow 2 |>.add
          ((continuous_uncurry_logPolarSlice hf).mul (continuous_logPolarXX hf)))
    · intro s t
      simpa [pow_two] using
        ((hasDerivAt_logPolarSlice_fst hf s t).mul
          (hasDerivAt_logPolarX_fst hf s t)).const_mul (2 : ℝ)
  have hHpos : 0 < H x := by
    simpa only [H] using logPolar_energy_pos_of_log_max_pos hf x hlog
  have hFpos : 0 < F := Real.sqrt_pos.2 hHpos
  have hF2 : F ^ 2 = H x := Real.sq_sqrt hHpos.le
  have hsecond : iteratedDeriv 2 (fun y ↦ √(H y)) x =
      H₂ x / (2 * F) - H₁ x ^ 2 / (4 * F ^ 3) := by
    simpa only [F] using iteratedDeriv_two_sqrt hH hH₁ hHpos
  have hH2 : H₂ x = iteratedDeriv 2 H x := by
    symm
    simpa only [H, H₂] using iteratedDeriv_two_cylindricalSquareEnergy
      (continuous_uncurry_logPolarSlice hf) (continuous_logPolarX hf)
      (continuous_logPolarXX hf) (hasDerivAt_logPolarSlice_fst hf)
      (hasDerivAt_logPolarX_fst hf) (-Real.pi) Real.pi x
  have henergy : 2 * (Ex + Et) ≤ H₂ x := by
    rw [hH2]
    simpa only [H, Ex, Et] using logPolar_energy_second_deriv_ge hf x
  have hEt : 0 ≤ Et := by
    apply intervalIntegral.integral_nonneg (by linarith [Real.pi_pos])
    intro θ _
    exact sq_nonneg _
  have hcs : H₁ x ^ 2 ≤ 4 * H x * Ex := by
    have h := logPolar_energy_deriv_sq_le hf x
    rw [(hH x).deriv] at h
    simpa only [H, H₁, Ex] using h
  have hExH2 : 2 * Ex ≤ H₂ x := by linarith
  have hmul : 4 * H x * Ex ≤ 2 * H x * H₂ x := by
    have hfactor : 0 ≤ 2 * H x := mul_nonneg (by norm_num) hHpos.le
    have h := mul_le_mul_of_nonneg_left hExH2 hfactor
    nlinarith
  have hnum : 0 ≤ 2 * H₂ x * F ^ 2 - H₁ x ^ 2 := by
    rw [hF2]
    nlinarith [hcs.trans hmul]
  have hid : H₂ x / (2 * F) - H₁ x ^ 2 / (4 * F ^ 3) =
      (2 * H₂ x * F ^ 2 - H₁ x ^ 2) / (4 * F ^ 3) := by
    field_simp [hFpos.ne']
    ring
  change 0 ≤ iteratedDeriv 2 (fun y ↦ √(H y)) x
  rw [hsecond, hid]
  exact div_nonneg hnum (by positivity)

/-! ### Named logarithmic-polar energy fields -/

noncomputable def logPolarEnergy (f : ℂ → ℂ) (x : ℝ) : ℝ :=
  cylindricalSquareEnergy (logPolarSlice f) (-Real.pi) Real.pi x

noncomputable def logPolarEnergyFirst (f : ℂ → ℂ) (x : ℝ) : ℝ :=
  ∫ θ in -Real.pi..Real.pi, 2 * (logPolarSlice f x θ * logPolarX f x θ)

noncomputable def logPolarEnergySecond (f : ℂ → ℂ) (x : ℝ) : ℝ :=
  ∫ θ in -Real.pi..Real.pi,
    2 * (logPolarX f x θ ^ 2 + logPolarSlice f x θ * logPolarXX f x θ)

noncomputable def logPolarSqrtEnergy (f : ℂ → ℂ) (x : ℝ) : ℝ :=
  √(logPolarEnergy f x)

noncomputable def logPolarSqrtEnergyFirst (f : ℂ → ℂ) (x : ℝ) : ℝ :=
  logPolarEnergyFirst f x / (2 * logPolarSqrtEnergy f x)

noncomputable def logPolarSqrtEnergySecond (f : ℂ → ℂ) (x : ℝ) : ℝ :=
  logPolarEnergySecond f x / (2 * logPolarSqrtEnergy f x) -
    logPolarEnergyFirst f x ^ 2 / (4 * logPolarSqrtEnergy f x ^ 3)

theorem hasDerivAt_logPolarEnergy {f : ℂ → ℂ} (hf : IsEntire f) (x : ℝ) :
    HasDerivAt (logPolarEnergy f) (logPolarEnergyFirst f x) x := by
  exact hasDerivAt_cylindricalSquareEnergy
    (continuous_uncurry_logPolarSlice hf) (continuous_logPolarX hf)
    (hasDerivAt_logPolarSlice_fst hf) (-Real.pi) Real.pi x

theorem hasDerivAt_logPolarEnergyFirst {f : ℂ → ℂ}
    (hf : IsEntire f) (x : ℝ) :
    HasDerivAt (logPolarEnergyFirst f) (logPolarEnergySecond f x) x := by
  apply hasDerivAt_intervalIntegral_of_continuous_partial
      (F := fun s t ↦ 2 * (logPolarSlice f s t * logPolarX f s t))
      (F' := fun s t ↦
        2 * (logPolarX f s t ^ 2 + logPolarSlice f s t * logPolarXX f s t))
  · exact continuous_const.mul
      ((continuous_uncurry_logPolarSlice hf).mul (continuous_logPolarX hf))
  · exact continuous_const.mul
      ((continuous_logPolarX hf).pow 2 |>.add
        ((continuous_uncurry_logPolarSlice hf).mul (continuous_logPolarXX hf)))
  · intro s t
    simpa [pow_two] using
      ((hasDerivAt_logPolarSlice_fst hf s t).mul
        (hasDerivAt_logPolarX_fst hf s t)).const_mul (2 : ℝ)

theorem continuous_logPolarEnergy {f : ℂ → ℂ} (hf : IsEntire f) :
    Continuous (logPolarEnergy f) :=
  continuous_iff_continuousAt.mpr fun x ↦ (hasDerivAt_logPolarEnergy hf x).continuousAt

theorem continuous_logPolarEnergyFirst {f : ℂ → ℂ} (hf : IsEntire f) :
    Continuous (logPolarEnergyFirst f) :=
  continuous_iff_continuousAt.mpr fun x ↦
    (hasDerivAt_logPolarEnergyFirst hf x).continuousAt

theorem continuous_logPolarEnergySecond {f : ℂ → ℂ} (hf : IsEntire f) :
    Continuous (logPolarEnergySecond f) := by
  let K : ℝ → ℝ → ℝ := fun x θ ↦
    2 * (logPolarX f x θ ^ 2 + logPolarSlice f x θ * logPolarXX f x θ)
  have hK : Continuous (Function.uncurry K) := by
    exact continuous_const.mul
      ((continuous_logPolarX hf).pow 2 |>.add
        ((continuous_uncurry_logPolarSlice hf).mul (continuous_logPolarXX hf)))
  have hc := continuous_parametric_integral_of_continuous
    (f := K) (μ := volume) hK
      (isCompact_Icc : IsCompact (Set.Icc (-Real.pi) Real.pi))
  have heq : logPolarEnergySecond f =
      fun x ↦ ∫ θ in Set.Icc (-Real.pi) Real.pi, K x θ := by
    funext x
    unfold logPolarEnergySecond
    rw [intervalIntegral.integral_of_le (by linarith [Real.pi_pos])]
    rw [setIntegral_congr_set Ioc_ae_eq_Icc]
  rw [heq]
  exact hc

theorem continuous_logPolarSqrtEnergy {f : ℂ → ℂ} (hf : IsEntire f) :
    Continuous (logPolarSqrtEnergy f) := by
  exact Real.continuous_sqrt.comp (continuous_logPolarEnergy hf)

theorem hasDerivAt_logPolarSqrtEnergy {f : ℂ → ℂ}
    (hf : IsEntire f) {x : ℝ}
    (hlog : 0 < Real.log (logarithmicMaximum f 1 (Real.exp x))) :
    HasDerivAt (logPolarSqrtEnergy f) (logPolarSqrtEnergyFirst f x) x := by
  have hpos : 0 < logPolarEnergy f x := by
    simpa only [logPolarEnergy] using logPolar_energy_pos_of_log_max_pos hf x hlog
  unfold logPolarSqrtEnergyFirst logPolarSqrtEnergy
  exact (hasDerivAt_logPolarEnergy hf x).sqrt hpos.ne'

theorem hasDerivAt_logPolarSqrtEnergyFirst {f : ℂ → ℂ}
    (hf : IsEntire f) {x : ℝ}
    (hlog : 0 < Real.log (logarithmicMaximum f 1 (Real.exp x))) :
    HasDerivAt (logPolarSqrtEnergyFirst f)
      (logPolarSqrtEnergySecond f x) x := by
  have hpos : 0 < logPolarEnergy f x := by
    simpa only [logPolarEnergy] using logPolar_energy_pos_of_log_max_pos hf x hlog
  unfold logPolarSqrtEnergyFirst logPolarSqrtEnergySecond logPolarSqrtEnergy
  exact hasDerivAt_sqrt_first_field
    (hasDerivAt_logPolarEnergy hf) (hasDerivAt_logPolarEnergyFirst hf) hpos

theorem logPolarSqrtEnergySecond_eq_iteratedDeriv {f : ℂ → ℂ}
    (hf : IsEntire f) {x : ℝ}
    (hlog : 0 < Real.log (logarithmicMaximum f 1 (Real.exp x))) :
    logPolarSqrtEnergySecond f x =
      iteratedDeriv 2 (logPolarSqrtEnergy f) x := by
  have hpos : 0 < logPolarEnergy f x := by
    simpa only [logPolarEnergy] using logPolar_energy_pos_of_log_max_pos hf x hlog
  symm
  unfold logPolarSqrtEnergy logPolarSqrtEnergySecond
  exact iteratedDeriv_two_sqrt
    (hasDerivAt_logPolarEnergy hf) (hasDerivAt_logPolarEnergyFirst hf) hpos

theorem logPolarSqrtEnergySecond_nonneg {f : ℂ → ℂ}
    (hf : IsEntire f) {x : ℝ}
    (hlog : 0 < Real.log (logarithmicMaximum f 1 (Real.exp x))) :
    0 ≤ logPolarSqrtEnergySecond f x := by
  rw [logPolarSqrtEnergySecond_eq_iteratedDeriv hf hlog]
  unfold logPolarSqrtEnergy logPolarEnergy
  exact logPolar_sqrt_energy_second_deriv_nonneg hf x hlog

/-- The reciprocal angular width with full circles removed.  A full circle contributes only
the fixed coefficient `(2π)⁻¹`, which is added back after the Carleman estimate. -/
noncomputable def reducedReciprocalLogWidth (f : ℂ → ℂ) (x : ℝ) : ℝ :=
  if angularWidth (exceptionalSet f 1) (Real.exp x) < 2 * Real.pi then
    (angularWidth (exceptionalSet f 1) (Real.exp x))⁻¹ else 0

theorem measurable_reducedReciprocalLogWidth {f : ℂ → ℂ}
    (hf : Continuous f) : Measurable (reducedReciprocalLogWidth f) := by
  unfold reducedReciprocalLogWidth
  apply Measurable.ite
  · exact measurableSet_lt
      ((measurable_angularWidth (measurableSet_exceptionalSet hf 1)).comp
        Real.measurable_exp) measurable_const
  · exact (show Measurable (fun x ↦
      angularWidth (exceptionalSet f 1) (Real.exp x)) from
        (measurable_angularWidth (measurableSet_exceptionalSet hf 1)).comp
          Real.measurable_exp).inv
  · exact measurable_const

theorem reducedReciprocalLogWidth_nonneg {f : ℂ → ℂ} {x : ℝ}
    (hΘ : 0 < angularWidth (exceptionalSet f 1) (Real.exp x)) :
    0 ≤ reducedReciprocalLogWidth f x := by
  unfold reducedReciprocalLogWidth
  split_ifs
  · exact inv_nonneg.mpr hΘ.le
  · exact le_rfl

/-- Restoring the omitted full-circle coefficient costs only the fixed quantity
`(2π)⁻¹`. -/
theorem reciprocal_log_width_le_reduced_add {f : ℂ → ℂ} (x : ℝ) :
    (angularWidth (exceptionalSet f 1) (Real.exp x))⁻¹ ≤
      reducedReciprocalLogWidth f x + (2 * Real.pi)⁻¹ := by
  by_cases hΘ : angularWidth (exceptionalSet f 1) (Real.exp x) < 2 * Real.pi
  · unfold reducedReciprocalLogWidth
    rw [if_pos hΘ]
    exact le_add_of_nonneg_right (inv_nonneg.mpr (by positivity))
  · have heq : angularWidth (exceptionalSet f 1) (Real.exp x) = 2 * Real.pi :=
      le_antisymm (angularWidth_le_two_pi _ _) (le_of_not_gt hΘ)
    unfold reducedReciprocalLogWidth
    rw [if_neg hΘ, heq, zero_add]

/-- Reciprocal angular width after the logarithmic change of radial variable. -/
noncomputable def logReciprocalAngularWidth (f : ℂ → ℂ) (x : ℝ) : ℝ :=
  (angularWidth (exceptionalSet f 1) (Real.exp x))⁻¹

theorem measurable_logReciprocalAngularWidth {f : ℂ → ℂ}
    (hf : Continuous f) : Measurable (logReciprocalAngularWidth f) := by
  unfold logReciprocalAngularWidth
  exact ((measurable_angularWidth (measurableSet_exceptionalSet hf 1)).comp
    Real.measurable_exp).inv

/-- Finite exceptional area in polar coordinates remains integrable after the logarithmic
change of variables. -/
theorem integrableOn_log_exceptional_area_density {f : ℂ → ℂ}
    (hf : Continuous f) (harea : HasFiniteArea f 1) (X : ℝ) :
    IntegrableOn (fun x ↦ Real.exp x ^ 2 *
      angularWidth (exceptionalSet f 1) (Real.exp x)) (Set.Ioi X) := by
  let g : ℝ → ℝ := fun r ↦ r * angularWidth (exceptionalSet f 1) r
  have hg : IntegrableOn g (Set.Ioi (Real.exp X)) := by
    apply (integrableOn_exceptional_radius_mul_angularWidth hf harea).mono_set
    intro r hr
    exact Real.exp_pos X |>.trans hr
  have h := (integrableOn_comp_exp_Ioi g X).mpr hg
  simpa only [g, smul_eq_mul, pow_two, mul_assoc] using h

theorem reducedReciprocalLogWidth_curvature {f : ℂ → ℂ}
    (hf : IsEntire f) {x : ℝ}
    (hlog : 0 < Real.log (logarithmicMaximum f 1 (Real.exp x))) :
    reducedReciprocalLogWidth f x ^ 2 * logPolarSqrtEnergy f x ≤
      logPolarSqrtEnergySecond f x := by
  by_cases hw : angularWidth (exceptionalSet f 1) (Real.exp x) < 2 * Real.pi
  · have h := logPolar_sqrt_energy_second_deriv_ge hf x hlog hw
    unfold reducedReciprocalLogWidth
    rw [if_pos hw]
    rw [logPolarSqrtEnergySecond_eq_iteratedDeriv hf hlog]
    unfold logPolarSqrtEnergy logPolarEnergy
    simpa only [inv_pow, div_eq_mul_inv, mul_comm] using h
  · unfold reducedReciprocalLogWidth
    rw [if_neg hw, zero_pow two_ne_zero, zero_mul]
    exact logPolarSqrtEnergySecond_nonneg hf hlog

theorem continuousOn_logPolarSqrtEnergyFirst {f : ℂ → ℂ}
    (hf : IsEntire f) {a b : ℝ}
    (hlog : ∀ x ∈ Set.Icc a b,
      0 < Real.log (logarithmicMaximum f 1 (Real.exp x))) :
    ContinuousOn (logPolarSqrtEnergyFirst f) (Set.Icc a b) := by
  intro x hx
  exact (hasDerivAt_logPolarSqrtEnergyFirst hf (hlog x hx)).continuousAt.continuousWithinAt

theorem continuousOn_logPolarSqrtEnergySecond {f : ℂ → ℂ}
    (hf : IsEntire f) {a b : ℝ}
    (hlog : ∀ x ∈ Set.Icc a b,
      0 < Real.log (logarithmicMaximum f 1 (Real.exp x))) :
    ContinuousOn (logPolarSqrtEnergySecond f) (Set.Icc a b) := by
  unfold logPolarSqrtEnergySecond
  have hroot : ∀ x ∈ Set.Icc a b, logPolarSqrtEnergy f x ≠ 0 := by
    intro x hx
    unfold logPolarSqrtEnergy
    apply (Real.sqrt_pos.2 ?_).ne'
    simpa only [logPolarEnergy] using logPolar_energy_pos_of_log_max_pos hf x (hlog x hx)
  exact ((continuous_logPolarEnergySecond hf).continuousOn.div
      ((continuous_logPolarSqrtEnergy hf).continuousOn.const_mul 2)
      (fun x hx ↦ mul_ne_zero two_ne_zero (hroot x hx))).sub
    (((continuous_logPolarEnergyFirst hf).continuousOn.pow 2).div
      (((continuous_logPolarSqrtEnergy hf).continuousOn.pow 3).const_mul 4)
      (fun x hx ↦ mul_ne_zero (by norm_num) (pow_ne_zero 3 (hroot x hx))))

/-- The scalar Carleman lemma applied to Camera's named log-polar energy fields. -/
theorem intervalIntegral_reducedReciprocalLogWidth_carleman
    {f : ℂ → ℂ} (hf : IsEntire f) {a b : ℝ} (hab : a ≤ b)
    (hlog : ∀ x ∈ Set.Icc a b,
      0 < Real.log (logarithmicMaximum f 1 (Real.exp x)))
    (hfirst : ∀ x ∈ Set.Icc a b, 0 < logPolarSqrtEnergyFirst f x) :
    IntervalIntegrable (reducedReciprocalLogWidth f) volume a b ∧
      2 * ∫ x in a..b, reducedReciprocalLogWidth f x ≤
        (Real.log (logPolarSqrtEnergy f b) -
          Real.log (logPolarSqrtEnergy f a)) +
        (Real.log (logPolarSqrtEnergyFirst f b) -
          Real.log (logPolarSqrtEnergyFirst f a)) := by
  apply intervalIntegral_carleman_log_bound hab
  · intro x hx
    exact hasDerivAt_logPolarSqrtEnergy hf (hlog x hx)
  · intro x hx
    exact hasDerivAt_logPolarSqrtEnergyFirst hf (hlog x hx)
  · exact (continuous_logPolarSqrtEnergy hf).continuousOn
  · exact continuousOn_logPolarSqrtEnergyFirst hf hlog
  · exact continuousOn_logPolarSqrtEnergySecond hf hlog
  · intro x hx
    unfold logPolarSqrtEnergy
    apply Real.sqrt_pos.2
    simpa only [logPolarEnergy] using logPolar_energy_pos_of_log_max_pos hf x (hlog x hx)
  · exact hfirst
  · exact (measurable_reducedReciprocalLogWidth hf.continuous).aestronglyMeasurable
  · intro x hx
    apply reducedReciprocalLogWidth_nonneg
    apply angularWidth_exceptional_pos_of_one_lt_logarithmicMaximum hf.continuous
      (Real.exp_pos x)
    exact (Real.log_pos_iff Real.posLog_nonneg).mp (hlog x hx)
  · intro x hx
    exact reducedReciprocalLogWidth_curvature hf (hlog x hx)

/-- Adding back full circles upgrades the reduced Carleman estimate to the true reciprocal
angular width at a fixed additive cost. -/
theorem intervalIntegral_logReciprocalAngularWidth_carleman
    {f : ℂ → ℂ} (hf : IsEntire f) {a b : ℝ} (hab : a ≤ b)
    (hlog : ∀ x ∈ Set.Icc a b,
      0 < Real.log (logarithmicMaximum f 1 (Real.exp x)))
    (hfirst : ∀ x ∈ Set.Icc a b, 0 < logPolarSqrtEnergyFirst f x) :
    IntervalIntegrable (logReciprocalAngularWidth f) volume a b ∧
      2 * ∫ x in a..b, logReciprocalAngularWidth f x ≤
        (Real.log (logPolarSqrtEnergy f b) -
          Real.log (logPolarSqrtEnergy f a)) +
        (Real.log (logPolarSqrtEnergyFirst f b) -
          Real.log (logPolarSqrtEnergyFirst f a)) +
        2 * (b - a) * (2 * Real.pi)⁻¹ := by
  obtain ⟨hredint, hredbound⟩ :=
    intervalIntegral_reducedReciprocalLogWidth_carleman hf hab hlog hfirst
  let k : ℝ := (2 * Real.pi)⁻¹
  have hk : 0 ≤ k := inv_nonneg.mpr (by positivity)
  have hdomint : IntervalIntegrable
      (fun x ↦ reducedReciprocalLogWidth f x + k) volume a b :=
    hredint.add intervalIntegrable_const
  have hactual_nonneg : ∀ x, 0 ≤ logReciprocalAngularWidth f x := by
    intro x
    exact inv_nonneg.mpr (angularWidth_nonneg _ _)
  have hdom : ∀ x ∈ Set.Icc a b,
      logReciprocalAngularWidth f x ≤ reducedReciprocalLogWidth f x + k := by
    intro x hx
    simpa only [logReciprocalAngularWidth, k] using
      reciprocal_log_width_le_reduced_add (f := f) x
  have hactint : IntervalIntegrable (logReciprocalAngularWidth f) volume a b := by
    apply hdomint.mono_fun'
    · exact (measurable_logReciprocalAngularWidth hf.continuous).aestronglyMeasurable.restrict
    · filter_upwards [ae_restrict_mem measurableSet_uIoc] with x hx
      have hx' : x ∈ Set.Icc a b := by
        simpa [uIcc_of_le hab] using uIoc_subset_uIcc hx
      rw [Real.norm_eq_abs, abs_of_nonneg (hactual_nonneg x)]
      exact hdom x hx'
  have hmono : (∫ x in a..b, logReciprocalAngularWidth f x) ≤
      ∫ x in a..b, reducedReciprocalLogWidth f x + k := by
    apply intervalIntegral.integral_mono_on hab hactint hdomint
    exact hdom
  have hkint : IntervalIntegrable (fun _ : ℝ ↦ k) volume a b := intervalIntegrable_const
  have heval : (∫ x in a..b, reducedReciprocalLogWidth f x + k) =
      (∫ x in a..b, reducedReciprocalLogWidth f x) + (b - a) * k := by
    rw [intervalIntegral.integral_add hredint hkint,
      intervalIntegral.integral_const, smul_eq_mul]
  refine ⟨hactint, ?_⟩
  rw [heval] at hmono
  dsimp only [k] at hmono ⊢
  linarith

/-- The smooth logarithmic slice is bounded by the fifth power of the positive logarithm of
the maximum modulus on the same circle. -/
theorem logPolarSlice_le_posLog_maximumModulus_pow_five {f : ℂ → ℂ}
    (hf : IsEntire f) (x θ : ℝ) :
    logPolarSlice f x θ ≤ (Real.posLog (maximumModulus f (Real.exp x))) ^ 5 := by
  have hnorm : ‖f (polarPoint (Real.exp x) θ)‖ ≤ maximumModulus f (Real.exp x) := by
    apply norm_le_maximumModulus hf.continuous (Real.exp_pos x).le
    simp [polarPoint, Complex.norm_mul, abs_of_pos (Real.exp_pos x)]
  have hposlog := Real.posLog_le_posLog (norm_nonneg _) hnorm
  have hpow : (Real.posLog ‖f (polarPoint (Real.exp x) θ)‖) ^ 5 ≤
      (Real.posLog (maximumModulus f (Real.exp x))) ^ 5 := by
    gcongr
    exact Real.posLog_nonneg
  rw [logPolarSlice, logPolarLevel, Function.comp_apply, exp_logPolarPoint,
    harmonicLogarithmicLevel, smoothPositivePart_eq_max]
  simpa only [Real.posLog_apply, max_comm] using hpow

/-- The square energy is at most `2π` times the tenth power of the positive logarithmic
maximum. -/
theorem logPolarEnergy_le_posLog_maximumModulus {f : ℂ → ℂ}
    (hf : IsEntire f) (x : ℝ) :
    logPolarEnergy f x ≤
      2 * Real.pi * (Real.posLog (maximumModulus f (Real.exp x))) ^ 10 := by
  let C : ℝ := (Real.posLog (maximumModulus f (Real.exp x))) ^ 10
  have hcont : Continuous (fun θ ↦ logPolarSlice f x θ ^ 2) :=
    (contDiff_logPolarSlice_snd hf x).continuous.pow 2
  have hconst : IntervalIntegrable (fun _ : ℝ ↦ C) volume (-Real.pi) Real.pi :=
    intervalIntegrable_const
  have hmono : ∀ θ ∈ Set.Icc (-Real.pi) Real.pi,
      logPolarSlice f x θ ^ 2 ≤ C := by
    intro θ hθ
    have hsnonneg : 0 ≤ logPolarSlice f x θ := smoothPositivePart_nonneg _
    have hCbase : 0 ≤ Real.posLog (maximumModulus f (Real.exp x)) := Real.posLog_nonneg
    have hs := logPolarSlice_le_posLog_maximumModulus_pow_five hf x θ
    have hsq := (sq_le_sq₀ hsnonneg (pow_nonneg hCbase 5)).mpr hs
    dsimp only [C]
    nlinarith [hsq]
  unfold logPolarEnergy cylindricalSquareEnergy
  calc
    (∫ θ in -Real.pi..Real.pi, logPolarSlice f x θ ^ 2) ≤
        ∫ _ in -Real.pi..Real.pi, C := by
      apply intervalIntegral.integral_mono_on (by linarith [Real.pi_pos])
      · exact hcont.intervalIntegrable (μ := volume) (-Real.pi) Real.pi
      · exact hconst
      · exact hmono
    _ = 2 * Real.pi * (Real.posLog (maximumModulus f (Real.exp x))) ^ 10 := by
      rw [intervalIntegral.integral_const]
      dsimp only [C]
      ring

theorem logPolarSqrtEnergy_le_posLog_maximumModulus {f : ℂ → ℂ}
    (hf : IsEntire f) (x : ℝ) :
    logPolarSqrtEnergy f x ≤
      √(2 * Real.pi) * (Real.posLog (maximumModulus f (Real.exp x))) ^ 5 := by
  have h := Real.sqrt_le_sqrt (logPolarEnergy_le_posLog_maximumModulus hf x)
  unfold logPolarSqrtEnergy
  calc
    √(logPolarEnergy f x) ≤
        √(2 * Real.pi * (Real.posLog (maximumModulus f (Real.exp x))) ^ 10) := h
    _ = √(2 * Real.pi) *
        √((Real.posLog (maximumModulus f (Real.exp x))) ^ 10) := by
      rw [Real.sqrt_mul (by positivity : 0 ≤ 2 * Real.pi)]
    _ = √(2 * Real.pi) *
        (Real.posLog (maximumModulus f (Real.exp x))) ^ 5 := by
      rw [show (Real.posLog (maximumModulus f (Real.exp x))) ^ 10 =
          ((Real.posLog (maximumModulus f (Real.exp x))) ^ 5) ^ 2 by ring,
        Real.sqrt_sq_eq_abs, abs_of_nonneg (pow_nonneg Real.posLog_nonneg 5)]

/-- The square-root energy dominates the fifth power of the Nevanlinna proximity. -/
theorem sqrt_two_pi_mul_proximity_pow_five_le_logPolarSqrtEnergy
    {f : ℂ → ℂ} (hf : IsEntire f) (x : ℝ) :
    √(2 * Real.pi) * (ValueDistribution.proximity f ⊤ (Real.exp x)) ^ 5 ≤
      logPolarSqrtEnergy f x := by
  let I : Set ℝ := Set.Ioc (-Real.pi) Real.pi
  let u : ℝ → ℝ := fun θ ↦ Real.posLog ‖f (polarPoint (Real.exp x) θ)‖
  let m : ℝ := ValueDistribution.proximity f ⊤ (Real.exp x)
  let A : ℝ := ∫ θ in I, logPolarSlice f x θ
  let H : ℝ := logPolarEnergy f x
  let L : ℝ := 2 * Real.pi
  have hucont : Continuous u := by
    have hp : Continuous (polarPoint (Real.exp x)) := by
      have h : Continuous (fun θ : ℝ ↦
          (Real.exp x : ℂ) * (Real.cos θ + Real.sin θ * Complex.I)) := by fun_prop
      convert h using 1
      funext θ
      simp [polarPoint]
    exact Real.continuous_posLog.comp ((hf.continuous.comp hp).norm)
  have hslice : ∀ θ, u θ ^ 5 = logPolarSlice f x θ := by
    intro θ
    dsimp only [u]
    rw [logPolarSlice, logPolarLevel, Function.comp_apply, exp_logPolarPoint,
      harmonicLogarithmicLevel, smoothPositivePart_eq_max]
    simp only [Real.posLog_apply, max_comm]
  have hJ := angular_set_average_pow_five_le hucont
    (fun _ ↦ Real.posLog_nonneg)
  have hmean : m ^ 5 ≤ L⁻¹ * A := by
    have hm : m = L⁻¹ * ∫ θ in I, u θ := by
      dsimp only [m, L, I, u]
      exact proximity_top_eq_polar_posLog_set_average f (Real.exp x)
    have hpowint : (∫ θ in I, u θ ^ 5) = A := by
      apply setIntegral_congr_fun measurableSet_Ioc
      intro θ hθ
      exact hslice θ
    calc
      m ^ 5 = (L⁻¹ * ∫ θ in I, u θ) ^ 5 := by rw [← hm]
      _ ≤ L⁻¹ * ∫ θ in I, u θ ^ 5 := by
        simpa only [L, I] using hJ
      _ = L⁻¹ * A := by rw [hpowint]
  have hL : 0 < L := mul_pos (by norm_num) Real.pi_pos
  have hLA : L * m ^ 5 ≤ A := by
    have := mul_le_mul_of_nonneg_left hmean hL.le
    calc
      L * m ^ 5 ≤ L * (L⁻¹ * A) := this
      _ = A := by field_simp
  have hA : 0 ≤ A := by
    dsimp only [A, I]
    apply integral_nonneg_of_ae
    exact ae_of_all _ fun θ ↦ smoothPositivePart_nonneg _
  have hcs : A ^ 2 ≤ L * H := by
    have hraw := setIntegral_sq_le_measure_mul_setIntegral_sq
      (μ := volume) (s := I) (g := fun θ ↦ logPolarSlice f x θ)
      (ne_of_lt measure_Ioc_lt_top)
      (contDiff_logPolarSlice_snd hf x).continuous.aestronglyMeasurable.restrict
      ((contDiff_logPolarSlice_snd hf x).continuous.pow 2
        |>.integrableOn_Icc.mono_set fun θ hθ ↦ ⟨hθ.1.le, hθ.2⟩)
      (ae_of_all _ fun θ ↦ smoothPositivePart_nonneg _)
    have hmeasure : volume.real I = L := by
      dsimp only [I, L]
      exact volumeReal_Ioc_neg_pi_pi
    have henergy : (∫ θ in I, logPolarSlice f x θ ^ 2) = H := by
      dsimp only [H, logPolarEnergy, cylindricalSquareEnergy, I]
      rw [intervalIntegral.integral_of_le (by linarith [Real.pi_pos])]
    simpa only [A, hmeasure, henergy] using hraw
  have hmnonneg : 0 ≤ m := ValueDistribution.proximity_nonneg (f := f) (Real.exp x)
  have hsqrtL : √L ^ 2 = L := Real.sq_sqrt hL.le
  have hsquare : (√L * m ^ 5) ^ 2 ≤ H := by
    have hLm : 0 ≤ L * m ^ 5 := mul_nonneg hL.le (pow_nonneg hmnonneg 5)
    have hsqLA : (L * m ^ 5) ^ 2 ≤ A ^ 2 :=
      (sq_le_sq₀ hLm hA).mpr hLA
    have hmul : L ^ 2 * (m ^ 5) ^ 2 ≤ L * H := by
      nlinarith [hcs, hsqLA]
    have hcancel : L * (m ^ 5) ^ 2 ≤ H := by
      nlinarith [mul_nonneg hL.le (sq_nonneg (m ^ 5))]
    calc
      (√L * m ^ 5) ^ 2 = L * (m ^ 5) ^ 2 := by nlinarith
      _ ≤ H := hcancel
  have hleft : 0 ≤ √L * m ^ 5 :=
    mul_nonneg (Real.sqrt_nonneg _) (pow_nonneg hmnonneg 5)
  have hH : 0 ≤ H := by
    dsimp only [H, logPolarEnergy, cylindricalSquareEnergy]
    apply intervalIntegral.integral_nonneg (by linarith [Real.pi_pos])
    intro θ hθ
    exact sq_nonneg _
  have hfinal : √L * m ^ 5 ≤ √H := by
    apply (sq_le_sq₀ hleft (Real.sqrt_nonneg _)).mp
    rw [Real.sq_sqrt hH]
    exact hsquare
  simpa only [L, m, H, logPolarSqrtEnergy] using hfinal

/-- On a logarithmic tail, the square-root energy is bounded away from zero. -/
theorem eventually_uniform_pos_logPolarSqrtEnergy {f : ℂ → ℂ}
    (hf : IsNonconstantEntire f) :
    ∃ X C : ℝ, 0 < C ∧
      (∀ x, X ≤ x →
        0 < Real.log (logarithmicMaximum f 1 (Real.exp x))) ∧
      ∀ x, X ≤ x → C ≤ logPolarSqrtEnergy f x := by
  obtain ⟨R, hR, hlog⟩ := eventually_pos_log_logarithmicMaximum_one hf
  let X : ℝ := Real.log R
  let m₀ : ℝ := ValueDistribution.proximity f ⊤ R
  let C : ℝ := √(2 * Real.pi) * m₀ ^ 5
  have hB : 1 < logarithmicMaximum f 1 R :=
    (Real.log_pos_iff Real.posLog_nonneg).mp (hlog R le_rfl)
  have hm₀ : 0 < m₀ := by
    dsimp only [m₀]
    exact proximity_top_pos_of_one_lt_logarithmicMaximum hf.1 hR hB
  have hC : 0 < C := mul_pos (Real.sqrt_pos.2 (by positivity)) (pow_pos hm₀ 5)
  refine ⟨X, C, hC, ?_, ?_⟩
  · intro x hx
    apply hlog (Real.exp x)
    have := Real.exp_le_exp.mpr hx
    simpa only [X, Real.exp_log hR] using this
  · intro x hx
    have hrx : R ≤ Real.exp x := by
      have := Real.exp_le_exp.mpr hx
      simpa only [X, Real.exp_log hR] using this
    have hm : m₀ ≤ ValueDistribution.proximity f ⊤ (Real.exp x) := by
      apply proximity_top_monoOn_of_entire hf.1 hR (Real.exp_pos x) hrx
    have hpow : m₀ ^ 5 ≤ (ValueDistribution.proximity f ⊤ (Real.exp x)) ^ 5 := by
      gcongr
    calc
      C ≤ √(2 * Real.pi) *
          (ValueDistribution.proximity f ⊤ (Real.exp x)) ^ 5 := by
        exact mul_le_mul_of_nonneg_left hpow (Real.sqrt_nonneg _)
      _ ≤ logPolarSqrtEnergy f x :=
        sqrt_two_pi_mul_proximity_pow_five_le_logPolarSqrtEnergy hf.1 x

/-- Finite exceptional area forces the square of the reduced reciprocal width to be
nonintegrable on every logarithmic tail where the logarithmic maximum is positive. -/
theorem not_integrableOn_reducedReciprocalLogWidth_sq {f : ℂ → ℂ}
    (hf : IsEntire f) (harea : HasFiniteArea f 1) {X : ℝ}
    (hlog : ∀ x, X < x →
      0 < Real.log (logarithmicMaximum f 1 (Real.exp x))) :
    ¬ IntegrableOn (fun x ↦ reducedReciprocalLogWidth f x ^ 2) (Set.Ioi X) := by
  intro hqint
  let ν : Measure ℝ := volume.restrict (Set.Ioi X)
  let Θ : ℝ → ℝ := fun x ↦ angularWidth (exceptionalSet f 1) (Real.exp x)
  let q : ℝ → ℝ := reducedReciprocalLogWidth f
  let area : ℝ → ℝ := fun x ↦ Real.exp x ^ 2 * Θ x
  let L : ℝ := 2 * Real.pi
  let K : ℝ := Real.exp X ^ 2 * L
  let S : Set ℝ := {x | X < x ∧ Θ x = L}
  let T : Set ℝ := {x | X < x ∧ Θ x < L}
  have hL : 0 < L := mul_pos (by norm_num) Real.pi_pos
  have hK : 0 < K := mul_pos (sq_pos_of_pos (Real.exp_pos X)) hL
  have hareaint : Integrable area ν := by
    simpa only [area, Θ, ν, IntegrableOn] using
      integrableOn_log_exceptional_area_density hf.continuous harea X
  have hSfinite : ν S ≠ ∞ := by
    have hscaled : Integrable (fun x ↦ K⁻¹ * area x) ν := hareaint.const_mul K⁻¹
    have hnonneg : 0 ≤ᵐ[ν] fun x ↦ K⁻¹ * area x := by
      exact ae_of_all _ fun x ↦ mul_nonneg (inv_nonneg.mpr hK.le)
        (mul_nonneg (sq_nonneg _) (angularWidth_nonneg _ _))
    have hmeasure := hscaled.measure_le_integral hnonneg (s := S) (by
      intro x hx
      have hxexp : Real.exp X ≤ Real.exp x := Real.exp_le_exp.mpr hx.1.le
      have hsq : Real.exp X ^ 2 ≤ Real.exp x ^ 2 := by gcongr
      have harea : K ≤ area x := by
        dsimp only [K, area]
        rw [show Θ x = L from hx.2]
        exact mul_le_mul_of_nonneg_right hsq hL.le
      rw [← div_eq_inv_mul, (le_div_iff₀ hK)]
      simpa only [one_mul] using harea)
    exact ne_of_lt (hmeasure.trans_lt ENNReal.ofReal_lt_top)
  have hqscaled : Integrable (fun x ↦ L ^ 2 * q x ^ 2) ν := by
    have hsquare : Integrable (fun x ↦ q x ^ 2) ν := by
      simpa only [q, ν, IntegrableOn] using hqint
    exact hsquare.const_mul (L ^ 2)
  have hTfinite : ν T ≠ ∞ := by
    have hnonneg : 0 ≤ᵐ[ν] fun x ↦ L ^ 2 * q x ^ 2 :=
      ae_of_all _ fun x ↦ mul_nonneg (sq_nonneg _) (sq_nonneg _)
    have hmeasure := hqscaled.measure_le_integral hnonneg (s := T) (by
      intro x hx
      have hΘpos : 0 < Θ x := by
        dsimp only [Θ]
        apply angularWidth_exceptional_pos_of_one_lt_logarithmicMaximum hf.continuous
          (Real.exp_pos x)
        exact (Real.log_pos_iff Real.posLog_nonneg).mp (hlog x hx.1)
      have hΘle : Θ x ≤ L := by
        dsimp only [Θ, L]
        exact angularWidth_le_two_pi _ _
      have hsq : Θ x ^ 2 ≤ L ^ 2 :=
        (sq_le_sq₀ hΘpos.le hL.le).mpr hΘle
      have hqeq : q x = (Θ x)⁻¹ := by
        dsimp only [q]
        unfold reducedReciprocalLogWidth
        rw [if_pos hx.2]
      rw [hqeq, show L ^ 2 * (Θ x)⁻¹ ^ 2 = L ^ 2 / Θ x ^ 2 by
        field_simp]
      exact (le_div_iff₀ (sq_pos_of_pos hΘpos)).mpr (by simpa using hsq))
    exact ne_of_lt (hmeasure.trans_lt ENNReal.ofReal_lt_top)
  have hST : S ∪ T = Set.Ioi X := by
    ext x
    constructor
    · rintro (hx | hx) <;> exact hx.1
    · intro hx
      by_cases hlt : Θ x < L
      · exact Or.inr ⟨hx, hlt⟩
      · exact Or.inl ⟨hx, le_antisymm (by
          dsimp only [Θ, L]
          exact angularWidth_le_two_pi _ _) (le_of_not_gt hlt)⟩
  have htop : ν (S ∪ T) = ∞ := by
    rw [hST]
    dsimp only [ν]
    rw [Measure.restrict_apply measurableSet_Ioi, Set.inter_self, Real.volume_Ioi]
  have hle := measure_union_le S T (μ := ν)
  rw [htop] at hle
  exact (ENNReal.add_ne_top.mpr ⟨hSfinite, hTfinite⟩) (top_unique hle)

/-- The energy slope is eventually strictly positive.  Uniform positivity of the energy and
finite area rule out a nonpositive convex slope. -/
theorem eventually_pos_logPolarSqrtEnergyFirst {f : ℂ → ℂ}
    (hf : IsNonconstantEntire f) (harea : HasFiniteArea f 1) :
    ∃ Y : ℝ,
      (∀ x, Y ≤ x →
        0 < Real.log (logarithmicMaximum f 1 (Real.exp x))) ∧
      ∀ x, Y ≤ x → 0 < logPolarSqrtEnergyFirst f x := by
  obtain ⟨X, C, hC, hlog, hFlower⟩ := eventually_uniform_pos_logPolarSqrtEnergy hf
  have hmono : MonotoneOn (logPolarSqrtEnergyFirst f) (Set.Ici X) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici X)
    · intro x hx
      exact (hasDerivAt_logPolarSqrtEnergyFirst hf.1
        (hlog x hx)).continuousAt.continuousWithinAt
    · intro x hx
      have hxX : X ≤ x := interior_subset hx
      exact (hasDerivAt_logPolarSqrtEnergyFirst hf.1
        (hlog x hxX)).differentiableAt.differentiableWithinAt
    · intro x hx
      have hxX : X ≤ x := interior_subset hx
      rw [(hasDerivAt_logPolarSqrtEnergyFirst hf.1 (hlog x hxX)).deriv]
      exact logPolarSqrtEnergySecond_nonneg hf.1 (hlog x hxX)
  have hex : ∃ y, X ≤ y ∧ 0 < logPolarSqrtEnergyFirst f y := by
    by_contra hnot
    push_neg at hnot
    have hslope_nonpos : ∀ y, X ≤ y → logPolarSqrtEnergyFirst f y ≤ 0 := hnot
    let q : ℝ → ℝ := reducedReciprocalLogWidth f
    have hqmeas : AEStronglyMeasurable q volume :=
      (measurable_reducedReciprocalLogWidth hf.1.continuous).aestronglyMeasurable
    have hlocal : ∀ b, X ≤ b →
        IntervalIntegrable (fun x ↦ q x ^ 2) volume X b := by
      intro b hb
      have hlogI : ∀ x ∈ Set.Icc X b,
          0 < Real.log (logarithmicMaximum f 1 (Real.exp x)) :=
        fun x hx ↦ hlog x hx.1
      have hF2cont := continuousOn_logPolarSqrtEnergySecond hf.1 hlogI
      have hdomint : IntervalIntegrable
          (fun x ↦ C⁻¹ * logPolarSqrtEnergySecond f x) volume X b := by
        apply ContinuousOn.intervalIntegrable
        rw [uIcc_of_le hb]
        exact continuousOn_const.mul hF2cont
      apply hdomint.mono_fun'
      · exact (hqmeas.pow 2).restrict
      · filter_upwards [ae_restrict_mem measurableSet_uIoc] with x hx
        have hx' : x ∈ Set.Icc X b := by
          simpa [uIcc_of_le hb] using uIoc_subset_uIcc hx
        have hqnonneg : 0 ≤ q x := by
          dsimp only [q]
          apply reducedReciprocalLogWidth_nonneg
          apply angularWidth_exceptional_pos_of_one_lt_logarithmicMaximum hf.1.continuous
            (Real.exp_pos x)
          exact (Real.log_pos_iff Real.posLog_nonneg).mp (hlogI x hx')
        have hCF : C * q x ^ 2 ≤
            q x ^ 2 * logPolarSqrtEnergy f x := by
          simpa only [mul_comm] using
            mul_le_mul_of_nonneg_left (hFlower x hx'.1) (sq_nonneg (q x))
        have hcurv := reducedReciprocalLogWidth_curvature hf.1 (hlogI x hx')
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        rw [← div_eq_inv_mul, (le_div_iff₀ hC)]
        simpa only [mul_comm] using hCF.trans hcurv
    have hbound : ∀ b, X ≤ b →
        (∫ x in X..b, ‖q x ^ 2‖) ≤ C⁻¹ * (-logPolarSqrtEnergyFirst f X) := by
      intro b hb
      have hlogI : ∀ x ∈ Set.Icc X b,
          0 < Real.log (logarithmicMaximum f 1 (Real.exp x)) :=
        fun x hx ↦ hlog x hx.1
      have hqint := hlocal b hb
      have hF2int : IntervalIntegrable (logPolarSqrtEnergySecond f) volume X b := by
        apply ContinuousOn.intervalIntegrable
        rw [uIcc_of_le hb]
        exact continuousOn_logPolarSqrtEnergySecond hf.1 hlogI
      have hpoint : ∀ x ∈ Set.Icc X b,
          q x ^ 2 ≤ C⁻¹ * logPolarSqrtEnergySecond f x := by
        intro x hx
        have hCF : C * q x ^ 2 ≤ q x ^ 2 * logPolarSqrtEnergy f x :=
          by simpa only [mul_comm] using
            mul_le_mul_of_nonneg_left (hFlower x hx.1) (sq_nonneg (q x))
        have hcurv := reducedReciprocalLogWidth_curvature hf.1 (hlogI x hx)
        rw [← div_eq_inv_mul, (le_div_iff₀ hC)]
        simpa only [mul_comm] using hCF.trans hcurv
      have hmonoInt : (∫ x in X..b, q x ^ 2) ≤
          ∫ x in X..b, C⁻¹ * logPolarSqrtEnergySecond f x := by
        apply intervalIntegral.integral_mono_on hb hqint
          (hF2int.const_mul C⁻¹)
        exact hpoint
      have hFTC : (∫ x in X..b, logPolarSqrtEnergySecond f x) =
          logPolarSqrtEnergyFirst f b - logPolarSqrtEnergyFirst f X := by
        apply intervalIntegral.integral_eq_sub_of_hasDerivAt
        · intro x hx
          have hx' : x ∈ Set.Icc X b := by
            simpa [uIcc_of_le hb] using hx
          exact hasDerivAt_logPolarSqrtEnergyFirst hf.1 (hlogI x hx')
        · exact hF2int
      rw [intervalIntegral.integral_const_mul, hFTC] at hmonoInt
      have hbnonpos := hslope_nonpos b hb
      have hnorm : (∫ x in X..b, ‖q x ^ 2‖) = ∫ x in X..b, q x ^ 2 := by
        apply intervalIntegral.integral_congr
        intro x hx
        change |q x ^ 2| = q x ^ 2
        exact abs_of_nonneg (sq_nonneg _)
      rw [hnorm]
      calc
        (∫ x in X..b, q x ^ 2) ≤
            C⁻¹ * (logPolarSqrtEnergyFirst f b -
              logPolarSqrtEnergyFirst f X) := hmonoInt
        _ ≤ C⁻¹ * (-logPolarSqrtEnergyFirst f X) := by
          exact mul_le_mul_of_nonneg_left (by linarith) (inv_nonneg.mpr hC.le)
    have hqintTail : IntegrableOn (fun x ↦ q x ^ 2) (Set.Ioi X) := by
      apply integrableOn_Ioi_of_intervalIntegral_norm_bounded
        (μ := volume) (l := atTop)
        (C⁻¹ * (-logPolarSqrtEnergyFirst f X)) X
        (b := fun n : ℕ ↦ X + (n : ℝ))
      · intro n
        have hn : X ≤ X + (n : ℝ) := le_add_of_nonneg_right (Nat.cast_nonneg n)
        apply (intervalIntegrable_iff_integrableOn_Ioc_of_le hn).mp
        exact hlocal (X + (n : ℝ)) hn
      · exact tendsto_const_nhds.add_atTop tendsto_natCast_atTop_atTop
      · filter_upwards with n
        exact hbound (X + (n : ℝ)) (le_add_of_nonneg_right (Nat.cast_nonneg n))
    exact (not_integrableOn_reducedReciprocalLogWidth_sq hf.1 harea
      (fun x hx ↦ hlog x hx.le)) (by simpa only [q] using hqintTail)
  obtain ⟨Y, hXY, hYpos⟩ := hex
  refine ⟨Y, (fun x hx ↦ hlog x (hXY.trans hx)), ?_⟩
  intro x hx
  exact hYpos.trans_le (hmono hXY (hXY.trans hx) hx)

theorem log_logPolarSqrtEnergy_le {f : ℂ → ℂ}
    (hf : IsEntire f) {x : ℝ}
    (hB : 1 < logarithmicMaximum f 1 (Real.exp x)) :
    Real.log (logPolarSqrtEnergy f x) ≤
      5 * Real.log (logarithmicMaximum f 1 (Real.exp x)) +
        Real.log √(2 * Real.pi) := by
  have hlog : 0 < Real.log (logarithmicMaximum f 1 (Real.exp x)) :=
    Real.log_pos hB
  have hF : 0 < logPolarSqrtEnergy f x := by
    unfold logPolarSqrtEnergy
    apply Real.sqrt_pos.2
    simpa only [logPolarEnergy] using logPolar_energy_pos_of_log_max_pos hf x hlog
  have hC : 0 < √(2 * Real.pi) := Real.sqrt_pos.2 (by positivity)
  have hBpos : 0 < logarithmicMaximum f 1 (Real.exp x) := lt_trans (by norm_num) hB
  have hu := logPolarSqrtEnergy_le_posLog_maximumModulus hf x
  have hposlog : Real.posLog (maximumModulus f (Real.exp x)) =
      logarithmicMaximum f 1 (Real.exp x) := by
    simp [logarithmicMaximum]
  rw [hposlog] at hu
  have hlogle := Real.log_le_log hF hu
  rw [Real.log_mul hC.ne' (pow_ne_zero 5 hBpos.ne'), Real.log_pow] at hlogle
  norm_num only [Nat.cast_ofNat] at hlogle
  nlinarith

/-- On a tail where the double logarithmic maximum is positive, the first derivative of the
square-root energy is monotone. -/
theorem monotoneOn_logPolarSqrtEnergyFirst {f : ℂ → ℂ}
    (hf : IsEntire f) {X : ℝ}
    (hlog : ∀ x, X ≤ x →
      0 < Real.log (logarithmicMaximum f 1 (Real.exp x))) :
    MonotoneOn (logPolarSqrtEnergyFirst f) (Set.Ici X) := by
  apply monotoneOn_of_deriv_nonneg (convex_Ici X)
  · intro x hx
    exact (hasDerivAt_logPolarSqrtEnergyFirst hf (hlog x hx)).continuousAt.continuousWithinAt
  · intro x hx
    have hxX : X ≤ x := interior_subset hx
    exact (hasDerivAt_logPolarSqrtEnergyFirst hf (hlog x hxX)).differentiableAt.differentiableWithinAt
  · intro x hx
    have hxX : X ≤ x := interior_subset hx
    rw [(hasDerivAt_logPolarSqrtEnergyFirst hf (hlog x hxX)).deriv]
    exact logPolarSqrtEnergySecond_nonneg hf (hlog x hxX)

theorem monotoneOn_logPolarSqrtEnergy {f : ℂ → ℂ}
    (hf : IsEntire f) {X : ℝ}
    (hlog : ∀ x, X ≤ x →
      0 < Real.log (logarithmicMaximum f 1 (Real.exp x)))
    (hfirst : ∀ x, X ≤ x → 0 < logPolarSqrtEnergyFirst f x) :
    MonotoneOn (logPolarSqrtEnergy f) (Set.Ici X) := by
  apply monotoneOn_of_deriv_nonneg (convex_Ici X)
  · exact (continuous_logPolarSqrtEnergy hf).continuousOn
  · intro x hx
    have hxX : X ≤ x := interior_subset hx
    exact (hasDerivAt_logPolarSqrtEnergy hf (hlog x hxX)).differentiableAt.differentiableWithinAt
  · intro x hx
    have hxX : X ≤ x := interior_subset hx
    rw [(hasDerivAt_logPolarSqrtEnergy hf (hlog x hxX)).deriv]
    exact (hfirst x hxX).le

/-- Convexity bounds the first energy derivative by a forward difference quotient. -/
theorem logPolarSqrtEnergyFirst_le_forward_quotient {f : ℂ → ℂ}
    (hf : IsEntire f) {X b c : ℝ}
    (hlog : ∀ x, X ≤ x →
      0 < Real.log (logarithmicMaximum f 1 (Real.exp x)))
    (hb : X ≤ b) (hbc : b < c) :
    (c - b) * logPolarSqrtEnergyFirst f b ≤
      logPolarSqrtEnergy f c - logPolarSqrtEnergy f b := by
  have hmono := monotoneOn_logPolarSqrtEnergyFirst hf hlog
  have hint : IntervalIntegrable (logPolarSqrtEnergyFirst f) volume b c := by
    apply ContinuousOn.intervalIntegrable
    intro x hx
    have hx' : x ∈ Set.Icc b c := by simpa [uIcc_of_le hbc.le] using hx
    exact (hasDerivAt_logPolarSqrtEnergyFirst hf
      (hlog x (hb.trans hx'.1))).continuousAt.continuousWithinAt
  have hconst : IntervalIntegrable (fun _ : ℝ ↦ logPolarSqrtEnergyFirst f b) volume b c :=
    intervalIntegrable_const
  have hle : (∫ _ in b..c, logPolarSqrtEnergyFirst f b) ≤
      ∫ x in b..c, logPolarSqrtEnergyFirst f x := by
    apply intervalIntegral.integral_mono_on hbc.le hconst hint
    intro x hx
    exact hmono hb (hb.trans hx.1) hx.1
  have hFTC : (∫ x in b..c, logPolarSqrtEnergyFirst f x) =
      logPolarSqrtEnergy f c - logPolarSqrtEnergy f b := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    · intro x hx
      have hx' : x ∈ Set.Icc b c := by simpa [uIcc_of_le hbc.le] using hx
      exact hasDerivAt_logPolarSqrtEnergy hf (hlog x (hb.trans hx'.1))
    · exact hint
  rw [intervalIntegral.integral_const, hFTC] at hle
  simpa [smul_eq_mul] using hle

theorem log_logPolarSqrtEnergyFirst_le_future {f : ℂ → ℂ}
    (hf : IsEntire f) {X b c : ℝ}
    (hlog : ∀ x, X ≤ x →
      0 < Real.log (logarithmicMaximum f 1 (Real.exp x)))
    (hfirst : ∀ x, X ≤ x → 0 < logPolarSqrtEnergyFirst f x)
    (hb : X ≤ b) (hbc : b < c) :
    Real.log (logPolarSqrtEnergyFirst f b) ≤
      Real.log (logPolarSqrtEnergy f c) - Real.log (c - b) := by
  have hforward := logPolarSqrtEnergyFirst_le_forward_quotient hf hlog hb hbc
  have hFb : 0 ≤ logPolarSqrtEnergy f b := by
    unfold logPolarSqrtEnergy
    exact Real.sqrt_nonneg _
  have hprod : (c - b) * logPolarSqrtEnergyFirst f b ≤
      logPolarSqrtEnergy f c := by
    linarith
  have hgap : 0 < c - b := sub_pos.mpr hbc
  have hslope : 0 < logPolarSqrtEnergyFirst f b := hfirst b hb
  have hFc : 0 < logPolarSqrtEnergy f c := by
    unfold logPolarSqrtEnergy
    apply Real.sqrt_pos.2
    simpa only [logPolarEnergy] using
      logPolar_energy_pos_of_log_max_pos hf c (hlog c (hb.trans hbc.le))
  have hlogprod := Real.log_le_log (mul_pos hgap hslope) hprod
  rw [Real.log_mul hgap.ne' hslope.ne'] at hlogprod
  linarith

theorem logarithmicMaximum_one_eq_log {f : ℂ → ℂ} (hf : Continuous f)
    {r : ℝ} (hr : 0 ≤ r) (hM : 1 ≤ maximumModulus f r) :
    logarithmicMaximum f 1 r = Real.log (maximumModulus f r) := by
  unfold logarithmicMaximum
  rw [div_one]
  apply Real.posLog_eq_log
  rw [abs_of_nonneg (maximumModulus_nonneg hf hr)]
  exact hM

/-- The integrand in Hayman's necessary growth condition. -/
noncomputable def growthIntegrand (f : ℂ → ℂ) (r : ℝ) : ℝ :=
  r / Real.log (Real.log (maximumModulus f r))

/-- On a tail where its denominator is positive, Hayman's integrand is continuous. -/
theorem continuousOn_growthIntegrand {f : ℂ → ℂ} {R : ℝ}
    (hf : Continuous f) (hR : 0 < R)
    (hpos : ∀ r, R ≤ r → 0 < Real.log (Real.log (maximumModulus f r))) :
    ContinuousOn (growthIntegrand f) (Set.Ioi R) := by
  have hsubset : Set.Ioi R ⊆ Set.Ici (0 : ℝ) := by
    intro r hr
    exact hR.le.trans hr.le
  have hMcont : ContinuousOn (maximumModulus f) (Set.Ioi R) :=
    (continuousOn_maximumModulus hf).mono hsubset
  have hMne : ∀ r ∈ Set.Ioi R, maximumModulus f r ≠ 0 := by
    intro r hr hzero
    have hp := hpos r hr.le
    simp [hzero] at hp
  have hlogMcont : ContinuousOn (fun r ↦ Real.log (maximumModulus f r)) (Set.Ioi R) :=
    hMcont.log hMne
  have hlogMne : ∀ r ∈ Set.Ioi R, Real.log (maximumModulus f r) ≠ 0 := by
    intro r hr hzero
    have hp := hpos r hr.le
    simp [hzero] at hp
  have hdenom : ContinuousOn
      (fun r ↦ Real.log (Real.log (maximumModulus f r))) (Set.Ioi R) :=
    hlogMcont.log hlogMne
  unfold growthIntegrand
  exact continuousOn_id.div hdenom fun r hr ↦ (hpos r hr.le).ne'

/-- Convergence of Hayman's integral, stated on a positive tail so that
small-radius zeros of `log (log M(r))` do not create an artificial issue. -/
def GrowthIntegralConverges (f : ℂ → ℂ) : Prop :=
  ∃ R > 0,
    (∀ r, R ≤ r → 0 < Real.log (Real.log (maximumModulus f r))) ∧
    IntegrableOn (growthIntegrand f) (Set.Ioi R)

/-- The integrand occurring directly in the normalized logarithmic-level reduction. -/
noncomputable def cameraIntegrand (f : ℂ → ℂ) (r : ℝ) : ℝ :=
  r / Real.log (logarithmicMaximum f 1 r)

/-- On a closed positive tail where its denominator is positive, the normalized Camera
integrand is continuous. -/
theorem continuousOn_cameraIntegrand {f : ℂ → ℂ} {R : ℝ}
    (hf : Continuous f) (hR : 0 < R)
    (hpos : ∀ r, R ≤ r → 0 < Real.log (logarithmicMaximum f 1 r)) :
    ContinuousOn (cameraIntegrand f) (Set.Ici R) := by
  have hsubset : Set.Ici R ⊆ Set.Ici (0 : ℝ) := by
    intro r hr
    exact hR.le.trans hr
  have hMcont : ContinuousOn (maximumModulus f) (Set.Ici R) :=
    (continuousOn_maximumModulus hf).mono hsubset
  have hBcont : ContinuousOn (logarithmicMaximum f 1) (Set.Ici R) := by
    unfold logarithmicMaximum
    exact Real.continuous_posLog.comp_continuousOn (hMcont.div_const 1)
  have hBne : ∀ r ∈ Set.Ici R, logarithmicMaximum f 1 r ≠ 0 := by
    intro r hr hzero
    have hp := hpos r hr
    simp [hzero] at hp
  have hdenom : ContinuousOn
      (fun r ↦ Real.log (logarithmicMaximum f 1 r)) (Set.Ici R) :=
    hBcont.log hBne
  unfold cameraIntegrand
  exact continuousOn_id.div hdenom fun r hr ↦ (hpos r hr).ne'

/-- Weighted exceptional area in one dyadic annulus. -/
noncomputable def dyadicAreaMass (f : ℂ → ℂ) (R : ℝ) (n : ℕ) : ℝ :=
  ∫ r in Set.Ico (R * (2 : ℝ) ^ n) (R * (2 : ℝ) ^ (n + 1)),
    r * angularWidth (exceptionalSet f 1) r

/-- Camera's normalized area--growth conclusion, separated as an interface used by the
level-scaling argument below. -/
def NormalizedAreaGrowthTheorem : Prop :=
  ∀ f : ℂ → ℂ,
    IsNonconstantEntire f → HasFiniteArea f 1 →
      ∃ R > 0,
        (∀ r, R ≤ r → 0 < Real.log (logarithmicMaximum f 1 r)) ∧
        IntegrableOn (cameraIntegrand f) (Set.Ioi R)

/-- Reciprocal-weight Cauchy--Schwarz in the exact real-integral form used by the
Tsuji--Carleman reduction.  Strict positivity is only required almost everywhere on the
integration set. -/
theorem measureReal_sq_le_setIntegral_mul_setIntegral_inv
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {s : Set α} {w : α → ℝ}
    (hw : IntegrableOn w s μ)
    (hinv : IntegrableOn (fun x ↦ (w x)⁻¹) s μ)
    (hpos : ∀ᵐ x ∂μ.restrict s, 0 < w x) :
    (μ.real s) ^ 2 ≤
      (∫ x in s, w x ∂μ) * (∫ x in s, (w x)⁻¹ ∂μ) := by
  let ν : Measure α := μ.restrict s
  let u : α → ℝ := fun x ↦ √(w x)
  let v : α → ℝ := fun x ↦ √((w x)⁻¹)
  change ∀ᵐ x ∂ν, 0 < w x at hpos
  have hu_meas : AEStronglyMeasurable u ν := by
    exact Real.continuous_sqrt.comp_aestronglyMeasurable hw.1
  have hv_meas : AEStronglyMeasurable v ν := by
    exact Real.continuous_sqrt.comp_aestronglyMeasurable hinv.1
  have hu_sq : Integrable (fun x ↦ u x ^ 2) ν := by
    apply hw.congr
    filter_upwards [hpos] with x hx
    exact (Real.sq_sqrt hx.le).symm
  have hv_sq : Integrable (fun x ↦ v x ^ 2) ν := by
    apply hinv.congr
    filter_upwards [hpos] with x hx
    exact (Real.sq_sqrt (inv_nonneg.mpr hx.le)).symm
  have hu : MemLp u 2 ν :=
    (memLp_two_iff_integrable_sq hu_meas).mpr hu_sq
  have hv : MemLp v 2 ν :=
    (memLp_two_iff_integrable_sq hv_meas).mpr hv_sq
  have huv : u * v =ᵐ[ν] (fun _ ↦ (1 : ℝ)) := by
    filter_upwards [hpos] with x hx
    change √(w x) * √((w x)⁻¹) = 1
    rw [← Real.sqrt_mul hx.le, mul_inv_cancel₀ hx.ne', Real.sqrt_one]
  have hholder := integral_mul_le_Lp_mul_Lq_of_nonneg
    (μ := ν) (f := u) (g := v) Real.HolderConjugate.two_two
    (ae_of_all ν fun x ↦ Real.sqrt_nonneg (w x))
    (ae_of_all ν fun x ↦ Real.sqrt_nonneg ((w x)⁻¹))
    (by simpa using hu) (by simpa using hv)
  have hu_int : (∫ x, u x ^ (2 : ℝ) ∂ν) = ∫ x, w x ∂ν := by
    apply integral_congr_ae
    filter_upwards [hpos] with x hx
    rw [Real.rpow_two, Real.sq_sqrt hx.le]
  have hv_int : (∫ x, v x ^ (2 : ℝ) ∂ν) = ∫ x, (w x)⁻¹ ∂ν := by
    apply integral_congr_ae
    filter_upwards [hpos] with x hx
    rw [Real.rpow_two, Real.sq_sqrt (inv_nonneg.mpr hx.le)]
  have hw_nonneg : 0 ≤ ∫ x, w x ∂ν := by
    apply integral_nonneg_of_ae
    filter_upwards [hpos] with x hx
    exact hx.le
  have hinv_nonneg : 0 ≤ ∫ x, (w x)⁻¹ ∂ν :=
    integral_nonneg_of_ae (hpos.mono fun _ hx ↦ inv_nonneg.mpr hx.le)
  change (∫ x, u x * v x ∂ν) ≤
      (∫ x, u x ^ (2 : ℝ) ∂ν) ^ (1 / (2 : ℝ)) *
        (∫ x, v x ^ (2 : ℝ) ∂ν) ^ (1 / (2 : ℝ)) at hholder
  rw [hu_int, hv_int, ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow] at hholder
  have hroot : ν.real Set.univ ≤
      √(∫ x, w x ∂ν) * √(∫ x, (w x)⁻¹ ∂ν) := by
    calc
      ν.real Set.univ = ∫ _ : α, (1 : ℝ) ∂ν := by simp
      _ = ∫ x, u x * v x ∂ν := integral_congr_ae huv.symm
      _ ≤ √(∫ x, w x ∂ν) * √(∫ x, (w x)⁻¹ ∂ν) := hholder
  have hsquare : (ν.real Set.univ) ^ 2 ≤
      (√(∫ x, w x ∂ν) * √(∫ x, (w x)⁻¹ ∂ν)) ^ 2 :=
    (sq_le_sq₀ (measureReal_nonneg) (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))).mpr
      hroot
  rw [mul_pow, Real.sq_sqrt hw_nonneg, Real.sq_sqrt hinv_nonneg] at hsquare
  simpa only [ν, measureReal_restrict_apply_univ] using hsquare

/-- The one-annulus-shifted interval estimate furnished by the Tsuji--Carleman inequality and
reciprocal-width Cauchy--Schwarz argument. -/
def HasDyadicCameraEstimate (f : ℂ → ℂ) (R C : ℝ) : Prop :=
  0 < R ∧ 0 < C ∧
  (∀ r, R ≤ r → 0 < Real.log (logarithmicMaximum f 1 r)) ∧
  (∀ n : ℕ,
    IntegrableOn (cameraIntegrand f)
      (Set.Ico (R * (2 : ℝ) ^ (n + 1)) (R * (2 : ℝ) ^ (n + 2)))) ∧
  ∀ n : ℕ,
    (∫ r in Set.Ico (R * (2 : ℝ) ^ (n + 1)) (R * (2 : ℝ) ^ (n + 2)),
        ‖cameraIntegrand f r‖) ≤
      C * dyadicAreaMass f R n

/-- The dyadic estimate with the two-annulus shift forced by the endpoint-stable slope bound. -/
def HasDyadicCameraEstimateTwoShift (f : ℂ → ℂ) (R C : ℝ) : Prop :=
  0 < R ∧ 0 < C ∧
  (∀ r, R ≤ r → 0 < Real.log (logarithmicMaximum f 1 r)) ∧
  (∀ n : ℕ,
    IntegrableOn (cameraIntegrand f)
      (Set.Ico (R * (2 : ℝ) ^ (n + 2)) (R * (2 : ℝ) ^ (n + 3)))) ∧
  ∀ n : ℕ,
    (∫ r in Set.Ico (R * (2 : ℝ) ^ (n + 2)) (R * (2 : ℝ) ^ (n + 3)),
        ‖cameraIntegrand f r‖) ≤
      C * dyadicAreaMass f R n

/-- Pointwise annular form of the Tsuji--Carleman conclusion.  Area on `[q,2q)` controls the
logarithmic maximum, and hence the growth integrand, throughout the following annulus
`[2q,4q)`. -/
def HasAnnularCameraLowerBound (f : ℂ → ℂ) (R A : ℝ) : Prop :=
  0 < R ∧ 0 < A ∧
  (∀ r, R ≤ r → 0 < Real.log (logarithmicMaximum f 1 r)) ∧
  ∀ n : ℕ,
    0 < dyadicAreaMass f R n ∧
    ∀ r ∈ Set.Ico (R * (2 : ℝ) ^ (n + 1)) (R * (2 : ℝ) ^ (n + 2)),
      (R * (2 : ℝ) ^ n) ^ 2 ≤
        A * dyadicAreaMass f R n * Real.log (logarithmicMaximum f 1 r)

/-- The endpoint-stable annular lower bound: mass on `[q,2q)` controls the logarithmic
maximum throughout `[4q,8q)`. -/
def HasAnnularCameraLowerBoundTwoShift (f : ℂ → ℂ) (R A : ℝ) : Prop :=
  0 < R ∧ 0 < A ∧
  (∀ r, R ≤ r → 0 < Real.log (logarithmicMaximum f 1 r)) ∧
  ∀ n : ℕ,
    0 < dyadicAreaMass f R n ∧
    ∀ r ∈ Set.Ico (R * (2 : ℝ) ^ (n + 2)) (R * (2 : ℝ) ^ (n + 3)),
      (R * (2 : ℝ) ^ n) ^ 2 ≤
        A * dyadicAreaMass f R n * Real.log (logarithmicMaximum f 1 r)

/-- Reciprocal of the polar area density.  This is the integrand in Tsuji's angular-width
estimate. -/
noncomputable def reciprocalAngularWeight (f : ℂ → ℂ) (r : ℝ) : ℝ :=
  (r * angularWidth (exceptionalSet f 1) r)⁻¹

/-- The exponential change of variables turns the radial reciprocal area density into the
reciprocal angular width on the logarithmic cylinder. -/
theorem integral_reciprocalAngularWeight_eq_log {f : ℂ → ℂ} {q : ℝ}
    (hq : 0 < q) :
    (∫ r in q..2 * q, reciprocalAngularWeight f r) =
      ∫ x in Real.log q..Real.log (2 * q), logReciprocalAngularWidth f x := by
  have hsubst := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg
    (a := Real.log q) (b := Real.log (2 * q))
    (f := Real.exp) (f' := Real.exp) (g := reciprocalAngularWeight f)
    Real.continuous_exp.continuousOn
    (fun x hx ↦ Real.hasDerivAt_exp x)
    (fun x hx ↦ (Real.exp_pos x).le)
  have hleft : (fun x ↦
      (reciprocalAngularWeight f ∘ Real.exp) x * Real.exp x) =
      logReciprocalAngularWidth f := by
    funext x
    simp only [reciprocalAngularWeight, logReciprocalAngularWidth,
      Function.comp_apply, mul_inv_rev]
    rw [mul_assoc, inv_mul_cancel₀ (Real.exp_ne_zero x), mul_one]
  rw [hleft, Real.exp_log hq, Real.exp_log (mul_pos (by norm_num) hq)] at hsubst
  exact hsubst.symm

theorem intervalIntegrable_reciprocalAngularWeight_iff_log {f : ℂ → ℂ} {q : ℝ}
    (hq : 0 < q) :
    IntervalIntegrable (reciprocalAngularWeight f) volume q (2 * q) ↔
      IntervalIntegrable (logReciprocalAngularWidth f) volume
        (Real.log q) (Real.log (2 * q)) := by
  have hiff := intervalIntegral.integrable_comp_mul_deriv_iff_of_deriv_nonneg
    (a := Real.log q) (b := Real.log (2 * q))
    (f := Real.exp) (f' := Real.exp) (g := reciprocalAngularWeight f)
    Real.continuous_exp.continuousOn
    (fun x hx ↦ Real.hasDerivAt_exp x)
    (fun x hx ↦ (Real.exp_pos x).le)
  have hleft : (fun x ↦
      (reciprocalAngularWeight f ∘ Real.exp) x * Real.exp x) =
      logReciprocalAngularWidth f := by
    funext x
    simp only [reciprocalAngularWeight, logReciprocalAngularWidth,
      Function.comp_apply, mul_inv_rev]
    rw [mul_assoc, inv_mul_cancel₀ (Real.exp_ne_zero x), mul_one]
  rw [hleft, Real.exp_log hq, Real.exp_log (mul_pos (by norm_num) hq)] at hiff
  exact hiff.symm

/-- Lebesgue-null endpoints identify the half-open set integral with the oriented interval
integral.  Keeping this elementary conversion separate prevents the main Tsuji estimate from
spending its elaboration budget on interval notation. -/
theorem integral_reciprocalAngularWeight_Ico_eq_interval {f : ℂ → ℂ} {q : ℝ}
    (hq : 0 ≤ q) :
    (∫ t in Set.Ico q (2 * q), reciprocalAngularWeight f t) =
      ∫ t in q..2 * q, reciprocalAngularWeight f t := by
  have hq2 : q ≤ 2 * q := le_mul_of_one_le_left hq (by norm_num)
  rw [intervalIntegral.integral_of_le hq2, integral_Ico_eq_integral_Ioc]

/-- The precise Tsuji conclusion needed by Camera's proof.  On each dyadic annulus the polar
area density is positive almost everywhere, its reciprocal is integrable, and the reciprocal
integral is controlled by the logarithmic maximum on the following annulus. -/
def HasTsujiCameraBound (f : ℂ → ℂ) (R A : ℝ) : Prop :=
  0 < R ∧ 0 < A ∧
  (∀ r, R ≤ r → 0 < Real.log (logarithmicMaximum f 1 r)) ∧
  ∀ n : ℕ,
    let I := Set.Ico (R * (2 : ℝ) ^ n) (R * (2 : ℝ) ^ (n + 1))
    IntegrableOn (fun r ↦ r * angularWidth (exceptionalSet f 1) r) I ∧
    IntegrableOn (reciprocalAngularWeight f) I ∧
    (∀ᵐ r ∂volume.restrict I,
      0 < r * angularWidth (exceptionalSet f 1) r) ∧
    ∀ r ∈ Set.Ico (R * (2 : ℝ) ^ (n + 1)) (R * (2 : ℝ) ^ (n + 2)),
      (∫ t in I, reciprocalAngularWeight f t) ≤
        A * Real.log (logarithmicMaximum f 1 r)

/-- The irreducible Tsuji estimate after positivity and ordinary area-density integrability
have been separated off. -/
def HasTsujiReciprocalEstimate (f : ℂ → ℂ) (R A : ℝ) : Prop :=
  0 < R ∧ 0 < A ∧
  (∀ r, R ≤ r → 0 < Real.log (logarithmicMaximum f 1 r)) ∧
  ∀ n : ℕ,
    let I := Set.Ico (R * (2 : ℝ) ^ n) (R * (2 : ℝ) ^ (n + 1))
    IntegrableOn (reciprocalAngularWeight f) I ∧
    ∀ r ∈ Set.Ico (R * (2 : ℝ) ^ (n + 1)) (R * (2 : ℝ) ^ (n + 2)),
      (∫ t in I, reciprocalAngularWeight f t) ≤
        A * Real.log (logarithmicMaximum f 1 r)

/-- The quantitatively natural form of Tsuji's estimate: controlling the energy slope at the
right endpoint uses one further annulus, so `[q,2q]` is compared with `[4q,8q]`. -/
def HasTsujiReciprocalEstimateTwoShift (f : ℂ → ℂ) (R A : ℝ) : Prop :=
  0 < R ∧ 0 < A ∧
  (∀ r, R ≤ r → 0 < Real.log (logarithmicMaximum f 1 r)) ∧
  ∀ n : ℕ,
    let I := Set.Ico (R * (2 : ℝ) ^ n) (R * (2 : ℝ) ^ (n + 1))
    IntegrableOn (reciprocalAngularWeight f) I ∧
    ∀ r ∈ Set.Ico (R * (2 : ℝ) ^ (n + 2)) (R * (2 : ℝ) ^ (n + 3)),
      (∫ t in I, reciprocalAngularWeight f t) ≤
        A * Real.log (logarithmicMaximum f 1 r)

/-- Tsuji's reciprocal estimate together with the direct finite-area density facts, in the
two-shift form actually produced by endpoint control. -/
def HasTsujiCameraBoundTwoShift (f : ℂ → ℂ) (R A : ℝ) : Prop :=
  0 < R ∧ 0 < A ∧
  (∀ r, R ≤ r → 0 < Real.log (logarithmicMaximum f 1 r)) ∧
  ∀ n : ℕ,
    let I := Set.Ico (R * (2 : ℝ) ^ n) (R * (2 : ℝ) ^ (n + 1))
    IntegrableOn (fun r ↦ r * angularWidth (exceptionalSet f 1) r) I ∧
    IntegrableOn (reciprocalAngularWeight f) I ∧
    (∀ᵐ r ∂volume.restrict I,
      0 < r * angularWidth (exceptionalSet f 1) r) ∧
    ∀ r ∈ Set.Ico (R * (2 : ℝ) ^ (n + 2)) (R * (2 : ℝ) ^ (n + 3)),
      (∫ t in I, reciprocalAngularWeight f t) ≤
        A * Real.log (logarithmicMaximum f 1 r)

theorem hasTsujiReciprocalEstimateTwoShift {f : ℂ → ℂ}
    (hf : IsNonconstantEntire f) (harea : HasFiniteArea f 1) :
    ∃ R A, HasTsujiReciprocalEstimateTwoShift f R A := by
  obtain ⟨Y, hlog, hfirst⟩ := eventually_pos_logPolarSqrtEnergyFirst hf harea
  let R : ℝ := Real.exp Y
  let L : ℝ := Real.log 2
  let d : ℝ := Real.log (logarithmicMaximum f 1 R)
  let c₀ : ℝ := Real.log √(2 * Real.pi)
  let K : ℝ := 2 * |c₀| + |Real.log (logPolarSqrtEnergy f Y)| +
    |Real.log (logPolarSqrtEnergyFirst f Y)| + |Real.log L| +
    2 * L * (2 * Real.pi)⁻¹
  let A : ℝ := 5 + K / (2 * d)
  have hR : 0 < R := Real.exp_pos Y
  have hL : 0 < L := Real.log_pos (by norm_num)
  have hd : 0 < d := by
    dsimp only [d, R]
    simpa only [Real.exp_log (Real.exp_pos Y)] using hlog Y le_rfl
  have hK : 0 ≤ K := by
    dsimp only [K]
    positivity
  have hA : 0 < A := by
    dsimp only [A]
    positivity
  have htail : ∀ r, R ≤ r →
      0 < Real.log (logarithmicMaximum f 1 r) := by
    intro r hr
    have hbaseB : 0 < logarithmicMaximum f 1 R := by
      have hB := (Real.log_pos_iff Real.posLog_nonneg).mp hd
      unfold logarithmicMaximum
      exact (by linarith : 0 < (maximumModulus f R / 1).posLog)
    exact hd.trans_le
      (log_logarithmicMaximum_one_mono hf.1 hR.le hr hbaseB)
  refine ⟨R, A, hR, hA, htail, ?_⟩
  intro n
  let q : ℝ := R * (2 : ℝ) ^ n
  let a : ℝ := Real.log q
  let b : ℝ := Real.log (2 * q)
  let c : ℝ := Real.log (4 * q)
  let I : Set ℝ := Set.Ico q (2 * q)
  have hq : 0 < q := mul_pos hR (pow_pos (by norm_num) n)
  have hRq : R ≤ q := by
    have hone : (1 : ℝ) ≤ (2 : ℝ) ^ n := one_le_pow₀ (by norm_num)
    simpa only [q, mul_one] using mul_le_mul_of_nonneg_left hone hR.le
  have haY : Y ≤ a := by
    have h := Real.log_le_log hR hRq
    simpa only [a, R, Real.log_exp] using h
  have hab : a < b := by
    exact Real.strictMonoOn_log hq (mul_pos (by norm_num) hq) (by nlinarith)
  have hbc : b < c := by
    exact Real.strictMonoOn_log (mul_pos (by norm_num) hq)
      (mul_pos (by norm_num) hq) (by nlinarith)
  have hgap₁ : b - a = L := by
    dsimp only [a, b, L]
    rw [Real.log_mul (by norm_num) hq.ne']
    ring
  have hgap₂ : c - b = L := by
    dsimp only [b, c, L]
    rw [show 4 * q = 2 * (2 * q) by ring,
      Real.log_mul (by norm_num) (mul_ne_zero (by norm_num) hq.ne')]
    ring
  have hbY : Y ≤ b := haY.trans hab.le
  have hcY : Y ≤ c := hbY.trans hbc.le
  have hlogab : ∀ x ∈ Set.Icc a b,
      0 < Real.log (logarithmicMaximum f 1 (Real.exp x)) :=
    fun x hx ↦ hlog x (haY.trans hx.1)
  have hfirstab : ∀ x ∈ Set.Icc a b,
      0 < logPolarSqrtEnergyFirst f x :=
    fun x hx ↦ hfirst x (haY.trans hx.1)
  obtain ⟨hlogint, hcar⟩ :=
    intervalIntegral_logReciprocalAngularWidth_carleman hf.1 hab.le hlogab hfirstab
  have hradint : IntervalIntegrable (reciprocalAngularWeight f) volume q (2 * q) :=
    (intervalIntegrable_reciprocalAngularWeight_iff_log hq).mpr
      (by simpa only [a, b] using hlogint)
  have hradset : IntegrableOn (reciprocalAngularWeight f) I := by
    dsimp only [I]
    have hIoc := (intervalIntegrable_iff_integrableOn_Ioc_of_le
      (by nlinarith : q ≤ 2 * q)).mp hradint
    exact hIoc.congr_set_ae Ico_ae_eq_Ioc
  have hnext₂ : R * (2 : ℝ) ^ (n + 2) = 4 * q := by
    simp only [q, pow_succ]
    ring
  have hnext₃ : R * (2 : ℝ) ^ (n + 3) = 8 * q := by
    simp only [q, pow_succ]
    ring
  have hIeq : Set.Ico (R * (2 : ℝ) ^ n) (R * (2 : ℝ) ^ (n + 1)) = I := by
    dsimp only [I, q]
    congr 1
    simp only [pow_succ]
    ring
  refine ⟨by rw [hIeq]; exact hradset, ?_⟩
  intro r hr
  have hr' : r ∈ Set.Ico (4 * q) (8 * q) := by
    rw [hnext₂, hnext₃] at hr
    exact hr
  have hbr : Real.exp b ≤ r := by
    have hexpb : Real.exp b = 2 * q := by
      dsimp only [b]
      exact Real.exp_log (mul_pos (by norm_num) hq)
    rw [hexpb]
    nlinarith [hr'.1]
  have hcr : Real.exp c ≤ r := by
    have hexpc : Real.exp c = 4 * q := by
      dsimp only [c]
      exact Real.exp_log (mul_pos (by norm_num) hq)
    rw [hexpc]
    exact hr'.1
  have hBlogb : 1 < logarithmicMaximum f 1 (Real.exp b) :=
    (Real.log_pos_iff Real.posLog_nonneg).mp (hlog b hbY)
  have hBlogc : 1 < logarithmicMaximum f 1 (Real.exp c) :=
    (Real.log_pos_iff Real.posLog_nonneg).mp (hlog c hcY)
  have hUb : Real.log (logPolarSqrtEnergy f b) ≤
      5 * Real.log (logarithmicMaximum f 1 r) + c₀ := by
    have hbase := log_logPolarSqrtEnergy_le hf.1 hBlogb
    have hmonoB := log_logarithmicMaximum_one_mono hf.1
      (Real.exp_pos b).le hbr (lt_trans (by norm_num) hBlogb)
    dsimp only [c₀]
    linarith
  have hUc : Real.log (logPolarSqrtEnergy f c) ≤
      5 * Real.log (logarithmicMaximum f 1 r) + c₀ := by
    have hbase := log_logPolarSqrtEnergy_le hf.1 hBlogc
    have hmonoB := log_logarithmicMaximum_one_mono hf.1
      (Real.exp_pos c).le hcr (lt_trans (by norm_num) hBlogc)
    dsimp only [c₀]
    linarith
  have hslope := log_logPolarSqrtEnergyFirst_le_future hf.1 hlog hfirst hbY hbc
  rw [hgap₂] at hslope
  have hmonoF := monotoneOn_logPolarSqrtEnergy hf.1 hlog hfirst
  have hmonoF₁ := monotoneOn_logPolarSqrtEnergyFirst hf.1 hlog
  have hFYpos : 0 < logPolarSqrtEnergy f Y := by
    unfold logPolarSqrtEnergy
    apply Real.sqrt_pos.2
    simpa only [logPolarEnergy] using
      logPolar_energy_pos_of_log_max_pos hf.1 Y (hlog Y le_rfl)
  have hFapos : 0 < logPolarSqrtEnergy f a := by
    exact hFYpos.trans_le
      (hmonoF (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 haY) haY)
  have hlogFa : Real.log (logPolarSqrtEnergy f Y) ≤
      Real.log (logPolarSqrtEnergy f a) :=
    Real.log_le_log hFYpos
      (hmonoF (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 haY) haY)
  have hlogF₁a : Real.log (logPolarSqrtEnergyFirst f Y) ≤
      Real.log (logPolarSqrtEnergyFirst f a) :=
    Real.log_le_log (hfirst Y le_rfl)
      (hmonoF₁ (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 haY) haY)
  have hraw : 2 * ∫ x in a..b, logReciprocalAngularWidth f x ≤
      10 * Real.log (logarithmicMaximum f 1 r) + K := by
    have hc₀abs : c₀ ≤ |c₀| := le_abs_self _
    have hnegFa : -Real.log (logPolarSqrtEnergy f a) ≤
        |Real.log (logPolarSqrtEnergy f Y)| := by
      exact (neg_le_neg hlogFa).trans (neg_le_abs _)
    have hnegF₁a : -Real.log (logPolarSqrtEnergyFirst f a) ≤
        |Real.log (logPolarSqrtEnergyFirst f Y)| := by
      exact (neg_le_neg hlogF₁a).trans (neg_le_abs _)
    have hnegL : -Real.log L ≤ |Real.log L| := neg_le_abs _
    dsimp only [K]
    rw [hgap₁] at hcar
    linarith
  have hRr : R ≤ r := by nlinarith [hRq, hr'.1]
  have hbaseB : 0 < logarithmicMaximum f 1 R :=
    by
      have hB := (Real.log_pos_iff Real.posLog_nonneg).mp hd
      unfold logarithmicMaximum
      exact (by linarith : 0 < (maximumModulus f R / 1).posLog)
  have hdD : d ≤ Real.log (logarithmicMaximum f 1 r) := by
    dsimp only [d]
    exact log_logarithmicMaximum_one_mono hf.1 hR.le hRr hbaseB
  have hKD : K ≤ (K / d) * Real.log (logarithmicMaximum f 1 r) := by
    calc
      K = (K / d) * d := by field_simp
      _ ≤ (K / d) * Real.log (logarithmicMaximum f 1 r) :=
        mul_le_mul_of_nonneg_left hdD (div_nonneg hK hd.le)
  have hfinalLog : (∫ x in a..b, logReciprocalAngularWidth f x) ≤
      A * Real.log (logarithmicMaximum f 1 r) := by
    have hAid : 2 * A * Real.log (logarithmicMaximum f 1 r) =
        10 * Real.log (logarithmicMaximum f 1 r) +
          (K / d) * Real.log (logarithmicMaximum f 1 r) := by
      dsimp only [A]
      field_simp
      ring
    nlinarith [hKD]
  have hseteq : (∫ t in I, reciprocalAngularWeight f t) =
      ∫ t in q..2 * q, reciprocalAngularWeight f t := by
    simpa only [I] using
      (integral_reciprocalAngularWeight_Ico_eq_interval (f := f) hq.le)
  rw [hIeq, hseteq, integral_reciprocalAngularWeight_eq_log hq]
  simpa only [a, b] using hfinalLog

/-- Finite exceptional area supplies the direct area-density integrability, while positivity
of the logarithmic maximum supplies strict positivity of that density.  Consequently the only
new analytic input in `HasTsujiCameraBound` is `HasTsujiReciprocalEstimate`. -/
theorem hasTsujiCameraBound_of_reciprocalEstimate {f : ℂ → ℂ} {R A : ℝ}
    (hf : IsNonconstantEntire f) (harea : HasFiniteArea f 1)
    (h : HasTsujiReciprocalEstimate f R A) : HasTsujiCameraBound f R A := by
  obtain ⟨hR, hA, hlog, hrecip⟩ := h
  refine ⟨hR, hA, hlog, ?_⟩
  have hwfull : IntegrableOn
      (fun r : ℝ ↦ r * angularWidth (exceptionalSet f 1) r) (Set.Ioi 0) :=
    integrableOn_exceptional_radius_mul_angularWidth hf.1.continuous harea
  intro n
  let I := Set.Ico (R * (2 : ℝ) ^ n) (R * (2 : ℝ) ^ (n + 1))
  have hbase : R ≤ R * (2 : ℝ) ^ n := by
    have hone : (1 : ℝ) ≤ (2 : ℝ) ^ n := one_le_pow₀ (by norm_num)
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hone hR.le
  have hIpos : I ⊆ Set.Ioi (0 : ℝ) := by
    intro r hr
    exact hR.trans_le (hbase.trans hr.1)
  obtain ⟨hinv, hbound⟩ := hrecip n
  refine ⟨hwfull.mono_set hIpos, hinv, ?_, hbound⟩
  filter_upwards [ae_restrict_mem measurableSet_Ico] with r hr
  have hrR : R ≤ r := hbase.trans hr.1
  exact radius_mul_angularWidth_exceptional_pos_of_log_logarithmicMaximum
    hf.1.continuous (hR.trans_le hrR) (hlog r hrR)

/-- Finite area and eventual logarithmic positivity add the ordinary-density clauses to the
two-shift reciprocal estimate. -/
theorem hasTsujiCameraBoundTwoShift_of_reciprocalEstimate {f : ℂ → ℂ} {R A : ℝ}
    (hf : IsNonconstantEntire f) (harea : HasFiniteArea f 1)
    (h : HasTsujiReciprocalEstimateTwoShift f R A) :
    HasTsujiCameraBoundTwoShift f R A := by
  obtain ⟨hR, hA, hlog, hrecip⟩ := h
  refine ⟨hR, hA, hlog, ?_⟩
  have hwfull : IntegrableOn
      (fun r : ℝ ↦ r * angularWidth (exceptionalSet f 1) r) (Set.Ioi 0) :=
    integrableOn_exceptional_radius_mul_angularWidth hf.1.continuous harea
  intro n
  let I := Set.Ico (R * (2 : ℝ) ^ n) (R * (2 : ℝ) ^ (n + 1))
  have hbase : R ≤ R * (2 : ℝ) ^ n := by
    have hone : (1 : ℝ) ≤ (2 : ℝ) ^ n := one_le_pow₀ (by norm_num)
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hone hR.le
  have hIpos : I ⊆ Set.Ioi (0 : ℝ) := by
    intro r hr
    exact hR.trans_le (hbase.trans hr.1)
  obtain ⟨hinv, hbound⟩ := hrecip n
  refine ⟨hwfull.mono_set hIpos, hinv, ?_, hbound⟩
  filter_upwards [ae_restrict_mem measurableSet_Ico] with r hr
  have hrR : R ≤ r := hbase.trans hr.1
  exact radius_mul_angularWidth_exceptional_pos_of_log_logarithmicMaximum
    hf.1.continuous (hR.trans_le hrR) (hlog r hrR)

/-- Reciprocal-width Cauchy--Schwarz turns Tsuji's integral estimate into the pointwise
annular lower bound used by the dyadic summation. -/
theorem hasAnnularCameraLowerBound_of_tsujiCameraBound {f : ℂ → ℂ} {R A : ℝ}
    (h : HasTsujiCameraBound f R A) : HasAnnularCameraLowerBound f R A := by
  obtain ⟨hR, hA, hlog, hTsuji⟩ := h
  refine ⟨hR, hA, hlog, ?_⟩
  intro n
  let q : ℝ := R * (2 : ℝ) ^ n
  let I : Set ℝ := Set.Ico q (2 * q)
  let w : ℝ → ℝ := fun r ↦ r * angularWidth (exceptionalSet f 1) r
  let J : ℝ := ∫ r in I, reciprocalAngularWeight f r
  have hq : 0 < q := mul_pos hR (pow_pos (by norm_num) n)
  have hnext₁ : R * (2 : ℝ) ^ (n + 1) = 2 * q := by
    simp only [q, pow_succ]
    ring
  have hnext₂ : R * (2 : ℝ) ^ (n + 2) = 4 * q := by
    simp only [q, pow_succ]
    ring
  obtain ⟨hw, hinv, hwpos, hJ⟩ := hTsuji n
  have hI : Set.Ico (R * (2 : ℝ) ^ n) (R * (2 : ℝ) ^ (n + 1)) = I := by
    simp only [I, q, hnext₁]
  rw [hI] at hw hinv hwpos hJ
  have hinv' : @IntegrableOn ℝ ℝ Real.measurableSpace _ _
      (fun r ↦ (w r)⁻¹) I volume := by
    unfold reciprocalAngularWeight at hinv
    simpa only [w] using hinv
  have hcs := @measureReal_sq_le_setIntegral_mul_setIntegral_inv
    ℝ Real.measurableSpace volume I w hw hinv' hwpos
  have hmeasure : volume.real I = q := by
    change volume.real (Set.Ico q (2 * q)) = q
    rw [measureReal_def, Real.volume_Ico]
    simp only [ENNReal.toReal_ofReal (by linarith : 0 ≤ 2 * q - q)]
    ring
  rw [hmeasure] at hcs
  have hmass_nonneg : 0 ≤ ∫ r in I, w r := by
    apply integral_nonneg_of_ae
    filter_upwards [hwpos] with r hr
    exact hr.le
  have hmass_pos : 0 < ∫ r in I, w r := by
    by_contra hnot
    have hzero : (∫ r in I, w r) = 0 := le_antisymm (le_of_not_gt hnot) hmass_nonneg
    rw [hzero, zero_mul] at hcs
    nlinarith [sq_pos_of_pos hq]
  refine ⟨?_, ?_⟩
  · simpa only [dyadicAreaMass, hI, w] using hmass_pos
  · intro r hr
    have hJle : J ≤ A * Real.log (logarithmicMaximum f 1 r) := by
      apply hJ r
      simpa only [hnext₁, hnext₂, q] using hr
    have hprod : (∫ t in I, w t) * J ≤
        (∫ t in I, w t) * (A * Real.log (logarithmicMaximum f 1 r)) :=
      mul_le_mul_of_nonneg_left hJle hmass_nonneg
    have hcs' : q ^ 2 ≤ (∫ t in I, w t) * J := by
      simpa only [J, w, reciprocalAngularWeight] using hcs
    calc
      q ^ 2 ≤ (∫ t in I, w t) * J := hcs'
      _ ≤ (∫ t in I, w t) * (A * Real.log (logarithmicMaximum f 1 r)) := hprod
      _ = A * dyadicAreaMass f R n * Real.log (logarithmicMaximum f 1 r) := by
        rw [dyadicAreaMass, hI]
        dsimp only [w]
        ring

/-- Reciprocal-width Cauchy--Schwarz applied to the two-shift Tsuji estimate. -/
theorem hasAnnularCameraLowerBoundTwoShift_of_tsujiCameraBound
    {f : ℂ → ℂ} {R A : ℝ}
    (h : HasTsujiCameraBoundTwoShift f R A) :
    HasAnnularCameraLowerBoundTwoShift f R A := by
  obtain ⟨hR, hA, hlog, hTsuji⟩ := h
  refine ⟨hR, hA, hlog, ?_⟩
  intro n
  let q : ℝ := R * (2 : ℝ) ^ n
  let I : Set ℝ := Set.Ico q (2 * q)
  let w : ℝ → ℝ := fun r ↦ r * angularWidth (exceptionalSet f 1) r
  let J : ℝ := ∫ r in I, reciprocalAngularWeight f r
  have hq : 0 < q := mul_pos hR (pow_pos (by norm_num) n)
  have hnext₁ : R * (2 : ℝ) ^ (n + 1) = 2 * q := by
    simp only [q, pow_succ]
    ring
  have hnext₂ : R * (2 : ℝ) ^ (n + 2) = 4 * q := by
    simp only [q, pow_succ]
    ring
  have hnext₃ : R * (2 : ℝ) ^ (n + 3) = 8 * q := by
    simp only [q, pow_succ]
    ring
  obtain ⟨hw, hinv, hwpos, hJ⟩ := hTsuji n
  have hI : Set.Ico (R * (2 : ℝ) ^ n) (R * (2 : ℝ) ^ (n + 1)) = I := by
    simp only [I, q, hnext₁]
  rw [hI] at hw hinv hwpos hJ
  have hinv' : @IntegrableOn ℝ ℝ Real.measurableSpace _ _
      (fun r ↦ (w r)⁻¹) I volume := by
    unfold reciprocalAngularWeight at hinv
    simpa only [w] using hinv
  have hcs := @measureReal_sq_le_setIntegral_mul_setIntegral_inv
    ℝ Real.measurableSpace volume I w hw hinv' hwpos
  have hmeasure : volume.real I = q := by
    change volume.real (Set.Ico q (2 * q)) = q
    rw [measureReal_def, Real.volume_Ico]
    simp only [ENNReal.toReal_ofReal (by linarith : 0 ≤ 2 * q - q)]
    ring
  rw [hmeasure] at hcs
  have hmass_nonneg : 0 ≤ ∫ r in I, w r := by
    apply integral_nonneg_of_ae
    filter_upwards [hwpos] with r hr
    exact hr.le
  have hmass_pos : 0 < ∫ r in I, w r := by
    by_contra hnot
    have hzero : (∫ r in I, w r) = 0 :=
      le_antisymm (le_of_not_gt hnot) hmass_nonneg
    rw [hzero, zero_mul] at hcs
    nlinarith [sq_pos_of_pos hq]
  refine ⟨?_, ?_⟩
  · simpa only [dyadicAreaMass, hI, w] using hmass_pos
  · intro r hr
    have hJle : J ≤ A * Real.log (logarithmicMaximum f 1 r) := by
      apply hJ r
      simpa only [hnext₂, hnext₃, q] using hr
    have hprod : (∫ t in I, w t) * J ≤
        (∫ t in I, w t) * (A * Real.log (logarithmicMaximum f 1 r)) :=
      mul_le_mul_of_nonneg_left hJle hmass_nonneg
    have hcs' : q ^ 2 ≤ (∫ t in I, w t) * J := by
      simpa only [J, w, reciprocalAngularWeight] using hcs
    calc
      q ^ 2 ≤ (∫ t in I, w t) * J := hcs'
      _ ≤ (∫ t in I, w t) *
          (A * Real.log (logarithmicMaximum f 1 r)) := hprod
      _ = A * dyadicAreaMass f R n *
          Real.log (logarithmicMaximum f 1 r) := by
        rw [dyadicAreaMass, hI]
        dsimp only [w]
        ring

theorem norm_cameraIntegrand_le_on_dyadic {f : ℂ → ℂ} {R A : ℝ}
    (h : HasAnnularCameraLowerBound f R A) (n : ℕ) {r : ℝ}
    (hr : r ∈ Set.Ico (R * (2 : ℝ) ^ (n + 1)) (R * (2 : ℝ) ^ (n + 2))) :
    ‖cameraIntegrand f r‖ ≤
      4 * A * dyadicAreaMass f R n / (R * (2 : ℝ) ^ n) := by
  obtain ⟨hR, hA, hpos, hann⟩ := h
  let q : ℝ := R * (2 : ℝ) ^ n
  let m : ℝ := dyadicAreaMass f R n
  let d : ℝ := Real.log (logarithmicMaximum f 1 r)
  have hq : 0 < q := mul_pos hR (pow_pos (by norm_num) n)
  have hqR : R ≤ q := by
    have hone : (1 : ℝ) ≤ (2 : ℝ) ^ n := one_le_pow₀ (by norm_num)
    simpa only [q, mul_one] using mul_le_mul_of_nonneg_left hone hR.le
  have hrR : R ≤ r := hqR.trans (le_trans (by
    have : q ≤ R * (2 : ℝ) ^ (n + 1) := by
      simp only [q, pow_succ]
      nlinarith
    exact this) hr.1)
  have hd : 0 < d := hpos r hrR
  have hm : 0 < m := (hann n).1
  have hlower : q ^ 2 ≤ A * m * d := by
    simpa only [q, m, d] using (hann n).2 r hr
  have hquot : q / d ≤ A * m / q := by
    apply (div_le_div_iff₀ hd hq).mpr
    simpa only [pow_two] using hlower
  have hnext₂ : R * (2 : ℝ) ^ (n + 2) = 4 * q := by
    simp only [q, pow_succ]
    ring
  have hrle : r ≤ 4 * q := by
    rw [← hnext₂]
    exact hr.2.le
  have hcam : 0 ≤ cameraIntegrand f r := by
    unfold cameraIntegrand
    exact div_nonneg (hR.le.trans hrR) hd.le
  rw [Real.norm_eq_abs, abs_of_nonneg hcam]
  unfold cameraIntegrand
  change r / d ≤ 4 * A * m / q
  calc
    r / d ≤ (4 * q) / d := div_le_div_of_nonneg_right hrle hd.le
    _ = 4 * (q / d) := by ring
    _ ≤ 4 * (A * m / q) := mul_le_mul_of_nonneg_left hquot (by norm_num)
    _ = 4 * A * m / q := by ring

/-- Pointwise growth-integrand majorization on the two-shift target annulus. -/
theorem norm_cameraIntegrand_le_on_dyadic_twoShift {f : ℂ → ℂ} {R A : ℝ}
    (h : HasAnnularCameraLowerBoundTwoShift f R A) (n : ℕ) {r : ℝ}
    (hr : r ∈ Set.Ico (R * (2 : ℝ) ^ (n + 2)) (R * (2 : ℝ) ^ (n + 3))) :
    ‖cameraIntegrand f r‖ ≤
      8 * A * dyadicAreaMass f R n / (R * (2 : ℝ) ^ n) := by
  obtain ⟨hR, hA, hpos, hann⟩ := h
  let q : ℝ := R * (2 : ℝ) ^ n
  let m : ℝ := dyadicAreaMass f R n
  let d : ℝ := Real.log (logarithmicMaximum f 1 r)
  have hq : 0 < q := mul_pos hR (pow_pos (by norm_num) n)
  have hqR : R ≤ q := by
    have hone : (1 : ℝ) ≤ (2 : ℝ) ^ n := one_le_pow₀ (by norm_num)
    simpa only [q, mul_one] using mul_le_mul_of_nonneg_left hone hR.le
  have hn2 : q ≤ R * (2 : ℝ) ^ (n + 2) := by
    simp only [q, pow_succ]
    nlinarith
  have hrR : R ≤ r := hqR.trans (hn2.trans hr.1)
  have hd : 0 < d := hpos r hrR
  have hm : 0 < m := (hann n).1
  have hlower : q ^ 2 ≤ A * m * d := by
    simpa only [q, m, d] using (hann n).2 r hr
  have hquot : q / d ≤ A * m / q := by
    apply (div_le_div_iff₀ hd hq).mpr
    simpa only [pow_two] using hlower
  have hnext₃ : R * (2 : ℝ) ^ (n + 3) = 8 * q := by
    simp only [q, pow_succ]
    ring
  have hrle : r ≤ 8 * q := by
    rw [← hnext₃]
    exact hr.2.le
  have hcam : 0 ≤ cameraIntegrand f r := by
    unfold cameraIntegrand
    exact div_nonneg (hR.le.trans hrR) hd.le
  rw [Real.norm_eq_abs, abs_of_nonneg hcam]
  unfold cameraIntegrand
  change r / d ≤ 8 * A * m / q
  calc
    r / d ≤ (8 * q) / d := div_le_div_of_nonneg_right hrle hd.le
    _ = 8 * (q / d) := by ring
    _ ≤ 8 * (A * m / q) := mul_le_mul_of_nonneg_left hquot (by norm_num)
    _ = 8 * A * m / q := by ring

theorem integrableOn_cameraIntegrand_dyadic {f : ℂ → ℂ} {R A : ℝ}
    (hf : Continuous f) (h : HasAnnularCameraLowerBound f R A) (n : ℕ) :
    IntegrableOn (cameraIntegrand f)
      (Set.Ico (R * (2 : ℝ) ^ (n + 1)) (R * (2 : ℝ) ^ (n + 2))) := by
  obtain ⟨hR, -, hpos, -⟩ := h
  have hcont := continuousOn_cameraIntegrand hf hR hpos
  have hqR : R ≤ R * (2 : ℝ) ^ (n + 1) := by
    have hone : (1 : ℝ) ≤ (2 : ℝ) ^ (n + 1) := one_le_pow₀ (by norm_num)
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hone hR.le
  have hcontIcc : ContinuousOn (cameraIntegrand f)
      (Set.Icc (R * (2 : ℝ) ^ (n + 1)) (R * (2 : ℝ) ^ (n + 2))) := by
    apply hcont.mono
    intro r hr
    exact hqR.trans hr.1
  exact hcontIcc.integrableOn_Icc.mono_set Set.Ico_subset_Icc_self

theorem integrableOn_cameraIntegrand_dyadic_twoShift {f : ℂ → ℂ} {R A : ℝ}
    (hf : Continuous f) (h : HasAnnularCameraLowerBoundTwoShift f R A) (n : ℕ) :
    IntegrableOn (cameraIntegrand f)
      (Set.Ico (R * (2 : ℝ) ^ (n + 2)) (R * (2 : ℝ) ^ (n + 3))) := by
  obtain ⟨hR, -, hpos, -⟩ := h
  have hcont := continuousOn_cameraIntegrand hf hR hpos
  have hqR : R ≤ R * (2 : ℝ) ^ (n + 2) := by
    have hone : (1 : ℝ) ≤ (2 : ℝ) ^ (n + 2) := one_le_pow₀ (by norm_num)
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hone hR.le
  have hcontIcc : ContinuousOn (cameraIntegrand f)
      (Set.Icc (R * (2 : ℝ) ^ (n + 2)) (R * (2 : ℝ) ^ (n + 3))) := by
    apply hcont.mono
    intro r hr
    exact hqR.trans hr.1
  exact hcontIcc.integrableOn_Icc.mono_set Set.Ico_subset_Icc_self

theorem integral_norm_cameraIntegrand_dyadic_le {f : ℂ → ℂ} {R A : ℝ}
    (h : HasAnnularCameraLowerBound f R A) (n : ℕ) :
    (∫ r in Set.Ico (R * (2 : ℝ) ^ (n + 1)) (R * (2 : ℝ) ^ (n + 2)),
        ‖cameraIntegrand f r‖) ≤
      8 * A * dyadicAreaMass f R n := by
  have hcopy := h
  obtain ⟨hR, hA, hpos, hann⟩ := h
  let q : ℝ := R * (2 : ℝ) ^ n
  let m : ℝ := dyadicAreaMass f R n
  let K : ℝ := 4 * A * m / q
  have hq : 0 < q := mul_pos hR (pow_pos (by norm_num) n)
  have hm : 0 < m := (hann n).1
  have hnext₁ : R * (2 : ℝ) ^ (n + 1) = 2 * q := by
    simp only [q, pow_succ]
    ring
  have hnext₂ : R * (2 : ℝ) ^ (n + 2) = 4 * q := by
    simp only [q, pow_succ]
    ring
  have hconst : IntegrableOn (fun _ : ℝ ↦ K) (Set.Ico (2 * q) (4 * q)) :=
    continuousOn_const.integrableOn_Icc.mono_set Set.Ico_subset_Icc_self
  have hmono : (∫ r in Set.Ico (2 * q) (4 * q), ‖cameraIntegrand f r‖) ≤
      ∫ _ in Set.Ico (2 * q) (4 * q), K := by
    apply setIntegral_mono_of_nonneg
    · intro r hr
      exact norm_nonneg _
    · intro r hr
      apply norm_cameraIntegrand_le_on_dyadic hcopy n
      simpa only [q, hnext₁, hnext₂] using hr
    · exact hconst
  rw [hnext₁, hnext₂]
  change (∫ r in Set.Ico (2 * q) (4 * q), ‖cameraIntegrand f r‖) ≤ 8 * A * m
  calc
    (∫ r in Set.Ico (2 * q) (4 * q), ‖cameraIntegrand f r‖)
        ≤ ∫ _ in Set.Ico (2 * q) (4 * q), K := hmono
    _ = (2 * q) * K := by
      rw [setIntegral_const, smul_eq_mul, measureReal_def, Real.volume_Ico]
      simp only [ENNReal.toReal_ofReal (by linarith : 0 ≤ 4 * q - 2 * q)]
      ring
    _ = 8 * A * m := by
      dsimp only [K]
      field_simp
      ring

theorem integral_norm_cameraIntegrand_dyadic_twoShift_le
    {f : ℂ → ℂ} {R A : ℝ}
    (h : HasAnnularCameraLowerBoundTwoShift f R A) (n : ℕ) :
    (∫ r in Set.Ico (R * (2 : ℝ) ^ (n + 2)) (R * (2 : ℝ) ^ (n + 3)),
        ‖cameraIntegrand f r‖) ≤
      32 * A * dyadicAreaMass f R n := by
  have hcopy := h
  obtain ⟨hR, hA, hpos, hann⟩ := h
  let q : ℝ := R * (2 : ℝ) ^ n
  let m : ℝ := dyadicAreaMass f R n
  let K : ℝ := 8 * A * m / q
  have hq : 0 < q := mul_pos hR (pow_pos (by norm_num) n)
  have hm : 0 < m := (hann n).1
  have hnext₂ : R * (2 : ℝ) ^ (n + 2) = 4 * q := by
    simp only [q, pow_succ]
    ring
  have hnext₃ : R * (2 : ℝ) ^ (n + 3) = 8 * q := by
    simp only [q, pow_succ]
    ring
  have hconst : IntegrableOn (fun _ : ℝ ↦ K) (Set.Ico (4 * q) (8 * q)) :=
    continuousOn_const.integrableOn_Icc.mono_set Set.Ico_subset_Icc_self
  have hmono : (∫ r in Set.Ico (4 * q) (8 * q), ‖cameraIntegrand f r‖) ≤
      ∫ _ in Set.Ico (4 * q) (8 * q), K := by
    apply setIntegral_mono_of_nonneg
    · intro r hr
      exact norm_nonneg _
    · intro r hr
      apply norm_cameraIntegrand_le_on_dyadic_twoShift hcopy n
      simpa only [q, hnext₂, hnext₃] using hr
    · exact hconst
  rw [hnext₂, hnext₃]
  change (∫ r in Set.Ico (4 * q) (8 * q), ‖cameraIntegrand f r‖) ≤ 32 * A * m
  calc
    (∫ r in Set.Ico (4 * q) (8 * q), ‖cameraIntegrand f r‖)
        ≤ ∫ _ in Set.Ico (4 * q) (8 * q), K := hmono
    _ = (4 * q) * K := by
      rw [setIntegral_const, smul_eq_mul, measureReal_def, Real.volume_Ico]
      simp only [ENNReal.toReal_ofReal (by linarith : 0 ≤ 8 * q - 4 * q)]
      ring
    _ = 32 * A * m := by
      dsimp only [K]
      field_simp
      ring

theorem hasDyadicCameraEstimate_of_annularLowerBound {f : ℂ → ℂ} {R A : ℝ}
    (hf : Continuous f) (h : HasAnnularCameraLowerBound f R A) :
    HasDyadicCameraEstimate f R (8 * A) := by
  have hcopy := h
  obtain ⟨hR, hA, hpos, hann⟩ := h
  refine ⟨hR, mul_pos (by norm_num) hA, hpos, ?_, ?_⟩
  · intro n
    exact integrableOn_cameraIntegrand_dyadic hf hcopy n
  · intro n
    exact integral_norm_cameraIntegrand_dyadic_le hcopy n

theorem hasDyadicCameraEstimateTwoShift_of_annularLowerBound
    {f : ℂ → ℂ} {R A : ℝ}
    (hf : Continuous f) (h : HasAnnularCameraLowerBoundTwoShift f R A) :
    HasDyadicCameraEstimateTwoShift f R (32 * A) := by
  have hcopy := h
  obtain ⟨hR, hA, hpos, hann⟩ := h
  refine ⟨hR, mul_pos (by norm_num) hA, hpos, ?_, ?_⟩
  · intro n
    exact integrableOn_cameraIntegrand_dyadic_twoShift hf hcopy n
  · intro n
    exact integral_norm_cameraIntegrand_dyadic_twoShift_le hcopy n

/-- A one-shift annular packaging of the quantitative Tsuji--Carleman conclusion. -/
def NormalizedAnnularCameraTheorem : Prop :=
  ∀ f : ℂ → ℂ,
    IsNonconstantEntire f → HasFiniteArea f 1 →
      ∃ R A, HasAnnularCameraLowerBound f R A

/-- The one-shift reciprocal-width formulation, retained for comparison with the endpoint-stable
two-shift theorem proved above. -/
def NormalizedTsujiCameraTheorem : Prop :=
  ∀ f : ℂ → ℂ,
    IsNonconstantEntire f → HasFiniteArea f 1 →
      ∃ R A, HasTsujiReciprocalEstimate f R A

theorem normalizedAnnularCameraTheorem_of_normalizedTsujiCameraTheorem
    (htsuji : NormalizedTsujiCameraTheorem) : NormalizedAnnularCameraTheorem := by
  intro f hf harea
  obtain ⟨R, A, h⟩ := htsuji f hf harea
  exact ⟨R, A, hasAnnularCameraLowerBound_of_tsujiCameraBound
    (hasTsujiCameraBound_of_reciprocalEstimate hf harea h)⟩

/-- A one-shift dyadic formulation of the normalized area--growth estimate. -/
def NormalizedDyadicCameraTheorem : Prop :=
  ∀ f : ℂ → ℂ,
    IsNonconstantEntire f → HasFiniteArea f 1 →
      ∃ R C, HasDyadicCameraEstimate f R C

theorem normalizedDyadicCameraTheorem_of_normalizedAnnularCameraTheorem
    (hannular : NormalizedAnnularCameraTheorem) : NormalizedDyadicCameraTheorem := by
  intro f hf harea
  obtain ⟨R, A, h⟩ := hannular f hf harea
  exact ⟨R, 8 * A, hasDyadicCameraEstimate_of_annularLowerBound hf.1.continuous h⟩

theorem normalizedAreaGrowthTheorem_of_normalizedDyadicCameraTheorem
    (hdyadic : NormalizedDyadicCameraTheorem) : NormalizedAreaGrowthTheorem := by
  intro f hf harea
  obtain ⟨R, C, hR, hC, hpos, hlocal, hbound⟩ := hdyadic f hf harea
  have hwfull : IntegrableOn
      (fun r : ℝ ↦ r * angularWidth (exceptionalSet f 1) r) (Set.Ioi 0) :=
    integrableOn_exceptional_radius_mul_angularWidth hf.1.continuous harea
  have hw : IntegrableOn
      (fun r : ℝ ↦ r * angularWidth (exceptionalSet f 1) r) (Set.Ici R) := by
    apply hwfull.mono_set
    intro r hr
    exact hR.trans_le hr
  have hintIci : IntegrableOn (cameraIntegrand f) (Set.Ici (2 * R)) :=
    integrableOn_Ici_two_mul_of_shifted_dyadic_bounds hR hw hlocal (by
      intro n
      simpa only [dyadicAreaMass] using hbound n)
  have htwoR : 0 < 2 * R := mul_pos (by norm_num) hR
  refine ⟨2 * R, htwoR, ?_, ?_⟩
  · intro r hr
    exact hpos r (by nlinarith)
  exact hintIci.mono_set Set.Ioi_subset_Ici_self

/-- Camera's normalized area--growth theorem, proved from the endpoint-stable two-shift
Tsuji estimate above. -/
theorem normalizedAreaGrowthTheorem : NormalizedAreaGrowthTheorem := by
  intro f hf harea
  obtain ⟨R, A, hrecip⟩ := hasTsujiReciprocalEstimateTwoShift hf harea
  have htsuji : HasTsujiCameraBoundTwoShift f R A :=
    hasTsujiCameraBoundTwoShift_of_reciprocalEstimate hf harea hrecip
  have hann : HasAnnularCameraLowerBoundTwoShift f R A :=
    hasAnnularCameraLowerBoundTwoShift_of_tsujiCameraBound htsuji
  have hdyadic : HasDyadicCameraEstimateTwoShift f R (32 * A) :=
    hasDyadicCameraEstimateTwoShift_of_annularLowerBound hf.1.continuous hann
  obtain ⟨hR, hC, hpos, hlocal, hbound⟩ := hdyadic
  have hwfull : IntegrableOn
      (fun r : ℝ ↦ r * angularWidth (exceptionalSet f 1) r) (Set.Ioi 0) :=
    integrableOn_exceptional_radius_mul_angularWidth hf.1.continuous harea
  have hw : IntegrableOn
      (fun r : ℝ ↦ r * angularWidth (exceptionalSet f 1) r) (Set.Ici R) := by
    apply hwfull.mono_set
    intro r hr
    exact hR.trans_le hr
  have hintIci : IntegrableOn (cameraIntegrand f) (Set.Ici (4 * R)) :=
    integrableOn_Ici_four_mul_of_two_shifted_dyadic_bounds hR hw hlocal (by
      intro n
      simpa only [dyadicAreaMass] using hbound n)
  have hfourR : 0 < 4 * R := mul_pos (by norm_num) hR
  refine ⟨4 * R, hfourR, ?_, ?_⟩
  · intro r hr
    exact hpos r (by nlinarith)
  · exact hintIci.mono_set Set.Ioi_subset_Ici_self

/-- Camera's normalized area--growth estimate implies convergence of Hayman's integral, since
the two integrands agree once the positive logarithmic maximum exceeds `1`. -/
theorem normalizedCameraTheorem_of_normalizedAreaGrowthTheorem
    (hcore : NormalizedAreaGrowthTheorem) :
    ∀ f : ℂ → ℂ,
      IsNonconstantEntire f → HasFiniteArea f 1 → GrowthIntegralConverges f := by
  intro f hf harea
  obtain ⟨R, hR, hpos, hint⟩ := hcore f hf harea
  have hM : ∀ r, R ≤ r → 1 ≤ maximumModulus f r := by
    intro r hr
    have hr0 : 0 ≤ r := hR.le.trans hr
    have hBnonneg : 0 ≤ logarithmicMaximum f 1 r := Real.posLog_nonneg
    have hBone : 1 < logarithmicMaximum f 1 r :=
      (Real.log_pos_iff hBnonneg).mp (hpos r hr)
    have hnot : ¬ |maximumModulus f r| ≤ 1 := by
      intro hle
      have hzero : Real.posLog (maximumModulus f r) = 0 :=
        (Real.posLog_eq_zero_iff _).mpr hle
      have : logarithmicMaximum f 1 r = 0 := by
        simpa [logarithmicMaximum] using hzero
      linarith
    have habs : 1 < |maximumModulus f r| := lt_of_not_ge hnot
    rw [abs_of_nonneg (maximumModulus_nonneg hf.1.continuous hr0)] at habs
    exact habs.le
  have heq : ∀ r, R ≤ r →
      growthIntegrand f r = cameraIntegrand f r := by
    intro r hr
    unfold growthIntegrand cameraIntegrand
    rw [logarithmicMaximum_one_eq_log hf.1.continuous (hR.le.trans hr) (hM r hr)]
  refine ⟨R, hR, ?_, ?_⟩
  · intro r hr
    have hp := hpos r hr
    rw [logarithmicMaximum_one_eq_log hf.1.continuous (hR.le.trans hr) (hM r hr)] at hp
    exact hp
  · apply hint.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    exact (heq r hr.le).symm

/-- Convergence of the growth integral is preserved when a function is divided or multiplied
by a positive real constant.  This direction is the one needed after normalizing an exceptional
level to `1`. -/
theorem growthIntegralConverges_of_const_mul {f : ℂ → ℂ}
    (hf : IsNonconstantEntire f) {a : ℝ} (ha : 0 < a)
    (hscaled : GrowthIntegralConverges (fun z ↦ (a : ℂ) * f z)) :
    GrowthIntegralConverges f := by
  obtain ⟨Rs, hRs, hposs, hints⟩ := hscaled
  obtain ⟨Rc, hRc, hcomp⟩ := eventually_log_log_const_mul_le_two hf ha
  let R := max Rs Rc
  have hR : 0 < R := hRs.trans_le (le_max_left _ _)
  have hpos : ∀ r, R ≤ r →
      0 < Real.log (Real.log (maximumModulus f r)) := by
    intro r hr
    exact (hcomp r ((le_max_right _ _).trans hr)).1
  refine ⟨R, hR, hpos, ?_⟩
  have hsubset : Set.Ioi R ⊆ Set.Ioi Rs := by
    intro r hr
    exact (le_max_left Rs Rc).trans_lt (Set.mem_Ioi.mp hr)
  have hintTail : IntegrableOn
      (growthIntegrand (fun z ↦ (a : ℂ) * f z)) (Set.Ioi R) :=
    hints.mono_set hsubset
  have hintScaled : IntegrableOn
      (fun r ↦ 2 * growthIntegrand (fun z ↦ (a : ℂ) * f z) r) (Set.Ioi R) :=
    hintTail.const_mul 2
  have hmeas : AEStronglyMeasurable (growthIntegrand f)
      ((volume : Measure ℝ).restrict (Set.Ioi R)) :=
    (continuousOn_growthIntegrand hf.1.continuous hR hpos).aestronglyMeasurable
      measurableSet_Ioi
  refine hintScaled.mono_nonneg hmeas ?_ ?_
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    unfold growthIntegrand
    exact div_nonneg (hR.le.trans hr.le) (hpos r hr.le).le
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    have hrc : Rc ≤ r := (le_max_right _ _).trans hr.le
    obtain ⟨hdf, hdg, hle⟩ := hcomp r hrc
    have hrr : 0 ≤ r := hR.le.trans hr.le
    have hmax : maximumModulus (fun z ↦ (a : ℂ) * f z) r =
        a * maximumModulus f r := by
      simpa [Complex.norm_real, abs_of_pos ha] using
        (maximumModulus_const_mul hf.1.continuous (a : ℂ) hrr)
    have hrecip : 1 / Real.log (Real.log (maximumModulus f r)) ≤
        2 / Real.log (Real.log (a * maximumModulus f r)) := by
      apply (div_le_div_iff₀ hdf hdg).mpr
      simpa only [one_mul] using hle
    unfold growthIntegrand
    rw [hmax]
    calc
      r / Real.log (Real.log (maximumModulus f r)) =
          r * (1 / Real.log (Real.log (maximumModulus f r))) := by ring
      _ ≤ r * (2 / Real.log (Real.log (a * maximumModulus f r))) :=
        mul_le_mul_of_nonneg_left hrecip hrr
      _ = 2 * (r / Real.log (Real.log (a * maximumModulus f r))) := by ring

/-- The set `T_f` of positive levels whose strict superlevel set has finite area. -/
def thresholdSet (f : ℂ → ℂ) : Set ℝ :=
  {c | 0 < c ∧ HasFiniteArea f c}

theorem exceptionalSet_antitone {f : ℂ → ℂ} {a b : ℝ} (hab : a ≤ b) :
    exceptionalSet f b ⊆ exceptionalSet f a := by
  intro z hz
  exact hab.trans_lt hz

theorem hasFiniteArea_mono {f : ℂ → ℂ} {a b : ℝ} (hab : a ≤ b)
    (ha : HasFiniteArea f a) : HasFiniteArea f b := by
  unfold HasFiniteArea at ha ⊢
  exact ne_top_of_le_ne_top ha (measure_mono (exceptionalSet_antitone hab))

theorem thresholdSet_upward {f : ℂ → ℂ} {a b : ℝ} (ha : a ∈ thresholdSet f)
    (hab : a ≤ b) : b ∈ thresholdSet f := by
  exact ⟨ha.1.trans_le hab, hasFiniteArea_mono hab ha.2⟩

/-- Every threshold set has one of the four interval shapes listed by Gol'dberg.  This part is
purely order-theoretic; the difficult theorem is that both positive-endpoint shapes occur. -/
theorem thresholdSet_shape (f : ℂ → ℂ) :
    thresholdSet f = ∅ ∨ thresholdSet f = Set.Ioi 0 ∨
      ∃ m > 0, thresholdSet f = Set.Ici m ∨ thresholdSet f = Set.Ioi m := by
  by_cases hempty : thresholdSet f = ∅
  · exact Or.inl hempty
  right
  have hne : (thresholdSet f).Nonempty := Set.nonempty_iff_ne_empty.mpr hempty
  have hbdd : BddBelow (thresholdSet f) := by
    refine ⟨0, ?_⟩
    intro c hc
    exact hc.1.le
  let m : ℝ := sInf (thresholdSet f)
  have hm_nonneg : 0 ≤ m := by
    exact le_csInf hne fun c hc ↦ hc.1.le
  by_cases hm0 : m = 0
  · left
    ext c
    constructor
    · exact fun hc ↦ hc.1
    · intro hc
      change 0 < c at hc
      have hmc : m < c := by simpa [hm0] using hc
      obtain ⟨a, haT, hac⟩ := exists_lt_of_csInf_lt hne hmc
      exact thresholdSet_upward haT hac.le
  · right
    have hm : 0 < m := lt_of_le_of_ne hm_nonneg (Ne.symm hm0)
    refine ⟨m, hm, ?_⟩
    by_cases hmT : m ∈ thresholdSet f
    · left
      ext c
      constructor
      · intro hc
        exact csInf_le hbdd hc
      · intro hc
        change m ≤ c at hc
        exact thresholdSet_upward hmT hc
    · right
      ext c
      constructor
      · intro hc
        have hmc : m ≤ c := csInf_le hbdd hc
        exact lt_of_le_of_ne hmc fun hcm ↦ hmT (hcm ▸ hc)
      · intro hc
        change m < c at hc
        obtain ⟨a, haT, hac⟩ := exists_lt_of_csInf_lt hne hc
        exact thresholdSet_upward haT hac.le

/-- The identity function realizes the empty threshold set. -/
theorem thresholdSet_id : thresholdSet (fun z : ℂ ↦ z) = ∅ := by
  ext c
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hc
  have hcpos : 0 < c := hc.1
  have hset : exceptionalSet (fun z : ℂ ↦ z) c = (Metric.closedBall (0 : ℂ) c)ᶜ := by
    ext z
    simp [exceptionalSet, Metric.mem_closedBall, dist_zero_right]
  have hball : volume (Metric.closedBall (0 : ℂ) c) ≠ ∞ :=
    ne_of_lt ((isCompact_closedBall (0 : ℂ) c).measure_lt_top)
  have htop : volume (exceptionalSet (fun z : ℂ ↦ z) c) = ∞ := by
    rw [hset]
    exact volume_compl_eq_top_of_ne_top hball
  exact hc.2 htop

@[simp] theorem exceptionalSet_zero_smul (f : ℂ → ℂ) (c : ℝ) :
    exceptionalSet (fun z ↦ (0 : ℂ) * f z) c =
      if c < 0 then Set.univ else ∅ := by
  ext z
  simp [exceptionalSet]

theorem exceptionalSet_const_mul {f : ℂ → ℂ} {a c : ℝ} (ha : 0 < a) :
    exceptionalSet (fun z ↦ (a : ℂ) * f z) c = exceptionalSet f (c / a) := by
  ext z
  simp only [exceptionalSet, Set.mem_ofPred_eq, norm_mul, Complex.norm_real]
  rw [Real.norm_eq_abs, abs_of_pos ha, div_lt_iff₀ ha, mul_comm]

theorem hasFiniteArea_const_mul {f : ℂ → ℂ} {a c : ℝ} (ha : 0 < a) :
    HasFiniteArea (fun z ↦ (a : ℂ) * f z) c ↔ HasFiniteArea f (c / a) := by
  simp only [HasFiniteArea, exceptionalSet_const_mul ha]

theorem thresholdSet_const_mul {f : ℂ → ℂ} {a : ℝ} (ha : 0 < a) :
    thresholdSet (fun z ↦ (a : ℂ) * f z) =
      (fun d : ℝ ↦ a * d) '' thresholdSet f := by
  ext c
  constructor
  · rintro ⟨hc, harea⟩
    refine ⟨c / a, ⟨div_pos hc ha, ?_⟩, ?_⟩
    · exact (hasFiniteArea_const_mul ha).mp harea
    · field_simp
  · rintro ⟨d, ⟨hd, harea⟩, rfl⟩
    refine ⟨mul_pos ha hd, ?_⟩
    rw [hasFiniteArea_const_mul ha]
    simpa [ha.ne'] using harea

/-- The exact closed-endpoint witness asserted by Gol'dberg. -/
def ClosedThresholdWitness (m : ℝ) : Prop :=
  ∃ f : ℂ → ℂ, IsNonconstantEntire f ∧ thresholdSet f = Set.Ici m

/-- The exact open-endpoint witness asserted by Gol'dberg. -/
def OpenThresholdWitness (m : ℝ) : Prop :=
  ∃ f : ℂ → ℂ, IsNonconstantEntire f ∧ thresholdSet f = Set.Ioi m

/-- The literal negative answer requested in the second part of Problem 1118. -/
def NegativeAnswer : Prop :=
  ∃ (f : ℂ → ℂ) (c : ℝ),
    IsNonconstantEntire f ∧ 0 < c ∧ HasFiniteArea f c ∧
      ∀ c', 0 < c' → c' < c → ¬ HasFiniteArea f c'

theorem closedThresholdWitness_gives_negativeAnswer {m : ℝ} (hm : 0 < m)
    (h : ClosedThresholdWitness m) : NegativeAnswer := by
  obtain ⟨f, hf, hT⟩ := h
  refine ⟨f, m, hf, hm, ?_, ?_⟩
  · have hmT : m ∈ thresholdSet f := by
      rw [hT]
      exact Set.mem_Ici.mpr le_rfl
    exact hmT.2
  · intro c hc hcm harea
    have hcT : c ∈ thresholdSet f := ⟨hc, harea⟩
    rw [hT] at hcT
    exact (not_le_of_gt hcm) hcT

theorem closedThresholdWitness_scale {m : ℝ} (hm : 0 < m)
    (h : ClosedThresholdWitness 1) : ClosedThresholdWitness m := by
  obtain ⟨f, hf, hT⟩ := h
  refine ⟨fun z ↦ (m : ℂ) * f z, ?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · exact hf.1.const_mul (m : ℂ)
    · obtain ⟨x, y, hxy⟩ := hf.2
      refine ⟨x, y, ?_⟩
      intro h
      exact hxy (mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr hm.ne') h)
  · rw [thresholdSet_const_mul hm, hT]
    ext c
    constructor
    · rintro ⟨d, hd, rfl⟩
      change m ≤ m * d
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hd hm.le
    · intro hc
      change m ≤ c at hc
      refine ⟨c / m, ?_, ?_⟩
      · change 1 ≤ c / m
        apply (le_div_iff₀ hm).mpr
        simpa only [one_mul] using hc
      · field_simp

theorem openThresholdWitness_scale {m : ℝ} (hm : 0 < m)
    (h : OpenThresholdWitness 1) : OpenThresholdWitness m := by
  obtain ⟨f, hf, hT⟩ := h
  refine ⟨fun z ↦ (m : ℂ) * f z, ?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · exact hf.1.const_mul (m : ℂ)
    · obtain ⟨x, y, hxy⟩ := hf.2
      refine ⟨x, y, ?_⟩
      intro h
      exact hxy (mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr hm.ne') h)
  · rw [thresholdSet_const_mul hm, hT]
    ext c
    constructor
    · rintro ⟨d, hd, rfl⟩
      change m < m * d
      simpa only [mul_one] using mul_lt_mul_of_pos_left hd hm
    · intro hc
      change m < c at hc
      refine ⟨c / m, ?_, ?_⟩
      · change 1 < c / m
        apply (lt_div_iff₀ hm).mpr
        simpa only [one_mul] using hc
      · field_simp

/-! ## Gol'dberg's two endpoint examples -/

open Erdos1118Construction

lemma closedEndpoint_isNonconstantEntire :
    IsNonconstantEntire (endpointFunction closedEndpointTarget) :=
  ⟨endpointFunction_differentiable closedEndpointTarget,
    endpointFunction_nonconstant closedEndpointTarget⟩

lemma openEndpoint_isNonconstantEntire :
    IsNonconstantEntire (endpointFunction openEndpointTarget) :=
  ⟨endpointFunction_differentiable openEndpointTarget,
    endpointFunction_nonconstant openEndpointTarget⟩

lemma closedEndpoint_hasFiniteArea_one :
    HasFiniteArea (endpointFunction closedEndpointTarget) 1 := by
  apply ne_top_of_le_ne_top (volume_endpointBadSet_union_closedBall_ne_top 1)
  apply measure_mono
  intro z hz
  by_contra hzunion
  have hzbad : z ∉ endpointBadSet := fun h ↦ hzunion (Or.inl h)
  have hzball : z ∉ Metric.closedBall (0 : ℂ) 1 := fun h ↦ hzunion (Or.inr h)
  have hznorm : 1 < ‖z‖ := by
    simpa [Metric.mem_closedBall, dist_zero_right, not_le] using hzball
  obtain ⟨n, hzS, hzT, hzcorr⟩ := exists_endpointBulkIndex hznorm hzbad
  have hlt := (closedEndpointFunction_bounds_on_bulk n hzS hzT hzcorr).2
  exact (not_lt_of_ge hz.le) hlt

lemma closedEndpoint_volume_exceptionalSet_eq_top {c : ℝ} (hc : c < 1) :
    volume (exceptionalSet (endpointFunction closedEndpointTarget) c) = ∞ := by
  have hpos : 0 < 1 - c := sub_pos.mpr hc
  have hlim : Tendsto (fun n : ℕ ↦ 2 * endpointMargin n) atTop (𝓝 0) := by
    convert endpointMargin_tendsto_zero.const_mul 2 using 1 <;> simp
  have hev : ∀ᶠ n : ℕ in atTop, 2 * endpointMargin n < 1 - c :=
    hlim.eventually (Iio_mem_nhds hpos)
  obtain ⟨N, hN⟩ := eventually_atTop.1 hev
  let s : Set ℂ :=
    (endpointBadSet ∪ Metric.closedBall (0 : ℂ) (endpointOuterRadius N))ᶜ
  have hsvol : volume s = ∞ := by
    exact volume_compl_eq_top_of_ne_top
      (volume_endpointBadSet_union_closedBall_ne_top (endpointOuterRadius N))
  have hsub : s ⊆ exceptionalSet (endpointFunction closedEndpointTarget) c := by
    intro z hz
    have hznot : z ∉ endpointBadSet ∪
        Metric.closedBall (0 : ℂ) (endpointOuterRadius N) := hz
    have hzbad : z ∉ endpointBadSet := fun h ↦ hznot (Or.inl h)
    have hzball : z ∉ Metric.closedBall (0 : ℂ) (endpointOuterRadius N) :=
      fun h ↦ hznot (Or.inr h)
    have hzlarge : endpointOuterRadius N < ‖z‖ := by
      simpa [Metric.mem_closedBall, dist_zero_right, not_le] using hzball
    have hznorm : 1 < ‖z‖ := by
      have hR : 1 ≤ endpointOuterRadius N := by
        unfold endpointOuterRadius
        have hN0 : (0 : ℝ) ≤ (N : ℝ) := by positivity
        linarith
      exact hR.trans_lt hzlarge
    obtain ⟨n, hzS, hzT, hzcorr⟩ := exists_endpointBulkIndex hznorm hzbad
    have hNn : N ≤ n := by
      unfold endpointOuterRadius at hzlarge hzT
      push_cast at hzlarge hzT
      exact_mod_cast (show (N : ℝ) ≤ n by linarith)
    have hm := hN n hNn
    have hbulk := (closedEndpointFunction_bounds_on_bulk n hzS hzT hzcorr).1
    exact lt_trans (by linarith) hbulk
  apply top_unique
  rw [← hsvol]
  exact measure_mono hsub

theorem closedThresholdWitness_one : ClosedThresholdWitness 1 := by
  refine ⟨endpointFunction closedEndpointTarget, closedEndpoint_isNonconstantEntire, ?_⟩
  ext c
  constructor
  · rintro ⟨hcpos, hcarea⟩
    change 1 ≤ c
    by_contra hc
    exact hcarea (closedEndpoint_volume_exceptionalSet_eq_top (lt_of_not_ge hc))
  · intro hc
    change 1 ≤ c at hc
    exact thresholdSet_upward ⟨zero_lt_one, closedEndpoint_hasFiniteArea_one⟩ hc

lemma openEndpoint_volume_exceptionalSet_one :
    volume (exceptionalSet (endpointFunction openEndpointTarget) 1) = ∞ := by
  let s : Set ℂ :=
    (endpointBadSet ∪ Metric.closedBall (0 : ℂ) 1)ᶜ
  have hsvol : volume s = ∞ :=
    volume_compl_eq_top_of_ne_top
      (volume_endpointBadSet_union_closedBall_ne_top 1)
  have hsub : s ⊆ exceptionalSet (endpointFunction openEndpointTarget) 1 := by
    intro z hz
    have hznot : z ∉ endpointBadSet ∪ Metric.closedBall (0 : ℂ) 1 := hz
    have hzbad : z ∉ endpointBadSet := fun h ↦ hznot (Or.inl h)
    have hzball : z ∉ Metric.closedBall (0 : ℂ) 1 := fun h ↦ hznot (Or.inr h)
    have hznorm : 1 < ‖z‖ := by
      simpa [Metric.mem_closedBall, dist_zero_right, not_le] using hzball
    obtain ⟨n, hzS, hzT, hzcorr⟩ := exists_endpointBulkIndex hznorm hzbad
    exact (openEndpointFunction_bounds_on_bulk n hzS hzT hzcorr).1
  apply top_unique
  rw [← hsvol]
  exact measure_mono hsub

lemma openEndpoint_hasFiniteArea {c : ℝ} (hc : 1 < c) :
    HasFiniteArea (endpointFunction openEndpointTarget) c := by
  have hpos : 0 < c - 1 := sub_pos.mpr hc
  have hlim : Tendsto (fun n : ℕ ↦ 2 * endpointMargin n) atTop (𝓝 0) := by
    convert endpointMargin_tendsto_zero.const_mul 2 using 1 <;> simp
  have hev : ∀ᶠ n : ℕ in atTop, 2 * endpointMargin n < c - 1 :=
    hlim.eventually (Iio_mem_nhds hpos)
  obtain ⟨N, hN⟩ := eventually_atTop.1 hev
  apply ne_top_of_le_ne_top
    (volume_endpointBadSet_union_closedBall_ne_top (endpointOuterRadius N))
  apply measure_mono
  intro z hz
  by_contra hzunion
  have hzbad : z ∉ endpointBadSet := fun h ↦ hzunion (Or.inl h)
  have hzball : z ∉ Metric.closedBall (0 : ℂ) (endpointOuterRadius N) :=
    fun h ↦ hzunion (Or.inr h)
  have hzlarge : endpointOuterRadius N < ‖z‖ := by
    simpa [Metric.mem_closedBall, dist_zero_right, not_le] using hzball
  have hznorm : 1 < ‖z‖ := by
    have hR : 1 ≤ endpointOuterRadius N := by
      unfold endpointOuterRadius
      have hN0 : (0 : ℝ) ≤ (N : ℝ) := by positivity
      linarith
    exact hR.trans_lt hzlarge
  obtain ⟨n, hzS, hzT, hzcorr⟩ := exists_endpointBulkIndex hznorm hzbad
  have hNn : N ≤ n := by
    unfold endpointOuterRadius at hzlarge hzT
    exact_mod_cast (show (N : ℝ) ≤ n by linarith)
  have hm := hN n hNn
  have hbulk := (openEndpointFunction_bounds_on_bulk n hzS hzT hzcorr).2
  exact (not_lt_of_ge hz.le) (by linarith :
    ‖endpointFunction openEndpointTarget z‖ < c)

theorem openThresholdWitness_one : OpenThresholdWitness 1 := by
  refine ⟨endpointFunction openEndpointTarget, openEndpoint_isNonconstantEntire, ?_⟩
  ext c
  constructor
  · rintro ⟨hcpos, hcarea⟩
    change 1 < c
    by_contra hc
    have hc1 : c ≤ 1 := le_of_not_gt hc
    have hmono : volume (exceptionalSet (endpointFunction openEndpointTarget) 1) ≤
        volume (exceptionalSet (endpointFunction openEndpointTarget) c) :=
      measure_mono (exceptionalSet_antitone hc1)
    rw [openEndpoint_volume_exceptionalSet_one] at hmono
    exact hcarea (top_unique hmono)
  · intro hc
    change 1 < c at hc
    exact ⟨zero_lt_one.trans hc, openEndpoint_hasFiniteArea hc⟩

/-- Camera's direct theorem normalized to the exceptional level `1`.  The subharmonic
area--growth argument naturally produces this form. -/
def NormalizedCameraTheorem : Prop :=
  ∀ f : ℂ → ℂ,
    IsNonconstantEntire f → HasFiniteArea f 1 → GrowthIntegralConverges f

/-- Exact statement of the direct Camera--Gol'dberg theorem. -/
def DirectGrowthTheorem : Prop :=
  ∀ (f : ℂ → ℂ) (c : ℝ),
    IsNonconstantEntire f → HasFiniteArea f c → GrowthIntegralConverges f

/-- The normalized theorem is equivalent to the unnormalized implication in the direction
needed for the original problem.  Positivity of the given level is derived from finite area. -/
theorem directGrowthTheorem_of_normalizedCameraTheorem
    (hcamera : NormalizedCameraTheorem) : DirectGrowthTheorem := by
  intro f c hf harea
  have hc : 0 < c := positive_level_of_hasFiniteArea hf harea
  have ha : 0 < 1 / c := one_div_pos.mpr hc
  let g : ℂ → ℂ := fun z ↦ ((1 / c : ℝ) : ℂ) * f z
  have hg : IsNonconstantEntire g := by
    refine ⟨hf.1.const_mul (((1 / c : ℝ) : ℂ)), ?_⟩
    obtain ⟨x, y, hxy⟩ := hf.2
    refine ⟨x, y, ?_⟩
    intro h
    apply hxy
    exact mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr ha.ne') h
  have hgarea : HasFiniteArea g 1 := by
    change HasFiniteArea (fun z ↦ ((1 / c : ℝ) : ℂ) * f z) 1
    rw [hasFiniteArea_const_mul ha]
    simpa [hc.ne'] using harea
  have hgrowth : GrowthIntegralConverges g := hcamera g hg hgarea
  exact growthIntegralConverges_of_const_mul hf ha hgrowth

theorem normalizedCameraTheorem_of_directGrowthTheorem
    (hdirect : DirectGrowthTheorem) : NormalizedCameraTheorem := by
  intro f hf harea
  exact hdirect f 1 hf harea

theorem normalizedCameraTheorem_iff_directGrowthTheorem :
    NormalizedCameraTheorem ↔ DirectGrowthTheorem :=
  ⟨directGrowthTheorem_of_normalizedCameraTheorem,
    normalizedCameraTheorem_of_directGrowthTheorem⟩

theorem directGrowthTheorem_of_normalizedAreaGrowthTheorem
    (hcore : NormalizedAreaGrowthTheorem) : DirectGrowthTheorem :=
  directGrowthTheorem_of_normalizedCameraTheorem
    (normalizedCameraTheorem_of_normalizedAreaGrowthTheorem hcore)

theorem directGrowthTheorem_of_normalizedDyadicCameraTheorem
    (hdyadic : NormalizedDyadicCameraTheorem) : DirectGrowthTheorem :=
  directGrowthTheorem_of_normalizedAreaGrowthTheorem
    (normalizedAreaGrowthTheorem_of_normalizedDyadicCameraTheorem hdyadic)

theorem directGrowthTheorem_of_normalizedAnnularCameraTheorem
    (hannular : NormalizedAnnularCameraTheorem) : DirectGrowthTheorem :=
  directGrowthTheorem_of_normalizedDyadicCameraTheorem
    (normalizedDyadicCameraTheorem_of_normalizedAnnularCameraTheorem hannular)

theorem directGrowthTheorem_of_normalizedTsujiCameraTheorem
    (htsuji : NormalizedTsujiCameraTheorem) : DirectGrowthTheorem :=
  directGrowthTheorem_of_normalizedAnnularCameraTheorem
    (normalizedAnnularCameraTheorem_of_normalizedTsujiCameraTheorem htsuji)

/-- The direct Camera--Gol'dberg theorem with no remaining analytic hypothesis. -/
theorem directGrowthTheorem : DirectGrowthTheorem :=
  directGrowthTheorem_of_normalizedAreaGrowthTheorem normalizedAreaGrowthTheorem

/-- Exact inverse statement expressing optimality of the growth integral. -/
def SharpGrowthTheorem : Prop :=
  ∀ φ : ℝ → ℝ,
    Monotone φ → (∀ r, 0 ≤ r → 0 < φ r) →
    IntegrableOn (fun r : ℝ ↦ r / φ r) (Set.Ioi 0) →
    ∃ (f : ℂ → ℂ) (c C R : ℝ),
      IsNonconstantEntire f ∧ 0 < c ∧ HasFiniteArea f c ∧ 0 < C ∧ 0 < R ∧
        ∀ r, R ≤ r →
          Real.log (Real.log (maximumModulus f r)) ≤ C * φ r

/-- Camera--Gol'dberg sharpness: every admissible majorant is attained, up to a constant. -/
theorem sharpGrowthTheorem : SharpGrowthTheorem := by
  intro φ hφmono hφpos hInt
  let A : ℕ → ℕ := Erdos1118Sharp.regularizedComplexity φ
  let g : ℂ → ℂ := Erdos1118Sharp.sharpFunction A
  let f : ℂ → ℂ := fun z ↦ (2 : ℂ) * g z
  have hA : ∀ n, 0 < A n := Erdos1118Sharp.regularizedComplexity_pos φ
  have hfour : ∀ n, 4 * A n ≤ A (n + 1) :=
    Erdos1118Sharp.regularizedComplexity_four_mul_le hφmono hφpos hInt
  have hareaSum : Summable (Erdos1118Sharp.sharpAreaTerm A) :=
    Erdos1118Sharp.summable_regularizedAreaTerm hφmono hφpos hInt
  obtain ⟨K, hK, hAK⟩ :=
    Erdos1118Sharp.exists_regularizedComplexity_le_phi hφmono hφpos hInt
  have hgEntire : IsEntire g :=
    Erdos1118Sharp.sharpFunction_differentiable hA
  have hfEntire : IsEntire f := by
    exact (differentiable_const (c := (2 : ℂ))).mul hgEntire
  have hgNonconstant : ∃ x y, g x ≠ g y :=
    Erdos1118Sharp.sharpFunction_nonconstant hA
  have hfNonconstant : ∃ x y, f x ≠ f y := by
    obtain ⟨x, y, hxy⟩ := hgNonconstant
    refine ⟨x, y, fun h ↦ hxy ?_⟩
    exact mul_left_cancel₀ (by norm_num : (2 : ℂ) ≠ 0) h
  have hfiniteG : volume {z : ℂ | 1 < ‖g z‖} ≠ ∞ :=
    Erdos1118Sharp.sharpFunction_hasFiniteArea hA hareaSum
  have hfiniteF : HasFiniteArea f 2 := by
    have hnorm2 : ‖(2 : ℂ)‖ = 2 := by norm_num
    have hset : exceptionalSet f 2 = {z : ℂ | 1 < ‖g z‖} := by
      ext z
      simp only [exceptionalSet, Set.mem_setOf_eq, f, norm_mul, hnorm2]
      constructor <;> intro h <;> nlinarith [norm_nonneg (g z)]
    unfold HasFiniteArea
    rw [hset]
    exact hfiniteG
  let C : ℝ := 4000 * K
  refine ⟨f, 2, C, 4, ⟨hfEntire, hfNonconstant⟩, by norm_num, hfiniteF,
    by unfold C; positivity, by norm_num, ?_⟩
  intro r hr
  have hr1 : 1 < r := by linarith
  obtain ⟨n, hnR, hnT⟩ := Erdos1118Sharp.exists_sharpAnnulusIndex hr1
  have hr0 : 0 ≤ r := by linarith
  have hgclose := Erdos1118Sharp.sharpFunction_sub_id_norm_le hA (z := (1 : ℂ))
    (by norm_num : ‖(1 : ℂ)‖ ≤ 1)
  have hg1 : (7 / 8 : ℝ) ≤ ‖g 1‖ := by
    have htri : (1 : ℝ) ≤ ‖g 1 - 1‖ + ‖g 1‖ := by
      calc
        (1 : ℝ) = ‖(1 : ℂ)‖ := by norm_num
        _ = ‖(1 - g 1) + g 1‖ := by ring_nf
        _ ≤ ‖1 - g 1‖ + ‖g 1‖ := norm_add_le _ _
        _ = ‖g 1 - 1‖ + ‖g 1‖ := by rw [norm_sub_rev]
    nlinarith
  have hf1 : 1 < ‖f 1‖ := by
    have hnorm2 : ‖(2 : ℂ)‖ = 2 := by norm_num
    simp only [f, norm_mul, hnorm2]
    nlinarith
  have hMlower : 1 < maximumModulus f r :=
    hf1.trans_le (norm_le_maximumModulus_of_norm_le hfEntire hr0 (by norm_num; linarith))
  obtain ⟨z, hz, hM, -⟩ := exists_maximumModulus_eq hfEntire.continuous hr0
  have hz1 : 1 ≤ ‖z‖ := by rw [hz]; linarith
  have hgrowth := Erdos1118Sharp.sharpFunction_norm_le_on_annulus hA hfour n hz1
    (by rw [hz]; exact hnT)
  have hMupper : maximumModulus f r ≤
      (2 : ℝ) ^ (9 * A n * 2 ^ (3210 * A n) + 1) := by
    rw [hM]
    calc
      ‖f z‖ = 2 * ‖g z‖ := by simp [f, norm_mul]
      _ ≤ 2 * ((2 ^ (9 * A n * 2 ^ (3210 * A n)) : ℕ) : ℝ) := by gcongr
      _ = (2 : ℝ) ^ (9 * A n * 2 ^ (3210 * A n) + 1) := by
        rw [pow_succ]
        norm_cast
        ring
  have hlog := Erdos1118Sharp.log_log_le_of_stage_bound (hA n) hMlower hMupper
  have hAφ : (A n : ℝ) ≤ K * φ r := by
    calc
      (A n : ℝ) ≤ K * φ (Erdos1118Sharp.sharpRadius n) := hAK n
      _ ≤ K * φ r := mul_le_mul_of_nonneg_left (hφmono hnR.le) hK.le
  calc
    Real.log (Real.log (maximumModulus f r)) ≤ 4000 * (A n : ℝ) := hlog
    _ ≤ 4000 * (K * φ r) := mul_le_mul_of_nonneg_left hAφ (by norm_num)
    _ = C * φ r := by unfold C; ring

/-- Exact statement of Gol'dberg's prescribed-threshold theorem. -/
def PrescribedThresholdTheorem : Prop :=
  ∀ m : ℝ, 0 < m → ClosedThresholdWitness m ∧ OpenThresholdWitness m

/-- Gol'dberg's prescribed-threshold theorem, including both possible endpoint conventions. -/
theorem prescribedThresholdTheorem : PrescribedThresholdTheorem := by
  intro m hm
  exact ⟨closedThresholdWitness_scale hm closedThresholdWitness_one,
    openThresholdWitness_scale hm openThresholdWitness_one⟩

/-- The complete published resolution, split into its three exact assertions. -/
def Resolution : Prop :=
  DirectGrowthTheorem ∧ SharpGrowthTheorem ∧ PrescribedThresholdTheorem

/-- Complete formal resolution of Erdős Problem 1118. -/
theorem erdos_1118 : Resolution :=
  ⟨directGrowthTheorem, sharpGrowthTheorem, prescribedThresholdTheorem⟩

/-- The second answer follows formally from Gol'dberg's exact theorem. -/
theorem negativeAnswer_of_prescribedThresholdTheorem
    (h : PrescribedThresholdTheorem) : NegativeAnswer := by
  exact closedThresholdWitness_gives_negativeAnswer zero_lt_one (h 1 zero_lt_one).1

end Erdos1118

#print axioms Erdos1118.closedThresholdWitness_gives_negativeAnswer
#print axioms Erdos1118.negativeAnswer_of_prescribedThresholdTheorem
#print axioms Erdos1118.erdos_1118
