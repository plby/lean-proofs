/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import Mathlib.Analysis.Complex.JensenFormula
import Mathlib.Analysis.SpecialFunctions.Integrals.PosLogEqCircleAverage

/-!
# Finite continuous subharmonic functions on planar open sets

This file develops the small, real-valued subharmonic API needed for Erdős Problem 515.  We use
the exact circle-submean definition.  In particular, our functions are finite and continuous; no
extended-real convention at logarithmic singularities is hidden in the definition.
-/

open Metric Real Set

namespace Erdos515

/-- A finite continuous real-valued function is subharmonic on `U` when `U` is open and it
satisfies the circle-submean inequality on every closed disk contained in `U`. -/
def SubharmonicOn (u : ℂ → ℝ) (U : Set ℂ) : Prop :=
  IsOpen U ∧ ContinuousOn u U ∧
    ∀ ⦃c : ℂ⦄, c ∈ U → ∀ ⦃R : ℝ⦄, 0 < R → closedBall c R ⊆ U →
      u c ≤ circleAverage u c R

/-- A finite continuous subharmonic function on the whole complex plane. -/
def Subharmonic (u : ℂ → ℝ) : Prop :=
  SubharmonicOn u Set.univ

namespace SubharmonicOn

variable {u v : ℂ → ℝ} {U V : Set ℂ}

lemma isOpen (hu : SubharmonicOn u U) : IsOpen U := hu.1

lemma continuousOn (hu : SubharmonicOn u U) : ContinuousOn u U := hu.2.1

lemma submean (hu : SubharmonicOn u U) {c : ℂ} (hc : c ∈ U) {R : ℝ} (hR : 0 < R)
    (hball : closedBall c R ⊆ U) :
    u c ≤ circleAverage u c R :=
  hu.2.2 hc hR hball

/-- Restriction to an open subset preserves subharmonicity. -/
lemma mono (hu : SubharmonicOn u U) (hV : IsOpen V) (hVU : V ⊆ U) :
    SubharmonicOn u V := by
  refine ⟨hV, hu.continuousOn.mono hVU, ?_⟩
  intro c hc R hR hball
  exact hu.submean (hVU hc) hR (hball.trans hVU)

/-- Constant functions are subharmonic on every open set. -/
lemma const (hU : IsOpen U) (b : ℝ) : SubharmonicOn (fun _ : ℂ ↦ b) U := by
  refine ⟨hU, continuousOn_const, ?_⟩
  intro c hc R hR hball
  rw [circleAverage_const]

/-- Subharmonicity is preserved by adding two finite continuous subharmonic functions. -/
lemma add (hu : SubharmonicOn u U) (hv : SubharmonicOn v U) :
    SubharmonicOn (fun z ↦ u z + v z) U := by
  refine ⟨hu.isOpen, hu.continuousOn.add hv.continuousOn, ?_⟩
  intro c hc R hR hball
  have hui : CircleIntegrable u c R :=
    (hu.continuousOn.mono (sphere_subset_closedBall.trans hball)).circleIntegrable hR.le
  have hvi : CircleIntegrable v c R :=
    (hv.continuousOn.mono (sphere_subset_closedBall.trans hball)).circleIntegrable hR.le
  rw [circleAverage_fun_add hui hvi]
  exact add_le_add (hu.submean hc hR hball) (hv.submean hc hR hball)

/-- Multiplication by a nonnegative real scalar preserves subharmonicity. -/
lemma nonneg_mul (hu : SubharmonicOn u U) {a : ℝ} (ha : 0 ≤ a) :
    SubharmonicOn (fun z ↦ a * u z) U := by
  refine ⟨hu.isOpen, continuousOn_const.mul hu.continuousOn, ?_⟩
  intro c hc R hR hball
  change a • u c ≤ circleAverage (fun z ↦ a • u z) c R
  rw [circleAverage_fun_smul]
  exact smul_le_smul_of_nonneg_left (hu.submean hc hR hball) ha

/-- Positive affine changes of scale preserve subharmonicity. -/
lemma affine (hu : SubharmonicOn u U) {a b : ℝ} (ha : 0 ≤ a) :
    SubharmonicOn (fun z ↦ a * u z + b) U := by
  exact (hu.nonneg_mul ha).add (const hu.isOpen b)

/-- The pointwise maximum of two finite continuous subharmonic functions is subharmonic. -/
lemma max (hu : SubharmonicOn u U) (hv : SubharmonicOn v U) :
    SubharmonicOn (fun z ↦ u z ⊔ v z) U := by
  refine ⟨hu.isOpen, hu.continuousOn.sup hv.continuousOn, ?_⟩
  intro c hc R hR hball
  have hui : CircleIntegrable u c R :=
    (hu.continuousOn.mono (sphere_subset_closedBall.trans hball)).circleIntegrable hR.le
  have hvi : CircleIntegrable v c R :=
    (hv.continuousOn.mono (sphere_subset_closedBall.trans hball)).circleIntegrable hR.le
  have hmaxi : CircleIntegrable (fun z ↦ u z ⊔ v z) c R :=
    ((hu.continuousOn.sup hv.continuousOn).mono
      (sphere_subset_closedBall.trans hball)).circleIntegrable hR.le
  apply max_le
  · exact (hu.submean hc hR hball).trans
      (circleAverage_mono hui hmaxi fun z hz ↦ le_max_left _ _)
  · exact (hv.submean hc hR hball).trans
      (circleAverage_mono hvi hmaxi fun z hz ↦ le_max_right _ _)

/-- Centered-disk maximum principle: a boundary upper bound is also an upper bound at the center. -/
lemma le_of_forall_sphere_le (hu : SubharmonicOn u U) {c : ℂ} (hc : c ∈ U)
    {R M : ℝ} (hR : 0 < R) (hball : closedBall c R ⊆ U)
    (hM : ∀ z ∈ sphere c R, u z ≤ M) :
    u c ≤ M := by
  refine (hu.submean hc hR hball).trans ?_
  apply circleAverage_mono_on_of_le_circle
  · exact (hu.continuousOn.mono (sphere_subset_closedBall.trans hball)).circleIntegrable hR.le
  simpa [abs_of_pos hR] using hM

/-- A maximum-principle formulation especially convenient for recursive disk constructions:
on every admissible positive-radius disk, some boundary point has value at least the value at the
center. -/
lemma exists_mem_sphere_ge (hu : SubharmonicOn u U) {c : ℂ} (hc : c ∈ U)
    {R : ℝ} (hR : 0 < R) (hball : closedBall c R ⊆ U) :
    ∃ z ∈ sphere c R, u c ≤ u z := by
  have hcont : ContinuousOn u (sphere c R) :=
    hu.continuousOn.mono (sphere_subset_closedBall.trans hball)
  obtain ⟨z, hz, hzmax⟩ := (isCompact_sphere c R).exists_isMaxOn
    (NormedSpace.sphere_nonempty.mpr hR.le) hcont
  exact ⟨z, hz, hu.le_of_forall_sphere_le hc hR hball (fun w hw ↦ hzmax hw)⟩

end SubharmonicOn

namespace Subharmonic

variable {u v : ℂ → ℝ}

lemma continuous (hu : Subharmonic u) : Continuous u := by
  exact continuousOn_univ.mp hu.2.1

lemma submean (hu : Subharmonic u) (c : ℂ) {R : ℝ} (hR : 0 < R) :
    u c ≤ circleAverage u c R :=
  hu.2.2 (by simp) hR (by simp)

lemma add (hu : Subharmonic u) (hv : Subharmonic v) :
    Subharmonic (fun z ↦ u z + v z) :=
  SubharmonicOn.add hu hv

lemma affine (hu : Subharmonic u) {a b : ℝ} (ha : 0 ≤ a) :
    Subharmonic (fun z ↦ a * u z + b) :=
  SubharmonicOn.affine hu ha

lemma max (hu : Subharmonic u) (hv : Subharmonic v) :
    Subharmonic (fun z ↦ u z ⊔ v z) :=
  SubharmonicOn.max hu hv

end Subharmonic

/-- The finite logarithmic majorant used for an entire function.  Mathlib's `log⁺` has the
continuous convention `log⁺ 0 = 0` and equals `log (max 1 x)` for nonnegative `x`. -/
noncomputable def logPosNorm (f : ℂ → ℂ) (z : ℂ) : ℝ :=
  log⁺ ‖f z‖

lemma logPosNorm_eq_log_max (f : ℂ → ℂ) (z : ℂ) :
    logPosNorm f z = log (max 1 ‖f z‖) := by
  exact posLog_eq_log_max_one (norm_nonneg _)

lemma logPosNorm_nonneg (f : ℂ → ℂ) (z : ℂ) : 0 ≤ logPosNorm f z :=
  posLog_nonneg

lemma continuous_logPosNorm {f : ℂ → ℂ} (hf : Continuous f) :
    Continuous (logPosNorm f) := by
  exact continuous_posLog.comp hf.norm

/-!
## The logarithmic regularization and the analytic example

The circular regularization below is the safe way to regularize `log ‖f‖`: averaging the
logarithmic singularity over *all phases* of a circle.  Replacing `f` by `f + ε` would be wrong,
since that merely moves the zeros.  The exact formula shows that radius one produces precisely
`log⁺ ‖f‖`, including at zeros.
-/

/-- Circular logarithmic regularization at scale `ε`. -/
noncomputable def circleLogRegularization (ε : ℝ) (f : ℂ → ℂ) (z : ℂ) : ℝ :=
  circleAverage (fun a : ℂ ↦ log ‖a - f z‖) 0 ε

/-- Exact evaluation of the circular logarithmic regularization. -/
lemma circleLogRegularization_eq (f : ℂ → ℂ) (z : ℂ) {ε : ℝ} (hε : 0 < ε) :
    circleLogRegularization ε f z = log ε + log⁺ (ε⁻¹ * ‖f z‖) := by
  simpa [circleLogRegularization] using
    (circleAverage_log_norm_sub_const_eq_log_radius_add_posLog
      (a := f z) (c := 0) (R := ε) hε.ne')

/-- At scale one, circular regularization is exactly the finite logarithmic majorant. -/
lemma circleLogRegularization_one (f : ℂ → ℂ) (z : ℂ) :
    circleLogRegularization 1 f z = logPosNorm f z := by
  simp [circleLogRegularization_eq, logPosNorm]

/-- Jensen's formula gives the submean inequality for `log ‖f‖` at a nonzero center.

The nonnegativity proof for the Jensen correction is written out because `Real.log 0 = 0` in Lean.
The assumption `f c ≠ 0` removes the exceptional center term; every other zero contributes its
nonnegative multiplicity times `log (R / ‖c-z‖)`. -/
lemma log_norm_le_circleAverage_of_analyticOnNhd {f : ℂ → ℂ} {c : ℂ} {R : ℝ}
    (hR : 0 < R) (hf : AnalyticOnNhd ℂ f (closedBall c R)) (hc : f c ≠ 0) :
    log ‖f c‖ ≤ circleAverage (fun z ↦ log ‖f z‖) c R := by
  have hfR : AnalyticOnNhd ℂ f (closedBall c |R|) := by
    simpa [abs_of_pos hR] using hf
  rw [hfR.circleAverage_log_norm hR.ne' hc]
  suffices 0 ≤ ∑ᶠ z, (MeromorphicOn.divisor f (closedBall c |R|) z : ℝ) *
      log (R * ‖c - z‖⁻¹) by
    linarith
  apply finsum_nonneg
  intro z
  by_cases hz : z ∈ closedBall c |R|
  · by_cases hzc : z = c
    · subst z
      have hdivc : MeromorphicOn.divisor f (closedBall c |R|) c = 0 := by
        rw [MeromorphicOn.AnalyticOnNhd.divisor_apply hfR (by simp)]
        simp [(hfR c (by simp)).analyticOrderAt_eq_zero.mpr hc]
      simp [hdivc]
    · apply mul_nonneg
      · exact_mod_cast MeromorphicOn.AnalyticOnNhd.divisor_nonneg hfR z
      · apply log_nonneg
        rw [mul_comm]
        apply (one_le_inv_mul₀ (norm_pos_iff.mpr ?_)).2
        · rw [abs_of_pos hR] at hz
          simpa [mem_closedBall, dist_eq_norm'] using hz
        · simpa [sub_eq_zero] using Ne.symm hzc
  · simp [Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hz]

/-- If `f` is analytic on an open set, then `log⁺ ‖f‖` is a finite continuous subharmonic
function there.  At a zero of `f`, the center value is zero and nonnegativity of the boundary
average settles the submean inequality.  At a nonzero center, Jensen's formula and monotonicity of
circle averages apply. -/
theorem subharmonicOn_logPosNorm {f : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hf : AnalyticOnNhd ℂ f U) :
    SubharmonicOn (logPosNorm f) U := by
  have hcont : ContinuousOn (logPosNorm f) U := by
    intro z hz
    exact continuous_posLog.continuousAt.comp_continuousWithinAt
      ((hf z hz).continuousAt.norm.continuousWithinAt)
  refine ⟨hU, hcont, ?_⟩
  intro c hc R hR hball
  have hfball : AnalyticOnNhd ℂ f (closedBall c R) := hf.mono hball
  have hposInt : CircleIntegrable (logPosNorm f) c R :=
    (hcont.mono (sphere_subset_closedBall.trans hball)).circleIntegrable hR.le
  have hnonneg : 0 ≤ circleAverage (logPosNorm f) c R :=
    circleAverage_nonneg_of_nonneg fun z hz ↦ logPosNorm_nonneg f z
  by_cases hfc : f c = 0
  · simpa [logPosNorm, hfc] using hnonneg
  · rw [logPosNorm, posLog_apply]
    apply max_le hnonneg
    refine (log_norm_le_circleAverage_of_analyticOnNhd hR hfball hfc).trans ?_
    apply circleAverage_mono
    · have hfSphere : AnalyticOnNhd ℂ f (sphere c |R|) := by
        simpa [abs_of_pos hR] using hfball.mono sphere_subset_closedBall
      exact hfSphere.meromorphicOn.circleIntegrable_log_norm
    · exact hposInt
    · intro z hz
      exact le_max_right 0 (log ‖f z‖)

/-- In particular, the finite logarithmic majorant of an entire function is subharmonic on the
whole plane. -/
theorem subharmonic_logPosNorm {f : ℂ → ℂ} (hf : Differentiable ℂ f) :
    Subharmonic (logPosNorm f) := by
  exact subharmonicOn_logPosNorm isOpen_univ
    (Complex.analyticOnNhd_univ_iff_differentiable.2 hf)

end Erdos515
