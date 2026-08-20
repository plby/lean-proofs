/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos515.Hall
import ErdosProblems.Erdos515.HallConcrete
import ErdosProblems.Erdos515.ShortPathPrinciple

/-!
# The Hall--Prawitz stage adapter

This file removes the elementary normalization and radial bookkeeping from the remaining
analytic input to the LRW construction.  A stage is reduced to the quantitative Hall estimate
for one explicitly defined bounded subharmonic disk function and the two Prawitz/area estimates
for the chosen Riemann map.
-/

open MeasureTheory Metric Set
open scoped ENNReal NNReal Topology

namespace Erdos515

/-- The normalized LRW control pulled back to the unit disk by a Riemann map. -/
noncomputable def lrwDiskControl (delta : ℝ) (u : ℂ → ℝ)
    (a : PositiveControlPoint u) (F : ℂ → ℂ) (z : ℂ) : ℝ :=
  lrwNormalizedControl delta u a (F z)

/-- A fixed recursion parameter small enough for the quantitative Hall theorem. -/
noncomputable def lrwRecursionDelta : ℝ := 1 / 4096

/-- Hall's center defect for the LRW normalization at `lrwRecursionDelta`. -/
noncomputable def lrwHallDefect : ℝ :=
  1 - (1 - lrwRecursionDelta) ^ 2

lemma lrwRecursionDelta_pos : 0 < lrwRecursionDelta := by
  norm_num [lrwRecursionDelta]

lemma lrwRecursionDelta_lt_one : lrwRecursionDelta < 1 := by
  norm_num [lrwRecursionDelta]

lemma lrwHallDefect_nonneg : 0 ≤ lrwHallDefect := by
  norm_num [lrwHallDefect, lrwRecursionDelta]

lemma lrwHallDefect_le : lrwHallDefect ≤ 1 / 512 := by
  norm_num [lrwHallDefect, lrwRecursionDelta]

lemma lrwNormalizedControl_nonneg {delta : ℝ} {u : ℂ → ℝ}
    (a : PositiveControlPoint u) (z : ℂ) :
    0 ≤ lrwNormalizedControl delta u a z := by
  unfold lrwNormalizedControl
  exact mul_nonneg (inv_nonneg.mpr a.positive.le) (le_max_right _ _)

lemma lrwNormalizedControl_self {delta : ℝ} {u : ℂ → ℝ}
    (hdelta0 : 0 < delta) (hdelta1 : delta < 1) (a : PositiveControlPoint u) :
    lrwNormalizedControl delta u a a.point = (1 - delta) ^ 2 := by
  have hsub : 0 < 1 - delta := sub_pos.mpr hdelta1
  have hinside : 0 ≤ (1 - delta) * (u a.point - delta * u a.point) := by
    have : 0 ≤ u a.point - delta * u a.point := by
      nlinarith [mul_pos hsub a.positive]
    positivity
  unfold lrwNormalizedControl
  rw [max_eq_left hinside]
  field_simp [ne_of_gt a.positive]

/-- On its defining strict sublevel component, the normalized LRW control is at most one. -/
lemma lrwNormalizedControl_le_one_of_mem_domain
    {delta : ℝ} {u : ℂ → ℝ} {base : ℂ}
    (hdelta0 : 0 < delta) (hdelta1 : delta < 1)
    (a : PositiveControlPoint u) {z : ℂ}
    (hz : z ∈ lrwDomain delta u base a) :
    lrwNormalizedControl delta u a z ≤ 1 := by
  have hsub : 0 < 1 - delta := sub_pos.mpr hdelta1
  have hzlt := sublevelComponent_subset u (lrwLevel delta u a) base hz
  change u z < u a.point / (1 - delta) at hzlt
  have hzmul : u z * (1 - delta) < u a.point := (lt_div_iff₀ hsub).mp hzlt
  have hsubtract : 0 ≤ delta * ((1 - delta) * u a.point) :=
    mul_nonneg hdelta0.le (mul_nonneg hsub.le a.positive.le)
  have hraw : (1 - delta) * (u z - delta * u a.point) ≤ u a.point := by
    calc
      (1 - delta) * (u z - delta * u a.point) =
          u z * (1 - delta) - delta * ((1 - delta) * u a.point) := by ring
      _ ≤ u z * (1 - delta) := sub_le_self _ hsubtract
      _ ≤ u a.point := hzmul.le
  have hmax : max ((1 - delta) * (u z - delta * u a.point)) 0 ≤ u a.point :=
    max_le hraw a.positive.le
  unfold lrwNormalizedControl
  calc
    (u a.point)⁻¹ * max ((1 - delta) * (u z - delta * u a.point)) 0 ≤
        (u a.point)⁻¹ * u a.point :=
      mul_le_mul_of_nonneg_left hmax (inv_nonneg.mpr a.positive.le)
    _ = 1 := inv_mul_cancel₀ (ne_of_gt a.positive)

lemma lrwDiskControl_nonneg {delta : ℝ} {u : ℂ → ℝ}
    (a : PositiveControlPoint u) (F : ℂ → ℂ) (z : ℂ) :
    0 ≤ lrwDiskControl delta u a F z :=
  lrwNormalizedControl_nonneg a (F z)

lemma lrwDiskControl_le_one {delta : ℝ} {u : ℂ → ℝ} {base : ℂ}
    (hdelta0 : 0 < delta) (hdelta1 : delta < 1)
    (a : PositiveControlPoint u) {F : ℂ → ℂ}
    (hFmaps : MapsTo F (ball 0 1) (lrwDomain delta u base a))
    {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) :
    lrwDiskControl delta u a F z ≤ 1 :=
  lrwNormalizedControl_le_one_of_mem_domain hdelta0 hdelta1 a (hFmaps hz)

lemma lrwDiskControl_zero {delta : ℝ} {u : ℂ → ℝ}
    (hdelta0 : 0 < delta) (hdelta1 : delta < 1)
    (a : PositiveControlPoint u) {F : ℂ → ℂ} (hFzero : F 0 = a.point) :
    lrwDiskControl delta u a F 0 = (1 - delta) ^ 2 := by
  rw [lrwDiskControl, hFzero]
  exact lrwNormalizedControl_self hdelta0 hdelta1 a

/-- For `u = log⁺ |f|`, the pulled-back normalized control is subharmonic.  This uses the
identity `logPosNorm f (F z) = logPosNorm (f ∘ F) z`, avoiding any separate general theorem
about composition of subharmonic functions with holomorphic maps. -/
theorem subharmonicOn_lrwDiskControl_logPosNorm {f F : ℂ → ℂ} {base : ℂ}
    {delta : ℝ} (hf : Differentiable ℂ f)
    (hdelta0 : 0 < delta) (hdelta1 : delta < 1)
    (a : PositiveControlPoint (logPosNorm f))
    (hFdiff : DifferentiableOn ℂ F (ball 0 1)) :
    SubharmonicOn (lrwDiskControl delta (logPosNorm f) a F) unitDisk := by
  have hFanalytic : AnalyticOnNhd ℂ F (ball 0 1) :=
    hFdiff.analyticOnNhd isOpen_ball
  have hfanalytic : AnalyticOnNhd ℂ f (Set.univ : Set ℂ) :=
    Complex.analyticOnNhd_univ_iff_differentiable.mpr hf
  have hcomp : AnalyticOnNhd ℂ (f ∘ F) (ball 0 1) :=
    hfanalytic.comp hFanalytic (mapsTo_univ F (ball 0 1))
  have hlog : SubharmonicOn (logPosNorm (f ∘ F)) (ball 0 1) :=
    subharmonicOn_logPosNorm isOpen_ball hcomp
  have haffine : SubharmonicOn
      (fun z ↦ (1 - delta) * logPosNorm (f ∘ F) z -
        (1 - delta) * (delta * logPosNorm f a.point)) (ball 0 1) := by
    simpa only [sub_eq_add_neg] using hlog.affine (a := 1 - delta)
      (b := -((1 - delta) * (delta * logPosNorm f a.point))) (sub_pos.mpr hdelta1).le
  have hmax : SubharmonicOn
      (fun z ↦ max ((1 - delta) * logPosNorm (f ∘ F) z -
        (1 - delta) * (delta * logPosNorm f a.point)) 0) (ball 0 1) :=
    haffine.max (SubharmonicOn.const isOpen_ball 0)
  have hscaled := hmax.nonneg_mul (inv_nonneg.mpr a.positive.le)
  change SubharmonicOn (lrwDiskControl delta (logPosNorm f) a F) (ball 0 1)
  convert hscaled using 1
  ext z
  unfold lrwDiskControl lrwNormalizedControl
  simp only [logPosNorm, Function.comp_apply]
  congr 2
  ring

/-- Specialize the quantitative Hall radial theorem to the exact LRW normalization. -/
theorem hall_measure_lrwDiskControl
    {f F : ℂ → ℂ} {base : ℂ}
    (hf : Differentiable ℂ f)
    (a : LRWAdmissiblePoint lrwRecursionDelta (logPosNorm f) base)
    (hFdiff : DifferentiableOn ℂ F (ball 0 1))
    (hFbij : BijOn F (ball 0 1)
      (lrwDomain lrwRecursionDelta (logPosNorm f) base a.controlPoint))
    (hFzero : F 0 = a.controlPoint.point)
    (hHall : ∀ (w : ℂ → ℝ) (delta : ℝ),
      SubharmonicOn w unitDisk →
      (∀ z ∈ unitDisk, 0 ≤ w z) →
      (∀ z ∈ unitDisk, w z ≤ 1) →
      w 0 = 1 - delta → 0 ≤ delta → delta ≤ 1 / 512 →
      ENNReal.ofReal Real.pi ≤ volume (goodDirections w)) :
    ENNReal.ofReal Real.pi ≤ volume
      (goodDirections (lrwDiskControl lrwRecursionDelta (logPosNorm f)
        a.controlPoint F)) := by
  apply hHall _ lrwHallDefect
  · exact subharmonicOn_lrwDiskControl_logPosNorm (base := base) hf lrwRecursionDelta_pos
      lrwRecursionDelta_lt_one a.controlPoint hFdiff
  · intro z _hz
    exact lrwDiskControl_nonneg a.controlPoint F z
  · intro z hz
    exact lrwDiskControl_le_one lrwRecursionDelta_pos lrwRecursionDelta_lt_one
      a.controlPoint hFbij.mapsTo hz
  · rw [lrwDiskControl_zero lrwRecursionDelta_pos lrwRecursionDelta_lt_one
      a.controlPoint hFzero]
    unfold lrwHallDefect
    ring
  · exact lrwHallDefect_nonneg
  · exact lrwHallDefect_le

/-- The Prawitz/log-area output at one stage, after the radial statistics have been chosen.
Unlike `LRWStageEstimates`, this contains no Hall set and no positivity-along-rays field. -/
structure LRWPrawitzStageData (u : ℂ → ℝ) (base : ℂ) (delta constant : ℝ)
    (a : LRWAdmissiblePoint delta u base) (F : ℂ → ℂ) where
  radialBad : Set ℝ
  logBad : Set ℝ
  K : ℝ
  J : ℝ
  K_nonneg : 0 ≤ K
  J_nonneg : 0 ≤ J
  prawitz : volume radialBad < ENNReal.ofReal (Real.pi / 4)
  logArea : volume logBad < ENNReal.ofReal (Real.pi / 4)
  variation : ∀ theta ∈ angleDomain,
    theta ∉ radialBad → theta ∉ logBad →
    eVariationOn (shortPathRadialCurve F theta) (Ico (0 : ℝ) 1) ≤
      ENNReal.ofReal (K * ‖deriv F 0‖ * J)
  constant_bound : 4 * K * J ≤ constant

namespace LRWPrawitzStageData

/-- Combine a Hall measure estimate with the Prawitz stage data. -/
noncomputable def toStageEstimates {f F : ℂ → ℂ} {base : ℂ} {delta constant : ℝ}
    (hdelta0 : 0 < delta) (hdelta1 : delta < 1)
    (a : LRWAdmissiblePoint delta (logPosNorm f) base)
    (hFmaps : MapsTo F (ball 0 1)
      (lrwDomain delta (logPosNorm f) base a.controlPoint))
    (P : LRWPrawitzStageData (logPosNorm f) base delta constant a F)
    (hHall : ENNReal.ofReal Real.pi ≤ volume
      (goodDirections (lrwDiskControl delta (logPosNorm f) a.controlPoint F))) :
    LRWStageEstimates (logPosNorm f) base delta constant a F where
  good := goodDirections (lrwDiskControl delta (logPosNorm f) a.controlPoint F)
  radialBad := P.radialBad
  logBad := P.logBad
  K := P.K
  J := P.J
  K_nonneg := P.K_nonneg
  J_nonneg := P.J_nonneg
  hall := hHall
  prawitz := P.prawitz
  logArea := P.logArea
  good_radius := by
    intro theta htheta r hr
    have hpoint : radialPoint r theta = shortPathRadialPoint r theta := by
      unfold radialPoint shortPathRadialPoint
      congr 2
      ring
    refine ⟨hFmaps (shortPathRadialPoint_mem_unitDisk hr), ?_⟩
    change 0 < lrwDiskControl delta (logPosNorm f) a.controlPoint F
      (shortPathRadialPoint r theta)
    rw [← hpoint]
    exact htheta.2 r hr
  variation := fun theta htheta hthetaMax hthetaLog ↦
    P.variation theta htheta.1 hthetaMax hthetaLog
  constant_bound := P.constant_bound

end LRWPrawitzStageData

/-- Exact Hall and Prawitz inputs, with all normalization and good-ray bookkeeping removed. -/
structure LRWStageTheorems (f : ℂ → ℂ) (base : ℂ) where
  delta : ℝ
  constant : ℝ
  delta_pos : 0 < delta
  delta_lt_one : delta < 1
  constant_nonneg : 0 ≤ constant
  hall : ∀ (a : LRWAdmissiblePoint delta (logPosNorm f) base) (F : ℂ → ℂ),
    DifferentiableOn ℂ F (ball 0 1) →
    BijOn F (ball 0 1) (lrwDomain delta (logPosNorm f) base a.controlPoint) →
    F 0 = a.controlPoint.point →
    ENNReal.ofReal Real.pi ≤ volume
      (goodDirections (lrwDiskControl delta (logPosNorm f) a.controlPoint F))
  prawitz : ∀ (a : LRWAdmissiblePoint delta (logPosNorm f) base) (F : ℂ → ℂ),
    DifferentiableOn ℂ F (ball 0 1) →
    BijOn F (ball 0 1) (lrwDomain delta (logPosNorm f) base a.controlPoint) →
    F 0 = a.controlPoint.point → deriv F 0 ≠ 0 →
    Nonempty (LRWPrawitzStageData (logPosNorm f) base delta constant a F)

namespace LRWStageTheorems

/-- Build the exact stage provider at the fixed LRW parameter from the unconditional Hall
theorem and the remaining Prawitz/log-area provider. -/
noncomputable def ofHallAndPrawitz {f : ℂ → ℂ} {base : ℂ}
    (hf : Differentiable ℂ f)
    (constant : ℝ) (hconstant : 0 ≤ constant)
    (hHall : ∀ (w : ℂ → ℝ) (delta : ℝ),
      SubharmonicOn w unitDisk →
      (∀ z ∈ unitDisk, 0 ≤ w z) →
      (∀ z ∈ unitDisk, w z ≤ 1) →
      w 0 = 1 - delta → 0 ≤ delta → delta ≤ 1 / 512 →
      ENNReal.ofReal Real.pi ≤ volume (goodDirections w))
    (hPrawitz : ∀
      (a : LRWAdmissiblePoint lrwRecursionDelta (logPosNorm f) base) (F : ℂ → ℂ),
      DifferentiableOn ℂ F (ball 0 1) →
      BijOn F (ball 0 1)
        (lrwDomain lrwRecursionDelta (logPosNorm f) base a.controlPoint) →
      F 0 = a.controlPoint.point → deriv F 0 ≠ 0 →
      Nonempty (LRWPrawitzStageData (logPosNorm f) base lrwRecursionDelta constant a F)) :
    LRWStageTheorems f base where
  delta := lrwRecursionDelta
  constant := constant
  delta_pos := lrwRecursionDelta_pos
  delta_lt_one := lrwRecursionDelta_lt_one
  constant_nonneg := hconstant
  hall := fun a F hFdiff hFbij hFzero ↦
    hall_measure_lrwDiskControl hf a hFdiff hFbij hFzero hHall
  prawitz := hPrawitz

/-- The unconditional Hall theorem discharges the Hall field, leaving only the Prawitz/log-area
stage theorem as an analytic parameter. -/
noncomputable def ofPrawitz {f : ℂ → ℂ} {base : ℂ}
    (hf : Differentiable ℂ f)
    (constant : ℝ) (hconstant : 0 ≤ constant)
    (hPrawitz : ∀
      (a : LRWAdmissiblePoint lrwRecursionDelta (logPosNorm f) base) (F : ℂ → ℂ),
      DifferentiableOn ℂ F (ball 0 1) →
      BijOn F (ball 0 1)
        (lrwDomain lrwRecursionDelta (logPosNorm f) base a.controlPoint) →
      F 0 = a.controlPoint.point → deriv F 0 ≠ 0 →
      Nonempty (LRWPrawitzStageData (logPosNorm f) base lrwRecursionDelta constant a F)) :
    LRWStageTheorems f base :=
  ofHallAndPrawitz hf constant hconstant hall_radial_unconditional hPrawitz

/-- Convert the separated Hall and Prawitz theorems to the stage-estimate provider consumed by
the Riemann-map adapter. -/
def estimates {f : ℂ → ℂ} {base : ℂ} (A : LRWStageTheorems f base) :
    ∀ (a : LRWAdmissiblePoint A.delta (logPosNorm f) base) (F : ℂ → ℂ),
      DifferentiableOn ℂ F (ball 0 1) →
      BijOn F (ball 0 1) (lrwDomain A.delta (logPosNorm f) base a.controlPoint) →
      F 0 = a.controlPoint.point → deriv F 0 ≠ 0 →
      Nonempty (LRWStageEstimates (logPosNorm f) base A.delta A.constant a F) := by
  intro a F hFdiff hFbij hFzero hFderiv
  let P := Classical.choice (A.prawitz a F hFdiff hFbij hFzero hFderiv)
  exact ⟨P.toStageEstimates A.delta_pos A.delta_lt_one a hFbij.mapsTo
    (A.hall a F hFdiff hFbij hFzero)⟩

/-- Add the one planar-topology theorem to the separated Hall and Prawitz estimates. -/
def toLogPosShortPathInputs {f : ℂ → ℂ} {base : ℂ} (A : LRWStageTheorems f base)
    (hsimplyConnected : ∀ a : LRWAdmissiblePoint A.delta (logPosNorm f) base,
      IsSimplyConnected (lrwDomain A.delta (logPosNorm f) base a.controlPoint)) :
    LRWLogPosShortPathInputs f base where
  delta := A.delta
  constant := A.constant
  delta_pos := A.delta_pos
  delta_lt_one := A.delta_lt_one
  constant_nonneg := A.constant_nonneg
  simplyConnected := hsimplyConnected
  estimates := A.estimates

end LRWStageTheorems

end Erdos515
