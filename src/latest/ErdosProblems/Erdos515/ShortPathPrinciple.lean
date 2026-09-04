/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos515.AnalyticConstruction
import ErdosProblems.Erdos515.RiemannMapping

/-!
# Analytic assembly of the LRW short-path principle

This module records the topology and limit arguments between a normalized Riemann map and the
finite Hall--Prawitz short-path theorem.  In particular, finite radial variation forces a finite
limit, bijectivity of the Riemann map forces that limit onto the frontier, and continuity of the
control function identifies its value with the exact sublevel defining the domain.
-/

open Filter MeasureTheory Metric Set
open scoped ENNReal NNReal Topology

namespace Erdos515

lemma shortPathRadialPoint_mem_unitDisk {r theta : ℝ} (hr : r ∈ Ico (0 : ℝ) 1) :
    shortPathRadialPoint r theta ∈ ball (0 : ℂ) 1 := by
  rw [mem_ball_zero_iff]
  simp [shortPathRadialPoint, abs_of_nonneg hr.1, hr.2]

lemma tendsto_shortPathRadialPoint_one (theta : ℝ) :
    Tendsto (fun r ↦ shortPathRadialPoint r theta)
      (nhdsWithin (1 : ℝ) (Ico (0 : ℝ) 1))
      (nhds (Complex.exp (Complex.I * theta))) := by
  have htoOne : Tendsto id (nhdsWithin (1 : ℝ) (Ico (0 : ℝ) 1)) (nhds 1) :=
    tendsto_id.mono_left inf_le_left
  have hcontinuous : Continuous (fun r : ℝ ↦ shortPathRadialPoint r theta) := by
    unfold shortPathRadialPoint
    fun_prop
  simpa [shortPathRadialPoint] using hcontinuous.continuousAt.tendsto.comp htoOne

/-- A bijective holomorphic disk map cannot have a radial limit in the interior of its image. -/
theorem riemannMap_noInteriorLimit {D : Set ℂ} {F : ℂ → ℂ}
    (hDopen : IsOpen D)
    (hFdiff : DifferentiableOn ℂ F (ball 0 1))
    (hFbij : BijOn F (ball 0 1) D) :
    ∀ (theta : ℝ) (b : ℂ),
      Tendsto (shortPathRadialCurve F theta)
        (nhdsWithin (1 : ℝ) (Ico (0 : ℝ) 1)) (nhds b) → b ∉ D := by
  have hopen : ∀ s ⊆ ball (0 : ℂ) 1, IsOpen s → IsOpen (F '' s) := by
    refine ((hFdiff.analyticOnNhd isOpen_ball).is_constant_or_isOpen
      (convex_ball (0 : ℂ) 1).isPreconnected).resolve_left ?_
    rintro ⟨w, hw⟩
    have hzero : (0 : ℂ) ∈ ball 0 1 := by simp
    have hhalf : (1 / 2 : ℂ) ∈ ball 0 1 := by norm_num [mem_ball_zero_iff]
    have heq : (0 : ℂ) = 1 / 2 := hFbij.injOn hzero hhalf ((hw 0 hzero).trans (hw _ hhalf).symm)
    norm_num at heq
  let G : ℂ → ℂ := Function.invFunOn F (ball 0 1)
  have hinv : Set.InvOn G F (ball (0 : ℂ) 1) D := hFbij.invOn_invFunOn
  have hGmaps : MapsTo G D (ball (0 : ℂ) 1) := hFbij.surjOn.mapsTo_invFunOn
  have hGcont : ∀ z ∈ D, ContinuousAt G z := by
    intro z hz
    rw [continuousAt_def]
    intro t ht
    rcases _root_.mem_nhds_iff.mp ht with ⟨s, hst, hsopen, hGs⟩
    have hGz : G z ∈ ball (0 : ℂ) 1 := hGmaps hz
    have himOpen : IsOpen (F '' (s ∩ ball (0 : ℂ) 1)) :=
      hopen _ inter_subset_right (hsopen.inter isOpen_ball)
    have hzimg : z ∈ F '' (s ∩ ball (0 : ℂ) 1) :=
      ⟨G z, ⟨hGs, hGz⟩, hinv.2 hz⟩
    refine mem_of_superset (himOpen.mem_nhds hzimg) ?_
    rintro y ⟨x, ⟨hxs, hxball⟩, rfl⟩
    exact hst (by simpa [hinv.1 hxball])
  intro theta b hb hbD
  let l : Filter ℝ := nhdsWithin (1 : ℝ) (Ico (0 : ℝ) 1)
  have hclosure : (1 : ℝ) ∈ closure (Ico (0 : ℝ) 1) := by simp
  let : l.NeBot := mem_closure_iff_nhdsWithin_neBot.mp hclosure
  have hGb : Tendsto (fun r ↦ G (shortPathRadialCurve F theta r)) l (nhds (G b)) :=
    (hGcont b hbD).tendsto.comp hb
  have heventual : (fun r ↦ G (shortPathRadialCurve F theta r)) =ᶠ[l]
      (fun r ↦ shortPathRadialPoint r theta) := by
    filter_upwards [self_mem_nhdsWithin] with r hr
    exact hinv.1 (shortPathRadialPoint_mem_unitDisk hr)
  have hradial : Tendsto (fun r ↦ shortPathRadialPoint r theta) l
      (nhds (Complex.exp (Complex.I * theta))) :=
    tendsto_shortPathRadialPoint_one theta
  have heq : G b = Complex.exp (Complex.I * theta) :=
    tendsto_nhds_unique hGb (hradial.congr' heventual.symm)
  have hGbnorm : ‖G b‖ < 1 := by
    simpa only [mem_ball_zero_iff] using hGmaps hbD
  rw [heq] at hGbnorm
  have hexpNorm : ‖Complex.exp (Complex.I * theta)‖ = 1 := by
    rw [Complex.norm_exp]
    simp
  linarith

/-- Finite radial variation and the no-interior-limit property force the control function to
approach the exact level defining a strict-sublevel component. -/
theorem tendsto_control_along_finite_riemannRadius
    {u : ℂ → ℝ} (hu : Continuous u) {level : ℝ} {base : ℂ}
    {F : ℂ → ℂ} {theta L : ℝ}
    (hradial_mem : ∀ r ∈ Ico (0 : ℝ) 1,
      shortPathRadialCurve F theta r ∈ sublevelComponent u level base)
    (hvariation : eVariationOn (shortPathRadialCurve F theta) (Ico (0 : ℝ) 1) ≤
      ENNReal.ofReal L)
    (hnoInterior : ∀ b : ℂ,
      Tendsto (shortPathRadialCurve F theta)
        (nhdsWithin (1 : ℝ) (Ico (0 : ℝ) 1)) (nhds b) →
      b ∉ sublevelComponent u level base) :
    Tendsto (fun r ↦ u (shortPathRadialCurve F theta r))
      (nhdsWithin (1 : ℝ) (Ico (0 : ℝ) 1)) (nhds level) := by
  have hbounded : BoundedVariationOn (shortPathRadialCurve F theta) (Ico (0 : ℝ) 1) :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hvariation
  obtain ⟨b, hb⟩ := hbounded.exists_tendsto_left (1 : ℝ)
  have hset : Ico (0 : ℝ) 1 ∩ Iio 1 = Ico (0 : ℝ) 1 := by
    exact inter_eq_left.mpr fun _ hz ↦ hz.2
  have hb' : Tendsto (shortPathRadialCurve F theta)
      (nhdsWithin (1 : ℝ) (Ico (0 : ℝ) 1)) (nhds b) := by
    simpa only [hset] using hb
  have hclosureParam : (1 : ℝ) ∈ closure (Ico (0 : ℝ) 1) := by simp
  let : (nhdsWithin (1 : ℝ) (Ico (0 : ℝ) 1)).NeBot :=
    mem_closure_iff_nhdsWithin_neBot.mp hclosureParam
  have hbclosure : b ∈ closure (sublevelComponent u level base) := by
    apply isClosed_closure.mem_of_tendsto hb'
    filter_upwards [eventually_mem_nhdsWithin] with r hr
    exact subset_closure (hradial_mem r hr)
  have hbnot : b ∉ sublevelComponent u level base := hnoInterior b hb'
  have hbfrontier : b ∈ frontier (sublevelComponent u level base) := by
    change b ∈ closure (sublevelComponent u level base) \
      interior (sublevelComponent u level base)
    exact ⟨hbclosure, fun hbint ↦ hbnot
      ((isOpen_sublevelComponent hu level base).interior_eq.symm ▸ hbint)⟩
  have hblevel : u b = level := eq_level_of_mem_frontier_sublevelComponent hu hbfrontier
  change Tendsto (u ∘ shortPathRadialCurve F theta)
    (nhdsWithin (1 : ℝ) (Ico (0 : ℝ) 1)) (nhds level)
  rw [← hblevel]
  exact hu.continuousAt.tendsto.comp hb'

lemma continuous_lrwNormalizedControl {u : ℂ → ℝ} (hu : Continuous u)
    (delta : ℝ) (a : PositiveControlPoint u) :
    Continuous (lrwNormalizedControl delta u a) := by
  unfold lrwNormalizedControl
  fun_prop

/-- The Koebe-quarter inclusion gives the conformal-radius estimate used in the short-path
length bound. -/
theorem norm_deriv_le_four_infDist_of_koebe {D : Set ℂ} {a : ℂ} {F : ℂ → ℂ}
    (hDopen : IsOpen D) (ha : a ∈ D) (hDproper : D ≠ univ)
    (hkoebe : ball a (‖deriv F 0‖ / 4) ⊆ D) :
    ‖deriv F 0‖ ≤ 4 * infDist a (frontier D) := by
  have hfront : (frontier D).Nonempty :=
    nonempty_frontier_iff.mpr ⟨⟨a, ha⟩, hDproper⟩
  have hquarter : ‖deriv F 0‖ / 4 ≤ infDist a (frontier D) := by
    rw [le_infDist hfront]
    intro y hy
    have hyNotD : y ∉ D := by
      intro hyD
      have hyBoth : y ∈ D ∩ frontier D := ⟨hyD, hy⟩
      rw [hDopen.inter_frontier_eq] at hyBoth
      exact hyBoth
    have hyNotBall : y ∉ ball a (‖deriv F 0‖ / 4) := fun hyBall ↦ hyNotD (hkoebe hyBall)
    rw [mem_ball, not_lt] at hyNotBall
    simpa only [dist_comm] using hyNotBall
  nlinarith

/-- The radial information remaining after a Riemann map has been chosen at one LRW stage.

The three measure/variation fields are precisely the Hall lower bound, the Prawitz radial-maximal
exceptional estimate, and the logarithmic-derivative area estimate.  All boundary-limit and
finite-truncation bookkeeping is proved below rather than included as an input. -/
structure LRWFiniteRadialData (u : ℂ → ℝ) (base : ℂ) (delta constant : ℝ)
    (a : LRWAdmissiblePoint delta u base) where
  F : ℂ → ℂ
  F_diff : DifferentiableOn ℂ F (ball 0 1)
  F_bij : BijOn F (ball 0 1) (lrwDomain delta u base a.controlPoint)
  F_zero : F 0 = a.controlPoint.point
  good : Set ℝ
  radialBad : Set ℝ
  logBad : Set ℝ
  K : ℝ
  J : ℝ
  scale : ℝ
  K_nonneg : 0 ≤ K
  J_nonneg : 0 ≤ J
  scale_nonneg : 0 ≤ scale
  hall : ENNReal.ofReal Real.pi ≤ volume good
  prawitz : volume radialBad < ENNReal.ofReal (Real.pi / 4)
  logArea : volume logBad < ENNReal.ofReal (Real.pi / 4)
  good_radius : ∀ theta ∈ good, ∀ r ∈ Ico (0 : ℝ) 1,
    shortPathRadialCurve F theta r ∈ lrwDomain delta u base a.controlPoint ∧
      0 < lrwNormalizedControl delta u a.controlPoint (shortPathRadialCurve F theta r)
  variation : ∀ theta ∈ good,
    theta ∉ radialBad → theta ∉ logBad →
    eVariationOn (shortPathRadialCurve F theta) (Ico (0 : ℝ) 1) ≤
      ENNReal.ofReal (K * scale * J)
  koebe : scale ≤ 4 * infDist a.controlPoint.point
    (frontier (lrwDomain delta u base a.controlPoint))
  constant_bound : 4 * K * J ≤ constant

namespace LRWFiniteRadialData

/-- Hall--Prawitz radial data at one stage produces the exact finite LRW recursive step. -/
theorem toStepOutput {u : ℂ → ℝ} {base : ℂ} {delta constant : ℝ}
    (hu : Continuous u) (hdelta0 : 0 < delta) (hdelta1 : delta < 1)
    (a : LRWAdmissiblePoint delta u base) (R : LRWFiniteRadialData u base delta constant a) :
    Nonempty (LRWStepOutput u base delta constant a) := by
  let D : Set ℂ := lrwDomain delta u base a.controlPoint
  let v : ℂ → ℝ := lrwNormalizedControl delta u a.controlPoint
  let level : ℝ := lrwLevel delta u a.controlPoint
  have hDopen : IsOpen D := isOpen_sublevelComponent hu _ _
  have hv : Continuous v := continuous_lrwNormalizedControl hu delta a.controlPoint
  have hcontinuous : ∀ theta ∈ R.good,
      ContinuousOn (shortPathRadialCurve R.F theta) (Ico (0 : ℝ) 1) := by
    intro theta _htheta
    rw [show shortPathRadialCurve R.F theta =
      R.F ∘ (fun r ↦ shortPathRadialPoint r theta) by rfl]
    apply R.F_diff.continuousOn.comp
      (show ContinuousOn (fun r ↦ shortPathRadialPoint r theta) (Ico (0 : ℝ) 1) by
        apply Continuous.continuousOn
        unfold shortPathRadialPoint
        fun_prop)
    intro r hr
    exact shortPathRadialPoint_mem_unitDisk hr
  have hnoInterior : ∀ theta ∈ R.good, ∀ b : ℂ,
      Tendsto (shortPathRadialCurve R.F theta)
        (nhdsWithin (1 : ℝ) (Ico (0 : ℝ) 1)) (nhds b) → b ∉ D := by
    intro theta _htheta
    exact riemannMap_noInteriorLimit hDopen R.F_diff R.F_bij theta
  have htargetLimit : ∀ theta ∈ R.good,
      theta ∉ R.radialBad → theta ∉ R.logBad →
      Tendsto (fun r ↦ u (shortPathRadialCurve R.F theta r))
        (nhdsWithin (1 : ℝ) (Ico (0 : ℝ) 1)) (nhds level) := by
    intro theta htheta hthetaMax hthetaLog
    exact tendsto_control_along_finite_riemannRadius hu
      (fun r hr ↦ (R.good_radius theta htheta r hr).1)
      (R.variation theta htheta hthetaMax hthetaLog) (hnoInterior theta htheta)
  have htarget : lrwGrowthFactor delta * u a.controlPoint.point < level := by
    dsimp [level]
    unfold lrwLevel
    have hgrowth := lrwGrowthFactor_lt_inv_one_sub hdelta0 hdelta1
    have hmul := mul_lt_mul_of_pos_right hgrowth a.controlPoint.positive
    simpa only [div_eq_mul_inv, mul_comm] using hmul
  obtain ⟨c, _hcD, hcgrowth, P, hPlength⟩ := short_positive_polygonal_path
    R.good R.radialBad R.logBad R.K R.J R.scale level
      (lrwGrowthFactor delta * u a.controlPoint.point)
      hDopen hv R.F_zero R.K_nonneg R.J_nonneg R.scale_nonneg
      R.hall R.prawitz R.logArea hcontinuous R.good_radius R.variation R.koebe
      htargetLimit htarget
  have hnextPos : 0 < u c := by
    have hfactor : 0 < lrwGrowthFactor delta :=
      zero_lt_one.trans (one_lt_lrwGrowthFactor hdelta0 hdelta1)
    exact (mul_pos hfactor a.controlPoint.positive).trans hcgrowth
  refine ⟨{
    next := ⟨c, hnextPos⟩
    growth := hcgrowth.le
    arc := P
    length_le := hPlength.trans ?_ }⟩
  apply ENNReal.ofReal_le_ofReal
  exact mul_le_mul_of_nonneg_right R.constant_bound infDist_nonneg

end LRWFiniteRadialData

/-- The genuinely analytic estimates at a stage whose normalized Riemann map has already been
chosen.  The conformal scale is fixed to `‖F'(0)‖`, so Koebe's theorem supplies its distance
comparison automatically. -/
structure LRWStageEstimates (u : ℂ → ℝ) (base : ℂ) (delta constant : ℝ)
    (a : LRWAdmissiblePoint delta u base) (F : ℂ → ℂ) where
  good : Set ℝ
  radialBad : Set ℝ
  logBad : Set ℝ
  K : ℝ
  J : ℝ
  K_nonneg : 0 ≤ K
  J_nonneg : 0 ≤ J
  hall : ENNReal.ofReal Real.pi ≤ volume good
  prawitz : volume radialBad < ENNReal.ofReal (Real.pi / 4)
  logArea : volume logBad < ENNReal.ofReal (Real.pi / 4)
  good_radius : ∀ theta ∈ good, ∀ r ∈ Ico (0 : ℝ) 1,
    shortPathRadialCurve F theta r ∈ lrwDomain delta u base a.controlPoint ∧
      0 < lrwNormalizedControl delta u a.controlPoint (shortPathRadialCurve F theta r)
  variation : ∀ theta ∈ good,
    theta ∉ radialBad → theta ∉ logBad →
    eVariationOn (shortPathRadialCurve F theta) (Ico (0 : ℝ) 1) ≤
      ENNReal.ofReal (K * ‖deriv F 0‖ * J)
  constant_bound : 4 * K * J ≤ constant

namespace LRWStageEstimates

/-- Add the Riemann-map and Koebe data to a stage's Hall--Prawitz estimates. -/
noncomputable def toFiniteRadialData {u : ℂ → ℝ} {base : ℂ} {delta constant : ℝ}
    {a : LRWAdmissiblePoint delta u base} {F : ℂ → ℂ}
    (E : LRWStageEstimates u base delta constant a F)
    (hFdiff : DifferentiableOn ℂ F (ball 0 1))
    (hFbij : BijOn F (ball 0 1) (lrwDomain delta u base a.controlPoint))
    (hFzero : F 0 = a.controlPoint.point)
    (hkoebe : ‖deriv F 0‖ ≤ 4 * infDist a.controlPoint.point
      (frontier (lrwDomain delta u base a.controlPoint))) :
    LRWFiniteRadialData u base delta constant a where
  F := F
  F_diff := hFdiff
  F_bij := hFbij
  F_zero := hFzero
  good := E.good
  radialBad := E.radialBad
  logBad := E.logBad
  K := E.K
  J := E.J
  scale := ‖deriv F 0‖
  K_nonneg := E.K_nonneg
  J_nonneg := E.J_nonneg
  scale_nonneg := norm_nonneg _
  hall := E.hall
  prawitz := E.prawitz
  logArea := E.logArea
  good_radius := E.good_radius
  variation := E.variation
  koebe := hkoebe
  constant_bound := E.constant_bound

end LRWStageEstimates

/-- A uniform choice of Hall--Prawitz radial data at every admissible state. -/
structure LRWRadialShortPathPrinciple (u : ℂ → ℝ) (base : ℂ) where
  delta : ℝ
  constant : ℝ
  delta_pos : 0 < delta
  delta_lt_one : delta < 1
  constant_nonneg : 0 ≤ constant
  radial : ∀ a : LRWAdmissiblePoint delta u base,
    Nonempty (LRWFiniteRadialData u base delta constant a)

namespace LRWRadialShortPathPrinciple

/-- Convert the uniform analytic radial statement to the recursion's short-path principle. -/
def toShortPathPrinciple {u : ℂ → ℝ} {base : ℂ} (hu : Continuous u)
    (R : LRWRadialShortPathPrinciple u base) : LRWShortPathPrinciple u base where
  delta := R.delta
  constant := R.constant
  delta_pos := R.delta_pos
  delta_lt_one := R.delta_lt_one
  constant_nonneg := R.constant_nonneg
  step a := (Classical.choice (R.radial a)).toStepOutput hu R.delta_pos R.delta_lt_one a

end LRWRadialShortPathPrinciple

/-- Exact remaining inputs after all Riemann-mapping and recursive bookkeeping has been removed.
The first field is the planar simple-connectivity statement for LRW sublevel components.  The
second is the uniform Hall--Prawitz/log-area estimate for an arbitrary normalized Riemann map. -/
structure LRWLogPosShortPathInputs (f : ℂ → ℂ) (base : ℂ) where
  delta : ℝ
  constant : ℝ
  delta_pos : 0 < delta
  delta_lt_one : delta < 1
  constant_nonneg : 0 ≤ constant
  simplyConnected : ∀ a : LRWAdmissiblePoint delta (logPosNorm f) base,
    IsSimplyConnected (lrwDomain delta (logPosNorm f) base a.controlPoint)
  estimates : ∀ (a : LRWAdmissiblePoint delta (logPosNorm f) base) (F : ℂ → ℂ),
    DifferentiableOn ℂ F (ball 0 1) →
    BijOn F (ball 0 1) (lrwDomain delta (logPosNorm f) base a.controlPoint) →
    F 0 = a.controlPoint.point → deriv F 0 ≠ 0 →
    Nonempty (LRWStageEstimates (logPosNorm f) base delta constant a F)

namespace LRWLogPosShortPathInputs

/-- Riemann mapping and Koebe turn the exact remaining inputs into the uniform radial principle. -/
theorem toRadialShortPathPrinciple {f : ℂ → ℂ} {base : ℂ}
    (hf : Differentiable ℂ f) (htrans : ¬ IsPolynomialFunction f)
    (A : LRWLogPosShortPathInputs f base) :
    Nonempty (LRWRadialShortPathPrinciple (logPosNorm f) base) := by
  refine ⟨{
    delta := A.delta
    constant := A.constant
    delta_pos := A.delta_pos
    delta_lt_one := A.delta_lt_one
    constant_nonneg := A.constant_nonneg
    radial := ?_ }⟩
  intro a
  let D : Set ℂ := lrwDomain A.delta (logPosNorm f) base a.controlPoint
  have hDopen : IsOpen D := isOpen_sublevelComponent (continuous_logPosNorm hf.continuous) _ _
  have hDproper : D ≠ univ := by
    obtain ⟨z, hz⟩ := logPosNorm_unbounded hf htrans
      (lrwLevel A.delta (logPosNorm f) a.controlPoint)
    exact sublevelComponent_ne_univ_of_le_value hz
  obtain ⟨F, hFdiff, hFbij, hFzero, hFderiv, hquarter⟩ :=
    exists_riemannMap_with_koebe hDopen (A.simplyConnected a) hDproper a.mem_domain
  let E := Classical.choice (A.estimates a F hFdiff hFbij hFzero hFderiv)
  have hkoebe : ‖deriv F 0‖ ≤
      4 * infDist a.controlPoint.point (frontier D) :=
    norm_deriv_le_four_infDist_of_koebe hDopen a.mem_domain hDproper hquarter
  exact ⟨E.toFiniteRadialData hFdiff hFbij hFzero hkoebe⟩

end LRWLogPosShortPathInputs

end Erdos515
