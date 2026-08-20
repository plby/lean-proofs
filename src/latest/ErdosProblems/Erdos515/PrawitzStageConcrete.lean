/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos515.PrawitzStage
import ErdosProblems.Erdos515.RadialVariation
import ErdosProblems.Erdos515.LogDerivative

/-!
# The concrete Hall--Prawitz stage

This file combines the two explicit exceptional sets with the radial variation estimate.  In
particular, neither exceptional direction is assigned a fictitious finite real supremum: the
variation estimate is used only after Hall's selection has avoided both bad sets.
-/

open Metric MeasureTheory Set
open scoped ENNReal Real

noncomputable section

namespace Erdos515
namespace PrawitzStageConcrete

/-- The fixed universal constant supplied to the LRW short-path construction. -/
def prawitzStageConstant : ℝ :=
  4 * PrawitzStage.radialThreshold * LogDerivative.logThreshold

lemma prawitzStageConstant_nonneg : 0 ≤ prawitzStageConstant := by
  unfold prawitzStageConstant
  positivity [PrawitzStage.radialThreshold_pos, LogDerivative.logThreshold_pos]

/-- Package the concrete radial and logarithmic estimates once the measure estimate for the
logarithmic exceptional set is available.  This is split out so that the purely geometric
assembly is independent of the proof of the planar logarithmic-area estimate. -/
noncomputable def prawitzStageData_of_logArea
    {u : ℂ → ℝ} {base : ℂ} {delta : ℝ}
    {a : LRWAdmissiblePoint delta u base} {F : ℂ → ℂ}
    (hFdiff : DifferentiableOn ℂ F (ball 0 1))
    (hFinj : InjOn F (ball 0 1)) (hFderiv : deriv F 0 ≠ 0)
    (hlogArea : volume (LogDerivative.logBad (PrawitzStage.normalizedMap F)) <
      ENNReal.ofReal (Real.pi / 4)) :
    LRWPrawitzStageData u base delta prawitzStageConstant a F := by
  let G : ℂ → ℂ := PrawitzStage.normalizedMap F
  have hG : AnalyticOnNhd ℂ G (ball 0 1) :=
    PrawitzStage.normalizedMap_analyticOnNhd hFdiff hFderiv
  have hGinj : InjOn G (ball 0 1) :=
    PrawitzStage.normalizedMap_injOn hFinj hFderiv
  exact PrawitzStage.prawitzStageData_of_normalized_variation
    hFdiff hFinj hFderiv (LogDerivative.logBad G) LogDerivative.logThreshold
    LogDerivative.logThreshold_nonneg hlogArea (by
      intro theta htheta hradial hlog
      apply RadialVariation.normalized_radialCurve_eVariation_le
        hG hGinj (PrawitzStage.normalizedMap_zero F)
        PrawitzStage.radialThreshold_pos.le LogDerivative.logThreshold_nonneg
      · intro r hr
        exact PrawitzStage.radialQuotient_le_threshold htheta hradial hr
      · exact LogDerivative.logRadialIntegralE_le_of_not_mem_logBad htheta hlog)
    (by
      unfold prawitzStageConstant
      exact le_rfl)

/-- The unconditional concrete Prawitz-stage provider used by the LRW recursion.  The image and
normalization hypotheses are kept in the exact form produced by the Riemann-mapping stage. -/
theorem prawitzStageData {f : ℂ → ℂ} (base : ℂ)
    (a : LRWAdmissiblePoint lrwRecursionDelta (logPosNorm f) base)
    (F : ℂ → ℂ)
    (hFdiff : DifferentiableOn ℂ F (ball 0 1))
    (hFbij : BijOn F (ball 0 1)
      (lrwDomain lrwRecursionDelta (logPosNorm f) base a.controlPoint))
    (_hFzero : F 0 = a.controlPoint.point)
    (hFderiv : deriv F 0 ≠ 0) :
    Nonempty (LRWPrawitzStageData (logPosNorm f) base lrwRecursionDelta
      prawitzStageConstant a F) := by
  let G : ℂ → ℂ := PrawitzStage.normalizedMap F
  have hG : AnalyticOnNhd ℂ G (ball 0 1) :=
    PrawitzStage.normalizedMap_analyticOnNhd hFdiff hFderiv
  have hGinj : InjOn G (ball 0 1) :=
    PrawitzStage.normalizedMap_injOn hFbij.injOn hFderiv
  have hlogArea : volume (LogDerivative.logBad G) <
      ENNReal.ofReal (Real.pi / 4) :=
    LogDerivative.volume_logBad_lt_quarter hG hGinj
      (PrawitzStage.normalizedMap_zero F)
      (PrawitzStage.deriv_normalizedMap_zero hFdiff hFderiv)
  exact ⟨prawitzStageData_of_logArea hFdiff hFbij.injOn hFderiv hlogArea⟩

end PrawitzStageConcrete
end Erdos515
