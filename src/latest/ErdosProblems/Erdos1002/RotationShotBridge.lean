import ErdosProblems.Erdos1002.ConvergenceBridge
import ErdosProblems.Erdos1002.ShotLaws
import ErdosProblems.Erdos1002.WeakPerturbation

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# From analytic shot estimates to weak convergence

These lemmas turn the manuscript's `L²` and convergence-in-probability
estimates into statements about probability laws.  They contain no analytic
estimate themselves; their role is to make the final logical implications
kernel-checkable.
-/

open Filter MeasureTheory
open scoped Topology ENNReal

namespace Erdos1002

noncomputable section

local instance probabilityMeasureWeakTopologyRSB :
    TopologicalSpace (ProbabilityMeasure ℝ) :=
  ProbabilityMeasure.instTopologicalSpace

/-- An `L²`-vanishing reconstruction error transfers weak convergence from
the reconstructed shot law to the original rotation-sum law. -/
theorem rotationLaw_tendsto_of_reconstructedShotLaw_tendsto_of_eLpNorm
    (ν : ProbabilityMeasure ℝ)
    (hshot : Tendsto reconstructedShotLaw atTop
      (@nhds (ProbabilityMeasure ℝ) probabilityMeasureWeakTopologyRSB ν))
    (hL2 : Tendsto
      (fun N ↦ eLpNorm
        (normalizedRotationSum N - normalizedReconstructedShotSum N)
        2 uniform01Measure) atTop (nhds 0)) :
    Tendsto rotationLaw atTop
      (@nhds (ProbabilityMeasure ℝ) probabilityMeasureWeakTopologyRSB ν) := by
  have hprob : TendstoInMeasure uniform01Measure
      (normalizedRotationSum - normalizedReconstructedShotSum) atTop 0 := by
    apply tendstoInMeasure_of_tendsto_eLpNorm (p := (2 : ENNReal)) (by norm_num)
    · intro N
      exact ((measurable_normalizedRotationSum N).sub
        (measurable_normalizedReconstructedShotSum N)).aestronglyMeasurable
    · exact aestronglyMeasurable_zero
    · simpa only [Pi.sub_apply, sub_zero] using! hL2
  have h := tendsto_map_of_tendsto_map_of_tendstoInMeasure_sub
    (μ := uniform01Measure)
    (fun N ↦ normalizedReconstructedShotSum N)
    (fun N ↦ normalizedRotationSum N) ν
    (fun N ↦ (measurable_normalizedReconstructedShotSum N).aemeasurable)
    (fun N ↦ (measurable_normalizedRotationSum N).aemeasurable)
    hshot hprob
  simpa [rotationLaw, reconstructedShotLaw, uniform01] using! h

/-- For a fixed cutoff, a minor-shot error vanishing in probability transfers
weak convergence from the retained finite shots to all reconstructed shots. -/
theorem reconstructedShotLaw_tendsto_of_finiteShotLaw_tendsto
    (A : ℝ) (ν : ProbabilityMeasure ℝ)
    (hfinite : Tendsto (fun N ↦ finiteResonanceShotLaw N A) atTop
      (@nhds (ProbabilityMeasure ℝ) probabilityMeasureWeakTopologyRSB ν))
    (hminor : TendstoInMeasure uniform01Measure
      (fun N ↦ normalizedMinorResonanceShotSum N A) atTop 0) :
    Tendsto reconstructedShotLaw atTop
      (@nhds (ProbabilityMeasure ℝ) probabilityMeasureWeakTopologyRSB ν) := by
  have hdiff : TendstoInMeasure uniform01Measure
      ((fun N ↦ normalizedReconstructedShotSum N) -
        (fun N ↦ normalizedFiniteResonanceShotSum N A)) atTop 0 := by
    apply hminor.congr'
    · filter_upwards with N
      filter_upwards with α
      simp only [Pi.sub_apply]
      rw [normalizedReconstructedShotSum_eq_finite_add_minor]
      ring
    · exact Filter.EventuallyEq.rfl
  have h := tendsto_map_of_tendsto_map_of_tendstoInMeasure_sub
    (μ := uniform01Measure)
    (fun N ↦ normalizedFiniteResonanceShotSum N A)
    (fun N ↦ normalizedReconstructedShotSum N) ν
    (fun N ↦ (measurable_normalizedFiniteResonanceShotSum N A).aemeasurable)
    (fun N ↦ (measurable_normalizedReconstructedShotSum N).aemeasurable)
    hfinite hdiff
  simpa [reconstructedShotLaw, finiteResonanceShotLaw, uniform01] using! h

end

end Erdos1002
