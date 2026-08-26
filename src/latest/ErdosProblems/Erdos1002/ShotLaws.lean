import ErdosProblems.Erdos1002.ProbabilityFoundations
import ErdosProblems.Erdos1002.Shots

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Probability laws of the shot approximations

The normalization is kept outside the finite sums, exactly as in the
manuscript.  This module packages each measurable approximation as a
`ProbabilityMeasure`, ready for weak-convergence arguments.
-/

open MeasureTheory

namespace Erdos1002

noncomputable section

def normalizedReconstructedShotSum (N : ℕ) (α : ℝ) : ℝ :=
  reconstructedShotSum N α / Real.log (N : ℝ)

def normalizedFiniteResonanceShotSum (N : ℕ) (A : ℝ) (α : ℝ) : ℝ :=
  finiteResonanceShotSum N A α / Real.log (N : ℝ)

def normalizedMinorResonanceShotSum (N : ℕ) (A : ℝ) (α : ℝ) : ℝ :=
  minorResonanceShotSum N A α / Real.log (N : ℝ)

theorem measurable_normalizedReconstructedShotSum (N : ℕ) :
    Measurable (normalizedReconstructedShotSum N) :=
  (measurable_reconstructedShotSum N).div_const _

theorem measurable_normalizedFiniteResonanceShotSum (N : ℕ) (A : ℝ) :
    Measurable (normalizedFiniteResonanceShotSum N A) :=
  (measurable_finiteResonanceShotSum N A).div_const _

theorem measurable_normalizedMinorResonanceShotSum (N : ℕ) (A : ℝ) :
    Measurable (normalizedMinorResonanceShotSum N A) :=
  (measurable_minorResonanceShotSum N A).div_const _

def reconstructedShotLaw (N : ℕ) : ProbabilityMeasure ℝ :=
  uniform01.map (measurable_normalizedReconstructedShotSum N).aemeasurable

def finiteResonanceShotLaw (N : ℕ) (A : ℝ) : ProbabilityMeasure ℝ :=
  uniform01.map (measurable_normalizedFiniteResonanceShotSum N A).aemeasurable

theorem normalizedReconstructedShotSum_eq_finite_add_minor
    (N : ℕ) (A : ℝ) (α : ℝ) :
    normalizedReconstructedShotSum N α =
      normalizedFiniteResonanceShotSum N A α +
        normalizedMinorResonanceShotSum N A α := by
  rw [normalizedReconstructedShotSum, normalizedFiniteResonanceShotSum,
    normalizedMinorResonanceShotSum,
    reconstructedShotSum_eq_finite_add_minor]
  ring

end

end Erdos1002
