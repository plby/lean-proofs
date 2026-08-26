import Mathlib.Probability.Distributions.Poisson.Basic

open MeasureTheory ProbabilityTheory

namespace Erdos1002

/-- The direct measure definition agrees with the earlier probability-mass
function presentation used by the imported proof. -/
theorem poissonMeasure_eq_toMeasure (r : NNReal) :
    poissonMeasure r = (poissonPMF r).toMeasure := by
  apply Measure.ext_of_singleton
  intro n
  rw [poissonMeasure_singleton,
    PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton n)]
  rfl

end Erdos1002
