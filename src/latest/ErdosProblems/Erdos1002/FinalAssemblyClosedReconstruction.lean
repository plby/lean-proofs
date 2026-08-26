import ErdosProblems.Erdos1002.FinalAssembly
import ErdosProblems.Erdos1002.NaturalCutoffShotErrorSublog

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Final assembly after closing the reconstruction input

The Fourier--Ramanujan reconstruction estimate is now unconditional.  This
module removes that hypothesis from the final interface, leaving only the
minor-shot deletion and fixed-cutoff marked-process limit.
-/

open Filter MeasureTheory Set
open scoped Topology ENNReal

namespace Erdos1002

noncomputable section

local instance probabilityMeasureWeakTopologyFACR :
    TopologicalSpace (ProbabilityMeasure ℝ) :=
  ProbabilityMeasure.instTopologicalSpace

theorem erdos1002Conclusion_of_fixed_limits_and_minor
    (νA : ℕ → ProbabilityMeasure ℝ)
    (hfixed : ∀ A : ℕ,
      Tendsto (fun N ↦ finiteResonanceShotLaw N (A : ℝ)) atTop
        (@nhds (ProbabilityMeasure ℝ) probabilityMeasureWeakTopologyFACR (νA A)))
    (hPoissonLimit : Tendsto νA atTop
      (@nhds (ProbabilityMeasure ℝ) probabilityMeasureWeakTopologyFACR
        cauchyLimitProbability))
    (hminor : ∀ r > 0, ∀ δ > 0,
      ∀ᶠ A : ℕ in atTop, ∀ᶠ N : ℕ in atTop,
        uniform01Measure.real
          {α | r ≤ ‖normalizedMinorResonanceShotSum N (A : ℝ) α‖} < δ) :
    Erdos1002Conclusion := by
  exact erdos1002Conclusion_of_shot_inputs νA hfixed hPoissonLimit
    tendsto_rotation_reconstruction_of_window_carrier_estimate hminor

end


end Erdos1002
