import ErdosProblems.Erdos1002.AnnularCompoundPoissonGrid
import ErdosProblems.Erdos1002.FinalAssemblyClosedReconstruction

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Supplying the continuum limiting laws to the final assembly

The continuum probability side of the proof is unconditional here.  For a
fixed outer cutoff, the only remaining input is convergence of the arithmetic
annular shot to the explicitly constructed annular compound-Poisson law.  The
inner-cutoff and outer-cutoff passages are discharged by
`AnnularCompoundPoisson`.
-/

open Filter MeasureTheory Set
open scoped ENNReal Topology

namespace Erdos1002

noncomputable section

local instance probabilityMeasureWeakTopologyFACP :
    TopologicalSpace (ProbabilityMeasure ℝ) :=
  ProbabilityMeasure.instTopologicalSpace

/-- Fixed-cutoff continuum law used in `FinalAssembly`. -/
def continuumCutoffLaw (A : ℕ) : ProbabilityMeasure ℝ :=
  cutoffCompoundPoissonProbability (A : ℝ)

theorem tendsto_continuumCutoffLaw_cauchy :
    Tendsto continuumCutoffLaw atTop (nhds cauchyLimitProbability) := by
  exact tendsto_cutoffCompoundPoissonProbability_cauchy

/-- Once each arithmetic annular shot converges to its explicit continuum
compound-Poisson law, the singular-coordinate deletion theorem gives the
literal fixed-cutoff shot limit. -/
theorem tendsto_finiteResonanceShotLaw_cutoffCompoundPoisson
    {A : ℝ} (hA : 0 < A)
    (hAnnular : ∀ m : ℕ,
      Tendsto
        (fun N ↦ annularMarkedShotLaw N (smallCoordinateCutoff m) A)
        atTop
        (nhds (annularCompoundPoissonProbability
          (smallCoordinateCutoff m) A))) :
    Tendsto (fun N ↦ finiteResonanceShotLaw N A) atTop
      (nhds (cutoffCompoundPoissonProbability A)) := by
  exact tendsto_finiteResonanceShotLaw_of_annular_limits A
    (fun m ↦ annularCompoundPoissonProbability (smallCoordinateCutoff m) A)
    (cutoffCompoundPoissonProbability A) hAnnular
    (tendsto_annularCompoundPoissonProbability_smallCoordinateCutoff hA)

/-- Final assembly with the continuum Poisson/Cauchy limit supplied rather
than assumed.  The remaining hypotheses are precisely the arithmetic
fixed-cutoff convergence and minor-shot deletion inputs. -/
theorem erdos1002Conclusion_of_continuumCutoff_fixed_limits_and_minor
    (hfixed : ∀ A : ℕ,
      Tendsto (fun N ↦ finiteResonanceShotLaw N (A : ℝ)) atTop
        (nhds (continuumCutoffLaw A)))
    (hminor : ∀ r > 0, ∀ δ > 0,
      ∀ᶠ A : ℕ in atTop, ∀ᶠ N : ℕ in atTop,
        uniform01Measure.real
          {α | r ≤ ‖normalizedMinorResonanceShotSum N (A : ℝ) α‖} < δ) :
    Erdos1002Conclusion := by
  exact erdos1002Conclusion_of_fixed_limits_and_minor continuumCutoffLaw
    hfixed tendsto_continuumCutoffLaw_cauchy hminor

end

end Erdos1002
