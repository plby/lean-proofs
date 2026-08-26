import ErdosProblems.Erdos1002.NearResonantCarrierPhysical
import ErdosProblems.Erdos1002.FinalAssemblyContinuousPoisson

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# From a near-resonant `L²` estimate to minor-shot deletion

This module connects the analytic form of the near-resonant estimate to the
exact probability interface used by the final assembly.  The cutoff `A` and
the main parameter `N` are placed on the product filter
`atTop ×ˢ atTop`; this is a uniform rectangular two-parameter limit and is
therefore slightly stronger than the iterated eventual statement required by
`FinalAssembly`.

Together with `NearResonantUnconditionalBridge`, the local multiplier input
to this interface is now unconditional: neither the theorem below nor the
cross-square-root Ramanujan bound has a Chan--Kumchev premise.  The zero
carrier has an exact physical dyadic Parseval identity, and every nonzero
Bernoulli carrier is now identified with the abstract modulation/leakage
sequence in `NearResonantCarrierPhysical`.  What remains outside this module
is the quantitative summation of those carrier projections over dyadic
denominator blocks, followed by smoothing removal and comparison with the
literal minor shot.
-/

open Filter MeasureTheory Set
open scoped ENNReal Topology

namespace Erdos1002

noncomputable section

/-- The exact two-parameter `L²` statement expected from the global
near-resonant square-function argument.  Writing it as a named proposition
prevents a local arithmetic hypothesis from being hidden in the final
assembly. -/
def MinorShotTwoParameterL2Deletion : Prop :=
  Tendsto
    (fun z : ℕ × ℕ =>
      eLpNorm (normalizedMinorResonanceShotSum z.2 (z.1 : ℝ))
        (2 : ENNReal) uniform01Measure)
    ((atTop : Filter ℕ) ×ˢ (atTop : Filter ℕ)) (nhds 0)

/-- A uniform two-parameter `L²` deletion estimate implies exactly the
iterated convergence-in-probability estimate consumed by `FinalAssembly`.
All conversions between the product filter, convergence in measure, and real
measure thresholds are explicit. -/
theorem minorProbabilityDeletion_of_twoParameterL2
    (hL2 : MinorShotTwoParameterL2Deletion) :
    ∀ r > 0, ∀ δ > 0,
      ∀ᶠ A : ℕ in atTop, ∀ᶠ N : ℕ in atTop,
        uniform01Measure.real
          {α | r ≤ ‖normalizedMinorResonanceShotSum N (A : ℝ) α‖} < δ := by
  have hmeasure : TendstoInMeasure uniform01Measure
      (fun z : ℕ × ℕ => normalizedMinorResonanceShotSum z.2 (z.1 : ℝ))
      ((atTop : Filter ℕ) ×ˢ (atTop : Filter ℕ)) 0 := by
    apply tendstoInMeasure_of_tendsto_eLpNorm (p := (2 : ENNReal)) (by norm_num)
    · intro z
      exact (measurable_normalizedMinorResonanceShotSum z.2 (z.1 : ℝ)).aestronglyMeasurable
    · exact aestronglyMeasurable_zero
    · simpa only [Pi.zero_apply, sub_zero] using! hL2
  rw [tendstoInMeasure_iff_measureReal_norm] at hmeasure
  intro r hr δ hδ
  have hthreshold := hmeasure r hr
  rw [Metric.tendsto_nhds] at hthreshold
  have hevent : ∀ᶠ z : ℕ × ℕ in
      ((atTop : Filter ℕ) ×ˢ (atTop : Filter ℕ)),
      uniform01Measure.real
        {α | r ≤ ‖normalizedMinorResonanceShotSum z.2 (z.1 : ℝ) α‖} < δ := by
    have hball := hthreshold δ hδ
    simpa [Real.dist_eq, abs_of_nonneg measureReal_nonneg] using! hball
  rcases eventually_prod_iff.mp hevent with ⟨sA, hsA, sN, hsN, hrect⟩
  filter_upwards [hsA] with A hA
  filter_upwards [hsN] with N hN
  exact hrect hA hN

/-- Final assembly with the minor-shot premise stated in its natural `L²`
form.  In particular, no Chan--Kumchev interface occurs among the remaining
logical assumptions. -/
theorem erdos1002Conclusion_of_fixed_limits_and_minorL2
    (νA : ℕ → ProbabilityMeasure ℝ)
    (hfixed : ∀ A : ℕ,
      Tendsto (fun N ↦ finiteResonanceShotLaw N (A : ℝ)) atTop
        (@nhds (ProbabilityMeasure ℝ)
          probabilityMeasureWeakTopologyFACR (νA A)))
    (hPoissonLimit : Tendsto νA atTop
      (@nhds (ProbabilityMeasure ℝ)
        probabilityMeasureWeakTopologyFACR cauchyLimitProbability))
    (hminorL2 : MinorShotTwoParameterL2Deletion) :
    Erdos1002Conclusion := by
  exact erdos1002Conclusion_of_fixed_limits_and_minor νA hfixed hPoissonLimit
    (minorProbabilityDeletion_of_twoParameterL2 hminorL2)

/-- Version with the continuum compound-Poisson-to-Cauchy passage already
discharged.  The only remaining probability input is the arithmetic
fixed-cutoff convergence to `continuumCutoffLaw`. -/
theorem erdos1002Conclusion_of_continuumCutoff_fixed_limits_and_minorL2
    (hfixed : ∀ A : ℕ,
      Tendsto (fun N ↦ finiteResonanceShotLaw N (A : ℝ)) atTop
        (@nhds (ProbabilityMeasure ℝ)
          probabilityMeasureWeakTopologyFACR (continuumCutoffLaw A)))
    (hminorL2 : MinorShotTwoParameterL2Deletion) :
    Erdos1002Conclusion := by
  exact erdos1002Conclusion_of_continuumCutoff_fixed_limits_and_minor
    hfixed (minorProbabilityDeletion_of_twoParameterL2 hminorL2)

end

end Erdos1002
