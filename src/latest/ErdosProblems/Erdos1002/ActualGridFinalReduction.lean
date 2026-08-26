import ErdosProblems.Erdos1002.AnnularCompoundPoissonGrid
import ErdosProblems.Erdos1002.FinalAssemblyContinuousPoisson
import ErdosProblems.Erdos1002.MarkedResonanceGaussCountBridge
import ErdosProblems.Erdos1002.NearResonantMinorAssembly

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Final reduction to the actual marked-grid factorial limits

This module gives one source-faithful name to the arithmetic marked-Poisson
input.  It then derives both uses of that input: the fixed-annulus shot law
and deletion of the lower transition layer.  No abstract point-process
hypothesis is inserted between the literal resonance counts and these two
consequences.
-/

open Filter MeasureTheory
open scoped Topology

namespace Erdos1002

noncomputable section

open MultivariateFactorialMomentMethod

local instance probabilityMeasureWeakTopologyAGFR :
    TopologicalSpace (ProbabilityMeasure ℝ) :=
  ProbabilityMeasure.instTopologicalSpace

/-- Mixed falling-factorial convergence for every positive literal annulus
and every explicit finite grid.  This is the exact actual-count statement
that the continued-fraction argument must prove. -/
def ActualAnnularGridFactorialLimits : Prop :=
  ∀ {ε A : ℝ}, 0 < ε → ε < A →
    ∀ m (k : AnnularGridIndex (m + 1) → ℕ),
      Tendsto
        (fun N ↦ mixedFactorialMoment
          (markedResonanceCountVectorLaw N N
            (annularGridCell ε A (m + 1))
            (fun i ↦ measurableSet_annularGridCell ε A (m + 1) i)) k)
        atTop
        (nhds (∏ i,
          (annularGridCellPoissonRate ε A (m + 1) i : ℝ) ^ (k i)))

/-- The same statement after the exact denominator-to-convergent
bijection, expressed under the literal Gauss-prefix count law. -/
def GaussPrefixAnnularGridFactorialLimits : Prop :=
  ∀ {ε A : ℝ}, 0 < ε → ε < A →
    ∀ m (k : AnnularGridIndex (m + 1) → ℕ),
      Tendsto
        (fun N ↦ mixedFactorialMoment
          (gaussPrefixMarkedCountVectorLaw N
            (annularGridCell ε A (m + 1))
            (fun i ↦ measurableSet_annularGridCell ε A (m + 1) i)) k)
        atTop
        (nhds (∏ i,
          (annularGridCellPoissonRate ε A (m + 1) i : ℝ) ^ (k i)))

/-- The all-zero factorial order is a genuine separate base case: both the
literal moment and the target product are identically one.  Positive-order
canonical occurrence parametrizations are never invoked here. -/
theorem gaussPrefixAnnularGridFactorialLimit_zero
    {ε A : ℝ} (m : ℕ) :
    Tendsto
      (fun N ↦ mixedFactorialMoment
        (gaussPrefixMarkedCountVectorLaw N
          (annularGridCell ε A (m + 1))
          (fun i ↦ measurableSet_annularGridCell ε A (m + 1) i))
        (fun _i ↦ 0))
      atTop
      (nhds (∏ i,
        (annularGridCellPoissonRate ε A (m + 1) i : ℝ) ^ (0 : ℕ))) := by
  simp only [mixedFactorialMoment_zero, prod_pow_zero]
  exact tendsto_const_nhds

/-- The already proved literal count-law identity transfers every
Gauss-prefix grid limit to the actual rational-resonance count. -/
theorem actualAnnularGridFactorialLimits_of_gaussPrefix
    (hFac : GaussPrefixAnnularGridFactorialLimits) :
    ActualAnnularGridFactorialLimits := by
  intro ε A hε hεA m k
  exact tendsto_mixedFactorialMoment_markedResonance_of_gaussPrefix
    (annularGridCell ε A (m + 1))
    (fun i ↦ measurableSet_annularGridCell ε A (m + 1) i)
    (annularGridCell_subset_compactAnnularMarkedRegion
      hεA (by omega)) hε.le k (hFac hε hεA m k)

/-- The global actual-grid statement contains exactly the annuli used in
the lower-transition deletion. -/
theorem lowerTransitionActualGridFactorialLimits_of_actualAnnular
    (hFac : ActualAnnularGridFactorialLimits) :
    LowerTransitionActualGridFactorialLimits := by
  intro A hA m k
  exact hFac (ε := (A : ℝ) / 2) (A := (A : ℝ))
    (by positivity) (by
      have hAreal : 0 < (A : ℝ) := by exact_mod_cast hA
      linarith) m k

/-- Actual-grid factorial limits give the literal annular marked-shot law,
with the natural denominator cutoff on both the count and the shot. -/
theorem tendsto_annularMarkedShotLaw_compoundPoisson_of_actualAnnular
    (hFac : ActualAnnularGridFactorialLimits)
    {ε A : ℝ} (hε : 0 < ε) (hεA : ε < A) :
    Tendsto (fun N ↦ annularMarkedShotLaw N ε A) atTop
      (nhds (annularCompoundPoissonProbability ε A)) := by
  exact tendsto_annularMarkedShotLaw_compoundPoisson_of_gridFactorialMoments
    (fun N : ℕ ↦ N) hε hεA (eventually_ge_atTop 2)
      (hFac hε hεA)

/-- Every cutoff in the small-coordinate sequence is positive and at most
one. -/
private theorem smallCoordinateCutoff_pos_le_one (m : ℕ) :
    0 < smallCoordinateCutoff m ∧ smallCoordinateCutoff m ≤ 1 := by
  unfold smallCoordinateCutoff
  constructor
  · positivity
  · rw [div_le_iff₀ (by positivity)]
    have hm : 0 ≤ (m : ℝ) := by positivity
    linarith

/-- Consequently the fixed-cutoff shot law is closed for every outer
cutoff strictly larger than one.  This is sufficient for the final
outer-cutoff limit and avoids an artificial degenerate annulus at the first
index of the chosen inner-cutoff sequence. -/
theorem tendsto_finiteResonanceShotLaw_cutoffCompoundPoisson_of_actualAnnular
    (hFac : ActualAnnularGridFactorialLimits)
    {A : ℝ} (hA : 1 < A) :
    Tendsto (fun N ↦ finiteResonanceShotLaw N A) atTop
      (nhds (cutoffCompoundPoissonProbability A)) := by
  apply tendsto_finiteResonanceShotLaw_cutoffCompoundPoisson (by linarith)
  intro m
  have hm := smallCoordinateCutoff_pos_le_one m
  exact tendsto_annularMarkedShotLaw_compoundPoisson_of_actualAnnular
    hFac hm.1 (hm.2.trans_lt hA)

/-- Natural cutoffs shifted by two are therefore all covered by the same
literal actual-grid theorem. -/
theorem tendsto_shiftedFiniteResonanceShotLaw_of_actualAnnular
    (hFac : ActualAnnularGridFactorialLimits) (A : ℕ) :
    Tendsto
      (fun N ↦ finiteResonanceShotLaw N ((A + 2 : ℕ) : ℝ)) atTop
      (nhds (cutoffCompoundPoissonProbability ((A + 2 : ℕ) : ℝ))) := by
  apply tendsto_finiteResonanceShotLaw_cutoffCompoundPoisson_of_actualAnnular
    hFac
  exact_mod_cast (show 1 < A + 2 by omega)

/-- The same actual-grid theorem supplies the exact physical lower-layer
probability deletion used by the minor-shot decomposition. -/
theorem lowerTransitionProbabilityDeletion_of_actualAnnular
    (ε : ℝ) (hε : 0 < ε)
    (hFac : ActualAnnularGridFactorialLimits) :
    ∀ r > 0, ∀ δ > 0,
      ∀ᶠ A : ℕ in atTop, ∀ᶠ N : ℕ in atTop,
        uniform01Measure.real
          {alpha | r ≤ ‖normalizedNearMinorLowerTransitionSum
            N (A : ℝ) ε alpha‖} < δ := by
  exact lowerTransitionProbabilityDeletion_of_actualGridFactorialLimits
    ε hε
      (lowerTransitionActualGridFactorialLimits_of_actualAnnular hFac)

/-- Reindexing the outer cutoff by `A ↦ A + 2` avoids only the two
degenerate initial cutoff parameters.  The existing minor deletion gives
the exact converging-together approximation along this cofinal sequence. -/
private theorem rotation_shiftedFinite_close_of_minor
    (hminor : ∀ r > 0, ∀ δ > 0,
      ∀ᶠ A : ℕ in atTop, ∀ᶠ N : ℕ in atTop,
        uniform01Measure.real
          {alpha | r ≤ ‖normalizedMinorResonanceShotSum
            N (A : ℝ) alpha‖} < δ) :
    ∀ r > 0, ∀ δ > 0,
      ∀ᶠ A : ℕ in atTop, ∀ᶠ N : ℕ in atTop,
        uniform01Measure.real
          {alpha | r ≤ ‖normalizedRotationSum N alpha -
            normalizedFiniteResonanceShotSum
              N ((A + 2 : ℕ) : ℝ) alpha‖} < δ := by
  have hclose := rotation_finite_close_of_reconstruction_and_minor
    tendsto_rotation_reconstruction_of_window_carrier_estimate hminor
  intro r hr δ hδ
  exact (Filter.tendsto_add_atTop_nat 2).eventually
    (hclose r hr δ hδ)

/-- The actual-grid factorial theorem plus the already assembled minor-shot
deletion imply the exact Erdős conclusion.  The cofinal shift is internal
and changes neither the original sequence `N` nor its asserted limit. -/
theorem erdos1002Conclusion_of_actualAnnular_and_minor
    (hFac : ActualAnnularGridFactorialLimits)
    (hminor : ∀ r > 0, ∀ δ > 0,
      ∀ᶠ A : ℕ in atTop, ∀ᶠ N : ℕ in atTop,
        uniform01Measure.real
          {alpha | r ≤ ‖normalizedMinorResonanceShotSum
            N (A : ℝ) alpha‖} < δ) :
    Erdos1002Conclusion := by
  let cutoff : ℕ → ℝ := fun A ↦ ((A + 2 : ℕ) : ℝ)
  let ν : ℕ → ProbabilityMeasure ℝ := fun A ↦
    cutoffCompoundPoissonProbability (cutoff A)
  have hfixed : ∀ A : ℕ,
      Tendsto (fun N ↦ finiteResonanceShotLaw N (cutoff A)) atTop
        (@nhds (ProbabilityMeasure ℝ)
          probabilityMeasureWeakTopologyAGFR (ν A)) := by
    intro A
    exact tendsto_shiftedFiniteResonanceShotLaw_of_actualAnnular hFac A
  have hindex : Tendsto (fun A : ℕ ↦ A + 2) atTop atTop :=
    Filter.tendsto_add_atTop_nat 2
  have hpoisson : Tendsto ν atTop
      (@nhds (ProbabilityMeasure ℝ)
        probabilityMeasureWeakTopologyAGFR cauchyLimitProbability) := by
    exact tendsto_cutoffCompoundPoissonProbability_cauchy.comp hindex
  have hclose := rotation_shiftedFinite_close_of_minor hminor
  have hweak := tendsto_map_of_convergingTogether
    (μ := uniform01Measure)
    (fun N ↦ normalizedRotationSum N)
    (fun A N ↦ normalizedFiniteResonanceShotSum N (cutoff A))
    ν cauchyLimitProbability
    (fun N ↦ (measurable_normalizedRotationSum N).aemeasurable)
    (fun A N ↦
      (measurable_normalizedFiniteResonanceShotSum
        N (cutoff A)).aemeasurable)
    (by simpa only [finiteResonanceShotLaw, uniform01] using! hfixed)
    hpoisson
    (by simpa only [cutoff] using! hclose)
  apply erdos1002Conclusion_of_rotationLaw_tendsto
  simpa only [rotationLaw, uniform01] using! hweak

/-- Final two-input reduction.  All reconstruction, probability, endpoint,
smoothing, continuum compound-Poisson, and converging-together steps have
been discharged.  What remains is precisely the actual marked-grid
factorial theorem and the fixed-away Ramanujan remainder estimate. -/
theorem erdos1002Conclusion_of_actualAnnular_and_fixedAway
    (ε : ℝ) (hε : 0 < ε) (hεhalf : ε < 1 / 2)
    (hFac : ActualAnnularGridFactorialLimits)
    (hfixedAway : ∀ r > 0, ∀ δ > 0,
      ∀ᶠ A : ℕ in atTop, ∀ᶠ N : ℕ in atTop,
        uniform01Measure.real
          {alpha | r ≤ ‖normalizedFixedAwayMinorRemainder
            N (A : ℝ) ε alpha‖} < δ) :
    Erdos1002Conclusion := by
  apply erdos1002Conclusion_of_actualAnnular_and_minor hFac
  exact minorProbabilityDeletion_of_actualGridFactorialLimits_and_fixedAway
    ε hε hεhalf
      (lowerTransitionActualGridFactorialLimits_of_actualAnnular hFac)
      hfixedAway

/-- Equivalent final interface on the continued-fraction side of the exact
count-law bridge. -/
theorem erdos1002Conclusion_of_gaussPrefix_and_fixedAway
    (ε : ℝ) (hε : 0 < ε) (hεhalf : ε < 1 / 2)
    (hFac : GaussPrefixAnnularGridFactorialLimits)
    (hfixedAway : ∀ r > 0, ∀ δ > 0,
      ∀ᶠ A : ℕ in atTop, ∀ᶠ N : ℕ in atTop,
        uniform01Measure.real
          {alpha | r ≤ ‖normalizedFixedAwayMinorRemainder
            N (A : ℝ) ε alpha‖} < δ) :
    Erdos1002Conclusion := by
  exact erdos1002Conclusion_of_actualAnnular_and_fixedAway
    ε hε hεhalf
      (actualAnnularGridFactorialLimits_of_gaussPrefix hFac)
      hfixedAway

end

end Erdos1002
