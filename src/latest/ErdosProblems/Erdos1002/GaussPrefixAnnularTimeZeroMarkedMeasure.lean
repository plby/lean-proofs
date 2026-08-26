import ErdosProblems.Erdos1002.GaussPrefixAnnularTimeZeroMode
import ErdosProblems.Erdos1002.GaussPrefixAnnularTaggedMarkedMeasure
import ErdosProblems.Erdos1002.GaussPrefixAnnularMarkedMeasure

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Reindexed annular marked measures including time zero

This is the faithful tagged Fourier-to-Haar closure, using the zero-mode
theorem which includes the first time cell.  It removes the obsolete
positive-time assumption from the marked finite-measure interface.
-/

open Filter MeasureTheory
open scoped BigOperators Topology

namespace Erdos1002

noncomputable section

theorem
    tendsto_reindexedAnnularUniformMarkedTupleFiniteMeasure_including_time_zero_of_nonzero
    {ε A : ℝ} (hε : 0 < ε) (hεA : ε < A)
    {grid : ℕ} (hgrid : 0 < grid)
    (k : AnnularGridIndex grid → ℕ)
    (hr : 0 < MixedOccurrenceCount k)
    (htime : ∀ i, 0 < k i → i.time.1 < grid)
    (hsigned : ∀ i, 0 < k i → i.signed.1 < grid)
    (e₀ : Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k)
    (hnonzero :
      ∀ mode : Fin (MixedOccurrenceCount k) → ℤ, mode ≠ 0 →
        Tendsto
          (fun N : ℕ ↦
            reindexedAnnularUniformMarkedFourierTupleSum
              (ε := ε) (A := A) N k e₀ mode)
          atTop (nhds 0)) :
    Tendsto
      (fun N : ℕ ↦
        reindexedAnnularUniformMarkedTupleFiniteMeasure
          (ε := ε) (A := A) N k e₀)
      atTop
      (nhds
        (scaledUnitTorusHaarFiniteMeasure
          (r := MixedOccurrenceCount k)
          (annularOccurrenceTimeDensity k *
            annularOccurrenceSignedDensity ε A k))) := by
  apply tendsto_finiteMeasure_of_unitTorusFourier
  · apply
      (tendsto_annularCanonicalUniformZeroMode_including_time_zero
        hε hεA hgrid k hr htime hsigned).congr'
    filter_upwards with N
    exact
      (reindexedAnnularUniformMarkedTupleFiniteMeasure_real_mass
        (ε := ε) (A := A) N k e₀).symm
  · intro mode hmode
    apply (hnonzero mode hmode).congr'
    filter_upwards with N
    exact
      (integral_reindexedAnnularUniformMarkedTupleFiniteMeasure_mFourier
        (ε := ε) (A := A) N k e₀ mode).symm

/-- Every product half-open torus box is a continuity set for the limit,
so its reindexed canonical mass has the corresponding Haar limit. -/
theorem
    tendsto_reindexedAnnularUniformMarkedTupleFiniteMeasure_halfOpenBox_including_time_zero
    {ε A : ℝ} (hε : 0 < ε) (hεA : ε < A)
    {grid : ℕ} (hgrid : 0 < grid)
    (k : AnnularGridIndex grid → ℕ)
    (hr : 0 < MixedOccurrenceCount k)
    (htime : ∀ i, 0 < k i → i.time.1 < grid)
    (hsigned : ∀ i, 0 < k i → i.signed.1 < grid)
    (e₀ : Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k)
    (hnonzero :
      ∀ mode : Fin (MixedOccurrenceCount k) → ℤ, mode ≠ 0 →
        Tendsto
          (fun N : ℕ ↦
            reindexedAnnularUniformMarkedFourierTupleSum
              (ε := ε) (A := A) N k e₀ mode)
          atTop (nhds 0))
    (torusLower torusUpper : Fin (MixedOccurrenceCount k) → ℝ) :
    Tendsto
      (fun N : ℕ ↦
        reindexedAnnularUniformMarkedTupleFiniteMeasure
          (ε := ε) (A := A) N k e₀
          (unitTorusHalfOpenBox torusLower torusUpper))
      atTop
      (nhds
        (scaledUnitTorusHaarFiniteMeasure
          (r := MixedOccurrenceCount k)
          (annularOccurrenceTimeDensity k *
            annularOccurrenceSignedDensity ε A k)
          (unitTorusHalfOpenBox torusLower torusUpper))) := by
  apply tendsto_finiteMeasure_apply_of_null_frontier
    (tendsto_reindexedAnnularUniformMarkedTupleFiniteMeasure_including_time_zero_of_nonzero
      hε hεA hgrid k hr htime hsigned e₀ hnonzero)
  · exact scaledUnitTorusHaarFiniteMeasure_ne_zero
      (annularOccurrenceMassDensity_pos hεA hgrid k)
  · rw [scaledUnitTorusHaarFiniteMeasure_normalize
      (annularOccurrenceMassDensity_pos hεA hgrid k)]
    exact unitTorusHaarProbabilityMeasure_frontier_halfOpenBox
      torusLower torusUpper

end

end Erdos1002
