import ErdosProblems.Erdos1002.GaussPrefixAnnularBoundaryCells
import ErdosProblems.Erdos1002.GaussPrefixAnnularTimeZeroMarkedMeasure

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Interior annular marked-measure closure

This module packages the final harmonic-analysis step of the marked
Gauss-prefix argument.  Vanishing of every nonzero labeled torus Fourier
mode, together with the already proved zero mode, gives convergence of the
canonical marked tuple measure on the exact half-open torus cell.  The
limit is then evaluated as the required product of Poisson rates.
-/

open Filter MeasureTheory Set
open scoped BigOperators Topology

namespace Erdos1002

noncomputable section

/-- The precise nonzero-mode input needed for all nonterminal annular
factorial rectangles.  The mode lives in one fixed labeled occurrence
order; chronological order tags are already reindexed in the definition
of the coefficient. -/
def GaussPrefixAnnularReindexedNonzeroFourierLimits : Prop :=
  ∀ {ε A : ℝ}, 0 < ε → ε < A →
    ∀ {grid : ℕ}, 0 < grid →
      ∀ (k : AnnularGridIndex grid → ℕ),
        0 < MixedOccurrenceCount k →
        (∀ i, 0 < k i → i.time.1 < grid) →
        (∀ i, 0 < k i → i.signed.1 < grid) →
        ∀ (e₀ : Fin (MixedOccurrenceCount k) ≃
            GaussPrefixMixedOccurrence k)
          (mode : Fin (MixedOccurrenceCount k) → ℤ),
          mode ≠ 0 →
            Tendsto
              (fun N : ℕ ↦
                reindexedAnnularUniformMarkedFourierTupleSum
                  (ε := ε) (A := A) N k e₀ mode)
              atTop (nhds 0)

/-- The nonzero Fourier input gives the exact real-valued mass limit for
the flattened half-open torus cell. -/
theorem
    tendsto_reindexedAnnularUniformMarkedTupleFiniteMeasure_real_torusBox
    (hFourier : GaussPrefixAnnularReindexedNonzeroFourierLimits)
    {ε A : ℝ} (hε : 0 < ε) (hεA : ε < A)
    {grid : ℕ} (hgrid : 0 < grid)
    (k : AnnularGridIndex grid → ℕ)
    (hr : 0 < MixedOccurrenceCount k)
    (htime : ∀ i, 0 < k i → i.time.1 < grid)
    (hsigned : ∀ i, 0 < k i → i.signed.1 < grid)
    (htorus : ∀ i, 0 < k i → i.torus.1 < grid)
    (e₀ : Fin (MixedOccurrenceCount k) ≃
      GaussPrefixMixedOccurrence k) :
    Tendsto
      (fun N : ℕ ↦
        (reindexedAnnularUniformMarkedTupleFiniteMeasure
          (ε := ε) (A := A) N k e₀ :
            Measure (UnitAddTorus (Fin (MixedOccurrenceCount k)))).real
          (unitTorusHalfOpenBox
            (flattenedAnnularTorusLower e₀)
            (flattenedAnnularTorusUpper e₀)))
      atTop
      (nhds
        (∏ i,
          (annularGridCellPoissonRate ε A grid i : ℝ) ^ k i)) := by
  have hENN :=
    tendsto_reindexedAnnularUniformMarkedTupleFiniteMeasure_halfOpenBox_including_time_zero
      hε hεA hgrid k hr htime hsigned e₀
      (hFourier hε hεA hgrid k hr htime hsigned e₀)
      (flattenedAnnularTorusLower e₀)
      (flattenedAnnularTorusUpper e₀)
  have hreal :=
    (NNReal.continuous_coe.tendsto
      ((scaledUnitTorusHaarFiniteMeasure
        (r := MixedOccurrenceCount k)
        (annularOccurrenceTimeDensity k *
          annularOccurrenceSignedDensity ε A k))
        (unitTorusHalfOpenBox
          (flattenedAnnularTorusLower e₀)
          (flattenedAnnularTorusUpper e₀)))).comp hENN
  have hlimit :
      (((scaledUnitTorusHaarFiniteMeasure
        (r := MixedOccurrenceCount k)
        (annularOccurrenceTimeDensity k *
          annularOccurrenceSignedDensity ε A k))
        (unitTorusHalfOpenBox
          (flattenedAnnularTorusLower e₀)
          (flattenedAnnularTorusUpper e₀)) : NNReal) : ℝ) =
        ∏ i,
          (annularGridCellPoissonRate ε A grid i : ℝ) ^ k i := by
    simpa only [FiniteMeasure.measureReal_eq_coe_coeFn] using!
      (scaledUnitTorusHaarFiniteMeasure_real_flattenedAnnularTorusBox_eq_prod_poissonRate
        hεA hgrid k htime hsigned htorus e₀)
  rw [hlimit] at hreal
  simpa only [Function.comp_apply,
    FiniteMeasure.measureReal_eq_coe_coeFn] using! hreal

end

end Erdos1002
