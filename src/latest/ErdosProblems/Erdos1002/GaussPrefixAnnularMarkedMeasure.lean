import ErdosProblems.Erdos1002.GaussPrefixAnnularUniformZeroMode
import ErdosProblems.Erdos1002.UnitTorusFourierMeasureConvergence

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# The annular marked tuple measure after the zero-mode calculation

The literal uniform-Lebesgue zero mode for the canonical annular tuple
families is already known.  The abstract Fourier criterion for finite
measures on a product torus is also already known.  This file joins those
two results without inserting a point-process assumption.

Consequently the only analytic input to the marked-measure convergence
theorem below is the explicit vanishing of each nonzero aggregate torus
Fourier coefficient.  Both the coefficient and the limiting measure are
the literal objects used elsewhere in the formalization.
-/

open Filter MeasureTheory
open scoped BigOperators Topology

namespace Erdos1002

noncomputable section

/-! ## Positivity of the annular zero-mode mass -/

/-- Every labeled time/parity factor in a positive grid has positive
density.  The statement is independent of which cells are active because
`annularOccurrenceTimeDensity` is indexed only by actual occurrences. -/
theorem annularOccurrenceTimeDensity_pos
    {grid : ℕ} (hgrid : 0 < grid)
    (k : AnnularGridIndex grid → ℕ) :
    0 < annularOccurrenceTimeDensity k := by
  unfold annularOccurrenceTimeDensity
  apply Finset.prod_pos
  intro z _hz
  exact div_pos
    (sub_pos.mpr
      (intervalGridPoint_strictMono_step
        (a := (0 : ℝ)) (b := 1) (k := z.1.time.1)
        zero_lt_one hgrid))
    (mul_pos (by norm_num) gaussRoofMean_pos)

/-- Every labeled signed-value factor has positive density on a genuine
annulus and a positive grid. -/
theorem annularOccurrenceSignedDensity_pos
    {ε A : ℝ} (hεA : ε < A)
    {grid : ℕ} (hgrid : 0 < grid)
    (k : AnnularGridIndex grid → ℕ) :
    0 < annularOccurrenceSignedDensity ε A k := by
  unfold annularOccurrenceSignedDensity
  apply Finset.prod_pos
  intro z _hz
  exact div_pos
    (sub_pos.mpr
      (intervalGridPoint_strictMono_step
        (a := signedGridLower ε A z.1.sign)
        (b := signedGridUpper ε A z.1.sign)
        (k := z.1.signed.1)
        (signedGridLower_lt_upper hεA z.1.sign) hgrid))
    (Real.log_pos (by norm_num))

/-- The complete canonical annular zero-mode limit is strictly positive
as soon as at least one occurrence is present (and in fact the same proof
also covers the empty product). -/
theorem annularOccurrenceMassDensity_pos
    {ε A : ℝ} (hεA : ε < A)
    {grid : ℕ} (hgrid : 0 < grid)
    (k : AnnularGridIndex grid → ℕ) :
    0 <
      annularOccurrenceTimeDensity k *
        annularOccurrenceSignedDensity ε A k :=
  mul_pos (annularOccurrenceTimeDensity_pos hgrid k)
    (annularOccurrenceSignedDensity_pos hεA hgrid k)

/-! ## Exact Fourier-to-Haar closure for the annular family -/

/-- The strongest marked-measure conclusion that follows from the proved
uniform zero mode and a literal nonzero-mode cancellation theorem.

There is no abstract equidistribution or point-process hypothesis here:
`hnonzero` is exactly the aggregate arithmetic Fourier coefficient of the
canonical annular depth families under `uniform01Measure`. -/
theorem
    tendsto_annularCanonicalUniformMarkedTupleFiniteMeasure_of_nonzero
    {ε A : ℝ} (hε : 0 < ε) (hεA : ε < A)
    {grid : ℕ} (hgrid : 0 < grid)
    (k : AnnularGridIndex grid → ℕ)
    (hr : 0 < MixedOccurrenceCount k)
    (htimePositive : ∀ i, 0 < k i → 0 < i.time.1)
    (htime : ∀ i, 0 < k i → i.time.1 < grid)
    (hsigned : ∀ i, 0 < k i → i.signed.1 < grid)
    (hnonzero :
      ∀ mode : Fin (MixedOccurrenceCount k) → ℤ, mode ≠ 0 →
        Tendsto
          (fun N : ℕ ↦
            aggregateUniformMovingSignedMarkedFourierTupleSum
              (β := Fin (MixedOccurrenceCount k) ≃
                GaussPrefixMixedOccurrence k)
              N (Real.log (N : ℝ))
              (fun e ↦ flattenedAnnularSignedLower ε A e)
              (fun e ↦ flattenedAnnularSignedUpper ε A e)
              mode
              (fun e ↦ canonicalAnnularGridTupleFamily N k e))
          atTop (nhds 0)) :
    Tendsto
      (fun N : ℕ ↦
        aggregateUniformMovingSignedMarkedTupleFiniteMeasure
          (β := Fin (MixedOccurrenceCount k) ≃
            GaussPrefixMixedOccurrence k)
          N (Real.log (N : ℝ))
          (fun e ↦ flattenedAnnularSignedLower ε A e)
          (fun e ↦ flattenedAnnularSignedUpper ε A e)
          (fun e ↦ canonicalAnnularGridTupleFamily N k e))
      atTop
      (nhds
        (scaledUnitTorusHaarFiniteMeasure
          (r := MixedOccurrenceCount k)
          (annularOccurrenceTimeDensity k *
            annularOccurrenceSignedDensity ε A k))) := by
  let signedLower :
      (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) →
        Fin (MixedOccurrenceCount k) → ℝ :=
    fun e ↦ flattenedAnnularSignedLower ε A e
  let signedUpper :
      (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) →
        Fin (MixedOccurrenceCount k) → ℝ :=
    fun e ↦ flattenedAnnularSignedUpper ε A e
  let tuples :
      ℕ →
        (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) →
        Finset (Fin (MixedOccurrenceCount k) → ℕ) :=
    fun N e ↦ canonicalAnnularGridTupleFamily N k e
  have hmass :
      Tendsto
        (fun N : ℕ ↦
          aggregateMovingSignedApproximationTupleMassSum
            uniform01Measure (Real.log (N : ℝ))
            signedLower signedUpper (tuples N))
        atTop
        (nhds
          (annularOccurrenceTimeDensity k *
            annularOccurrenceSignedDensity ε A k)) := by
    simpa only [signedLower, signedUpper, tuples,
      aggregateUniformMovingSignedApproximationTupleMassSum] using!
      tendsto_annularCanonicalUniformZeroMode
        hε hεA hgrid k hr htimePositive htime hsigned
  have hfourier :
      ∀ mode : Fin (MixedOccurrenceCount k) → ℤ, mode ≠ 0 →
        Tendsto
          (fun N : ℕ ↦
            aggregateMovingSignedMarkedFourierTupleSum
              uniform01Measure N (Real.log (N : ℝ))
              signedLower signedUpper mode (tuples N))
          atTop (nhds 0) := by
    intro mode hmode
    simpa only [signedLower, signedUpper, tuples,
      aggregateUniformMovingSignedMarkedFourierTupleSum] using!
      hnonzero mode hmode
  simpa only [signedLower, signedUpper, tuples,
    aggregateUniformMovingSignedMarkedTupleFiniteMeasure] using!
    tendsto_aggregateMovingSignedMarkedTupleFiniteMeasure_of_fourier
      uniform01Measure (fun N : ℕ ↦ N)
      (fun N : ℕ ↦ Real.log (N : ℝ))
      signedLower signedUpper tuples
      (annularOccurrenceTimeDensity k *
        annularOccurrenceSignedDensity ε A k)
      hmass hfourier

/-- Concrete continuity-box consequence of the preceding marked-measure
limit.  Endpoint nullity is supplied by the proved quotient-torus frontier
theorem, not by an informal boundary convention. -/
theorem
    tendsto_annularCanonicalUniformMarkedTupleHalfOpenBox_of_nonzero
    {ε A : ℝ} (hε : 0 < ε) (hεA : ε < A)
    {grid : ℕ} (hgrid : 0 < grid)
    (k : AnnularGridIndex grid → ℕ)
    (hr : 0 < MixedOccurrenceCount k)
    (htimePositive : ∀ i, 0 < k i → 0 < i.time.1)
    (htime : ∀ i, 0 < k i → i.time.1 < grid)
    (hsigned : ∀ i, 0 < k i → i.signed.1 < grid)
    (hnonzero :
      ∀ mode : Fin (MixedOccurrenceCount k) → ℤ, mode ≠ 0 →
        Tendsto
          (fun N : ℕ ↦
            aggregateUniformMovingSignedMarkedFourierTupleSum
              (β := Fin (MixedOccurrenceCount k) ≃
                GaussPrefixMixedOccurrence k)
              N (Real.log (N : ℝ))
              (fun e ↦ flattenedAnnularSignedLower ε A e)
              (fun e ↦ flattenedAnnularSignedUpper ε A e)
              mode
              (fun e ↦ canonicalAnnularGridTupleFamily N k e))
          atTop (nhds 0))
    (torusLower torusUpper : Fin (MixedOccurrenceCount k) → ℝ) :
    Tendsto
      (fun N : ℕ ↦
        aggregateUniformMovingSignedMarkedTupleFiniteMeasure
          (β := Fin (MixedOccurrenceCount k) ≃
            GaussPrefixMixedOccurrence k)
          N (Real.log (N : ℝ))
          (fun e ↦ flattenedAnnularSignedLower ε A e)
          (fun e ↦ flattenedAnnularSignedUpper ε A e)
          (fun e ↦ canonicalAnnularGridTupleFamily N k e)
          (unitTorusHalfOpenBox torusLower torusUpper))
      atTop
      (nhds
        (scaledUnitTorusHaarFiniteMeasure
          (r := MixedOccurrenceCount k)
          (annularOccurrenceTimeDensity k *
            annularOccurrenceSignedDensity ε A k)
          (unitTorusHalfOpenBox torusLower torusUpper))) := by
  apply tendsto_finiteMeasure_apply_of_null_frontier
    (tendsto_annularCanonicalUniformMarkedTupleFiniteMeasure_of_nonzero
      hε hεA hgrid k hr htimePositive htime hsigned hnonzero)
  · exact scaledUnitTorusHaarFiniteMeasure_ne_zero
      (annularOccurrenceMassDensity_pos hεA hgrid k)
  · rw [scaledUnitTorusHaarFiniteMeasure_normalize
      (annularOccurrenceMassDensity_pos hεA hgrid k)]
    exact unitTorusHaarProbabilityMeasure_frontier_halfOpenBox
      torusLower torusUpper

end

end Erdos1002
