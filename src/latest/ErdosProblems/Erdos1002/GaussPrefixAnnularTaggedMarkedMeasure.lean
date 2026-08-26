import ErdosProblems.Erdos1002.GaussPrefixAnnularDepthBoxes
import ErdosProblems.Erdos1002.GaussPrefixAnnularUniformZeroMode
import ErdosProblems.Erdos1002.UnitTorusFourierMeasureConvergence

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Annular marked measures in one fixed labeled coordinate system

Each canonical depth family is sorted by a different occurrence order.
The torus coordinates of the literal mixed factorial statistic, however,
are labeled occurrences.  Therefore the tagged chronological measures
must be reindexed before they are added.

This file performs that reindexing exactly.  Its Fourier identity shows
that one fixed labeled mode is transformed on the tag `e` into the
tag-dependent chronological mode
`flattenedAnnularFourierMode e h`.  This is the faithful interface between
the mixed factorial coefficient and the chronological oscillatory
estimates.
-/

open Filter MeasureTheory Set
open scoped BigOperators Topology

namespace Erdos1002

noncomputable section

/-! ## Coordinate reindexing -/

/-- Reindex chronological coordinates belonging to order `e` into the
fixed reference order `e₀`.  Both coordinate systems represent the same
labeled occurrence. -/
def annularOrderReindex
    {ι : Type*} [Fintype ι] {k : ι → ℕ}
    (e₀ e : Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k)
    (z : UnitAddTorus (Fin (MixedOccurrenceCount k))) :
    UnitAddTorus (Fin (MixedOccurrenceCount k)) :=
  fun j ↦ z (e.symm (e₀ j))

theorem continuous_annularOrderReindex
    {ι : Type*} [Fintype ι] {k : ι → ℕ}
    (e₀ e : Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) :
    Continuous (annularOrderReindex e₀ e) := by
  apply continuous_pi
  intro j
  exact continuous_apply (e.symm (e₀ j))

theorem measurable_annularOrderReindex
    {ι : Type*} [Fintype ι] {k : ι → ℕ}
    (e₀ e : Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) :
    Measurable (annularOrderReindex e₀ e) :=
  (continuous_annularOrderReindex e₀ e).measurable

/-- Pulling a reference-order Fourier character through the coordinate
reindexing gives the corresponding tag-order Fourier character. -/
theorem unitAddTorus_mFourier_annularOrderReindex
    {ι : Type*} [Fintype ι] {k : ι → ℕ}
    (e₀ e : Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k)
    (mode : Fin (MixedOccurrenceCount k) → ℤ)
    (z : UnitAddTorus (Fin (MixedOccurrenceCount k))) :
    UnitAddTorus.mFourier mode (annularOrderReindex e₀ e z) =
      UnitAddTorus.mFourier
        (fun j ↦ mode (e₀.symm (e j))) z := by
  unfold UnitAddTorus.mFourier annularOrderReindex
  change
    (∏ j : Fin (MixedOccurrenceCount k),
      fourier (mode j) (z (e.symm (e₀ j)))) =
      ∏ j : Fin (MixedOccurrenceCount k),
        fourier (mode (e₀.symm (e j))) (z j)
  let p :
      Fin (MixedOccurrenceCount k) ≃ Fin (MixedOccurrenceCount k) :=
    e₀.trans e.symm
  have hp :
      ∀ j : Fin (MixedOccurrenceCount k),
        fourier (mode j) (z (e.symm (e₀ j))) =
          fourier (mode (e₀.symm (e (p j)))) (z (p j)) := by
    intro j
    dsimp only [p]
    rw [Equiv.trans_apply, e.apply_symm_apply,
      e₀.symm_apply_apply]
  exact Fintype.prod_equiv p _ _ hp

/-- In particular a labeled mixed mode `h`, flattened in the reference
order, pulls back to the same labeled mode flattened in the tag order. -/
theorem
    unitAddTorus_mFourier_annularOrderReindex_flattened
    {grid : ℕ} {k : AnnularGridIndex grid → ℕ}
    (e₀ e : Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k)
    (h : ∀ i, Fin (k i) → ℤ)
    (z : UnitAddTorus (Fin (MixedOccurrenceCount k))) :
    UnitAddTorus.mFourier (flattenedAnnularFourierMode e₀ h)
        (annularOrderReindex e₀ e z) =
      UnitAddTorus.mFourier (flattenedAnnularFourierMode e h) z := by
  rw [unitAddTorus_mFourier_annularOrderReindex]
  apply congrArg (fun m : Fin (MixedOccurrenceCount k) → ℤ ↦
    UnitAddTorus.mFourier m z)
  funext j
  have he :
      e₀ (e₀.symm (e j)) = e j :=
    e₀.apply_symm_apply (e j)
  simp only [flattenedAnnularFourierMode]
  rw [he]

/-! ## The correctly reindexed tagged aggregate -/

/-- Positive uniform-Lebesgue marked measure obtained after pushing every
chronological order tag into one fixed reference coordinate system. -/
def reindexedAnnularUniformMarkedTupleFiniteMeasure
    {ε A : ℝ} {grid : ℕ}
    (N : ℕ) (k : AnnularGridIndex grid → ℕ)
    (e₀ : Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) :
    FiniteMeasure (UnitAddTorus (Fin (MixedOccurrenceCount k))) := by
  classical
  exact ∑ e : Fin (MixedOccurrenceCount k) ≃
      GaussPrefixMixedOccurrence k,
    FiniteMeasure.map
      (movingSignedMarkedTupleFiniteMeasure
        uniform01Measure N (Real.log (N : ℝ))
        (flattenedAnnularSignedLower ε A e)
        (flattenedAnnularSignedUpper ε A e)
        (canonicalAnnularGridTupleFamily N k e))
      (annularOrderReindex e₀ e)

/-- Arithmetic Fourier coefficient of the preceding reindexed measure.
The mode is fixed in the reference coordinate system and is pulled back
separately through every order tag. -/
def reindexedAnnularUniformMarkedFourierTupleSum
    {ε A : ℝ} {grid : ℕ}
    (N : ℕ) (k : AnnularGridIndex grid → ℕ)
    (e₀ : Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k)
    (mode : Fin (MixedOccurrenceCount k) → ℤ) : ℂ :=
  ∑ e : Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k,
    uniformMovingSignedMarkedFourierTupleSum
      N (Real.log (N : ℝ))
      (flattenedAnnularSignedLower ε A e)
      (flattenedAnnularSignedUpper ε A e)
      (fun j ↦ mode (e₀.symm (e j)))
      (canonicalAnnularGridTupleFamily N k e)

/-- Fourier integration against the reindexed positive measure is exactly
the tag-dependent arithmetic coefficient. -/
theorem
    integral_reindexedAnnularUniformMarkedTupleFiniteMeasure_mFourier
    {ε A : ℝ} {grid : ℕ}
    (N : ℕ) (k : AnnularGridIndex grid → ℕ)
    (e₀ : Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k)
    (mode : Fin (MixedOccurrenceCount k) → ℤ) :
    (∫ z, UnitAddTorus.mFourier mode z
      ∂(reindexedAnnularUniformMarkedTupleFiniteMeasure
        (ε := ε) (A := A) N k e₀ :
          Measure (UnitAddTorus (Fin (MixedOccurrenceCount k))))) =
      reindexedAnnularUniformMarkedFourierTupleSum
        (ε := ε) (A := A) N k e₀ mode := by
  classical
  unfold reindexedAnnularUniformMarkedTupleFiniteMeasure
    reindexedAnnularUniformMarkedFourierTupleSum
  rw [FiniteMeasure.toMeasure_sum,
    MeasureTheory.integral_finset_sum_measure]
  · apply Finset.sum_congr rfl
    intro e _he
    rw [FiniteMeasure.toMeasure_map,
      MeasureTheory.integral_map
        (measurable_annularOrderReindex e₀ e).aemeasurable
        (Continuous.aestronglyMeasurable
          (UnitAddTorus.mFourier mode).continuous)]
    rw [show
        (fun z ↦ UnitAddTorus.mFourier mode
          (annularOrderReindex e₀ e z)) =
        UnitAddTorus.mFourier
          (fun j ↦ mode (e₀.symm (e j))) by
      funext z
      exact unitAddTorus_mFourier_annularOrderReindex
        e₀ e mode z]
    exact integral_movingSignedMarkedTupleFiniteMeasure_mFourier
      uniform01Measure N (Real.log (N : ℝ))
      (flattenedAnnularSignedLower ε A e)
      (flattenedAnnularSignedUpper ε A e)
      (fun j ↦ mode (e₀.symm (e j)))
      (canonicalAnnularGridTupleFamily N k e)
  · intro e _he
    exact Integrable.of_bound
      (Continuous.aestronglyMeasurable
        (UnitAddTorus.mFourier mode).continuous)
      1 (Eventually.of_forall fun z ↦ by
        have hz := (UnitAddTorus.mFourier mode).norm_coe_le_norm z
        simpa only [UnitAddTorus.mFourier_norm] using! hz)

/-- For an actual labeled mixed Fourier assignment, the exact coefficient
of the reindexed aggregate is the sum of the chronological coefficients
with modes `flattenedAnnularFourierMode e h`. -/
theorem
    integral_reindexedAnnularUniformMarkedTupleFiniteMeasure_flattened
    {ε A : ℝ} {grid : ℕ}
    (N : ℕ) (k : AnnularGridIndex grid → ℕ)
    (e₀ : Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k)
    (h : ∀ i, Fin (k i) → ℤ) :
    (∫ z, UnitAddTorus.mFourier
        (flattenedAnnularFourierMode e₀ h) z
      ∂(reindexedAnnularUniformMarkedTupleFiniteMeasure
        (ε := ε) (A := A) N k e₀ :
          Measure (UnitAddTorus (Fin (MixedOccurrenceCount k))))) =
      ∑ e : Fin (MixedOccurrenceCount k) ≃
          GaussPrefixMixedOccurrence k,
        uniformMovingSignedMarkedFourierTupleSum
          N (Real.log (N : ℝ))
          (flattenedAnnularSignedLower ε A e)
          (flattenedAnnularSignedUpper ε A e)
          (flattenedAnnularFourierMode e h)
          (canonicalAnnularGridTupleFamily N k e) := by
  rw [integral_reindexedAnnularUniformMarkedTupleFiniteMeasure_mFourier]
  unfold reindexedAnnularUniformMarkedFourierTupleSum
  apply Finset.sum_congr rfl
  intro e _he
  congr 2
  funext j
  have he :
      e₀ (e₀.symm (e j)) = e j :=
    e₀.apply_symm_apply (e j)
  simp only [flattenedAnnularFourierMode]
  rw [he]

/-! ## Exact mass and the faithful Fourier closure -/

/-- The total mass is unchanged by the order-dependent coordinate
permutations and is exactly the already studied aggregate unmarked mass. -/
theorem reindexedAnnularUniformMarkedTupleFiniteMeasure_real_mass
    {ε A : ℝ} {grid : ℕ}
    (N : ℕ) (k : AnnularGridIndex grid → ℕ)
    (e₀ : Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) :
    ((reindexedAnnularUniformMarkedTupleFiniteMeasure
        (ε := ε) (A := A) N k e₀).mass : ℝ) =
      aggregateUniformMovingSignedApproximationTupleMassSum
        (β := Fin (MixedOccurrenceCount k) ≃
          GaussPrefixMixedOccurrence k)
        (Real.log (N : ℝ))
        (fun e ↦ flattenedAnnularSignedLower ε A e)
        (fun e ↦ flattenedAnnularSignedUpper ε A e)
        (fun e ↦ canonicalAnnularGridTupleFamily N k e) := by
  apply Complex.ofReal_injective
  calc
    ((((reindexedAnnularUniformMarkedTupleFiniteMeasure
          (ε := ε) (A := A) N k e₀).mass : NNReal) : ℝ) : ℂ) =
        ∫ z, UnitAddTorus.mFourier
          (fun _ : Fin (MixedOccurrenceCount k) ↦ 0) z
          ∂(reindexedAnnularUniformMarkedTupleFiniteMeasure
            (ε := ε) (A := A) N k e₀ :
              Measure (UnitAddTorus
                (Fin (MixedOccurrenceCount k)))) :=
      (integral_unitAddTorus_mFourier_zero_finiteMeasure
        (reindexedAnnularUniformMarkedTupleFiniteMeasure
          (ε := ε) (A := A) N k e₀)).symm
    _ = reindexedAnnularUniformMarkedFourierTupleSum
          (ε := ε) (A := A) N k e₀
          (fun _ : Fin (MixedOccurrenceCount k) ↦ 0) :=
      integral_reindexedAnnularUniformMarkedTupleFiniteMeasure_mFourier
        N k e₀ (fun _ : Fin (MixedOccurrenceCount k) ↦ 0)
    _ = (aggregateUniformMovingSignedApproximationTupleMassSum
          (β := Fin (MixedOccurrenceCount k) ≃
            GaussPrefixMixedOccurrence k)
          (Real.log (N : ℝ))
          (fun e ↦ flattenedAnnularSignedLower ε A e)
          (fun e ↦ flattenedAnnularSignedUpper ε A e)
          (fun e ↦ canonicalAnnularGridTupleFamily N k e) : ℂ) := by
      unfold reindexedAnnularUniformMarkedFourierTupleSum
        aggregateUniformMovingSignedApproximationTupleMassSum
        aggregateMovingSignedApproximationTupleMassSum
        uniformMovingSignedMarkedFourierTupleSum
      simp only [movingSignedMarkedFourierTupleSum_zero,
        Complex.ofReal_sum]

/-- A nonzero reference-coordinate mode remains nonzero after pullback
through any order tag. -/
theorem annularOrderPulledMode_ne_zero
    {ι : Type*} [Fintype ι] {k : ι → ℕ}
    (e₀ e : Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k)
    (mode : Fin (MixedOccurrenceCount k) → ℤ)
    (hmode : mode ≠ 0) :
    (fun j ↦ mode (e₀.symm (e j))) ≠ 0 := by
  intro hzero
  apply hmode
  funext j
  have hj := congrFun hzero (e.symm (e₀ j))
  simpa using! hj

/-- Tagwise nonzero Fourier cancellation implies cancellation of the
faithfully reindexed aggregate.  This finite-sum step keeps the
tag-dependent pulled modes explicit. -/
theorem
    tendsto_reindexedAnnularUniformMarkedFourierTupleSum_zero_of_tagwise
    {ε A : ℝ} {grid : ℕ}
    (k : AnnularGridIndex grid → ℕ)
    (e₀ : Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k)
    (mode : Fin (MixedOccurrenceCount k) → ℤ)
    (hmode : mode ≠ 0)
    (htag :
      ∀ e : Fin (MixedOccurrenceCount k) ≃
          GaussPrefixMixedOccurrence k,
        ∀ tagMode : Fin (MixedOccurrenceCount k) → ℤ,
          tagMode ≠ 0 →
            Tendsto
              (fun N : ℕ ↦
                uniformMovingSignedMarkedFourierTupleSum
                  N (Real.log (N : ℝ))
                  (flattenedAnnularSignedLower ε A e)
                  (flattenedAnnularSignedUpper ε A e)
                  tagMode
                  (canonicalAnnularGridTupleFamily N k e))
              atTop (nhds 0)) :
    Tendsto
      (fun N : ℕ ↦
        reindexedAnnularUniformMarkedFourierTupleSum
          (ε := ε) (A := A) N k e₀ mode)
      atTop (nhds 0) := by
  simpa only [reindexedAnnularUniformMarkedFourierTupleSum,
    Finset.sum_const_zero] using!
    tendsto_finset_sum Finset.univ (fun e _he ↦
      htag e (fun j ↦ mode (e₀.symm (e j)))
        (annularOrderPulledMode_ne_zero e₀ e mode hmode))

/-- Correct Fourier-to-Haar closure for the annular canonical families.
Unlike an unreindexed tagged sum, its nonzero hypothesis is exactly a
fixed labeled Fourier mode pulled through every chronological tag. -/
theorem
    tendsto_reindexedAnnularUniformMarkedTupleFiniteMeasure_of_nonzero
    {ε A : ℝ} (hε : 0 < ε) (hεA : ε < A)
    {grid : ℕ} (hgrid : 0 < grid)
    (k : AnnularGridIndex grid → ℕ)
    (hr : 0 < MixedOccurrenceCount k)
    (htimePositive : ∀ i, 0 < k i → 0 < i.time.1)
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
      (tendsto_annularCanonicalUniformZeroMode
        hε hεA hgrid k hr htimePositive htime hsigned).congr'
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

end

end Erdos1002
