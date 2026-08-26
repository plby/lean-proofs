import ErdosProblems.Erdos1002.GaussPrefixAnnularTaggedMarkedMeasure
import ErdosProblems.Erdos1002.GaussPrefixAnnularBoundaryCells

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Exact canonical annular box evaluation

The reindexed annular marked measure is a finite sum of pushforwards, one
for each chronological occurrence order.  This file evaluates that measure
on the literal labeled torus box.  The result is an exact finite sum of
uniform-Lebesgue masses of the canonical signed tuple events intersected
with their labeled torus-cell events.

No limit, endpoint replacement, or boundary estimate is used here.
-/

open MeasureTheory Set Finset
open scoped BigOperators

namespace Erdos1002

noncomputable section

local instance gaussPrefixAnnularCanonicalBoxBridgePropDecidable
    (P : Prop) : Decidable P := Classical.propDecidable P

/-! ## Measurability of the genuine grid arcs and boxes -/

/-- A nonterminal interval-grid arc in the quotient circle is Borel.
The one-cell grid is treated separately because its unique nonterminal
arc is the whole circle rather than an arc of length strictly below one. -/
theorem measurableSet_unitAddCircle_intervalGridArc_of_nonterminal
    {grid : ℕ} (hgrid : 0 < grid)
    (i : IntervalGridIndex grid) (hi : i.1 < grid) :
    MeasurableSet
      (unitAddCircleHalfOpenArc
        (intervalGridPoint 0 1 grid i.1)
        (intervalGridPoint 0 1 grid (i.1 + 1))) := by
  by_cases hgridOne : grid = 1
  · subst grid
    have hiZero : i.1 = 0 := by omega
    have harc :
        unitAddCircleHalfOpenArc
            (intervalGridPoint 0 1 1 i.1)
            (intervalGridPoint 0 1 1 (i.1 + 1)) =
          (Set.univ : Set UnitAddCircle) := by
      rw [hiZero]
      simpa [intervalGridPoint, unitAddCircleHalfOpenArc] using!
        (AddCircle.coe_image_Ico_eq (p := (1 : ℝ)) (a := (0 : ℝ)))
    rw [harc]
    exact MeasurableSet.univ
  · have hgridTwo : 2 ≤ grid := by omega
    have hstep :=
      intervalGridPoint_strictMono_step
        (a := (0 : ℝ)) (b := 1) zero_lt_one hgrid
        (k := i.1)
    have hgridReal : (0 : ℝ) < (grid : ℝ) := by
      exact_mod_cast hgrid
    have hgridTwoReal : (2 : ℝ) ≤ (grid : ℝ) := by
      exact_mod_cast hgridTwo
    have hwidth :
        intervalGridPoint 0 1 grid (i.1 + 1) <
          intervalGridPoint 0 1 grid i.1 + 1 := by
      unfold intervalGridPoint
      norm_num
      rw [div_lt_iff₀ hgridReal, add_mul,
        div_mul_cancel₀ _ hgridReal.ne', one_mul]
      nlinarith [hgridTwoReal]
    exact measurableSet_unitAddCircleHalfOpenArc_of_lt_one
      hstep hwidth

/-- Under the active-cell nonterminal hypothesis, every coordinate arc
of a flattened annular torus box is Borel, hence so is the finite product
box. -/
theorem measurableSet_flattenedAnnularTorusBox
    {grid : ℕ} (hgrid : 0 < grid)
    {k : AnnularGridIndex grid → ℕ}
    (htorus : ∀ i : AnnularGridIndex grid,
      0 < k i → i.torus.1 < grid)
    (e : Fin (MixedOccurrenceCount k) ≃
      GaussPrefixMixedOccurrence k) :
    MeasurableSet
      (unitTorusHalfOpenBox
        (flattenedAnnularTorusLower e)
        (flattenedAnnularTorusUpper e)) := by
  unfold unitTorusHalfOpenBox
  apply MeasurableSet.iInter
  intro j
  apply MeasurableSet.preimage
  · have hactive : 0 < k (e j).1 := by
      have hj := (e j).2.isLt
      omega
    simpa only [flattenedAnnularTorusLower,
      flattenedAnnularTorusUpper] using!
      measurableSet_unitAddCircle_intervalGridArc_of_nonterminal
        hgrid (e j).1.torus (htorus (e j).1 hactive)
  · exact measurable_pi_apply j

/-! ## Exact reindexing of the labeled torus box -/

/-- Pulling the reference-order labeled box back through the
order-reindexing map gives the same labeled box in chronological
coordinates. -/
theorem annularOrderReindex_preimage_flattenedAnnularTorusBox
    {grid : ℕ} {k : AnnularGridIndex grid → ℕ}
    (e₀ e : Fin (MixedOccurrenceCount k) ≃
      GaussPrefixMixedOccurrence k) :
    annularOrderReindex e₀ e ⁻¹'
        unitTorusHalfOpenBox
          (flattenedAnnularTorusLower e₀)
          (flattenedAnnularTorusUpper e₀) =
      unitTorusHalfOpenBox
        (flattenedAnnularTorusLower e)
        (flattenedAnnularTorusUpper e) := by
  ext z
  simp only [unitTorusHalfOpenBox, Set.mem_preimage,
    Set.mem_iInter, annularOrderReindex]
  constructor
  · intro hz j
    have h :=
      hz (e₀.symm (e j))
    simpa only [e₀.apply_symm_apply, e.symm_apply_apply,
      flattenedAnnularTorusLower,
      flattenedAnnularTorusUpper] using! h
  · intro hz j
    have h :=
      hz (e.symm (e₀ j))
    simpa only [e.apply_symm_apply, e₀.symm_apply_apply,
      flattenedAnnularTorusLower,
      flattenedAnnularTorusUpper] using! h

/-! ## Literal canonical signed-and-torus event -/

/-- For one chronological order and one canonical depth tuple, this is
the exact event imposing both the signed approximation windows and the
labeled quotient-torus grid cells. -/
def canonicalAnnularSignedTorusTupleEvent
    (ε A : ℝ) (N : ℕ) {grid : ℕ}
    {k : AnnularGridIndex grid → ℕ}
    (e : Fin (MixedOccurrenceCount k) ≃
      GaussPrefixMixedOccurrence k)
    (times : Fin (MixedOccurrenceCount k) → ℕ) : Set ℝ :=
  (gaussMovingUnitTorusPoint N times) ⁻¹'
      unitTorusHalfOpenBox
        (flattenedAnnularTorusLower e)
        (flattenedAnnularTorusUpper e) ∩
    gaussSignedApproximationTupleEvent
      (Real.log (N : ℝ))
      (flattenedAnnularSignedLower ε A e)
      (flattenedAnnularSignedUpper ε A e)
      times

/-- Membership in the preceding event is literally the signed tuple event
together with every chronological coordinate lying in the torus cell
attached to its labeled occurrence. -/
theorem mem_canonicalAnnularSignedTorusTupleEvent_iff
    {ε A : ℝ} {N grid : ℕ}
    {k : AnnularGridIndex grid → ℕ}
    (e : Fin (MixedOccurrenceCount k) ≃
      GaussPrefixMixedOccurrence k)
    (times : Fin (MixedOccurrenceCount k) → ℕ)
    (x : ℝ) :
    x ∈ canonicalAnnularSignedTorusTupleEvent ε A N e times ↔
      x ∈ gaussSignedApproximationTupleEvent
        (Real.log (N : ℝ))
        (flattenedAnnularSignedLower ε A e)
        (flattenedAnnularSignedUpper ε A e)
        times ∧
      ∀ j : Fin (MixedOccurrenceCount k),
        (gaussSelectedPrefixTorusMark N (times j) x :
            UnitAddCircle) ∈
          unitAddCircleHalfOpenArc
            (intervalGridPoint 0 1 grid (e j).1.torus.1)
            (intervalGridPoint 0 1 grid ((e j).1.torus.1 + 1)) := by
  simp only [canonicalAnnularSignedTorusTupleEvent, Set.mem_inter_iff,
    Set.mem_preimage, unitTorusHalfOpenBox, Set.mem_iInter,
    gaussMovingUnitTorusPoint, flattenedAnnularTorusLower,
    flattenedAnnularTorusUpper]
  tauto

/-- The canonical signed-and-torus tuple event is measurable whenever all
actively labeled torus cells are nonterminal. -/
theorem measurableSet_canonicalAnnularSignedTorusTupleEvent
    {ε A : ℝ} {N grid : ℕ} (hgrid : 0 < grid)
    {k : AnnularGridIndex grid → ℕ}
    (htorus : ∀ i : AnnularGridIndex grid,
      0 < k i → i.torus.1 < grid)
    (e : Fin (MixedOccurrenceCount k) ≃
      GaussPrefixMixedOccurrence k)
    (times : Fin (MixedOccurrenceCount k) → ℕ) :
    MeasurableSet
      (canonicalAnnularSignedTorusTupleEvent ε A N e times) := by
  apply MeasurableSet.inter
  · exact
      (measurableSet_flattenedAnnularTorusBox hgrid htorus e).preimage
        (measurable_gaussMovingUnitTorusPoint N times)
  · exact measurableSet_gaussSignedApproximationTupleEvent
      (Real.log (N : ℝ))
      (flattenedAnnularSignedLower ε A e)
      (flattenedAnnularSignedUpper ε A e)
      times

/-! ## Exact finite box formula -/

/-- Exact evaluation of the reindexed canonical marked measure on its
literal labeled half-open torus box.

Each chronological tag contributes the canonical depth tuples belonging
to that tag.  For each such tuple, the summand is precisely the
uniform-Lebesgue mass of the simultaneous signed-window and labeled
torus-cell event. -/
theorem
    reindexedAnnularUniformMarkedTupleFiniteMeasure_real_flattenedTorusBox
    {ε A : ℝ} {grid : ℕ} (hgrid : 0 < grid)
    (N : ℕ) (k : AnnularGridIndex grid → ℕ)
    (htorus : ∀ i : AnnularGridIndex grid,
      0 < k i → i.torus.1 < grid)
    (e₀ : Fin (MixedOccurrenceCount k) ≃
      GaussPrefixMixedOccurrence k) :
    (reindexedAnnularUniformMarkedTupleFiniteMeasure
        (ε := ε) (A := A) N k e₀ :
      Measure (UnitAddTorus (Fin (MixedOccurrenceCount k)))).real
        (unitTorusHalfOpenBox
          (flattenedAnnularTorusLower e₀)
          (flattenedAnnularTorusUpper e₀)) =
      ∑ e : Fin (MixedOccurrenceCount k) ≃
          GaussPrefixMixedOccurrence k,
        ∑ times ∈ canonicalAnnularGridTupleFamily N k e,
          uniform01Measure.real
            (canonicalAnnularSignedTorusTupleEvent ε A N e times) := by
  classical
  let S : Set (UnitAddTorus (Fin (MixedOccurrenceCount k))) :=
    unitTorusHalfOpenBox
      (flattenedAnnularTorusLower e₀)
      (flattenedAnnularTorusUpper e₀)
  have hS : MeasurableSet S :=
    measurableSet_flattenedAnnularTorusBox hgrid htorus e₀
  unfold reindexedAnnularUniformMarkedTupleFiniteMeasure
  rw [measureReal_def, FiniteMeasure.toMeasure_sum,
    Measure.coe_finset_sum, Finset.sum_apply, ENNReal.toReal_sum]
  apply Finset.sum_congr rfl
  intro e _he
  rw [FiniteMeasure.toMeasure_map,
    Measure.map_apply (measurable_annularOrderReindex e₀ e) hS,
    annularOrderReindex_preimage_flattenedAnnularTorusBox e₀ e]
  unfold movingSignedMarkedTupleFiniteMeasure
  rw [FiniteMeasure.toMeasure_sum,
    Measure.coe_finset_sum, Finset.sum_apply, ENNReal.toReal_sum]
  apply Finset.sum_congr rfl
  intro times _htimes
  rw [FiniteMeasure.toMeasure_map,
    Measure.map_apply
      (measurable_gaussMovingUnitTorusPoint N times)
      (measurableSet_flattenedAnnularTorusBox hgrid htorus e)]
  rw [FiniteMeasure.restrict_measure_eq,
    Measure.restrict_apply
      ((measurableSet_flattenedAnnularTorusBox hgrid htorus e).preimage
        (measurable_gaussMovingUnitTorusPoint N times))]
  rfl
  all_goals
    intro a _ha
    exact measure_ne_top _ _

end

end Erdos1002
