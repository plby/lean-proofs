import ErdosProblems.Erdos1002.GaussPrefixMixedChronology

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Literal prefix characters on one continued-fraction cylinder

This file supplies the local geometric step used in the late case of the
marked Fourier argument.  At a deterministic split depth `m`, only the
occurrences no later than `m` belong to the prefix.  Their literal compact
marked events are converted, on one exact depth-`m` cylinder, into finitely
many affine value constraints.  Up to the terminating endpoint null set,
their intersection is empty or one closed interval.  The literal prefix
character consequently has exactly one fixed oscillatory carrier on that
interval.
-/

open Filter MeasureTheory Set
open scoped BigOperators Topology

namespace Erdos1002

noncomputable section

local instance gaussPrefixMarkedPrefixCylinderPropDecidable (P : Prop) :
    Decidable P := Classical.propDecidable P

variable {ι : Type*} [Fintype ι]

/-- Occurrences retained by the prefix at the deterministic split `m`. -/
def GaussPrefixMixedPrefixOccurrence
    (N : ℕ) (k : ι → ℕ) (F : GaussPrefixMixedDepthTuple N k)
    (m : ℕ) : Type _ :=
  {z : GaussPrefixMixedOccurrence k // (F z.1 z.2 : ℕ) ≤ m}

instance instFintypeGaussPrefixMixedPrefixOccurrence
    (N : ℕ) (k : ι → ℕ) (F : GaussPrefixMixedDepthTuple N k)
    (m : ℕ) : Fintype (GaussPrefixMixedPrefixOccurrence N k F m) :=
  Fintype.ofFinset
    ((Finset.univ : Finset (GaussPrefixMixedOccurrence k)).filter
      (fun z ↦ (F z.1 z.2 : ℕ) ≤ m)) (by
        intro z
        change
          z ∈ ((Finset.univ : Finset (GaussPrefixMixedOccurrence k)).filter
            (fun z ↦ (F z.1 z.2 : ℕ) ≤ m)) ↔
              (F z.1 z.2 : ℕ) ≤ m
        simp)

/-- The selected earlier positive word, expressed only in terms of the
deepest cylinder word. -/
def exactDepthCylinderPrefixOccurrenceWord
    (N : ℕ) (k : ι → ℕ) (F : GaussPrefixMixedDepthTuple N k)
    {m : ℕ} (w : ExactDepthBoundedPositiveWord N m)
    (z : GaussPrefixMixedPrefixOccurrence N k F m) :
    PositiveDigitWord (F z.1.1 z.1.2 : ℕ) :=
  positiveDigitWordTake (F z.1.1 z.1.2 : ℕ) z.2 w.toPositive

/-- Closed-cylinder intersection with the affine signed-value constraints
of precisely the retained prefix occurrences. -/
def exactDepthMixedPrefixValueWindowIntersection
    (N : ℕ) (k : ι → ℕ) (F : GaussPrefixMixedDepthTuple N k)
    {m : ℕ} (w : ExactDepthBoundedPositiveWord N m)
    (lower upper : ∀ i, Fin (k i) → ℝ) : Set ℝ :=
  finiteAffineWindowIntersection
    (closedGaussPrefixCylinderLeft w.1.1)
    (closedGaussPrefixCylinderRight w.1.1)
    (fun z : GaussPrefixMixedPrefixOccurrence N k F m ↦
      lower z.1.1 z.1.2)
    (fun z : GaussPrefixMixedPrefixOccurrence N k F m ↦
      upper z.1.1 z.1.2)
    (fun z : GaussPrefixMixedPrefixOccurrence N k F m ↦
      gaussPrefixMarkedValueSlope N
        (exactDepthCylinderPrefixOccurrenceWord N k F w z))
    (fun z : GaussPrefixMixedPrefixOccurrence N k F m ↦
      gaussPrefixMarkedValueIntercept N
        (exactDepthCylinderPrefixOccurrenceWord N k F w z))

/-- The complete affine prefix constraint in one deepest cylinder is empty
or a single closed interval. -/
theorem exactDepthMixedPrefixValueWindowIntersection_eq_empty_or_Icc
    (N : ℕ) (k : ι → ℕ) (F : GaussPrefixMixedDepthTuple N k)
    {m : ℕ} (w : ExactDepthBoundedPositiveWord N m)
    (lower upper : ∀ i, Fin (k i) → ℝ) :
    exactDepthMixedPrefixValueWindowIntersection N k F w lower upper = ∅ ∨
      ∃ left right : ℝ, left ≤ right ∧
        exactDepthMixedPrefixValueWindowIntersection N k F w lower upper =
          Icc left right := by
  unfold exactDepthMixedPrefixValueWindowIntersection
  exact finiteAffineWindowIntersection_eq_empty_or_Icc
    (closedGaussPrefixCylinderLeft w.1.1)
    (closedGaussPrefixCylinderRight w.1.1)
    (fun z : GaussPrefixMixedPrefixOccurrence N k F m ↦
      lower z.1.1 z.1.2)
    (fun z : GaussPrefixMixedPrefixOccurrence N k F m ↦
      upper z.1.1 z.1.2)
    (fun z : GaussPrefixMixedPrefixOccurrence N k F m ↦
      gaussPrefixMarkedValueSlope N
        (exactDepthCylinderPrefixOccurrenceWord N k F w z))
    (fun z : GaussPrefixMixedPrefixOccurrence N k F m ↦
      gaussPrefixMarkedValueIntercept N
        (exactDepthCylinderPrefixOccurrenceWord N k F w z))

/-- The same prefix constraints written with the actual selected Gauss
prefix points and the actual half-open deepest cylinder. -/
def exactDepthActualMixedPrefixValueWindowSet
    (N : ℕ) (k : ι → ℕ) (F : GaussPrefixMixedDepthTuple N k)
    {m : ℕ} (w : ExactDepthBoundedPositiveWord N m)
    (lower upper : ∀ i, Fin (k i) → ℝ) : Set ℝ :=
  exactDepthBoundedCylinder w ∩
    ⋂ z : GaussPrefixMixedPrefixOccurrence N k F m,
      {x | (gaussPrefixMarkedPoint N (F z.1.1 z.1.2)
        (selectedGaussPrefixWord (F z.1.1 z.1.2) x) x).2.1 ∈
          Icc (lower z.1.1 z.1.2) (upper z.1.1 z.1.2)}

/-- On a nonterminating point of the deepest half-open cylinder, actual
selected-prefix constraints are equivalent to the explicit affine ones. -/
theorem mem_exactDepthMixedPrefixValueWindowIntersection_iff
    (N : ℕ) (k : ι → ℕ) (F : GaussPrefixMixedDepthTuple N k)
    {m : ℕ} (w : ExactDepthBoundedPositiveWord N m)
    (lower upper : ∀ i, Fin (k i) → ℝ)
    {x : ℝ} (hxUnit : x ∈ Ioo (0 : ℝ) 1)
    (hxNonterm : ∀ r : ℕ, (gaussMap^[r]) x ≠ 0)
    (hx : x ∈ exactDepthBoundedCylinder w) :
    x ∈ exactDepthMixedPrefixValueWindowIntersection
        N k F w lower upper ↔
      ∀ z : GaussPrefixMixedPrefixOccurrence N k F m,
        (gaussPrefixMarkedPoint N (F z.1.1 z.1.2)
          (selectedGaussPrefixWord (F z.1.1 z.1.2) x) x).2.1 ∈
            Icc (lower z.1.1 z.1.2) (upper z.1.1 z.1.2) := by
  have hxClosed : x ∈ closedGaussPrefixCylinder w.1.1 :=
    gaussHalfOpenPrefixCylinder_subset_closed w.1.2.2.1 hx
  have hxBounds : x ∈ Icc (closedGaussPrefixCylinderLeft w.1.1)
      (closedGaussPrefixCylinderRight w.1.1) := by
    rw [← closedGaussPrefixCylinder_eq_Icc w.1.2.2.1]
    exact hxClosed
  constructor
  · intro hinter z
    have hall := Set.mem_iInter.mp hinter.2 z
    change
      gaussPrefixMarkedValueSlope N
          (exactDepthCylinderPrefixOccurrenceWord N k F w z) * x +
        gaussPrefixMarkedValueIntercept N
          (exactDepthCylinderPrefixOccurrenceWord N k F w z) ∈
        Icc (lower z.1.1 z.1.2) (upper z.1.1 z.1.2) at hall
    have hvalue :=
      selectedGaussPrefixMarkedPoint_value_eq_affine_on_deeperCylinder
        (N := N) z.2 w.toPositive hxUnit hxNonterm hx
    simpa only [exactDepthCylinderPrefixOccurrenceWord] using!
      hvalue.symm ▸ hall
  · intro hall
    refine ⟨hxBounds, Set.mem_iInter.mpr ?_⟩
    intro z
    have hvalue :=
      selectedGaussPrefixMarkedPoint_value_eq_affine_on_deeperCylinder
        (N := N) z.2 w.toPositive hxUnit hxNonterm hx
    change
      gaussPrefixMarkedValueSlope N
          (exactDepthCylinderPrefixOccurrenceWord N k F w z) * x +
        gaussPrefixMarkedValueIntercept N
          (exactDepthCylinderPrefixOccurrenceWord N k F w z) ∈
        Icc (lower z.1.1 z.1.2) (upper z.1.1 z.1.2)
    simpa only [exactDepthCylinderPrefixOccurrenceWord] using!
      hvalue ▸ hall z

/-- Endpoint choices and terminating continued fractions do not change the
prefix value-window set under the uniform Lebesgue law. -/
theorem exactDepthActualMixedPrefixValueWindowSet_ae_eq_affine
    (N : ℕ) (k : ι → ℕ) (F : GaussPrefixMixedDepthTuple N k)
    {m : ℕ} (w : ExactDepthBoundedPositiveWord N m)
    (lower upper : ∀ i, Fin (k i) → ℝ) :
    exactDepthActualMixedPrefixValueWindowSet N k F w lower upper
        =ᵐ[uniform01Measure]
      exactDepthMixedPrefixValueWindowIntersection N k F w lower upper := by
  have hcell := exactDepthBoundedCylinder_ae_eq_closed w
  filter_upwards [hcell, ae_nonterminating_uniform01] with x hcellx hxgood
  apply propext
  change
    (x ∈ exactDepthActualMixedPrefixValueWindowSet N k F w lower upper) ↔
      x ∈ exactDepthMixedPrefixValueWindowIntersection N k F w lower upper
  unfold exactDepthActualMixedPrefixValueWindowSet
  simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hxCell, hall⟩
    apply (mem_exactDepthMixedPrefixValueWindowIntersection_iff
      N k F w lower upper hxgood.1 hxgood.2 hxCell).2
    exact hall
  · intro hinter
    have hxBounds := hinter.1
    have hxClosed : x ∈ closedGaussPrefixCylinder w.1.1 := by
      rw [closedGaussPrefixCylinder_eq_Icc w.1.2.2.1]
      exact hxBounds
    have hxCell : x ∈ exactDepthBoundedCylinder w := by
      exact hcellx.symm.mp hxClosed
    refine ⟨hxCell, ?_⟩
    exact (mem_exactDepthMixedPrefixValueWindowIntersection_iff
      N k F w lower upper hxgood.1 hxgood.2 hxCell).1 hinter

/-- Therefore the actual prefix window set is almost everywhere empty or
one closed interval. -/
theorem exactDepthActualMixedPrefixValueWindowSet_ae_eq_empty_or_Icc
    (N : ℕ) (k : ι → ℕ) (F : GaussPrefixMixedDepthTuple N k)
    {m : ℕ} (w : ExactDepthBoundedPositiveWord N m)
    (lower upper : ∀ i, Fin (k i) → ℝ) :
    exactDepthActualMixedPrefixValueWindowSet N k F w lower upper
        =ᵐ[uniform01Measure] (∅ : Set ℝ) ∨
      ∃ left right : ℝ, left ≤ right ∧
        exactDepthActualMixedPrefixValueWindowSet N k F w lower upper
          =ᵐ[uniform01Measure] Icc left right := by
  have hae := exactDepthActualMixedPrefixValueWindowSet_ae_eq_affine
    N k F w lower upper
  rcases exactDepthMixedPrefixValueWindowIntersection_eq_empty_or_Icc
      N k F w lower upper with hempty | ⟨left, right, hlr, heq⟩
  · left
    simpa only [hempty] using! hae
  · right
    refine ⟨left, right, hlr, ?_⟩
    simpa only [heq] using! hae

/-- Every actual prefix value-window integral on one deepest cylinder is
exactly one ordinary interval integral. -/
theorem exists_intervalIntegral_eq_setIntegral_actualMixedPrefixValueWindows
    (N : ℕ) (k : ι → ℕ) (F : GaussPrefixMixedDepthTuple N k)
    {m : ℕ} (w : ExactDepthBoundedPositiveWord N m)
    (lower upper : ∀ i, Fin (k i) → ℝ) (K : ℝ) :
    ∃ left right : ℝ, left ≤ right ∧
      (∫ x in exactDepthActualMixedPrefixValueWindowSet
          N k F w lower upper,
        oscillatoryPhase K x ∂uniform01Measure) =
        ∫ x in left..right, oscillatoryPhase K x := by
  have hae := exactDepthActualMixedPrefixValueWindowSet_ae_eq_affine
    N k F w lower upper
  rcases exactDepthMixedPrefixValueWindowIntersection_eq_empty_or_Icc
      N k F w lower upper with hempty | ⟨left, right, hlr, heq⟩
  · refine ⟨0, 0, le_rfl, ?_⟩
    have haeEmpty :
        exactDepthActualMixedPrefixValueWindowSet N k F w lower upper
          =ᵐ[uniform01Measure] (∅ : Set ℝ) := by
      simpa only [hempty] using! hae
    change
      (∫ x, oscillatoryPhase K x
        ∂uniform01Measure.restrict
          (exactDepthActualMixedPrefixValueWindowSet
            N k F w lower upper)) =
        ∫ x in (0 : ℝ)..0, oscillatoryPhase K x
    rw [Measure.restrict_congr_set haeEmpty]
    simp
  · have haeIcc :
        exactDepthActualMixedPrefixValueWindowSet N k F w lower upper
          =ᵐ[uniform01Measure] Icc left right := by
      simpa only [heq] using! hae
    have hsub : Icc left right ⊆ Icc (0 : ℝ) 1 := by
      rw [← heq]
      intro x hx
      have hxClosed : x ∈ closedGaussPrefixCylinder w.1.1 := by
        rw [closedGaussPrefixCylinder_eq_Icc w.1.2.2.1]
        exact hx.1
      exact closedGaussPrefixCylinder_subset_unit w.1.2.2.1 hxClosed
    refine ⟨left, right, hlr, ?_⟩
    calc
      (∫ x in exactDepthActualMixedPrefixValueWindowSet
          N k F w lower upper,
          oscillatoryPhase K x ∂uniform01Measure) =
          ∫ x in Icc left right,
            oscillatoryPhase K x ∂uniform01Measure := by
        rw [Measure.restrict_congr_set haeIcc]
      _ = ∫ x in left..right, oscillatoryPhase K x :=
        setIntegral_uniform01_Icc_eq_intervalIntegral hlr hsub
          (oscillatoryPhase K)

/-! ## The literal prefix character on its simultaneous prefix event -/

/-- Simultaneous literal marked event for exactly the occurrences retained
at the prefix split, restricted to one exact-depth cylinder. -/
def exactDepthMixedPrefixTupleEventSet
    (N : ℕ) (B : ι → Set (ℝ × ℝ × ℝ)) (k : ι → ℕ)
    (F : GaussPrefixMixedDepthTuple N k) {m : ℕ}
    (w : ExactDepthBoundedPositiveWord N m) : Set ℝ :=
  exactDepthBoundedCylinder w ∩
    ⋂ z : GaussPrefixMixedPrefixOccurrence N k F m,
      gaussPrefixMarkedEvent N (B z.1.1) (F z.1.1 z.1.2)

theorem measurableSet_exactDepthMixedPrefixTupleEventSet
    (N : ℕ) {B : ι → Set (ℝ × ℝ × ℝ)}
    (hB : ∀ i, MeasurableSet (B i)) (k : ι → ℕ)
    (F : GaussPrefixMixedDepthTuple N k) {m : ℕ}
    (w : ExactDepthBoundedPositiveWord N m) :
    MeasurableSet (exactDepthMixedPrefixTupleEventSet N B k F w) := by
  apply (measurableSet_exactDepthBoundedCylinder w).inter
  apply MeasurableSet.iInter
  intro z
  exact measurableSet_gaussPrefixMarkedEvent N (F z.1.1 z.1.2) (hB z.1.1)

omit [Fintype ι] in
/-- For the paper's compact signed-value windows, the literal prefix event
inside a deepest cylinder is almost everywhere exactly the actual
selected-prefix value-window set. -/
theorem exactDepthMixedPrefixTupleEventSet_compactValue_ae_eq_valueWindows
    (N : ℕ) (hN : 2 ≤ N) (k : ι → ℕ)
    (F : GaussPrefixMixedDepthTuple N k) {m : ℕ}
    (w : ExactDepthBoundedPositiveWord N m)
    (lower upper : ι → ℝ) {A : ℝ}
    (hlower : ∀ i, |lower i| ≤ A)
    (hupper : ∀ i, |upper i| ≤ A)
    (hsmall : A / Real.log (N : ℝ) < (1 : ℝ) / 2) :
    exactDepthMixedPrefixTupleEventSet N
        (fun i ↦ compactValueMarkedRegion (lower i) (upper i)) k F w
        =ᵐ[uniform01Measure]
      exactDepthActualMixedPrefixValueWindowSet N k F w
        (fun i _j ↦ lower i) (fun i _j ↦ upper i) := by
  filter_upwards [ae_nonterminating_uniform01] with x hxgood
  apply propext
  change
    (x ∈ exactDepthMixedPrefixTupleEventSet N
        (fun i ↦ compactValueMarkedRegion (lower i) (upper i)) k F w) ↔
      x ∈ exactDepthActualMixedPrefixValueWindowSet N k F w
        (fun i _j ↦ lower i) (fun i _j ↦ upper i)
  constructor
  · intro hxEvent
    refine ⟨hxEvent.1, Set.mem_iInter.mpr ?_⟩
    intro z
    have hz := Set.mem_iInter.mp hxEvent.2 z
    exact (mem_gaussPrefixMarkedEvent_compactValue_iff_on_deeperCylinder
      hN z.2 w.toPositive (hlower z.1.1) (hupper z.1.1) hsmall
      w.1.2.2.2 hxgood.1 hxgood.2 hxEvent.1).1 hz
  · intro hxValue
    refine ⟨hxValue.1, Set.mem_iInter.mpr ?_⟩
    intro z
    have hz := Set.mem_iInter.mp hxValue.2 z
    exact (mem_gaussPrefixMarkedEvent_compactValue_iff_on_deeperCylinder
      hN z.2 w.toPositive (hlower z.1.1) (hupper z.1.1) hsmall
      w.1.2.2.2 hxgood.1 hxgood.2 hxValue.1).2 hz

/-- On one deepest cylinder, the literal prefix character is the indicator
of the simultaneous prefix event times the ordinary phase with the named
prefix carrier.  The identity is at the level of set integrals, so the
terminating continued-fraction null set is already removed. -/
theorem setIntegral_mixedPrefixCharacter_eq_fixedCarrier_on_event
    (N : ℕ) {B : ι → Set (ℝ × ℝ × ℝ)}
    (hB : ∀ i, MeasurableSet (B i)) (k : ι → ℕ)
    (h : ∀ i, Fin (k i) → ℤ)
    (F : GaussPrefixMixedDepthTuple N k) {m : ℕ}
    (w : ExactDepthBoundedPositiveWord N m) :
    (∫ x in exactDepthBoundedCylinder w,
        gaussPrefixMarkedMixedPrefixCharacter N B k h F m x
          ∂uniform01Measure) =
      ∫ x in exactDepthMixedPrefixTupleEventSet N B k F w,
        oscillatoryPhase
          ((N : ℝ) * exactDepthCylinderMixedPrefixCarrier N k h F w) x
            ∂uniform01Measure := by
  classical
  have hcellM := measurableSet_exactDepthBoundedCylinder w
  have heventM :=
    measurableSet_exactDepthMixedPrefixTupleEventSet N hB k F w
  rw [← integral_indicator hcellM, ← integral_indicator heventM]
  apply integral_congr_ae
  filter_upwards [ae_nonterminating_uniform01] with x hxgood
  by_cases hxCell : x ∈ exactDepthBoundedCylinder w
  · rw [Set.indicator_of_mem hxCell]
    by_cases hall : ∀ z : GaussPrefixMixedPrefixOccurrence N k F m,
        x ∈ gaussPrefixMarkedEvent N (B z.1.1) (F z.1.1 z.1.2)
    · have hxEvent : x ∈ exactDepthMixedPrefixTupleEventSet N B k F w :=
        ⟨hxCell, Set.mem_iInter.mpr hall⟩
      rw [Set.indicator_of_mem hxEvent]
      have hxEvents : ∀ z : GaussPrefixMixedOccurrence k,
          (F z.1 z.2 : ℕ) ≤ m →
            x ∈ gaussPrefixMarkedEvent N (B z.1) (F z.1 z.2) := by
        intro z hz
        exact hall ⟨z, hz⟩
      have hcharacter :=
        gaussPrefixMarkedMixedPrefixCharacter_eq_oscillatoryPhase
          (h := h) (F := F) hxgood.1 hxgood.2 hxEvents
      rw [hcharacter]
      have hcarrier :=
        gaussPrefixMarkedMixedPrefixCarrier_eq_exactDepthCylinder
          N k h F w ⟨hxgood.1.1.le, hxgood.1.2⟩ hxCell
      rw [hcarrier]
    · have hxNotEvent :
          x ∉ exactDepthMixedPrefixTupleEventSet N B k F w := by
        intro hxEvent
        exact hall (Set.mem_iInter.mp hxEvent.2)
      rw [Set.indicator_of_notMem hxNotEvent]
      push_neg at hall
      obtain ⟨z, hzNot⟩ := hall
      unfold gaussPrefixMarkedMixedPrefixCharacter
      apply Finset.prod_eq_zero
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ z.1, z.2⟩
      · unfold gaussPrefixMarkedDepthCharacter
        rw [if_neg hzNot]
  · rw [Set.indicator_of_notMem hxCell]
    have hxNotEvent :
        x ∉ exactDepthMixedPrefixTupleEventSet N B k F w := by
      exact fun hxEvent ↦ hxCell hxEvent.1
    rw [Set.indicator_of_notMem hxNotEvent]

/-- Complete late-case local reduction: on a deepest cylinder, the literal
compact-window prefix character is exactly one ordinary oscillatory
interval integral with the fixed prefix carrier. -/
theorem exists_intervalIntegral_eq_setIntegral_mixedPrefixCharacter_compactValue
    (N : ℕ) (hN : 2 ≤ N) (k : ι → ℕ)
    (h : ∀ i, Fin (k i) → ℤ)
    (F : GaussPrefixMixedDepthTuple N k) {m : ℕ}
    (w : ExactDepthBoundedPositiveWord N m)
    (lower upper : ι → ℝ) {A : ℝ}
    (hlower : ∀ i, |lower i| ≤ A)
    (hupper : ∀ i, |upper i| ≤ A)
    (hsmall : A / Real.log (N : ℝ) < (1 : ℝ) / 2) :
    ∃ left right : ℝ, left ≤ right ∧
      (∫ x in exactDepthBoundedCylinder w,
        gaussPrefixMarkedMixedPrefixCharacter N
          (fun i ↦ compactValueMarkedRegion (lower i) (upper i))
          k h F m x ∂uniform01Measure) =
        ∫ x in left..right,
          oscillatoryPhase
            ((N : ℝ) *
              exactDepthCylinderMixedPrefixCarrier N k h F w) x := by
  let B : ι → Set (ℝ × ℝ × ℝ) :=
    fun i ↦ compactValueMarkedRegion (lower i) (upper i)
  let lower' : ∀ i, Fin (k i) → ℝ := fun i _j ↦ lower i
  let upper' : ∀ i, Fin (k i) → ℝ := fun i _j ↦ upper i
  let K : ℝ :=
    (N : ℝ) * exactDepthCylinderMixedPrefixCarrier N k h F w
  have hfixed := setIntegral_mixedPrefixCharacter_eq_fixedCarrier_on_event
    N (fun i ↦ measurableSet_compactValueMarkedRegion (lower i) (upper i))
      k h F w
  have hae :=
    exactDepthMixedPrefixTupleEventSet_compactValue_ae_eq_valueWindows
      N hN k F w lower upper hlower hupper hsmall
  obtain ⟨left, right, hlr, hinterval⟩ :=
    exists_intervalIntegral_eq_setIntegral_actualMixedPrefixValueWindows
      N k F w lower' upper' K
  refine ⟨left, right, hlr, ?_⟩
  calc
    (∫ x in exactDepthBoundedCylinder w,
        gaussPrefixMarkedMixedPrefixCharacter N B k h F m x
          ∂uniform01Measure) =
        ∫ x in exactDepthMixedPrefixTupleEventSet N B k F w,
          oscillatoryPhase K x ∂uniform01Measure := by
      simpa only [B, K] using! hfixed
    _ = ∫ x in exactDepthActualMixedPrefixValueWindowSet
          N k F w lower' upper', oscillatoryPhase K x
            ∂uniform01Measure := by
      rw [Measure.restrict_congr_set
        (by simpa only [B, lower', upper'] using! hae)]
    _ = ∫ x in left..right, oscillatoryPhase K x := hinterval

end

end Erdos1002
