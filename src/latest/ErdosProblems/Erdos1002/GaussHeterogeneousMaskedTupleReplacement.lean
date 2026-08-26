import ErdosProblems.Erdos1002.GaussUniformAggregateTransfer

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Masked exact-to-digit replacement for heterogeneous Gauss tuples

In the late marked argument only the coordinates lying after a deterministic
split are replaced by one-digit events.  It is essential to keep the exact
rare events in the prefix: estimating a future suffix by itself loses the
prefix powers of the logarithmic scale.

This file proves the required full-tuple estimate.  A Boolean mask chooses,
coordinate by coordinate, between the exact event and its digit surrogate.
The symmetric difference between the all-exact tuple and this mixed tuple is
covered by the same full-dimensional replacement witnesses as the
all-exact/all-digit comparison.  Consequently every witness still contains
one boundary strip and `r - 1` ordinary rare windows.
-/

open Filter MeasureTheory Set Finset
open scoped BigOperators ENNReal Topology symmDiff

namespace Erdos1002

noncomputable section

local instance gaussHeterogeneousMaskedTupleReplacementPropDecidable
    (P : Prop) : Decidable P := Classical.propDecidable P

/-- Coordinatewise choice between an exact event (`false`) and its digit
surrogate (`true`). -/
def maskedCoordinateEvent
    {Ω : Type*} {r : ℕ} (E D : Fin r → Set Ω)
    (mask : Fin r → Bool) (i : Fin r) : Set Ω :=
  if mask i then D i else E i

/-- Intersection of the coordinatewise masked events. -/
def maskedOrderedEventIntersection
    {Ω : Type*} {r : ℕ} (E D : Fin r → Set Ω)
    (mask : Fin r → Bool) : Set Ω :=
  orderedEventIntersection <|
    List.ofFn (maskedCoordinateEvent E D mask)

@[simp] theorem mem_maskedOrderedEventIntersection_iff
    {Ω : Type*} {r : ℕ} {E D : Fin r → Set Ω}
    {mask : Fin r → Bool} {x : Ω} :
    x ∈ maskedOrderedEventIntersection E D mask ↔
      ∀ i, x ∈ maskedCoordinateEvent E D mask i := by
  unfold maskedOrderedEventIntersection
  exact mem_orderedEventIntersection_ofFn_iff

theorem measurableSet_maskedOrderedEventIntersection
    {Ω : Type*} [MeasurableSpace Ω] {r : ℕ}
    (E D : Fin r → Set Ω) (mask : Fin r → Bool)
    (hE : ∀ i, MeasurableSet (E i))
    (hD : ∀ i, MeasurableSet (D i)) :
    MeasurableSet (maskedOrderedEventIntersection E D mask) := by
  unfold maskedOrderedEventIntersection
  apply measurableSet_orderedEventIntersection
  intro S hS
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hS
  unfold maskedCoordinateEvent
  split
  · exact hD i
  · exact hE i

/-- A replacement witness for the all-exact/masked comparison is contained
in the corresponding all-exact/all-digit witness. -/
theorem coordinateReplacementWitness_masked_subset
    {Ω : Type*} {r : ℕ} (E D : Fin r → Set Ω)
    (mask : Fin r → Bool) (j : Fin r) :
    coordinateReplacementWitness E
        (maskedCoordinateEvent E D mask) j ⊆
      coordinateReplacementWitness E D j := by
  intro x hx
  unfold coordinateReplacementWitness at hx ⊢
  rw [mem_orderedEventIntersection_ofFn_iff] at hx ⊢
  intro i
  by_cases hij : i = j
  · subst i
    have hj := hx j
    simp only [if_pos] at hj ⊢
    cases hmask : mask j with
    | false =>
        exfalso
        simp [maskedCoordinateEvent, hmask] at hj
    | true =>
        simpa [maskedCoordinateEvent, hmask] using! hj
  · simp only [if_neg hij] at hx ⊢
    have hi := hx i
    simp only [if_neg hij] at hi
    unfold maskedCoordinateEvent at hi
    cases hmask : mask i with
    | false =>
        simp only [hmask, Bool.false_eq_true, ↓reduceIte] at hi
        rw [union_self] at hi
        exact Or.inl hi
    | true =>
        simpa only [hmask, ↓reduceIte] using! hi

/-- The full all-exact/masked symmetric difference is covered by the usual
full-dimensional all-exact/all-digit witnesses. -/
theorem symmDiff_exact_masked_subset_iUnion_witness
    {Ω : Type*} {r : ℕ} (E D : Fin r → Set Ω)
    (mask : Fin r → Bool) :
    orderedEventIntersection (List.ofFn E) ∆
        maskedOrderedEventIntersection E D mask ⊆
      ⋃ j, coordinateReplacementWitness E D j := by
  have hfirst :
      orderedEventIntersection (List.ofFn E) ∆
          maskedOrderedEventIntersection E D mask ⊆
        ⋃ j, coordinateReplacementWitness E
          (maskedCoordinateEvent E D mask) j := by
    simpa only [maskedOrderedEventIntersection] using!
      symmDiff_orderedIntersections_subset_iUnion_witness E
        (maskedCoordinateEvent E D mask)
  intro x hx
  obtain ⟨j, hj⟩ := mem_iUnion.mp (hfirst hx)
  exact mem_iUnion.mpr
    ⟨j, coordinateReplacementWitness_masked_subset E D mask j hj⟩

/-- The heterogeneous exact tuple and an arbitrary coordinatewise masked
exact/digit tuple obey the same fixed-tuple replacement estimate as the
all-digit tuple.  In particular, all prefix rare factors are retained. -/
theorem GaussDigitPsiMixing.measure_symmDiff_heterogeneousMaskedTuple_le
    {rate : ℕ → ℝ} (hpsi : GaussDigitPsiMixing rate)
    {r : ℕ} (hr : 0 < r) {scale : ℝ}
    (lower upper : Fin r → ℝ) (times : Fin r → ℕ)
    (mask : Fin r → Bool)
    (gap : ℕ) (hgap0 : 0 < gap)
    (hscale : 0 < scale)
    (hlower : ∀ i, 0 < lower i)
    (hupper : ∀ i, lower i < upper i)
    (hlarge : ∀ i, 16 * (upper i) ^ 2 ≤ lower i * scale)
    (hgap : ∀ i k, i < k → times i + gap ≤ times k)
    (hrate : 0 ≤ rate gap)
    {boundaryMass windowMass : ℝ}
    (hboundaryMass : 0 ≤ boundaryMass)
    (hboundaryLower : ∀ j, gaussMeasure.real
      (scaledGaussFirstDigitBoundaryStrip
        scale (lower j) (8 * (upper j) ^ 2)) ≤ boundaryMass)
    (hboundaryUpper : ∀ j, gaussMeasure.real
      (scaledGaussFirstDigitBoundaryStrip
        scale (upper j) (8 * (upper j) ^ 2)) ≤ boundaryMass)
    (hwindow : ∀ i, gaussMeasure.real
      (gaussEnlargedDigitWindow scale (lower i) (upper i)) ≤
        windowMass) :
    gaussMeasure.real
        (gaussHeterogeneousApproximationTupleEvent
            scale lower upper times ∆
          maskedOrderedEventIntersection
            (fun i ↦ gaussApproximationWindow
              scale (times i) (lower i) (upper i))
            (fun i ↦ gaussDigitWindowAt
              scale (times i) (lower i) (upper i))
            mask) ≤
      (r : ℝ) *
        (2 * ((1 + rate gap) ^ (r - 1) *
          (boundaryMass * windowMass ^ (r - 1)))) := by
  let E : Fin r → Set ℝ := fun i ↦
    gaussApproximationWindow scale (times i) (lower i) (upper i)
  let D : Fin r → Set ℝ := fun i ↦
    gaussDigitWindowAt scale (times i) (lower i) (upper i)
  have hsubset :
      gaussHeterogeneousApproximationTupleEvent scale lower upper times ∆
          maskedOrderedEventIntersection E D mask ⊆
        ⋃ j, coordinateReplacementWitness E D j := by
    simpa only [gaussHeterogeneousApproximationTupleEvent, E, D] using!
      symmDiff_exact_masked_subset_iUnion_witness E D mask
  let common : ℝ :=
    2 * ((1 + rate gap) ^ (r - 1) *
      (boundaryMass * windowMass ^ (r - 1)))
  have hwitness (j : Fin r) :
      gaussMeasure.real (coordinateReplacementWitness E D j) ≤ common := by
    simpa only [E, D, common] using!
      hpsi.measure_heterogeneousCoordinateWitness_le hr
        lower upper times j gap hgap0 hscale hlower hupper hlarge
          hgap hrate hboundaryMass (hboundaryLower j)
          (hboundaryUpper j) (fun i _hij ↦ hwindow i)
  calc
    gaussMeasure.real
        (gaussHeterogeneousApproximationTupleEvent
            scale lower upper times ∆
          maskedOrderedEventIntersection E D mask) ≤
        gaussMeasure.real (⋃ j, coordinateReplacementWitness E D j) :=
      measureReal_mono hsubset
    _ = gaussMeasure.real
        (⋃ j ∈ (Finset.univ : Finset (Fin r)),
          coordinateReplacementWitness E D j) := by simp
    _ ≤ ∑ j ∈ (Finset.univ : Finset (Fin r)),
        gaussMeasure.real (coordinateReplacementWitness E D j) :=
      measureReal_biUnion_finset_le _ _
    _ ≤ ∑ _j ∈ (Finset.univ : Finset (Fin r)), common := by
      exact Finset.sum_le_sum fun j _hj ↦ hwitness j
    _ = (r : ℝ) * common := by simp

/-- Explicit version of the masked replacement bound. -/
theorem gaussMeasure_real_symmDiff_heterogeneousMaskedTuple_le_explicit
    {r : ℕ} (hr : 0 < r) {scale A : ℝ}
    (lower upper : Fin r → ℝ) (times : Fin r → ℕ)
    (mask : Fin r → Bool)
    (gap : ℕ) (hgap0 : 0 < gap)
    (hscale : 0 < scale) (hscaleOne : 1 ≤ scale)
    (hA : 0 ≤ A)
    (hlower : ∀ i, 0 < lower i)
    (hupper : ∀ i, lower i < upper i)
    (hupperA : ∀ i, upper i ≤ A)
    (hlarge : ∀ i, 16 * (upper i) ^ 2 ≤ lower i * scale)
    (hgap : ∀ i k, i < k → times i + gap ≤ times k) :
    gaussMeasure.real
        (gaussHeterogeneousApproximationTupleEvent
            scale lower upper times ∆
          maskedOrderedEventIntersection
            (fun i ↦ gaussApproximationWindow
              scale (times i) (lower i) (upper i))
            (fun i ↦ gaussDigitWindowAt
              scale (times i) (lower i) (upper i))
            mask) ≤
      (r : ℝ) *
        (2 * ((1 + gaussDigitExponentialRate gap) ^ (r - 1) *
          ((((26 * A ^ 2 / scale ^ 2) / Real.log 2)) *
            (((2 * A + 10 * A ^ 2) / scale) /
              Real.log 2) ^ (r - 1)))) := by
  let boundaryMass : ℝ := (26 * A ^ 2 / scale ^ 2) / Real.log 2
  let windowMass : ℝ := ((2 * A + 10 * A ^ 2) / scale) / Real.log 2
  have hscaleSq : 0 < scale ^ 2 := sq_pos_of_pos hscale
  have hlog : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hupperNonneg (i : Fin r) : 0 ≤ upper i :=
    (hlower i).le.trans (hupper i).le
  have hupperSquare (i : Fin r) : (upper i) ^ 2 ≤ A ^ 2 := by
    nlinarith [hupperNonneg i, hupperA i]
  have hboundaryLower (i : Fin r) :
      gaussMeasure.real
          (scaledGaussFirstDigitBoundaryStrip
            scale (lower i) (8 * (upper i) ^ 2)) ≤ boundaryMass := by
    have hraw := gaussMeasure_real_replacementBoundaryStrip_le
      hscale (hlower i) (hupper i) (hlarge i) (Or.inl rfl)
    calc
      gaussMeasure.real
          (scaledGaussFirstDigitBoundaryStrip
            scale (lower i) (8 * (upper i) ^ 2)) ≤
          (26 * (upper i) ^ 2 / scale ^ 2) / Real.log 2 := hraw
      _ ≤ boundaryMass := by
        dsimp only [boundaryMass]
        apply (div_le_div_iff_of_pos_right hlog).2
        apply (div_le_div_iff_of_pos_right hscaleSq).2
        nlinarith [hupperSquare i]
  have hboundaryUpper (i : Fin r) :
      gaussMeasure.real
          (scaledGaussFirstDigitBoundaryStrip
            scale (upper i) (8 * (upper i) ^ 2)) ≤ boundaryMass := by
    have hraw := gaussMeasure_real_replacementBoundaryStrip_le
      hscale (hlower i) (hupper i) (hlarge i) (Or.inr rfl)
    calc
      gaussMeasure.real
          (scaledGaussFirstDigitBoundaryStrip
            scale (upper i) (8 * (upper i) ^ 2)) ≤
          (26 * (upper i) ^ 2 / scale ^ 2) / Real.log 2 := hraw
      _ ≤ boundaryMass := by
        dsimp only [boundaryMass]
        apply (div_le_div_iff_of_pos_right hlog).2
        apply (div_le_div_iff_of_pos_right hscaleSq).2
        nlinarith [hupperSquare i]
  have hwindow (i : Fin r) :
      gaussMeasure.real
          (gaussEnlargedDigitWindow scale (lower i) (upper i)) ≤
        windowMass := by
    have hraw := gaussMeasure_real_gaussEnlargedDigitWindow_le
      hscale hscaleOne (hlower i) (hupper i) (hlarge i)
    have hnumerator :
        2 * upper i + 10 * (upper i) ^ 2 ≤ 2 * A + 10 * A ^ 2 := by
      nlinarith [hupperA i, hupperSquare i]
    calc
      gaussMeasure.real
          (gaussEnlargedDigitWindow scale (lower i) (upper i)) ≤
          ((2 * upper i + 10 * (upper i) ^ 2) / scale) /
            Real.log 2 := hraw
      _ ≤ windowMass := by
        dsimp only [windowMass]
        apply (div_le_div_iff_of_pos_right hlog).2
        apply (div_le_div_iff_of_pos_right hscale).2
        exact hnumerator
  simpa only [boundaryMass, windowMass] using!
    GaussDigitPsiMixing.measure_symmDiff_heterogeneousMaskedTuple_le
      gaussDigitPsiMixing_exponential
        hr lower upper times mask gap hgap0 hscale hlower hupper hlarge
        hgap (gaussDigitExponentialRate_nonnegative gap)
        (by dsimp only [boundaryMass]; positivity)
          hboundaryLower hboundaryUpper hwindow

/-! ## Absolute aggregation at factorial scale -/

/-- Summing the explicit masked bound over an arbitrary finite tuple family
keeps the absolute event error inside the complete family sum. -/
theorem sum_gaussMeasure_real_symmDiff_heterogeneousMaskedTuples_le_explicit
    {r : ℕ} (hr : 0 < r) {scale A : ℝ}
    (lower upper : Fin r → ℝ)
    (tuples : Finset (Fin r → ℕ))
    (mask : (Fin r → ℕ) → Fin r → Bool)
    (gap : ℕ) (hgap0 : 0 < gap)
    (hscale : 0 < scale) (hscaleOne : 1 ≤ scale)
    (hA : 0 ≤ A)
    (hlower : ∀ i, 0 < lower i)
    (hupper : ∀ i, lower i < upper i)
    (hupperA : ∀ i, upper i ≤ A)
    (hlarge : ∀ i, 16 * (upper i) ^ 2 ≤ lower i * scale)
    (hgap : ∀ times ∈ tuples, ∀ i k, i < k →
      times i + gap ≤ times k) :
    (∑ times ∈ tuples,
      gaussMeasure.real
        (gaussHeterogeneousApproximationTupleEvent
            scale lower upper times ∆
          maskedOrderedEventIntersection
            (fun i ↦ gaussApproximationWindow
              scale (times i) (lower i) (upper i))
            (fun i ↦ gaussDigitWindowAt
              scale (times i) (lower i) (upper i))
            (mask times))) ≤
      (tuples.card : ℝ) *
        ((r : ℝ) *
          (2 * ((1 + gaussDigitExponentialRate gap) ^ (r - 1) *
            ((((26 * A ^ 2 / scale ^ 2) / Real.log 2)) *
              (((2 * A + 10 * A ^ 2) / scale) /
                Real.log 2) ^ (r - 1))))) := by
  let common : ℝ :=
    (r : ℝ) *
      (2 * ((1 + gaussDigitExponentialRate gap) ^ (r - 1) *
        ((((26 * A ^ 2 / scale ^ 2) / Real.log 2)) *
          (((2 * A + 10 * A ^ 2) / scale) /
            Real.log 2) ^ (r - 1))))
  calc
    (∑ times ∈ tuples,
      gaussMeasure.real
        (gaussHeterogeneousApproximationTupleEvent
            scale lower upper times ∆
          maskedOrderedEventIntersection
            (fun i ↦ gaussApproximationWindow
              scale (times i) (lower i) (upper i))
            (fun i ↦ gaussDigitWindowAt
              scale (times i) (lower i) (upper i))
            (mask times))) ≤
        ∑ _times ∈ tuples, common := by
      apply Finset.sum_le_sum
      intro times htimes
      exact
        gaussMeasure_real_symmDiff_heterogeneousMaskedTuple_le_explicit
          hr lower upper times (mask times) gap hgap0 hscale hscaleOne
          hA hlower hupper hupperA hlarge (hgap times htimes)
    _ = (tuples.card : ℝ) * common := by simp

variable {β : Type*} [Fintype β]

/-- For a moving logarithmic scale, any full tagged family having bounded
factorial-scale cardinality has vanishing all-exact/masked replacement
error.  The mask may depend on the outer parameter, tag, and tuple. -/
theorem
    tendsto_aggregateGaussHeterogeneousApproximationMaskedSymmDiff_zero
    {r : ℕ} (hr : 0 < r) {A density : ℝ}
    (scale : ℕ → ℝ) (hscale : Tendsto scale atTop atTop)
    (lower upper : β → Fin r → ℝ)
    (hA : 0 ≤ A)
    (hlower : ∀ b i, 0 < lower b i)
    (hupper : ∀ b i, lower b i < upper b i)
    (hupperA : ∀ b i, upper b i ≤ A)
    (tuples : ℕ → β → Finset (Fin r → ℕ))
    (mask : ℕ → β → (Fin r → ℕ) → Fin r → Bool)
    (hchronological : ∀ n b, ∀ t ∈ tuples n b,
      IsChronologicalNatTuple t)
    (htotalDensity : Tendsto
      (fun n ↦ (aggregateTupleFamilyCard (tuples n) : ℝ) /
        scale n ^ r) atTop (nhds density)) :
    Tendsto
      (fun n ↦ ∑ b, ∑ t ∈ tuples n b,
        gaussMeasure.real
          (gaussHeterogeneousApproximationTupleEvent
              (scale n) (lower b) (upper b) t ∆
            maskedOrderedEventIntersection
              (fun i ↦ gaussApproximationWindow
                (scale n) (t i) (lower b i) (upper b i))
              (fun i ↦ gaussDigitWindowAt
                (scale n) (t i) (lower b i) (upper b i))
              (mask n b t)))
      atTop (nhds 0) := by
  let C : ℝ :=
    (r : ℝ) * 2 *
      (1 + gaussDigitExponentialRate 1) ^ (r - 1) *
      (26 * A ^ 2 / Real.log 2) *
      ((2 * A + 10 * A ^ 2) / Real.log 2) ^ (r - 1)
  have hscalePos := hscale.eventually_gt_atTop 0
  have hscaleOne := hscale.eventually (eventually_ge_atTop (1 : ℝ))
  have hcomponentBound :=
    eventually_component_card_div_scale_le_of_aggregate_tendsto
      scale hscalePos tuples htotalDensity
  have hCdiv : Tendsto (fun n : ℕ ↦ C / scale n)
      atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop hscale
  have herrorComponent : ∀ b,
      Tendsto
        (fun n : ℕ ↦
          ∑ t ∈ tuples n b,
            gaussMeasure.real
              (gaussHeterogeneousApproximationTupleEvent
                  (scale n) (lower b) (upper b) t ∆
                maskedOrderedEventIntersection
                  (fun i ↦ gaussApproximationWindow
                    (scale n) (t i) (lower b i) (upper b i))
                  (fun i ↦ gaussDigitWindowAt
                    (scale n) (t i) (lower b i) (upper b i))
                  (mask n b t)))
        atTop (nhds 0) := by
    intro b
    let err : ℕ → ℝ := fun n ↦
      ∑ t ∈ tuples n b,
        gaussMeasure.real
          (gaussHeterogeneousApproximationTupleEvent
              (scale n) (lower b) (upper b) t ∆
            maskedOrderedEventIntersection
              (fun i ↦ gaussApproximationWindow
                (scale n) (t i) (lower b i) (upper b i))
              (fun i ↦ gaussDigitWindowAt
                (scale n) (t i) (lower b i) (upper b i))
              (mask n b t))
    let normalized : ℕ → ℝ := fun n ↦
      ((tuples n b).card : ℝ) / scale n ^ r
    have hlarge :=
      eventually_movingHeterogeneousApproximationWindow_large
        scale hscale (lower b) (upper b) (hlower b)
    have herrUpper : ∀ᶠ n : ℕ in atTop,
        err n ≤ normalized n * (C / scale n) := by
      filter_upwards [hlarge, hscalePos, hscaleOne] with
        n hlargeN hpos hone
      have hraw :=
        sum_gaussMeasure_real_symmDiff_heterogeneousMaskedTuples_le_explicit
          hr (lower b) (upper b) (tuples n b) (mask n b)
            1 (by norm_num) hpos hone hA (hlower b) (hupper b)
            (hupperA b) hlargeN
            (fun t ht i k hik ↦ hchronological n b t ht i k hik)
      refine hraw.trans_eq ?_
      dsimp only [C, normalized]
      have hsne : scale n ≠ 0 := ne_of_gt hpos
      have hboundary :
          (26 * A ^ 2 / scale n ^ 2) / Real.log 2 =
            (26 * A ^ 2 / Real.log 2) / scale n ^ 2 := by
        field_simp
      have hwindow :
          ((2 * A + 10 * A ^ 2) / scale n) / Real.log 2 =
            ((2 * A + 10 * A ^ 2) / Real.log 2) /
              scale n := by
        field_simp
      rw [hboundary, hwindow, div_pow]
      have hpow : scale n ^ r =
          scale n ^ (r - 1) * scale n := by
        conv_lhs =>
          rw [show r = (r - 1) + 1 by omega, pow_succ]
      rw [hpow]
      field_simp [hsne]
    have hnormalized0 :
        ∀ᶠ n : ℕ in atTop, 0 ≤ normalized n := by
      filter_upwards [hscalePos] with n hn
      dsimp only [normalized]
      positivity
    have hnormalizedBound :
        ∀ᶠ n : ℕ in atTop,
          normalized n ≤ |density| + 1 := by
      filter_upwards [hcomponentBound] with n hn
      exact hn b
    have hupperZero :=
      tendsto_bounded_nonneg_mul_zero normalized
        (fun n ↦ C / scale n)
        (add_nonneg (abs_nonneg density) zero_le_one)
        hnormalized0 hnormalizedBound hCdiv
    change Tendsto err atTop (nhds 0)
    apply squeeze_zero'
    · exact Eventually.of_forall fun n ↦
        Finset.sum_nonneg fun _t _ht ↦ measureReal_nonneg
    · exact herrUpper
    · exact hupperZero
  simpa using! tendsto_finset_sum Finset.univ
    (fun b _hb ↦ herrorComponent b)

/-- Uniform-Lebesgue version of the complete tagged masked replacement
estimate. -/
theorem
    tendsto_aggregateUniformHeterogeneousApproximationMaskedSymmDiff_zero
    {r : ℕ} (hr : 0 < r) {A density : ℝ}
    (scale : ℕ → ℝ) (hscale : Tendsto scale atTop atTop)
    (lower upper : β → Fin r → ℝ)
    (hA : 0 ≤ A)
    (hlower : ∀ b i, 0 < lower b i)
    (hupper : ∀ b i, lower b i < upper b i)
    (hupperA : ∀ b i, upper b i ≤ A)
    (tuples : ℕ → β → Finset (Fin r → ℕ))
    (mask : ℕ → β → (Fin r → ℕ) → Fin r → Bool)
    (hchronological : ∀ n b, ∀ t ∈ tuples n b,
      IsChronologicalNatTuple t)
    (htotalDensity : Tendsto
      (fun n ↦ (aggregateTupleFamilyCard (tuples n) : ℝ) /
        scale n ^ r) atTop (nhds density)) :
    Tendsto
      (fun n ↦ ∑ b, ∑ t ∈ tuples n b,
        uniform01Measure.real
          (gaussHeterogeneousApproximationTupleEvent
              (scale n) (lower b) (upper b) t ∆
            maskedOrderedEventIntersection
              (fun i ↦ gaussApproximationWindow
                (scale n) (t i) (lower b i) (upper b i))
              (fun i ↦ gaussDigitWindowAt
                (scale n) (t i) (lower b i) (upper b i))
              (mask n b t)))
      atTop (nhds 0) := by
  let gaussErr : ℕ → ℝ := fun n ↦ ∑ b, ∑ t ∈ tuples n b,
    gaussMeasure.real
      (gaussHeterogeneousApproximationTupleEvent
          (scale n) (lower b) (upper b) t ∆
        maskedOrderedEventIntersection
          (fun i ↦ gaussApproximationWindow
            (scale n) (t i) (lower b i) (upper b i))
          (fun i ↦ gaussDigitWindowAt
            (scale n) (t i) (lower b i) (upper b i))
          (mask n b t))
  have hgauss : Tendsto gaussErr atTop (nhds 0) := by
    simpa only [gaussErr] using!
      tendsto_aggregateGaussHeterogeneousApproximationMaskedSymmDiff_zero
        hr scale hscale lower upper hA hlower hupper hupperA
          tuples mask hchronological htotalDensity
  have hscaled :
      Tendsto (fun n ↦ (2 * Real.log 2) * gaussErr n)
        atTop (nhds 0) := by
    simpa only [mul_zero] using! tendsto_const_nhds.mul hgauss
  apply squeeze_zero'
  · exact Eventually.of_forall fun n ↦
      Finset.sum_nonneg fun _b _hb ↦
        Finset.sum_nonneg fun _t _ht ↦ measureReal_nonneg
  · exact Eventually.of_forall fun n ↦ by
      calc
        (∑ b, ∑ t ∈ tuples n b,
          uniform01Measure.real
            (gaussHeterogeneousApproximationTupleEvent
                (scale n) (lower b) (upper b) t ∆
              maskedOrderedEventIntersection
                (fun i ↦ gaussApproximationWindow
                  (scale n) (t i) (lower b i) (upper b i))
                (fun i ↦ gaussDigitWindowAt
                  (scale n) (t i) (lower b i) (upper b i))
                (mask n b t))) ≤
            ∑ b, ∑ t ∈ tuples n b,
              (2 * Real.log 2) *
                gaussMeasure.real
                  (gaussHeterogeneousApproximationTupleEvent
                      (scale n) (lower b) (upper b) t ∆
                    maskedOrderedEventIntersection
                      (fun i ↦ gaussApproximationWindow
                        (scale n) (t i) (lower b i) (upper b i))
                      (fun i ↦ gaussDigitWindowAt
                        (scale n) (t i) (lower b i) (upper b i))
                      (mask n b t)) := by
          apply Finset.sum_le_sum
          intro b _hb
          apply Finset.sum_le_sum
          intro t _ht
          exact uniform01MeasureReal_le_gaussMeasureReal
            ((measurableSet_gaussHeterogeneousApproximationTupleEvent
              (scale n) (lower b) (upper b) t).symmDiff
              (measurableSet_maskedOrderedEventIntersection
                (fun i ↦ gaussApproximationWindow
                  (scale n) (t i) (lower b i) (upper b i))
                (fun i ↦ gaussDigitWindowAt
                  (scale n) (t i) (lower b i) (upper b i))
                (mask n b t)
                (fun i ↦ measurableSet_gaussApproximationWindow _ _ _ _)
                (fun i ↦ measurableSet_gaussDigitWindowAt _ _ _ _)))
        _ = (2 * Real.log 2) * gaussErr n := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro b _hb
          rw [Finset.mul_sum]
  · exact hscaled

end

end Erdos1002
