import ErdosProblems.Erdos1002.GaussHeterogeneousTupleBounds
import ErdosProblems.Erdos1002.GaussDenominatorMaximal

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Exact-to-digit replacement for heterogeneous tuples

This is the coordinate-dependent version of the factorial tuple
replacement.  Each exact approximation window may have different positive
endpoints.  The symmetric difference is covered, with absolute values
already taken, by a union of tuples containing one one-digit endpoint strip
and enlarged one-digit windows in all other coordinates.
-/

open Filter MeasureTheory Set
open scoped BigOperators ENNReal Topology symmDiff

namespace Erdos1002

noncomputable section

/-- Coordinate-dependent tuple formed from the digit surrogate events that
retain the common initial-state restriction. -/
def gaussHeterogeneousDigitWindowTupleEvent
    {r : ℕ} (scale : ℝ) (lower upper : Fin r → ℝ)
    (times : Fin r → ℕ) : Set ℝ :=
  orderedEventIntersection <| List.ofFn fun i ↦
    gaussDigitWindowAt scale (times i) (lower i) (upper i)

theorem measurableSet_gaussHeterogeneousDigitWindowTupleEvent
    {r : ℕ} (scale : ℝ) (lower upper : Fin r → ℝ)
    (times : Fin r → ℕ) :
    MeasurableSet
      (gaussHeterogeneousDigitWindowTupleEvent
        scale lower upper times) := by
  apply measurableSet_orderedEventIntersection
  intro A hA
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hA
  exact measurableSet_gaussDigitWindowAt _ _ _ _

/-- Under Gauss measure, the common initial-state restriction in the digit
window tuple is redundant. -/
theorem gaussMeasure_real_heterogeneousDigitWindowTupleEvent_eq_pure
    {r : ℕ} (hr : 0 < r) (scale : ℝ)
    (lower upper : Fin r → ℝ) (times : Fin r → ℕ) :
    gaussMeasure.real
        (gaussHeterogeneousDigitWindowTupleEvent
          scale lower upper times) =
      gaussMeasure.real
        (gaussHeterogeneousDigitTupleEvent
          scale lower upper times) := by
  let U : Set ℝ := Ioc (0 : ℝ) 1
  let H : Set ℝ := gaussHeterogeneousDigitTupleEvent
    scale lower upper times
  have hset : gaussHeterogeneousDigitWindowTupleEvent
      scale lower upper times = U ∩ H := by
    ext x
    simp only [gaussHeterogeneousDigitWindowTupleEvent,
      gaussHeterogeneousDigitTupleEvent,
      mem_orderedEventIntersection_ofFn_iff,
      gaussDigitWindowAt, mem_inter_iff, Set.mem_preimage, U, H]
    constructor
    · intro hall
      exact ⟨(hall ⟨0, hr⟩).1, fun i ↦ (hall i).2⟩
    · rintro ⟨hxU, hxH⟩ i
      exact ⟨hxU, hxH i⟩
  rw [hset]
  apply measureReal_congr
  filter_upwards [gaussMeasure_unit_ae] with x hx
  change ((x ∈ Ioc (0 : ℝ) 1) ∧ x ∈ H) = (x ∈ H)
  apply propext
  exact and_iff_right hx

/-- Elementary measure triangle inequality through a symmetric difference. -/
theorem measureReal_le_add_measureReal_symmDiff
    (mu : Measure ℝ) [IsFiniteMeasure mu] (E D : Set ℝ) :
    mu.real E ≤ mu.real D + mu.real (E ∆ D) := by
  have hsubset : E ⊆ D ∪ (E ∆ D) := by
    intro x hxE
    by_cases hxD : x ∈ D
    · exact Or.inl hxD
    · exact Or.inr (Or.inl ⟨hxE, hxD⟩)
  exact (measureReal_mono hsubset).trans (measureReal_union_le D (E ∆ D))

/-- Upper endpoint of the one-digit window enlarged for exact-to-digit
replacement. -/
def gaussHeterogeneousEnlargedUpper
    {r : ℕ} (scale : ℝ) (upper : Fin r → ℝ) (i : Fin r) : ℝ :=
  upper i + 8 * (upper i) ^ 2 / scale

/-- An ordinary positive digit window is contained in its replacement
enlargement. -/
theorem scaledGaussFirstDigitWindow_subset_gaussEnlargedDigitWindow
    {scale lower upper : ℝ} (hscale : 0 < scale) :
    scaledGaussFirstDigitWindow scale lower upper ⊆
      gaussEnlargedDigitWindow scale lower upper := by
  intro x hx
  exact ⟨hx.1, hx.2.1, hx.2.2.trans
    (le_add_of_nonneg_right (div_nonneg
      (mul_nonneg (by norm_num) (sq_nonneg upper)) hscale.le))⟩

/-- One heterogeneous coordinate witness is covered by the terminating
exceptional event and the two possible pure one-digit boundary tuples. -/
theorem heterogeneousCoordinateReplacementWitness_subset_boundaryTuples
    {r : ℕ} {scale : ℝ} (lower upper : Fin r → ℝ)
    (times : Fin r → ℕ) (j : Fin r)
    (hscale : 0 < scale)
    (hlower : ∀ i, 0 < lower i)
    (hupper : ∀ i, lower i < upper i)
    (hlarge : ∀ i, 16 * (upper i) ^ 2 ≤ lower i * scale) :
    coordinateReplacementWitness
        (fun i ↦ gaussApproximationWindow
          scale (times i) (lower i) (upper i))
        (fun i ↦ gaussDigitWindowAt
          scale (times i) (lower i) (upper i)) j ⊆
      gaussTupleExceptional times ∪
        (gaussHeterogeneousBoundaryDigitTupleEvent
            scale lower
              (gaussHeterogeneousEnlargedUpper scale upper)
              (lower j) (8 * (upper j) ^ 2) times j ∪
          gaussHeterogeneousBoundaryDigitTupleEvent
            scale lower
              (gaussHeterogeneousEnlargedUpper scale upper)
              (upper j) (8 * (upper j) ^ 2) times j) := by
  intro x hxWitness
  have hall := mem_orderedEventIntersection_ofFn_iff.mp hxWitness
  by_cases hexists : ∃ i, x ∈ gaussPrefixExceptional (times i + 1)
  · left
    exact mem_iUnion.mpr hexists
  right
  have hnotExceptional (i : Fin r) :
      x ∉ gaussPrefixExceptional (times i + 1) := by
    exact fun hi ↦ hexists ⟨i, hi⟩
  have hjMismatch :
      x ∈ gaussApproximationWindow
          scale (times j) (lower j) (upper j) ∆
        gaussDigitWindowAt scale (times j) (lower j) (upper j) := by
    simpa using! hall j
  have hjCover :=
    symmDiff_gaussApproximationWindow_gaussDigitWindowAt_subset
      hscale (hlower j) (hupper j) (hlarge j) hjMismatch
  have hjBoundary :
      x ∈ (gaussOrbit (times j)) ⁻¹'
          scaledGaussFirstDigitBoundaryStrip
            scale (lower j) (8 * (upper j) ^ 2) ∨
        x ∈ (gaussOrbit (times j)) ⁻¹'
          scaledGaussFirstDigitBoundaryStrip
            scale (upper j) (8 * (upper j) ^ 2) := by
    rcases hjCover with hjExceptional | hjBoundary
    · exact (hnotExceptional j hjExceptional).elim
    · exact hjBoundary
  have hother (i : Fin r) (hij : i ≠ j) :
      x ∈ (gaussOrbit (times i)) ⁻¹'
        gaussEnlargedDigitWindow scale (lower i) (upper i) := by
    have hiUnion :
        x ∈ gaussApproximationWindow
            scale (times i) (lower i) (upper i) ∪
          gaussDigitWindowAt scale (times i) (lower i) (upper i) := by
      simpa only [if_neg hij] using! hall i
    have hiCover :=
      union_gaussApproximationWindow_gaussDigitWindowAt_subset
        hscale (hlower i) (hupper i) (hlarge i) hiUnion
    rcases hiCover with hiExceptional | hiWindow
    · exact (hnotExceptional i hiExceptional).elim
    · exact hiWindow
  rcases hjBoundary with hjLower | hjUpper
  · left
    apply mem_orderedEventIntersection_ofFn_iff.mpr
    intro i
    by_cases hij : i = j
    · subst i
      simpa [gaussHeterogeneousBoundaryDigitTupleEvent,
        gaussHeterogeneousBoundaryDigitBaseEvent] using! hjLower
    · simpa [gaussHeterogeneousBoundaryDigitTupleEvent,
        gaussHeterogeneousBoundaryDigitBaseEvent,
        gaussHeterogeneousEnlargedUpper, gaussEnlargedDigitWindow,
        hij] using! hother i hij
  · right
    apply mem_orderedEventIntersection_ofFn_iff.mpr
    intro i
    by_cases hij : i = j
    · subst i
      simpa [gaussHeterogeneousBoundaryDigitTupleEvent,
        gaussHeterogeneousBoundaryDigitBaseEvent] using! hjUpper
    · simpa [gaussHeterogeneousBoundaryDigitTupleEvent,
        gaussHeterogeneousBoundaryDigitBaseEvent,
        gaussHeterogeneousEnlargedUpper, gaussEnlargedDigitWindow,
        hij] using! hother i hij

/-- Mass of one heterogeneous replacement witness. -/
theorem GaussDigitPsiMixing.measure_heterogeneousCoordinateWitness_le
    {rate : ℕ → ℝ} (hpsi : GaussDigitPsiMixing rate)
    {r : ℕ} (hr : 0 < r) {scale : ℝ}
    (lower upper : Fin r → ℝ) (times : Fin r → ℕ) (j : Fin r)
    (gap : ℕ) (hgap0 : 0 < gap)
    (hscale : 0 < scale)
    (hlower : ∀ i, 0 < lower i)
    (hupper : ∀ i, lower i < upper i)
    (hlarge : ∀ i, 16 * (upper i) ^ 2 ≤ lower i * scale)
    (hgap : ∀ i k, i < k → times i + gap ≤ times k)
    (hrate : 0 ≤ rate gap)
    {boundaryMass windowMass : ℝ}
    (hboundaryMass : 0 ≤ boundaryMass)
    (hboundaryLower : gaussMeasure.real
      (scaledGaussFirstDigitBoundaryStrip
        scale (lower j) (8 * (upper j) ^ 2)) ≤ boundaryMass)
    (hboundaryUpper : gaussMeasure.real
      (scaledGaussFirstDigitBoundaryStrip
        scale (upper j) (8 * (upper j) ^ 2)) ≤ boundaryMass)
    (hwindow : ∀ i, i ≠ j → gaussMeasure.real
      (gaussEnlargedDigitWindow scale (lower i) (upper i)) ≤
        windowMass) :
    gaussMeasure.real
        (coordinateReplacementWitness
          (fun i ↦ gaussApproximationWindow
            scale (times i) (lower i) (upper i))
          (fun i ↦ gaussDigitWindowAt
            scale (times i) (lower i) (upper i)) j) ≤
      2 * ((1 + rate gap) ^ (r - 1) *
        (boundaryMass * windowMass ^ (r - 1))) := by
  let P₀ := gaussHeterogeneousBoundaryDigitTupleEvent
    scale lower (gaussHeterogeneousEnlargedUpper scale upper)
      (lower j) (8 * (upper j) ^ 2) times j
  let P₁ := gaussHeterogeneousBoundaryDigitTupleEvent
    scale lower (gaussHeterogeneousEnlargedUpper scale upper)
      (upper j) (8 * (upper j) ^ 2) times j
  let Z := gaussTupleExceptional times
  have hcover :
      coordinateReplacementWitness
          (fun i ↦ gaussApproximationWindow
            scale (times i) (lower i) (upper i))
          (fun i ↦ gaussDigitWindowAt
            scale (times i) (lower i) (upper i)) j ⊆
        Z ∪ (P₀ ∪ P₁) := by
    simpa only [Z, P₀, P₁] using!
      heterogeneousCoordinateReplacementWitness_subset_boundaryTuples
        lower upper times j hscale hlower hupper hlarge
  have hP₀ := hpsi.measure_heterogeneousBoundaryDigitTupleEvent_le hr
    lower (gaussHeterogeneousEnlargedUpper scale upper) times j gap
      hgap0 hgap hrate hboundaryMass hboundaryLower (by
        intro i hij
        simpa only [gaussHeterogeneousEnlargedUpper,
          gaussEnlargedDigitWindow] using! hwindow i hij)
  have hP₁ := hpsi.measure_heterogeneousBoundaryDigitTupleEvent_le hr
    lower (gaussHeterogeneousEnlargedUpper scale upper) times j gap
      hgap0 hgap hrate hboundaryMass hboundaryUpper (by
        intro i hij
        simpa only [gaussHeterogeneousEnlargedUpper,
          gaussEnlargedDigitWindow] using! hwindow i hij)
  let common : ℝ := (1 + rate gap) ^ (r - 1) *
    (boundaryMass * windowMass ^ (r - 1))
  calc
    gaussMeasure.real
        (coordinateReplacementWitness
          (fun i ↦ gaussApproximationWindow
            scale (times i) (lower i) (upper i))
          (fun i ↦ gaussDigitWindowAt
            scale (times i) (lower i) (upper i)) j) ≤
        gaussMeasure.real (Z ∪ (P₀ ∪ P₁)) := measureReal_mono hcover
    _ ≤ gaussMeasure.real Z + gaussMeasure.real (P₀ ∪ P₁) :=
      measureReal_union_le Z (P₀ ∪ P₁)
    _ = gaussMeasure.real (P₀ ∪ P₁) := by
      rw [show gaussMeasure.real Z = 0 by
        exact gaussMeasure_real_gaussTupleExceptional times]
      simp
    _ ≤ gaussMeasure.real P₀ + gaussMeasure.real P₁ :=
      measureReal_union_le P₀ P₁
    _ ≤ common + common := add_le_add
      (by simpa only [P₀, common] using! hP₀)
      (by simpa only [P₁, common] using! hP₁)
    _ = 2 * common := by ring

/-- Full heterogeneous tuple replacement estimate. -/
theorem GaussDigitPsiMixing.measure_symmDiff_heterogeneousTuples_le
    {rate : ℕ → ℝ} (hpsi : GaussDigitPsiMixing rate)
    {r : ℕ} (hr : 0 < r) {scale : ℝ}
    (lower upper : Fin r → ℝ) (times : Fin r → ℕ)
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
          gaussHeterogeneousDigitWindowTupleEvent
            scale lower upper times) ≤
      (r : ℝ) *
        (2 * ((1 + rate gap) ^ (r - 1) *
          (boundaryMass * windowMass ^ (r - 1)))) := by
  let E : Fin r → Set ℝ := fun i ↦
    gaussApproximationWindow scale (times i) (lower i) (upper i)
  let D : Fin r → Set ℝ := fun i ↦
    gaussDigitWindowAt scale (times i) (lower i) (upper i)
  have hsubset :
      gaussHeterogeneousApproximationTupleEvent scale lower upper times ∆
          gaussHeterogeneousDigitWindowTupleEvent scale lower upper times ⊆
        ⋃ j, coordinateReplacementWitness E D j := by
    simpa only [gaussHeterogeneousApproximationTupleEvent,
      gaussHeterogeneousDigitWindowTupleEvent, E, D] using!
      symmDiff_orderedIntersections_subset_iUnion_witness E D
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
          gaussHeterogeneousDigitWindowTupleEvent
            scale lower upper times) ≤
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

/-- Explicit heterogeneous replacement bound using the proved one-event
constants.  A common upper endpoint bound `A` gives one uniform
`O(scale⁻²)` boundary mass and one uniform `O(scale⁻¹)` enlarged-window
mass for every coordinate. -/
theorem gaussMeasure_real_symmDiff_heterogeneousTuples_le_explicit
    {r : ℕ} (hr : 0 < r) {scale A : ℝ}
    (lower upper : Fin r → ℝ) (times : Fin r → ℕ)
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
          gaussHeterogeneousDigitWindowTupleEvent
            scale lower upper times) ≤
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
    gaussDigitPsiMixing_exponential.measure_symmDiff_heterogeneousTuples_le
      hr lower upper times gap hgap0 hscale hlower hupper hlarge hgap
        (gaussDigitExponentialRate_nonnegative gap)
        (by dsimp only [boundaryMass]; positivity)
        hboundaryLower hboundaryUpper hwindow

/-- A heterogeneous exact tuple with one genuinely shrinking coordinate
has `O(scale^(-r-1))` mass.  The first term is the corresponding digit
tuple with its distinguished `O(scale^-2)` window; the second is the full
exact-to-digit replacement error. -/
theorem gaussMeasure_real_heterogeneousApproximationTupleEvent_le_boundary
    {r : ℕ} (hr : 0 < r) {scale A center eta : ℝ}
    (lower upper : Fin r → ℝ) (times : Fin r → ℕ) (j : Fin r)
    (gap : ℕ) (hgap0 : 0 < gap)
    (hscale : 0 < scale) (hscaleOne : 1 ≤ scale)
    (hA : 0 ≤ A) (hcenter : 0 < center) (hcenterA : center ≤ A)
    (heta : 0 < eta) (hetaCenter : 2 * eta ≤ center)
    (hetaScale : eta * scale ≤ A ^ 2)
    (hlower : ∀ i, 0 < lower i)
    (hupper : ∀ i, lower i < upper i)
    (hupperA : ∀ i, upper i ≤ A)
    (hjLower : lower j = center - eta)
    (hjUpper : upper j = center + eta)
    (hlarge : ∀ i, 16 * (upper i) ^ 2 ≤ lower i * scale)
    (hgap : ∀ i k, i < k → times i + gap ≤ times k) :
    gaussMeasure.real
        (gaussHeterogeneousApproximationTupleEvent
          scale lower upper times) ≤
      (1 + gaussDigitExponentialRate gap) ^ (r - 1) *
          (((12 * A ^ 2 / scale ^ 2) / Real.log 2) *
            (((2 * A + 10 * A ^ 2) / scale) /
              Real.log 2) ^ (r - 1)) +
        (r : ℝ) *
          (2 * ((1 + gaussDigitExponentialRate gap) ^ (r - 1) *
            ((((26 * A ^ 2 / scale ^ 2) / Real.log 2)) *
              (((2 * A + 10 * A ^ 2) / scale) /
                Real.log 2) ^ (r - 1)))) := by
  let boundaryMass : ℝ := (12 * A ^ 2 / scale ^ 2) / Real.log 2
  let windowMass : ℝ := ((2 * A + 10 * A ^ 2) / scale) / Real.log 2
  have hscaleNe : scale ≠ 0 := ne_of_gt hscale
  have hlog : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hcenterSquare : center ^ 2 ≤ A ^ 2 := by
    nlinarith [hcenter.le, hcenterA]
  have hboundarySet :
      scaledGaussFirstDigitWindow scale (lower j) (upper j) =
        scaledGaussFirstDigitBoundaryStrip
          scale center (eta * scale) := by
    rw [scaledGaussFirstDigitBoundaryStrip_eq_window, hjLower, hjUpper]
    congr 1 <;> field_simp
  have hboundaryRaw :
      gaussMeasure.real
          (scaledGaussFirstDigitWindow scale (lower j) (upper j)) ≤
        (((2 * (eta * scale) + 10 * center ^ 2) / scale ^ 2) /
          Real.log 2) := by
    rw [hboundarySet]
    apply gaussMeasure_real_scaledGaussFirstDigitBoundaryStrip_le
    · exact hscale
    · exact hcenter
    · exact mul_pos heta hscale
    · simpa only [mul_assoc] using!
        mul_le_mul_of_nonneg_right hetaCenter hscale.le
  have hboundary :
      gaussMeasure.real
          (scaledGaussFirstDigitWindow scale (lower j) (upper j)) ≤
        boundaryMass := by
    have hnumerator :
        2 * (eta * scale) + 10 * center ^ 2 ≤ 12 * A ^ 2 := by
      nlinarith [hetaScale, hcenterSquare]
    calc
      gaussMeasure.real
          (scaledGaussFirstDigitWindow scale (lower j) (upper j)) ≤
          (((2 * (eta * scale) + 10 * center ^ 2) / scale ^ 2) /
            Real.log 2) := hboundaryRaw
      _ ≤ boundaryMass := by
        dsimp only [boundaryMass]
        apply (div_le_div_iff_of_pos_right hlog).2
        apply (div_le_div_iff_of_pos_right (sq_pos_of_pos hscale)).2
        exact hnumerator
  have hwindow (i : Fin r) (hij : i ≠ j) :
      gaussMeasure.real
          (scaledGaussFirstDigitWindow scale (lower i) (upper i)) ≤
        windowMass := by
    have hsubset :=
      scaledGaussFirstDigitWindow_subset_gaussEnlargedDigitWindow
        (lower := lower i) (upper := upper i) hscale
    have hmono :
        gaussMeasure.real
            (scaledGaussFirstDigitWindow scale (lower i) (upper i)) ≤
          gaussMeasure.real
            (gaussEnlargedDigitWindow scale (lower i) (upper i)) :=
      measureReal_mono hsubset
    have henlarged := gaussMeasure_real_gaussEnlargedDigitWindow_le
      hscale hscaleOne (hlower i) (hupper i) (hlarge i)
    have hupperNonneg : 0 ≤ upper i :=
      (hlower i).le.trans (hupper i).le
    have hupperSquare : (upper i) ^ 2 ≤ A ^ 2 := by
      nlinarith [hupperNonneg, hupperA i]
    have hnumerator :
        2 * upper i + 10 * (upper i) ^ 2 ≤ 2 * A + 10 * A ^ 2 := by
      nlinarith [hupperA i, hupperSquare]
    calc
      gaussMeasure.real
          (scaledGaussFirstDigitWindow scale (lower i) (upper i)) ≤
          gaussMeasure.real
            (gaussEnlargedDigitWindow scale (lower i) (upper i)) := hmono
      _ ≤ (((2 * upper i + 10 * (upper i) ^ 2) / scale) /
            Real.log 2) := henlarged
      _ ≤ windowMass := by
        dsimp only [windowMass]
        apply (div_le_div_iff_of_pos_right hlog).2
        apply (div_le_div_iff_of_pos_right hscale).2
        exact hnumerator
  have hdigitPure :=
    GaussDigitPsiMixing.measure_heterogeneousDigitTupleEvent_le_distinguished
      gaussDigitPsiMixing_exponential hr lower upper times j gap hgap0 hgap
        (gaussDigitExponentialRate_nonnegative gap)
        (boundaryMass := boundaryMass) (windowMass := windowMass)
        (by dsimp only [boundaryMass]; positivity) hboundary hwindow
  have hdigitWindow :
      gaussMeasure.real
          (gaussHeterogeneousDigitWindowTupleEvent
            scale lower upper times) ≤
        (1 + gaussDigitExponentialRate gap) ^ (r - 1) *
          (boundaryMass * windowMass ^ (r - 1)) := by
    rw [gaussMeasure_real_heterogeneousDigitWindowTupleEvent_eq_pure
      hr scale lower upper times]
    exact hdigitPure
  have hreplacement :=
    gaussMeasure_real_symmDiff_heterogeneousTuples_le_explicit
      hr lower upper times gap hgap0 hscale hscaleOne hA hlower hupper
        hupperA hlarge hgap
  have htriangle := measureReal_le_add_measureReal_symmDiff gaussMeasure
    (gaussHeterogeneousApproximationTupleEvent scale lower upper times)
    (gaussHeterogeneousDigitWindowTupleEvent scale lower upper times)
  calc
    gaussMeasure.real
        (gaussHeterogeneousApproximationTupleEvent
          scale lower upper times) ≤
        gaussMeasure.real
            (gaussHeterogeneousDigitWindowTupleEvent
              scale lower upper times) +
          gaussMeasure.real
            (gaussHeterogeneousApproximationTupleEvent
                scale lower upper times ∆
              gaussHeterogeneousDigitWindowTupleEvent
                scale lower upper times) := htriangle
    _ ≤ (1 + gaussDigitExponentialRate gap) ^ (r - 1) *
          (boundaryMass * windowMass ^ (r - 1)) +
        (r : ℝ) *
          (2 * ((1 + gaussDigitExponentialRate gap) ^ (r - 1) *
            ((((26 * A ^ 2 / scale ^ 2) / Real.log 2)) *
              (((2 * A + 10 * A ^ 2) / scale) /
                Real.log 2) ^ (r - 1)))) :=
      add_le_add hdigitWindow hreplacement
    _ = _ := by rfl

/-- Algebraic cancellation for one distinguished boundary coordinate and
`r-1` ordinary rare coordinates. -/
theorem heterogeneousBoundaryTupleScaleCancellation
    {r L : ℕ} (hr : 0 < r) (hL : 0 < L) (C B W : ℝ) :
    (L : ℝ) ^ r *
        (C * ((B / (L : ℝ) ^ 2) *
          (W / (L : ℝ)) ^ (r - 1))) =
      (C * B * W ^ (r - 1)) / (L : ℝ) := by
  cases r with
  | zero => omega
  | succ q =>
      have hLne : (L : ℝ) ≠ 0 := by
        exact_mod_cast (Nat.ne_of_gt hL)
      simp only [Nat.add_sub_cancel, div_pow]
      field_simp
      ring

/-- Absolute sum of heterogeneous exact boundary-tuple masses over a full
factorial-scale family.  The bound is an explicit constant divided by the
horizon. -/
theorem sum_gaussMeasure_real_heterogeneousBoundaryFinTuples_le_const_div
    {r L : ℕ} (hr : 0 < r) (hL : 0 < L)
    {A center eta : ℝ} (lower upper : Fin r → ℝ)
    (tuples : Finset (Fin r → Fin L)) (j : Fin r)
    (gap : ℕ) (hgap0 : 0 < gap)
    (hA : 0 ≤ A) (hcenter : 0 < center) (hcenterA : center ≤ A)
    (heta : 0 < eta) (hetaCenter : 2 * eta ≤ center)
    (hetaScale : eta * (L : ℝ) ≤ A ^ 2)
    (hlower : ∀ i, 0 < lower i)
    (hupper : ∀ i, lower i < upper i)
    (hupperA : ∀ i, upper i ≤ A)
    (hjLower : lower j = center - eta)
    (hjUpper : upper j = center + eta)
    (hlarge : ∀ i, 16 * (upper i) ^ 2 ≤ lower i * (L : ℝ))
    (hgap : ∀ times ∈ tuples, ∀ i k, i < k →
      (times i).1 + gap ≤ (times k).1) :
    (∑ times ∈ tuples,
      gaussMeasure.real
        (gaussHeterogeneousApproximationTupleEvent
          (L : ℝ) lower upper (fun i ↦ (times i).1))) ≤
      ((1 + gaussDigitExponentialRate gap) ^ (r - 1) *
            (12 * A ^ 2 / Real.log 2) *
            ((2 * A + 10 * A ^ 2) / Real.log 2) ^ (r - 1) +
          ((r : ℝ) * 2 *
            (1 + gaussDigitExponentialRate gap) ^ (r - 1)) *
            (26 * A ^ 2 / Real.log 2) *
            ((2 * A + 10 * A ^ 2) / Real.log 2) ^ (r - 1)) /
        (L : ℝ) := by
  let mix : ℝ := (1 + gaussDigitExponentialRate gap) ^ (r - 1)
  let B₁ : ℝ := 12 * A ^ 2 / Real.log 2
  let B₂ : ℝ := 26 * A ^ 2 / Real.log 2
  let W : ℝ := (2 * A + 10 * A ^ 2) / Real.log 2
  let common : ℝ :=
    mix *
        (((12 * A ^ 2 / (L : ℝ) ^ 2) / Real.log 2) *
          (((2 * A + 10 * A ^ 2) / (L : ℝ)) /
            Real.log 2) ^ (r - 1)) +
      (r : ℝ) *
        (2 * (mix *
          ((((26 * A ^ 2 / (L : ℝ) ^ 2) / Real.log 2)) *
            (((2 * A + 10 * A ^ 2) / (L : ℝ)) /
              Real.log 2) ^ (r - 1))))
  have hterm (times : Fin r → Fin L) (htimes : times ∈ tuples) :
      gaussMeasure.real
          (gaussHeterogeneousApproximationTupleEvent
            (L : ℝ) lower upper (fun i ↦ (times i).1)) ≤ common := by
    simpa only [common, mix] using!
      gaussMeasure_real_heterogeneousApproximationTupleEvent_le_boundary
        hr lower upper (fun i ↦ (times i).1) j gap hgap0
          (by exact_mod_cast hL) (by exact_mod_cast hL)
          hA hcenter hcenterA heta hetaCenter hetaScale
          hlower hupper hupperA hjLower hjUpper hlarge (hgap times htimes)
  have hcardNat : tuples.card ≤ L ^ r := by
    have h := Finset.card_le_univ tuples
    simpa only [Fintype.card_fun, Fintype.card_fin] using! h
  have hcardReal : (tuples.card : ℝ) ≤ (L : ℝ) ^ r := by
    exact_mod_cast hcardNat
  have hlogNe : Real.log 2 ≠ 0 :=
    ne_of_gt (Real.log_pos one_lt_two)
  have hboundary₁Rewrite :
      (12 * A ^ 2 / (L : ℝ) ^ 2) / Real.log 2 =
        B₁ / (L : ℝ) ^ 2 := by
    dsimp only [B₁]
    field_simp
  have hboundary₂Rewrite :
      (26 * A ^ 2 / (L : ℝ) ^ 2) / Real.log 2 =
        B₂ / (L : ℝ) ^ 2 := by
    dsimp only [B₂]
    field_simp
  have hwindowRewrite :
      ((2 * A + 10 * A ^ 2) / (L : ℝ)) / Real.log 2 =
        W / (L : ℝ) := by
    dsimp only [W]
    field_simp
  have hcommonRewrite :
      common =
        mix * ((B₁ / (L : ℝ) ^ 2) *
          (W / (L : ℝ)) ^ (r - 1)) +
        ((r : ℝ) * 2 * mix) *
          ((B₂ / (L : ℝ) ^ 2) *
            (W / (L : ℝ)) ^ (r - 1)) := by
    dsimp only [common]
    rw [hboundary₁Rewrite, hboundary₂Rewrite, hwindowRewrite]
    ring
  have hmixNonneg : 0 ≤ mix := by
    dsimp only [mix]
    exact pow_nonneg (by
      linarith [gaussDigitExponentialRate_nonnegative gap]) _
  have hB₁Nonneg : 0 ≤ B₁ := by dsimp only [B₁]; positivity
  have hB₂Nonneg : 0 ≤ B₂ := by dsimp only [B₂]; positivity
  have hWNonneg : 0 ≤ W := by
    dsimp only [W]
    have hnum : 0 ≤ 2 * A + 10 * A ^ 2 := by
      nlinarith [sq_nonneg A]
    exact div_nonneg hnum (Real.log_pos one_lt_two).le
  have hcommonNonneg : 0 ≤ common := by
    rw [hcommonRewrite]
    positivity
  have hcancel₁ := heterogeneousBoundaryTupleScaleCancellation
    hr hL mix B₁ W
  have hcancel₂ := heterogeneousBoundaryTupleScaleCancellation
    hr hL ((r : ℝ) * 2 * mix) B₂ W
  calc
    (∑ times ∈ tuples,
      gaussMeasure.real
        (gaussHeterogeneousApproximationTupleEvent
          (L : ℝ) lower upper (fun i ↦ (times i).1))) ≤
        ∑ _times ∈ tuples, common := by
      exact Finset.sum_le_sum hterm
    _ = (tuples.card : ℝ) * common := by simp
    _ ≤ (L : ℝ) ^ r * common :=
      mul_le_mul_of_nonneg_right hcardReal hcommonNonneg
    _ = (mix * B₁ * W ^ (r - 1) +
          ((r : ℝ) * 2 * mix) * B₂ * W ^ (r - 1)) /
        (L : ℝ) := by
      rw [hcommonRewrite, mul_add, hcancel₁, hcancel₂]
      ring
    _ = ((1 + gaussDigitExponentialRate gap) ^ (r - 1) *
            (12 * A ^ 2 / Real.log 2) *
            ((2 * A + 10 * A ^ 2) / Real.log 2) ^ (r - 1) +
          ((r : ℝ) * 2 *
            (1 + gaussDigitExponentialRate gap) ^ (r - 1)) *
            (26 * A ^ 2 / Real.log 2) *
            ((2 * A + 10 * A ^ 2) / Real.log 2) ^ (r - 1)) /
        (L : ℝ) := by rfl

/-- The absolute sum of exact heterogeneous boundary-tuple masses tends to
zero for any fixed parity block. -/
theorem tendsto_sum_gaussMeasure_real_heterogeneousBoundaryFinTuples_zero
    {r : ℕ} (hr : 0 < r) {A center : ℝ}
    (lower upper : ℕ → Fin r → ℝ)
    (tuples : ∀ L : ℕ, Finset (Fin r → Fin L))
    (eta : ℕ → ℝ) (j : Fin r) (gap : ℕ) (hgap0 : 0 < gap)
    (hA : 0 ≤ A) (hcenter : 0 < center) (hcenterA : center ≤ A)
    (heta : ∀ᶠ L : ℕ in Filter.atTop,
      0 < eta L ∧ 2 * eta L ≤ center ∧ eta L * (L : ℝ) ≤ A ^ 2)
    (hlower : ∀ L i, 0 < lower L i)
    (hupper : ∀ L i, lower L i < upper L i)
    (hupperA : ∀ L i, upper L i ≤ A)
    (hjLower : ∀ L, lower L j = center - eta L)
    (hjUpper : ∀ L, upper L j = center + eta L)
    (hlarge : ∀ᶠ L : ℕ in Filter.atTop,
      ∀ i, 16 * (upper L i) ^ 2 ≤ lower L i * (L : ℝ))
    (hgap : ∀ L, ∀ times ∈ tuples L, ∀ i k, i < k →
      (times i).1 + gap ≤ (times k).1) :
    Tendsto
      (fun L : ℕ ↦
        ∑ times ∈ tuples L,
          gaussMeasure.real
            (gaussHeterogeneousApproximationTupleEvent
              (L : ℝ) (lower L) (upper L) (fun i ↦ (times i).1)))
      Filter.atTop (𝓝 0) := by
  let F : ℕ → ℝ := fun L ↦
    ∑ times ∈ tuples L,
      gaussMeasure.real
        (gaussHeterogeneousApproximationTupleEvent
          (L : ℝ) (lower L) (upper L) (fun i ↦ (times i).1))
  let C : ℝ :=
    (1 + gaussDigitExponentialRate gap) ^ (r - 1) *
          (12 * A ^ 2 / Real.log 2) *
          ((2 * A + 10 * A ^ 2) / Real.log 2) ^ (r - 1) +
      ((r : ℝ) * 2 *
        (1 + gaussDigitExponentialRate gap) ^ (r - 1)) *
          (26 * A ^ 2 / Real.log 2) *
          ((2 * A + 10 * A ^ 2) / Real.log 2) ^ (r - 1)
  have hFnonneg : ∀ L, 0 ≤ F L := by
    intro L
    exact Finset.sum_nonneg fun _times _htimes ↦ measureReal_nonneg
  have hupperEventually : ∀ᶠ L : ℕ in Filter.atTop,
      F L ≤ C / (L : ℝ) := by
    filter_upwards [heta, hlarge, Filter.eventually_gt_atTop 0] with
        L hetaL hlargeL hL
    exact sum_gaussMeasure_real_heterogeneousBoundaryFinTuples_le_const_div
      hr hL (lower L) (upper L) (tuples L) j gap hgap0 hA hcenter hcenterA
        hetaL.1 hetaL.2.1 hetaL.2.2 (hlower L) (hupper L) (hupperA L)
        (hjLower L) (hjUpper L) hlargeL (hgap L)
  have hCdiv : Tendsto (fun L : ℕ ↦ C / (L : ℝ))
      Filter.atTop (𝓝 0) := by
    exact tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  exact squeeze_zero' (Filter.Eventually.of_forall hFnonneg)
    hupperEventually hCdiv

/-- Generic transfer of an absolutely summed event-family estimate from
Gauss measure to uniform Lebesgue measure. -/
theorem tendsto_sum_uniform01MeasureReal_zero_of_gaussMeasureReal
    {r : ℕ} (tuples : ∀ L : ℕ, Finset (Fin r → Fin L))
    (events : ∀ L : ℕ, (Fin r → Fin L) → Set ℝ)
    (hmeasurable : ∀ L times, times ∈ tuples L →
      MeasurableSet (events L times))
    (hgauss : Tendsto
      (fun L : ℕ ↦ ∑ times ∈ tuples L,
        gaussMeasure.real (events L times))
      Filter.atTop (𝓝 0)) :
    Tendsto
      (fun L : ℕ ↦ ∑ times ∈ tuples L,
        uniform01Measure.real (events L times))
      Filter.atTop (𝓝 0) := by
  let F : ℕ → ℝ := fun L ↦ ∑ times ∈ tuples L,
    uniform01Measure.real (events L times)
  let G : ℕ → ℝ := fun L ↦ ∑ times ∈ tuples L,
    gaussMeasure.real (events L times)
  have hFnonneg : ∀ L, 0 ≤ F L := by
    intro L
    exact Finset.sum_nonneg fun _times _htimes ↦ measureReal_nonneg
  have hupper : ∀ L, F L ≤ (2 * Real.log 2) * G L := by
    intro L
    dsimp only [F, G]
    calc
      (∑ times ∈ tuples L,
          uniform01Measure.real (events L times)) ≤
          ∑ times ∈ tuples L,
            (2 * Real.log 2) * gaussMeasure.real (events L times) := by
        apply Finset.sum_le_sum
        intro times htimes
        exact uniform01MeasureReal_le_gaussMeasureReal
          (hmeasurable L times htimes)
      _ = (2 * Real.log 2) *
          ∑ times ∈ tuples L,
            gaussMeasure.real (events L times) := by
        rw [Finset.mul_sum]
  have hscaled : Tendsto (fun L ↦ (2 * Real.log 2) * G L)
      Filter.atTop (𝓝 0) := by
    simpa only [mul_zero] using! tendsto_const_nhds.mul hgauss
  exact squeeze_zero' (Filter.Eventually.of_forall hFnonneg)
    (Filter.Eventually.of_forall hupper) hscaled

/-- Uniform-measure specialization for heterogeneous exact approximation
tuples. -/
theorem tendsto_sum_uniform01Measure_real_heterogeneousTuples_zero_of_gauss
    {r : ℕ} (lower upper : ℕ → Fin r → ℝ)
    (tuples : ∀ L : ℕ, Finset (Fin r → Fin L))
    (hgauss : Tendsto
      (fun L : ℕ ↦ ∑ times ∈ tuples L,
        gaussMeasure.real
          (gaussHeterogeneousApproximationTupleEvent
            (L : ℝ) (lower L) (upper L) (fun i ↦ (times i).1)))
      Filter.atTop (𝓝 0)) :
    Tendsto
      (fun L : ℕ ↦ ∑ times ∈ tuples L,
        uniform01Measure.real
          (gaussHeterogeneousApproximationTupleEvent
            (L : ℝ) (lower L) (upper L) (fun i ↦ (times i).1)))
      Filter.atTop (𝓝 0) := by
  exact tendsto_sum_uniform01MeasureReal_zero_of_gaussMeasureReal
    tuples
    (fun L times ↦ gaussHeterogeneousApproximationTupleEvent
      (L : ℝ) (lower L) (upper L) (fun i ↦ (times i).1))
    (fun L times _htimes ↦
      measurableSet_gaussHeterogeneousApproximationTupleEvent
        (L : ℝ) (lower L) (upper L) (fun i ↦ (times i).1))
    hgauss

/-- Summing the explicit tuplewise bound over an arbitrary finite retained
family keeps the absolute value inside that family sum. -/
theorem sum_gaussMeasure_real_symmDiff_heterogeneousTuples_le_explicit
    {r : ℕ} (hr : 0 < r) {scale A : ℝ}
    (lower upper : Fin r → ℝ)
    (tuples : Finset (Fin r → ℕ))
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
          gaussHeterogeneousDigitWindowTupleEvent
            scale lower upper times)) ≤
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
            gaussHeterogeneousDigitWindowTupleEvent
              scale lower upper times)) ≤
        ∑ _times ∈ tuples, common := by
      apply Finset.sum_le_sum
      intro times htimes
      exact gaussMeasure_real_symmDiff_heterogeneousTuples_le_explicit
        hr lower upper times gap hgap0 hscale hscaleOne hA hlower hupper
          hupperA hlarge (hgap times htimes)
    _ = (tuples.card : ℝ) * common := by simp

/-- At the natural factorial scale, every finite family of heterogeneous
`r`-tuples is bounded by an explicit constant divided by the horizon.  The
ambient cardinality `L^r` is proved internally. -/
theorem sum_gaussMeasure_real_symmDiff_heterogeneousFinTuples_le_const_div
    {r L : ℕ} (hr : 0 < r) (hL : 0 < L) {A : ℝ}
    (lower upper : Fin r → ℝ)
    (tuples : Finset (Fin r → Fin L))
    (gap : ℕ) (hgap0 : 0 < gap)
    (hA : 0 ≤ A)
    (hlower : ∀ i, 0 < lower i)
    (hupper : ∀ i, lower i < upper i)
    (hupperA : ∀ i, upper i ≤ A)
    (hlarge : ∀ i, 16 * (upper i) ^ 2 ≤ lower i * (L : ℝ))
    (hgap : ∀ times ∈ tuples, ∀ i k, i < k →
      (times i).1 + gap ≤ (times k).1) :
    (∑ times ∈ tuples,
      gaussMeasure.real
        (gaussHeterogeneousApproximationTupleEvent
            (L : ℝ) lower upper (fun i ↦ (times i).1) ∆
          gaussHeterogeneousDigitWindowTupleEvent
            (L : ℝ) lower upper (fun i ↦ (times i).1))) ≤
      ((r : ℝ) * 2 *
          (1 + gaussDigitExponentialRate gap) ^ (r - 1) *
          (26 * A ^ 2 / Real.log 2) *
          ((2 * A + 10 * A ^ 2) / Real.log 2) ^ (r - 1)) /
        (L : ℝ) := by
  let B : ℝ := 26 * A ^ 2 / Real.log 2
  let W : ℝ := (2 * A + 10 * A ^ 2) / Real.log 2
  let mix : ℝ := (1 + gaussDigitExponentialRate gap) ^ (r - 1)
  let common : ℝ :=
    (r : ℝ) *
      (2 * (mix *
        (((26 * A ^ 2 / (L : ℝ) ^ 2) / Real.log 2) *
          (((2 * A + 10 * A ^ 2) / (L : ℝ)) /
            Real.log 2) ^ (r - 1))))
  have hterm (times : Fin r → Fin L) (htimes : times ∈ tuples) :
      gaussMeasure.real
          (gaussHeterogeneousApproximationTupleEvent
              (L : ℝ) lower upper (fun i ↦ (times i).1) ∆
            gaussHeterogeneousDigitWindowTupleEvent
              (L : ℝ) lower upper (fun i ↦ (times i).1)) ≤ common := by
    simpa only [common, mix] using!
      gaussMeasure_real_symmDiff_heterogeneousTuples_le_explicit
        hr lower upper (fun i ↦ (times i).1) gap hgap0
          (by exact_mod_cast hL) (by exact_mod_cast hL) hA hlower hupper
          hupperA hlarge (hgap times htimes)
  have hcardNat : tuples.card ≤ L ^ r := by
    have h := Finset.card_le_univ tuples
    simpa only [Fintype.card_fun, Fintype.card_fin] using! h
  have hcardReal : (tuples.card : ℝ) ≤ (L : ℝ) ^ r := by
    exact_mod_cast hcardNat
  have hrateFactor : 0 ≤ 1 + gaussDigitExponentialRate gap := by
    linarith [gaussDigitExponentialRate_nonnegative gap]
  have hcommon : 0 ≤ common := by
    dsimp only [common, mix]
    have hlog : 0 < Real.log 2 := Real.log_pos one_lt_two
    have hWnum : 0 ≤ 2 * A + 10 * A ^ 2 := by nlinarith [sq_nonneg A]
    positivity
  have hlogNe : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos one_lt_two)
  have hLne : (L : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hL)
  have hboundaryRewrite :
      (26 * A ^ 2 / (L : ℝ) ^ 2) / Real.log 2 =
        B / (L : ℝ) ^ 2 := by
    dsimp only [B]
    field_simp
  have hwindowRewrite :
      ((2 * A + 10 * A ^ 2) / (L : ℝ)) / Real.log 2 =
        W / (L : ℝ) := by
    dsimp only [W]
    field_simp
  have hcancel := factorialTupleScaleCancellation hr hL mix B W
  calc
    (∑ times ∈ tuples,
      gaussMeasure.real
        (gaussHeterogeneousApproximationTupleEvent
            (L : ℝ) lower upper (fun i ↦ (times i).1) ∆
          gaussHeterogeneousDigitWindowTupleEvent
            (L : ℝ) lower upper (fun i ↦ (times i).1))) ≤
        ∑ _times ∈ tuples, common := by
      exact Finset.sum_le_sum hterm
    _ = (tuples.card : ℝ) * common := by simp
    _ ≤ (L : ℝ) ^ r * common :=
      mul_le_mul_of_nonneg_right hcardReal hcommon
    _ = ((r : ℝ) * 2 * mix * B * W ^ (r - 1)) / (L : ℝ) := by
      dsimp only [common]
      rw [hboundaryRewrite, hwindowRewrite]
      exact hcancel
    _ = ((r : ℝ) * 2 *
          (1 + gaussDigitExponentialRate gap) ^ (r - 1) *
          (26 * A ^ 2 / Real.log 2) *
          ((2 * A + 10 * A ^ 2) / Real.log 2) ^ (r - 1)) /
        (L : ℝ) := by rfl

/-- Sequence-level `o(1)` heterogeneous replacement.  The large-scale
window condition is kept as an eventual hypothesis because applications
may use different fixed signed rectangles. -/
theorem tendsto_sum_gaussMeasure_real_symmDiff_heterogeneousFinTuples_zero
    {r : ℕ} (hr : 0 < r) {A : ℝ}
    (lower upper : Fin r → ℝ)
    (tuples : ∀ L : ℕ, Finset (Fin r → Fin L))
    (gap : ℕ) (hgap0 : 0 < gap)
    (hA : 0 ≤ A)
    (hlower : ∀ i, 0 < lower i)
    (hupper : ∀ i, lower i < upper i)
    (hupperA : ∀ i, upper i ≤ A)
    (hlarge : ∀ᶠ L : ℕ in Filter.atTop,
      ∀ i, 16 * (upper i) ^ 2 ≤ lower i * (L : ℝ))
    (hgap : ∀ L, ∀ times ∈ tuples L, ∀ i k, i < k →
      (times i).1 + gap ≤ (times k).1) :
    Tendsto
      (fun L : ℕ ↦
        ∑ times ∈ tuples L,
          gaussMeasure.real
            (gaussHeterogeneousApproximationTupleEvent
                (L : ℝ) lower upper (fun i ↦ (times i).1) ∆
              gaussHeterogeneousDigitWindowTupleEvent
                (L : ℝ) lower upper (fun i ↦ (times i).1)))
      Filter.atTop (𝓝 0) := by
  let F : ℕ → ℝ := fun L ↦
    ∑ times ∈ tuples L,
      gaussMeasure.real
        (gaussHeterogeneousApproximationTupleEvent
            (L : ℝ) lower upper (fun i ↦ (times i).1) ∆
          gaussHeterogeneousDigitWindowTupleEvent
            (L : ℝ) lower upper (fun i ↦ (times i).1))
  let C : ℝ :=
    (r : ℝ) * 2 *
      (1 + gaussDigitExponentialRate gap) ^ (r - 1) *
      (26 * A ^ 2 / Real.log 2) *
      ((2 * A + 10 * A ^ 2) / Real.log 2) ^ (r - 1)
  have hFnonneg : ∀ L, 0 ≤ F L := by
    intro L
    exact Finset.sum_nonneg fun _times _htimes ↦ measureReal_nonneg
  have hupperEventually : ∀ᶠ L : ℕ in Filter.atTop,
      F L ≤ C / (L : ℝ) := by
    filter_upwards [hlarge, Filter.eventually_gt_atTop 0] with L hlargeL hL
    exact sum_gaussMeasure_real_symmDiff_heterogeneousFinTuples_le_const_div
      hr hL lower upper (tuples L) gap hgap0 hA hlower hupper hupperA
        hlargeL (hgap L)
  have hCdiv : Tendsto (fun L : ℕ ↦ C / (L : ℝ))
      Filter.atTop (𝓝 0) := by
    exact tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  exact squeeze_zero' (Filter.Eventually.of_forall hFnonneg)
    hupperEventually hCdiv

end

end Erdos1002
