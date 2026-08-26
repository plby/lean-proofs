import ErdosProblems.Erdos1002.GaussApproximationCoordinate
import ErdosProblems.Erdos1002.RareEventMixing
import ErdosProblems.Erdos1002.FactorialEventExpansion

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Factorial-tuple replacement for Gauss approximation coordinates

This module upgrades the one-time boundary estimate to fixed-order tuple
intersections.  The deterministic part is unconditional.  The sole dynamical
input is `GaussDigitPsiMixing`: a precise event-level relative-mixing
statement for one-digit events pulled back to Gauss times separated by a
positive gap.  The later module `GaussDigitQuasiBernoulli` proves this
interface with the uniform rate `5`.  A rate tending to zero would be the
strictly stronger classical Gauss `psi`-mixing input and is not proved here.

Given that input, iterated relative mixing bounds a tuple containing one
`O(scale^-2)` boundary strip and `r-1` ordinary `O(scale^-1)` rare windows by
`O(scale^(-r-1))`.  Summing over all `O(scale^r)` fixed-order tuples is then
`O(scale^-1)`.  The same argument with gap one controls the close-time
subfamily separately; no independence is asserted at short gaps.
-/

open Filter MeasureTheory Set Finset
open scoped BigOperators ENNReal Topology symmDiff

namespace Erdos1002

noncomputable section

/-! ## The single external dynamical input -/

/-- A genuinely one-digit event: on the Gauss state space it is determined
solely by `a₁`.  Keeping this predicate explicit is essential.  Allowing an
arbitrary Borel set of the complete tail `T^n x` would make successive
sigma-fields overlap and would be much stronger than classical digit
`psi`-mixing. -/
def IsGaussOneDigitEvent (A : Set ℝ) : Prop :=
  ∃ digits : Set ℕ,
    A = Ioc (0 : ℝ) 1 ∩ gaussFirstDigitNat ⁻¹' digits

theorem isGaussOneDigitEvent_scaledGaussFirstDigitWindow
    (scale lower upper : ℝ) :
    IsGaussOneDigitEvent
      (scaledGaussFirstDigitWindow scale lower upper) := by
  refine ⟨{q : ℕ | lower ≤ scale / (q : ℝ) ∧
      scale / (q : ℝ) ≤ upper}, ?_⟩
  ext x
  simp only [scaledGaussFirstDigitWindow, mem_setOf_eq, mem_inter_iff,
    Set.mem_preimage]

theorem isGaussOneDigitEvent_scaledGaussFirstDigitBoundaryStrip
    (scale center width : ℝ) :
    IsGaussOneDigitEvent
      (scaledGaussFirstDigitBoundaryStrip scale center width) := by
  rw [scaledGaussFirstDigitBoundaryStrip_eq_window]
  exact isGaussOneDigitEvent_scaledGaussFirstDigitWindow _ _ _

/-- Event-level relative mixing for the stationary Gauss digit process.

`times` is already in chronological order, and `hgap` says that every later
time is at least the positive number `gap` after every earlier time.  The
positivity hypothesis is essential: repeated rare events at the same time
have no finite uniform relative-error bound.  The returned recursive
record is exactly the object consumed by `RareEventMixing`; all its errors are
bounded by `rate gap`.  This definition is the unique conditional interface
in this file. -/
def GaussDigitPsiMixing (rate : ℕ → ℝ) : Prop :=
  ∀ {r : ℕ} (times : Fin r → ℕ) (events : Fin r → Set ℝ) (gap : ℕ),
    (∀ i, MeasurableSet (events i)) →
    (∀ i, IsGaussOneDigitEvent (events i)) →
    0 < gap →
    (∀ i j, i < j → times i + gap ≤ times j) →
    ∃ errors : List ℝ,
      SequentialEventRelativeMixing gaussMeasure errors
        (List.ofFn fun i =>
          (gaussOrbit (times i)) ⁻¹' events i) ∧
      ∀ epsilon ∈ errors, 0 ≤ epsilon ∧ epsilon ≤ rate gap

/-- An `ofFn` intersection is membership in every indexed event. -/
theorem mem_orderedEventIntersection_ofFn_iff
    {Ω : Type*} {r : ℕ} {events : Fin r → Set Ω} {x : Ω} :
    x ∈ orderedEventIntersection (List.ofFn events) ↔
      ∀ i, x ∈ events i := by
  have hlist (l : List (Set Ω)) :
      x ∈ orderedEventIntersection l ↔ ∀ A ∈ l, x ∈ A := by
    induction l with
    | nil => simp
    | cons A l ih => simp [orderedEventIntersection, ih]
  rw [hlist]
  constructor
  · intro h i
    exact h (events i) (List.mem_ofFn.mpr ⟨i, rfl⟩)
  · intro h A hA
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hA
    exact h i

theorem orderedEventIntersection_ofFn
    {Ω : Type*} {r : ℕ} (events : Fin r → Set Ω) :
    orderedEventIntersection (List.ofFn events) = ⋂ i, events i := by
  ext x
  rw [mem_orderedEventIntersection_ofFn_iff, mem_iInter]

/-- Direct bridge to the tuple convention used by
`integral_finiteEventCount_descFactorial`. -/
theorem orderedEventIntersection_embedding_eq_tupleEvent
    {Ω I : Type*} {s : Finset I} {r : ℕ}
    (E : I → Set Ω) (f : Fin r ↪ s) :
    orderedEventIntersection (List.ofFn fun i => E (f i)) =
      tupleEvent E f := by
  rw [orderedEventIntersection_ofFn]
  rfl

/-- `GaussDigitPsiMixing` plus the generic iterated-mixing theorem gives the
literal finite product bound needed for a tuple. -/
theorem GaussDigitPsiMixing.measure_orderedIntersection_le
    {rate : ℕ → ℝ} (hpsi : GaussDigitPsiMixing rate)
    {r : ℕ} (hr : 0 < r) (times : Fin r → ℕ)
    (events : Fin r → Set ℝ) (gap : ℕ)
    (hEvents : ∀ i, MeasurableSet (events i))
    (hOneDigit : ∀ i, IsGaussOneDigitEvent (events i))
    (hgap0 : 0 < gap)
    (hgap : ∀ i j, i < j → times i + gap ≤ times j)
    (hrate : 0 ≤ rate gap) :
    gaussMeasure.real
        (orderedEventIntersection (List.ofFn fun i =>
          (gaussOrbit (times i)) ⁻¹' events i)) ≤
      (1 + rate gap) ^ (r - 1) *
        ∏ i, gaussMeasure.real (events i) := by
  obtain ⟨errors, hmix, herrors⟩ :=
    hpsi times events gap hEvents hOneDigit hgap0 hgap
  have hne :
      (List.ofFn fun i => (gaussOrbit (times i)) ⁻¹' events i) ≠ [] := by
    intro hempty
    have hlen := congrArg List.length hempty
    simp only [List.length_ofFn, List.length_nil] at hlen
    omega
  have hlength := hmix.length_errors_add_one hne
  have herrorLength : errors.length = r - 1 := by
    simp only [List.length_ofFn] at hlength
    omega
  have hbound := hmix.measure_intersection_le_pow gaussMeasure hrate herrors
  rw [herrorLength] at hbound
  calc
    gaussMeasure.real
        (orderedEventIntersection (List.ofFn fun i =>
          (gaussOrbit (times i)) ⁻¹' events i)) ≤
        (1 + rate gap) ^ (r - 1) *
          eventProbabilityProduct gaussMeasure
            (List.ofFn fun i =>
              (gaussOrbit (times i)) ⁻¹' events i) := hbound
    _ = (1 + rate gap) ^ (r - 1) *
        ∏ i, gaussMeasure.real (events i) := by
      congr 1
      simp only [eventProbabilityProduct, List.map_ofFn, Function.comp_apply,
        List.prod_ofFn]
      apply Finset.prod_congr rfl
      intro i _hi
      exact gaussMeasure_real_gaussOrbit_preimage (times i) (hEvents i)

/-- Product estimate when one distinguished event has mass at most
`boundaryMass` and every other event has mass at most `windowMass`. -/
theorem fin_prod_measure_le_boundary_mul_window_pow
    {r : ℕ} (events : Fin r → Set ℝ) (j : Fin r)
    {boundaryMass windowMass : ℝ}
    (hboundaryMass : 0 ≤ boundaryMass)
    (hboundary : gaussMeasure.real (events j) ≤ boundaryMass)
    (hwindow : ∀ i, i ≠ j →
      gaussMeasure.real (events i) ≤ windowMass) :
    (∏ i, gaussMeasure.real (events i)) ≤
      boundaryMass * windowMass ^ (r - 1) := by
  have hj : j ∈ (Finset.univ : Finset (Fin r)) := Finset.mem_univ j
  rw [← Finset.mul_prod_erase (Finset.univ : Finset (Fin r))
    (fun i => gaussMeasure.real (events i)) hj]
  calc
    gaussMeasure.real (events j) *
        ∏ i ∈ (Finset.univ : Finset (Fin r)).erase j,
          gaussMeasure.real (events i) ≤
      boundaryMass *
        ∏ _i ∈ (Finset.univ : Finset (Fin r)).erase j,
          windowMass := by
      apply mul_le_mul hboundary
      · apply Finset.prod_le_prod
        · intro i hi
          exact measureReal_nonneg
        · intro i hi
          exact hwindow i (Finset.ne_of_mem_erase hi)
      · exact Finset.prod_nonneg fun _ _ => measureReal_nonneg
      · exact hboundaryMass
    _ = boundaryMass * windowMass ^ (r - 1) := by
      rw [Finset.prod_const, Finset.card_erase_of_mem hj, Finset.card_univ,
        Fintype.card_fin]

/-! ## Deterministic tuple replacement -/

/-- The coordinate witness used in the telescoping symmetric-difference
inclusion: coordinate `j` mismatches, while all other coordinates lie in the
union of their old and new events. -/
def coordinateReplacementWitness
    {Ω : Type*} {r : ℕ} (E D : Fin r → Set Ω) (j : Fin r) : Set Ω :=
  orderedEventIntersection <| List.ofFn fun i =>
    if i = j then E i ∆ D i else E i ∪ D i

/-- Symmetric difference of two finite intersections is contained in the
union of the coordinate replacement witnesses. -/
theorem symmDiff_orderedIntersections_subset_iUnion_witness
    {Ω : Type*} {r : ℕ} (E D : Fin r → Set Ω) :
    orderedEventIntersection (List.ofFn E) ∆
        orderedEventIntersection (List.ofFn D) ⊆
      ⋃ j, coordinateReplacementWitness E D j := by
  intro x hx
  rw [mem_symmDiff] at hx
  rcases hx with ⟨hE, hD⟩ | ⟨hD, hE⟩
  · have hEall := mem_orderedEventIntersection_ofFn_iff.mp hE
    have hnot : ¬ ∀ i, x ∈ D i := by
      intro hall
      exact hD (mem_orderedEventIntersection_ofFn_iff.mpr hall)
    obtain ⟨j, hj⟩ := not_forall.mp hnot
    apply mem_iUnion.mpr
    refine ⟨j, mem_orderedEventIntersection_ofFn_iff.mpr ?_⟩
    intro i
    by_cases hij : i = j
    · subst i
      simpa using! (Or.inl ⟨hEall j, hj⟩)
    · simp only [if_neg hij, mem_union]
      exact Or.inl (hEall i)
  · have hDall := mem_orderedEventIntersection_ofFn_iff.mp hD
    have hnot : ¬ ∀ i, x ∈ E i := by
      intro hall
      exact hE (mem_orderedEventIntersection_ofFn_iff.mpr hall)
    obtain ⟨j, hj⟩ := not_forall.mp hnot
    apply mem_iUnion.mpr
    refine ⟨j, mem_orderedEventIntersection_ofFn_iff.mpr ?_⟩
    intro i
    by_cases hij : i = j
    · subst i
      simpa using! (Or.inr ⟨hDall j, hj⟩)
    · simp only [if_neg hij, mem_union]
      exact Or.inr (hDall i)

/-! ## Specialization to exact and digit continued-fraction windows -/

/-- The digit window enlarged just enough to contain the exact window after
the deterministic replacement. -/
def gaussEnlargedDigitWindow
    (scale lower upper : ℝ) : Set ℝ :=
  scaledGaussFirstDigitWindow scale lower
    (upper + 8 * upper ^ 2 / scale)

/-- The union of the exact and digit events is, off the terminating null set,
contained in the enlarged one-digit window. -/
theorem union_gaussApproximationWindow_gaussDigitWindowAt_subset
    {scale lower upper : ℝ} {n : ℕ}
    (hscale : 0 < scale) (hlower : 0 < lower) (hupper : lower < upper)
    (hlarge : 16 * upper ^ 2 ≤ lower * scale) :
    gaussApproximationWindow scale n lower upper ∪
        gaussDigitWindowAt scale n lower upper ⊆
      gaussPrefixExceptional (n + 1) ∪
        (gaussOrbit n) ⁻¹' gaussEnlargedDigitWindow scale lower upper := by
  intro x hxevent
  by_cases hex : x ∈ gaussPrefixExceptional (n + 1)
  · exact Or.inl hex
  right
  have hx : x ∈ Ioc (0 : ℝ) 1 := by
    rcases hxevent with he | hd
    · exact (mem_gaussApproximationWindow_iff.mp he).1
    · exact (mem_gaussDigitWindowAt_iff.mp hd).1
  have horbit := gaussOrbit_mem_Ioc_of_not_mem_exceptional
    (b := n + 1) (k := n) hx hex (by omega)
  have hlarge' : 4 * upper ≤ scale := by
    have hupper0 : 0 < upper := hlower.trans hupper
    have hmul : lower * scale ≤ upper * scale :=
      mul_le_mul_of_nonneg_right hupper.le hscale.le
    nlinarith [hlarge.trans hmul]
  have hdigitBounds :
      lower ≤ gaussScaledDigitCoordinate scale n x ∧
        gaussScaledDigitCoordinate scale n x ≤
          upper + 8 * upper ^ 2 / scale := by
    rcases hxevent with he | hd
    · have heBounds := (mem_gaussApproximationWindow_iff.mp he).2
      have herr := gaussScaledApproximation_digit_error_uniform
        hscale (hlower.trans hupper) hlarge' hx hex (Or.inl heBounds)
      constructor
      · linarith [heBounds.1, herr.1]
      · linarith [heBounds.2, herr.2]
    · have hdBounds := (mem_gaussDigitWindowAt_iff.mp hd).2.2
      exact ⟨hdBounds.1, hdBounds.2.trans (le_add_of_nonneg_right (by positivity))⟩
  change gaussOrbit n x ∈ Ioc (0 : ℝ) 1 ∧
    lower ≤ scale / (gaussFirstDigitNat (gaussOrbit n x) : ℝ) ∧
    scale / (gaussFirstDigitNat (gaussOrbit n x) : ℝ) ≤
      upper + 8 * upper ^ 2 / scale
  exact ⟨horbit, hdigitBounds⟩

/-- Exact tuple event for a chronological vector of times. -/
def gaussApproximationTupleEvent
    {r : ℕ} (scale lower upper : ℝ) (times : Fin r → ℕ) : Set ℝ :=
  orderedEventIntersection <| List.ofFn fun i =>
    gaussApproximationWindow scale (times i) lower upper

/-- Digit-only tuple event for the same vector of times. -/
def gaussDigitTupleEvent
    {r : ℕ} (scale lower upper : ℝ) (times : Fin r → ℕ) : Set ℝ :=
  orderedEventIntersection <| List.ofFn fun i =>
    gaussDigitWindowAt scale (times i) lower upper

theorem gaussApproximationTupleEvent_embedding_eq_tupleEvent
    {s : Finset ℕ} {r : ℕ} (scale lower upper : ℝ)
    (f : Fin r ↪ s) :
    gaussApproximationTupleEvent scale lower upper (fun i => (f i : ℕ)) =
      tupleEvent (fun n => gaussApproximationWindow scale n lower upper) f := by
  unfold gaussApproximationTupleEvent
  simpa using! (orderedEventIntersection_embedding_eq_tupleEvent
    (Ω := ℝ) (fun n : ℕ => gaussApproximationWindow scale n lower upper) f)

theorem gaussDigitTupleEvent_embedding_eq_tupleEvent
    {s : Finset ℕ} {r : ℕ} (scale lower upper : ℝ)
    (f : Fin r ↪ s) :
    gaussDigitTupleEvent scale lower upper (fun i => (f i : ℕ)) =
      tupleEvent (fun n => gaussDigitWindowAt scale n lower upper) f := by
  unfold gaussDigitTupleEvent
  simpa using! (orderedEventIntersection_embedding_eq_tupleEvent
    (Ω := ℝ) (fun n : ℕ => gaussDigitWindowAt scale n lower upper) f)

/-- Finite union of the terminating-prefix exceptional sets relevant to one
tuple. -/
def gaussTupleExceptional {r : ℕ} (times : Fin r → ℕ) : Set ℝ :=
  ⋃ i, gaussPrefixExceptional (times i + 1)

theorem gaussMeasure_gaussTupleExceptional
    {r : ℕ} (times : Fin r → ℕ) :
    gaussMeasure (gaussTupleExceptional times) = 0 := by
  exact measure_iUnion_null fun i =>
    gaussMeasure_gaussPrefixExceptional (times i + 1)

theorem gaussMeasure_real_gaussTupleExceptional
    {r : ℕ} (times : Fin r → ℕ) :
    gaussMeasure.real (gaussTupleExceptional times) = 0 := by
  simp only [measureReal_def, gaussMeasure_gaussTupleExceptional,
    ENNReal.toReal_zero]

/-- A pure one-digit tuple with a boundary strip at `j` and enlarged rare
windows at every other coordinate. -/
def gaussBoundaryDigitBaseEvent
    {r : ℕ} (scale lower upper center : ℝ) (j : Fin r) (i : Fin r) : Set ℝ :=
  if i = j then
    scaledGaussFirstDigitBoundaryStrip scale center (8 * upper ^ 2)
  else gaussEnlargedDigitWindow scale lower upper

def gaussBoundaryDigitTupleEvent
    {r : ℕ} (scale lower upper center : ℝ)
    (times : Fin r → ℕ) (j : Fin r) : Set ℝ :=
  orderedEventIntersection <| List.ofFn fun i =>
    (gaussOrbit (times i)) ⁻¹'
      gaussBoundaryDigitBaseEvent scale lower upper center j i

theorem measurableSet_gaussEnlargedDigitWindow
    (scale lower upper : ℝ) :
    MeasurableSet (gaussEnlargedDigitWindow scale lower upper) := by
  exact measurableSet_scaledGaussFirstDigitWindow _ _ _

theorem isGaussOneDigitEvent_gaussEnlargedDigitWindow
    (scale lower upper : ℝ) :
    IsGaussOneDigitEvent (gaussEnlargedDigitWindow scale lower upper) := by
  exact isGaussOneDigitEvent_scaledGaussFirstDigitWindow _ _ _

theorem measurableSet_gaussBoundaryDigitBaseEvent
    {r : ℕ} (scale lower upper center : ℝ) (j i : Fin r) :
    MeasurableSet
      (gaussBoundaryDigitBaseEvent scale lower upper center j i) := by
  by_cases hij : i = j
  · simp only [gaussBoundaryDigitBaseEvent, if_pos hij]
    exact measurableSet_scaledGaussFirstDigitBoundaryStrip _ _ _
  · simp only [gaussBoundaryDigitBaseEvent, if_neg hij]
    exact measurableSet_gaussEnlargedDigitWindow _ _ _

theorem isGaussOneDigitEvent_gaussBoundaryDigitBaseEvent
    {r : ℕ} (scale lower upper center : ℝ) (j i : Fin r) :
    IsGaussOneDigitEvent
      (gaussBoundaryDigitBaseEvent scale lower upper center j i) := by
  by_cases hij : i = j
  · simp only [gaussBoundaryDigitBaseEvent, if_pos hij]
    exact isGaussOneDigitEvent_scaledGaussFirstDigitBoundaryStrip _ _ _
  · simp only [gaussBoundaryDigitBaseEvent, if_neg hij]
    exact isGaussOneDigitEvent_gaussEnlargedDigitWindow _ _ _

/-- Each coordinate replacement witness is covered by the tuple exceptional
set and the two pure one-digit boundary tuples. -/
theorem coordinateReplacementWitness_subset_gauss_boundary_tuples
    {r : ℕ} {scale lower upper : ℝ} (times : Fin r → ℕ) (j : Fin r)
    (hscale : 0 < scale) (hlower : 0 < lower) (hupper : lower < upper)
    (hlarge : 16 * upper ^ 2 ≤ lower * scale) :
    coordinateReplacementWitness
        (fun i => gaussApproximationWindow scale (times i) lower upper)
        (fun i => gaussDigitWindowAt scale (times i) lower upper) j ⊆
      gaussTupleExceptional times ∪
        (gaussBoundaryDigitTupleEvent scale lower upper lower times j ∪
          gaussBoundaryDigitTupleEvent scale lower upper upper times j) := by
  intro x hxWitness
  have hall := mem_orderedEventIntersection_ofFn_iff.mp hxWitness
  by_cases hexists : ∃ i, x ∈ gaussPrefixExceptional (times i + 1)
  · left
    exact mem_iUnion.mpr hexists
  right
  have hnotExceptional (i : Fin r) :
      x ∉ gaussPrefixExceptional (times i + 1) := by
    exact fun hi => hexists ⟨i, hi⟩
  have hjMismatch :
      x ∈ gaussApproximationWindow scale (times j) lower upper ∆
        gaussDigitWindowAt scale (times j) lower upper := by
    simpa using! hall j
  have hjCover :=
    symmDiff_gaussApproximationWindow_gaussDigitWindowAt_subset
      hscale hlower hupper hlarge hjMismatch
  have hjBoundary :
      x ∈ (gaussOrbit (times j)) ⁻¹'
          scaledGaussFirstDigitBoundaryStrip scale lower (8 * upper ^ 2) ∨
        x ∈ (gaussOrbit (times j)) ⁻¹'
          scaledGaussFirstDigitBoundaryStrip scale upper (8 * upper ^ 2) := by
    rcases hjCover with hjExceptional | hjBoundary
    · exact (hnotExceptional j hjExceptional).elim
    · exact hjBoundary
  have hother (i : Fin r) (hij : i ≠ j) :
      x ∈ (gaussOrbit (times i)) ⁻¹'
        gaussEnlargedDigitWindow scale lower upper := by
    have hiUnion :
        x ∈ gaussApproximationWindow scale (times i) lower upper ∪
          gaussDigitWindowAt scale (times i) lower upper := by
      simpa only [if_neg hij] using! hall i
    have hiCover :=
      union_gaussApproximationWindow_gaussDigitWindowAt_subset
        hscale hlower hupper hlarge hiUnion
    rcases hiCover with hiExceptional | hiWindow
    · exact (hnotExceptional i hiExceptional).elim
    · exact hiWindow
  rcases hjBoundary with hjLower | hjUpper
  · left
    apply mem_orderedEventIntersection_ofFn_iff.mpr
    intro i
    by_cases hij : i = j
    · subst i
      simpa [gaussBoundaryDigitTupleEvent, gaussBoundaryDigitBaseEvent] using! hjLower
    · simpa [gaussBoundaryDigitTupleEvent, gaussBoundaryDigitBaseEvent, hij] using! hother i hij
  · right
    apply mem_orderedEventIntersection_ofFn_iff.mpr
    intro i
    by_cases hij : i = j
    · subst i
      simpa [gaussBoundaryDigitTupleEvent, gaussBoundaryDigitBaseEvent] using! hjUpper
    · simpa [gaussBoundaryDigitTupleEvent, gaussBoundaryDigitBaseEvent, hij] using! hother i hij

/-! ## Tuple bounds from the mixing input -/

/-- A pure digit tuple with one distinguished boundary coordinate. -/
theorem gaussMeasure_real_gaussBoundaryDigitTupleEvent_le
    {rate : ℕ → ℝ} (hpsi : GaussDigitPsiMixing rate)
    {r : ℕ} (hr : 0 < r) {scale lower upper center : ℝ}
    (times : Fin r → ℕ) (j : Fin r) (gap : ℕ)
    (hgap0 : 0 < gap)
    (hgap : ∀ i k, i < k → times i + gap ≤ times k)
    (hrate : 0 ≤ rate gap)
    {boundaryMass windowMass : ℝ}
    (hboundaryMass : 0 ≤ boundaryMass)
    (hboundary :
      gaussMeasure.real
          (scaledGaussFirstDigitBoundaryStrip scale center (8 * upper ^ 2)) ≤
        boundaryMass)
    (hwindow :
      gaussMeasure.real (gaussEnlargedDigitWindow scale lower upper) ≤
        windowMass) :
    gaussMeasure.real
        (gaussBoundaryDigitTupleEvent scale lower upper center times j) ≤
      (1 + rate gap) ^ (r - 1) *
        (boundaryMass * windowMass ^ (r - 1)) := by
  let events : Fin r → Set ℝ := fun i =>
    gaussBoundaryDigitBaseEvent scale lower upper center j i
  have hEvents : ∀ i, MeasurableSet (events i) := by
    intro i
    exact measurableSet_gaussBoundaryDigitBaseEvent _ _ _ _ _ _
  have hOneDigit : ∀ i, IsGaussOneDigitEvent (events i) := by
    intro i
    exact isGaussOneDigitEvent_gaussBoundaryDigitBaseEvent _ _ _ _ _ _
  have hmix := hpsi.measure_orderedIntersection_le hr times events gap
    hEvents hOneDigit hgap0 hgap hrate
  have hproduct :
      (∏ i, gaussMeasure.real (events i)) ≤
        boundaryMass * windowMass ^ (r - 1) := by
    apply fin_prod_measure_le_boundary_mul_window_pow events j hboundaryMass
    · simpa only [events, gaussBoundaryDigitBaseEvent, if_pos rfl] using! hboundary
    · intro i hij
      simpa only [events, gaussBoundaryDigitBaseEvent, if_neg hij] using! hwindow
  have hmult : 0 ≤ (1 + rate gap) ^ (r - 1) := by positivity
  calc
    gaussMeasure.real
        (gaussBoundaryDigitTupleEvent scale lower upper center times j) ≤
        (1 + rate gap) ^ (r - 1) *
          ∏ i, gaussMeasure.real (events i) := by
      simpa only [gaussBoundaryDigitTupleEvent, events] using! hmix
    _ ≤ (1 + rate gap) ^ (r - 1) *
        (boundaryMass * windowMass ^ (r - 1)) :=
      mul_le_mul_of_nonneg_left hproduct hmult

/-- One coordinate witness has two possible endpoint strips.  The terminating
exceptional set has exactly zero measure. -/
theorem gaussMeasure_real_coordinateReplacementWitness_le
    {rate : ℕ → ℝ} (hpsi : GaussDigitPsiMixing rate)
    {r : ℕ} (hr : 0 < r) {scale lower upper : ℝ}
    (times : Fin r → ℕ) (j : Fin r) (gap : ℕ)
    (hgap0 : 0 < gap)
    (hscale : 0 < scale) (hlower : 0 < lower) (hupper : lower < upper)
    (hlarge : 16 * upper ^ 2 ≤ lower * scale)
    (hgap : ∀ i k, i < k → times i + gap ≤ times k)
    (hrate : 0 ≤ rate gap)
    {boundaryMass windowMass : ℝ}
    (hboundaryMass : 0 ≤ boundaryMass)
    (hboundaryLower :
      gaussMeasure.real
          (scaledGaussFirstDigitBoundaryStrip scale lower (8 * upper ^ 2)) ≤
        boundaryMass)
    (hboundaryUpper :
      gaussMeasure.real
          (scaledGaussFirstDigitBoundaryStrip scale upper (8 * upper ^ 2)) ≤
        boundaryMass)
    (hwindow :
      gaussMeasure.real (gaussEnlargedDigitWindow scale lower upper) ≤
        windowMass) :
    gaussMeasure.real
        (coordinateReplacementWitness
          (fun i => gaussApproximationWindow scale (times i) lower upper)
          (fun i => gaussDigitWindowAt scale (times i) lower upper) j) ≤
      2 * ((1 + rate gap) ^ (r - 1) *
        (boundaryMass * windowMass ^ (r - 1))) := by
  let P₀ := gaussBoundaryDigitTupleEvent scale lower upper lower times j
  let P₁ := gaussBoundaryDigitTupleEvent scale lower upper upper times j
  let Z := gaussTupleExceptional times
  have hcover :
      coordinateReplacementWitness
          (fun i => gaussApproximationWindow scale (times i) lower upper)
          (fun i => gaussDigitWindowAt scale (times i) lower upper) j ⊆
        Z ∪ (P₀ ∪ P₁) := by
    simpa only [Z, P₀, P₁] using!
      coordinateReplacementWitness_subset_gauss_boundary_tuples
        times j hscale hlower hupper hlarge
  have hP₀ := gaussMeasure_real_gaussBoundaryDigitTupleEvent_le
    hpsi hr times j gap hgap0 hgap hrate hboundaryMass hboundaryLower hwindow
  have hP₁ := gaussMeasure_real_gaussBoundaryDigitTupleEvent_le
    hpsi hr times j gap hgap0 hgap hrate hboundaryMass hboundaryUpper hwindow
  let common : ℝ := (1 + rate gap) ^ (r - 1) *
    (boundaryMass * windowMass ^ (r - 1))
  calc
    gaussMeasure.real
        (coordinateReplacementWitness
          (fun i => gaussApproximationWindow scale (times i) lower upper)
          (fun i => gaussDigitWindowAt scale (times i) lower upper) j) ≤
        gaussMeasure.real (Z ∪ (P₀ ∪ P₁)) := measureReal_mono hcover
    _ ≤ gaussMeasure.real Z + gaussMeasure.real (P₀ ∪ P₁) :=
      measureReal_union_le Z (P₀ ∪ P₁)
    _ = gaussMeasure.real (P₀ ∪ P₁) := by
      rw [show gaussMeasure.real Z = 0 by
        exact gaussMeasure_real_gaussTupleExceptional times]
      simp
    _ ≤ gaussMeasure.real P₀ + gaussMeasure.real P₁ :=
      measureReal_union_le P₀ P₁
    _ ≤ common + common := add_le_add (by simpa only [P₀, common] using! hP₀)
      (by simpa only [P₁, common] using! hP₁)
    _ = 2 * common := by ring

/-- Fixed-tuple replacement estimate. -/
theorem gaussMeasure_real_symmDiff_approximation_digit_tuple_le
    {rate : ℕ → ℝ} (hpsi : GaussDigitPsiMixing rate)
    {r : ℕ} (hr : 0 < r) {scale lower upper : ℝ}
    (times : Fin r → ℕ) (gap : ℕ)
    (hgap0 : 0 < gap)
    (hscale : 0 < scale) (hlower : 0 < lower) (hupper : lower < upper)
    (hlarge : 16 * upper ^ 2 ≤ lower * scale)
    (hgap : ∀ i k, i < k → times i + gap ≤ times k)
    (hrate : 0 ≤ rate gap)
    {boundaryMass windowMass : ℝ}
    (hboundaryMass : 0 ≤ boundaryMass)
    (hboundaryLower :
      gaussMeasure.real
          (scaledGaussFirstDigitBoundaryStrip scale lower (8 * upper ^ 2)) ≤
        boundaryMass)
    (hboundaryUpper :
      gaussMeasure.real
          (scaledGaussFirstDigitBoundaryStrip scale upper (8 * upper ^ 2)) ≤
        boundaryMass)
    (hwindow :
      gaussMeasure.real (gaussEnlargedDigitWindow scale lower upper) ≤
        windowMass) :
    gaussMeasure.real
        (gaussApproximationTupleEvent scale lower upper times ∆
          gaussDigitTupleEvent scale lower upper times) ≤
      (r : ℝ) *
        (2 * ((1 + rate gap) ^ (r - 1) *
          (boundaryMass * windowMass ^ (r - 1)))) := by
  let E : Fin r → Set ℝ := fun i =>
    gaussApproximationWindow scale (times i) lower upper
  let D : Fin r → Set ℝ := fun i =>
    gaussDigitWindowAt scale (times i) lower upper
  have hsubset :
      gaussApproximationTupleEvent scale lower upper times ∆
          gaussDigitTupleEvent scale lower upper times ⊆
        ⋃ j, coordinateReplacementWitness E D j := by
    simpa only [gaussApproximationTupleEvent, gaussDigitTupleEvent, E, D] using!
      symmDiff_orderedIntersections_subset_iUnion_witness E D
  let common : ℝ :=
    2 * ((1 + rate gap) ^ (r - 1) *
      (boundaryMass * windowMass ^ (r - 1)))
  have hwitness (j : Fin r) :
      gaussMeasure.real (coordinateReplacementWitness E D j) ≤ common := by
    simpa only [E, D, common] using!
      gaussMeasure_real_coordinateReplacementWitness_le
        hpsi hr times j gap hgap0 hscale hlower hupper hlarge hgap hrate
          hboundaryMass hboundaryLower hboundaryUpper hwindow
  calc
    gaussMeasure.real
        (gaussApproximationTupleEvent scale lower upper times ∆
          gaussDigitTupleEvent scale lower upper times) ≤
        gaussMeasure.real (⋃ j, coordinateReplacementWitness E D j) :=
      measureReal_mono hsubset
    _ = gaussMeasure.real
        (⋃ j ∈ (Finset.univ : Finset (Fin r)),
          coordinateReplacementWitness E D j) := by simp
    _ ≤ ∑ j ∈ (Finset.univ : Finset (Fin r)),
        gaussMeasure.real (coordinateReplacementWitness E D j) :=
      measureReal_biUnion_finset_le _ _
    _ ≤ ∑ _j ∈ (Finset.univ : Finset (Fin r)), common := by
      exact Finset.sum_le_sum fun j _hj => hwitness j
    _ = (r : ℝ) * common := by simp

/-! ## Explicit one-event constants -/

/-- Either endpoint strip has mass at most
`26*upper^2/(scale^2 log 2)`. -/
theorem gaussMeasure_real_replacementBoundaryStrip_le
    {scale lower upper center : ℝ}
    (hscale : 0 < scale) (hlower : 0 < lower) (hupper : lower < upper)
    (hlarge : 16 * upper ^ 2 ≤ lower * scale)
    (hcenter : center = lower ∨ center = upper) :
    gaussMeasure.real
        (scaledGaussFirstDigitBoundaryStrip scale center (8 * upper ^ 2)) ≤
      ((26 * upper ^ 2 / scale ^ 2) / Real.log 2) := by
  have hupper0 : 0 < upper := hlower.trans hupper
  have hwidth : 0 < 8 * upper ^ 2 := by positivity
  rcases hcenter with hcenter | hcenter
  · subst center
    have hraw := gaussMeasure_real_scaledGaussFirstDigitBoundaryStrip_le
      hscale hlower hwidth (by nlinarith [hlarge])
    have hlowerSq : lower ^ 2 ≤ upper ^ 2 := by nlinarith
    have hscaleSq : 0 < scale ^ 2 := sq_pos_of_pos hscale
    have hlog : 0 < Real.log 2 := Real.log_pos one_lt_two
    calc
      gaussMeasure.real
          (scaledGaussFirstDigitBoundaryStrip scale lower (8 * upper ^ 2)) ≤
          ((2 * (8 * upper ^ 2) + 10 * lower ^ 2) / scale ^ 2) /
            Real.log 2 := hraw
      _ ≤ (26 * upper ^ 2 / scale ^ 2) / Real.log 2 := by
        apply (div_le_div_iff_of_pos_right hlog).2
        apply (div_le_div_iff_of_pos_right hscaleSq).2
        nlinarith
  · subst center
    have hsize : 2 * (8 * upper ^ 2) ≤ upper * scale := by
      have hmul : lower * scale ≤ upper * scale :=
        mul_le_mul_of_nonneg_right hupper.le hscale.le
      nlinarith [hlarge.trans hmul]
    have hraw := gaussMeasure_real_scaledGaussFirstDigitBoundaryStrip_le
      hscale hupper0 hwidth hsize
    convert! hraw using 1
    ring

/-- The enlarged ordinary digit window still has mass `O(scale^-1)`, with a
constant independent of the time index. -/
theorem gaussMeasure_real_gaussEnlargedDigitWindow_le
    {scale lower upper : ℝ}
    (hscale : 0 < scale) (hscaleOne : 1 ≤ scale)
    (hlower : 0 < lower) (hupper : lower < upper)
    (hlarge : 16 * upper ^ 2 ≤ lower * scale) :
    gaussMeasure.real (gaussEnlargedDigitWindow scale lower upper) ≤
      (((2 * upper + 10 * upper ^ 2) / scale) / Real.log 2) := by
  have hupper0 : 0 < upper := hlower.trans hupper
  let eta : ℝ := 8 * upper ^ 2 / scale
  have heta0 : 0 ≤ eta := by dsimp [eta]; positivity
  have hscaleLarge : 8 * upper ≤ scale := by
    have hmul : lower * scale ≤ upper * scale :=
      mul_le_mul_of_nonneg_right hupper.le hscale.le
    nlinarith [hlarge.trans hmul]
  have hetaUpper : eta ≤ upper := by
    dsimp [eta]
    apply (div_le_iff₀ hscale).2
    nlinarith
  have hupperEnlarged : lower < upper + eta :=
    hupper.trans_le (le_add_of_nonneg_right heta0)
  have hraw := gaussMeasure_real_scaledGaussFirstDigitWindow_le
    hscale hlower hupperEnlarged
  have hlowerSq : lower ^ 2 ≤ upper ^ 2 := by nlinarith
  have henlarged0 : 0 ≤ upper + eta := by positivity
  have henlargedLe : upper + eta ≤ 2 * upper := by linarith
  have henlargedSq : (upper + eta) ^ 2 ≤ (2 * upper) ^ 2 := by
    simpa only [pow_two] using!
      mul_self_le_mul_self henlarged0 henlargedLe
  have hwidth : upper + eta - lower ≤ 2 * upper := by linarith
  have hscaleSq : 0 < scale ^ 2 := sq_pos_of_pos hscale
  have hlog : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hinside :
      (upper + eta - lower) / scale +
          2 * ((upper + eta) ^ 2 + lower ^ 2) / scale ^ 2 ≤
        (2 * upper + 10 * upper ^ 2) / scale := by
    have hfirst : (upper + eta - lower) / scale ≤ 2 * upper / scale :=
      (div_le_div_iff_of_pos_right hscale).2 hwidth
    have hsecond :
        2 * ((upper + eta) ^ 2 + lower ^ 2) / scale ^ 2 ≤
          10 * upper ^ 2 / scale := by
      apply (div_le_iff₀ hscaleSq).2
      have hsum :
          2 * ((upper + eta) ^ 2 + lower ^ 2) ≤ 10 * upper ^ 2 := by
        nlinarith [henlargedSq, hlowerSq]
      have hscaleMul : 10 * upper ^ 2 ≤ 10 * upper ^ 2 * scale := by
        have hnonneg : 0 ≤ 10 * upper ^ 2 := by positivity
        nlinarith [mul_nonneg hnonneg (sub_nonneg.mpr hscaleOne)]
      have hrhs :
          10 * upper ^ 2 / scale * scale ^ 2 =
            10 * upper ^ 2 * scale := by
        field_simp
      rw [hrhs]
      exact hsum.trans hscaleMul
    calc
      (upper + eta - lower) / scale +
          2 * ((upper + eta) ^ 2 + lower ^ 2) / scale ^ 2 ≤
          2 * upper / scale + 10 * upper ^ 2 / scale :=
        add_le_add hfirst hsecond
      _ = (2 * upper + 10 * upper ^ 2) / scale := by ring
  calc
    gaussMeasure.real (gaussEnlargedDigitWindow scale lower upper) ≤
        (((upper + eta - lower) / scale +
          2 * ((upper + eta) ^ 2 + lower ^ 2) / scale ^ 2) /
            Real.log 2) := by
      simpa only [gaussEnlargedDigitWindow, eta] using! hraw
    _ ≤ ((2 * upper + 10 * upper ^ 2) / scale) / Real.log 2 :=
      (div_le_div_iff_of_pos_right hlog).2 hinside

/-- Fixed tuple with all analytic constants instantiated. -/
theorem gaussMeasure_real_symmDiff_approximation_digit_tuple_le_explicit
    {rate : ℕ → ℝ} (hpsi : GaussDigitPsiMixing rate)
    {r : ℕ} (hr : 0 < r) {scale lower upper : ℝ}
    (times : Fin r → ℕ) (gap : ℕ)
    (hgap0 : 0 < gap)
    (hscale : 0 < scale) (hscaleOne : 1 ≤ scale)
    (hlower : 0 < lower) (hupper : lower < upper)
    (hlarge : 16 * upper ^ 2 ≤ lower * scale)
    (hgap : ∀ i k, i < k → times i + gap ≤ times k)
    (hrate : 0 ≤ rate gap) :
    gaussMeasure.real
        (gaussApproximationTupleEvent scale lower upper times ∆
          gaussDigitTupleEvent scale lower upper times) ≤
      (r : ℝ) *
        (2 * ((1 + rate gap) ^ (r - 1) *
          (((26 * upper ^ 2 / scale ^ 2) / Real.log 2) *
            (((2 * upper + 10 * upper ^ 2) / scale) /
              Real.log 2) ^ (r - 1)))) := by
  apply gaussMeasure_real_symmDiff_approximation_digit_tuple_le
    hpsi hr times gap hgap0 hscale hlower hupper hlarge hgap hrate
    (boundaryMass := (26 * upper ^ 2 / scale ^ 2) / Real.log 2)
    (windowMass := ((2 * upper + 10 * upper ^ 2) / scale) / Real.log 2)
  · positivity
  · exact gaussMeasure_real_replacementBoundaryStrip_le
      hscale hlower hupper hlarge (Or.inl rfl)
  · exact gaussMeasure_real_replacementBoundaryStrip_le
      hscale hlower hupper hlarge (Or.inr rfl)
  · exact gaussMeasure_real_gaussEnlargedDigitWindow_le
      hscale hscaleOne hlower hupper hlarge

/-! ## Summation over factorial tuples -/

/-- Sum over any finite family of chronologically `gap`-separated tuples.
The ambient function space has cardinal `horizon^r`, so no tuple-counting
factor is hidden. -/
theorem sum_gaussMeasure_real_symmDiff_tupleFamily_le_explicit
    {rate : ℕ → ℝ} (hpsi : GaussDigitPsiMixing rate)
    {r horizon : ℕ} (hr : 0 < r)
    {scale lower upper : ℝ} (gap : ℕ)
    (hgap0 : 0 < gap)
    (tuples : Finset (Fin r → Fin horizon))
    (hscale : 0 < scale) (hscaleOne : 1 ≤ scale)
    (hlower : 0 < lower) (hupper : lower < upper)
    (hlarge : 16 * upper ^ 2 ≤ lower * scale)
    (hgap : ∀ t ∈ tuples, ∀ i k, i < k →
      (t i).1 + gap ≤ (t k).1)
    (hrate : 0 ≤ rate gap) :
    (∑ t ∈ tuples,
      gaussMeasure.real
        (gaussApproximationTupleEvent scale lower upper
            (fun i => (t i).1) ∆
          gaussDigitTupleEvent scale lower upper
            (fun i => (t i).1))) ≤
      (horizon : ℝ) ^ r *
        ((r : ℝ) *
          (2 * ((1 + rate gap) ^ (r - 1) *
            (((26 * upper ^ 2 / scale ^ 2) / Real.log 2) *
              (((2 * upper + 10 * upper ^ 2) / scale) /
                Real.log 2) ^ (r - 1))))) := by
  let common : ℝ :=
    (r : ℝ) *
      (2 * ((1 + rate gap) ^ (r - 1) *
        (((26 * upper ^ 2 / scale ^ 2) / Real.log 2) *
          (((2 * upper + 10 * upper ^ 2) / scale) /
            Real.log 2) ^ (r - 1))))
  have hterm (t : Fin r → Fin horizon) (ht : t ∈ tuples) :
      gaussMeasure.real
          (gaussApproximationTupleEvent scale lower upper
              (fun i => (t i).1) ∆
            gaussDigitTupleEvent scale lower upper
              (fun i => (t i).1)) ≤ common := by
    simpa only [common] using!
      gaussMeasure_real_symmDiff_approximation_digit_tuple_le_explicit
        hpsi hr (fun i => (t i).1) gap hgap0 hscale hscaleOne hlower hupper
          hlarge (hgap t ht) hrate
  have hcardNat : tuples.card ≤ horizon ^ r := by
    have h := Finset.card_le_univ tuples
    simpa only [Fintype.card_fun, Fintype.card_fin] using! h
  have hcardReal : (tuples.card : ℝ) ≤ (horizon : ℝ) ^ r := by
    exact_mod_cast hcardNat
  have hcommon : 0 ≤ common := by
    have hrateFactor : 0 ≤ 1 + rate gap := by linarith
    have hlog : 0 < Real.log 2 := Real.log_pos one_lt_two
    have hwindowNumerator : 0 ≤ 2 * upper + 10 * upper ^ 2 := by
      nlinarith [sq_nonneg upper, hlower.trans hupper]
    dsimp [common]
    apply mul_nonneg (Nat.cast_nonneg r)
    apply mul_nonneg (by norm_num)
    apply mul_nonneg (pow_nonneg hrateFactor _)
    apply mul_nonneg
    · exact div_nonneg
        (div_nonneg (mul_nonneg (by norm_num) (sq_nonneg upper))
          (sq_nonneg scale)) hlog.le
    · exact pow_nonneg
        (div_nonneg
          (div_nonneg hwindowNumerator hscale.le) hlog.le) _
  calc
    (∑ t ∈ tuples,
      gaussMeasure.real
        (gaussApproximationTupleEvent scale lower upper
            (fun i => (t i).1) ∆
          gaussDigitTupleEvent scale lower upper
            (fun i => (t i).1))) ≤
        ∑ _t ∈ tuples, common := by
      exact Finset.sum_le_sum hterm
    _ = (tuples.card : ℝ) * common := by simp
    _ ≤ (horizon : ℝ) ^ r * common :=
      mul_le_mul_of_nonneg_right hcardReal hcommon

/-- Close-time tuples are controlled separately by the same single mixing
input at gap one.  This uses only chronological distinctness, not a growing
separation parameter, and therefore does not smuggle independence into the
short-gap estimate. -/
theorem sum_gaussMeasure_real_symmDiff_closeTupleFamily_le_explicit
    {rate : ℕ → ℝ} (hpsi : GaussDigitPsiMixing rate)
    {r horizon : ℕ} (hr : 0 < r)
    {scale lower upper : ℝ}
    (closeTuples : Finset (Fin r → Fin horizon))
    (hscale : 0 < scale) (hscaleOne : 1 ≤ scale)
    (hlower : 0 < lower) (hupper : lower < upper)
    (hlarge : 16 * upper ^ 2 ≤ lower * scale)
    (hchronological : ∀ t ∈ closeTuples, ∀ i k, i < k →
      (t i).1 + 1 ≤ (t k).1)
    (hrateOne : 0 ≤ rate 1) :
    (∑ t ∈ closeTuples,
      gaussMeasure.real
        (gaussApproximationTupleEvent scale lower upper
            (fun i => (t i).1) ∆
          gaussDigitTupleEvent scale lower upper
            (fun i => (t i).1))) ≤
      (horizon : ℝ) ^ r *
        ((r : ℝ) *
          (2 * ((1 + rate 1) ^ (r - 1) *
            (((26 * upper ^ 2 / scale ^ 2) / Real.log 2) *
              (((2 * upper + 10 * upper ^ 2) / scale) /
                Real.log 2) ^ (r - 1))))) := by
  exact sum_gaussMeasure_real_symmDiff_tupleFamily_le_explicit
    hpsi hr 1 (by norm_num) closeTuples hscale hscaleOne hlower hupper hlarge
      hchronological hrateOne

/-! ## The `O(scale^-1)` cancellation and the resulting limit -/

/-- Algebraic cancellation behind factorial scale: `scale^r` possible tuples,
one `scale^-2` strip, and `r-1` ordinary `scale^-1` windows leave exactly one
inverse power of `scale`. -/
theorem factorialTupleScaleCancellation
    {r L : ℕ} (hr : 0 < r) (hL : 0 < L) (mix B W : ℝ) :
    (L : ℝ) ^ r *
        ((r : ℝ) * (2 * (mix *
          ((B / (L : ℝ) ^ 2) * (W / (L : ℝ)) ^ (r - 1))))) =
      ((r : ℝ) * 2 * mix * B * W ^ (r - 1)) / (L : ℝ) := by
  cases r with
  | zero => omega
  | succ m =>
      have hLne : (L : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hL)
      simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one, div_pow]
      field_simp
      ring

/-- At the natural scale `scale=horizon=L`, every separated tuple family has
an explicit constant-over-`L` replacement bound.  A uniform upper bound `R`
for the relevant mixing coefficient is enough; decay of the coefficient is
not needed for this replacement step. -/
theorem sum_gaussMeasure_real_symmDiff_tupleFamily_le_const_div
    {rate : ℕ → ℝ} (hpsi : GaussDigitPsiMixing rate)
    {r L : ℕ} (hr : 0 < r) (hL : 0 < L)
    {lower upper R : ℝ} (gap : ℕ)
    (hgap0 : 0 < gap)
    (tuples : Finset (Fin r → Fin L))
    (hlower : 0 < lower) (hupper : lower < upper)
    (hlarge : 16 * upper ^ 2 ≤ lower * (L : ℝ))
    (hgap : ∀ t ∈ tuples, ∀ i k, i < k →
      (t i).1 + gap ≤ (t k).1)
    (hrate : 0 ≤ rate gap) (hrateR : rate gap ≤ R) :
    (∑ t ∈ tuples,
      gaussMeasure.real
        (gaussApproximationTupleEvent (L : ℝ) lower upper
            (fun i => (t i).1) ∆
          gaussDigitTupleEvent (L : ℝ) lower upper
            (fun i => (t i).1))) ≤
      ((r : ℝ) * 2 * (1 + R) ^ (r - 1) *
          (26 * upper ^ 2 / Real.log 2) *
          ((2 * upper + 10 * upper ^ 2) / Real.log 2) ^ (r - 1)) /
        (L : ℝ) := by
  have hfamily := sum_gaussMeasure_real_symmDiff_tupleFamily_le_explicit
    hpsi hr gap hgap0 tuples (by exact_mod_cast hL) (by exact_mod_cast hL)
      hlower hupper hlarge hgap hrate
  let B : ℝ := 26 * upper ^ 2 / Real.log 2
  let W : ℝ := (2 * upper + 10 * upper ^ 2) / Real.log 2
  have hlog : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos one_lt_two)
  have hLreal : (L : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hL)
  have hboundaryRewrite :
      (26 * upper ^ 2 / (L : ℝ) ^ 2) / Real.log 2 =
        B / (L : ℝ) ^ 2 := by
    dsimp [B]
    field_simp
  have hwindowRewrite :
      ((2 * upper + 10 * upper ^ 2) / (L : ℝ)) / Real.log 2 =
        W / (L : ℝ) := by
    dsimp [W]
    field_simp
  have hcancel := factorialTupleScaleCancellation hr hL
    ((1 + rate gap) ^ (r - 1)) B W
  have hpow :
      (1 + rate gap) ^ (r - 1) ≤ (1 + R) ^ (r - 1) := by
    have hleft : 0 ≤ 1 + rate gap := by linarith
    exact pow_le_pow_left₀ hleft (by linarith) _
  have hB0 : 0 ≤ B := by
    dsimp [B]
    positivity
  have hW0 : 0 ≤ W := by
    dsimp [W]
    have hnum : 0 ≤ 2 * upper + 10 * upper ^ 2 := by
      nlinarith [sq_nonneg upper, hlower.trans hupper]
    exact div_nonneg hnum (Real.log_pos one_lt_two).le
  calc
    (∑ t ∈ tuples,
      gaussMeasure.real
        (gaussApproximationTupleEvent (L : ℝ) lower upper
            (fun i => (t i).1) ∆
          gaussDigitTupleEvent (L : ℝ) lower upper
            (fun i => (t i).1))) ≤
        (L : ℝ) ^ r *
          ((r : ℝ) *
            (2 * ((1 + rate gap) ^ (r - 1) *
              (((26 * upper ^ 2 / (L : ℝ) ^ 2) / Real.log 2) *
                (((2 * upper + 10 * upper ^ 2) / (L : ℝ)) /
                  Real.log 2) ^ (r - 1))))) := hfamily
    _ = ((r : ℝ) * 2 * (1 + rate gap) ^ (r - 1) *
          B * W ^ (r - 1)) / (L : ℝ) := by
      rw [hboundaryRewrite, hwindowRewrite]
      exact hcancel
    _ ≤ ((r : ℝ) * 2 * (1 + R) ^ (r - 1) *
          B * W ^ (r - 1)) / (L : ℝ) := by
      apply (div_le_div_iff_of_pos_right (by exact_mod_cast hL : (0 : ℝ) < L)).2
      gcongr
    _ = ((r : ℝ) * 2 * (1 + R) ^ (r - 1) *
          (26 * upper ^ 2 / Real.log 2) *
          ((2 * upper + 10 * upper ^ 2) / Real.log 2) ^ (r - 1)) /
        (L : ℝ) := by rfl

/-- Separate close-time corollary at gap one. -/
theorem sum_gaussMeasure_real_symmDiff_closeTupleFamily_le_const_div
    {rate : ℕ → ℝ} (hpsi : GaussDigitPsiMixing rate)
    {r L : ℕ} (hr : 0 < r) (hL : 0 < L)
    {lower upper R : ℝ}
    (closeTuples : Finset (Fin r → Fin L))
    (hlower : 0 < lower) (hupper : lower < upper)
    (hlarge : 16 * upper ^ 2 ≤ lower * (L : ℝ))
    (hchronological : ∀ t ∈ closeTuples, ∀ i k, i < k →
      (t i).1 + 1 ≤ (t k).1)
    (hrateOne : 0 ≤ rate 1) (hrateR : rate 1 ≤ R) :
    (∑ t ∈ closeTuples,
      gaussMeasure.real
        (gaussApproximationTupleEvent (L : ℝ) lower upper
            (fun i => (t i).1) ∆
          gaussDigitTupleEvent (L : ℝ) lower upper
            (fun i => (t i).1))) ≤
      ((r : ℝ) * 2 * (1 + R) ^ (r - 1) *
          (26 * upper ^ 2 / Real.log 2) *
          ((2 * upper + 10 * upper ^ 2) / Real.log 2) ^ (r - 1)) /
        (L : ℝ) := by
  exact sum_gaussMeasure_real_symmDiff_tupleFamily_le_const_div
    hpsi hr hL 1 (by norm_num) closeTuples hlower hupper hlarge hchronological
      hrateOne hrateR

/-- The summed replacement error for any fixed-order separated tuple family
tends to zero.  This is the literal `o(1)` statement used at factorial-moment
scale. -/
theorem tendsto_sum_gaussMeasure_real_symmDiff_tupleFamily_zero
    {rate : ℕ → ℝ} (hpsi : GaussDigitPsiMixing rate)
    {r : ℕ} (hr : 0 < r) {lower upper R : ℝ} (gap : ℕ)
    (hgap0 : 0 < gap)
    (tuples : ∀ L : ℕ, Finset (Fin r → Fin L))
    (hlower : 0 < lower) (hupper : lower < upper)
    (hgap : ∀ L, ∀ t ∈ tuples L, ∀ i k, i < k →
      (t i).1 + gap ≤ (t k).1)
    (hrate : 0 ≤ rate gap) (hrateR : rate gap ≤ R) :
    Tendsto
      (fun L : ℕ =>
        ∑ t ∈ tuples L,
          gaussMeasure.real
            (gaussApproximationTupleEvent (L : ℝ) lower upper
                (fun i => (t i).1) ∆
              gaussDigitTupleEvent (L : ℝ) lower upper
                (fun i => (t i).1)))
      atTop (𝓝 0) := by
  let F : ℕ → ℝ := fun L =>
    ∑ t ∈ tuples L,
      gaussMeasure.real
        (gaussApproximationTupleEvent (L : ℝ) lower upper
            (fun i => (t i).1) ∆
          gaussDigitTupleEvent (L : ℝ) lower upper
            (fun i => (t i).1))
  let C : ℝ :=
    (r : ℝ) * 2 * (1 + R) ^ (r - 1) *
      (26 * upper ^ 2 / Real.log 2) *
      ((2 * upper + 10 * upper ^ 2) / Real.log 2) ^ (r - 1)
  have hF0 : ∀ L, 0 ≤ F L := by
    intro L
    dsimp [F]
    exact Finset.sum_nonneg fun _ _ => measureReal_nonneg
  have hcastLarge :
      ∀ᶠ L : ℕ in atTop, 16 * upper ^ 2 / lower ≤ (L : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually
      (eventually_ge_atTop (16 * upper ^ 2 / lower))
  have hupperEventually : ∀ᶠ L : ℕ in atTop, F L ≤ C / (L : ℝ) := by
    filter_upwards [eventually_gt_atTop 0, hcastLarge] with L hL hratio
    have hlarge : 16 * upper ^ 2 ≤ lower * (L : ℝ) := by
      have h := (div_le_iff₀ hlower).1 hratio
      nlinarith
    simpa only [F, C] using!
      sum_gaussMeasure_real_symmDiff_tupleFamily_le_const_div
        hpsi hr hL gap hgap0 (tuples L) hlower hupper hlarge (hgap L)
          hrate hrateR
  exact squeeze_zero'
    (Eventually.of_forall hF0) hupperEventually
      (tendsto_const_div_atTop_nhds_zero_nat C)

/-- Close-time tuple replacement also tends to zero, using the mixing input
only at gap one.  This is stated separately so that close tuples cannot be
silently absorbed into the separated calculation. -/
theorem tendsto_sum_gaussMeasure_real_symmDiff_closeTupleFamily_zero
    {rate : ℕ → ℝ} (hpsi : GaussDigitPsiMixing rate)
    {r : ℕ} (hr : 0 < r) {lower upper R : ℝ}
    (closeTuples : ∀ L : ℕ, Finset (Fin r → Fin L))
    (hlower : 0 < lower) (hupper : lower < upper)
    (hchronological : ∀ L, ∀ t ∈ closeTuples L, ∀ i k, i < k →
      (t i).1 + 1 ≤ (t k).1)
    (hrateOne : 0 ≤ rate 1) (hrateR : rate 1 ≤ R) :
    Tendsto
      (fun L : ℕ =>
        ∑ t ∈ closeTuples L,
          gaussMeasure.real
            (gaussApproximationTupleEvent (L : ℝ) lower upper
                (fun i => (t i).1) ∆
              gaussDigitTupleEvent (L : ℝ) lower upper
                (fun i => (t i).1)))
      atTop (𝓝 0) := by
  exact tendsto_sum_gaussMeasure_real_symmDiff_tupleFamily_zero
    hpsi hr 1 (by norm_num) closeTuples hlower hupper hchronological hrateOne hrateR

end

end Erdos1002
