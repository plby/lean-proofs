import ErdosProblems.Erdos1002.GaussPrefixMarkedMixedFourier

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Event-level form of the prefix-freezing envelope

The pointwise freezing bound is useful in the late marked argument only if
its absolute error can be summed before cancellation.  This file rewrites
each `0`--`1` product in that envelope as the indicator of a literal finite
intersection.  Its integral is therefore exactly an event mass: one
enlarged-window tuple for the phase error and one endpoint-strip tuple for
each coordinate.  This is the interface consumed by the later rare-digit
and prefix--future mixing estimates.
-/

open MeasureTheory Set
open scoped BigOperators ENNReal

namespace Erdos1002

noncomputable section

local instance prefixFreezingAggregatePropDecidable (P : Prop) :
    Decidable P := Classical.propDecidable P

/-- Simultaneous membership of finitely many coordinate functions in their
closed windows. -/
def closedWindowTupleEvent
    {Ω : Type*} {r : ℕ} (a b : Fin r → ℝ)
    (coordinate : Ω → Fin r → ℝ) : Set Ω :=
  ⋂ i, (fun ω ↦ coordinate ω i) ⁻¹' Icc (a i) (b i)

/-- One endpoint strip at coordinate `j`, with enlarged windows at every
other coordinate.  Writing this as one finite intersection makes the
absolute-value-inside-the-tuple-sum requirement explicit. -/
def closedBoundaryWindowTupleEvent
    {Ω : Type*} {r : ℕ} (a b : Fin r → ℝ)
    (coordinate : Ω → Fin r → ℝ) (eta : ℝ) (j : Fin r) : Set Ω :=
  ⋂ i, (fun ω ↦ coordinate ω i) ⁻¹'
    if i = j then
      closedIntervalBoundaryStrip (a j) (b j) eta
    else Icc (a i - eta) (b i + eta)

/-- One of the two ordinary window tuples obtained by selecting the strip
around `center` at coordinate `j` and enlarged windows elsewhere. -/
def closedEndpointStripWindowTupleEvent
    {Ω : Type*} {r : ℕ} (a b : Fin r → ℝ)
    (coordinate : Ω → Fin r → ℝ) (eta : ℝ)
    (j : Fin r) (center : ℝ) : Set Ω :=
  closedWindowTupleEvent
    (fun i ↦ if i = j then center - eta else a i - eta)
    (fun i ↦ if i = j then center + eta else b i + eta)
    coordinate

/-- The boundary tuple is exactly the union of its lower-endpoint and
upper-endpoint ordinary window tuples. -/
theorem closedBoundaryWindowTupleEvent_eq_union_endpointStrips
    {Ω : Type*} {r : ℕ} (a b : Fin r → ℝ)
    (coordinate : Ω → Fin r → ℝ) (eta : ℝ) (j : Fin r) :
    closedBoundaryWindowTupleEvent a b coordinate eta j =
      closedEndpointStripWindowTupleEvent
          a b coordinate eta j (a j) ∪
        closedEndpointStripWindowTupleEvent
          a b coordinate eta j (b j) := by
  ext ω
  constructor
  · intro hω
    have hall := Set.mem_iInter.mp hω
    have hj := hall j
    rw [if_pos rfl] at hj
    rcases hj with hjLower | hjUpper
    · left
      apply Set.mem_iInter.mpr
      intro i
      by_cases hij : i = j
      · subst i
        simpa [closedEndpointStripWindowTupleEvent,
          closedWindowTupleEvent] using! hjLower
      · simpa [closedEndpointStripWindowTupleEvent,
          closedWindowTupleEvent, hij] using! hall i
    · right
      apply Set.mem_iInter.mpr
      intro i
      by_cases hij : i = j
      · subst i
        simpa [closedEndpointStripWindowTupleEvent,
          closedWindowTupleEvent] using! hjUpper
      · simpa [closedEndpointStripWindowTupleEvent,
          closedWindowTupleEvent, hij] using! hall i
  · rintro (hω | hω)
    · apply Set.mem_iInter.mpr
      intro i
      have hi := Set.mem_iInter.mp hω i
      by_cases hij : i = j
      · subst i
        rw [if_pos rfl]
        left
        simpa [closedEndpointStripWindowTupleEvent,
          closedWindowTupleEvent] using! hi
      · rw [if_neg hij]
        simpa [closedEndpointStripWindowTupleEvent,
          closedWindowTupleEvent, hij] using! hi
    · apply Set.mem_iInter.mpr
      intro i
      have hi := Set.mem_iInter.mp hω i
      by_cases hij : i = j
      · subst i
        rw [if_pos rfl]
        right
        simpa [closedEndpointStripWindowTupleEvent,
          closedWindowTupleEvent] using! hi
      · rw [if_neg hij]
        simpa [closedEndpointStripWindowTupleEvent,
          closedWindowTupleEvent, hij] using! hi

theorem measurableSet_closedWindowTupleEvent
    {Ω : Type*} [MeasurableSpace Ω] {r : ℕ}
    (a b : Fin r → ℝ) (coordinate : Ω → Fin r → ℝ)
    (hcoordinate : ∀ i, Measurable fun ω ↦ coordinate ω i) :
    MeasurableSet (closedWindowTupleEvent a b coordinate) := by
  apply MeasurableSet.iInter
  intro i
  exact measurableSet_Icc.preimage (hcoordinate i)

theorem measurableSet_closedBoundaryWindowTupleEvent
    {Ω : Type*} [MeasurableSpace Ω] {r : ℕ}
    (a b : Fin r → ℝ) (coordinate : Ω → Fin r → ℝ)
    (eta : ℝ) (j : Fin r)
    (hcoordinate : ∀ i, Measurable fun ω ↦ coordinate ω i) :
    MeasurableSet
      (closedBoundaryWindowTupleEvent a b coordinate eta j) := by
  apply MeasurableSet.iInter
  intro i
  by_cases hij : i = j
  · rw [if_pos hij]
    exact (measurableSet_Icc.union measurableSet_Icc).preimage
      (hcoordinate i)
  · rw [if_neg hij]
    exact measurableSet_Icc.preimage (hcoordinate i)

/-- A product of closed-window indicators is literally the indicator of
the corresponding finite intersection. -/
theorem closedIntervalIndicatorProduct_eq_eventIndicator
    {Ω : Type*} {r : ℕ} (a b : Fin r → ℝ)
    (coordinate : Ω → Fin r → ℝ) (ω : Ω) :
    closedIntervalIndicatorProduct a b (coordinate ω) =
      (closedWindowTupleEvent a b coordinate).indicator
        (fun _ ↦ (1 : ℝ)) ω := by
  classical
  by_cases hall : ∀ i, coordinate ω i ∈ Icc (a i) (b i)
  · have hmem : ω ∈ closedWindowTupleEvent a b coordinate := by
      exact Set.mem_iInter.mpr hall
    rw [Set.indicator_of_mem hmem]
    apply Finset.prod_eq_one
    intro i _hi
    simp only [closedIntervalIndicator, if_pos (hall i)]
  · push_neg at hall
    obtain ⟨i, hi⟩ := hall
    have hnotMem : ω ∉ closedWindowTupleEvent a b coordinate := by
      intro hmem
      exact hi (Set.mem_iInter.mp hmem i)
    rw [Set.indicator_of_notMem hnotMem]
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp only [closedIntervalIndicator, if_neg hi]

/-- Each boundary summand in the pointwise envelope is exactly the
indicator of a finite tuple event with one endpoint strip. -/
theorem boundaryIndicatorProduct_eq_eventIndicator
    {Ω : Type*} {r : ℕ} (a b : Fin r → ℝ)
    (coordinate : Ω → Fin r → ℝ) (eta : ℝ) (j : Fin r) (ω : Ω) :
    closedIntervalBoundaryIndicator (a j) (b j) eta (coordinate ω j) *
        ∏ i ∈ (Finset.univ : Finset (Fin r)).erase j,
          closedIntervalIndicator (a i - eta) (b i + eta)
            (coordinate ω i) =
      (closedBoundaryWindowTupleEvent a b coordinate eta j).indicator
        (fun _ ↦ (1 : ℝ)) ω := by
  classical
  by_cases hj : coordinate ω j ∈
      closedIntervalBoundaryStrip (a j) (b j) eta
  · by_cases hother : ∀ i, i ≠ j →
        coordinate ω i ∈ Icc (a i - eta) (b i + eta)
    · have hmem : ω ∈
          closedBoundaryWindowTupleEvent a b coordinate eta j := by
        apply Set.mem_iInter.mpr
        intro i
        by_cases hij : i = j
        · subst i
          simpa using! hj
        · simpa only [if_neg hij] using! hother i hij
      rw [Set.indicator_of_mem hmem]
      have hprod :
          ∏ i ∈ (Finset.univ : Finset (Fin r)).erase j,
              closedIntervalIndicator (a i - eta) (b i + eta)
                (coordinate ω i) = 1 := by
        apply Finset.prod_eq_one
        intro i hi
        have hij : i ≠ j := Finset.ne_of_mem_erase hi
        simp only [closedIntervalIndicator, if_pos (hother i hij)]
      simp only [closedIntervalBoundaryIndicator, if_pos hj, hprod, mul_one]
    · push_neg at hother
      obtain ⟨i, hij, hi⟩ := hother
      have hnotMem : ω ∉
          closedBoundaryWindowTupleEvent a b coordinate eta j := by
        intro hmem
        have hiMem := Set.mem_iInter.mp hmem i
        rw [if_neg hij] at hiMem
        exact hi hiMem
      rw [Set.indicator_of_notMem hnotMem]
      have hiErase : i ∈ (Finset.univ : Finset (Fin r)).erase j :=
        Finset.mem_erase.mpr ⟨hij, Finset.mem_univ i⟩
      have hprod :
          ∏ i ∈ (Finset.univ : Finset (Fin r)).erase j,
              closedIntervalIndicator (a i - eta) (b i + eta)
                (coordinate ω i) = 0 := by
        apply Finset.prod_eq_zero hiErase
        simp only [closedIntervalIndicator, if_neg hi]
      simp only [hprod, mul_zero]
  · have hnotMem : ω ∉
        closedBoundaryWindowTupleEvent a b coordinate eta j := by
      intro hmem
      have hjMem := Set.mem_iInter.mp hmem j
      rw [if_pos rfl] at hjMem
      exact hj hjMem
    rw [Set.indicator_of_notMem hnotMem]
    simp only [closedIntervalBoundaryIndicator, if_neg hj, zero_mul]

/-- Pointwise event decomposition of the entire freezing envelope. -/
theorem oscillatoryPrefixFreezingEnvelope_eq_eventIndicators
    {Ω : Type*} {r : ℕ} (a b : Fin r → ℝ)
    (coordinate : Ω → Fin r → ℝ) (K phaseRadius eta : ℝ) (ω : Ω) :
    oscillatoryPrefixFreezingEnvelope a b (coordinate ω)
        K phaseRadius eta =
      (2 * Real.pi * |K| * phaseRadius) *
        (closedWindowTupleEvent
          (fun i ↦ a i - eta) (fun i ↦ b i + eta)
          coordinate).indicator (fun _ ↦ (1 : ℝ)) ω +
      ∑ j,
        (closedBoundaryWindowTupleEvent a b coordinate eta j).indicator
          (fun _ ↦ (1 : ℝ)) ω := by
  unfold oscillatoryPrefixFreezingEnvelope
  rw [closedIntervalIndicatorProduct_eq_eventIndicator]
  apply congrArg₂ (· + ·) rfl
  apply Finset.sum_congr rfl
  intro j _hj
  exact boundaryIndicatorProduct_eq_eventIndicator
    a b coordinate eta j ω

/-- Integrated event decomposition.  In particular, the norm has already
been placed inside every later tuple sum before any mixing estimate is
applied. -/
theorem integral_oscillatoryPrefixFreezingEnvelope_eq_eventMasses
    {Ω : Type*} [MeasurableSpace Ω] {r : ℕ}
    (mu : Measure Ω) [IsFiniteMeasure mu]
    (a b : Fin r → ℝ) (coordinate : Ω → Fin r → ℝ)
    (K phaseRadius eta : ℝ)
    (hcoordinate : ∀ i, Measurable fun ω ↦ coordinate ω i) :
    (∫ ω, oscillatoryPrefixFreezingEnvelope a b (coordinate ω)
        K phaseRadius eta ∂mu) =
      (2 * Real.pi * |K| * phaseRadius) *
        mu.real (closedWindowTupleEvent
          (fun i ↦ a i - eta) (fun i ↦ b i + eta) coordinate) +
      ∑ j, mu.real
        (closedBoundaryWindowTupleEvent a b coordinate eta j) := by
  have hmain : MeasurableSet (closedWindowTupleEvent
      (fun i ↦ a i - eta) (fun i ↦ b i + eta) coordinate) :=
    measurableSet_closedWindowTupleEvent _ _ coordinate hcoordinate
  have hboundary : ∀ j, MeasurableSet
      (closedBoundaryWindowTupleEvent a b coordinate eta j) := by
    intro j
    exact measurableSet_closedBoundaryWindowTupleEvent
      a b coordinate eta j hcoordinate
  have hmainInt : Integrable (fun ω ↦
      (2 * Real.pi * |K| * phaseRadius) *
        (closedWindowTupleEvent
          (fun i ↦ a i - eta) (fun i ↦ b i + eta)
          coordinate).indicator (fun _ ↦ (1 : ℝ)) ω) mu :=
    ((integrable_const (1 : ℝ)).indicator hmain).const_mul _
  have hboundaryInt : ∀ j, Integrable (fun ω ↦
      (closedBoundaryWindowTupleEvent a b coordinate eta j).indicator
        (fun _ ↦ (1 : ℝ)) ω) mu := by
    intro j
    exact (integrable_const (1 : ℝ)).indicator (hboundary j)
  rw [integral_congr_ae (ae_of_all mu fun ω ↦
      oscillatoryPrefixFreezingEnvelope_eq_eventIndicators
        a b coordinate K phaseRadius eta ω),
    integral_add hmainInt
      (integrable_finset_sum _ fun j _hj ↦ hboundaryInt j),
    integral_const_mul,
    integral_finset_sum _ (fun j _hj ↦ hboundaryInt j)]
  apply congrArg₂ (· + ·)
  · exact congrArg (fun t : ℝ ↦
      (2 * Real.pi * |K| * phaseRadius) * t)
      (integral_indicator_one hmain)
  apply Finset.sum_congr rfl
  intro j _hj
  exact integral_indicator_one (hboundary j)

/-- Event-mass upper bound after replacing the word-dependent phase
coefficient by any deterministic majorant. -/
theorem integral_oscillatoryPrefixFreezingEnvelope_le_eventMasses
    {Ω : Type*} [MeasurableSpace Ω] {r : ℕ}
    (mu : Measure Ω) [IsFiniteMeasure mu]
    (a b : Fin r → ℝ) (coordinate : Ω → Fin r → ℝ)
    (K phaseRadius eta delta : ℝ)
    (hcoordinate : ∀ i, Measurable fun ω ↦ coordinate ω i)
    (hphaseCoefficient :
      2 * Real.pi * |K| * phaseRadius ≤ delta) :
    (∫ ω, oscillatoryPrefixFreezingEnvelope a b (coordinate ω)
        K phaseRadius eta ∂mu) ≤
      delta * mu.real (closedWindowTupleEvent
        (fun i ↦ a i - eta) (fun i ↦ b i + eta) coordinate) +
      ∑ j, mu.real
        (closedBoundaryWindowTupleEvent a b coordinate eta j) := by
  rw [integral_oscillatoryPrefixFreezingEnvelope_eq_eventMasses
    mu a b coordinate K phaseRadius eta hcoordinate]
  exact add_le_add
    (mul_le_mul_of_nonneg_right hphaseCoefficient measureReal_nonneg)
    le_rfl

end

end Erdos1002
