import ErdosProblems.Erdos1002.MarkedResonances

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Factorial moments as sums over distinct event tuples

This file makes the factorial-measure expansion used in the marked Poisson
argument literal.  A falling factorial of a finite event count is expanded
over embeddings, so repeated indices are excluded before any integration is
performed.
-/

open MeasureTheory Set Finset
open scoped BigOperators

namespace Erdos1002

noncomputable section

local instance factorialEventExpansionPropDecidable (P : Prop) : Decidable P :=
  Classical.propDecidable P

/-- Number of events from a finite family which occur at `ω`. -/
def finiteEventCount {Ω I : Type*} (s : Finset I) (E : I → Set Ω) (ω : Ω) : ℕ :=
  ∑ i ∈ s, if ω ∈ E i then 1 else 0

/-- Simultaneous occurrence event attached to an ordered distinct tuple. -/
def tupleEvent {Ω I : Type*} {s : Finset I} {r : ℕ}
    (E : I → Set Ω) (f : Fin r ↪ s) : Set Ω :=
  ⋂ j, E (f j)

theorem measurableSet_tupleEvent {Ω I : Type*} [MeasurableSpace Ω]
    {s : Finset I} {r : ℕ} {E : I → Set Ω}
    (hE : ∀ i ∈ s, MeasurableSet (E i)) (f : Fin r ↪ s) :
    MeasurableSet (tupleEvent E f) := by
  apply MeasurableSet.iInter
  intro j
  exact hE (f j) (f j).property

/-- Embeddings into a filtered finite set are the same thing as embeddings
into the original set whose values all satisfy the filter predicate. -/
def embeddingFilterEquiv {I : Type*} [DecidableEq I] (s : Finset I)
    (p : I → Prop) (r : ℕ) :
    (Fin r ↪ (s.filter p : Finset I)) ≃
      {f : Fin r ↪ (s : Finset I) // ∀ j, p (f j)} where
  toFun e :=
    ⟨
      {
        toFun := fun j ↦ ⟨(e j : I), (Finset.mem_filter.mp (e j).property).1⟩
        inj' := by
          intro a b h
          apply e.injective
          apply Subtype.ext
          exact congrArg (fun x : (s : Finset I) ↦ (x : I)) h
      },
      fun j ↦ (Finset.mem_filter.mp (e j).property).2
    ⟩
  invFun e :=
    {
      toFun := fun j ↦
        ⟨(e.1 j : I), Finset.mem_filter.mpr ⟨(e.1 j).property, e.2 j⟩⟩
      inj' := by
        intro a b h
        apply e.1.injective
        apply Subtype.ext
        exact congrArg (fun x : (s.filter p : Finset I) ↦ (x : I)) h
    }
  left_inv e := by
    ext j
    rfl
  right_inv e := by
    rcases e with ⟨e, he⟩
    apply Subtype.ext
    ext j
    rfl

/-- Pointwise factorial expansion.  The right side ranges over ordered
distinct tuples because its index type consists of embeddings. -/
theorem finiteEventCount_descFactorial_eq_sum_embeddings
    {Ω I : Type*} [DecidableEq I] (s : Finset I) (E : I → Set Ω)
    (ω : Ω) (r : ℕ) :
    (finiteEventCount s E ω).descFactorial r =
      ∑ f : Fin r ↪ (s : Finset I),
        if ω ∈ tupleEvent E f then 1 else 0 := by
  classical
  let p : I → Prop := fun i ↦ ω ∈ E i
  have hcount : finiteEventCount s E ω = (s.filter p).card := by
    unfold finiteEventCount p
    exact Finset.sum_boole _ _
  rw [hcount]
  calc
    (s.filter p).card.descFactorial r =
        Fintype.card (Fin r ↪ (s.filter p : Finset I)) :=
      (card_orderedDistinctTuples (s.filter p) r).symm
    _ = Fintype.card
        {f : Fin r ↪ (s : Finset I) // ∀ j, p (f j)} :=
      Fintype.card_congr (embeddingFilterEquiv s p r)
    _ = #{f : Fin r ↪ (s : Finset I) | ∀ j, p (f j)} :=
      Fintype.card_subtype _
    _ = ∑ f : Fin r ↪ (s : Finset I),
          if ∀ j, p (f j) then 1 else 0 := by
      symm
      exact Finset.sum_boole _ _
    _ = ∑ f : Fin r ↪ (s : Finset I),
          if ω ∈ tupleEvent E f then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro f _hf
      simp only [tupleEvent, mem_iInter, p]

/-- Real-valued indicator form of the pointwise expansion. -/
theorem cast_finiteEventCount_descFactorial_eq_sum_indicators
    {Ω I : Type*} [DecidableEq I] (s : Finset I) (E : I → Set Ω)
    (ω : Ω) (r : ℕ) :
    ((finiteEventCount s E ω).descFactorial r : ℝ) =
      ∑ f : Fin r ↪ (s : Finset I),
        (tupleEvent E f).indicator (fun _ ↦ (1 : ℝ)) ω := by
  rw [finiteEventCount_descFactorial_eq_sum_embeddings s E ω r]
  simp only [Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero,
    Set.indicator_apply]

/-- Integrated factorial expansion.  This is the exact bridge from count
moments to factorial measures; it has no diagonal or multiplicity convention
left implicit. -/
theorem integral_finiteEventCount_descFactorial
    {Ω I : Type*} [MeasurableSpace Ω] [DecidableEq I]
    (s : Finset I) (E : I → Set Ω) (r : ℕ) (mu : Measure Ω)
    [IsFiniteMeasure mu] (hE : ∀ i ∈ s, MeasurableSet (E i)) :
    ∫ ω, ((finiteEventCount s E ω).descFactorial r : ℝ) ∂mu =
      ∑ f : Fin r ↪ (s : Finset I), mu.real (tupleEvent E f) := by
  simp_rw [cast_finiteEventCount_descFactorial_eq_sum_indicators s E]
  rw [MeasureTheory.integral_finset_sum]
  · apply Finset.sum_congr rfl
    intro f _hf
    exact MeasureTheory.integral_indicator_one (measurableSet_tupleEvent hE f)
  · intro f _hf
    exact (integrable_const (1 : ℝ)).indicator (measurableSet_tupleEvent hE f)

/-- The event contributed by one denominator to a marked resonance count. -/
def markedDenominatorEvent (N : ℕ) (B : Set (ℝ × ℝ × ℝ)) (p : ℕ) : Set ℝ :=
  {α | IsPrimitiveResonance p α ∧ markedResonancePoint N p α ∈ B}

theorem measurableSet_markedDenominatorEvent (N : ℕ)
    {B : Set (ℝ × ℝ × ℝ)} (hB : MeasurableSet B) (p : ℕ) :
    MeasurableSet (markedDenominatorEvent N B p) := by
  exact (measurableSet_isPrimitiveResonance p).inter
    (hB.preimage (measurable_markedResonancePoint N p))

theorem markedResonanceCount_eq_finiteEventCount
    (N P : ℕ) (B : Set (ℝ × ℝ × ℝ)) (α : ℝ) :
    markedResonanceCount N P B α =
      finiteEventCount (Finset.Icc 1 P) (markedDenominatorEvent N B) α := by
  unfold markedResonanceCount finiteEventCount markedDenominatorEvent
  apply Finset.sum_congr rfl
  intro p _hp
  by_cases h : IsPrimitiveResonance p α ∧ markedResonancePoint N p α ∈ B
  · simp [h]
  · simp [h]

/-- Specialized factorial-measure identity for the marked resonance process. -/
theorem integral_markedResonanceCount_descFactorial
    (N P r : ℕ) {B : Set (ℝ × ℝ × ℝ)} (hB : MeasurableSet B) :
    ∫ α, ((markedResonanceCount N P B α).descFactorial r : ℝ)
        ∂uniform01Measure =
      ∑ f : Fin r ↪ (Finset.Icc 1 P : Finset ℕ),
        uniform01Measure.real
          (⋂ j, markedDenominatorEvent N B (f j)) := by
  simpa only [markedResonanceCount_eq_finiteEventCount] using!
    (integral_finiteEventCount_descFactorial
      (Finset.Icc 1 P) (markedDenominatorEvent N B) r uniform01Measure
      (fun p _hp ↦ measurableSet_markedDenominatorEvent N hB p))

end

end Erdos1002
