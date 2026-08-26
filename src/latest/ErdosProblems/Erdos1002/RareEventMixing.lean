import ErdosProblems.Erdos1002.PsiMixing

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Iterated relative mixing for rare events

The rare-event factorial-moment argument exposes an ordered tuple one event
at a time.  At each gap, event-level `ψ`-mixing compares the first event with
the intersection of all later events.  This file iterates that two-block
estimate without assuming independence and retains the complete product of
the multiplicative errors.
-/

open MeasureTheory Set
open scoped BigOperators

namespace Erdos1002

noncomputable section

variable {Omega : Type*}

/-- Intersection of an ordered finite list of events.  The empty intersection
is the whole space. -/
def orderedEventIntersection : List (Set Omega) → Set Omega
  | [] => univ
  | A :: events => A ∩ orderedEventIntersection events

@[simp]
theorem orderedEventIntersection_nil :
    orderedEventIntersection ([] : List (Set Omega)) = univ := rfl

@[simp]
theorem orderedEventIntersection_cons (A : Set Omega) (events : List (Set Omega)) :
    orderedEventIntersection (A :: events) = A ∩ orderedEventIntersection events := rfl

/-- Product of the one-event probabilities associated with an ordered list. -/
def eventProbabilityProduct [MeasurableSpace Omega]
    (mu : Measure Omega) (events : List (Set Omega)) : ℝ :=
  (events.map mu.real).prod

@[simp]
theorem eventProbabilityProduct_nil [MeasurableSpace Omega] (mu : Measure Omega) :
    eventProbabilityProduct mu [] = 1 := rfl

@[simp]
theorem eventProbabilityProduct_cons [MeasurableSpace Omega]
    (mu : Measure Omega) (A : Set Omega) (events : List (Set Omega)) :
    eventProbabilityProduct mu (A :: events) =
      mu.real A * eventProbabilityProduct mu events := rfl

/-- Product of the upper multiplicative factors accumulated while exposing
successive gaps. -/
def relativeErrorMultiplier (errors : List ℝ) : ℝ :=
  (errors.map fun epsilon ↦ 1 + epsilon).prod

@[simp]
theorem relativeErrorMultiplier_nil : relativeErrorMultiplier [] = 1 := rfl

@[simp]
theorem relativeErrorMultiplier_cons (epsilon : ℝ) (errors : List ℝ) :
    relativeErrorMultiplier (epsilon :: errors) =
      (1 + epsilon) * relativeErrorMultiplier errors := rfl

/-- Recursive record of the actual two-block relative-mixing estimates along
an ordered event list.  For `A :: B :: events`, the head estimate compares
`A` with the entire future intersection `B ∩ ⋂ events`; the tail stores the
remaining estimates.  Thus no pair is declared independent. -/
inductive SequentialEventRelativeMixing [MeasurableSpace Omega]
    (mu : Measure Omega) : List ℝ → List (Set Omega) → Prop
  | nil : SequentialEventRelativeMixing mu [] []
  | singleton (A : Set Omega) : SequentialEventRelativeMixing mu [] [A]
  | cons {epsilon : ℝ} {errors : List ℝ} {A B : Set Omega}
      {events : List (Set Omega)}
      (head :
        |mu.real (A ∩ orderedEventIntersection (B :: events)) -
            mu.real A * mu.real (orderedEventIntersection (B :: events))| ≤
          epsilon * mu.real A *
            mu.real (orderedEventIntersection (B :: events)))
      (tail : SequentialEventRelativeMixing mu errors (B :: events)) :
      SequentialEventRelativeMixing mu (epsilon :: errors) (A :: B :: events)

/-- Finite intersections of measurable listed events are measurable. -/
theorem measurableSet_orderedEventIntersection [m : MeasurableSpace Omega]
    {events : List (Set Omega)}
    (hEvents : ∀ A ∈ events, @MeasurableSet Omega m A) :
    @MeasurableSet Omega m (orderedEventIntersection events) := by
  induction events with
  | nil => exact MeasurableSet.univ
  | cons A events ih =>
      exact (hEvents A (by simp)).inter <|
        ih fun B hB ↦ hEvents B (by simp [hB])

/-- One application of `EventRelativeMixing` supplies the head estimate in
the recursive sequential record.  This is the bridge from the two-sigma-field
mixing theorem to the finite rare-event iteration. -/
theorem EventRelativeMixing.sequential_cons
    (mHead mTail : MeasurableSpace Omega) [mAmbient : MeasurableSpace Omega]
    (mu : Measure Omega) (epsilon : ℝ)
    (hmix : EventRelativeMixing mHead mTail mu epsilon)
    {errors : List ℝ} {A B : Set Omega} {events : List (Set Omega)}
    (hA : @MeasurableSet Omega mHead A)
    (hTail : @MeasurableSet Omega mTail
      (orderedEventIntersection (B :: events)))
    (hrest : SequentialEventRelativeMixing mu errors (B :: events)) :
    SequentialEventRelativeMixing mu (epsilon :: errors) (A :: B :: events) :=
  .cons (hmix A (orderedEventIntersection (B :: events)) hA hTail) hrest

theorem relativeErrorMultiplier_nonneg {errors : List ℝ}
    (herrors : ∀ epsilon ∈ errors, 0 ≤ epsilon) :
    0 ≤ relativeErrorMultiplier errors := by
  induction errors with
  | nil => simp
  | cons epsilon errors ih =>
      rw [relativeErrorMultiplier_cons]
      exact mul_nonneg (by linarith [herrors epsilon (by simp)]) <|
        ih fun eta heta ↦ herrors eta (by simp [heta])

theorem one_le_relativeErrorMultiplier {errors : List ℝ}
    (herrors : ∀ epsilon ∈ errors, 0 ≤ epsilon) :
    1 ≤ relativeErrorMultiplier errors := by
  induction errors with
  | nil => simp
  | cons epsilon errors ih =>
      rw [relativeErrorMultiplier_cons]
      have hepsilon : 1 ≤ 1 + epsilon := by
        linarith [herrors epsilon (by simp)]
      have htail := ih fun eta heta ↦ herrors eta (by simp [heta])
      exact one_le_mul_of_one_le_of_one_le hepsilon htail

theorem eventProbabilityProduct_nonneg [MeasurableSpace Omega]
    (mu : Measure Omega) (events : List (Set Omega)) :
    0 ≤ eventProbabilityProduct mu events := by
  induction events with
  | nil => simp
  | cons A events ih =>
      rw [eventProbabilityProduct_cons]
      exact mul_nonneg (measureReal_nonneg) ih

private theorem exists_relative_error_factor
    {x base epsilon : ℝ} (hbase : 0 ≤ base) (hepsilon : 0 ≤ epsilon)
    (hrelative : |x - base| ≤ epsilon * base) :
    ∃ delta : ℝ, |delta| ≤ epsilon ∧ x = (1 + delta) * base := by
  by_cases hbaseZero : base = 0
  · subst base
    have hxAbs : |x| = 0 := by
      apply le_antisymm
      · simpa using! hrelative
      · exact abs_nonneg x
    have hx : x = 0 := abs_eq_zero.mp hxAbs
    exact ⟨0, by simpa using! hepsilon, by simp [hx]⟩
  · have hbasePos : 0 < base := lt_of_le_of_ne hbase (Ne.symm hbaseZero)
    refine ⟨x / base - 1, ?_, ?_⟩
    · have hrewrite : x / base - 1 = (x - base) / base := by
        field_simp
      rw [hrewrite, abs_div, abs_of_pos hbasePos]
      exact (div_le_iff₀ hbasePos).2 hrelative
    · field_simp
      ring

/-- Exact multiplicative factorization.  It constructs one realized error
`delta_j` for every mixing gap, bounds it by that gap's prescribed
`epsilon_j`, and keeps all factors rather than collapsing them into big-O
notation. -/
theorem SequentialEventRelativeMixing.exists_multiplicative_error_factors
    [MeasurableSpace Omega] (mu : Measure Omega) [IsProbabilityMeasure mu]
    {errors : List ℝ} {events : List (Set Omega)}
    (hmix : SequentialEventRelativeMixing mu errors events)
    (herrors : ∀ epsilon ∈ errors, 0 ≤ epsilon) :
    ∃ deltas : List ℝ,
      List.Forall₂ (fun delta epsilon ↦ |delta| ≤ epsilon) deltas errors ∧
      mu.real (orderedEventIntersection events) =
        relativeErrorMultiplier deltas * eventProbabilityProduct mu events := by
  induction hmix with
  | nil =>
      exact ⟨[], .nil, by simp [measureReal_def]⟩
  | singleton A =>
      exact ⟨[], .nil, by simp⟩
  | @cons epsilon errors A B events hhead htail ih =>
      have hepsilon : 0 ≤ epsilon := herrors epsilon (by simp)
      have htailErrors : ∀ eta ∈ errors, 0 ≤ eta :=
        fun eta heta ↦ herrors eta (by simp [heta])
      obtain ⟨deltas, hdeltas, htailFactor⟩ := ih htailErrors
      have hbase :
          0 ≤ mu.real A * mu.real (orderedEventIntersection (B :: events)) :=
        mul_nonneg measureReal_nonneg measureReal_nonneg
      obtain ⟨delta, hdelta, hheadFactor⟩ :=
        exists_relative_error_factor
          (x := mu.real (A ∩ orderedEventIntersection (B :: events)))
          hbase hepsilon (by simpa only [mul_assoc] using! hhead)
      refine ⟨delta :: deltas, .cons hdelta hdeltas, ?_⟩
      rw [orderedEventIntersection_cons, relativeErrorMultiplier_cons,
        eventProbabilityProduct_cons, hheadFactor, htailFactor]
      ring

/-- Replace the internally stored one-event probabilities by any explicitly
identified values. -/
theorem eventProbabilityProduct_eq_of_single_probabilities
    [MeasurableSpace Omega] (mu : Measure Omega) {events : List (Set Omega)}
    (probability : Set Omega → ℝ)
    (hprobability : ∀ A ∈ events, mu.real A = probability A) :
    eventProbabilityProduct mu events = (events.map probability).prod := by
  induction events with
  | nil => simp
  | cons A events ih =>
      rw [eventProbabilityProduct_cons, hprobability A (by simp), List.map_cons,
        List.prod_cons, ih]
      exact fun B hB ↦ hprobability B (by simp [hB])

/-- Exact factorization with user-supplied formulas for all one-event
probabilities. -/
theorem SequentialEventRelativeMixing.exists_multiplicative_error_factors_of_single_probabilities
    [MeasurableSpace Omega] (mu : Measure Omega) [IsProbabilityMeasure mu]
    {errors : List ℝ} {events : List (Set Omega)}
    (hmix : SequentialEventRelativeMixing mu errors events)
    (herrors : ∀ epsilon ∈ errors, 0 ≤ epsilon)
    (probability : Set Omega → ℝ)
    (hprobability : ∀ A ∈ events, mu.real A = probability A) :
    ∃ deltas : List ℝ,
      List.Forall₂ (fun delta epsilon ↦ |delta| ≤ epsilon) deltas errors ∧
      mu.real (orderedEventIntersection events) =
        relativeErrorMultiplier deltas * (events.map probability).prod := by
  obtain ⟨deltas, hdeltas, hfactor⟩ :=
    hmix.exists_multiplicative_error_factors mu herrors
  refine ⟨deltas, hdeltas, ?_⟩
  rw [hfactor, eventProbabilityProduct_eq_of_single_probabilities
    mu probability hprobability]

/-- Iterated quasi-Bernoulli upper bound with every gap error retained. -/
theorem SequentialEventRelativeMixing.measure_intersection_le
    [MeasurableSpace Omega] (mu : Measure Omega) [IsProbabilityMeasure mu]
    {errors : List ℝ} {events : List (Set Omega)}
    (hmix : SequentialEventRelativeMixing mu errors events)
    (herrors : ∀ epsilon ∈ errors, 0 ≤ epsilon) :
    mu.real (orderedEventIntersection events) ≤
      relativeErrorMultiplier errors * eventProbabilityProduct mu events := by
  induction hmix with
  | nil => simp [measureReal_def]
  | singleton A => simp
  | @cons epsilon errors A B events hhead htail ih =>
      have hepsilon : 0 ≤ epsilon := herrors epsilon (by simp)
      have htailErrors : ∀ eta ∈ errors, 0 ≤ eta :=
        fun eta heta ↦ herrors eta (by simp [heta])
      have hheadUpper :
          mu.real (A ∩ orderedEventIntersection (B :: events)) ≤
            (1 + epsilon) * mu.real A *
              mu.real (orderedEventIntersection (B :: events)) := by
        calc
          mu.real (A ∩ orderedEventIntersection (B :: events)) =
              (mu.real (A ∩ orderedEventIntersection (B :: events)) -
                mu.real A * mu.real (orderedEventIntersection (B :: events))) +
                mu.real A * mu.real (orderedEventIntersection (B :: events)) := by ring
          _ ≤ epsilon * mu.real A *
                mu.real (orderedEventIntersection (B :: events)) +
                mu.real A * mu.real (orderedEventIntersection (B :: events)) := by
              gcongr
              exact (le_abs_self _).trans hhead
          _ = (1 + epsilon) * mu.real A *
                mu.real (orderedEventIntersection (B :: events)) := by ring
      rw [orderedEventIntersection_cons, relativeErrorMultiplier_cons,
        eventProbabilityProduct_cons]
      calc
        mu.real (A ∩ orderedEventIntersection (B :: events)) ≤
            (1 + epsilon) * mu.real A *
              mu.real (orderedEventIntersection (B :: events)) := hheadUpper
        _ ≤ (1 + epsilon) * mu.real A *
              (relativeErrorMultiplier errors *
                eventProbabilityProduct mu (B :: events)) := by
            exact mul_le_mul_of_nonneg_left (ih htailErrors) <|
              mul_nonneg (by linarith) measureReal_nonneg
        _ = ((1 + epsilon) * relativeErrorMultiplier errors) *
              (mu.real A * eventProbabilityProduct mu (B :: events)) := by ring

/-- Full product-factorization error.  In contrast with an additive union
bound, the coefficient is exactly the accumulated multiplier
`prod (1 + epsilon_j) - 1`. -/
theorem SequentialEventRelativeMixing.abs_measure_intersection_sub_product_le
    [MeasurableSpace Omega] (mu : Measure Omega) [IsProbabilityMeasure mu]
    {errors : List ℝ} {events : List (Set Omega)}
    (hmix : SequentialEventRelativeMixing mu errors events)
    (herrors : ∀ epsilon ∈ errors, 0 ≤ epsilon) :
    |mu.real (orderedEventIntersection events) - eventProbabilityProduct mu events| ≤
      (relativeErrorMultiplier errors - 1) * eventProbabilityProduct mu events := by
  induction hmix with
  | nil => simp [measureReal_def]
  | singleton A => simp
  | @cons epsilon errors A B events hhead htail ih =>
      have hepsilon : 0 ≤ epsilon := herrors epsilon (by simp)
      have htailErrors : ∀ eta ∈ errors, 0 ≤ eta :=
        fun eta heta ↦ herrors eta (by simp [heta])
      have htailUpper := htail.measure_intersection_le mu htailErrors
      have ha0 : 0 ≤ mu.real A := measureReal_nonneg
      have htailMultiplierOne : 1 ≤ relativeErrorMultiplier errors :=
        one_le_relativeErrorMultiplier htailErrors
      have htailProduct0 : 0 ≤ eventProbabilityProduct mu (B :: events) :=
        eventProbabilityProduct_nonneg mu (B :: events)
      rw [orderedEventIntersection_cons, relativeErrorMultiplier_cons,
        eventProbabilityProduct_cons]
      have hdecomp :
          mu.real (A ∩ orderedEventIntersection (B :: events)) -
              mu.real A * eventProbabilityProduct mu (B :: events) =
            (mu.real (A ∩ orderedEventIntersection (B :: events)) -
              mu.real A * mu.real (orderedEventIntersection (B :: events))) +
            mu.real A *
              (mu.real (orderedEventIntersection (B :: events)) -
                eventProbabilityProduct mu (B :: events)) := by ring
      rw [hdecomp]
      calc
        |(mu.real (A ∩ orderedEventIntersection (B :: events)) -
              mu.real A * mu.real (orderedEventIntersection (B :: events))) +
            mu.real A *
              (mu.real (orderedEventIntersection (B :: events)) -
                eventProbabilityProduct mu (B :: events))| ≤
            |mu.real (A ∩ orderedEventIntersection (B :: events)) -
              mu.real A * mu.real (orderedEventIntersection (B :: events))| +
            |mu.real A *
              (mu.real (orderedEventIntersection (B :: events)) -
                eventProbabilityProduct mu (B :: events))| := abs_add_le _ _
        _ = |mu.real (A ∩ orderedEventIntersection (B :: events)) -
              mu.real A * mu.real (orderedEventIntersection (B :: events))| +
            mu.real A *
              |mu.real (orderedEventIntersection (B :: events)) -
                eventProbabilityProduct mu (B :: events)| := by
              rw [abs_mul, abs_of_nonneg ha0]
        _ ≤ epsilon * mu.real A *
              mu.real (orderedEventIntersection (B :: events)) +
            mu.real A * ((relativeErrorMultiplier errors - 1) *
              eventProbabilityProduct mu (B :: events)) := by
              exact add_le_add hhead (mul_le_mul_of_nonneg_left (ih htailErrors) ha0)
        _ ≤ epsilon * mu.real A *
              (relativeErrorMultiplier errors *
                eventProbabilityProduct mu (B :: events)) +
            mu.real A * ((relativeErrorMultiplier errors - 1) *
              eventProbabilityProduct mu (B :: events)) := by
              gcongr
        _ = ((1 + epsilon) * relativeErrorMultiplier errors - 1) *
              (mu.real A * eventProbabilityProduct mu (B :: events)) := by ring

/-- The recursive record has exactly one fewer gap error than events whenever
the event list is nonempty. -/
theorem SequentialEventRelativeMixing.length_errors_add_one
    [MeasurableSpace Omega] {mu : Measure Omega}
    {errors : List ℝ} {events : List (Set Omega)}
    (hmix : SequentialEventRelativeMixing mu errors events)
    (hne : events ≠ []) : errors.length + 1 = events.length := by
  induction hmix with
  | nil => exact (hne rfl).elim
  | singleton A => simp
  | @cons epsilon errors A B events hhead htail ih =>
      have htailNe : B :: events ≠ [] := by simp
      simpa [Nat.add_assoc] using! congrArg Nat.succ (ih htailNe)

/-- Bounding every individual mixing error by `eta` gives the explicit
uniform-gap multiplier `(1 + eta) ^ numberOfGaps`. -/
theorem relativeErrorMultiplier_le_pow {errors : List ℝ} {eta : ℝ}
    (heta : 0 ≤ eta)
    (hbound : ∀ epsilon ∈ errors, 0 ≤ epsilon ∧ epsilon ≤ eta) :
    relativeErrorMultiplier errors ≤ (1 + eta) ^ errors.length := by
  induction errors with
  | nil => simp
  | cons epsilon errors ih =>
      rw [relativeErrorMultiplier_cons, List.length_cons, pow_succ']
      have hepsilon := hbound epsilon (by simp)
      have htail := ih fun delta hdelta ↦ hbound delta (by simp [hdelta])
      exact mul_le_mul (by linarith) htail
        (relativeErrorMultiplier_nonneg fun delta hdelta ↦
          (hbound delta (by simp [hdelta])).1)
        (by positivity)

/-- Uniform-error version of the quasi-Bernoulli estimate, ready to sum over
ordered tuples in a factorial-moment expansion. -/
theorem SequentialEventRelativeMixing.measure_intersection_le_pow
    [MeasurableSpace Omega] (mu : Measure Omega) [IsProbabilityMeasure mu]
    {errors : List ℝ} {events : List (Set Omega)} {eta : ℝ}
    (hmix : SequentialEventRelativeMixing mu errors events)
    (heta : 0 ≤ eta)
    (hbound : ∀ epsilon ∈ errors, 0 ≤ epsilon ∧ epsilon ≤ eta) :
    mu.real (orderedEventIntersection events) ≤
      (1 + eta) ^ errors.length * eventProbabilityProduct mu events := by
  calc
    mu.real (orderedEventIntersection events) ≤
        relativeErrorMultiplier errors * eventProbabilityProduct mu events :=
      hmix.measure_intersection_le mu fun epsilon hepsilon ↦
        (hbound epsilon hepsilon).1
    _ ≤ (1 + eta) ^ errors.length * eventProbabilityProduct mu events :=
      mul_le_mul_of_nonneg_right (relativeErrorMultiplier_le_pow heta hbound)
        (eventProbabilityProduct_nonneg mu events)

/-- The same uniform-gap hypothesis gives an explicit relative
factorization error. -/
theorem SequentialEventRelativeMixing.abs_measure_intersection_sub_product_le_pow
    [MeasurableSpace Omega] (mu : Measure Omega) [IsProbabilityMeasure mu]
    {errors : List ℝ} {events : List (Set Omega)} {eta : ℝ}
    (hmix : SequentialEventRelativeMixing mu errors events)
    (heta : 0 ≤ eta)
    (hbound : ∀ epsilon ∈ errors, 0 ≤ epsilon ∧ epsilon ≤ eta) :
    |mu.real (orderedEventIntersection events) - eventProbabilityProduct mu events| ≤
      ((1 + eta) ^ errors.length - 1) * eventProbabilityProduct mu events := by
  have herrors : ∀ epsilon ∈ errors, 0 ≤ epsilon :=
    fun epsilon hepsilon ↦ (hbound epsilon hepsilon).1
  calc
    |mu.real (orderedEventIntersection events) - eventProbabilityProduct mu events| ≤
        (relativeErrorMultiplier errors - 1) *
          eventProbabilityProduct mu events :=
      hmix.abs_measure_intersection_sub_product_le mu herrors
    _ ≤ ((1 + eta) ^ errors.length - 1) *
          eventProbabilityProduct mu events := by
      exact mul_le_mul_of_nonneg_right
        (sub_le_sub_right (relativeErrorMultiplier_le_pow heta hbound) 1)
        (eventProbabilityProduct_nonneg mu events)

end

end Erdos1002
