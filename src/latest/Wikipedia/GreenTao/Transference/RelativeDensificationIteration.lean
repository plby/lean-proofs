import Wikipedia.GreenTao.Transference.RelativeDensification

/-!
# Finite iteration of relative densification losses

This file supplies the bookkeeping layer which is valid independently of
how a densified pairing is represented as the next multilinear counting
problem.

A `RelativeDensificationState` carries both the current mathematical
payload and the real number which is claimed to be its count.  An iteration
is a finite prefix of such states, together with:

* an explicit invariant at every state in the prefix; and
* an explicit absolute count-loss estimate at every transition.

The endpoint estimate is then an exact finite telescoping argument.  The AP
specialization below uses the proved one-colour densification estimate for
the first transition.  Its later transitions remain hypotheses: in
particular, this file does not assert that `apOneColorDensifiedPairing`
already has the structural form needed for another application of
densification.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-! ## Abstract finite count-loss iterations -/

/-- A state in a relative densification argument.  The payload may contain
the current multilinear system, its distinguished face, and any boundedness
certificates needed by the next step.  The `count` field records the scalar
quantity which telescopes.

When successive stages have different concrete types, `Payload` can be a
dependent sum containing all stage-indexed payload types. -/
structure RelativeDensificationState (Payload : Type*) where
  payload : Payload
  count : ℝ

/-- The assertion that one transition changes its recorded count by at most
`ε`.  This predicate deliberately contains no structural conclusion: such a
conclusion belongs in the state invariant supplied by the application. -/
def RelativeDensificationCountLoss
    {Payload : Type*}
    (fromState toState : RelativeDensificationState Payload)
    (ε : ℝ) : Prop :=
  |fromState.count - toState.count| ≤ ε

/-- A finite relative densification iteration of `length` transitions.

Only the prefix indexed by `0, ..., length` is constrained.  Thus the
function representation of `state` and `error` is merely an indexing
convenience: `valid` and `countLoss` quantify over a genuinely finite
prefix, and all totals below use `Finset.range length`. -/
structure RelativeDensificationIteration
    (Payload : Type*)
    (Invariant : RelativeDensificationState Payload → Prop) where
  length : ℕ
  state : ℕ → RelativeDensificationState Payload
  error : ℕ → ℝ
  valid :
    ∀ i, i ≤ length → Invariant (state i)
  countLoss :
    ∀ i, i < length →
      RelativeDensificationCountLoss (state i) (state (i + 1)) (error i)

namespace RelativeDensificationIteration

variable {Payload : Type*}
  {Invariant : RelativeDensificationState Payload → Prop}

/-- The count before any transition. -/
def initialCount
    (iteration : RelativeDensificationIteration Payload Invariant) : ℝ :=
  (iteration.state 0).count

/-- The count after the last transition. -/
def finalCount
    (iteration : RelativeDensificationIteration Payload Invariant) : ℝ :=
  (iteration.state iteration.length).count

/-- The sum of all certified transition losses. -/
def totalError
    (iteration : RelativeDensificationIteration Payload Invariant) : ℝ :=
  ∑ i ∈ Finset.range iteration.length, iteration.error i

/-- The initial state satisfies the application-supplied invariant. -/
theorem initial_valid
    (iteration : RelativeDensificationIteration Payload Invariant) :
    Invariant (iteration.state 0) :=
  iteration.valid 0 (Nat.zero_le _)

/-- The final state satisfies the application-supplied invariant. -/
theorem final_valid
    (iteration : RelativeDensificationIteration Payload Invariant) :
    Invariant (iteration.state iteration.length) :=
  iteration.valid iteration.length le_rfl

/-- Every error used by an iteration is automatically nonnegative. -/
theorem error_nonneg
    (iteration : RelativeDensificationIteration Payload Invariant)
    {i : ℕ} (hi : i < iteration.length) :
    0 ≤ iteration.error i :=
  (abs_nonneg
    ((iteration.state i).count -
      (iteration.state (i + 1)).count)).trans
    (iteration.countLoss i hi)

/-- The accumulated error of a certified iteration is nonnegative. -/
theorem totalError_nonneg
    (iteration : RelativeDensificationIteration Payload Invariant) :
    0 ≤ iteration.totalError := by
  apply Finset.sum_nonneg
  intro i hi
  exact iteration.error_nonneg (Finset.mem_range.mp hi)

/-- The exact scalar telescoping identity underlying the iteration. -/
theorem count_sub_eq_sum_transitionDifference
    (iteration : RelativeDensificationIteration Payload Invariant) :
    iteration.initialCount - iteration.finalCount =
      ∑ i ∈ Finset.range iteration.length,
        ((iteration.state i).count -
          (iteration.state (i + 1)).count) := by
  exact
    (Finset.sum_range_sub'
      (fun i => (iteration.state i).count)
      iteration.length).symm

/-- Successive absolute count losses add.  No monotonicity of the counts is
required. -/
theorem abs_initialCount_sub_finalCount_le_totalError
    (iteration : RelativeDensificationIteration Payload Invariant) :
    |iteration.initialCount - iteration.finalCount| ≤
      iteration.totalError := by
  rw [iteration.count_sub_eq_sum_transitionDifference]
  calc
    |∑ i ∈ Finset.range iteration.length,
        ((iteration.state i).count -
          (iteration.state (i + 1)).count)| ≤
        ∑ i ∈ Finset.range iteration.length,
          |(iteration.state i).count -
            (iteration.state (i + 1)).count| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.range iteration.length,
          iteration.error i := by
      apply Finset.sum_le_sum
      intro i hi
      exact iteration.countLoss i (Finset.mem_range.mp hi)

/-- Endpoint form with externally named initial and final counts. -/
theorem abs_endpoint_sub_le_totalError
    (iteration : RelativeDensificationIteration Payload Invariant)
    {initial final : ℝ}
    (hinitial : iteration.initialCount = initial)
    (hfinal : iteration.finalCount = final) :
    |initial - final| ≤ iteration.totalError := by
  rw [← hinitial, ← hfinal]
  exact iteration.abs_initialCount_sub_finalCount_le_totalError

end RelativeDensificationIteration

/-! ## AP-simplex specialization -/

/-- Start with the proved one-colour AP densification step, and then
telescope any explicitly certified finite chain beginning at its densified
pairing.

The hypothesis `hstart` is the structural handoff: an application must
identify the first abstract state count with
`apOneColorDensifiedPairing`.  The iteration invariant and its `countLoss`
field must certify every later representation and loss.  Consequently this
theorem does not manufacture the still-missing lower-complexity
multilinear-system transition. -/
theorem HasLinearFormsCondition.abs_apOneColorMixedSimplexCount_sub_iterationFinal_le
    {n N : ℕ} [NeZero N]
    {ν f g : ZMod N → ℝ} {η : ℝ}
    (hLF : HasLinearFormsCondition (n + 1) N ν η)
    (hf0 : ∀ z, 0 ≤ f z)
    (hf1 : ∀ z, f z ≤ 1)
    (hg0 : ∀ z, 0 ≤ g z)
    (hgν : ∀ z, g z ≤ ν z)
    (j : Fin (n + 1))
    {Payload : Type*}
    {Invariant : RelativeDensificationState Payload → Prop}
    (iteration : RelativeDensificationIteration Payload Invariant)
    (hstart :
      iteration.initialCount =
        apOneColorDensifiedPairing n N f g j) :
    |(apOneColorMixedSimplexSystem n N f g j).simplexCount -
        iteration.finalCount| ≤
      Real.sqrt (3 * η) + iteration.totalError := by
  have hfirst :
      |(apOneColorMixedSimplexSystem n N f g j).simplexCount -
          apOneColorDensifiedPairing n N f g j| ≤
        Real.sqrt (3 * η) :=
    hLF.abs_apOneColorMixedSimplexCount_sub_densifiedPairing_le
      hf0 hf1 hg0 hgν j
  have htail :
      |apOneColorDensifiedPairing n N f g j -
          iteration.finalCount| ≤
        iteration.totalError := by
    rw [← hstart]
    exact iteration.abs_initialCount_sub_finalCount_le_totalError
  calc
    |(apOneColorMixedSimplexSystem n N f g j).simplexCount -
        iteration.finalCount| =
        |((apOneColorMixedSimplexSystem n N f g j).simplexCount -
            apOneColorDensifiedPairing n N f g j) +
          (apOneColorDensifiedPairing n N f g j -
            iteration.finalCount)| := by
      congr 1
      ring
    _ ≤
        |(apOneColorMixedSimplexSystem n N f g j).simplexCount -
            apOneColorDensifiedPairing n N f g j| +
          |apOneColorDensifiedPairing n N f g j -
            iteration.finalCount| :=
      abs_add_le _ _
    _ ≤ Real.sqrt (3 * η) + iteration.totalError :=
      add_le_add hfirst htail

end Wikipedia.SzemeredisTheorem
