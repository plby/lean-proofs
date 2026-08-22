/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors.
-/

import ErdosProblems.Erdos1165.BoundaryVisitRegeneration
import ErdosProblems.Erdos1165.HLOZGapPointReturn

/-!
# Source-correct future factors in the HLOZ upper transition

The proof of HLOZ Proposition 4.7 does not bound an unrestricted future by
changing the lazy coordinates of a stopped prefix.  At the `k`-th creation
clock it first filters the stopped history by the balance, candidate-count,
late-clock, and gap screens.  Only then does strong Markov supply one new
factor: in the fresh translated walk, the old favorite must be avoided until
the spatial scale selected by the branch has been crossed.

This file formalizes that separation.  A `FullTailFutureFactorCertificate`
contains only stopped-past observability, a pathwise containment in a fresh
future event, and a bound for that fresh walk event.  The relative transition
inequality is proved from the full-tail strong Markov theorem; it is
deliberately not a field of the certificate.

`BoundaryEscapeFutureFactorCertificate` is the specialization used in
Proposition 4.7.  Its future event is the complement of returning to the
origin before hitting the selected boundary.  Thus its only analytic input is
the one-walk escape probability, not a transition probability involving an
unrestricted continuation.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace Erdos1165.HLOZSourceCorrectFutureTransition

open BoundaryVisitRegeneration HLOZGapPointReturn

noncomputable section

/-! ## One full-tail strong-Markov factor -/

/-- Source-correct data for one transition after a filtered stopped history.

`past` is the filtered history event and `next` is the event after creating
one additional favorite.  The last field is only a deterministic pathwise
containment.  In particular, the structure has no field of the form
`P(next) <= q P(past)`; that inequality is derived below by strong Markov. -/
structure FullTailFutureFactorCertificate
    (State : Type*) [Countable State]
    (past next : Set WalkPath) (q : ℝ≥0∞) where
  stop : StepPath → ℕ
  location : StepPath → State
  stop_isStopping : IsFiniteStoppingTime stop
  pastFiber_observable : ∀ x,
    IsMeasurableAtStopping stop
      ((trajectory ⁻¹' past) ∩ {w | location w = x})
  future : State → Set StepPath
  future_measurable : ∀ x, MeasurableSet (future x)
  freshWalk_le : ∀ x,
    ((trajectory ⁻¹' past) ∩ {w | location w = x}).Nonempty →
      fairSteps (future x) ≤ q
  next_subset : trajectory ⁻¹' next ⊆
    {w | w ∈ trajectory ⁻¹' past ∧
      postStoppingSteps stop w ∈ future (location w)}

/-- One HLOZ transition factor, derived from the stopped history and the
fresh-walk event by full-tail strong Markov. -/
theorem FullTailFutureFactorCertificate.measure_next_le
    {State : Type*} [Countable State]
    {past next : Set WalkPath} {q : ℝ≥0∞}
    (cert : FullTailFutureFactorCertificate State past next q)
    (hpast : MeasurableSet past) (hnext : MeasurableSet next) :
    simpleRandomWalk next ≤ simpleRandomWalk past * q := by
  have hmarkov := strongMarkov_fullTail_spatial_le
    cert.stop_isStopping cert.future q cert.pastFiber_observable
    cert.future_measurable cert.freshWalk_le
  rw [simpleRandomWalk,
    Measure.map_apply measurable_trajectory hnext,
    Measure.map_apply measurable_trajectory hpast]
  exact (measure_mono cert.next_subset).trans hmarkov

/-! ## The literal escape-before-positive-return future -/

/-- The mass of escaping to `boundary` before the first positive return is
exactly the `ENNReal` coercion of the regenerative escape probability. -/
theorem fairSteps_compl_positiveReturnBeforeBoundary
    (boundary : Set Point) :
    fairSteps (positiveReturnBeforeBoundary boundary)ᶜ =
      ENNReal.ofReal (escapeBeforePositiveReturnProbability boundary) := by
  rw [measure_compl (measurableSet_positiveReturnBeforeBoundary boundary)
    (measure_ne_top _ _), measure_univ]
  unfold escapeBeforePositiveReturnProbability
  rw [ENNReal.ofReal_sub 1 measureReal_nonneg]
  simp only [ENNReal.ofReal_one, measureReal_def]
  rw [ENNReal.ofReal_toReal (measure_ne_top _ _)]

/-- One future factor in the exact form used in HLOZ (4.36)--(4.37): after
the stopped history, the translated walk must reach a branch-dependent
boundary before its first positive return to the old favorite.

The boundary may depend on any countable stopped-past state.  `escape_le`
is a one-walk potential-theoretic estimate.  No probability of `next`, and no
conditional transition inequality, is assumed. -/
structure BoundaryEscapeFutureFactorCertificate
    (State : Type*) [Countable State]
    (past next : Set WalkPath) (q : ℝ≥0∞) where
  stop : StepPath → ℕ
  location : StepPath → State
  boundary : State → Set Point
  stop_isStopping : IsFiniteStoppingTime stop
  pastFiber_observable : ∀ x,
    IsMeasurableAtStopping stop
      ((trajectory ⁻¹' past) ∩ {w | location w = x})
  escape_le : ∀ x,
    ((trajectory ⁻¹' past) ∩ {w | location w = x}).Nonempty →
      ENNReal.ofReal
        (escapeBeforePositiveReturnProbability (boundary x)) ≤ q
  next_subset : trajectory ⁻¹' next ⊆
    {w | w ∈ trajectory ⁻¹' past ∧
      postStoppingSteps stop w ∈
        (positiveReturnBeforeBoundary (boundary (location w)))ᶜ}

/-- Forget the special form of the fresh escape event. -/
def BoundaryEscapeFutureFactorCertificate.toFullTail
    {State : Type*} [Countable State]
    {past next : Set WalkPath} {q : ℝ≥0∞}
    (cert : BoundaryEscapeFutureFactorCertificate State past next q) :
    FullTailFutureFactorCertificate State past next q where
  stop := cert.stop
  location := cert.location
  stop_isStopping := cert.stop_isStopping
  pastFiber_observable := cert.pastFiber_observable
  future := fun x ↦ (positiveReturnBeforeBoundary (cert.boundary x))ᶜ
  future_measurable := fun x ↦
    (measurableSet_positiveReturnBeforeBoundary (cert.boundary x)).compl
  freshWalk_le := fun x hx ↦ by
    rw [fairSteps_compl_positiveReturnBeforeBoundary]
    exact cert.escape_le x hx
  next_subset := cert.next_subset

/-- Strong Markov turns a literal escape-before-return certificate into the
relative transition factor. -/
theorem BoundaryEscapeFutureFactorCertificate.measure_next_le
    {State : Type*} [Countable State]
    {past next : Set WalkPath} {q : ℝ≥0∞}
    (cert : BoundaryEscapeFutureFactorCertificate State past next q)
    (hpast : MeasurableSet past) (hnext : MeasurableSet next) :
    simpleRandomWalk next ≤ simpleRandomWalk past * q :=
  cert.toFullTail.measure_next_le hpast hnext

/-! ## Countable stopped-clock atoms -/

/-- A future escape factor assembled from countably many disjoint stopped
history atoms.

This is the form needed for threshold-creation clocks.  On the atom where
the old creation time equals `n`, the constant time `n` is an honest finite
stopping time, so `atom i` can apply strong Markov without inventing a
global totalized creation clock.  The `nextPiece` family need not be
disjoint: countable subadditivity is enough on the future side.  Disjointness
is required only for the past pieces, where it recovers exactly the mass of
their union; that union need only be contained in `previous`.  This permits
the first transition to omit paths which never reach the first creation
clock while still comparing with the unit-mass event `Set.univ`. -/
structure CountableAtomFutureFactor
    (Index State : Type*) [Countable Index] [Countable State]
    (previous next : Set WalkPath) (q : ℝ≥0∞) where
  pastPiece : Index → Set WalkPath
  nextPiece : Index → Set WalkPath
  past_pairwise : Pairwise fun i j ↦
    Disjoint (pastPiece i) (pastPiece j)
  past_measurable : ∀ i, MeasurableSet (pastPiece i)
  next_measurable : ∀ i, MeasurableSet (nextPiece i)
  past_subset : (⋃ i, pastPiece i) ⊆ previous
  next_union : (⋃ i, nextPiece i) = next
  atom : ∀ i, BoundaryEscapeFutureFactorCertificate
    State (pastPiece i) (nextPiece i) q

/-- Countable subadditivity on the future pieces and disjoint additivity on
the stopped-past pieces turn the atomwise strong-Markov certificates into
one relative transition factor. -/
theorem CountableAtomFutureFactor.measure_next_le
    {Index State : Type*} [Countable Index] [Countable State]
    {previous next : Set WalkPath} {q : ℝ≥0∞}
    (cert : CountableAtomFutureFactor Index State previous next q) :
    simpleRandomWalk next ≤ simpleRandomWalk previous * q := by
  rw [← cert.next_union]
  calc
    simpleRandomWalk (⋃ i, cert.nextPiece i) ≤
        ∑' i, simpleRandomWalk (cert.nextPiece i) :=
      measure_iUnion_le _
    _ ≤ ∑' i, simpleRandomWalk (cert.pastPiece i) * q := by
      exact ENNReal.tsum_le_tsum fun i ↦
        (cert.atom i).measure_next_le
          (cert.past_measurable i) (cert.next_measurable i)
    _ = (∑' i, simpleRandomWalk (cert.pastPiece i)) * q := by
      rw [ENNReal.tsum_mul_right]
    _ = simpleRandomWalk (⋃ i : Index, cert.pastPiece i) * q := by
      rw [← measure_iUnion cert.past_pairwise cert.past_measurable]
    _ ≤ simpleRandomWalk previous * q := by
      have hpastMass :
          simpleRandomWalk (⋃ i : Index, cert.pastPiece i) ≤
            simpleRandomWalk previous := measure_mono cert.past_subset
      exact mul_le_mul_of_nonneg_right hpastMass
        (show (0 : ℝ≥0∞) ≤ q from bot_le)

/-! ## Three successive new-favorite factors -/

/-- The three future factors of Proposition 4.7.  The first starts from the
whole probability space; the next two start from the preceding cumulatively
filtered transition event.  The stopped-past state type may differ between
the three ranks. -/
structure ThreeBoundaryEscapeFutureFactors
    (State₁ State₂ State₃ : Type*)
    [Countable State₁] [Countable State₂] [Countable State₃]
    (first second third : Set WalkPath) (q : ℝ≥0∞) where
  firstFactor : BoundaryEscapeFutureFactorCertificate
    State₁ Set.univ first q
  secondFactor : BoundaryEscapeFutureFactorCertificate
    State₂ first second q
  thirdFactor : BoundaryEscapeFutureFactorCertificate
    State₃ second third q

/-- All three measure estimates, derived rather than assumed.  The factors
are returned in the multiplication order consumed by `UpperAssembly`. -/
theorem ThreeBoundaryEscapeFutureFactors.measure_estimates
    {State₁ State₂ State₃ : Type*}
    [Countable State₁] [Countable State₂] [Countable State₃]
    {first second third : Set WalkPath} {q : ℝ≥0∞}
    (cert : ThreeBoundaryEscapeFutureFactors
      State₁ State₂ State₃ first second third q)
    (hfirst : MeasurableSet first)
    (hsecond : MeasurableSet second)
    (hthird : MeasurableSet third) :
    simpleRandomWalk first ≤ q ∧
      simpleRandomWalk second ≤ q * simpleRandomWalk first ∧
      simpleRandomWalk third ≤ q * simpleRandomWalk second := by
  have h₁ := cert.firstFactor.measure_next_le MeasurableSet.univ hfirst
  have h₂ := cert.secondFactor.measure_next_le hfirst hsecond
  have h₃ := cert.thirdFactor.measure_next_le hsecond hthird
  constructor
  · simpa using h₁
  · exact ⟨by simpa [mul_comm] using h₂,
      by simpa [mul_comm] using h₃⟩

end

end Erdos1165.HLOZSourceCorrectFutureTransition
