/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors.
-/

import ErdosProblems.Erdos1165.HLOZSourceCorrectFutureTransition

/-!
# The stopped-history candidate factor in HLOZ Proposition 4.9

For a low spatial scale, one transition in Proposition 4.7 has two logically
different factors.

1. After the stopped external trace and its finite near-favorite set have
   been exposed, Proposition 4.9 bounds the chance that some member of that
   set lies in the smaller deficit window.  This is a finite union of exact
   conditional negative-binomial window ratios.
2. Starting at the old favorite clock, strong Markov bounds the fresh event
   that the old favorite is avoided until the required spatial boundary.

This module formalizes the first factor as a countable stopped-history
partition and then composes it with the second factor from
`HLOZSourceCorrectFutureTransition`.  Neither structure contains a bound for
the whole new-favorite transition.
-/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

namespace Erdos1165.HLOZStoppedHistoryCandidateFuture

open HLOZSourceCorrectFutureTransition

noncomputable section

/-! ## A finite candidate family on each stopped-history atom -/

/-- Literal stopped-history form of the last union bound in HLOZ
Proposition 4.9.

`piece h` is one atom after exposing the stopped external trace, the old
favorite locations, and the finite `kappaOne` near-favorite set.  The pieces
partition `previous`.  For each candidate in that finite set, `near h x` is
the event that its lazy coordinate lands in the smaller deficit window.
`coordinate_ratio` is the output of the exact product disintegration and the
negative-binomial window-ratio estimate.  It is a stopped-prefix coordinate
statement, not a future transition bound. -/
structure StoppedHistoryCandidateFamily
    (History Candidate : Type*) [Countable History]
    (previous : Set WalkPath) (budget : ℕ) (ratio : ℝ≥0∞) where
  piece : History → Set WalkPath
  candidates : History → Finset Candidate
  near : History → Candidate → Set WalkPath
  piece_pairwise : Pairwise fun h h' ↦ Disjoint (piece h) (piece h')
  piece_measurable : ∀ h, MeasurableSet (piece h)
  piece_union : (⋃ h, piece h) = previous
  candidate_card : ∀ h, (candidates h).card ≤ budget
  coordinate_ratio : ∀ h x, x ∈ candidates h →
    simpleRandomWalk (piece h ∩ near h x) ≤
      ratio * simpleRandomWalk (piece h)

/-- The event that at least one candidate in the exposed stopped-history
family enters the small deficit window. -/
def StoppedHistoryCandidateFamily.someCandidate
    {History Candidate : Type*} [Countable History]
    {previous : Set WalkPath} {budget : ℕ} {ratio : ℝ≥0∞}
    (family : StoppedHistoryCandidateFamily
      History Candidate previous budget ratio) : Set WalkPath :=
  ⋃ h, ⋃ x, ⋃ (_hx : x ∈ family.candidates h),
    family.piece h ∩ family.near h x

/-- Proposition 4.9's candidate factor: at most `budget` candidates, each
with conditional coordinate cost at most `ratio`, cost at most
`budget * ratio` relative to the preceding filtered event. -/
theorem StoppedHistoryCandidateFamily.measure_someCandidate_le
    {History Candidate : Type*} [Countable History]
    {previous : Set WalkPath} {budget : ℕ} {ratio : ℝ≥0∞}
    (family : StoppedHistoryCandidateFamily
      History Candidate previous budget ratio) :
    simpleRandomWalk family.someCandidate ≤
      (budget : ℝ≥0∞) * ratio * simpleRandomWalk previous := by
  let within : History → Set WalkPath := fun h ↦
    ⋃ x, ⋃ (_hx : x ∈ family.candidates h),
      family.piece h ∩ family.near h x
  have hwithin (h : History) :
      simpleRandomWalk (within h) ≤
        (budget : ℝ≥0∞) * ratio *
          simpleRandomWalk (family.piece h) := by
    have hraw : simpleRandomWalk (within h) ≤
        ∑ x ∈ family.candidates h,
          simpleRandomWalk (family.piece h ∩ family.near h x) := by
      dsimp only [within]
      exact measure_biUnion_finset_le (family.candidates h)
        (fun x ↦ family.piece h ∩ family.near h x)
    calc
      simpleRandomWalk (within h) ≤
          ∑ x ∈ family.candidates h,
            simpleRandomWalk (family.piece h ∩ family.near h x) := hraw
      _ ≤ ∑ _x ∈ family.candidates h,
            ratio * simpleRandomWalk (family.piece h) := by
        exact Finset.sum_le_sum fun x hx ↦ family.coordinate_ratio h x hx
      _ = ((family.candidates h).card : ℝ≥0∞) *
            (ratio * simpleRandomWalk (family.piece h)) := by simp
      _ ≤ (budget : ℝ≥0∞) *
            (ratio * simpleRandomWalk (family.piece h)) := by
        gcongr
        exact_mod_cast family.candidate_card h
      _ = (budget : ℝ≥0∞) * ratio *
            simpleRandomWalk (family.piece h) := by simp [mul_assoc]
  have hunion : family.someCandidate = ⋃ h, within h := by
    rfl
  rw [hunion]
  calc
    simpleRandomWalk (⋃ h, within h) ≤
        ∑' h, simpleRandomWalk (within h) := measure_iUnion_le _
    _ ≤ ∑' h, (budget : ℝ≥0∞) * ratio *
          simpleRandomWalk (family.piece h) := by
      exact ENNReal.tsum_le_tsum hwithin
    _ = (budget : ℝ≥0∞) * ratio *
          ∑' h, simpleRandomWalk (family.piece h) := by
      rw [ENNReal.tsum_mul_left]
    _ = (budget : ℝ≥0∞) * ratio *
          simpleRandomWalk previous := by
      rw [← measure_iUnion family.piece_pairwise family.piece_measurable,
        family.piece_union]

/-! ## Candidate ratio followed by the fresh escape factor -/

/-- Complete low-scale factor data.  The candidate screen concerns only the
stopped history.  The boundary escape certificate begins from the resulting
candidate event and contains only the later fresh-walk containment. -/
structure LowScaleCandidateEscapeFactor
    (History Candidate State : Type*)
    [Countable History] [Countable State]
    (previous next : Set WalkPath)
    (budget : ℕ) (candidateRatio escapeCost : ℝ≥0∞) where
  candidate : StoppedHistoryCandidateFamily
    History Candidate previous budget candidateRatio
  escape : BoundaryEscapeFutureFactorCertificate
    State candidate.someCandidate next escapeCost

/-- The low-scale transition cost is the product of the stopped-history
candidate ratio and one future avoidance factor.  This is the exact logical
order of HLOZ (4.37). -/
theorem LowScaleCandidateEscapeFactor.measure_next_le
    {History Candidate State : Type*}
    [Countable History] [Countable State]
    {previous next : Set WalkPath}
    {budget : ℕ} {candidateRatio escapeCost : ℝ≥0∞}
    (factor : LowScaleCandidateEscapeFactor History Candidate State
      previous next budget candidateRatio escapeCost)
    (hcandidate : MeasurableSet factor.candidate.someCandidate)
    (hnext : MeasurableSet next) :
    simpleRandomWalk next ≤
      ((budget : ℝ≥0∞) * candidateRatio * escapeCost) *
        simpleRandomWalk previous := by
  have hfuture := factor.escape.measure_next_le hcandidate hnext
  have hpast := factor.candidate.measure_someCandidate_le
  calc
    simpleRandomWalk next ≤
        simpleRandomWalk factor.candidate.someCandidate * escapeCost := hfuture
    _ ≤ ((budget : ℝ≥0∞) * candidateRatio *
          simpleRandomWalk previous) * escapeCost := by gcongr
    _ = ((budget : ℝ≥0∞) * candidateRatio * escapeCost) *
          simpleRandomWalk previous := by
      ac_rfl

/-- Low-scale source factor when the future escape is available on a
countable family of fixed stopped-clock atoms.  Proposition 4.9 first pays
the stopped-history candidate ratio; the countable atom factor then pays
exactly one future escape, independently of how many atoms are used to
disintegrate the random creation clock. -/
structure LowScaleCandidateAtomEscapeFactor
    (Index History Candidate State : Type*)
    [Countable Index] [Countable History] [Countable State]
    (previous next : Set WalkPath)
    (budget : ℕ) (candidateRatio escapeCost : ℝ≥0∞) where
  candidate : StoppedHistoryCandidateFamily
    History Candidate previous budget candidateRatio
  escape : CountableAtomFutureFactor Index State
    candidate.someCandidate next escapeCost

theorem LowScaleCandidateAtomEscapeFactor.measure_next_le
    {Index History Candidate State : Type*}
    [Countable Index] [Countable History] [Countable State]
    {previous next : Set WalkPath}
    {budget : ℕ} {candidateRatio escapeCost : ℝ≥0∞}
    (factor : LowScaleCandidateAtomEscapeFactor
      Index History Candidate State previous next budget
        candidateRatio escapeCost) :
    simpleRandomWalk next ≤
      ((budget : ℝ≥0∞) * candidateRatio * escapeCost) *
        simpleRandomWalk previous := by
  have hfuture := factor.escape.measure_next_le
  have hpast := factor.candidate.measure_someCandidate_le
  calc
    simpleRandomWalk next ≤
        simpleRandomWalk factor.candidate.someCandidate * escapeCost :=
      hfuture
    _ ≤ ((budget : ℝ≥0∞) * candidateRatio *
          simpleRandomWalk previous) * escapeCost := by
      gcongr
    _ = ((budget : ℝ≥0∞) * candidateRatio * escapeCost) *
          simpleRandomWalk previous := by
      ac_rfl

/-! ## One source branch: high spatial scale or low candidate scale -/

/-- A source-correct certificate for one new-favorite transition.

For a high spatial scale, the whole factor is the escape-before-return cost.
For a low spatial scale, the factor is the product of the Proposition 4.9
candidate ratio and the escape-before-return cost.  These are precisely the
two cases (4.36) and (4.37) in the source proof. -/
inductive SourceCorrectTransitionFactor
    (History Candidate State : Type*)
    [Countable History] [Countable State]
    (previous next : Set WalkPath) (q : ℝ≥0∞) : Type _
  | high (escapeCost : ℝ≥0∞)
      (escape : BoundaryEscapeFutureFactorCertificate
        State previous next escapeCost)
      (cost_le : escapeCost ≤ q)
  | low (budget : ℕ) (candidateRatio escapeCost : ℝ≥0∞)
      (factor : LowScaleCandidateEscapeFactor History Candidate State
        previous next budget candidateRatio escapeCost)
      (candidate_measurable : MeasurableSet factor.candidate.someCandidate)
      (cost_le : (budget : ℝ≥0∞) * candidateRatio * escapeCost ≤ q)
  | highAtomwise {Index : Type} [Countable Index]
      (escapeCost : ℝ≥0∞)
      (escape : CountableAtomFutureFactor
        Index State previous next escapeCost)
      (cost_le : escapeCost ≤ q)
  | lowAtomwise {Index : Type} [Countable Index]
      (budget : ℕ) (candidateRatio escapeCost : ℝ≥0∞)
      (factor : LowScaleCandidateAtomEscapeFactor
        Index History Candidate State previous next budget
          candidateRatio escapeCost)
      (cost_le : (budget : ℝ≥0∞) * candidateRatio * escapeCost ≤ q)

/-- In either source regime, the transition inequality follows from the
certificate.  No such inequality occurs among the constructors' fields. -/
theorem SourceCorrectTransitionFactor.measure_next_le
    {History Candidate State : Type*}
    [Countable History] [Countable State]
    {previous next : Set WalkPath} {q : ℝ≥0∞}
    (factor : SourceCorrectTransitionFactor
      History Candidate State previous next q)
    (hprevious : MeasurableSet previous) (hnext : MeasurableSet next) :
    simpleRandomWalk next ≤ q * simpleRandomWalk previous := by
  cases factor with
  | high escapeCost escape hcost =>
      have h := escape.measure_next_le hprevious hnext
      calc
        simpleRandomWalk next ≤
            simpleRandomWalk previous * escapeCost := h
        _ ≤ simpleRandomWalk previous * q := by gcongr
        _ = q * simpleRandomWalk previous := by ac_rfl
  | low budget candidateRatio escapeCost factor hcand hcost =>
      have h := factor.measure_next_le hcand hnext
      calc
        simpleRandomWalk next ≤
            ((budget : ℝ≥0∞) * candidateRatio * escapeCost) *
              simpleRandomWalk previous := h
        _ ≤ q * simpleRandomWalk previous := by gcongr
  | highAtomwise escapeCost escape hcost =>
      have h := escape.measure_next_le
      calc
        simpleRandomWalk next ≤
            simpleRandomWalk previous * escapeCost := h
        _ ≤ simpleRandomWalk previous * q := by gcongr
        _ = q * simpleRandomWalk previous := by ac_rfl
  | lowAtomwise budget candidateRatio escapeCost factor hcost =>
      have h := factor.measure_next_le
      calc
        simpleRandomWalk next ≤
            ((budget : ℝ≥0∞) * candidateRatio * escapeCost) *
              simpleRandomWalk previous := h
        _ ≤ q * simpleRandomWalk previous := by gcongr

/-- Three successive source-correct factors on cumulatively filtered events.
Using one common countable carrier for histories/candidates/states is no
restriction: the three rank-specific carriers may be embedded into finite
sum types. -/
structure ThreeSourceCorrectTransitionFactors
    (History Candidate State : Type*)
    [Countable History] [Countable State]
    (first second third : Set WalkPath) (q : ℝ≥0∞) where
  firstFactor : SourceCorrectTransitionFactor
    History Candidate State Set.univ first q
  secondFactor : SourceCorrectTransitionFactor
    History Candidate State first second q
  thirdFactor : SourceCorrectTransitionFactor
    History Candidate State second third q

/-- The three transition estimates needed by the finite-mesh endgame, all
derived from source-regime certificates. -/
theorem ThreeSourceCorrectTransitionFactors.measure_estimates
    {History Candidate State : Type*}
    [Countable History] [Countable State]
    {first second third : Set WalkPath} {q : ℝ≥0∞}
    (factors : ThreeSourceCorrectTransitionFactors
      History Candidate State first second third q)
    (hfirst : MeasurableSet first)
    (hsecond : MeasurableSet second)
    (hthird : MeasurableSet third) :
    simpleRandomWalk first ≤ q ∧
      simpleRandomWalk second ≤ q * simpleRandomWalk first ∧
      simpleRandomWalk third ≤ q * simpleRandomWalk second := by
  have h₁ := factors.firstFactor.measure_next_le MeasurableSet.univ hfirst
  have h₂ := factors.secondFactor.measure_next_le hfirst hsecond
  have h₃ := factors.thirdFactor.measure_next_le hsecond hthird
  exact ⟨by simpa using h₁, h₂, h₃⟩

end

end Erdos1165.HLOZStoppedHistoryCandidateFuture
