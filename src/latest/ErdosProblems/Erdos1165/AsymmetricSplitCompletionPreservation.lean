/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
import ErdosProblems.Erdos1165.AsymmetricSplitLevelSplice
import ErdosProblems.Erdos1165.AsymmetricPairSeparationGeometry

/-!
# Whole-path preservation for asymmetric split completion

The source extractor deletes only endpoint-matched `y` return intervals.
This file records the two global facts needed after they are reinserted:

* a replacement tuple confined to one regular profile disc preserves the
  first global exit; and
* a tuple with the same transition as the source tuple on every `x`
  scanner preserves the complete `x` excursion profile.

The compatibility predicate quantifies over the incoming scanner state.
Consequently the proof composes chronologically without storing or
reconstructing intermediate scanner states in the retained code.
-/

open Set

namespace Erdos1165.AsymmetricSplitCompletionPreservation

open AnnularProfileClocks TerminalGlobalExitSplice
open TerminalProfileClockEquivalence TerminalSkeletonWords
open ThickPoint

noncomputable section

attribute [local instance] Classical.propDecidable

noncomputable instance boundaryScanStateCountable :
    Countable BoundaryScanState :=
  (show Function.Injective
      (fun state : BoundaryScanState ↦
        (state.seekingOuter, state.completed)) by
    intro left right h
    cases left
    cases right
    simpa using h).countable

/-- Two endpoint-matched words have the same transition on every scanner
which contributes to the complete profile at `x`. -/
def XProfileScanCompatible
    (n : ℕ) (x start : Point)
    (source candidate : List Direction) : Prop :=
  ∀ k : Fin (n + 2), (k : ℕ) ≠ 0 → ∀ state : BoundaryScanState,
    scanWordFrom (profileOuterBoundary n (k : ℕ) x)
        (profileInnerBoundary n (k : ℕ) x) start state source =
      scanWordFrom (profileOuterBoundary n (k : ℕ) x)
        (profileInnerBoundary n (k : ℕ) x) start state candidate

/-! ## A countable code for universal scanner compatibility -/

/-- Add a fixed offset to the completed-excursion counter without changing
the scanner phase. -/
def shiftScanCompleted (c : ℕ) (state : BoundaryScanState) :
    BoundaryScanState :=
  ⟨state.seekingOuter, state.completed + c⟩

@[simp] theorem shiftScanCompleted_seekingOuter
    (c : ℕ) (state : BoundaryScanState) :
    (shiftScanCompleted c state).seekingOuter = state.seekingOuter := rfl

@[simp] theorem shiftScanCompleted_completed
    (c : ℕ) (state : BoundaryScanState) :
    (shiftScanCompleted c state).completed = state.completed + c := rfl

theorem visitBoundary_shiftScanCompleted
    (outer inner : Set Point) (c : ℕ)
    (state : BoundaryScanState) (z : Point) :
    visitBoundary outer inner (shiftScanCompleted c state) z =
      shiftScanCompleted c (visitBoundary outer inner state z) := by
  rcases state with ⟨seekingOuter, completed⟩
  cases seekingOuter <;>
    simp only [shiftScanCompleted, visitBoundary] <;>
    split_ifs <;> simp [Nat.add_assoc, Nat.add_comm]

/-- A word transition is affine in the incoming completed counter.  Hence
its values on the two zero-counter phases are a complete, countable
signature of its action on all scanner states. -/
theorem scanWordFrom_shiftScanCompleted
    (outer inner : Set Point) (start : Point) (c : ℕ)
    (state : BoundaryScanState) (word : List Direction) :
    scanWordFrom outer inner start (shiftScanCompleted c state) word =
      let result := scanWordFrom outer inner start state word
      (result.1, shiftScanCompleted c result.2) := by
  induction word generalizing start state with
  | nil => rfl
  | cons d tail ih =>
      simp only [scanWordFrom, List.foldl_cons]
      rw [visitBoundary_shiftScanCompleted]
      exact ih (Annulus.neighbor start d)
        (visitBoundary outer inner state (Annulus.neighbor start d))

/-- Finite scanner-transition signature of one return word. -/
abbrev XProfileScanSignatureData (n : ℕ) :=
  {k : Fin (n + 2) // (k : ℕ) ≠ 0} →
    Bool → Point × BoundaryScanState

/-- Finite scanner-transition signature of one return word. -/
def XProfileScanSignature
    (n : ℕ) (x start : Point) (word : List Direction) :
    XProfileScanSignatureData n :=
  fun k : {k : Fin (n + 2) // (k : ℕ) ≠ 0} ↦
    fun seekingOuter : Bool ↦
    scanWordFrom (profileOuterBoundary n (k.1 : ℕ) x)
      (profileInnerBoundary n (k.1 : ℕ) x) start
      ⟨seekingOuter, 0⟩ word

/-- Equality of the finite signature is equivalent to universal scanner
compatibility.  This lets global retained codes store a genuinely
countable transition class instead of a representative source word. -/
theorem xProfileScanCompatible_iff_signature_eq
    (n : ℕ) (x start : Point) (source candidate : List Direction) :
    XProfileScanCompatible n x start source candidate ↔
      XProfileScanSignature n x start source =
        XProfileScanSignature n x start candidate := by
  constructor
  · intro h
    funext k seekingOuter
    exact h k.1 k.2 ⟨seekingOuter, 0⟩
  · intro h k hk state
    have hbase := congrFun (congrFun h ⟨k, hk⟩) state.seekingOuter
    change scanWordFrom (profileOuterBoundary n (k : ℕ) x)
        (profileInnerBoundary n (k : ℕ) x) start
        ⟨state.seekingOuter, 0⟩ source =
      scanWordFrom (profileOuterBoundary n (k : ℕ) x)
        (profileInnerBoundary n (k : ℕ) x) start
        ⟨state.seekingOuter, 0⟩ candidate at hbase
    have hstate : state =
        shiftScanCompleted state.completed ⟨state.seekingOuter, 0⟩ := by
      cases state
      simp [shiftScanCompleted]
    rw [hstate, scanWordFrom_shiftScanCompleted,
      scanWordFrom_shiftScanCompleted, hbase]

@[simp] theorem xProfileScanCompatible_self
    (n : ℕ) (x start : Point) (word : List Direction) :
    XProfileScanCompatible n x start word word := by
  intro k hk state
  rfl

/-- Coordinatewise universal scanner compatibility composes through the
shared retained pieces and preserves the whole `x` profile. -/
theorem excursionProfile_alternatingConcat_eq_of_xProfileScanCompatible
    {n m : ℕ} (hn : 2 ≤ n) {x start : Point}
    {pieces : Fin (m + 1) → List Direction}
    {sourceWords candidateWords : TerminalSegmentWords m}
    (geometry : EndpointMatchedAlternatingGeometry m start pieces
      sourceWords candidateWords)
    (hcompatible : ∀ j,
      XProfileScanCompatible n x (geometry.wordStart j)
        (sourceWords j) (candidateWords j)) :
    excursionProfile
        (wordWalk start (alternatingConcat m pieces sourceWords)) n
        (alternatingConcat m pieces sourceWords).length x =
      excursionProfile
        (wordWalk start (alternatingConcat m pieces candidateWords)) n
        (alternatingConcat m pieces candidateWords).length x := by
  apply excursionProfile_wordWalk_eq_of_scanWordFrom_eq
  · intro k hk
    exact profileBoundaries_disjoint hn x k hk
  · intro k hk
    change scanWordFrom (profileOuterBoundary n (k : ℕ) x)
        (profileInnerBoundary n (k : ℕ) x) start
        (visitBoundary
          (profileOuterBoundary n (k : ℕ) x)
          (profileInnerBoundary n (k : ℕ) x)
          TerminalBoundaryScan.initialState start)
        (alternatingConcat m pieces sourceWords) = _
    apply scanWordFrom_alternatingConcat_eq_of_endpointGeometry
      m _ _ pieces sourceWords candidateWords start _ geometry
    intro j state
    exact hcompatible j k hk state

/-- A profile-disc-confined replacement tuple preserves the original first
global exit.  Unlike the terminal-only wrapper, the retained disc may be at
any regular scale `k ≤ n`. -/
theorem isOuterExitTime_alternatingConcat_complementaryPieces_profileDisc
    {m n k : ℕ} {omega : StepPath} {y : Point}
    {t : TimedTerminalSkeleton m} {words : TerminalSegmentWords m}
    (hn : 1 ≤ n) (hk : k ≤ n) (hy : y ∈ candidateBox n)
    (ht : t.WellFormed)
    (hexit : IsOuterExitTime (trajectory omega) n t.horizon)
    (hentrancePoint : ∀ j,
      t.entrancePoint j = trajectory omega (t.entrance j))
    (hexitPoint : ∀ j,
      t.exitPoint j = trajectory omega (t.exit j))
    (hwithin : ∀ j,
      WordWithin (disc y (scaleRadius n k)) (t.entrancePoint j) (words j))
    (hwordEnd : ∀ j,
      wordEndpoint (t.entrancePoint j) (words j) = t.exitPoint j) :
    IsOuterExitTime
      (wordWalk (trajectory omega 0)
        (alternatingConcat m
          (complementaryPieces m omega 0 t.horizon t.entrance t.exit)
          words)) n
      (alternatingConcat m
        (complementaryPieces m omega 0 t.horizon t.entrance t.exit)
        words).length := by
  have hsafe : AlternatingTerminalSpliceSafe
      (discBoundary (0, 0) (outerScale n))
      (disc y (scaleRadius n k)) m (trajectory omega 0)
      (complementaryPieces m omega 0 t.horizon t.entrance t.exit) words := by
    apply alternatingTerminalSpliceSafe_complementaryPieces
      m omega 0 t.horizon t.entrance t.exit
      (discBoundary (0, 0) (outerScale n))
      (disc y (scaleRadius n k)) words (Nat.zero_le _)
      (orderedIntervals_of_wellFormed ht) hexit.1 hexit.2
      (fun z hz ↦ profileDisc_disjoint_globalBoundary hn hk hy hz)
    · intro j
      rw [← hentrancePoint j]
      exact hwithin j
    · intro j
      rw [← hentrancePoint j, ← hexitPoint j]
      exact hwordEnd j
  exact (WordFirstHitsAtEnd.alternatingConcat_of_terminalSpliceSafe
    (fun z hz ↦ profileDisc_disjoint_globalBoundary hn hk hy hz)
    hsafe).isFirstHit

end

end Erdos1165.AsymmetricSplitCompletionPreservation
