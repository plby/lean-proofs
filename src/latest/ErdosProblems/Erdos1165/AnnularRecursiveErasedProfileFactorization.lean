/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
import ErdosProblems.Erdos1165.AnnularErasedParentSpineProfile
import ErdosProblems.Erdos1165.AsymmetricExtractedReturnCompletion

/-!
# Recursive refinements of an erased annular parent spine

A recursive child condition must be imposed on the word which was deleted
from the parent, not on a second copy of a full parent gap.  This file turns
the pathwise erased-spine theorem into the literal prefix-free factor used by
the probability calculation.

The complementary word is exactly the compressed parent spine.  Coordinate
`j` is exactly one `BoundaryExitWordCode` from the stored child entrance to
the stored child exit.  An arbitrary recursive predicate can then restrict
that coordinate with `restrictBridges`; the generic stopped-word theorem
gives its exact mass as

`retained-spine weight * product of restricted child-word masses`.

Thus every deleted child interval occurs once, while the already-integrated
full parent-gap mass does not occur in the factorization.
-/

open MeasureTheory Set
open scoped BigOperators ENNReal

namespace Erdos1165.AnnularRecursiveErasedProfileFactorization

open AnnularErasedParentSpine AnnularErasedParentSpineProfile
open AnnularProfileClocks
open AsymmetricExtractedReturnCompletion MarkedBridgeFactorization
open AsymmetricSplitLevelSplice
open TerminalGlobalExitSplice TerminalSequentialVisitLaw
open TerminalSkeletonFactorization
open TerminalSkeletonInvariance TerminalSkeletonWords ThickPoint

noncomputable section

/-- The literal erased-parent factor at one profile level.  The prefix has
length zero because the parent gap already starts at `origin`; its sole
complement code is the compressed retained spine. -/
def profileErasedParentCompletionAtom
    {m n k : ℕ} {center origin : Point} {omega : StepPath}
    {horizon : ℕ} {t : TimedTerminalSkeleton m}
    (hn : 2 ≤ n) (hk0 : 0 < k) (hk : k + 1 ≤ n)
    (ht : t.WellFormed)
    (hfirst : AbsoluteBoundaryFirstAt
      (profileOuterBoundary n k center) origin omega horizon)
    (hhorizon : t.horizon = horizon)
    (hentranceInner : ∀ j,
      t.entrancePoint j ∈ profileInnerBoundary n (k + 1) center)
    (hentrancePoint : ∀ j, t.entrancePoint j =
      PlanarPotential.trajectoryFrom origin omega (t.entrance j))
    (hexitPoint : ∀ j, t.exitPoint j =
      PlanarPotential.trajectoryFrom origin omega (t.exit j)) :
    ComplementarySkeletonAtom m (Fin 0 → Direction)
      (fun j ↦ BoundaryExitWordCode (profileInnerBoundary n k center)
        (t.entrancePoint j) (t.exitPoint j)) :=
  boundaryReturnCompletionAtom (start := 0) (compressTimedSkeleton omega t)
    (profileInnerBoundary n k center) (profileOuterBoundary n k center)
    origin fun bridges ↦
      absoluteBoundaryFirstAt_profileChildBoundaryExitWords
        hn hk0 hk ht hfirst hhorizon hentranceInner bridges
          hentrancePoint hexitPoint

/-- Refine each deleted child word by an arbitrary recursive condition.
No parent word is duplicated: this is literally `restrictBridges` of the
erased-parent factor. -/
def profileRecursiveErasedParentAtom
    {m n k : ℕ} {center origin : Point} {omega : StepPath}
    {horizon : ℕ} {t : TimedTerminalSkeleton m}
    (hn : 2 ≤ n) (hk0 : 0 < k) (hk : k + 1 ≤ n)
    (ht : t.WellFormed)
    (hfirst : AbsoluteBoundaryFirstAt
      (profileOuterBoundary n k center) origin omega horizon)
    (hhorizon : t.horizon = horizon)
    (hentranceInner : ∀ j,
      t.entrancePoint j ∈ profileInnerBoundary n (k + 1) center)
    (hentrancePoint : ∀ j, t.entrancePoint j =
      PlanarPotential.trajectoryFrom origin omega (t.entrance j))
    (hexitPoint : ∀ j, t.exitPoint j =
      PlanarPotential.trajectoryFrom origin omega (t.exit j))
    (admissible : (j : Fin m) →
      BoundaryExitWordCode (profileInnerBoundary n k center)
        (t.entrancePoint j) (t.exitPoint j) → Prop) :
    ComplementarySkeletonAtom m (Fin 0 → Direction)
      (fun j ↦ {bridge : BoundaryExitWordCode
          (profileInnerBoundary n k center)
          (t.entrancePoint j) (t.exitPoint j) // admissible j bridge}) :=
  restrictBridges
    (profileErasedParentCompletionAtom hn hk0 hk ht hfirst hhorizon
      hentranceInner hentrancePoint hexitPoint)
    admissible

/-- Reassembling recursively admissible child words produces a canonical
first-boundary word for the parent, with its original recorded endpoint.
This is the constructor used to feed a completed refined parent into the
next outer recursive level. -/
def reassembledProfileBoundaryExitWordCode
    {m n k : ℕ} {center origin endpoint : Point} {omega : StepPath}
    {horizon : ℕ} {t : TimedTerminalSkeleton m}
    (hn : 2 ≤ n) (hk0 : 0 < k) (hk : k + 1 ≤ n)
    (ht : t.WellFormed)
    (hfirst : AbsoluteBoundaryFirstAt
      (profileOuterBoundary n k center) origin omega horizon)
    (hhorizon : t.horizon = horizon)
    (hendpoint : PlanarPotential.trajectoryFrom origin omega horizon = endpoint)
    (hentranceInner : ∀ j,
      t.entrancePoint j ∈ profileInnerBoundary n (k + 1) center)
    (hentrancePoint : ∀ j, t.entrancePoint j =
      PlanarPotential.trajectoryFrom origin omega (t.entrance j))
    (hexitPoint : ∀ j, t.exitPoint j =
      PlanarPotential.trajectoryFrom origin omega (t.exit j))
    (admissible : (j : Fin m) →
      BoundaryExitWordCode (profileInnerBoundary n k center)
        (t.entrancePoint j) (t.exitPoint j) → Prop)
    (children : (j : Fin m) →
      {bridge : BoundaryExitWordCode (profileInnerBoundary n k center)
          (t.entrancePoint j) (t.exitPoint j) // admissible j bridge}) :
    BoundaryExitWordCode (profileOuterBoundary n k center) origin endpoint := by
  let words : TerminalSegmentWords m :=
    fun j ↦ List.ofFn (children j).1.1.2
  let code := compressTimedSkeleton omega t
  let parentWord := assembledTerminalWord code words
  refine ⟨parentWord, ?_, ?_⟩
  · simpa only [parentWord, code, words, assembledTerminalPath,
      assembledTerminalHorizon, assembledTerminalWord] using
      absoluteBoundaryFirstAt_profileChildBoundaryExitWords
        hn hk0 hk ht hfirst hhorizon hentranceInner
          (fun j ↦ (children j).1) hentrancePoint hexitPoint
  · have hfinal :=
      trajectoryFrom_assembledTerminalPath_horizon_eq_original_from
        (origin := origin) ht
          (fun j ↦ boundaryExitWordCode_wordEndpoint (children j).1)
          hentrancePoint hexitPoint
    rw [hhorizon, hendpoint] at hfinal
    simpa only [parentWord, code, words, assembledTerminalPath,
      assembledTerminalHorizon, assembledTerminalWord] using hfinal

/-- Exact recursive stopped-word factorization.  The first factor is the
retained erased spine; each product coordinate is one (and only one)
deleted child word satisfying its recursive predicate. -/
theorem fairSteps_profileRecursiveErasedParentAtom
    {m n k : ℕ} {center origin : Point} {omega : StepPath}
    {horizon : ℕ} {t : TimedTerminalSkeleton m}
    (hn : 2 ≤ n) (hk0 : 0 < k) (hk : k + 1 ≤ n)
    (ht : t.WellFormed)
    (hfirst : AbsoluteBoundaryFirstAt
      (profileOuterBoundary n k center) origin omega horizon)
    (hhorizon : t.horizon = horizon)
    (hentranceInner : ∀ j,
      t.entrancePoint j ∈ profileInnerBoundary n (k + 1) center)
    (hentrancePoint : ∀ j, t.entrancePoint j =
      PlanarPotential.trajectoryFrom origin omega (t.entrance j))
    (hexitPoint : ∀ j, t.exitPoint j =
      PlanarPotential.trajectoryFrom origin omega (t.exit j))
    (admissible : (j : Fin m) →
      BoundaryExitWordCode (profileInnerBoundary n k center)
        (t.entrancePoint j) (t.exitPoint j) → Prop) :
    fairSteps
        (profileRecursiveErasedParentAtom hn hk0 hk ht hfirst hhorizon
          hentranceInner hentrancePoint hexitPoint admissible).event =
      (profileErasedParentCompletionAtom hn hk0 hk ht hfirst hhorizon
          hentranceInner hentrancePoint hexitPoint).weight *
        ∏ j,
          (profileRecursiveErasedParentAtom hn hk0 hk ht hfirst hhorizon
            hentranceInner hentrancePoint hexitPoint admissible).kernel j := by
  rw [fairSteps_event_eq_weight_mul_prod_kernel]
  simp only [profileRecursiveErasedParentAtom, restrictBridges_weight]

/-- The assembled length also displays the no-double-counting invariant:
retained-spine length plus the lengths of the deleted child words, once. -/
theorem profileRecursiveErasedParentAtom_length
    {m n k : ℕ} {center origin : Point} {omega : StepPath}
    {horizon : ℕ} {t : TimedTerminalSkeleton m}
    (hn : 2 ≤ n) (hk0 : 0 < k) (hk : k + 1 ≤ n)
    (ht : t.WellFormed)
    (hfirst : AbsoluteBoundaryFirstAt
      (profileOuterBoundary n k center) origin omega horizon)
    (hhorizon : t.horizon = horizon)
    (hentranceInner : ∀ j,
      t.entrancePoint j ∈ profileInnerBoundary n (k + 1) center)
    (hentrancePoint : ∀ j, t.entrancePoint j =
      PlanarPotential.trajectoryFrom origin omega (t.entrance j))
    (hexitPoint : ∀ j, t.exitPoint j =
      PlanarPotential.trajectoryFrom origin omega (t.exit j))
    (admissible : (j : Fin m) →
      BoundaryExitWordCode (profileInnerBoundary n k center)
        (t.entrancePoint j) (t.exitPoint j) → Prop)
    (code : (Fin 0 → Direction) ×
      ((j : Fin m) → {bridge : BoundaryExitWordCode
          (profileInnerBoundary n k center)
          (t.entrancePoint j) (t.exitPoint j) // admissible j bridge})) :
    ((profileRecursiveErasedParentAtom hn hk0 hk ht hfirst hhorizon
        hentranceInner hentrancePoint hexitPoint admissible).assemble code).1 =
      ((profileRecursiveErasedParentAtom hn hk0 hk ht hfirst hhorizon
        hentranceInner hentrancePoint hexitPoint admissible).complementWord
          code.1).1 +
        ∑ j,
          ((profileRecursiveErasedParentAtom hn hk0 hk ht hfirst hhorizon
            hentranceInner hentrancePoint hexitPoint admissible).bridgeWord j
              (code.2 j)).1 := by
  exact (profileRecursiveErasedParentAtom hn hk0 hk ht hfirst hhorizon
    hentranceInner hentrancePoint hexitPoint admissible).length_assemble code

/-- The actual parent word belongs to the recursively refined factor as soon
as its genuinely deleted interval words satisfy the recursive predicates.
This is the source-coverage half of the recursive splice: no synthetic
retained cylinder is substituted for the assembled parent word. -/
theorem source_mem_profileRecursiveErasedParentAtom
    {m n k : ℕ} {center origin : Point} {omega : StepPath}
    {horizon : ℕ} {t : TimedTerminalSkeleton m}
    (hn : 2 ≤ n) (hk0 : 0 < k) (hk : k + 1 ≤ n)
    (ht : t.WellFormed)
    (hfirst : AbsoluteBoundaryFirstAt
      (profileOuterBoundary n k center) origin omega horizon)
    (hhorizon : t.horizon = horizon)
    (hentranceInner : ∀ j,
      t.entrancePoint j ∈ profileInnerBoundary n (k + 1) center)
    (hentrancePoint : ∀ j, t.entrancePoint j =
      PlanarPotential.trajectoryFrom origin omega (t.entrance j))
    (hexitPoint : ∀ j, t.exitPoint j =
      PlanarPotential.trajectoryFrom origin omega (t.exit j))
    (admissible : (j : Fin m) →
      BoundaryExitWordCode (profileInnerBoundary n k center)
        (t.entrancePoint j) (t.exitPoint j) → Prop)
    (source : (j : Fin m) →
      BoundaryExitWordCode (profileInnerBoundary n k center)
        (t.entrancePoint j) (t.exitPoint j))
    (hsourceWords : ∀ j, List.ofFn (source j).1.2 =
      intervalWords omega t.entrance t.exit j)
    (hsourceAdmissible : ∀ j, admissible j (source j)) :
    omega ∈
      (profileRecursiveErasedParentAtom hn hk0 hk ht hfirst hhorizon
        hentranceInner hentrancePoint hexitPoint admissible).event := by
  let code := compressTimedSkeleton omega t
  have hcylinder : omega ∈ stoppedWordCylinder
      (assembleAfterPrefix (stepPrefix 0 omega) code
        (fun j ↦ List.ofFn (source j).1.2)) := by
    have hsourceWords' : (fun j ↦ List.ofFn (source j).1.2) =
        intervalWords omega t.entrance t.exit := by
      funext j
      exact hsourceWords j
    rw [hsourceWords']
    have hraw :=
      mem_stoppedWordCylinder_assembleAfterPrefix_packetOfTimedSkeleton
        (start := 0) omega t ht
    have hshift : shiftSteps 0 omega = omega := by
      funext q
      simp [shiftSteps]
    simpa only [hshift, code] using hraw
  rw [ComplementarySkeletonAtom.event, stoppedWordEvent]
  apply Set.mem_iUnion.mpr
  refine ⟨(stepPrefix 0 omega,
    fun j ↦ ⟨source j, hsourceAdmissible j⟩), ?_⟩
  exact hcylinder

end

end Erdos1165.AnnularRecursiveErasedProfileFactorization
