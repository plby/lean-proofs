/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
import ErdosProblems.Erdos1165.AsymmetricSplitLevelSplice

/-!
# Erased spines for one annular parent gap

The recursive annular profile cannot be obtained by multiplying a complete
parent-gap kernel by kernels for intervals already integrated inside that
parent.  The correct path decomposition first deletes the completed
inner-to-middle returns.  Their entrance and exit points, and all pieces
between them, remain in the parent spine; the deleted return words are then
inserted exactly once.

`TerminalGlobalExitSplice.alternatingTerminalSpliceSafe_complementaryPieces`
already proves the needed finite-word statement for a walk started at the
origin.  Annular gaps start at arbitrary boundary points.  This file proves
the translation-free arbitrary-start form and packages the resulting exact
first-boundary reconstruction.  No probability or conditional-kernel claim
is made here.
-/

open Set

namespace Erdos1165.AnnularErasedParentSpine

open AsymmetricSplitLevelSplice MarkedBridgeFactorization
open TerminalGlobalExitSplice TerminalSkeletonWords
open TerminalSequentialVisitLaw TerminalSkeletonInvariance
open TerminalProfileClockEquivalence
open TerminalExcursionPathwise
open ThickPoint

noncomputable section

/-- Following an increment slice from the corresponding position of a walk
started at `origin` reproduces that walk. -/
theorem wordPosition_incrementSlice_from
    (origin : Point) (omega : StepPath)
    {start stop t : ℕ} (_hstart : start ≤ stop) (ht : t ≤ stop - start) :
    wordPosition (PlanarPotential.trajectoryFrom origin omega start)
        (incrementSlice omega start stop) t =
      PlanarPotential.trajectoryFrom origin omega (start + t) := by
  induction t with
  | zero => simp
  | succ t ih =>
      have htlt : t < (incrementSlice omega start stop).length := by
        simp only [incrementSlice_length]
        omega
      rw [wordPosition_succ _ _ htlt, ih (by omega)]
      simp only [incrementSlice, List.getElem_ofFn, Annulus.neighbor]
      rw [show start + (t + 1) = (start + t) + 1 by omega,
        PlanarPotential.trajectoryFrom_succ]

/-- Endpoint form of `wordPosition_incrementSlice_from`. -/
theorem wordEndpoint_incrementSlice_from
    (origin : Point) (omega : StepPath)
    {start stop : ℕ} (hstart : start ≤ stop) :
    wordEndpoint (PlanarPotential.trajectoryFrom origin omega start)
        (incrementSlice omega start stop) =
      PlanarPotential.trajectoryFrom origin omega stop := by
  have h := wordPosition_incrementSlice_from origin omega hstart
    (show stop - start ≤ stop - start from le_rfl)
  calc
    wordEndpoint (PlanarPotential.trajectoryFrom origin omega start)
        (incrementSlice omega start stop) =
      wordPosition (PlanarPotential.trajectoryFrom origin omega start)
        (incrementSlice omega start stop)
        (incrementSlice omega start stop).length := by
          exact (wordPosition_length _ _).symm
    _ = PlanarPotential.trajectoryFrom origin omega stop := by
      simpa only [incrementSlice_length, Nat.add_sub_of_le hstart] using h

/-- Endpoint preservation for an erased spine with arbitrary endpoint-matched
replacement words.  This is independent of the first-boundary geometry. -/
theorem wordEndpoint_alternatingConcat_complementaryPieces_from :
    ∀ (m : ℕ) (origin : Point) (omega : StepPath) (base horizon : ℕ)
      (entrance exit : Fin m → ℕ) (words : TerminalSegmentWords m),
      base ≤ horizon →
      OrderedIntervals base horizon entrance exit →
      (∀ j, wordEndpoint
        (PlanarPotential.trajectoryFrom origin omega (entrance j)) (words j) =
          PlanarPotential.trajectoryFrom origin omega (exit j)) →
      wordEndpoint (PlanarPotential.trajectoryFrom origin omega base)
          (alternatingConcat m
            (complementaryPieces m omega base horizon entrance exit) words) =
        PlanarPotential.trajectoryFrom origin omega horizon := by
  intro m
  induction m with
  | zero =>
      intro origin omega base horizon entrance exit words hbase _hordered _hwordEnd
      simp only [alternatingConcat, complementaryPieces]
      exact wordEndpoint_incrementSlice_from origin omega hbase
  | succ m ih =>
      intro origin omega base horizon entrance exit words _hbase hordered hwordEnd
      have hzero := hordered.1 (0 : Fin (m + 1))
      have htail : OrderedIntervals (exit 0) horizon
          (fun j : Fin m ↦ entrance j.succ)
          (fun j : Fin m ↦ exit j.succ) := by
        constructor
        · intro j
          have hj := hordered.1 j.succ
          refine ⟨?_, hj.2⟩
          exact hordered.2 0 j.succ (by simp)
        · intro i j hij
          exact hordered.2 i.succ j.succ (by simpa using hij)
      simp only [alternatingConcat, complementaryPieces, Fin.cases_zero,
        Fin.cases_succ, wordEndpoint_append]
      rw [wordEndpoint_incrementSlice_from origin omega hzero.1,
        hwordEnd 0]
      exact ih origin omega (exit 0) horizon
        (fun j ↦ entrance j.succ) (fun j ↦ exit j.succ)
        (fun j ↦ words j.succ) hzero.2.2 htail
        (fun j ↦ hwordEnd j.succ)

/-- The stopped extension assembled from a compressed erased spine has the
same final spatial endpoint as the original parent word whenever all deleted
interval replacements match their stored endpoints. -/
theorem trajectoryFrom_assembledTerminalPath_horizon_eq_original_from
    {m : ℕ} {origin : Point} {omega : StepPath}
    {t : TimedTerminalSkeleton m} {words : TerminalSegmentWords m}
    (ht : t.WellFormed)
    (hwordEnd : ∀ j,
      wordEndpoint (t.entrancePoint j) (words j) = t.exitPoint j)
    (hentrancePoint : ∀ j, t.entrancePoint j =
      PlanarPotential.trajectoryFrom origin omega (t.entrance j))
    (hexitPoint : ∀ j, t.exitPoint j =
      PlanarPotential.trajectoryFrom origin omega (t.exit j)) :
    PlanarPotential.trajectoryFrom origin
        (assembledTerminalPath (compressTimedSkeleton omega t) words)
        (assembledTerminalHorizon (compressTimedSkeleton omega t) words) =
      PlanarPotential.trajectoryFrom origin omega t.horizon := by
  let code := compressTimedSkeleton omega t
  let word := reconstructTerminalPacket (code, words)
  have hwordEnd' : ∀ j,
      wordEndpoint
          (PlanarPotential.trajectoryFrom origin omega (t.entrance j))
          (words j) =
        PlanarPotential.trajectoryFrom origin omega (t.exit j) := by
    intro j
    rw [← hentrancePoint j, ← hexitPoint j]
    exact hwordEnd j
  have hendWord : wordEndpoint origin word =
      PlanarPotential.trajectoryFrom origin omega t.horizon := by
    simpa only [PlanarPotential.trajectoryFrom_zero, word, code,
      reconstructTerminalPacket, compressTimedSkeleton] using
        wordEndpoint_alternatingConcat_complementaryPieces_from
          m origin omega 0 t.horizon t.entrance t.exit words
            (Nat.zero_le _) (orderedIntervals_of_wellFormed ht) hwordEnd'
  have hpath := wordWalk_eq_trajectoryFrom_extendStoppedWord
    origin word (show word.length ≤ word.length from le_rfl)
  calc
    PlanarPotential.trajectoryFrom origin
        (assembledTerminalPath (compressTimedSkeleton omega t) words)
        (assembledTerminalHorizon (compressTimedSkeleton omega t) words) =
        wordWalk origin word word.length := by
          symm
          change wordWalk origin word word.length =
            PlanarPotential.trajectoryFrom origin
              (extendStoppedWord
                (TerminalVisitSpliceInvariance.stoppedWordOfList word))
              word.length
          exact hpath
    _ = wordEndpoint origin word := by
      simp only [wordWalk_length, wordEndpoint]
    _ = PlanarPotential.trajectoryFrom origin omega t.horizon := hendWord

/-- Arbitrary-start version of the structural complementary-piece splice.
Every deleted word is inserted between the exact retained entrance and exit
points, while the last retained piece still makes the first hit of `B`. -/
theorem alternatingTerminalSpliceSafe_complementaryPieces_from :
    ∀ (m : ℕ) (origin : Point) (omega : StepPath) (base horizon : ℕ)
      (entrance exit : Fin m → ℕ) (B D : Set Point)
      (words : TerminalSegmentWords m),
      base ≤ horizon →
      OrderedIntervals base horizon entrance exit →
      PlanarPotential.trajectoryFrom origin omega horizon ∈ B →
      (∀ k < horizon, PlanarPotential.trajectoryFrom origin omega k ∉ B) →
      (∀ y, y ∈ D → y ∉ B) →
      (∀ j, WordWithin D
        (PlanarPotential.trajectoryFrom origin omega (entrance j)) (words j)) →
      (∀ j, wordEndpoint
        (PlanarPotential.trajectoryFrom origin omega (entrance j)) (words j) =
          PlanarPotential.trajectoryFrom origin omega (exit j)) →
      AlternatingTerminalSpliceSafe B D m
        (PlanarPotential.trajectoryFrom origin omega base)
        (complementaryPieces m omega base horizon entrance exit) words := by
  intro m
  induction m with
  | zero =>
      intro origin omega base horizon entrance exit B D words hbase _hordered
        hend hbefore _hdisjoint _hwithin _hwordEnd
      simp only [complementaryPieces, AlternatingTerminalSpliceSafe]
      apply WordFirstHitsAtEnd.of_isFirstHit
      · rw [wordWalk_length]
        change wordEndpoint (PlanarPotential.trajectoryFrom origin omega base)
          (incrementSlice omega base horizon) ∈ B
        rw [wordEndpoint_incrementSlice_from origin omega hbase]
        exact hend
      · intro q hq
        have hq' : q ≤ horizon - base := by
          simpa only [incrementSlice_length] using hq.le
        rw [wordWalk,
          wordPosition_incrementSlice_from origin omega hbase hq']
        apply hbefore
        simp only [incrementSlice_length] at hq
        omega
  | succ m ih =>
      intro origin omega base horizon entrance exit B D words hbase hordered
        hend hbefore hdisjoint hwithin hwordEnd
      have hzero := hordered.1 (0 : Fin (m + 1))
      have hentranceNotBoundary :
          PlanarPotential.trajectoryFrom origin omega (entrance 0) ∉ B :=
        hdisjoint _ (hwithin 0).start_mem
      have hentranceLt : entrance 0 < horizon := by
        have hne : entrance 0 ≠ horizon := by
          intro heq
          exact hentranceNotBoundary (heq ▸ hend)
        omega
      have htail : OrderedIntervals (exit 0) horizon
          (fun j : Fin m ↦ entrance j.succ)
          (fun j : Fin m ↦ exit j.succ) := by
        constructor
        · intro j
          have hj := hordered.1 j.succ
          refine ⟨?_, hj.2⟩
          exact hordered.2 0 j.succ (by simp)
        · intro i j hij
          exact hordered.2 i.succ j.succ (by simpa using hij)
      simp only [complementaryPieces, AlternatingTerminalSpliceSafe,
        Fin.cases_zero, Fin.cases_succ]
      refine ⟨?_, ?_, ?_⟩
      · apply WordAvoids.of_forall_wordWalk
        intro q hq
        have hq' : q ≤ entrance 0 - base := by
          simpa only [incrementSlice_length] using hq
        rw [wordWalk,
          wordPosition_incrementSlice_from origin omega hzero.1 hq']
        apply hbefore
        omega
      · rw [wordEndpoint_incrementSlice_from origin omega hzero.1]
        exact hwithin 0
      · rw [wordEndpoint_incrementSlice_from origin omega hzero.1,
          hwordEnd 0]
        exact ih origin omega (exit 0) horizon
          (fun j ↦ entrance j.succ) (fun j ↦ exit j.succ) B D
          (fun j ↦ words j.succ) hzero.2.2 htail hend hbefore hdisjoint
          (fun j ↦ hwithin j.succ) (fun j ↦ hwordEnd j.succ)

/-- Reinsertions into a well-formed erased spine preserve the parent's exact
first hit of `B`, for an arbitrary spatial starting point. -/
theorem absoluteBoundaryFirstAt_alternatingConcat_complementaryPieces_from
    {m : ℕ} {origin : Point} {omega : StepPath} {horizon : ℕ}
    {t : TimedTerminalSkeleton m} {B D : Set Point}
    {words : TerminalSegmentWords m}
    (ht : t.WellFormed)
    (hfirst : AbsoluteBoundaryFirstAt B origin omega horizon)
    (hhorizon : t.horizon = horizon)
    (hdisjoint : ∀ y, y ∈ D → y ∉ B)
    (hwithin : ∀ j, WordWithin D (t.entrancePoint j) (words j))
    (hwordEnd : ∀ j,
      wordEndpoint (t.entrancePoint j) (words j) = t.exitPoint j)
    (hentrancePoint : ∀ j, t.entrancePoint j =
      PlanarPotential.trajectoryFrom origin omega (t.entrance j))
    (hexitPoint : ∀ j, t.exitPoint j =
      PlanarPotential.trajectoryFrom origin omega (t.exit j)) :
    AbsoluteBoundaryFirstAt B origin
      (assembledTerminalPath (compressTimedSkeleton omega t) words)
      (assembledTerminalHorizon (compressTimedSkeleton omega t) words) := by
  subst horizon
  have hsafe : AlternatingTerminalSpliceSafe B D m origin
      (complementaryPieces m omega 0 t.horizon t.entrance t.exit) words := by
    have h := alternatingTerminalSpliceSafe_complementaryPieces_from
        m origin omega 0 t.horizon t.entrance t.exit B D words
        (Nat.zero_le _) (orderedIntervals_of_wellFormed ht) hfirst.1 hfirst.2
        hdisjoint
        (fun j ↦ by
          rw [← hentrancePoint j]
          exact hwithin j)
        (fun j ↦ by
          rw [← hentrancePoint j, ← hexitPoint j]
          exact hwordEnd j)
    simpa only [PlanarPotential.trajectoryFrom_zero] using h
  have hwordFirst :=
    WordFirstHitsAtEnd.alternatingConcat_of_terminalSpliceSafe
      hdisjoint hsafe
  have hisFirst := hwordFirst.isFirstHit
  let code := compressTimedSkeleton omega t
  let word := reconstructTerminalPacket (code, words)
  have hhorizonWord : assembledTerminalHorizon code words = word.length := rfl
  have hpath (q : ℕ) (hq : q ≤ word.length) :
      PlanarPotential.trajectoryFrom origin
          (assembledTerminalPath code words) q =
        wordWalk origin word q := by
    symm
    change wordWalk origin word q =
      PlanarPotential.trajectoryFrom origin
        (extendStoppedWord
          (TerminalVisitSpliceInvariance.stoppedWordOfList word)) q
    exact wordWalk_eq_trajectoryFrom_extendStoppedWord origin word hq
  constructor
  · rw [hhorizonWord, hpath word.length le_rfl]
    exact hisFirst.1
  · intro q hq
    rw [hhorizonWord] at hq
    rw [hpath q hq.le]
    exact hisFirst.2 q hq

/-- Boundary-exit-code specialization of the erased-spine reconstruction.
The erased child words are canonical first hits of `innerBoundary D`; their
containment in `D` and endpoint alignment are therefore automatic. -/
theorem absoluteBoundaryFirstAt_boundaryExitWords_complementaryPieces_from
    {m : ℕ} {origin : Point} {omega : StepPath} {horizon : ℕ}
    {t : TimedTerminalSkeleton m} {B D : Set Point}
    (ht : t.WellFormed)
    (hfirst : AbsoluteBoundaryFirstAt B origin omega horizon)
    (hhorizon : t.horizon = horizon)
    (hdisjoint : ∀ y, y ∈ D → y ∉ B)
    (hentranceMem : ∀ j, t.entrancePoint j ∈ D)
    (bridges : (j : Fin m) →
      BoundaryExitWordCode (innerBoundary D)
        (t.entrancePoint j) (t.exitPoint j))
    (hentrancePoint : ∀ j, t.entrancePoint j =
      PlanarPotential.trajectoryFrom origin omega (t.entrance j))
    (hexitPoint : ∀ j, t.exitPoint j =
      PlanarPotential.trajectoryFrom origin omega (t.exit j)) :
    AbsoluteBoundaryFirstAt B origin
      (assembledTerminalPath (compressTimedSkeleton omega t)
        (fun j ↦ List.ofFn (bridges j).1.2))
      (assembledTerminalHorizon (compressTimedSkeleton omega t)
        (fun j ↦ List.ofFn (bridges j).1.2)) := by
  apply absoluteBoundaryFirstAt_alternatingConcat_complementaryPieces_from
    ht hfirst hhorizon hdisjoint
  · intro j
    exact (boundaryExitWordCode_wordWithin_and_endpoint
      (hentranceMem j) (bridges j)).1
  · intro j
    exact (boundaryExitWordCode_wordWithin_and_endpoint
      (hentranceMem j) (bridges j)).2
  · exact hentrancePoint
  · exact hexitPoint

end

end Erdos1165.AnnularErasedParentSpine
