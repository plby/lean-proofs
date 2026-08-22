/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import ErdosProblems.Erdos1165.MarkedSkeletonPartition
import ErdosProblems.Erdos1165.Proposition13Measurability
import ErdosProblems.Erdos1165.TerminalExcursionPathwise

/-!
# Compressed terminal skeleton words

For the first `m` complete terminal inner-to-outer pieces, the complementary
skeleton stores the `m+1` retained increment pieces and the entrance/exit
endpoints.  Crucially, it stores neither the removed durations nor their
absolute times.  Thus a fibre leaves each removed word free to range over all
finite first-hit bridges, whose total mass is the infinite-horizon boundary
kernel rather than a fixed-time kernel.

A packet adds the arbitrary finite removed words.  Alternating the retained
pieces and removed words reconstructs the original stopped prefix.  A
separate timed witness is used only to prove extraction and coverage; it is
not part of the skeleton code that indexes probability fibres.
-/

open Set

namespace Erdos1165.TerminalSkeletonWords

open ThickPoint Proposition13Measurability TerminalExcursionPathwise

noncomputable section

/-! ## Finite increment slices -/

/-- The half-open increment slice `[start, stop)`. -/
def incrementSlice (omega : StepPath) (start stop : ℕ) : List Direction :=
  List.ofFn fun k : Fin (stop - start) ↦ omega (start + k)

@[simp] theorem incrementSlice_length (omega : StepPath) (start stop : ℕ) :
    (incrementSlice omega start stop).length = stop - start := by
  simp [incrementSlice]

theorem incrementSlice_append (omega : StepPath) {a b c : ℕ}
    (hab : a ≤ b) (hbc : b ≤ c) :
    incrementSlice omega a b ++ incrementSlice omega b c =
      incrementSlice omega a c := by
  apply List.ext_get
  · simp [incrementSlice]
    omega
  · intro n hn hn'
    rw [List.get_eq_getElem, List.get_eq_getElem]
    by_cases hleft : n < (incrementSlice omega a b).length
    · rw [List.getElem_append_left hleft]
      simp only [incrementSlice, List.getElem_ofFn]
    · rw [List.getElem_append_right (Nat.le_of_not_gt hleft)]
      have hleft' : b - a ≤ n := by
        simpa only [incrementSlice, List.length_ofFn] using Nat.le_of_not_gt hleft
      simp only [incrementSlice, List.length_ofFn, List.getElem_ofFn]
      congr 1
      omega

/-! ## Compressed skeletons and packets -/

/-- The complementary data used as `Data` in a marked skeleton partition.
The endpoint vectors are deliberately kept outside this structure, in the
`SkeletonIndex Data Point Point m` coordinates. -/
@[ext]
structure TerminalSkeletonData (m : ℕ) where
  retainedPiece : Fin (m + 1) → List Direction
  deriving Countable, DecidableEq

/-- A complete unmarked skeleton index: compressed complementary data plus
the terminal entrance and exit endpoint vectors. -/
abbrev TerminalSkeletonCode (m : ℕ) :=
  MarkedSkeletonPartition.SkeletonIndex (TerminalSkeletonData m) Point Point m

/-- Arbitrary variable-length words inserted between the retained pieces. -/
abbrev TerminalSegmentWords (m : ℕ) := Fin m → List Direction

/-- The reconstruction-side packet.  Segment lengths occur only here, never
in the unmarked skeleton code. -/
abbrev TerminalSkeletonPacket (m : ℕ) :=
  TerminalSkeletonCode m × TerminalSegmentWords m

instance terminalSkeletonCode_countable (m : ℕ) :
    Countable (TerminalSkeletonCode m) := by infer_instance

instance terminalSkeletonPacket_countable (m : ℕ) :
    Countable (TerminalSkeletonPacket m) := by infer_instance

/-- Alternate `piece 0, word 0, piece 1, ..., word (m-1), piece m`. -/
def alternatingConcat : (m : ℕ) →
    (Fin (m + 1) → List Direction) → TerminalSegmentWords m →
      List Direction
  | 0, pieces, _words => pieces 0
  | m + 1, pieces, words =>
      pieces 0 ++ words 0 ++
        alternatingConcat m (fun j ↦ pieces j.succ) (fun j ↦ words j.succ)

/-- Reconstruct the entire stopped prefix represented by a packet. -/
def reconstructTerminalPacket {m : ℕ} (packet : TerminalSkeletonPacket m) :
    List Direction :=
  alternatingConcat m packet.1.1.retainedPiece packet.2

/-! ## Timed extraction witnesses -/

/-- Exact times are retained only in this pathwise witness.  They are erased
when passing to `TerminalSkeletonCode`. -/
@[ext]
structure TimedTerminalSkeleton (m : ℕ) where
  horizon : ℕ
  entrance : Fin m → ℕ
  exit : Fin m → ℕ
  entrancePoint : Fin m → Point
  exitPoint : Fin m → Point
  deriving Countable, DecidableEq

/-- Chronological disjointness and completion before the stopped horizon. -/
def TimedTerminalSkeleton.WellFormed {m : ℕ}
    (t : TimedTerminalSkeleton m) : Prop :=
  (∀ j, t.entrance j ≤ t.exit j ∧ t.exit j ≤ t.horizon) ∧
    ∀ i j : Fin m, (i : ℕ) < j → t.exit i ≤ t.entrance j

/-- The retained pieces determined by ordered timed intervals.  The recursive
form makes the first piece, intervening gaps, and final suffix explicit. -/
def complementaryPieces : (m : ℕ) → StepPath → ℕ → ℕ →
    (Fin m → ℕ) → (Fin m → ℕ) → Fin (m + 1) → List Direction
  | 0, omega, base, horizon, _entrance, _exit =>
      fun _ ↦ incrementSlice omega base horizon
  | m + 1, omega, base, horizon, entrance, exit =>
      Fin.cases (incrementSlice omega base (entrance 0))
        (complementaryPieces m omega (exit 0) horizon
          (fun j ↦ entrance j.succ) (fun j ↦ exit j.succ))

/-- Extract the removed words themselves. -/
def intervalWords {m : ℕ} (omega : StepPath)
    (entrance exit : Fin m → ℕ) : TerminalSegmentWords m :=
  fun j ↦ incrementSlice omega (entrance j) (exit j)

/-- Compress a timed witness by deleting all durations and absolute times. -/
def compressTimedSkeleton {m : ℕ} (omega : StepPath)
    (t : TimedTerminalSkeleton m) : TerminalSkeletonCode m :=
  (⟨complementaryPieces m omega 0 t.horizon t.entrance t.exit⟩,
    (t.entrancePoint, t.exitPoint))

@[simp] theorem compressTimedSkeleton_entrancePoint {m : ℕ}
    (omega : StepPath) (t : TimedTerminalSkeleton m) (j : Fin m) :
    (compressTimedSkeleton omega t).2.1 j = t.entrancePoint j := rfl

@[simp] theorem compressTimedSkeleton_exitPoint {m : ℕ}
    (omega : StepPath) (t : TimedTerminalSkeleton m) (j : Fin m) :
    (compressTimedSkeleton omega t).2.2 j = t.exitPoint j := rfl

/-- Add the extracted variable-length words on the reconstruction side. -/
def packetOfTimedSkeleton {m : ℕ} (omega : StepPath)
    (t : TimedTerminalSkeleton m) : TerminalSkeletonPacket m :=
  (compressTimedSkeleton omega t, intervalWords omega t.entrance t.exit)

/-! ## Reconstruction -/

def OrderedIntervals {m : ℕ} (base horizon : ℕ)
    (entrance exit : Fin m → ℕ) : Prop :=
  (∀ j, base ≤ entrance j ∧ entrance j ≤ exit j ∧
      exit j ≤ horizon) ∧
    ∀ i j : Fin m, (i : ℕ) < j → exit i ≤ entrance j

theorem alternatingConcat_complementaryPieces : ∀ (m : ℕ) (omega : StepPath)
    (base horizon : ℕ) (entrance exit : Fin m → ℕ),
    OrderedIntervals base horizon entrance exit →
      alternatingConcat m
        (complementaryPieces m omega base horizon entrance exit)
        (intervalWords omega entrance exit) =
      incrementSlice omega base horizon := by
  intro m
  induction m with
  | zero =>
      intro omega base horizon entrance exit hord
      rfl
  | succ m ih =>
      intro omega base horizon entrance exit hord
      have hzero := hord.1 (0 : Fin (m + 1))
      have htail : OrderedIntervals (exit 0) horizon
          (fun j : Fin m ↦ entrance j.succ) (fun j : Fin m ↦ exit j.succ) := by
        constructor
        · intro j
          have hj := hord.1 j.succ
          refine ⟨?_, hj.2⟩
          exact hord.2 0 j.succ (by simp)
        · intro i j hij
          exact hord.2 i.succ j.succ (by simpa using hij)
      simp only [alternatingConcat, complementaryPieces, intervalWords,
        Fin.cases_zero, Fin.cases_succ]
      change incrementSlice omega base (entrance 0) ++
          incrementSlice omega (entrance 0) (exit 0) ++
            alternatingConcat m
              (complementaryPieces m omega (exit 0) horizon
                (fun j ↦ entrance j.succ) (fun j ↦ exit j.succ))
              (intervalWords omega (fun j ↦ entrance j.succ)
                (fun j ↦ exit j.succ)) = _
      rw [ih omega (exit 0) horizon _ _ htail]
      rw [incrementSlice_append omega hzero.1 hzero.2.1]
      exact incrementSlice_append omega (hzero.1.trans hzero.2.1) hzero.2.2

theorem orderedIntervals_of_wellFormed {m : ℕ}
    {t : TimedTerminalSkeleton m} (ht : t.WellFormed) :
    OrderedIntervals 0 t.horizon t.entrance t.exit := by
  refine ⟨?_, ht.2⟩
  intro j
  exact ⟨Nat.zero_le _, (ht.1 j).1, (ht.1 j).2⟩

/-- Erasure followed by reinsertion of the extracted variable-length words
recovers the exact original prefix. -/
theorem reconstruct_packetOfTimedSkeleton {m : ℕ} (omega : StepPath)
    (t : TimedTerminalSkeleton m) (ht : t.WellFormed) :
    reconstructTerminalPacket (packetOfTimedSkeleton omega t) =
      incrementSlice omega 0 t.horizon := by
  exact alternatingConcat_complementaryPieces m omega 0 t.horizon
    t.entrance t.exit (orderedIntervals_of_wellFormed ht)

/-- Consequently equal packets determine equal finite prefixes. -/
theorem incrementSlice_eq_of_packet_eq {m : ℕ}
    {omega omega' : StepPath} {t t' : TimedTerminalSkeleton m}
    (ht : t.WellFormed) (ht' : t'.WellFormed)
    (hpacket : packetOfTimedSkeleton omega t = packetOfTimedSkeleton omega' t') :
    incrementSlice omega 0 t.horizon = incrementSlice omega' 0 t'.horizon := by
  rw [← reconstruct_packetOfTimedSkeleton omega t ht,
    ← reconstruct_packetOfTimedSkeleton omega' t' ht', hpacket]

/-! ## Literal extraction from the terminal excursion clocks -/

noncomputable def extractedEntrance (s : WalkPath) (scale horizon : ℕ)
    (x : Point) (j : ℕ) : ℕ := by
  classical
  exact excursionFinish s (terminalOuterBoundary scale x)
    (terminalInnerBoundary scale x) horizon j

noncomputable def extractedExit (s : WalkPath) (scale horizon : ℕ)
    (x : Point) (j : ℕ) : ℕ := by
  classical
  exact terminalSegmentExitTime s scale horizon x j

def extractTimedTerminalSkeleton (scale horizon : ℕ) (profileDelta : ℝ)
    (x : Point) (omega : StepPath) :
    TimedTerminalSkeleton
      (AppendixLocalTime.requiredTerminalCount scale profileDelta) :=
  let s := trajectory omega
  let m := AppendixLocalTime.requiredTerminalCount scale profileDelta
  let entrance : Fin m → ℕ := fun j ↦ extractedEntrance s scale horizon x j
  let exit : Fin m → ℕ := fun j ↦ extractedExit s scale horizon x j
  { horizon := horizon
    entrance := entrance
    exit := exit
    entrancePoint := fun j ↦ s (entrance j)
    exitPoint := fun j ↦ s (exit j) }

/-- The total fixed-horizon compressed code extractor. -/
def extractTerminalSkeletonCode (scale horizon : ℕ) (profileDelta : ℝ)
    (x : Point) (omega : StepPath) :
    TerminalSkeletonCode
      (AppendixLocalTime.requiredTerminalCount scale profileDelta) :=
  compressTimedSkeleton omega
    (extractTimedTerminalSkeleton scale horizon profileDelta x omega)

/-- The total fixed-horizon marked code appends the literal visit vector. -/
def extractMarkedTerminalCode (scale horizon : ℕ) (profileDelta : ℝ)
    (x : Point) (omega : StepPath) :
    MarkedSkeletonPartition.MarkedIndex
      (TerminalSkeletonData
        (AppendixLocalTime.requiredTerminalCount scale profileDelta))
      Point Point (AppendixLocalTime.requiredTerminalCount scale profileDelta) :=
  let code := extractTerminalSkeletonCode scale horizon profileDelta x omega
  (code.1, (code.2.1, (code.2.2,
    terminalVisitVector (trajectory omega) scale horizon profileDelta x)))

lemma extractedEntrance_le_extractedExit
    (s : WalkPath) (scale horizon : ℕ) (x : Point) (j : ℕ) :
    extractedEntrance s scale horizon x j ≤
      extractedExit s scale horizon x j := by
  classical
  exact excursionFinish_le_next_start s (terminalOuterBoundary scale x)
    (terminalInnerBoundary scale x) horizon j

lemma extractedExit_le_entrance_of_lt
    (s : WalkPath) (scale horizon : ℕ) (x : Point) {i j : ℕ}
    (hij : i < j) :
    extractedExit s scale horizon x i ≤
      extractedEntrance s scale horizon x j := by
  classical
  exact (excursionStart_le_finish s (terminalOuterBoundary scale x)
      (terminalInnerBoundary scale x) horizon (i + 1)).trans
    (excursionFinish_mono s (terminalOuterBoundary scale x)
      (terminalInnerBoundary scale x) horizon (Nat.succ_le_iff.mpr hij))

lemma adjacent_trajectory_succ (omega : StepPath) (k : ℕ) :
    Adjacent (trajectory omega k) (trajectory omega (k + 1)) := by
  rw [trajectory_succ]
  unfold Adjacent
  generalize hd : omega k = d
  fin_cases d <;> simp [directionVector]

/-- The timed extraction of every stopped successful path is well formed.
This uses completion of all `requiredTerminalCount` segments, including the
last one, from the global-exit geometry theorem. -/
theorem extractTimedTerminalSkeleton_wellFormed_of_stopped_success
    {scale horizon : ℕ} {profileDelta : ℝ} {x : Point} {omega : StepPath}
    (hscale : 1 ≤ scale)
    (hexit : IsOuterExitTime (trajectory omega) scale horizon)
    (hx : SuccessfulPoint (trajectory omega) scale horizon profileDelta x) :
    (extractTimedTerminalSkeleton scale horizon profileDelta x omega).WellFormed := by
  constructor
  · intro j
    constructor
    · simpa [extractTimedTerminalSkeleton] using extractedEntrance_le_extractedExit
        (trajectory omega) scale horizon x (j : ℕ)
    · simpa [extractTimedTerminalSkeleton, extractedExit] using
        terminalVisitSegment_complete_of_stopped_success hscale hexit hx
          (adjacent_trajectory_succ omega) j
  · intro i j hij
    simpa [extractTimedTerminalSkeleton] using extractedExit_le_entrance_of_lt
      (trajectory omega) scale horizon x hij

@[simp] theorem extractTerminalSkeletonCode_entrancePoint
    (scale horizon : ℕ) (profileDelta : ℝ) (x : Point) (omega : StepPath)
    (j : Fin (AppendixLocalTime.requiredTerminalCount scale profileDelta)) :
    (extractTerminalSkeletonCode scale horizon profileDelta x omega).2.1 j =
      trajectory omega (extractedEntrance (trajectory omega) scale horizon x j) :=
  compressTimedSkeleton_entrancePoint omega
    (extractTimedTerminalSkeleton scale horizon profileDelta x omega) j

@[simp] theorem extractTerminalSkeletonCode_exitPoint
    (scale horizon : ℕ) (profileDelta : ℝ) (x : Point) (omega : StepPath)
    (j : Fin (AppendixLocalTime.requiredTerminalCount scale profileDelta)) :
    (extractTerminalSkeletonCode scale horizon profileDelta x omega).2.2 j =
      trajectory omega (extractedExit (trajectory omega) scale horizon x j) :=
  compressTimedSkeleton_exitPoint omega
    (extractTimedTerminalSkeleton scale horizon profileDelta x omega) j

/-- On stopped success, every recorded entrance endpoint lies on the literal
terminal inner boundary. -/
theorem extractTerminalSkeletonCode_entrance_mem
    {scale horizon : ℕ} {profileDelta : ℝ} {x : Point} {omega : StepPath}
    (hscale : 1 ≤ scale)
    (hexit : IsOuterExitTime (trajectory omega) scale horizon)
    (hx : SuccessfulPoint (trajectory omega) scale horizon profileDelta x)
    (j : Fin (AppendixLocalTime.requiredTerminalCount scale profileDelta)) :
    (extractTerminalSkeletonCode scale horizon profileDelta x omega).2.1 j ∈
      terminalInnerBoundary scale x := by
  classical
  let t := extractTimedTerminalSkeleton scale horizon profileDelta x omega
  have ht : t.WellFormed :=
    extractTimedTerminalSkeleton_wellFormed_of_stopped_success hscale hexit hx
  have hfinish : t.entrance j ≤ horizon :=
    (ht.1 j).1.trans (ht.1 j).2
  rw [extractTerminalSkeletonCode_entrancePoint]
  have hfinish' : excursionFinish (trajectory omega)
      (terminalOuterBoundary scale x) (terminalInnerBoundary scale x)
        horizon j ≤ horizon := by
    simpa [t, extractTimedTerminalSkeleton, extractedEntrance] using hfinish
  exact
    excursionFinish_mem_inner_of_le (trajectory omega)
      (terminalOuterBoundary scale x) (terminalInnerBoundary scale x)
        horizon j hfinish'

/-- On stopped success, every recorded exit endpoint lies on the literal
terminal outer boundary. -/
theorem extractTerminalSkeletonCode_exit_mem
    {scale horizon : ℕ} {profileDelta : ℝ} {x : Point} {omega : StepPath}
    (hscale : 1 ≤ scale)
    (hexit : IsOuterExitTime (trajectory omega) scale horizon)
    (hx : SuccessfulPoint (trajectory omega) scale horizon profileDelta x)
    (j : Fin (AppendixLocalTime.requiredTerminalCount scale profileDelta)) :
    (extractTerminalSkeletonCode scale horizon profileDelta x omega).2.2 j ∈
      terminalOuterBoundary scale x := by
  classical
  let t := extractTimedTerminalSkeleton scale horizon profileDelta x omega
  have ht : t.WellFormed :=
    extractTimedTerminalSkeleton_wellFormed_of_stopped_success hscale hexit hx
  have hexitLe : t.exit j ≤ horizon := (ht.1 j).2
  rw [extractTerminalSkeletonCode_exitPoint]
  unfold extractedExit terminalSegmentExitTime excursionStart
  apply firstHitThrough_mem_set_of_le
  simpa [t, extractTimedTerminalSkeleton, extractedExit,
    terminalSegmentExitTime, excursionStart] using hexitLe

/-- Boundary-supported endpoint types used by the terminal Harnack kernels. -/
abbrev TerminalEntrance (scale : ℕ) (x : Point) :=
  {p : Point // p ∈ terminalInnerBoundary scale x}

abbrev TerminalExit (scale : ℕ) (x : Point) :=
  {p : Point // p ∈ terminalOuterBoundary scale x}

/-- Lift a raw compressed code once support of all endpoint coordinates has
been proved. -/
def liftTerminalSkeletonCode {m scale : ℕ} {x : Point}
    (code : TerminalSkeletonCode m)
    (hentrance : ∀ j, code.2.1 j ∈ terminalInnerBoundary scale x)
    (hexit : ∀ j, code.2.2 j ∈ terminalOuterBoundary scale x) :
    MarkedSkeletonPartition.SkeletonIndex (TerminalSkeletonData m)
      (TerminalEntrance scale x) (TerminalExit scale x) m :=
  (code.1, ((fun j ↦ ⟨code.2.1 j, hentrance j⟩),
    fun j ↦ ⟨code.2.2 j, hexit j⟩))

/-- Canonical supported code extracted from a stopped successful path. -/
def extractSupportedTerminalSkeletonCode
    {scale horizon : ℕ} {profileDelta : ℝ} {x : Point} {omega : StepPath}
    (hscale : 1 ≤ scale)
    (hexit : IsOuterExitTime (trajectory omega) scale horizon)
    (hx : SuccessfulPoint (trajectory omega) scale horizon profileDelta x) :
    MarkedSkeletonPartition.SkeletonIndex
      (TerminalSkeletonData
        (AppendixLocalTime.requiredTerminalCount scale profileDelta))
      (TerminalEntrance scale x) (TerminalExit scale x)
      (AppendixLocalTime.requiredTerminalCount scale profileDelta) :=
  liftTerminalSkeletonCode
    (extractTerminalSkeletonCode scale horizon profileDelta x omega)
    (extractTerminalSkeletonCode_entrance_mem hscale hexit hx)
    (extractTerminalSkeletonCode_exit_mem hscale hexit hx)

/-! ## Finite-prefix dependence of the code extractors -/

lemma trajectory_congr_of_incrementPrefix
    {omega omega' : StepPath} {N : ℕ}
    (hprefix : ∀ k < N, omega k = omega' k) {q : ℕ} (hq : q ≤ N) :
    trajectory omega q = trajectory omega' q := by
  unfold trajectory
  apply Finset.sum_congr rfl
  intro k hk
  rw [hprefix k ((Finset.mem_range.mp hk).trans_le hq)]

lemma excursionStep_congr_prefix
    {s t : WalkPath} {horizon : ℕ}
    (hst : ∀ k ≤ horizon, s k = t k)
    (outer inner : Set Point) [DecidablePred (· ∈ outer)]
    [DecidablePred (· ∈ inner)] (start : ℕ) :
    excursionStep s outer inner horizon start =
      excursionStep t outer inner horizon start := by
  unfold excursionStep
  rw [firstHitThrough_congr_prefix hst outer start,
    firstHitThrough_congr_prefix hst inner]

lemma excursionStart_congr_prefix
    {s t : WalkPath} {horizon : ℕ}
    (hst : ∀ k ≤ horizon, s k = t k)
    (outer inner : Set Point) [DecidablePred (· ∈ outer)]
    [DecidablePred (· ∈ inner)] (j : ℕ) :
    excursionStart s outer inner horizon j =
      excursionStart t outer inner horizon j := by
  have hstep : excursionStep s outer inner horizon =
      excursionStep t outer inner horizon := by
    funext start
    exact excursionStep_congr_prefix hst outer inner start
  unfold excursionStart
  rw [hstep, firstHitThrough_congr_prefix hst outer]

lemma excursionFinish_congr_prefix
    {s t : WalkPath} {horizon : ℕ}
    (hst : ∀ k ≤ horizon, s k = t k)
    (outer inner : Set Point) [DecidablePred (· ∈ outer)]
    [DecidablePred (· ∈ inner)] (j : ℕ) :
    excursionFinish s outer inner horizon j =
      excursionFinish t outer inner horizon j := by
  unfold excursionFinish
  rw [excursionStart_congr_prefix hst outer inner j,
    firstHitThrough_congr_prefix hst inner]

lemma incrementSlice_congr {omega omega' : StepPath} {N start stop : ℕ}
    (hprefix : ∀ k < N, omega k = omega' k) (hstop : stop ≤ N) :
    incrementSlice omega start stop = incrementSlice omega' start stop := by
  apply List.ext_get
  · simp
  · intro k hk hk'
    simp only [incrementSlice, List.get_eq_getElem, List.getElem_ofFn]
    rw [hprefix]
    have hklt : k < stop - start := by
      simpa [incrementSlice] using hk
    omega

lemma complementaryPieces_congr : ∀ (m : ℕ)
    {omega omega' : StepPath} {N base horizon : ℕ}
    (entrance exit : Fin m → ℕ),
    (∀ k < N, omega k = omega' k) → horizon ≤ N →
      (∀ j, entrance j ≤ N) →
      complementaryPieces m omega base horizon entrance exit =
        complementaryPieces m omega' base horizon entrance exit := by
  intro m
  induction m with
  | zero =>
      intro omega omega' N base horizon entrance exit hprefix hhorizon hentrance
      funext j
      exact incrementSlice_congr hprefix hhorizon
  | succ m ih =>
      intro omega omega' N base horizon entrance exit hprefix hhorizon hentrance
      funext j
      refine Fin.cases ?_ (fun i ↦ ?_) j
      · exact incrementSlice_congr hprefix (hentrance 0)
      · exact congrFun (ih (fun k ↦ entrance k.succ)
          (fun k ↦ exit k.succ) hprefix hhorizon (fun k ↦ hentrance k.succ)) i

theorem extractTimedTerminalSkeleton_congr_prefix
    {scale horizon : ℕ} {profileDelta : ℝ} {x : Point}
    {omega omega' : StepPath}
    (hprefix : ∀ k < horizon + 1, omega k = omega' k) :
    extractTimedTerminalSkeleton scale horizon profileDelta x omega =
      extractTimedTerminalSkeleton scale horizon profileDelta x omega' := by
  classical
  let s := trajectory omega
  let t := trajectory omega'
  have hst : ∀ k ≤ horizon, s k = t k := by
    intro k hk
    exact trajectory_congr_of_incrementPrefix hprefix (hk.trans (Nat.le_succ _))
  apply TimedTerminalSkeleton.ext
  · rfl
  · funext j
    simpa [extractTimedTerminalSkeleton, extractedEntrance] using
      excursionFinish_congr_prefix hst (terminalOuterBoundary scale x)
        (terminalInnerBoundary scale x) (j : ℕ)
  · funext j
    simpa [extractTimedTerminalSkeleton, extractedExit, terminalSegmentExitTime] using
      excursionStart_congr_prefix hst (terminalOuterBoundary scale x)
        (terminalInnerBoundary scale x) ((j : ℕ) + 1)
  · funext j
    have htime : extractedEntrance s scale horizon x j =
        extractedEntrance t scale horizon x j := by
      simpa [extractedEntrance] using excursionFinish_congr_prefix hst
        (terminalOuterBoundary scale x) (terminalInnerBoundary scale x) (j : ℕ)
    simp only [extractTimedTerminalSkeleton]
    change s (extractedEntrance s scale horizon x j) =
      t (extractedEntrance t scale horizon x j)
    rw [htime]
    apply trajectory_congr_of_incrementPrefix hprefix
    exact firstHitThrough_le_sentinel t (terminalInnerBoundary scale x)
      (excursionStart t (terminalOuterBoundary scale x)
        (terminalInnerBoundary scale x) horizon j) horizon
  · funext j
    have htime : extractedExit s scale horizon x j =
        extractedExit t scale horizon x j := by
      simpa [extractedExit, terminalSegmentExitTime] using
        excursionStart_congr_prefix hst (terminalOuterBoundary scale x)
          (terminalInnerBoundary scale x) ((j : ℕ) + 1)
    simp only [extractTimedTerminalSkeleton]
    change s (extractedExit s scale horizon x j) =
      t (extractedExit t scale horizon x j)
    rw [htime]
    apply trajectory_congr_of_incrementPrefix hprefix
    exact firstHitThrough_le_sentinel t (terminalOuterBoundary scale x)
      ((excursionStep t (terminalOuterBoundary scale x)
        (terminalInnerBoundary scale x) horizon)^[(j : ℕ) + 1] 0) horizon

theorem extractTerminalSkeletonCode_congr_prefix
    {scale horizon : ℕ} {profileDelta : ℝ} {x : Point}
    {omega omega' : StepPath}
    (hprefix : ∀ k < horizon + 1, omega k = omega' k) :
    extractTerminalSkeletonCode scale horizon profileDelta x omega =
    extractTerminalSkeletonCode scale horizon profileDelta x omega' := by
  classical
  let tw := extractTimedTerminalSkeleton scale horizon profileDelta x omega
  let tw' := extractTimedTerminalSkeleton scale horizon profileDelta x omega'
  have htw : tw = tw' := extractTimedTerminalSkeleton_congr_prefix hprefix
  have hentrance : ∀ j, tw'.entrance j ≤ horizon + 1 := by
    intro j
    exact firstHitThrough_le_sentinel (trajectory omega')
      (terminalInnerBoundary scale x)
      (excursionStart (trajectory omega') (terminalOuterBoundary scale x)
        (terminalInnerBoundary scale x) horizon j) horizon
  unfold extractTerminalSkeletonCode compressTimedSkeleton
  change (TerminalSkeletonData.mk
      (complementaryPieces _ omega 0 horizon tw.entrance tw.exit),
      (tw.entrancePoint, tw.exitPoint)) =
    (TerminalSkeletonData.mk
      (complementaryPieces _ omega' 0 horizon tw'.entrance tw'.exit),
      (tw'.entrancePoint, tw'.exitPoint))
  rw [htw]
  apply Prod.ext
  · apply TerminalSkeletonData.ext
    exact complementaryPieces_congr _ tw'.entrance tw'.exit hprefix
      (Nat.le_succ _) hentrance
  · rfl

lemma terminalVisitVector_congr_prefix
    {scale horizon : ℕ} {profileDelta : ℝ} {x : Point}
    {omega omega' : StepPath}
    (hprefix : ∀ k < horizon + 1, omega k = omega' k) :
    terminalVisitVector (trajectory omega) scale horizon profileDelta x =
      terminalVisitVector (trajectory omega') scale horizon profileDelta x := by
  classical
  have htraj : ∀ k ≤ horizon, trajectory omega k = trajectory omega' k := by
    intro k hk
    exact trajectory_congr_of_incrementPrefix hprefix (hk.trans (Nat.le_succ _))
  funext j
  unfold terminalVisitVector terminalExcursionVisits innerVisitCount innerVisitTimes
  have hfinish := excursionFinish_congr_prefix htraj
    (terminalOuterBoundary scale x) (terminalInnerBoundary scale x) j
  have hstart := excursionStart_congr_prefix htraj
    (terminalOuterBoundary scale x) (terminalInnerBoundary scale x) (j + 1)
  rw [hfinish, hstart]
  apply congrArg Finset.card
  apply Finset.filter_congr
  intro k hk
  have hklt := (Finset.mem_Ico.mp hk).2
  have hstartBound := firstHitThrough_le_sentinel (trajectory omega')
    (terminalOuterBoundary scale x)
      ((excursionStep (trajectory omega') (terminalOuterBoundary scale x)
        (terminalInnerBoundary scale x) horizon)^[j + 1] 0) horizon
  have hstartBound' : excursionStart (trajectory omega')
      (terminalOuterBoundary scale x) (terminalInnerBoundary scale x)
        horizon (j + 1) ≤ horizon + 1 := by
    simpa [excursionStart] using hstartBound
  have hkN : k ≤ horizon + 1 := hklt.le.trans hstartBound'
  rw [trajectory_congr_of_incrementPrefix hprefix hkN]

theorem extractMarkedTerminalCode_congr_prefix
    {scale horizon : ℕ} {profileDelta : ℝ} {x : Point}
    {omega omega' : StepPath}
    (hprefix : ∀ k < horizon + 1, omega k = omega' k) :
    extractMarkedTerminalCode scale horizon profileDelta x omega =
      extractMarkedTerminalCode scale horizon profileDelta x omega' := by
  have hcode := extractTerminalSkeletonCode_congr_prefix
    (scale := scale) (profileDelta := profileDelta) (x := x) hprefix
  have hvisits := terminalVisitVector_congr_prefix
    (scale := scale) (profileDelta := profileDelta) (x := x) hprefix
  unfold extractMarkedTerminalCode
  rw [hcode, hvisits]

/-! ## Stopped-horizon uniqueness and code atoms -/

theorem isOuterExitTime_unique {s : WalkPath} {scale horizon horizon' : ℕ}
    (h : IsOuterExitTime s scale horizon)
    (h' : IsOuterExitTime s scale horizon') : horizon = horizon' := by
  rcases lt_trichotomy horizon horizon' with hlt | heq | hgt
  · exact (h'.2 horizon hlt h.1).elim
  · exact heq
  · exact (h.2 horizon' hgt h'.1).elim

theorem shiftedStoppedSuccessfulPointAtEvent_disjoint_of_ne
    (start scale : ℕ) (profileDelta : ℝ) (x : Point)
    {horizon horizon' : ℕ} (hne : horizon ≠ horizon') :
    Disjoint
      (shiftedStoppedSuccessfulPointAtEvent start scale horizon profileDelta x)
      (shiftedStoppedSuccessfulPointAtEvent start scale horizon' profileDelta x) := by
  rw [Set.disjoint_left]
  intro omega hmem hmem'
  exact hne (isOuterExitTime_unique hmem.1 hmem'.1)

/-- The fixed-horizon fibre of one compressed complementary code. -/
def stoppedTerminalSkeletonCodeAtom (start scale horizon : ℕ)
    (profileDelta : ℝ) (x : Point)
    (code : TerminalSkeletonCode
      (AppendixLocalTime.requiredTerminalCount scale profileDelta)) : Set StepPath :=
  shiftedStoppedSuccessfulPointAtEvent start scale horizon profileDelta x ∩
    {omega | extractTerminalSkeletonCode scale horizon profileDelta x
      (shiftSteps start omega) = code}

/-- Extend a finite direction word arbitrarily beyond its length. -/
def extendFiniteDirectionWord {N : ℕ} (u : Fin N → Direction) : StepPath :=
  fun k ↦ if hk : k < N then u ⟨k, hk⟩ else 0

@[simp] theorem stepPrefix_extendFiniteDirectionWord {N : ℕ}
    (u : Fin N → Direction) :
    stepPrefix N (extendFiniteDirectionWord u) = u := by
  funext k
  simp [stepPrefix, extendFiniteDirectionWord, k.isLt]

theorem extractTerminalSkeletonCode_extend_stepBlock
    (start scale horizon : ℕ) (profileDelta : ℝ) (x : Point)
    (omega : StepPath) :
    extractTerminalSkeletonCode scale horizon profileDelta x
        (extendFiniteDirectionWord (stepBlock start (horizon + 1) omega)) =
      extractTerminalSkeletonCode scale horizon profileDelta x
        (shiftSteps start omega) := by
  apply extractTerminalSkeletonCode_congr_prefix
  intro k hk
  simp [extendFiniteDirectionWord, stepBlock, shiftSteps, hk]

theorem extractMarkedTerminalCode_extend_stepBlock
    (start scale horizon : ℕ) (profileDelta : ℝ) (x : Point)
    (omega : StepPath) :
    extractMarkedTerminalCode scale horizon profileDelta x
        (extendFiniteDirectionWord (stepBlock start (horizon + 1) omega)) =
      extractMarkedTerminalCode scale horizon profileDelta x
        (shiftSteps start omega) := by
  apply extractMarkedTerminalCode_congr_prefix
  intro k hk
  simp [extendFiniteDirectionWord, stepBlock, shiftSteps, hk]

theorem measurableSet_fixedTerminalSkeletonCodeFiber
    (start scale horizon : ℕ) (profileDelta : ℝ) (x : Point)
    (code : TerminalSkeletonCode
      (AppendixLocalTime.requiredTerminalCount scale profileDelta)) :
    MeasurableSet {omega : StepPath |
      extractTerminalSkeletonCode scale horizon profileDelta x
        (shiftSteps start omega) = code} := by
  let C : Set (Fin (horizon + 1) → Direction) :=
    {u | extractTerminalSkeletonCode scale horizon profileDelta x
      (extendFiniteDirectionWord u) = code}
  have hC : MeasurableSet C := (Set.to_countable C).measurableSet
  have heq : {omega : StepPath |
      extractTerminalSkeletonCode scale horizon profileDelta x
        (shiftSteps start omega) = code} =
      stepBlock start (horizon + 1) ⁻¹' C := by
    ext omega
    simp only [Set.mem_ofPred_eq, Set.mem_preimage]
    change _ ↔ extractTerminalSkeletonCode scale horizon profileDelta x
      (extendFiniteDirectionWord (stepBlock start (horizon + 1) omega)) = code
    rw [extractTerminalSkeletonCode_extend_stepBlock]
  rw [heq]
  exact (measurable_stepBlock start (horizon + 1)) hC

theorem measurableSet_fixedMarkedTerminalCodeFiber
    (start scale horizon : ℕ) (profileDelta : ℝ) (x : Point)
    (code : MarkedSkeletonPartition.MarkedIndex
      (TerminalSkeletonData
        (AppendixLocalTime.requiredTerminalCount scale profileDelta))
      Point Point (AppendixLocalTime.requiredTerminalCount scale profileDelta)) :
    MeasurableSet {omega : StepPath |
      extractMarkedTerminalCode scale horizon profileDelta x
        (shiftSteps start omega) = code} := by
  let C : Set (Fin (horizon + 1) → Direction) :=
    {u | extractMarkedTerminalCode scale horizon profileDelta x
      (extendFiniteDirectionWord u) = code}
  have hC : MeasurableSet C := (Set.to_countable C).measurableSet
  have heq : {omega : StepPath |
      extractMarkedTerminalCode scale horizon profileDelta x
        (shiftSteps start omega) = code} =
      stepBlock start (horizon + 1) ⁻¹' C := by
    ext omega
    simp only [Set.mem_ofPred_eq, Set.mem_preimage]
    change _ ↔ extractMarkedTerminalCode scale horizon profileDelta x
      (extendFiniteDirectionWord (stepBlock start (horizon + 1) omega)) = code
    rw [extractMarkedTerminalCode_extend_stepBlock]
  rw [heq]
  exact (measurable_stepBlock start (horizon + 1)) hC

theorem measurableSet_stoppedTerminalSkeletonCodeAtom
    (start scale horizon : ℕ) (profileDelta : ℝ) (x : Point)
    (code : TerminalSkeletonCode
      (AppendixLocalTime.requiredTerminalCount scale profileDelta)) :
    MeasurableSet
      (stoppedTerminalSkeletonCodeAtom start scale horizon profileDelta x code) :=
  (measurableSet_shiftedStoppedSuccessfulPointAtEvent
    start scale horizon profileDelta x).inter
      (measurableSet_fixedTerminalSkeletonCodeFiber
        start scale horizon profileDelta x code)

theorem stoppedTerminalSkeletonCodeAtom_disjoint_of_ne
    (start scale horizon : ℕ) (profileDelta : ℝ) (x : Point)
    {code code' : TerminalSkeletonCode
      (AppendixLocalTime.requiredTerminalCount scale profileDelta)}
    (hne : code ≠ code') :
    Disjoint
      (stoppedTerminalSkeletonCodeAtom start scale horizon profileDelta x code)
      (stoppedTerminalSkeletonCodeAtom start scale horizon profileDelta x code') := by
  rw [Set.disjoint_left]
  intro omega hmem hmem'
  exact hne (hmem.2.symm.trans hmem'.2)

theorem stoppedSuccessfulPointAtEvent_covered_by_codeAtoms
    (start scale horizon : ℕ) (profileDelta : ℝ) (x : Point) :
    shiftedStoppedSuccessfulPointAtEvent start scale horizon profileDelta x =
      ⋃ code : TerminalSkeletonCode
        (AppendixLocalTime.requiredTerminalCount scale profileDelta),
        stoppedTerminalSkeletonCodeAtom start scale horizon profileDelta x code := by
  ext omega
  constructor
  · intro hmem
    refine Set.mem_iUnion.mpr
      ⟨extractTerminalSkeletonCode scale horizon profileDelta x
        (shiftSteps start omega), hmem, rfl⟩
  · intro hmem
    obtain ⟨code, hcode⟩ := Set.mem_iUnion.mp hmem
    exact hcode.1

/-- Coverage of the variable-horizon stopped event by countably many
fixed-horizon compressed code atoms. -/
theorem stoppedSuccessfulPointEvent_covered_by_codeAtoms
    (start scale : ℕ) (profileDelta : ℝ) (x : Point) :
    stoppedSuccessfulPointEvent start scale profileDelta x =
      ⋃ horizon : ℕ, ⋃ code : TerminalSkeletonCode
        (AppendixLocalTime.requiredTerminalCount scale profileDelta),
        stoppedTerminalSkeletonCodeAtom start scale horizon profileDelta x code := by
  rw [stoppedSuccessfulPointEvent_eq_iUnion_shiftedAt]
  congr 1
  funext horizon
  exact stoppedSuccessfulPointAtEvent_covered_by_codeAtoms
    start scale horizon profileDelta x

/-! ## Horizon-collapsed skeleton atoms -/

/-- The genuine unmarked skeleton atom.  The first-exit horizon is summed
inside the atom; it is not a component of `TerminalSkeletonData`. -/
def stoppedTerminalSkeletonAtom (start scale : ℕ) (profileDelta : ℝ)
    (x : Point)
    (code : TerminalSkeletonCode
      (AppendixLocalTime.requiredTerminalCount scale profileDelta)) : Set StepPath :=
  ⋃ horizon : ℕ,
    stoppedTerminalSkeletonCodeAtom start scale horizon profileDelta x code

theorem stoppedTerminalSkeletonAtom_disjoint_of_ne
    (start scale : ℕ) (profileDelta : ℝ) (x : Point)
    {code code' : TerminalSkeletonCode
      (AppendixLocalTime.requiredTerminalCount scale profileDelta)}
    (hne : code ≠ code') :
    Disjoint (stoppedTerminalSkeletonAtom start scale profileDelta x code)
      (stoppedTerminalSkeletonAtom start scale profileDelta x code') := by
  rw [Set.disjoint_left]
  intro omega hmem hmem'
  obtain ⟨horizon, hhorizon⟩ := Set.mem_iUnion.mp hmem
  obtain ⟨horizon', hhorizon'⟩ := Set.mem_iUnion.mp hmem'
  have heq : horizon = horizon' :=
    isOuterExitTime_unique hhorizon.1.1 hhorizon'.1.1
  subst horizon'
  exact hne (hhorizon.2.symm.trans hhorizon'.2)

theorem measurableSet_stoppedTerminalSkeletonAtom
    (start scale : ℕ) (profileDelta : ℝ) (x : Point)
    (code : TerminalSkeletonCode
      (AppendixLocalTime.requiredTerminalCount scale profileDelta)) :
    MeasurableSet (stoppedTerminalSkeletonAtom start scale profileDelta x code) :=
  MeasurableSet.iUnion fun horizon ↦
    measurableSet_stoppedTerminalSkeletonCodeAtom
      start scale horizon profileDelta x code

theorem stoppedSuccessfulPointEvent_eq_iUnion_skeletonAtoms
    (start scale : ℕ) (profileDelta : ℝ) (x : Point) :
    stoppedSuccessfulPointEvent start scale profileDelta x =
      ⋃ code : TerminalSkeletonCode
        (AppendixLocalTime.requiredTerminalCount scale profileDelta),
        stoppedTerminalSkeletonAtom start scale profileDelta x code := by
  rw [stoppedSuccessfulPointEvent_covered_by_codeAtoms]
  ext omega
  simp only [Set.mem_iUnion, stoppedTerminalSkeletonAtom]
  constructor
  · rintro ⟨horizon, code, hmem⟩
    exact ⟨code, horizon, hmem⟩
  · rintro ⟨code, horizon, hmem⟩
    exact ⟨horizon, code, hmem⟩

/-! ## Marked code atoms -/

/-- A fixed-horizon skeleton atom with its terminal visit vector recorded. -/
def stoppedMarkedTerminalCodeAtom (start scale horizon : ℕ)
    (profileDelta : ℝ) (x : Point)
    (code : MarkedSkeletonPartition.MarkedIndex
      (TerminalSkeletonData
        (AppendixLocalTime.requiredTerminalCount scale profileDelta))
      Point Point (AppendixLocalTime.requiredTerminalCount scale profileDelta)) :
    Set StepPath :=
  shiftedStoppedSuccessfulPointAtEvent start scale horizon profileDelta x ∩
    {omega | extractMarkedTerminalCode scale horizon profileDelta x
      (shiftSteps start omega) = code}

theorem measurableSet_stoppedMarkedTerminalCodeAtom
    (start scale horizon : ℕ) (profileDelta : ℝ) (x : Point)
    (code : MarkedSkeletonPartition.MarkedIndex
      (TerminalSkeletonData
        (AppendixLocalTime.requiredTerminalCount scale profileDelta))
      Point Point (AppendixLocalTime.requiredTerminalCount scale profileDelta)) :
    MeasurableSet
      (stoppedMarkedTerminalCodeAtom start scale horizon profileDelta x code) :=
  (measurableSet_shiftedStoppedSuccessfulPointAtEvent
    start scale horizon profileDelta x).inter
      (measurableSet_fixedMarkedTerminalCodeFiber
        start scale horizon profileDelta x code)

/-- The horizon-collapsed marked atom. -/
def stoppedMarkedTerminalAtom (start scale : ℕ) (profileDelta : ℝ)
    (x : Point)
    (code : MarkedSkeletonPartition.MarkedIndex
      (TerminalSkeletonData
        (AppendixLocalTime.requiredTerminalCount scale profileDelta))
      Point Point (AppendixLocalTime.requiredTerminalCount scale profileDelta)) :
    Set StepPath :=
  ⋃ horizon : ℕ,
    stoppedMarkedTerminalCodeAtom start scale horizon profileDelta x code

theorem measurableSet_stoppedMarkedTerminalAtom
    (start scale : ℕ) (profileDelta : ℝ) (x : Point)
    (code : MarkedSkeletonPartition.MarkedIndex
      (TerminalSkeletonData
        (AppendixLocalTime.requiredTerminalCount scale profileDelta))
      Point Point (AppendixLocalTime.requiredTerminalCount scale profileDelta)) :
    MeasurableSet (stoppedMarkedTerminalAtom start scale profileDelta x code) :=
  MeasurableSet.iUnion fun horizon ↦
    measurableSet_stoppedMarkedTerminalCodeAtom
      start scale horizon profileDelta x code

theorem stoppedMarkedTerminalAtom_disjoint_of_ne
    (start scale : ℕ) (profileDelta : ℝ) (x : Point)
    {code code' : MarkedSkeletonPartition.MarkedIndex
      (TerminalSkeletonData
        (AppendixLocalTime.requiredTerminalCount scale profileDelta))
      Point Point (AppendixLocalTime.requiredTerminalCount scale profileDelta)}
    (hne : code ≠ code') :
    Disjoint (stoppedMarkedTerminalAtom start scale profileDelta x code)
      (stoppedMarkedTerminalAtom start scale profileDelta x code') := by
  rw [Set.disjoint_left]
  intro omega hmem hmem'
  obtain ⟨horizon, hhorizon⟩ := Set.mem_iUnion.mp hmem
  obtain ⟨horizon', hhorizon'⟩ := Set.mem_iUnion.mp hmem'
  have heq : horizon = horizon' :=
    isOuterExitTime_unique hhorizon.1.1 hhorizon'.1.1
  subst horizon'
  exact hne (hhorizon.2.symm.trans hhorizon'.2)

theorem stoppedSuccessfulPointEvent_eq_iUnion_markedAtoms
    (start scale : ℕ) (profileDelta : ℝ) (x : Point) :
    stoppedSuccessfulPointEvent start scale profileDelta x =
      ⋃ code : MarkedSkeletonPartition.MarkedIndex
        (TerminalSkeletonData
          (AppendixLocalTime.requiredTerminalCount scale profileDelta))
        Point Point (AppendixLocalTime.requiredTerminalCount scale profileDelta),
        stoppedMarkedTerminalAtom start scale profileDelta x code := by
  rw [stoppedSuccessfulPointEvent_eq_iUnion_shiftedAt]
  ext omega
  simp only [Set.mem_iUnion, stoppedMarkedTerminalAtom,
    stoppedMarkedTerminalCodeAtom, Set.mem_inter_iff, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨horizon, hmem⟩
    let code := extractMarkedTerminalCode scale horizon profileDelta x
      (shiftSteps start omega)
    exact ⟨code, horizon, hmem, rfl⟩
  · rintro ⟨code, horizon, hmem, _hcode⟩
    exact ⟨horizon, hmem⟩

/-! ## Total stopped coding functions -/

/-- The fixed first-global-exit event, on the deterministic shifted block. -/
def shiftedOuterExitAtEvent (start scale horizon : ℕ) : Set StepPath :=
  {omega | IsOuterExitTime (shiftedWalk start omega) scale horizon}

theorem measurableSet_shiftedOuterExitAtEvent (start scale horizon : ℕ) :
    MeasurableSet (shiftedOuterExitAtEvent start scale horizon) := by
  change MeasurableSet
    (shiftedWalkEvent start (outerExitAtEvent scale horizon))
  exact measurableSet_shiftedWalkEvent start
    (measurableSet_outerExitAtEvent scale horizon)

/-- Defaulted first outer-exit horizon.  The value is zero only when the
boundary is never hit or when it is first hit at time zero. -/
noncomputable def stoppedOuterExitHorizon (start scale : ℕ)
    (omega : StepPath) : ℕ := by
  classical
  exact if h : ∃ horizon : ℕ,
      IsOuterExitTime (shiftedWalk start omega) scale horizon then
    Nat.find h
  else 0

theorem stoppedOuterExitHorizon_eq_of_isOuterExitTime
    {start scale horizon : ℕ} {omega : StepPath}
    (hexit : IsOuterExitTime (shiftedWalk start omega) scale horizon) :
    stoppedOuterExitHorizon start scale omega = horizon := by
  classical
  unfold stoppedOuterExitHorizon
  let h : ∃ horizon : ℕ,
      IsOuterExitTime (shiftedWalk start omega) scale horizon := ⟨horizon, hexit⟩
  rw [dif_pos h]
  exact isOuterExitTime_unique (Nat.find_spec h) hexit

theorem stoppedOuterExitHorizon_eq_iff
    (start scale horizon : ℕ) (omega : StepPath) :
    stoppedOuterExitHorizon start scale omega = horizon ↔
      IsOuterExitTime (shiftedWalk start omega) scale horizon ∨
        (horizon = 0 ∧ ¬ ∃ h : ℕ,
          IsOuterExitTime (shiftedWalk start omega) scale h) := by
  classical
  constructor
  · intro heq
    by_cases h : ∃ h : ℕ,
        IsOuterExitTime (shiftedWalk start omega) scale h
    · left
      unfold stoppedOuterExitHorizon at heq
      rw [dif_pos h] at heq
      simpa [← heq] using Nat.find_spec h
    · right
      refine ⟨?_, h⟩
      unfold stoppedOuterExitHorizon at heq
      simpa [dif_neg h] using heq.symm
  · rintro (hexit | ⟨rfl, hno⟩)
    · exact stoppedOuterExitHorizon_eq_of_isOuterExitTime hexit
    · unfold stoppedOuterExitHorizon
      rw [dif_neg hno]

theorem measurableSet_stoppedOuterExitHorizon_eq
    (start scale horizon : ℕ) :
    MeasurableSet {omega : StepPath |
      stoppedOuterExitHorizon start scale omega = horizon} := by
  let noExit : Set StepPath :=
    {omega | ¬ ∃ h : ℕ, IsOuterExitTime (shiftedWalk start omega) scale h}
  have hnoExit : MeasurableSet noExit := by
    have heq : noExit = (⋃ h : ℕ, shiftedOuterExitAtEvent start scale h)ᶜ := by
      ext omega
      simp [noExit, shiftedOuterExitAtEvent]
    rw [heq]
    exact (MeasurableSet.iUnion fun h ↦
      measurableSet_shiftedOuterExitAtEvent start scale h).compl
  have heq : {omega : StepPath |
      stoppedOuterExitHorizon start scale omega = horizon} =
      shiftedOuterExitAtEvent start scale horizon ∪
        if horizon = 0 then noExit else ∅ := by
    ext omega
    simp only [Set.mem_ofPred_eq, Set.mem_union]
    rw [stoppedOuterExitHorizon_eq_iff]
    by_cases hzero : horizon = 0
    · simp [shiftedOuterExitAtEvent, hzero, noExit]
    · simp [shiftedOuterExitAtEvent, hzero]
  rw [heq]
  apply (measurableSet_shiftedOuterExitAtEvent start scale horizon).union
  split_ifs
  · exact hnoExit
  · exact MeasurableSet.empty

/-- Total horizon-collapsed unmarked code used by singleton coding fibres. -/
def stoppedTerminalSkeletonCode (start scale : ℕ) (profileDelta : ℝ)
    (x : Point) (omega : StepPath) :
    TerminalSkeletonCode
      (AppendixLocalTime.requiredTerminalCount scale profileDelta) :=
  let horizon := stoppedOuterExitHorizon start scale omega
  extractTerminalSkeletonCode scale horizon profileDelta x
    (shiftSteps start omega)

/-- Total horizon-collapsed marked code. -/
def stoppedMarkedTerminalCode (start scale : ℕ) (profileDelta : ℝ)
    (x : Point) (omega : StepPath) :
    MarkedSkeletonPartition.MarkedIndex
      (TerminalSkeletonData
        (AppendixLocalTime.requiredTerminalCount scale profileDelta))
      Point Point (AppendixLocalTime.requiredTerminalCount scale profileDelta) :=
  let horizon := stoppedOuterExitHorizon start scale omega
  extractMarkedTerminalCode scale horizon profileDelta x
    (shiftSteps start omega)

theorem measurableSet_stoppedTerminalSkeletonCode_fiber
    (start scale : ℕ) (profileDelta : ℝ) (x : Point)
    (code : TerminalSkeletonCode
      (AppendixLocalTime.requiredTerminalCount scale profileDelta)) :
    MeasurableSet {omega : StepPath |
      stoppedTerminalSkeletonCode start scale profileDelta x omega = code} := by
  have heq : {omega : StepPath |
      stoppedTerminalSkeletonCode start scale profileDelta x omega = code} =
      ⋃ horizon : ℕ,
        {omega | stoppedOuterExitHorizon start scale omega = horizon} ∩
          {omega | extractTerminalSkeletonCode scale horizon profileDelta x
            (shiftSteps start omega) = code} := by
    ext omega
    simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_ofPred_eq]
    constructor
    · intro hcode
      refine ⟨stoppedOuterExitHorizon start scale omega, rfl, ?_⟩
      exact hcode
    · rintro ⟨horizon, hhorizon, hcode⟩
      unfold stoppedTerminalSkeletonCode
      rw [hhorizon]
      exact hcode
  rw [heq]
  exact MeasurableSet.iUnion fun horizon ↦
    (measurableSet_stoppedOuterExitHorizon_eq start scale horizon).inter
      (measurableSet_fixedTerminalSkeletonCodeFiber
        start scale horizon profileDelta x code)

theorem measurableSet_stoppedMarkedTerminalCode_fiber
    (start scale : ℕ) (profileDelta : ℝ) (x : Point)
    (code : MarkedSkeletonPartition.MarkedIndex
      (TerminalSkeletonData
        (AppendixLocalTime.requiredTerminalCount scale profileDelta))
      Point Point (AppendixLocalTime.requiredTerminalCount scale profileDelta)) :
    MeasurableSet {omega : StepPath |
      stoppedMarkedTerminalCode start scale profileDelta x omega = code} := by
  have heq : {omega : StepPath |
      stoppedMarkedTerminalCode start scale profileDelta x omega = code} =
      ⋃ horizon : ℕ,
        {omega | stoppedOuterExitHorizon start scale omega = horizon} ∩
          {omega | extractMarkedTerminalCode scale horizon profileDelta x
            (shiftSteps start omega) = code} := by
    ext omega
    simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_ofPred_eq]
    constructor
    · intro hcode
      refine ⟨stoppedOuterExitHorizon start scale omega, rfl, ?_⟩
      exact hcode
    · rintro ⟨horizon, hhorizon, hcode⟩
      unfold stoppedMarkedTerminalCode
      rw [hhorizon]
      exact hcode
  rw [heq]
  exact MeasurableSet.iUnion fun horizon ↦
    (measurableSet_stoppedOuterExitHorizon_eq start scale horizon).inter
      (measurableSet_fixedMarkedTerminalCodeFiber
        start scale horizon profileDelta x code)

/-- On the successful source, the total-code fibre is exactly the
horizon-collapsed skeleton atom. -/
theorem codingFiber_stoppedTerminalSkeletonCode_eq_atom
    (start scale : ℕ) (profileDelta : ℝ) (x : Point)
    (code : TerminalSkeletonCode
      (AppendixLocalTime.requiredTerminalCount scale profileDelta)) :
    MarkedSkeletonPartition.codingFiber
      (stoppedSuccessfulPointEvent start scale profileDelta x)
      (stoppedTerminalSkeletonCode start scale profileDelta x) code =
        stoppedTerminalSkeletonAtom start scale profileDelta x code := by
  ext omega
  constructor
  · rintro ⟨⟨horizon, hexit, hx⟩, hcode⟩
    have hhorizon := stoppedOuterExitHorizon_eq_of_isOuterExitTime hexit
    refine Set.mem_iUnion.mpr ⟨horizon, ⟨hexit, hx⟩, ?_⟩
    simpa [stoppedTerminalSkeletonCode, hhorizon] using hcode
  · intro hmem
    obtain ⟨horizon, ⟨hexit, hx⟩, hcode⟩ := Set.mem_iUnion.mp hmem
    have hhorizon := stoppedOuterExitHorizon_eq_of_isOuterExitTime hexit
    refine ⟨⟨horizon, hexit, hx⟩, ?_⟩
    simpa [stoppedTerminalSkeletonCode, hhorizon] using hcode

/-- Marked analogue of the preceding fibre identification. -/
theorem codingFiber_stoppedMarkedTerminalCode_eq_atom
    (start scale : ℕ) (profileDelta : ℝ) (x : Point)
    (code : MarkedSkeletonPartition.MarkedIndex
      (TerminalSkeletonData
        (AppendixLocalTime.requiredTerminalCount scale profileDelta))
      Point Point (AppendixLocalTime.requiredTerminalCount scale profileDelta)) :
    MarkedSkeletonPartition.codingFiber
      (stoppedSuccessfulPointEvent start scale profileDelta x)
      (stoppedMarkedTerminalCode start scale profileDelta x) code =
        stoppedMarkedTerminalAtom start scale profileDelta x code := by
  ext omega
  constructor
  · rintro ⟨⟨horizon, hexit, hx⟩, hcode⟩
    have hhorizon := stoppedOuterExitHorizon_eq_of_isOuterExitTime hexit
    refine Set.mem_iUnion.mpr ⟨horizon, ⟨hexit, hx⟩, ?_⟩
    simpa [stoppedMarkedTerminalCode, hhorizon] using hcode
  · intro hmem
    obtain ⟨horizon, ⟨hexit, hx⟩, hcode⟩ := Set.mem_iUnion.mp hmem
    have hhorizon := stoppedOuterExitHorizon_eq_of_isOuterExitTime hexit
    refine ⟨⟨horizon, hexit, hx⟩, ?_⟩
    simpa [stoppedMarkedTerminalCode, hhorizon] using hcode

end

end Erdos1165.TerminalSkeletonWords
