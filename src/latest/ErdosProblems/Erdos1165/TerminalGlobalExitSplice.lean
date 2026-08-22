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

import ErdosProblems.Erdos1165.MarkedBridgeFactorization
import ErdosProblems.Erdos1165.TerminalSkeletonWords

/-!
# The global exit under a finite terminal splice

Replacing terminal inner-to-outer words changes their durations, so the
global outer-exit horizon of the reconstructed word need not be the original
integer horizon.  This file isolates the elementary pathwise fact needed to
handle that change.

Every vertex strictly before the end of a reconstructed finite word is of
one of two kinds: it is a retained vertex from the original stopped prefix,
or it belongs to a replacement terminal word.  The former cannot lie on the
global boundary by the original first-hit property.  The latter cannot lie
there because the terminal disc is disjoint from the global boundary.  If
the last reconstructed vertex is the original global-boundary vertex, the
new word therefore has its first global-boundary hit exactly at its own
length.

The result is stated both for an arbitrary finite word and directly for the
`alternatingConcat` representation used by compressed terminal skeletons.
-/

namespace Erdos1165.TerminalGlobalExitSplice

open Set
open ThickPoint TerminalExcursionPathwise TerminalSkeletonWords
open TerminalSequentialVisitLaw MarkedBridgeFactorization

noncomputable section

/-! ## The walk carried by a finite direction word -/

/-- Position after the first `t` directions of `word`, starting at `a`.
For `t >= word.length` this stays at the endpoint. -/
def wordPosition (a : Point) (word : List Direction) (t : ℕ) : Point :=
  (word.take t).foldl Annulus.neighbor a

/-- The infinite path obtained by following a finite word and then staying
at its endpoint. -/
def wordWalk (a : Point) (word : List Direction) : WalkPath :=
  fun t ↦ wordPosition a word t

@[simp] theorem wordPosition_zero (a : Point) (word : List Direction) :
    wordPosition a word 0 = a := by
  simp [wordPosition]

@[simp] theorem wordWalk_zero (a : Point) (word : List Direction) :
    wordWalk a word 0 = a := by
  simp [wordWalk]

@[simp] theorem wordPosition_length (a : Point) (word : List Direction) :
    wordPosition a word word.length = word.foldl Annulus.neighbor a := by
  simp [wordPosition]

@[simp] theorem wordWalk_length (a : Point) (word : List Direction) :
    wordWalk a word word.length = word.foldl Annulus.neighbor a := by
  simp [wordWalk]

theorem wordPosition_eq_endpoint_of_length_le (a : Point)
    (word : List Direction) {t : ℕ} (ht : word.length ≤ t) :
    wordPosition a word t = word.foldl Annulus.neighbor a := by
  simp [wordPosition, List.take_of_length_le ht]

theorem wordPosition_succ (a : Point) (word : List Direction)
    {t : ℕ} (ht : t < word.length) :
    wordPosition a word (t + 1) =
      Annulus.neighbor (wordPosition a word t) word[t] := by
  unfold wordPosition
  rw [← List.take_append_getElem (l := word) (i := t) ht,
    List.foldl_append]
  rfl

@[simp] theorem wordPosition_cons_succ (a : Point) (d : Direction)
    (word : List Direction) (t : ℕ) :
    wordPosition a (d :: word) (t + 1) =
      wordPosition (Annulus.neighbor a d) word t := by
  simp [wordPosition, List.take_succ_cons]

/-- Following the increment slice `[start, stop)` from the actual position
at `start` reproduces the original trajectory. -/
theorem wordPosition_incrementSlice (omega : StepPath)
    {start stop t : ℕ} (_hstart : start ≤ stop) (ht : t ≤ stop - start) :
    wordPosition (trajectory omega start) (incrementSlice omega start stop) t =
      trajectory omega (start + t) := by
  induction t with
  | zero => simp
  | succ t ih =>
      have htlt : t < (incrementSlice omega start stop).length := by
        simp only [incrementSlice_length]
        omega
      rw [wordPosition_succ _ _ htlt, ih (by omega)]
      simp only [incrementSlice, List.getElem_ofFn, Annulus.neighbor]
      rw [show start + (t + 1) = (start + t) + 1 by omega,
        trajectory_succ]

/-- A finite prefix list carries the same positions as the absolute walk
started at `a`. -/
theorem wordPosition_ofFn_stepPrefix (a : Point) (omega : StepPath)
    {N q : ℕ} (hq : q ≤ N) :
    wordPosition a (List.ofFn (stepPrefix N omega)) q =
      PlanarPotential.trajectoryFrom a omega q := by
  induction q with
  | zero => simp [PlanarPotential.trajectoryFrom]
  | succ q ih =>
      have hqN : q < N := by omega
      have hqLength : q < (List.ofFn (stepPrefix N omega)).length := by
        simp [hqN]
      rw [wordPosition_succ _ _ hqLength, ih hqN.le]
      simp only [List.getElem_ofFn, stepPrefix]
      rw [PlanarPotential.trajectoryFrom_succ]
      rfl

/-- Prefix-list bridge used to transfer a finite-word first-exit statement
to any infinite step path carrying that exact prefix. -/
theorem wordWalk_zero_eq_trajectory_of_prefixList
    {word : List Direction} {omega : StepPath}
    (hprefix : List.ofFn (stepPrefix word.length omega) = word)
    {q : ℕ} (hq : q ≤ word.length) :
    wordWalk (0, 0) word q = trajectory omega q := by
  rw [← hprefix]
  change wordPosition (0, 0) (List.ofFn (stepPrefix word.length omega)) q = _
  rw [wordPosition_ofFn_stepPrefix (0, 0) omega hq,
    PlanarPotential.trajectoryFrom_eq_add_trajectory]
  ext <;> simp

lemma adjacent_trajectoryFrom_succ (a : Point) (omega : StepPath) (q : ℕ) :
    Adjacent (PlanarPotential.trajectoryFrom a omega q)
      (PlanarPotential.trajectoryFrom a omega (q + 1)) := by
  rw [PlanarPotential.trajectoryFrom_succ]
  unfold Adjacent
  generalize hd : omega q = d
  fin_cases d <;> simp [directionVector]

/-! ## A structural finite-list splice invariant -/

/-- All vertices of a word, including both endpoints, avoid `B`.  The
recursive formulation makes concatenation proofs independent of absolute
times. -/
def WordAvoids (B : Set Point) : Point → List Direction → Prop
  | a, [] => a ∉ B
  | a, d :: word => a ∉ B ∧ WordAvoids B (Annulus.neighbor a d) word

/-- All vertices of a word, including both endpoints, lie in `D`. -/
def WordWithin (D : Set Point) : Point → List Direction → Prop
  | a, [] => a ∈ D
  | a, d :: word => a ∈ D ∧ WordWithin D (Annulus.neighbor a d) word

/-- A word first meets `B` at its last vertex. -/
def WordFirstHitsAtEnd (B : Set Point) : Point → List Direction → Prop
  | a, [] => a ∈ B
  | a, d :: word => a ∉ B ∧
      WordFirstHitsAtEnd B (Annulus.neighbor a d) word

@[simp] theorem WordAvoids.nil (B : Set Point) (a : Point) :
    WordAvoids B a [] ↔ a ∉ B := by
  rfl

@[simp] theorem WordAvoids.cons (B : Set Point) (a : Point)
    (d : Direction) (word : List Direction) :
    WordAvoids B a (d :: word) ↔
      a ∉ B ∧ WordAvoids B (Annulus.neighbor a d) word := by
  rfl

@[simp] theorem WordWithin.nil (D : Set Point) (a : Point) :
    WordWithin D a [] ↔ a ∈ D := by
  rfl

@[simp] theorem WordWithin.cons (D : Set Point) (a : Point)
    (d : Direction) (word : List Direction) :
    WordWithin D a (d :: word) ↔
      a ∈ D ∧ WordWithin D (Annulus.neighbor a d) word := by
  rfl

@[simp] theorem WordFirstHitsAtEnd.nil (B : Set Point) (a : Point) :
    WordFirstHitsAtEnd B a [] ↔ a ∈ B := by
  rfl

@[simp] theorem WordFirstHitsAtEnd.cons (B : Set Point) (a : Point)
    (d : Direction) (word : List Direction) :
    WordFirstHitsAtEnd B a (d :: word) ↔
      a ∉ B ∧ WordFirstHitsAtEnd B (Annulus.neighbor a d) word := by
  rfl

/-- The endpoint used as the start of the following spliced piece. -/
def wordEndpoint (a : Point) (word : List Direction) : Point :=
  word.foldl Annulus.neighbor a

theorem wordEndpoint_incrementSlice (omega : StepPath)
    {start stop : ℕ} (hstart : start ≤ stop) :
    wordEndpoint (trajectory omega start) (incrementSlice omega start stop) =
      trajectory omega stop := by
  have h := wordPosition_incrementSlice omega hstart
    (show stop - start ≤ stop - start from le_rfl)
  calc
    wordEndpoint (trajectory omega start) (incrementSlice omega start stop) =
        wordPosition (trajectory omega start) (incrementSlice omega start stop)
          (incrementSlice omega start stop).length := by
            exact (wordPosition_length (trajectory omega start)
              (incrementSlice omega start stop)).symm
    _ = trajectory omega stop := by
      simpa [incrementSlice_length, Nat.add_sub_of_le hstart] using h

theorem wordEndpoint_ofFn_stepPrefix (a : Point) (omega : StepPath) (N : ℕ) :
    wordEndpoint a (List.ofFn (stepPrefix N omega)) =
      PlanarPotential.trajectoryFrom a omega N := by
  calc
    wordEndpoint a (List.ofFn (stepPrefix N omega)) =
        wordPosition a (List.ofFn (stepPrefix N omega))
          (List.ofFn (stepPrefix N omega)).length := by
            exact (wordPosition_length a _).symm
    _ = PlanarPotential.trajectoryFrom a omega N := by
      simpa using wordPosition_ofFn_stepPrefix a omega (show N ≤ N from le_rfl)

@[simp] theorem wordEndpoint_nil (a : Point) : wordEndpoint a [] = a := by
  rfl

@[simp] theorem wordEndpoint_cons (a : Point) (d : Direction)
    (word : List Direction) :
    wordEndpoint a (d :: word) =
      wordEndpoint (Annulus.neighbor a d) word := by
  rfl

@[simp] theorem wordEndpoint_append (a : Point)
    (u v : List Direction) :
    wordEndpoint a (u ++ v) = wordEndpoint (wordEndpoint a u) v := by
  simp [wordEndpoint, List.foldl_append]

theorem WordAvoids.append {B : Set Point} {a : Point}
    {u v : List Direction} (hu : WordAvoids B a u)
    (hv : WordAvoids B (wordEndpoint a u) v) :
    WordAvoids B a (u ++ v) := by
  induction u generalizing a with
  | nil => simpa using hv
  | cons d u ih =>
      exact ⟨hu.1, ih hu.2 hv⟩

theorem WordFirstHitsAtEnd.append {B : Set Point} {a : Point}
    {u v : List Direction} (hu : WordAvoids B a u)
    (hv : WordFirstHitsAtEnd B (wordEndpoint a u) v) :
    WordFirstHitsAtEnd B a (u ++ v) := by
  induction u generalizing a with
  | nil => simpa using hv
  | cons d u ih =>
      exact ⟨hu.1, ih hu.2 hv⟩

/-- Containment in a set disjoint from `B` gives boundary avoidance. -/
theorem WordWithin.avoids {B D : Set Point} {a : Point}
    {word : List Direction} (hdisjoint : ∀ y, y ∈ D → y ∉ B)
    (hword : WordWithin D a word) : WordAvoids B a word := by
  induction word generalizing a with
  | nil => exact hdisjoint a hword
  | cons d word ih => exact ⟨hdisjoint a hword.1, ih hword.2⟩

theorem WordWithin.start_mem {D : Set Point} {a : Point}
    {word : List Direction} (hword : WordWithin D a word) : a ∈ D := by
  cases word with
  | nil => exact hword
  | cons d word => exact hword.1

theorem WordWithin.of_forall_wordWalk {D : Set Point} {a : Point}
    {word : List Direction}
    (hword : ∀ t ≤ word.length, wordWalk a word t ∈ D) :
    WordWithin D a word := by
  induction word generalizing a with
  | nil => simpa using hword 0 (by simp)
  | cons d word ih =>
      constructor
      · simpa using hword 0 (by simp)
      · apply ih
        intro t ht
        have h := hword (t + 1) (by simp; omega)
        simpa [wordWalk] using h

/-- Before its first hit of the inner vertex boundary of `D`, a
nearest-neighbour word started in `D` stays in `D`; the boundary endpoint is
inside `D` as well. -/
theorem trajectoryFrom_mem_of_absoluteBoundaryFirstAt_innerBoundary
    {D : Set Point} {a : Point} {omega : StepPath} {N : ℕ}
    (ha : a ∈ D)
    (hfirst : AbsoluteBoundaryFirstAt (innerBoundary D) a omega N) :
    ∀ q ≤ N, PlanarPotential.trajectoryFrom a omega q ∈ D := by
  intro q hq
  induction q with
  | zero =>
      rw [PlanarPotential.trajectoryFrom_zero]
      exact ha
  | succ q ih =>
      have hqN : q < N := by omega
      have hcurrent : PlanarPotential.trajectoryFrom a omega q ∈ D :=
        ih hqN.le
      by_contra hnext
      exact hfirst.2 q hqN
        ⟨hcurrent, PlanarPotential.trajectoryFrom a omega (q + 1), hnext,
          adjacent_trajectoryFrom_succ a omega q⟩

/-- List form of the preceding inner-boundary fact. -/
theorem wordWithin_of_absoluteBoundaryFirstAt_innerBoundary
    {D : Set Point} {a : Point} {omega : StepPath} {N : ℕ}
    (ha : a ∈ D)
    (hfirst : AbsoluteBoundaryFirstAt (innerBoundary D) a omega N) :
    WordWithin D a (List.ofFn (stepPrefix N omega)) := by
  apply WordWithin.of_forall_wordWalk
  intro q hq
  have hqN : q ≤ N := by simpa using hq
  rw [wordWalk, wordPosition_ofFn_stepPrefix a omega hqN]
  exact trajectoryFrom_mem_of_absoluteBoundaryFirstAt_innerBoundary
    ha hfirst q hqN

/-- Every canonical first-boundary code is a word staying in the domain and
ending at its recorded endpoint. -/
theorem boundaryExitWordCode_wordWithin_and_endpoint
    {D : Set Point} {a endpoint : Point} (ha : a ∈ D)
    (bridge : BoundaryExitWordCode (innerBoundary D) a endpoint) :
    WordWithin D a (List.ofFn bridge.1.2) ∧
      wordEndpoint a (List.ofFn bridge.1.2) = endpoint := by
  constructor
  · have h := wordWithin_of_absoluteBoundaryFirstAt_innerBoundary ha bridge.2.1
    simpa using h
  · calc
      wordEndpoint a (List.ofFn bridge.1.2) =
          wordEndpoint a
            (List.ofFn (stepPrefix bridge.1.1 (extendStoppedWord bridge.1))) := by
              rw [stepPrefix_extendStoppedWord]
      _ = PlanarPotential.trajectoryFrom a (extendStoppedWord bridge.1)
          bridge.1.1 := wordEndpoint_ofFn_stepPrefix _ _ _
      _ = endpoint := bridge.2.2

/-- Endpoint-only projection, kept separate so callers need not elaborate
the substantially larger domain-containment certificate. -/
theorem boundaryExitWordCode_wordEndpoint
    {boundary : Set Point} {a endpoint : Point}
    (bridge : BoundaryExitWordCode boundary a endpoint) :
    wordEndpoint a (List.ofFn bridge.1.2) = endpoint := by
  calc
    wordEndpoint a (List.ofFn bridge.1.2) =
        wordEndpoint a
          (List.ofFn (stepPrefix bridge.1.1 (extendStoppedWord bridge.1))) := by
            rw [stepPrefix_extendStoppedWord]
    _ = PlanarPotential.trajectoryFrom a (extendStoppedWord bridge.1)
        bridge.1.1 := wordEndpoint_ofFn_stepPrefix _ _ _
    _ = endpoint := bridge.2.2

/-- Canonical terminal inner-to-outer first-hit words stay in the terminal
disc and end at the endpoint recorded by their code. -/
theorem terminalBoundaryExitWordCode_wordWithin_and_endpoint
    {n : ℕ} {x a endpoint : Point}
    (ha : a ∈ disc x (scaleRadius n n))
    (bridge : BoundaryExitWordCode (terminalOuterBoundary n x) a endpoint) :
    WordWithin (disc x (scaleRadius n n)) a (List.ofFn bridge.1.2) ∧
      wordEndpoint a (List.ofFn bridge.1.2) = endpoint := by
  simpa [terminalOuterBoundary, discBoundary] using
    (boundaryExitWordCode_wordWithin_and_endpoint ha bridge)

/-- Variant whose start is only known to lie in the smaller terminal inner
disc, as supplied by an extracted terminal entrance mark. -/
theorem terminalBoundaryExitWordCode_wordWithin_and_endpoint_of_innerDisc
    {n : ℕ} {x a endpoint : Point} (hn : 1 ≤ n)
    (ha : a ∈ disc x (scaleRadius n (n + 1)))
    (bridge : BoundaryExitWordCode (terminalOuterBoundary n x) a endpoint) :
    WordWithin (disc x (scaleRadius n n)) a (List.ofFn bridge.1.2) ∧
      wordEndpoint a (List.ofFn bridge.1.2) = endpoint := by
  apply terminalBoundaryExitWordCode_wordWithin_and_endpoint
  exact ha.trans (terminalRadius_le_regularRadius_self n hn)

/-- Containment-only projection for an extracted terminal entrance. -/
theorem terminalBoundaryExitWordCode_wordWithin_of_innerDisc
    {n : ℕ} {x a endpoint : Point} (hn : 1 ≤ n)
    (ha : a ∈ disc x (scaleRadius n (n + 1)))
    (bridge : BoundaryExitWordCode (terminalOuterBoundary n x) a endpoint) :
    WordWithin (disc x (scaleRadius n n)) a (List.ofFn bridge.1.2) :=
  (terminalBoundaryExitWordCode_wordWithin_and_endpoint_of_innerDisc
    hn ha bridge).1

theorem WordAvoids.of_forall_wordWalk {B : Set Point} {a : Point}
    {word : List Direction}
    (hword : ∀ t ≤ word.length, wordWalk a word t ∉ B) :
    WordAvoids B a word := by
  induction word generalizing a with
  | nil => simpa using hword 0 (by simp)
  | cons d word ih =>
      constructor
      · simpa using hword 0 (by simp)
      · apply ih
        intro t ht
        have h := hword (t + 1) (by simp; omega)
        simpa [wordWalk] using h

theorem WordFirstHitsAtEnd.of_isFirstHit
    {B : Set Point} {a : Point} {word : List Direction}
    (hend : wordWalk a word word.length ∈ B)
    (hbefore : ∀ t < word.length, wordWalk a word t ∉ B) :
    WordFirstHitsAtEnd B a word := by
  induction word generalizing a with
  | nil => simpa using hend
  | cons d word ih =>
      constructor
      · simpa using hbefore 0 (by simp)
      · apply ih
        · simpa [wordWalk] using hend
        · intro t ht
          have h := hbefore (t + 1) (by simp; omega)
          simpa [wordWalk] using h

/-- The local hypotheses for an alternating splice.  Every retained piece
before the last avoids the global boundary, every replacement word stays in
the terminal disc, and the last retained piece first hits the global
boundary at its end. -/
def AlternatingTerminalSpliceSafe (B D : Set Point) :
    (m : ℕ) → Point → (Fin (m + 1) → List Direction) →
      TerminalSegmentWords m → Prop
  | 0, a, pieces, _words => WordFirstHitsAtEnd B a (pieces 0)
  | m + 1, a, pieces, words =>
      WordAvoids B a (pieces 0) ∧
      WordWithin D (wordEndpoint a (pieces 0)) (words 0) ∧
      AlternatingTerminalSpliceSafe B D m
        (wordEndpoint (wordEndpoint a (pieces 0)) (words 0))
        (fun j ↦ pieces j.succ) (fun j ↦ words j.succ)

/-- The retained pieces cut from an original first-hit word, together with
arbitrary endpoint-matched replacement words inside `D`, satisfy the
structural alternating-splice invariant. -/
theorem alternatingTerminalSpliceSafe_complementaryPieces :
    ∀ (m : ℕ) (omega : StepPath) (base horizon : ℕ)
      (entrance exit : Fin m → ℕ) (B D : Set Point)
      (words : TerminalSegmentWords m),
      base ≤ horizon →
      OrderedIntervals base horizon entrance exit →
      trajectory omega horizon ∈ B →
      (∀ k < horizon, trajectory omega k ∉ B) →
      (∀ y, y ∈ D → y ∉ B) →
      (∀ j, WordWithin D (trajectory omega (entrance j)) (words j)) →
      (∀ j, wordEndpoint (trajectory omega (entrance j)) (words j) =
        trajectory omega (exit j)) →
      AlternatingTerminalSpliceSafe B D m (trajectory omega base)
        (complementaryPieces m omega base horizon entrance exit) words := by
  intro m
  induction m with
  | zero =>
      intro omega base horizon entrance exit B D words hbase _hordered
        hend hbefore _hdisjoint _hwithin _hwordEnd
      simp only [complementaryPieces, AlternatingTerminalSpliceSafe]
      apply WordFirstHitsAtEnd.of_isFirstHit
      · rw [wordWalk_length]
        change wordEndpoint (trajectory omega base)
          (incrementSlice omega base horizon) ∈ B
        rw [wordEndpoint_incrementSlice omega hbase]
        exact hend
      · intro q hq
        have hq' : q ≤ horizon - base := by
          simpa [incrementSlice_length] using hq.le
        rw [wordWalk, wordPosition_incrementSlice omega hbase hq']
        apply hbefore
        simp only [incrementSlice_length] at hq
        omega
  | succ m ih =>
      intro omega base horizon entrance exit B D words hbase hordered
        hend hbefore hdisjoint hwithin hwordEnd
      have hzero := hordered.1 (0 : Fin (m + 1))
      have hentranceNotBoundary : trajectory omega (entrance 0) ∉ B :=
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
          simpa [incrementSlice_length] using hq
        rw [wordWalk, wordPosition_incrementSlice omega hzero.1 hq']
        apply hbefore
        omega
      · rw [wordEndpoint_incrementSlice omega hzero.1]
        exact hwithin 0
      · rw [wordEndpoint_incrementSlice omega hzero.1, hwordEnd 0]
        exact ih omega (exit 0) horizon
          (fun j ↦ entrance j.succ) (fun j ↦ exit j.succ) B D
          (fun j ↦ words j.succ) hzero.2.2 htail hend hbefore hdisjoint
          (fun j ↦ hwithin j.succ) (fun j ↦ hwordEnd j.succ)

/-- Timed-skeleton wrapper.  The point fields are kept explicit because an
arbitrary `TimedTerminalSkeleton` does not definitionally assert that they
are the trajectory at its clock fields. -/
theorem alternatingTerminalSpliceSafe_complementaryPieces_timed
    {m n : ℕ} {omega : StepPath} {x : Point}
    {t : TimedTerminalSkeleton m} {words : TerminalSegmentWords m}
    (hn : 1 ≤ n) (hx : x ∈ candidateBox n)
    (ht : t.WellFormed)
    (hexit : IsOuterExitTime (trajectory omega) n t.horizon)
    (hentrancePoint : ∀ j,
      t.entrancePoint j = trajectory omega (t.entrance j))
    (hexitPoint : ∀ j, t.exitPoint j = trajectory omega (t.exit j))
    (hwithin : ∀ j,
      WordWithin (disc x (scaleRadius n n)) (t.entrancePoint j) (words j))
    (hwordEnd : ∀ j,
      wordEndpoint (t.entrancePoint j) (words j) = t.exitPoint j) :
    AlternatingTerminalSpliceSafe
      (discBoundary (0, 0) (outerScale n))
      (disc x (scaleRadius n n)) m (trajectory omega 0)
      (complementaryPieces m omega 0 t.horizon t.entrance t.exit) words := by
  apply alternatingTerminalSpliceSafe_complementaryPieces m omega 0 t.horizon
    t.entrance t.exit (discBoundary (0, 0) (outerScale n))
    (disc x (scaleRadius n n)) words (Nat.zero_le _) (orderedIntervals_of_wellFormed ht)
    hexit.1 hexit.2 (fun y hy ↦ terminalDisc_disjoint_globalBoundary hn hx hy)
  · intro j
    rw [← hentrancePoint j]
    exact hwithin j
  · intro j
    rw [← hentrancePoint j, ← hexitPoint j]
    exact hwordEnd j

/-- Structural finite-list splice theorem.  Durations are absent: only
endpoints and the alternating list structure matter. -/
theorem WordFirstHitsAtEnd.alternatingConcat_of_terminalSpliceSafe :
    ∀ {m : ℕ} {B D : Set Point} {a : Point}
      {pieces : Fin (m + 1) → List Direction}
      {words : TerminalSegmentWords m},
      (∀ y, y ∈ D → y ∉ B) →
      AlternatingTerminalSpliceSafe B D m a pieces words →
      WordFirstHitsAtEnd B a (alternatingConcat m pieces words) := by
  intro m
  induction m with
  | zero =>
      intro B D a pieces words hdisjoint hsafe
      exact hsafe
  | succ m ih =>
      intro B D a pieces words hdisjoint hsafe
      simp only [alternatingConcat]
      apply WordFirstHitsAtEnd.append
        (WordAvoids.append hsafe.1 (hsafe.2.1.avoids hdisjoint))
      simpa using ih hdisjoint hsafe.2.2

theorem WordFirstHitsAtEnd.endpoint_mem {B : Set Point} {a : Point}
    {word : List Direction} (h : WordFirstHitsAtEnd B a word) :
    wordEndpoint a word ∈ B := by
  induction word generalizing a with
  | nil => exact h
  | cons d word ih => exact ih h.2

theorem WordFirstHitsAtEnd.before_endpoint_not_mem
    {B : Set Point} {a : Point} {word : List Direction}
    (h : WordFirstHitsAtEnd B a word) :
    ∀ t < word.length, wordWalk a word t ∉ B := by
  induction word generalizing a with
  | nil => simp
  | cons d word ih =>
      intro t ht
      cases t with
      | zero => simpa using h.1
      | succ t =>
          have ht' : t < word.length := by simpa using ht
          simpa [wordWalk, wordPosition] using ih h.2 t ht'

/-- Semantic form of the structural first-hit predicate. -/
theorem WordFirstHitsAtEnd.isFirstHit
    {B : Set Point} {a : Point} {word : List Direction}
    (h : WordFirstHitsAtEnd B a word) :
    wordWalk a word word.length ∈ B ∧
      ∀ t < word.length, wordWalk a word t ∉ B := by
  exact ⟨by simpa [wordWalk, wordEndpoint] using h.endpoint_mem,
    h.before_endpoint_not_mem⟩

/-- Geometry-specialized alternating-splice theorem.  It is the direct
finite-list statement: terminal replacement words whose vertices stay in
the terminal disc preserve the first global outer exit. -/
theorem isOuterExitTime_alternatingConcat_of_terminalSpliceSafe
    {n m : ℕ} {x a : Point}
    {pieces : Fin (m + 1) → List Direction}
    {words : TerminalSegmentWords m}
    (hn : 1 ≤ n) (hx : x ∈ candidateBox n)
    (hsafe : AlternatingTerminalSpliceSafe
      (discBoundary (0, 0) (outerScale n))
      (disc x (scaleRadius n n)) m a pieces words) :
    IsOuterExitTime (wordWalk a (alternatingConcat m pieces words)) n
      (alternatingConcat m pieces words).length := by
  have hfirst := WordFirstHitsAtEnd.alternatingConcat_of_terminalSpliceSafe
    (fun y hy ↦ terminalDisc_disjoint_globalBoundary hn hx hy) hsafe
  exact hfirst.isFirstHit

/-- The concrete finite-list global-exit invariant requested by terminal
skeleton reconstruction.  Replacement durations may be arbitrary. -/
theorem isOuterExitTime_alternatingConcat_complementaryPieces_timed
    {m n : ℕ} {omega : StepPath} {x : Point}
    {t : TimedTerminalSkeleton m} {words : TerminalSegmentWords m}
    (hn : 1 ≤ n) (hx : x ∈ candidateBox n)
    (ht : t.WellFormed)
    (hexit : IsOuterExitTime (trajectory omega) n t.horizon)
    (hentrancePoint : ∀ j,
      t.entrancePoint j = trajectory omega (t.entrance j))
    (hexitPoint : ∀ j, t.exitPoint j = trajectory omega (t.exit j))
    (hwithin : ∀ j,
      WordWithin (disc x (scaleRadius n n)) (t.entrancePoint j) (words j))
    (hwordEnd : ∀ j,
      wordEndpoint (t.entrancePoint j) (words j) = t.exitPoint j) :
    IsOuterExitTime
      (wordWalk (trajectory omega 0)
        (alternatingConcat m
          (complementaryPieces m omega 0 t.horizon t.entrance t.exit) words)) n
      (alternatingConcat m
        (complementaryPieces m omega 0 t.horizon t.entrance t.exit) words).length := by
  apply isOuterExitTime_alternatingConcat_of_terminalSpliceSafe hn hx
  exact alternatingTerminalSpliceSafe_complementaryPieces_timed
    hn hx ht hexit hentrancePoint hexitPoint hwithin hwordEnd

/-- High-level adapter for the literal canonical terminal bridge family.
All subtype and finite-word bookkeeping is discharged here, so downstream
invariance proofs need only provide the extracted inner-boundary marks. -/
theorem isOuterExitTime_alternatingConcat_canonicalTerminalBridges_timed
    {m n : ℕ} {omega : StepPath} {x : Point}
    {t : TimedTerminalSkeleton m}
    (hn : 1 ≤ n) (hx : x ∈ candidateBox n)
    (ht : t.WellFormed)
    (hexit : IsOuterExitTime (trajectory omega) n t.horizon)
    (hentrancePoint : ∀ j,
      t.entrancePoint j = trajectory omega (t.entrance j))
    (hexitPoint : ∀ j, t.exitPoint j = trajectory omega (t.exit j))
    (hinner : ∀ j, t.entrancePoint j ∈ terminalInnerBoundary n x)
    (bridges : (j : Fin m) → BoundaryExitWordCode
      (terminalOuterBoundary n x) (t.entrancePoint j) (t.exitPoint j)) :
    IsOuterExitTime
      (wordWalk (trajectory omega 0)
        (alternatingConcat m
          (complementaryPieces m omega 0 t.horizon t.entrance t.exit)
          (fun j ↦ List.ofFn (bridges j).1.2))) n
      (alternatingConcat m
        (complementaryPieces m omega 0 t.horizon t.entrance t.exit)
        (fun j ↦ List.ofFn (bridges j).1.2)).length := by
  apply isOuterExitTime_alternatingConcat_complementaryPieces_timed
    hn hx ht hexit hentrancePoint hexitPoint
  · intro j
    exact terminalBoundaryExitWordCode_wordWithin_of_innerDisc
      hn (hinner j).1 (bridges j)
  · intro j
    exact boundaryExitWordCode_wordEndpoint (bridges j)

/-- Transported endpoint-family version.  The bridge subtype is indexed by
explicit endpoint functions, so callers do not ask elaboration to unfold a
compressed code while unifying dependent subtypes. -/
theorem isOuterExitTime_alternatingConcat_canonicalTerminalBridges_timed_of_endpoint_eq
    {m n : ℕ} {omega : StepPath} {x : Point}
    {t : TimedTerminalSkeleton m}
    {entrancePoints exitPoints : Fin m → Point}
    (hn : 1 ≤ n) (hx : x ∈ candidateBox n)
    (ht : t.WellFormed)
    (hexit : IsOuterExitTime (trajectory omega) n t.horizon)
    (hentrancePoint : ∀ j,
      t.entrancePoint j = trajectory omega (t.entrance j))
    (hexitPoint : ∀ j, t.exitPoint j = trajectory omega (t.exit j))
    (hinner : ∀ j, t.entrancePoint j ∈ terminalInnerBoundary n x)
    (hentranceEq : entrancePoints = t.entrancePoint)
    (hexitEq : exitPoints = t.exitPoint)
    (bridges : (j : Fin m) → BoundaryExitWordCode
      (terminalOuterBoundary n x) (entrancePoints j) (exitPoints j)) :
    IsOuterExitTime
      (wordWalk (trajectory omega 0)
        (alternatingConcat m
          (complementaryPieces m omega 0 t.horizon t.entrance t.exit)
          (fun j ↦ List.ofFn (bridges j).1.2))) n
      (alternatingConcat m
        (complementaryPieces m omega 0 t.horizon t.entrance t.exit)
        (fun j ↦ List.ofFn (bridges j).1.2)).length := by
  subst entrancePoints
  subst exitPoints
  exact isOuterExitTime_alternatingConcat_canonicalTerminalBridges_timed
    hn hx ht hexit hentrancePoint hexitPoint hinner bridges

theorem extractTimedTerminalSkeleton_entrancePoint_eq
    (n horizon : ℕ) (profileDelta : ℝ) (x : Point) (omega : StepPath) :
    ∀ j, (extractTimedTerminalSkeleton n horizon profileDelta x omega).entrancePoint j =
      trajectory omega
        ((extractTimedTerminalSkeleton n horizon profileDelta x omega).entrance j) := by
  intro j
  rfl

theorem extractTimedTerminalSkeleton_exitPoint_eq
    (n horizon : ℕ) (profileDelta : ℝ) (x : Point) (omega : StepPath) :
    ∀ j, (extractTimedTerminalSkeleton n horizon profileDelta x omega).exitPoint j =
      trajectory omega
        ((extractTimedTerminalSkeleton n horizon profileDelta x omega).exit j) := by
  intro j
  rfl

theorem extractTerminalSkeletonCode_entrancePoints_eq
    (n horizon : ℕ) (profileDelta : ℝ) (x : Point) (omega : StepPath) :
    (extractTerminalSkeletonCode n horizon profileDelta x omega).2.1 =
      (extractTimedTerminalSkeleton n horizon profileDelta x omega).entrancePoint := by
  rfl

theorem extractTerminalSkeletonCode_exitPoints_eq
    (n horizon : ℕ) (profileDelta : ℝ) (x : Point) (omega : StepPath) :
    (extractTerminalSkeletonCode n horizon profileDelta x omega).2.2 =
      (extractTimedTerminalSkeleton n horizon profileDelta x omega).exitPoint := by
  rfl

theorem extractTimedTerminalSkeleton_all_entrances_inner
    {n horizon : ℕ} {profileDelta : ℝ} {omega : StepPath} {x : Point}
    (hn : 1 ≤ n)
    (hexit : IsOuterExitTime (trajectory omega) n horizon)
    (hx : SuccessfulPoint (trajectory omega) n horizon profileDelta x) :
    ∀ j, (extractTimedTerminalSkeleton n horizon profileDelta x omega).entrancePoint j ∈
      terminalInnerBoundary n x := by
  intro j
  exact extractTerminalSkeletonCode_entrance_mem hn hexit hx j

/-- Canonical bridge insertion with the endpoint indices exposed in their
compressed-code form.  This declaration isolates the dependent-subtype
transport from the final reconstructed-packet rewrite. -/
theorem isOuterExitTime_alternatingConcat_canonical_of_stopped_success
    {n horizon : ℕ} {profileDelta : ℝ} {omega : StepPath} {x : Point}
    (hn : 1 ≤ n)
    (hexit : IsOuterExitTime (trajectory omega) n horizon)
    (hx : SuccessfulPoint (trajectory omega) n horizon profileDelta x)
    (bridges : (j : Fin
      (AppendixLocalTime.requiredTerminalCount n profileDelta)) →
      BoundaryExitWordCode (terminalOuterBoundary n x)
        ((extractTerminalSkeletonCode n horizon profileDelta x omega).2.1 j)
        ((extractTerminalSkeletonCode n horizon profileDelta x omega).2.2 j)) :
    IsOuterExitTime
      (wordWalk (trajectory omega 0)
        (alternatingConcat
          (AppendixLocalTime.requiredTerminalCount n profileDelta)
          (complementaryPieces
            (AppendixLocalTime.requiredTerminalCount n profileDelta) omega 0 horizon
            (extractTimedTerminalSkeleton n horizon profileDelta x omega).entrance
            (extractTimedTerminalSkeleton n horizon profileDelta x omega).exit)
          (fun j ↦ List.ofFn (bridges j).1.2))) n
      (alternatingConcat
        (AppendixLocalTime.requiredTerminalCount n profileDelta)
        (complementaryPieces
          (AppendixLocalTime.requiredTerminalCount n profileDelta) omega 0 horizon
          (extractTimedTerminalSkeleton n horizon profileDelta x omega).entrance
          (extractTimedTerminalSkeleton n horizon profileDelta x omega).exit)
        (fun j ↦ List.ofFn (bridges j).1.2)).length := by
  exact isOuterExitTime_alternatingConcat_canonicalTerminalBridges_timed_of_endpoint_eq
    hn hx.1
    (extractTimedTerminalSkeleton_wellFormed_of_stopped_success hn hexit hx)
    hexit
    (extractTimedTerminalSkeleton_entrancePoint_eq n horizon profileDelta x omega)
    (extractTimedTerminalSkeleton_exitPoint_eq n horizon profileDelta x omega)
    (extractTimedTerminalSkeleton_all_entrances_inner hn hexit hx)
    (entrancePoints :=
      (extractTerminalSkeletonCode n horizon profileDelta x omega).2.1)
    (exitPoints :=
      (extractTerminalSkeletonCode n horizon profileDelta x omega).2.2)
    (extractTerminalSkeletonCode_entrancePoints_eq n horizon profileDelta x omega)
    (extractTerminalSkeletonCode_exitPoints_eq n horizon profileDelta x omega)
    bridges

/-- Compression exposes exactly the complementary pieces of the timed
skeleton; the inserted words are unchanged. -/
theorem reconstructTerminalPacket_extractTerminalSkeletonCode
    (n horizon : ℕ) (profileDelta : ℝ) (x : Point) (omega : StepPath)
    (words : TerminalSegmentWords
      (AppendixLocalTime.requiredTerminalCount n profileDelta)) :
    reconstructTerminalPacket
      (extractTerminalSkeletonCode n horizon profileDelta x omega, words) =
      alternatingConcat
        (AppendixLocalTime.requiredTerminalCount n profileDelta)
        (complementaryPieces
          (AppendixLocalTime.requiredTerminalCount n profileDelta) omega 0 horizon
          (extractTimedTerminalSkeleton n horizon profileDelta x omega).entrance
          (extractTimedTerminalSkeleton n horizon profileDelta x omega).exit)
        words := by
  rfl

/-- Exact extracted-code adapter used by compressed-skeleton invariance.
The original stopped successful path supplies the retained pieces; any
canonical endpoint-indexed first-hit bridge family may be reinserted. -/
theorem isOuterExitTime_reconstructTerminalPacket_canonical_of_stopped_success
    {n horizon : ℕ} {profileDelta : ℝ} {omega : StepPath} {x : Point}
    (hn : 1 ≤ n)
    (hexit : IsOuterExitTime (trajectory omega) n horizon)
    (hx : SuccessfulPoint (trajectory omega) n horizon profileDelta x)
    (bridges : (j : Fin
      (AppendixLocalTime.requiredTerminalCount n profileDelta)) →
      BoundaryExitWordCode (terminalOuterBoundary n x)
        ((extractTerminalSkeletonCode n horizon profileDelta x omega).2.1 j)
        ((extractTerminalSkeletonCode n horizon profileDelta x omega).2.2 j)) :
    IsOuterExitTime
      (wordWalk (0, 0)
        (reconstructTerminalPacket
          (extractTerminalSkeletonCode n horizon profileDelta x omega,
            fun j ↦ List.ofFn (bridges j).1.2))) n
      (reconstructTerminalPacket
        (extractTerminalSkeletonCode n horizon profileDelta x omega,
          fun j ↦ List.ofFn (bridges j).1.2)).length := by
  have h := isOuterExitTime_alternatingConcat_canonical_of_stopped_success
    hn hexit hx bridges
  rw [reconstructTerminalPacket_extractTerminalSkeletonCode] at ⊢
  simpa only [trajectory_zero] using h

/-! ## First global-boundary hit after splicing -/

/-- A finite reconstructed word preserves the global first exit whenever
its endpoint is the original global-boundary endpoint and every earlier
vertex is either an earlier vertex of the original stopped prefix or lies in
the candidate-centred terminal disc.

This is the exact dichotomy supplied by a finite-list splice: retained
pieces give the left disjunct, while intermediate vertices of replacement
inner-to-outer first-hit words give the right disjunct. -/
theorem isOuterExitTime_wordWalk_of_retained_or_terminal
    {s : WalkPath} {n horizon : ℕ} {x a : Point}
    {word : List Direction}
    (hn : 1 ≤ n) (hx : x ∈ candidateBox n)
    (hexit : IsOuterExitTime s n horizon)
    (hend : wordWalk a word word.length = s horizon)
    (hvertices : ∀ t < word.length,
      (∃ k < horizon, wordWalk a word t = s k) ∨
        wordWalk a word t ∈ disc x (scaleRadius n n)) :
    IsOuterExitTime (wordWalk a word) n word.length := by
  constructor
  · simpa [hend] using hexit.1
  · intro t ht
    rcases hvertices t ht with hretained | hterminal
    · obtain ⟨k, hk, hpos⟩ := hretained
      rw [hpos]
      exact hexit.2 k hk
    · exact terminalDisc_disjoint_globalBoundary hn hx hterminal

/-- Origin-based form, matching reconstructed increment prefixes of the
canonical planar walk. -/
theorem isOuterExitTime_wordWalk_zero_of_retained_or_terminal
    {s : WalkPath} {n horizon : ℕ} {x : Point}
    {word : List Direction}
    (hn : 1 ≤ n) (hx : x ∈ candidateBox n)
    (hexit : IsOuterExitTime s n horizon)
    (hend : wordWalk (0, 0) word word.length = s horizon)
    (hvertices : ∀ t < word.length,
      (∃ k < horizon, wordWalk (0, 0) word t = s k) ∨
        wordWalk (0, 0) word t ∈ disc x (scaleRadius n n)) :
    IsOuterExitTime (wordWalk (0, 0) word) n word.length := by
  exact isOuterExitTime_wordWalk_of_retained_or_terminal
    hn hx hexit hend hvertices

/-- Direct wrapper for the alternating retained/replacement word used by a
terminal skeleton packet.  It deliberately asks only for the splice-cover
dichotomy; endpoint matching and the first-hit property of each replacement
word are precisely what establish that dichotomy in the skeleton-invariance
argument. -/
theorem isOuterExitTime_alternatingConcat_of_retained_or_terminal
    {s : WalkPath} {n horizon m : ℕ} {x a : Point}
    {pieces : Fin (m + 1) → List Direction}
    {words : TerminalSegmentWords m}
    (hn : 1 ≤ n) (hx : x ∈ candidateBox n)
    (hexit : IsOuterExitTime s n horizon)
    (hend : wordWalk a (alternatingConcat m pieces words)
        (alternatingConcat m pieces words).length = s horizon)
    (hvertices : ∀ t < (alternatingConcat m pieces words).length,
      (∃ k < horizon,
        wordWalk a (alternatingConcat m pieces words) t = s k) ∨
      wordWalk a (alternatingConcat m pieces words) t ∈
        disc x (scaleRadius n n)) :
    IsOuterExitTime (wordWalk a (alternatingConcat m pieces words)) n
      (alternatingConcat m pieces words).length := by
  exact isOuterExitTime_wordWalk_of_retained_or_terminal
    hn hx hexit hend hvertices

/-- Packet-level form of the same finite-splice invariant. -/
theorem isOuterExitTime_reconstructTerminalPacket_of_retained_or_terminal
    {s : WalkPath} {n horizon m : ℕ} {x a : Point}
    {packet : TerminalSkeletonPacket m}
    (hn : 1 ≤ n) (hx : x ∈ candidateBox n)
    (hexit : IsOuterExitTime s n horizon)
    (hend : wordWalk a (reconstructTerminalPacket packet)
        (reconstructTerminalPacket packet).length = s horizon)
    (hvertices : ∀ t < (reconstructTerminalPacket packet).length,
      (∃ k < horizon,
        wordWalk a (reconstructTerminalPacket packet) t = s k) ∨
      wordWalk a (reconstructTerminalPacket packet) t ∈
        disc x (scaleRadius n n)) :
    IsOuterExitTime (wordWalk a (reconstructTerminalPacket packet)) n
      (reconstructTerminalPacket packet).length := by
  exact isOuterExitTime_wordWalk_of_retained_or_terminal
    hn hx hexit hend hvertices

end

end Erdos1165.TerminalGlobalExitSplice
