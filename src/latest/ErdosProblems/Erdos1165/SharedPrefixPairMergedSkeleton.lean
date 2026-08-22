/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import ErdosProblems.Erdos1165.SharedPrefixPairClockAlignment
import ErdosProblems.Erdos1165.SharedPrefixPairFactorization
import ErdosProblems.Erdos1165.TerminalSkeletonFactorization

/-!
# A single chronological skeleton for two separated terminal families

The terminal clocks at two separated points are individually ordered, and
`SharedPrefixPairClockAlignment` proves that every left interval is disjoint
from every right interval.  This file sorts their disjoint union by the
lexicographic key `(entrance, exit, logical coordinate)`.  The resulting
`TimedTerminalSkeleton (m + m)` has one complementary word and reconstructs
the original stopped prefix exactly.

The sorting permutation is kept explicit.  Its range uses chronological
coordinates, while its values use the logical convention “all left
coordinates, then all right coordinates”.  Thus bridge tuples can remain
logically split even though reconstruction inserts their words in temporal
order.
-/

open Set

namespace Erdos1165.SharedPrefixPairMergedSkeleton

open AppendixPair Hitting MarkedBridgeFactorization SharedPrefixPairClockAlignment
open SharedPrefixPairExtraction SharedPrefixPairFactorization
open AlternatingConcatPrefixFree TerminalSequentialVisitLaw
open TerminalExcursionPathwise
open TerminalSkeletonFactorization TerminalSkeletonInvariance
open TerminalSkeletonWords ThickPoint

noncomputable section

/-! ## Logical left-then-right coordinates -/

/-- Select a value from the left or right branch at a logical coordinate.
Logical coordinates are left first and right second. -/
def pairValue {mLeft mRight : ℕ} {A : Type*}
    (left : Fin mLeft → A) (right : Fin mRight → A) :
    Fin (mLeft + mRight) → A :=
  Fin.addCases left right

@[simp] theorem pairValue_castAdd {mLeft mRight : ℕ} {A : Type*}
    (left : Fin mLeft → A) (right : Fin mRight → A) (i : Fin mLeft) :
    pairValue left right (Fin.castAdd mRight i) = left i := by
  simp [pairValue]

@[simp] theorem pairValue_natAdd {mLeft mRight : ℕ} {A : Type*}
    (left : Fin mLeft → A) (right : Fin mRight → A) (j : Fin mRight) :
    pairValue left right (Fin.natAdd mLeft j) = right j := by
  simp [pairValue]

/-- Logical entrance times of two timed families. -/
def pairEntrance {mLeft mRight : ℕ}
    (left : TimedTerminalSkeleton mLeft)
    (right : TimedTerminalSkeleton mRight) :
    Fin (mLeft + mRight) → ℕ :=
  pairValue left.entrance right.entrance

/-- Logical exit times of two timed families. -/
def pairExit {mLeft mRight : ℕ}
    (left : TimedTerminalSkeleton mLeft)
    (right : TimedTerminalSkeleton mRight) :
    Fin (mLeft + mRight) → ℕ :=
  pairValue left.exit right.exit

/-- Logical entrance points of two timed families. -/
def pairEntrancePoint {mLeft mRight : ℕ}
    (left : TimedTerminalSkeleton mLeft)
    (right : TimedTerminalSkeleton mRight) :
    Fin (mLeft + mRight) → Point :=
  pairValue left.entrancePoint right.entrancePoint

/-- Logical exit points of two timed families. -/
def pairExitPoint {mLeft mRight : ℕ}
    (left : TimedTerminalSkeleton mLeft)
    (right : TimedTerminalSkeleton mRight) :
    Fin (mLeft + mRight) → Point :=
  pairValue left.exitPoint right.exitPoint

/-! ## Chronological sorting -/

/-- The total sorting key.  Exit time resolves simultaneous entrances; the
logical coordinate is the final tie breaker and makes the key injective. -/
def chronologicalKey {mLeft mRight : ℕ}
    (left : TimedTerminalSkeleton mLeft)
    (right : TimedTerminalSkeleton mRight)
    (q : Fin (mLeft + mRight)) : ℕ ×ₗ (ℕ ×ₗ ℕ) :=
  toLex (pairEntrance left right q,
    toLex (pairExit left right q, (q : ℕ)))

theorem chronologicalKey_injective {mLeft mRight : ℕ}
    (left : TimedTerminalSkeleton mLeft)
    (right : TimedTerminalSkeleton mRight) :
    Function.Injective (chronologicalKey left right) := by
  intro a b hab
  have hval : (a : ℕ) = (b : ℕ) := by
    exact congrArg (fun z : ℕ ×ₗ (ℕ ×ₗ ℕ) ↦ ((ofLex (ofLex z).2).2)) hab
  exact Fin.ext hval

/-- The chronological order pulled back from the injective sorting key. -/
@[instance_reducible] def chronologicalLinearOrder {mLeft mRight : ℕ}
    (left : TimedTerminalSkeleton mLeft)
    (right : TimedTerminalSkeleton mRight) :
    LinearOrder (ULift.{0, 0} (Fin (mLeft + mRight))) :=
  LinearOrder.lift' (fun q ↦ chronologicalKey left right q.down)
    ((chronologicalKey_injective left right).comp Equiv.ulift.injective)

/-- At chronological position `k`, return the corresponding logical
left-then-right coordinate. -/
def chronologicalEquiv {mLeft mRight : ℕ}
    (left : TimedTerminalSkeleton mLeft)
    (right : TimedTerminalSkeleton mRight) :
    Fin (mLeft + mRight) ≃ Fin (mLeft + mRight) := by
  letI := chronologicalLinearOrder left right
  exact (Fintype.orderIsoFinOfCardEq
    (ULift.{0, 0} (Fin (mLeft + mRight))) (k := mLeft + mRight)
      (by simp)).toEquiv.trans Equiv.ulift

/-- Sorting is strictly increasing for the chronological key. -/
theorem chronologicalKey_strictMono {mLeft mRight : ℕ}
    (left : TimedTerminalSkeleton mLeft)
    (right : TimedTerminalSkeleton mRight)
    {i j : Fin (mLeft + mRight)} (hij : (i : ℕ) < j) :
    chronologicalKey left right (chronologicalEquiv left right i) <
      chronologicalKey left right (chronologicalEquiv left right j) := by
  letI := chronologicalLinearOrder left right
  let e := Fintype.orderIsoFinOfCardEq
    (ULift.{0, 0} (Fin (mLeft + mRight))) (k := mLeft + mRight) (by simp)
  have hijFin : i < j := by
    exact hij
  have hle := e.map_rel_iff'.mpr hijFin.le
  change chronologicalKey left right (e i).down ≤
      chronologicalKey left right (e j).down at hle
  have hne : chronologicalKey left right (e i).down ≠
      chronologicalKey left right (e j).down := by
    intro hkey
    have hdown : (e i).down = (e j).down :=
      chronologicalKey_injective left right hkey
    have hup : e i = e j := Equiv.ulift.injective hdown
    exact Fin.ne_of_lt hijFin (e.toEquiv.injective hup)
  have hkey : chronologicalKey left right (e i).down <
      chronologicalKey left right (e j).down := lt_of_le_of_ne hle hne
  simpa [chronologicalEquiv, chronologicalLinearOrder, e] using hkey

/-- Reindex a logical bridge tuple into chronological insertion order. -/
def chronologicalValues {mLeft mRight : ℕ} {A : Type*}
    (left : TimedTerminalSkeleton mLeft)
    (right : TimedTerminalSkeleton mRight)
    (values : Fin (mLeft + mRight) → A) :
    Fin (mLeft + mRight) → A :=
  fun k ↦ values (chronologicalEquiv left right k)

/-- Recover logical coordinates from chronologically indexed values. -/
def logicalValues {mLeft mRight : ℕ} {A : Type*}
    (left : TimedTerminalSkeleton mLeft)
    (right : TimedTerminalSkeleton mRight)
    (values : Fin (mLeft + mRight) → A) :
    Fin (mLeft + mRight) → A :=
  fun q ↦ values ((chronologicalEquiv left right).symm q)

@[simp] theorem logicalValues_chronologicalValues
    {mLeft mRight : ℕ} {A : Type*}
    (left : TimedTerminalSkeleton mLeft)
    (right : TimedTerminalSkeleton mRight)
    (values : Fin (mLeft + mRight) → A) :
    logicalValues left right (chronologicalValues left right values) = values := by
  funext q
  simp [logicalValues, chronologicalValues]

@[simp] theorem chronologicalValues_logicalValues
    {mLeft mRight : ℕ} {A : Type*}
    (left : TimedTerminalSkeleton mLeft)
    (right : TimedTerminalSkeleton mRight)
    (values : Fin (mLeft + mRight) → A) :
    chronologicalValues left right (logicalValues left right values) = values := by
  funext q
  simp [logicalValues, chronologicalValues]

/-! ## Pairwise interval ordering -/

/-- Separate within-branch well-formedness and cross-branch alignment imply
that every two distinct logical intervals have one of the two possible
non-overlap orders. -/
theorem pairIntervals_nonoverlap {mLeft mRight : ℕ}
    {left : TimedTerminalSkeleton mLeft}
    {right : TimedTerminalSkeleton mRight}
    (hleft : left.WellFormed) (hright : right.WellFormed)
    (halign : ∀ (i : Fin mLeft) (j : Fin mRight),
      left.exit i ≤ right.entrance j ∨ right.exit j ≤ left.entrance i)
    {a b : Fin (mLeft + mRight)} (hab : a ≠ b) :
    pairExit left right a ≤ pairEntrance left right b ∨
      pairExit left right b ≤ pairEntrance left right a := by
  obtain ⟨i | i, rfl⟩ := finSumFinEquiv.surjective a
  · obtain ⟨j | j, rfl⟩ := finSumFinEquiv.surjective b
    · have hij : i ≠ j := by
        intro h
        apply hab
        simpa [h]
      rcases lt_or_gt_of_ne hij with hij | hji
      · left
        simpa [pairExit, pairEntrance] using hleft.2 i j hij
      · right
        simpa [pairExit, pairEntrance] using hleft.2 j i hji
    · simpa [pairExit, pairEntrance] using halign i j
  · obtain ⟨j | j, rfl⟩ := finSumFinEquiv.surjective b
    · simpa [pairExit, pairEntrance, or_comm] using halign j i
    · have hij : i ≠ j := by
        intro h
        apply hab
        simpa [h]
      rcases lt_or_gt_of_ne hij with hij | hji
      · left
        simpa [pairExit, pairEntrance] using hright.2 i j hij
      · right
        simpa [pairExit, pairEntrance] using hright.2 j i hji

private theorem exit_le_entrance_of_key_lt
    {mLeft mRight : ℕ}
    {left : TimedTerminalSkeleton mLeft}
    {right : TimedTerminalSkeleton mRight}
    {a b : Fin (mLeft + mRight)}
    (hbstart : pairEntrance left right b ≤ pairExit left right b)
    (hkey : chronologicalKey left right a < chronologicalKey left right b)
    (hdisjoint : pairExit left right a ≤ pairEntrance left right b ∨
      pairExit left right b ≤ pairEntrance left right a) :
    pairExit left right a ≤ pairEntrance left right b := by
  rcases hdisjoint with hgood | hreverse
  · exact hgood
  · rw [chronologicalKey, chronologicalKey,
      Prod.Lex.toLex_lt_toLex] at hkey
    rcases hkey with hentrance | ⟨hentrance, htail⟩
    · have : pairEntrance left right b < pairEntrance left right b :=
        lt_of_le_of_lt (hbstart.trans hreverse) hentrance
      exact False.elim (Nat.lt_irrefl _ this)
    · rw [Prod.Lex.toLex_lt_toLex] at htail
      rcases htail with hexit | ⟨_hexit, _hlogical⟩
      · exact hexit.le.trans (hreverse.trans hentrance.le)
      · exact _hexit.le.trans (hreverse.trans hentrance.le)

/-! ## The merged timed skeleton -/

/-- Merge two interval families by the chronological sorting permutation.
The left horizon is used as the common horizon; well-formedness below asks
that the right horizon agree with it. -/
def mergeTimedTerminalSkeleton {mLeft mRight : ℕ}
    (left : TimedTerminalSkeleton mLeft)
    (right : TimedTerminalSkeleton mRight) :
    TimedTerminalSkeleton (mLeft + mRight) where
  horizon := left.horizon
  entrance := chronologicalValues left right (pairEntrance left right)
  exit := chronologicalValues left right (pairExit left right)
  entrancePoint := chronologicalValues left right (pairEntrancePoint left right)
  exitPoint := chronologicalValues left right (pairExitPoint left right)

/-- The merged family is a genuine chronological timed skeleton. -/
theorem mergeTimedTerminalSkeleton_wellFormed {mLeft mRight : ℕ}
    {left : TimedTerminalSkeleton mLeft}
    {right : TimedTerminalSkeleton mRight}
    (hleft : left.WellFormed) (hright : right.WellFormed)
    (hhorizon : right.horizon = left.horizon)
    (halign : ∀ (i : Fin mLeft) (j : Fin mRight),
      left.exit i ≤ right.entrance j ∨ right.exit j ≤ left.entrance i) :
    (mergeTimedTerminalSkeleton left right).WellFormed := by
  constructor
  · intro k
    let q := chronologicalEquiv left right k
    have hq : pairEntrance left right q ≤ pairExit left right q ∧
        pairExit left right q ≤ left.horizon := by
      obtain ⟨i | i, hi⟩ := finSumFinEquiv.surjective q
      · simpa [pairEntrance, pairExit, ← hi] using hleft.1 i
      · have hrighti := hright.1 i
        simpa [pairEntrance, pairExit, hhorizon, ← hi] using hrighti
    simpa [mergeTimedTerminalSkeleton, chronologicalValues, q] using hq
  · intro i j hij
    let a := chronologicalEquiv left right i
    let b := chronologicalEquiv left right j
    have hab : a ≠ b := by
      intro hab
      exact Fin.ne_of_lt hij ((chronologicalEquiv left right).injective hab)
    have hbstart : pairEntrance left right b ≤ pairExit left right b := by
      obtain ⟨q | q, hq⟩ := finSumFinEquiv.surjective b
      · simpa [pairEntrance, pairExit, ← hq] using (hleft.1 q).1
      · simpa [pairEntrance, pairExit, ← hq] using (hright.1 q).1
    have hkey : chronologicalKey left right a < chronologicalKey left right b :=
      chronologicalKey_strictMono left right hij
    have hdisjoint := pairIntervals_nonoverlap hleft hright halign hab
    have hordered := exit_le_entrance_of_key_lt hbstart hkey hdisjoint
    simpa [mergeTimedTerminalSkeleton, chronologicalValues, a, b] using hordered

/-- Logical coordinates of the merged entrance vector are exactly the two
original entrance vectors. -/
@[simp] theorem logicalValues_mergeTimedTerminalSkeleton_entrance
    {mLeft mRight : ℕ}
    (left : TimedTerminalSkeleton mLeft)
    (right : TimedTerminalSkeleton mRight) :
    logicalValues left right (mergeTimedTerminalSkeleton left right).entrance =
      pairEntrance left right := by
  change logicalValues left right
      (chronologicalValues left right (pairEntrance left right)) = _
  exact logicalValues_chronologicalValues left right _

/-- Logical coordinates of the merged exit vector are exactly the two
original exit vectors. -/
@[simp] theorem logicalValues_mergeTimedTerminalSkeleton_exit
    {mLeft mRight : ℕ}
    (left : TimedTerminalSkeleton mLeft)
    (right : TimedTerminalSkeleton mRight) :
    logicalValues left right (mergeTimedTerminalSkeleton left right).exit =
      pairExit left right := by
  change logicalValues left right
      (chronologicalValues left right (pairExit left right)) = _
  exact logicalValues_chronologicalValues left right _

/-! ## Exact reconstruction with logical bridge coordinates -/

/-- The actual interval words, still indexed left-then-right. -/
def logicalIntervalWords {mLeft mRight : ℕ} (omega : StepPath)
    (left : TimedTerminalSkeleton mLeft)
    (right : TimedTerminalSkeleton mRight) :
    Fin (mLeft + mRight) → List Direction :=
  pairValue (intervalWords omega left.entrance left.exit)
    (intervalWords omega right.entrance right.exit)

/-- Reordering the logical actual words chronologically gives exactly the
interval-word vector of the merged timed skeleton. -/
theorem chronologicalValues_logicalIntervalWords
    {mLeft mRight : ℕ} (omega : StepPath)
    (left : TimedTerminalSkeleton mLeft)
    (right : TimedTerminalSkeleton mRight) :
    chronologicalValues left right (logicalIntervalWords omega left right) =
      intervalWords omega (mergeTimedTerminalSkeleton left right).entrance
        (mergeTimedTerminalSkeleton left right).exit := by
  funext k
  let q := chronologicalEquiv left right k
  obtain ⟨i | i, hi⟩ := finSumFinEquiv.surjective q
  · simp [chronologicalValues, logicalIntervalWords, intervalWords,
      mergeTimedTerminalSkeleton, pairEntrance, pairExit, q, ← hi]
  · simp [chronologicalValues, logicalIntervalWords, intervalWords,
      mergeTimedTerminalSkeleton, pairEntrance, pairExit, q, ← hi]

/-- One compressed complementary skeleton and the chronologically reordered
logical words reconstruct the original stopped prefix exactly. -/
theorem reconstruct_mergedTerminalPacket
    {mLeft mRight : ℕ} (omega : StepPath)
    {left : TimedTerminalSkeleton mLeft}
    {right : TimedTerminalSkeleton mRight}
    (hleft : left.WellFormed) (hright : right.WellFormed)
    (hhorizon : right.horizon = left.horizon)
    (halign : ∀ (i : Fin mLeft) (j : Fin mRight),
      left.exit i ≤ right.entrance j ∨ right.exit j ≤ left.entrance i) :
    reconstructTerminalPacket
        (compressTimedSkeleton omega (mergeTimedTerminalSkeleton left right),
          chronologicalValues left right
            (logicalIntervalWords omega left right)) =
      incrementSlice omega 0 left.horizon := by
  rw [chronologicalValues_logicalIntervalWords]
  exact reconstruct_packetOfTimedSkeleton omega _
    (mergeTimedTerminalSkeleton_wellFormed hleft hright hhorizon halign)

/-! ## A concrete flat complementary atom with logical pair coordinates -/

/-- The terminal centre attached to a logical left-then-right coordinate. -/
def logicalPairCenter {mLeft mRight : ℕ} (x y : Point) :
    Fin (mLeft + mRight) → Point :=
  pairValue (fun _ ↦ x) (fun _ ↦ y)

/-- The genuine first-outer-boundary word code at each logical pair
coordinate.  The boundary and both endpoints are those of the corresponding
branch of the timed skeleton. -/
abbrev LogicalPairTerminalBridge
    {mLeft mRight : ℕ} (scale : ℕ) (x y : Point)
    (left : TimedTerminalSkeleton mLeft)
    (right : TimedTerminalSkeleton mRight)
    (q : Fin (mLeft + mRight)) :=
  BoundaryExitWordCode
    (terminalOuterBoundary scale (logicalPairCenter x y q))
    (pairEntrancePoint left right q) (pairExitPoint left right q)

/-- Erase a logical bridge tuple and reorder its words into chronological
insertion order. -/
def chronologicalPairBridgeWords
    {mLeft mRight : ℕ} {scale : ℕ} {x y : Point}
    {left : TimedTerminalSkeleton mLeft}
    {right : TimedTerminalSkeleton mRight}
    (bridges : (q : Fin (mLeft + mRight)) →
      LogicalPairTerminalBridge scale x y left right q) :
    TerminalSegmentWords (mLeft + mRight) :=
  chronologicalValues left right (fun q ↦ List.ofFn (bridges q).1.2)

/-- Reindexing a dependent logical bridge tuple chronologically is
injective. -/
theorem chronologicalPairBridgeWords_injective
    {mLeft mRight : ℕ} {scale : ℕ} {x y : Point}
    {left : TimedTerminalSkeleton mLeft}
    {right : TimedTerminalSkeleton mRight} :
    Function.Injective
      (chronologicalPairBridgeWords
        (scale := scale) (x := x) (y := y) (left := left) (right := right)) := by
  intro a b hab
  funext q
  let k := (chronologicalEquiv left right).symm q
  have hk := congrFun hab k
  change List.ofFn (a (chronologicalEquiv left right k)).1.2 =
    List.ofFn (b (chronologicalEquiv left right k)).1.2 at hk
  have hword : (a (chronologicalEquiv left right k)).1 =
      (b (chronologicalEquiv left right k)).1 := by
    have := congrArg listStoppedWord hk
    simpa only [listStoppedWord_ofFn] using this
  have hbridge : a (chronologicalEquiv left right k) =
      b (chronologicalEquiv left right k) := Subtype.ext hword
  have hkq : chronologicalEquiv left right k = q := by
    simp [k]
  rw [hkq] at hbridge
  exact hbridge

/-- Assemble a pair tuple with logical left-then-right coordinates by first
moving its bridge words to chronological coordinates. -/
def assembleLogicalPairTerminalBridges
    {start mLeft mRight scale : ℕ} {x y : Point}
    (omega : StepPath)
    (left : TimedTerminalSkeleton mLeft)
    (right : TimedTerminalSkeleton mRight)
    (code : (Fin start → Direction) ×
      ((q : Fin (mLeft + mRight)) →
        LogicalPairTerminalBridge scale x y left right q)) : StoppedWord :=
  assembleAfterPrefix code.1
    (compressTimedSkeleton omega (mergeTimedTerminalSkeleton left right))
    (chronologicalPairBridgeWords code.2)

/-- A literal complementary-skeleton atom for two terminal bridge families.

The common retained word is stored once.  Bridge coordinates remain in the
logical order `left ++ right`; only `assemble` applies the chronological
permutation.  `hfirst` is the exact residual pathwise splice premise needed
to turn injectivity of parsing into prefix-freeness of stopped cylinders.
It is not a probability or mass assumption. -/
def logicalPairComplementarySkeletonAtom
    {start mLeft mRight scale : ℕ} {x y : Point}
    (omega : StepPath)
    (left : TimedTerminalSkeleton mLeft)
    (right : TimedTerminalSkeleton mRight)
    (globalBoundary : Set Point) (globalStart : Point)
    (hfirst : ∀ bridges : (q : Fin (mLeft + mRight)) →
        LogicalPairTerminalBridge scale x y left right q,
      AbsoluteBoundaryFirstAt globalBoundary globalStart
        (assembledTerminalPath
          (compressTimedSkeleton omega (mergeTimedTerminalSkeleton left right))
          (chronologicalPairBridgeWords bridges))
        (assembledTerminalHorizon
          (compressTimedSkeleton omega (mergeTimedTerminalSkeleton left right))
          (chronologicalPairBridgeWords bridges))) :
    ComplementarySkeletonAtom (mLeft + mRight) (Fin start → Direction)
      (LogicalPairTerminalBridge scale x y left right) where
  complementWord := fun pre ↦ retainedTerminalWord pre
    (compressTimedSkeleton omega (mergeTimedTerminalSkeleton left right))
  bridgeWord := fun _ bridge ↦ bridge.1
  assemble := assembleLogicalPairTerminalBridges omega left right
  prefixFree_assemble := by
    let mergedCode :=
      compressTimedSkeleton omega (mergeTimedTerminalSkeleton left right)
    let assemble := assembleLogicalPairTerminalBridges
      (start := start) (scale := scale) (x := x) (y := y) omega left right
    have hcoordinateFree : ∀ k : Fin (mLeft + mRight),
        PrefixFree (fun b : LogicalPairTerminalBridge scale x y left right
            (chronologicalEquiv left right k) ↦
          listStoppedWord (List.ofFn b.1.2)) := by
      intro k
      simpa only [listStoppedWord_ofFn] using
        prefixFree_boundaryExitWordCode
          (terminalOuterBoundary scale
            (logicalPairCenter x y (chronologicalEquiv left right k)))
          (pairEntrancePoint left right (chronologicalEquiv left right k))
          (pairExitPoint left right (chronologicalEquiv left right k))
    have hparse : Function.Injective assemble := by
      intro c d hcd
      let toChronological := fun c : (Fin start → Direction) ×
          ((q : Fin (mLeft + mRight)) →
            LogicalPairTerminalBridge scale x y left right q) ↦
        (c.1, fun k ↦ c.2 (chronologicalEquiv left right k))
      have hbase : Function.Injective
          (fun c : (Fin start → Direction) ×
              ((k : Fin (mLeft + mRight)) →
                LogicalPairTerminalBridge scale x y left right
                  (chronologicalEquiv left right k)) ↦
            assembleAfterPrefix c.1 mergedCode
              (fun k ↦ List.ofFn (c.2 k).1.2)) := by
        exact assembleAfterPrefix_injective_of_prefixFree mergedCode
          (fun k ↦ LogicalPairTerminalBridge scale x y left right
            (chronologicalEquiv left right k))
          (fun _ bridge ↦ List.ofFn bridge.1.2) hcoordinateFree
      have hchron : toChronological c = toChronological d := by
        apply hbase
        exact hcd
      apply Prod.ext
      · exact congrArg
          (fun z : (Fin start → Direction) ×
              ((k : Fin (mLeft + mRight)) →
                LogicalPairTerminalBridge scale x y left right
                  (chronologicalEquiv left right k)) ↦ z.1) hchron
      · apply chronologicalPairBridgeWords_injective
        change chronologicalPairBridgeWords c.2 = chronologicalPairBridgeWords d.2
        exact congrArg
          (fun z : (Fin start → Direction) ×
              ((k : Fin (mLeft + mRight)) →
                LogicalPairTerminalBridge scale x y left right
                  (chronologicalEquiv left right k)) ↦
            fun k ↦ List.ofFn (z.2 k).1.2) hchron
    intro c d hcd
    rw [Set.disjoint_left]
    intro path hc hd
    have hcTail :=
      Erdos1165.TerminalSkeletonFactorization.shiftSteps_mem_assembledTerminalWordCylinder_of_mem_assembleAfterPrefix hc
    have hdTail :=
      Erdos1165.TerminalSkeletonFactorization.shiftSteps_mem_assembledTerminalWordCylinder_of_mem_assembleAfterPrefix hd
    have hcfirst := absoluteBoundaryFirstAt_of_mem_stoppedWordCylinder hcTail
      (hfirst c.2)
    have hdfirst := absoluteBoundaryFirstAt_of_mem_stoppedWordCylinder hdTail
      (hfirst d.2)
    have htailLength :
        (assembledTerminalWord mergedCode
          (chronologicalPairBridgeWords c.2)).1 =
        (assembledTerminalWord mergedCode
          (chronologicalPairBridgeWords d.2)).1 :=
      absoluteBoundaryFirstAt_unique hcfirst hdfirst
    have hlen : (assemble c).1 = (assemble d).1 := by
      simpa only [assemble, assembleLogicalPairTerminalBridges, mergedCode,
        assembleAfterPrefix_length] using congrArg (start + ·) htailLength
    apply hcd
    apply hparse
    apply Sigma.ext hlen
    apply (Fin.heq_fun_iff hlen).2
    intro i
    change stepPrefix (assemble c).1 path = (assemble c).2 at hc
    change stepPrefix (assemble d).1 path = (assemble d).2 at hd
    have hci := congrFun hc i
    have hdi := congrFun hd ⟨(i : ℕ), hlen ▸ i.2⟩
    simpa only [stepPrefix] using hci.symm.trans hdi
  prefixFree_bridge := fun q ↦
    prefixFree_boundaryExitWordCode
      (terminalOuterBoundary scale (logicalPairCenter x y q))
      (pairEntrancePoint left right q) (pairExitPoint left right q)
  length_assemble := by
    rintro ⟨pre, bridges⟩
    rw [assembleLogicalPairTerminalBridges, assembleAfterPrefix_length_eq,
      retainedTerminalWord_length]
    apply congrArg ((start + retainedTerminalLength
      (compressTimedSkeleton omega
        (mergeTimedTerminalSkeleton left right))) + ·)
    simp only [chronologicalPairBridgeWords, chronologicalValues,
      List.length_ofFn]
    exact Equiv.sum_comp (chronologicalEquiv left right)
      (fun q ↦ (bridges q).1.1)

@[simp] theorem logicalPairComplementarySkeletonAtom_complementWord
    {start mLeft mRight scale : ℕ} {x y : Point}
    (omega : StepPath)
    (left : TimedTerminalSkeleton mLeft)
    (right : TimedTerminalSkeleton mRight)
    (globalBoundary : Set Point) (globalStart : Point)
    (hfirst : ∀ bridges : (q : Fin (mLeft + mRight)) →
        LogicalPairTerminalBridge scale x y left right q,
      AbsoluteBoundaryFirstAt globalBoundary globalStart
        (assembledTerminalPath
          (compressTimedSkeleton omega (mergeTimedTerminalSkeleton left right))
          (chronologicalPairBridgeWords bridges))
        (assembledTerminalHorizon
          (compressTimedSkeleton omega (mergeTimedTerminalSkeleton left right))
          (chronologicalPairBridgeWords bridges)))
    (pre : Fin start → Direction) :
    (logicalPairComplementarySkeletonAtom omega left right
      globalBoundary globalStart hfirst).complementWord pre =
        retainedTerminalWord pre
          (compressTimedSkeleton omega
            (mergeTimedTerminalSkeleton left right)) := rfl

@[simp] theorem logicalPairComplementarySkeletonAtom_bridgeWord
    {start mLeft mRight scale : ℕ} {x y : Point}
    (omega : StepPath)
    (left : TimedTerminalSkeleton mLeft)
    (right : TimedTerminalSkeleton mRight)
    (globalBoundary : Set Point) (globalStart : Point)
    (hfirst : ∀ bridges : (q : Fin (mLeft + mRight)) →
        LogicalPairTerminalBridge scale x y left right q,
      AbsoluteBoundaryFirstAt globalBoundary globalStart
        (assembledTerminalPath
          (compressTimedSkeleton omega (mergeTimedTerminalSkeleton left right))
          (chronologicalPairBridgeWords bridges))
        (assembledTerminalHorizon
          (compressTimedSkeleton omega (mergeTimedTerminalSkeleton left right))
          (chronologicalPairBridgeWords bridges)))
    (q : Fin (mLeft + mRight))
    (bridge : LogicalPairTerminalBridge scale x y left right q) :
    (logicalPairComplementarySkeletonAtom (start := start) omega left right
      globalBoundary globalStart hfirst).bridgeWord q bridge = bridge.1 := rfl

/-- View the flat atom as the pair-factorization interface.  This changes no
word, event, or common retained weight; it only splits the logical coordinate
tuple at the deterministic left/right boundary. -/
def logicalPairSharedPrefixAtom
    {start mLeft mRight scale : ℕ} {x y : Point}
    (omega : StepPath)
    (left : TimedTerminalSkeleton mLeft)
    (right : TimedTerminalSkeleton mRight)
    (globalBoundary : Set Point) (globalStart : Point)
    (hfirst : ∀ bridges : (q : Fin (mLeft + mRight)) →
        LogicalPairTerminalBridge scale x y left right q,
      AbsoluteBoundaryFirstAt globalBoundary globalStart
        (assembledTerminalPath
          (compressTimedSkeleton omega (mergeTimedTerminalSkeleton left right))
          (chronologicalPairBridgeWords bridges))
        (assembledTerminalHorizon
          (compressTimedSkeleton omega (mergeTimedTerminalSkeleton left right))
          (chronologicalPairBridgeWords bridges))) :=
  SharedPrefixPairAtom.ofComplementarySkeletonAtom
    (mLeft := mLeft) (mRight := mRight)
    (logicalPairComplementarySkeletonAtom (start := start) omega left right
      globalBoundary globalStart hfirst)

/-! ## The actual separated-point extraction -/

/-- Merge the two concrete terminal skeletons extracted from one stopped
walk. -/
def extractMergedTimedTerminalSkeleton
    (scale horizon : ℕ) (profileDelta : ℝ) (x y : Point)
    (omega : StepPath) :
    TimedTerminalSkeleton (terminalCount scale profileDelta +
      terminalCount scale profileDelta) :=
  mergeTimedTerminalSkeleton
    (extractTimedTerminalSkeleton scale horizon profileDelta x omega)
    (extractTimedTerminalSkeleton scale horizon profileDelta y omega)

/-- Far separated stopped-successful points give a well-formed merged
terminal skeleton with no additional clock premise. -/
theorem extractMergedTimedTerminalSkeleton_wellFormed
    {scale horizon : ℕ} {profileDelta : ℝ} {x y : Point}
    {omega : StepPath}
    (hscale : 1 ≤ scale)
    (hlevel : separationLevel scale x y ≤ scale)
    (hexit : IsOuterExitTime (trajectory omega) scale horizon)
    (hx : SuccessfulPoint (trajectory omega) scale horizon profileDelta x)
    (hy : SuccessfulPoint (trajectory omega) scale horizon profileDelta y) :
    (extractMergedTimedTerminalSkeleton scale horizon profileDelta x y omega).WellFormed := by
  apply mergeTimedTerminalSkeleton_wellFormed
  · exact extractTimedTerminalSkeleton_wellFormed_of_stopped_success
      hscale hexit hx
  · exact extractTimedTerminalSkeleton_wellFormed_of_stopped_success
      hscale hexit hy
  · rfl
  · simpa [TerminalPairClockAligned, extractTimedTerminalSkeleton] using
      terminalPairClockAligned_of_separationLevel_le
        hscale hlevel hexit hx hy

/-- Exact one-copy reconstruction for the actual separated pair. -/
theorem reconstruct_extractMergedTerminalPacket
    {scale horizon : ℕ} {profileDelta : ℝ} {x y : Point}
    {omega : StepPath}
    (hscale : 1 ≤ scale)
    (hlevel : separationLevel scale x y ≤ scale)
    (hexit : IsOuterExitTime (trajectory omega) scale horizon)
    (hx : SuccessfulPoint (trajectory omega) scale horizon profileDelta x)
    (hy : SuccessfulPoint (trajectory omega) scale horizon profileDelta y) :
    reconstructTerminalPacket
        (packetOfTimedSkeleton omega
          (extractMergedTimedTerminalSkeleton scale horizon profileDelta x y omega)) =
      incrementSlice omega 0 horizon := by
  exact reconstruct_packetOfTimedSkeleton omega _
    (extractMergedTimedTerminalSkeleton_wellFormed
      hscale hlevel hexit hx hy)

end

end Erdos1165.SharedPrefixPairMergedSkeleton
