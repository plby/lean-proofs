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

import ErdosProblems.Erdos1165.AlternatingConcatPrefixFree
import ErdosProblems.Erdos1165.TerminalSkeletonInvariance
import ErdosProblems.Erdos1165.TerminalExtractedBridgeCodes

/-!
# Prefix-free factorization for concrete terminal skeletons

This module proves the purely finite-word uniqueness needed to turn the
literal alternating terminal reconstruction into a
`ComplementarySkeletonAtom`.  The retained pieces are fixed, whereas the
deleted bridge words may have arbitrary lengths.  Their canonical
first-boundary codes are prefix-free, so the words can be parsed uniquely
from left to right.  A final first-hit condition at the global boundary then
makes the complete assembled family prefix-free as stopped words.
-/

open Set

namespace Erdos1165.TerminalSkeletonFactorization

open MarkedBridgeFactorization TerminalSkeletonWords
open TerminalSkeletonInvariance
open AlternatingConcatPrefixFree
open ThickPoint TerminalExcursionPathwise TerminalSequentialVisitLaw
open TerminalExtractedBridgeCodes Proposition13Measurability

noncomputable section

/-! ## Exact assembled words -/

/-- Reattaching the literal deleted intervals of a well-formed timed
skeleton after the actual length-`start` prefix recovers an exact stopped
prefix of the original path. -/
lemma mem_stoppedWordCylinder_assembleAfterPrefix_packetOfTimedSkeleton
    {start m : ℕ} (omega : StepPath) (t : TimedTerminalSkeleton m)
    (ht : t.WellFormed) :
    omega ∈ stoppedWordCylinder
      (assembleAfterPrefix (stepPrefix start omega)
        (compressTimedSkeleton (shiftSteps start omega) t)
        (intervalWords (shiftSteps start omega) t.entrance t.exit)) := by
  have hreconstruct := reconstruct_packetOfTimedSkeleton
    (shiftSteps start omega) t ht
  change reconstructTerminalPacket
      (compressTimedSkeleton (shiftSteps start omega) t,
        intervalWords (shiftSteps start omega) t.entrance t.exit) =
      incrementSlice (shiftSteps start omega) 0 t.horizon at hreconstruct
  let full := List.ofFn (stepPrefix start omega) ++
    reconstructTerminalPacket
      (compressTimedSkeleton (shiftSteps start omega) t,
        intervalWords (shiftSteps start omega) t.entrance t.exit)
  have hpre : List.ofFn (stepPrefix start omega) =
      incrementSlice omega 0 start := by
    apply List.ext_get
    · simp [incrementSlice]
    · intro n hn hn'
      rw [List.get_eq_getElem, List.get_eq_getElem]
      simp [incrementSlice, stepPrefix]
  have hshift : incrementSlice (shiftSteps start omega) 0 t.horizon =
      incrementSlice omega start (start + t.horizon) := by
    simp [incrementSlice, shiftSteps]
  have hfull : full = incrementSlice omega 0 (start + t.horizon) := by
    simp only [full, hreconstruct, hpre, hshift]
    exact incrementSlice_append omega (Nat.zero_le start)
      (Nat.le_add_right start t.horizon)
  unfold assembleAfterPrefix stoppedWordCylinder
  change stepPrefix full.length omega = (stoppedWordOfList full).2
  rw [hfull]
  unfold stoppedWordOfList
  funext j
  change omega (j : ℕ) = (incrementSlice omega 0 (start + t.horizon)).get j
  rw [List.get_eq_getElem]
  simp [incrementSlice]

/-- For a fixed compressed terminal skeleton, the exact assembly map is
injective in the fixed-length pre-prefix and the canonical bridge tuple. -/
theorem assembleAfterPrefix_injective_of_prefixFree
    {start m : ℕ} (code : TerminalSkeletonCode m)
    (Bridge : Fin m → Type*)
    (word : (j : Fin m) → Bridge j → List Direction)
    (hfree : ∀ j, PrefixFree (fun b ↦ listStoppedWord (word j b))) :
    Function.Injective
      (fun c : (Fin start → Direction) × ((j : Fin m) → Bridge j) ↦
        assembleAfterPrefix c.1 code (fun j ↦ word j (c.2 j))) := by
  rintro ⟨pre, bridges⟩ ⟨pre', bridges'⟩ hassemble
  have hlists :
      List.ofFn pre ++
          alternatingConcat m code.1.retainedPiece
            (fun j ↦ word j (bridges j)) =
        List.ofFn pre' ++
          alternatingConcat m code.1.retainedPiece
            (fun j ↦ word j (bridges' j)) := by
    have := congrArg (fun w : StoppedWord ↦ List.ofFn w.2) hassemble
    dsimp only at this
    unfold assembleAfterPrefix at this
    rw [stoppedWordOfList_toList, stoppedWordOfList_toList] at this
    simpa only [reconstructTerminalPacket] using this
  have hpreList : List.ofFn pre = List.ofFn pre' :=
    List.append_inj_left hlists (by simp)
  have hpre : pre = pre' := List.ofFn_injective hpreList
  have htail :
      alternatingConcat m code.1.retainedPiece
          (fun j ↦ word j (bridges j)) =
        alternatingConcat m code.1.retainedPiece
          (fun j ↦ word j (bridges' j)) :=
    List.append_inj_right hlists (by simp)
  have hbridges : bridges = bridges' :=
    AlternatingConcatPrefixFree.alternatingConcat_injective_of_prefixFree
      m code.1.retainedPiece
      Bridge word hfree htail
  simp only [hpre, hbridges]

/-- Membership in a complete assembled cylinder implies membership of the
shifted path in the cylinder of its terminal tail. -/
lemma shiftSteps_mem_assembledTerminalWordCylinder_of_mem_assembleAfterPrefix
    {start m : ℕ} {pre : Fin start → Direction}
    {code : TerminalSkeletonCode m} {words : TerminalSegmentWords m}
    {omega : StepPath}
    (homega : omega ∈ stoppedWordCylinder
      (assembleAfterPrefix pre code words)) :
    shiftSteps start omega ∈
      stoppedWordCylinder (assembledTerminalWord code words) := by
  let tail := reconstructTerminalPacket (code, words)
  let full := List.ofFn pre ++ tail
  change stepPrefix tail.length (shiftSteps start omega) =
    (stoppedWordOfList tail).2
  funext q
  have hfullLength : full.length = start + tail.length := by
    simp [full]
  have hqfull : start + (q : ℕ) < full.length := by
    omega
  have hprefix := congrFun homega ⟨start + q, by
    simpa only [assembleAfterPrefix, stoppedWordOfList_length,
      List.length_append, List.length_ofFn, full, tail] using hqfull⟩
  change omega (start + q) = full.get ⟨start + q, hqfull⟩ at hprefix
  change omega (start + q) = tail.get q
  rw [hprefix, List.get_eq_getElem, List.get_eq_getElem]
  simp [full]

/-- If every assembled terminal tail first hits one common global boundary,
then arbitrary fixed-length pre-prefixes followed by those tails form a
prefix-free family.  No condition before the shift time is needed. -/
theorem prefixFree_assembleAfterPrefix_of_tailFirstAt
    {start m : ℕ} (code : TerminalSkeletonCode m)
    (Bridge : Fin m → Type*)
    (word : (j : Fin m) → Bridge j → List Direction)
    (hbridgeFree : ∀ j,
      PrefixFree (fun b ↦ listStoppedWord (word j b)))
    (boundary : Set Point) (tailStart : Point)
    (hfirst : ∀ bridges : (j : Fin m) → Bridge j,
      AbsoluteBoundaryFirstAt boundary tailStart
        (assembledTerminalPath code (fun j ↦ word j (bridges j)))
        (assembledTerminalHorizon code (fun j ↦ word j (bridges j)))) :
    PrefixFree
      (fun c : (Fin start → Direction) × ((j : Fin m) → Bridge j) ↦
        assembleAfterPrefix c.1 code (fun j ↦ word j (c.2 j))) := by
  let assemble :=
    (fun c : (Fin start → Direction) × ((j : Fin m) → Bridge j) ↦
      assembleAfterPrefix c.1 code (fun j ↦ word j (c.2 j)))
  have hinjective : Function.Injective assemble :=
    assembleAfterPrefix_injective_of_prefixFree code Bridge word hbridgeFree
  intro c d hcd
  rw [Set.disjoint_left]
  intro omega hc hd
  have hcTail :=
    shiftSteps_mem_assembledTerminalWordCylinder_of_mem_assembleAfterPrefix hc
  have hdTail :=
    shiftSteps_mem_assembledTerminalWordCylinder_of_mem_assembleAfterPrefix hd
  have hcfirst := absoluteBoundaryFirstAt_of_mem_stoppedWordCylinder hcTail
    (hfirst c.2)
  have hdfirst := absoluteBoundaryFirstAt_of_mem_stoppedWordCylinder hdTail
    (hfirst d.2)
  have htailLength :
      (assembledTerminalWord code (fun j ↦ word j (c.2 j))).1 =
        (assembledTerminalWord code (fun j ↦ word j (d.2 j))).1 :=
    absoluteBoundaryFirstAt_unique hcfirst hdfirst
  have hlen : (assemble c).1 = (assemble d).1 := by
    simp only [assemble, assembleAfterPrefix_length]
    omega
  apply hcd
  apply hinjective
  apply Sigma.ext hlen
  apply (Fin.heq_fun_iff hlen).2
  intro i
  change stepPrefix (assemble c).1 omega = (assemble c).2 at hc
  change stepPrefix (assemble d).1 omega = (assemble d).2 at hd
  have hci := congrFun hc i
  have hdi := congrFun hd ⟨(i : ℕ), hlen ▸ i.2⟩
  simpa only [stepPrefix] using hci.symm.trans hdi

/-! ## Canonical unmarked and marked bridge families -/

/-- Erased unmarked first-boundary words are prefix-free at each terminal
coordinate. -/
theorem prefixFree_unmarkedBridgeWords
    {m scale : ℕ} {x : Point} (code : TerminalSkeletonCode m) (j : Fin m) :
    PrefixFree (fun b : UnmarkedTerminalBridgeCode scale x code j ↦
      listStoppedWord (List.ofFn b.1.2)) := by
  simpa only [listStoppedWord_ofFn]
    using prefixFree_boundaryExitWordCode
      (terminalOuterBoundary scale x) (code.2.1 j) (code.2.2 j)

/-- Erased marked first-boundary words are prefix-free at each terminal
coordinate. -/
theorem prefixFree_markedBridgeWords
    {m scale : ℕ} {x : Point} (code : TerminalSkeletonCode m)
    (visits : Fin m → ℕ) (j : Fin m) :
    PrefixFree (fun b : MarkedTerminalBridgeCode scale x code visits j ↦
      listStoppedWord (List.ofFn b.1.2)) := by
  simpa only [listStoppedWord_ofFn]
    using prefixFree_boundaryVisitExitWordCode
      (terminalOuterBoundary scale x) x (code.2.1 j) (visits j) (code.2.2 j)

/-- Exact injectivity of the unmarked terminal assembly. -/
theorem assembleUnmarkedTerminalBridges_injective
    {start m scale : ℕ} {x : Point} (code : TerminalSkeletonCode m) :
    Function.Injective
      (assembleUnmarkedTerminalBridges (start := start) (scale := scale)
        (x := x) code) := by
  apply assembleAfterPrefix_injective_of_prefixFree code
    (fun j ↦ UnmarkedTerminalBridgeCode scale x code j)
    (fun _ b ↦ List.ofFn b.1.2)
  exact prefixFree_unmarkedBridgeWords code

/-- Exact injectivity of the marked terminal assembly. -/
theorem assembleMarkedTerminalBridges_injective
    {start m scale : ℕ} {x : Point} (code : TerminalSkeletonCode m)
    (visits : Fin m → ℕ) :
    Function.Injective
      (assembleMarkedTerminalBridges (start := start) (scale := scale)
        (x := x) code visits) := by
  apply assembleAfterPrefix_injective_of_prefixFree code
    (fun j ↦ MarkedTerminalBridgeCode scale x code visits j)
    (fun _ b ↦ List.ofFn b.1.2)
  exact prefixFree_markedBridgeWords code visits

/-- If every unmarked assembled word first hits a common global boundary at
its own horizon, the whole alternating family has disjoint stopped
cylinders. -/
theorem prefixFree_assembleUnmarkedTerminalBridges
    {start m scale : ℕ} {x : Point} (code : TerminalSkeletonCode m)
    (globalBoundary : Set Point) (globalStart : Point)
    (hfirst : ∀ bridges : (j : Fin m) →
        UnmarkedTerminalBridgeCode scale x code j,
      AbsoluteBoundaryFirstAt globalBoundary globalStart
      (assembledTerminalPath code
        (unmarkedBridgeWords (scale := scale) (x := x) (code := code) bridges))
      (assembledTerminalHorizon code
        (unmarkedBridgeWords (scale := scale) (x := x) (code := code) bridges))) :
    PrefixFree
      (assembleUnmarkedTerminalBridges (start := start) (scale := scale)
        (x := x) code) := by
  exact prefixFree_assembleAfterPrefix_of_tailFirstAt code
    (fun j ↦ UnmarkedTerminalBridgeCode scale x code j)
    (fun _ b ↦ List.ofFn b.1.2) (prefixFree_unmarkedBridgeWords code)
    globalBoundary globalStart hfirst

/-- Marked analogue of `prefixFree_assembleUnmarkedTerminalBridges`. -/
theorem prefixFree_assembleMarkedTerminalBridges
    {start m scale : ℕ} {x : Point} (code : TerminalSkeletonCode m)
    (visits : Fin m → ℕ) (globalBoundary : Set Point) (globalStart : Point)
    (hfirst : ∀ bridges : (j : Fin m) →
        MarkedTerminalBridgeCode scale x code visits j,
      AbsoluteBoundaryFirstAt globalBoundary globalStart
      (assembledTerminalPath code
        (markedBridgeWords (scale := scale) (x := x) (code := code)
          (visits := visits) bridges))
      (assembledTerminalHorizon code
        (markedBridgeWords (scale := scale) (x := x) (code := code)
          (visits := visits) bridges))) :
    PrefixFree
      (assembleMarkedTerminalBridges (start := start) (scale := scale)
        (x := x) code visits) := by
  exact prefixFree_assembleAfterPrefix_of_tailFirstAt code
    (fun j ↦ MarkedTerminalBridgeCode scale x code visits j)
    (fun _ b ↦ List.ofFn b.1.2) (prefixFree_markedBridgeWords code visits)
    globalBoundary globalStart hfirst

/-! ## Every raw stopped atom has a literal insertion representation -/

/-- Every path in a raw unmarked stopped skeleton atom is obtained by
re-inserting its own canonical first-outer-hit bridge words after its actual
length-`start` prefix.  This direction uses only finite-word reconstruction,
not splice invariance. -/
theorem stoppedTerminalSkeletonAtom_subset_unmarkedTerminalInsertionEvent
    {start scale : ℕ} {profileDelta : ℝ} {x : Point}
    (hscale : 1 ≤ scale)
    (code : TerminalSkeletonCode
      (AppendixLocalTime.requiredTerminalCount scale profileDelta)) :
    stoppedTerminalSkeletonAtom start scale profileDelta x code ⊆
      unmarkedTerminalInsertionEvent (start := start) (scale := scale)
        (x := x) code := by
  intro omega homega
  obtain ⟨horizon, hsuccess, hcode⟩ := Set.mem_iUnion.mp homega
  change extractTerminalSkeletonCode scale horizon profileDelta x
      (shiftSteps start omega) = code at hcode
  let sigma := shiftSteps start omega
  have hexit : IsOuterExitTime (trajectory sigma) scale horizon := hsuccess.1
  have hx : SuccessfulPoint (trajectory sigma) scale horizon profileDelta x :=
    hsuccess.2
  subst code
  let bridges : (j : Fin
      (AppendixLocalTime.requiredTerminalCount scale profileDelta)) →
      UnmarkedTerminalBridgeCode scale x
        (extractTerminalSkeletonCode scale horizon profileDelta x sigma) j :=
    fun j ↦ extractedTerminalBoundaryExitWordCode hscale hexit hx j
  have hwords : unmarkedBridgeWords bridges =
      intervalWords sigma
        (extractTimedTerminalSkeleton scale horizon profileDelta x sigma).entrance
        (extractTimedTerminalSkeleton scale horizon profileDelta x sigma).exit := by
    funext j
    exact extractedTerminalBoundaryExitWordCode_erased hscale hexit hx j
  unfold unmarkedTerminalInsertionEvent stoppedWordEvent
  apply Set.mem_iUnion.mpr
  refine ⟨(stepPrefix start omega, bridges), ?_⟩
  rw [assembleUnmarkedTerminalBridges, hwords]
  simpa only [extractTerminalSkeletonCode] using
    mem_stoppedWordCylinder_assembleAfterPrefix_packetOfTimedSkeleton omega
      (extractTimedTerminalSkeleton scale horizon profileDelta x sigma)
      (extractTimedTerminalSkeleton_wellFormed_of_stopped_success
        hscale hexit hx)

/-- Fixed-horizon marked adapter used to keep the final collapsed-atom
transport independent of the nested marked-index equality. -/
theorem shiftedStoppedSuccessfulPointAtEvent_subset_markedTerminalInsertionEvent
    {start scale horizon : ℕ} {profileDelta : ℝ} {x : Point}
    (hscale : 1 ≤ scale)
    (omega : StepPath)
    (hsuccess : omega ∈ shiftedStoppedSuccessfulPointAtEvent
      start scale horizon profileDelta x) :
    omega ∈
      markedTerminalInsertionEvent (start := start) (scale := scale) (x := x)
        (extractTerminalSkeletonCode scale horizon profileDelta x
          (shiftSteps start omega))
        (terminalVisitVector (trajectory (shiftSteps start omega)) scale horizon
          profileDelta x) := by
  let sigma := shiftSteps start omega
  have hexit : IsOuterExitTime (trajectory sigma) scale horizon := hsuccess.1
  have hx : SuccessfulPoint (trajectory sigma) scale horizon profileDelta x :=
    hsuccess.2
  let bridges : (j : Fin
      (AppendixLocalTime.requiredTerminalCount scale profileDelta)) →
      MarkedTerminalBridgeCode scale x
        (extractTerminalSkeletonCode scale horizon profileDelta x sigma)
        (terminalVisitVector (trajectory sigma) scale horizon profileDelta x) j :=
    fun j ↦ extractedTerminalBoundaryVisitExitWordCode hscale hexit hx j
  have hwords : markedBridgeWords bridges =
      intervalWords sigma
        (extractTimedTerminalSkeleton scale horizon profileDelta x sigma).entrance
        (extractTimedTerminalSkeleton scale horizon profileDelta x sigma).exit := by
    funext j
    exact extractedTerminalBoundaryVisitExitWordCode_erased hscale hexit hx j
  unfold markedTerminalInsertionEvent stoppedWordEvent
  apply Set.mem_iUnion.mpr
  refine ⟨(stepPrefix start omega, bridges), ?_⟩
  rw [assembleMarkedTerminalBridges, hwords]
  simpa only [extractMarkedTerminalCode, extractTerminalSkeletonCode] using
    mem_stoppedWordCylinder_assembleAfterPrefix_packetOfTimedSkeleton omega
      (extractTimedTerminalSkeleton scale horizon profileDelta x sigma)
      (extractTimedTerminalSkeleton_wellFormed_of_stopped_success
        hscale hexit hx)

/-- Marked analogue of
`stoppedTerminalSkeletonAtom_subset_unmarkedTerminalInsertionEvent`: the
actual deleted segments retain exactly the recorded visit vector. -/
theorem stoppedMarkedTerminalAtom_subset_markedTerminalInsertionEvent
    {start scale : ℕ} {profileDelta : ℝ} {x : Point}
    (hscale : 1 ≤ scale)
    (code : MarkedSkeletonPartition.MarkedIndex
      (TerminalSkeletonData
        (AppendixLocalTime.requiredTerminalCount scale profileDelta))
      Point Point (AppendixLocalTime.requiredTerminalCount scale profileDelta)) :
    stoppedMarkedTerminalAtom start scale profileDelta x code ⊆
      markedTerminalInsertionEvent (start := start) (scale := scale) (x := x)
        (code.1, (code.2.1, code.2.2.1)) code.2.2.2 := by
  intro omega homega
  obtain ⟨horizon, hsuccess, hcode⟩ := Set.mem_iUnion.mp homega
  change extractMarkedTerminalCode scale horizon profileDelta x
      (shiftSteps start omega) = code at hcode
  have hin :=
    shiftedStoppedSuccessfulPointAtEvent_subset_markedTerminalInsertionEvent
      hscale omega hsuccess
  rw [← hcode]
  simpa only [extractMarkedTerminalCode] using hin

/-! ## Valid terminal skeletons hit the global boundary -/

/-- Parent pathwise insertion invariance, restated in the exact first-hit
form used by the finite-word prefix-free argument. -/
theorem assembledUnmarkedTerminalBridges_globalFirstAt_of_valid
    {scale : ℕ} {profileDelta : ℝ} {x : Point}
    {code : TerminalSkeletonCode
      (AppendixLocalTime.requiredTerminalCount scale profileDelta)}
    (hscale : 1 ≤ scale)
    (hvalid : ValidTerminalSkeleton scale profileDelta x code)
    (bridges : (j : Fin
      (AppendixLocalTime.requiredTerminalCount scale profileDelta)) →
        UnmarkedTerminalBridgeCode scale x code j) :
    AbsoluteBoundaryFirstAt (discBoundary (0, 0) (outerScale scale)) (0, 0)
      (assembledTerminalPath code
        (unmarkedBridgeWords (scale := scale) (x := x) (code := code) bridges))
      (assembledTerminalHorizon code
        (unmarkedBridgeWords (scale := scale) (x := x) (code := code) bridges)) := by
  have h := isOuterExitTime_assembled_unmarked_of_valid hscale hvalid bridges
  have hzeroAdd : ∀ p : Point, (0, 0) + p = p := by
    rintro ⟨a, b⟩
    simp only [Prod.mk_add_mk, zero_add]
  simpa only [AbsoluteBoundaryFirstAt, IsOuterExitTime,
    PlanarPotential.trajectoryFrom, hzeroAdd]
    using h

/-- Marking a canonical bridge by its visit count does not change its word,
so the same global first-hit conclusion holds for marked bridge tuples. -/
theorem assembledMarkedTerminalBridges_globalFirstAt_of_valid
    {scale : ℕ} {profileDelta : ℝ} {x : Point}
    {code : TerminalSkeletonCode
      (AppendixLocalTime.requiredTerminalCount scale profileDelta)}
    (hscale : 1 ≤ scale)
    (hvalid : ValidTerminalSkeleton scale profileDelta x code)
    (visits : Fin (AppendixLocalTime.requiredTerminalCount scale profileDelta) → ℕ)
    (bridges : (j : Fin
      (AppendixLocalTime.requiredTerminalCount scale profileDelta)) →
        MarkedTerminalBridgeCode scale x code visits j) :
    AbsoluteBoundaryFirstAt (discBoundary (0, 0) (outerScale scale)) (0, 0)
      (assembledTerminalPath code
        (markedBridgeWords (scale := scale) (x := x) (code := code)
          (visits := visits) bridges))
      (assembledTerminalHorizon code
        (markedBridgeWords (scale := scale) (x := x) (code := code)
          (visits := visits) bridges)) := by
  let erase : (j : Fin
      (AppendixLocalTime.requiredTerminalCount scale profileDelta)) →
      UnmarkedTerminalBridgeCode scale x code j := fun j ↦
    ⟨(bridges j).1, (bridges j).2.1, (bridges j).2.2.2⟩
  have h := assembledUnmarkedTerminalBridges_globalFirstAt_of_valid
    hscale hvalid erase
  have hwords :
      markedBridgeWords (scale := scale) (x := x) (code := code)
          (visits := visits) bridges =
        unmarkedBridgeWords (scale := scale) (x := x) (code := code) erase := by
    funext j
    rfl
  rw [← hwords] at h
  exact h

/-! ## Concrete complementary-skeleton atoms -/

/-- The literal unmarked terminal insertion family, packaged in the exact
interface used by the finite-word factorization theorem. -/
def unmarkedComplementarySkeletonAtom
    {start m scale : ℕ} {x : Point} (code : TerminalSkeletonCode m)
    (globalBoundary : Set Point) (globalStart : Point)
    (hfirst : ∀ bridges : (j : Fin m) →
        UnmarkedTerminalBridgeCode scale x code j,
      AbsoluteBoundaryFirstAt globalBoundary globalStart
      (assembledTerminalPath code
        (unmarkedBridgeWords (scale := scale) (x := x) (code := code) bridges))
      (assembledTerminalHorizon code
        (unmarkedBridgeWords (scale := scale) (x := x) (code := code) bridges))) :
    ComplementarySkeletonAtom m (Fin start → Direction)
      (fun j ↦ UnmarkedTerminalBridgeCode scale x code j) where
  complementWord := fun pre ↦ retainedTerminalWord pre code
  bridgeWord := fun _ bridge ↦ bridge.1
  assemble := assembleUnmarkedTerminalBridges (start := start) (scale := scale)
    (x := x) code
  prefixFree_assemble :=
    prefixFree_assembleUnmarkedTerminalBridges code globalBoundary globalStart hfirst
  prefixFree_bridge := fun j ↦
    prefixFree_boundaryExitWordCode (terminalOuterBoundary scale x)
      (code.2.1 j) (code.2.2 j)
  length_assemble := by
    rintro ⟨pre, bridges⟩
    rw [assembleUnmarkedTerminalBridges, assembleAfterPrefix_length_eq]
    rw [retainedTerminalWord, assembleAfterPrefix_length_eq]
    simp only [emptyTerminalWords, List.length_nil, Finset.sum_const_zero,
      add_zero, unmarkedBridgeWords, List.length_ofFn]

/-- The fixed-visit marked terminal insertion family, packaged as a
`ComplementarySkeletonAtom`. -/
def markedComplementarySkeletonAtom
    {start m scale : ℕ} {x : Point} (code : TerminalSkeletonCode m)
    (visits : Fin m → ℕ) (globalBoundary : Set Point) (globalStart : Point)
    (hfirst : ∀ bridges : (j : Fin m) →
        MarkedTerminalBridgeCode scale x code visits j,
      AbsoluteBoundaryFirstAt globalBoundary globalStart
      (assembledTerminalPath code
        (markedBridgeWords (scale := scale) (x := x) (code := code)
          (visits := visits) bridges))
      (assembledTerminalHorizon code
        (markedBridgeWords (scale := scale) (x := x) (code := code)
          (visits := visits) bridges))) :
    ComplementarySkeletonAtom m (Fin start → Direction)
      (fun j ↦ MarkedTerminalBridgeCode scale x code visits j) where
  complementWord := fun pre ↦ retainedTerminalWord pre code
  bridgeWord := fun _ bridge ↦ bridge.1
  assemble := assembleMarkedTerminalBridges (start := start) (scale := scale)
    (x := x) code visits
  prefixFree_assemble :=
    prefixFree_assembleMarkedTerminalBridges code visits globalBoundary globalStart hfirst
  prefixFree_bridge := fun j ↦
    prefixFree_boundaryVisitExitWordCode (terminalOuterBoundary scale x) x
      (code.2.1 j) (visits j) (code.2.2 j)
  length_assemble := by
    rintro ⟨pre, bridges⟩
    rw [assembleMarkedTerminalBridges, assembleAfterPrefix_length_eq]
    rw [retainedTerminalWord, assembleAfterPrefix_length_eq]
    simp only [emptyTerminalWords, List.length_nil, Finset.sum_const_zero,
      add_zero, markedBridgeWords, List.length_ofFn]

/-- A valid raw compressed skeleton gives the canonical unmarked
`ComplementarySkeletonAtom` without any remaining prefix-free premise. -/
def validUnmarkedComplementarySkeletonAtom
    {start scale : ℕ} {profileDelta : ℝ} {x : Point}
    (code : TerminalSkeletonCode
      (AppendixLocalTime.requiredTerminalCount scale profileDelta))
    (hscale : 1 ≤ scale)
    (hvalid : ValidTerminalSkeleton scale profileDelta x code) :
    ComplementarySkeletonAtom
      (AppendixLocalTime.requiredTerminalCount scale profileDelta)
      (Fin start → Direction)
      (fun j ↦ UnmarkedTerminalBridgeCode scale x code j) :=
  unmarkedComplementarySkeletonAtom code
    (discBoundary (0, 0) (outerScale scale)) (0, 0)
    (assembledUnmarkedTerminalBridges_globalFirstAt_of_valid hscale hvalid)

/-- Marked valid-code analogue of
`validUnmarkedComplementarySkeletonAtom`. -/
def validMarkedComplementarySkeletonAtom
    {start scale : ℕ} {profileDelta : ℝ} {x : Point}
    (code : TerminalSkeletonCode
      (AppendixLocalTime.requiredTerminalCount scale profileDelta))
    (hscale : 1 ≤ scale)
    (hvalid : ValidTerminalSkeleton scale profileDelta x code)
    (visits : Fin (AppendixLocalTime.requiredTerminalCount scale profileDelta) → ℕ) :
    ComplementarySkeletonAtom
      (AppendixLocalTime.requiredTerminalCount scale profileDelta)
      (Fin start → Direction)
      (fun j ↦ MarkedTerminalBridgeCode scale x code visits j) :=
  markedComplementarySkeletonAtom code visits
    (discBoundary (0, 0) (outerScale scale)) (0, 0)
    (assembledMarkedTerminalBridges_globalFirstAt_of_valid
      hscale hvalid visits)

@[simp] theorem validUnmarkedComplementarySkeletonAtom_bridgeWord
    {start scale : ℕ} {profileDelta : ℝ} {x : Point}
    (code : TerminalSkeletonCode
      (AppendixLocalTime.requiredTerminalCount scale profileDelta))
    (hscale : 1 ≤ scale)
    (hvalid : ValidTerminalSkeleton scale profileDelta x code)
    (j : Fin (AppendixLocalTime.requiredTerminalCount scale profileDelta))
    (bridge : UnmarkedTerminalBridgeCode scale x code j) :
    (validUnmarkedComplementarySkeletonAtom (start := start)
      code hscale hvalid).bridgeWord j bridge = bridge.1 := rfl

@[simp] theorem validUnmarkedComplementarySkeletonAtom_assemble
    {start scale : ℕ} {profileDelta : ℝ} {x : Point}
    (code : TerminalSkeletonCode
      (AppendixLocalTime.requiredTerminalCount scale profileDelta))
    (hscale : 1 ≤ scale)
    (hvalid : ValidTerminalSkeleton scale profileDelta x code)
    (c : (Fin start → Direction) ×
      ((j : Fin (AppendixLocalTime.requiredTerminalCount scale profileDelta)) →
        UnmarkedTerminalBridgeCode scale x code j)) :
    (validUnmarkedComplementarySkeletonAtom (start := start)
      code hscale hvalid).assemble c =
        assembleUnmarkedTerminalBridges (start := start) (scale := scale)
          (x := x) code c := rfl

@[simp] theorem validMarkedComplementarySkeletonAtom_bridgeWord
    {start scale : ℕ} {profileDelta : ℝ} {x : Point}
    (code : TerminalSkeletonCode
      (AppendixLocalTime.requiredTerminalCount scale profileDelta))
    (hscale : 1 ≤ scale)
    (hvalid : ValidTerminalSkeleton scale profileDelta x code)
    (visits : Fin (AppendixLocalTime.requiredTerminalCount scale profileDelta) → ℕ)
    (j : Fin (AppendixLocalTime.requiredTerminalCount scale profileDelta))
    (bridge : MarkedTerminalBridgeCode scale x code visits j) :
    (validMarkedComplementarySkeletonAtom (start := start)
      code hscale hvalid visits).bridgeWord j bridge = bridge.1 := rfl

@[simp] theorem validMarkedComplementarySkeletonAtom_assemble
    {start scale : ℕ} {profileDelta : ℝ} {x : Point}
    (code : TerminalSkeletonCode
      (AppendixLocalTime.requiredTerminalCount scale profileDelta))
    (hscale : 1 ≤ scale)
    (hvalid : ValidTerminalSkeleton scale profileDelta x code)
    (visits : Fin (AppendixLocalTime.requiredTerminalCount scale profileDelta) → ℕ)
    (c : (Fin start → Direction) ×
      ((j : Fin (AppendixLocalTime.requiredTerminalCount scale profileDelta)) →
        MarkedTerminalBridgeCode scale x code visits j)) :
    (validMarkedComplementarySkeletonAtom (start := start)
      code hscale hvalid visits).assemble c =
        assembleMarkedTerminalBridges (start := start) (scale := scale)
          (x := x) code visits c := rfl

@[simp] theorem validUnmarkedComplementarySkeletonAtom_event
    {start scale : ℕ} {profileDelta : ℝ} {x : Point}
    (code : TerminalSkeletonCode
      (AppendixLocalTime.requiredTerminalCount scale profileDelta))
    (hscale : 1 ≤ scale)
    (hvalid : ValidTerminalSkeleton scale profileDelta x code) :
    (validUnmarkedComplementarySkeletonAtom (start := start)
      code hscale hvalid).event =
        unmarkedTerminalInsertionEvent (start := start) (scale := scale)
          (x := x) code := rfl

@[simp] theorem validMarkedComplementarySkeletonAtom_event
    {start scale : ℕ} {profileDelta : ℝ} {x : Point}
    (code : TerminalSkeletonCode
      (AppendixLocalTime.requiredTerminalCount scale profileDelta))
    (hscale : 1 ≤ scale)
    (hvalid : ValidTerminalSkeleton scale profileDelta x code)
    (visits : Fin (AppendixLocalTime.requiredTerminalCount scale profileDelta) → ℕ) :
    (validMarkedComplementarySkeletonAtom (start := start)
      code hscale hvalid visits).event =
        markedTerminalInsertionEvent (start := start) (scale := scale)
          (x := x) code visits := rfl

@[simp] theorem validMarkedComplementarySkeletonAtom_weight_eq_unmarked
    {start scale : ℕ} {profileDelta : ℝ} {x : Point}
    (code : TerminalSkeletonCode
      (AppendixLocalTime.requiredTerminalCount scale profileDelta))
    (hscale : 1 ≤ scale)
    (hvalid : ValidTerminalSkeleton scale profileDelta x code)
    (visits : Fin (AppendixLocalTime.requiredTerminalCount scale profileDelta) → ℕ) :
    (validMarkedComplementarySkeletonAtom (start := start)
      code hscale hvalid visits).weight =
        (validUnmarkedComplementarySkeletonAtom (start := start)
          code hscale hvalid).weight := rfl

theorem validUnmarked_assemble_prefixFree
    {start scale : ℕ} {profileDelta : ℝ} {x : Point}
    (code : TerminalSkeletonCode
      (AppendixLocalTime.requiredTerminalCount scale profileDelta))
    (hscale : 1 ≤ scale)
    (hvalid : ValidTerminalSkeleton scale profileDelta x code) :
    PrefixFree
      (assembleUnmarkedTerminalBridges (start := start) (scale := scale)
        (x := x) code) :=
  (validUnmarkedComplementarySkeletonAtom (start := start)
    code hscale hvalid).prefixFree_assemble

theorem validMarked_assemble_prefixFree
    {start scale : ℕ} {profileDelta : ℝ} {x : Point}
    (code : TerminalSkeletonCode
      (AppendixLocalTime.requiredTerminalCount scale profileDelta))
    (hscale : 1 ≤ scale)
    (hvalid : ValidTerminalSkeleton scale profileDelta x code)
    (visits : Fin (AppendixLocalTime.requiredTerminalCount scale profileDelta) → ℕ) :
    PrefixFree
      (assembleMarkedTerminalBridges (start := start) (scale := scale)
        (x := x) code visits) :=
  (validMarkedComplementarySkeletonAtom (start := start)
    code hscale hvalid visits).prefixFree_assemble

end

end Erdos1165.TerminalSkeletonFactorization
