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

import ErdosProblems.Erdos1165.AsymmetricExtractedTerminalRightReplacement
import ErdosProblems.Erdos1165.TerminalMarkedSkeletonMass

/-!
# A countable asymmetric terminal partition

The complete compressed skeleton at `y` deletes precisely the terminal
bridges around `y`.  Its complementary word therefore retains every other
increment, in particular the complete stopped history used to impose the
condition at `x`.  This file packages those right-only atoms in the literal
factorization interface used by `AsymmetricActualFarPairConstructor`.

Validity is stored as a proof in the complement code.  Consequently an
invalid combination of compressed data and endpoint vectors has no
complement codes and hence an empty event, while its bridge family still has
the canonical unmarked or marked `y` kernel.
-/

open MeasureTheory Set
open scoped BigOperators ENNReal

namespace Erdos1165.AsymmetricTerminalPartitionAdapter

open AppendixPair AsymmetricExtractedTerminalRightReplacement
open MarkedBoundaryVisitKernel MarkedBridgeFactorization
open MarkedSkeletonPartition Proposition13Measurability
open TerminalExcursionPathwise TerminalMarkedSkeletonDecomposition
open TerminalMarkedSkeletonMass TerminalSkeletonFactorization
open TerminalSkeletonInsertionInvariance TerminalSkeletonInvariance
open TerminalSkeletonWords ThickPoint

noncomputable section

abbrev coordinateCount (scale : ℕ) (profileDelta : ℝ) : ℕ :=
  AppendixLocalTime.requiredTerminalCount scale profileDelta

abbrev Data (scale : ℕ) (profileDelta : ℝ) :=
  TerminalSkeletonData (coordinateCount scale profileDelta)

/-- The raw `y` skeleton reconstructed from separately indexed supported
endpoint vectors. -/
abbrev rawCode
    {scale : ℕ} {profileDelta : ℝ} {y : Point}
    (data : Data scale profileDelta)
    (entrance : Fin (coordinateCount scale profileDelta) →
      TerminalEntrance scale y)
    (exit : Fin (coordinateCount scale profileDelta) →
      TerminalExit scale y) :=
  rawSupportedTerminalCode data entrance exit

/-- The complement is the arbitrary pre-block prefix together with evidence
that the compressed endpoint-labelled skeleton is genuine.  If the code is
invalid, this type is empty. -/
abbrev Complement
    (start scale : ℕ) (profileDelta : ℝ) (y : Point)
    (data : Data scale profileDelta)
    (entrance : Fin (coordinateCount scale profileDelta) →
      TerminalEntrance scale y)
    (exit : Fin (coordinateCount scale profileDelta) →
      TerminalExit scale y) :=
  {pre : Fin start → Direction //
    ValidTerminalSkeleton scale profileDelta y
      (rawCode data entrance exit)}

/-- Only a first-exit bridge around `y` is variable. -/
abbrev UnmarkedBridge
    (profileDelta : ℝ) (scale : ℕ) (y : Point)
    (_j : Fin (coordinateCount scale profileDelta))
    (entrance : TerminalEntrance scale y)
    (exit : TerminalExit scale y) :=
  BoundaryExitWordCode (terminalOuterBoundary scale y) entrance.1 exit.1

/-- Marked right bridge: visit count at `y` and the next outer endpoint. -/
abbrev MarkedBridge
    (profileDelta : ℝ) (scale : ℕ) (y : Point)
    (_j : Fin (coordinateCount scale profileDelta))
    (entrance : TerminalEntrance scale y) (visits : ℕ)
    (exit : TerminalExit scale y) :=
  BoundaryVisitExitWordCode (terminalOuterBoundary scale y) y
    entrance.1 visits exit.1

/-- Literal right-only unmarked factor.  The proof component in the
complement is erased before assembly; it contributes no extra choice. -/
def unmarkedFactor
    {start scale : ℕ} {profileDelta : ℝ} {y : Point}
    (hscale : 1 ≤ scale)
    (data : Data scale profileDelta)
    (entrance : Fin (coordinateCount scale profileDelta) →
      TerminalEntrance scale y)
    (exit : Fin (coordinateCount scale profileDelta) →
      TerminalExit scale y) :
    ComplementarySkeletonAtom (coordinateCount scale profileDelta)
      (Complement start scale profileDelta y data entrance exit)
      (fun j ↦ UnmarkedBridge profileDelta scale y j (entrance j) (exit j)) where
  complementWord := fun pre ↦
    retainedTerminalWord pre.1 (rawCode data entrance exit)
  bridgeWord := fun _ bridge ↦ bridge.1
  assemble := fun code ↦
    assembleUnmarkedTerminalBridges (start := start) (scale := scale)
      (x := y) (rawCode data entrance exit) (code.1.1, code.2)
  prefixFree_assemble := by
    let erase :
        (Complement start scale profileDelta y data entrance exit) ×
            ((j : Fin (coordinateCount scale profileDelta)) →
              UnmarkedBridge profileDelta scale y j (entrance j) (exit j)) →
          (Fin start → Direction) ×
            ((j : Fin (coordinateCount scale profileDelta)) →
              UnmarkedBridge profileDelta scale y j (entrance j) (exit j)) :=
      fun code ↦ (code.1.1, code.2)
    have herase : Function.Injective erase := by
      intro a b h
      dsimp only [erase] at h
      apply Prod.ext
      · exact Subtype.ext (congrArg Prod.fst h)
      · have hbridges := congrArg (fun z ↦ z.2) h
        exact hbridges
    intro a b hab
    let base := validUnmarkedComplementarySkeletonAtom (start := start)
      (rawCode data entrance exit) hscale a.1.2
    apply base.prefixFree_assemble
    exact fun h ↦ hab (herase h)
  prefixFree_bridge := fun j ↦
    prefixFree_boundaryExitWordCode (terminalOuterBoundary scale y)
      (entrance j).1 (exit j).1
  length_assemble := by
    intro code
    let base := validUnmarkedComplementarySkeletonAtom (start := start)
      (rawCode data entrance exit) hscale code.1.2
    exact base.length_assemble (code.1.1, code.2)

/-- Literal fixed-visit marked right-only factor with the identical retained
complement word. -/
def markedFactor
    {start scale : ℕ} {profileDelta : ℝ} {y : Point}
    (hscale : 1 ≤ scale)
    (data : Data scale profileDelta)
    (entrance : Fin (coordinateCount scale profileDelta) →
      TerminalEntrance scale y)
    (exit : Fin (coordinateCount scale profileDelta) →
      TerminalExit scale y)
    (visits : Fin (coordinateCount scale profileDelta) → ℕ) :
    ComplementarySkeletonAtom (coordinateCount scale profileDelta)
      (Complement start scale profileDelta y data entrance exit)
      (fun j ↦ MarkedBridge profileDelta scale y j
        (entrance j) (visits j) (exit j)) where
  complementWord := fun pre ↦
    retainedTerminalWord pre.1 (rawCode data entrance exit)
  bridgeWord := fun _ bridge ↦ bridge.1
  assemble := fun code ↦
    assembleMarkedTerminalBridges (start := start) (scale := scale)
      (x := y) (rawCode data entrance exit) visits (code.1.1, code.2)
  prefixFree_assemble := by
    let erase :
        (Complement start scale profileDelta y data entrance exit) ×
            ((j : Fin (coordinateCount scale profileDelta)) →
              MarkedBridge profileDelta scale y j
                (entrance j) (visits j) (exit j)) →
          (Fin start → Direction) ×
            ((j : Fin (coordinateCount scale profileDelta)) →
              MarkedBridge profileDelta scale y j
                (entrance j) (visits j) (exit j)) :=
      fun code ↦ (code.1.1, code.2)
    have herase : Function.Injective erase := by
      intro a b h
      dsimp only [erase] at h
      apply Prod.ext
      · exact Subtype.ext (congrArg Prod.fst h)
      · have hbridges := congrArg (fun z ↦ z.2) h
        exact hbridges
    intro a b hab
    let base := validMarkedComplementarySkeletonAtom (start := start)
      (rawCode data entrance exit) hscale a.1.2 visits
    apply base.prefixFree_assemble
    exact fun h ↦ hab (herase h)
  prefixFree_bridge := fun j ↦
    prefixFree_boundaryVisitExitWordCode (terminalOuterBoundary scale y) y
      (entrance j).1 (visits j) (exit j).1
  length_assemble := by
    intro code
    let base := validMarkedComplementarySkeletonAtom (start := start)
      (rawCode data entrance exit) hscale code.1.2 visits
    exact base.length_assemble (code.1.1, code.2)

abbrev skeletonAtom
    (start scale : ℕ) (profileDelta : ℝ) (y : Point) :=
  terminalSkeletonAtom start scale profileDelta y

abbrev markedAtom
    (start scale : ℕ) (profileDelta : ℝ) (y : Point) :=
  terminalMarkedAtom start scale profileDelta y

private theorem unmarkedFactor_event_eq_validEvent
    {start scale : ℕ} {profileDelta : ℝ} {y : Point}
    (hscale : 1 ≤ scale)
    (data : Data scale profileDelta)
    (entrance : Fin (coordinateCount scale profileDelta) →
      TerminalEntrance scale y)
    (exit : Fin (coordinateCount scale profileDelta) →
      TerminalExit scale y)
    (hvalid : ValidTerminalSkeleton scale profileDelta y
      (rawCode data entrance exit)) :
    (unmarkedFactor (start := start) hscale data entrance exit).event =
      (validUnmarkedComplementarySkeletonAtom (start := start)
        (rawCode data entrance exit) hscale hvalid).event := by
  ext omega
  unfold ComplementarySkeletonAtom.event stoppedWordEvent
  constructor
  · intro homega
    obtain ⟨code, homega⟩ := Set.mem_iUnion.mp homega
    obtain ⟨pre, bridges⟩ := code
    apply Set.mem_iUnion.mpr
    refine ⟨(pre.1, bridges), ?_⟩
    exact homega
  · intro homega
    obtain ⟨code, homega⟩ := Set.mem_iUnion.mp homega
    obtain ⟨pre, bridges⟩ := code
    apply Set.mem_iUnion.mpr
    refine ⟨(⟨pre, hvalid⟩, bridges), ?_⟩
    exact homega

private theorem markedFactor_event_eq_validEvent
    {start scale : ℕ} {profileDelta : ℝ} {y : Point}
    (hscale : 1 ≤ scale)
    (data : Data scale profileDelta)
    (entrance : Fin (coordinateCount scale profileDelta) →
      TerminalEntrance scale y)
    (exit : Fin (coordinateCount scale profileDelta) →
      TerminalExit scale y)
    (visits : Fin (coordinateCount scale profileDelta) → ℕ)
    (hvalid : ValidTerminalSkeleton scale profileDelta y
      (rawCode data entrance exit)) :
    (markedFactor (start := start) hscale data entrance exit visits).event =
      (validMarkedComplementarySkeletonAtom (start := start)
        (rawCode data entrance exit) hscale hvalid visits).event := by
  ext omega
  unfold ComplementarySkeletonAtom.event stoppedWordEvent
  constructor
  · intro homega
    obtain ⟨code, homega⟩ := Set.mem_iUnion.mp homega
    obtain ⟨pre, bridges⟩ := code
    apply Set.mem_iUnion.mpr
    refine ⟨(pre.1, bridges), ?_⟩
    exact homega
  · intro homega
    obtain ⟨code, homega⟩ := Set.mem_iUnion.mp homega
    obtain ⟨pre, bridges⟩ := code
    apply Set.mem_iUnion.mpr
    refine ⟨(⟨pre, hvalid⟩, bridges), ?_⟩
    exact homega

theorem skeletonAtom_event
    {start scale : ℕ} {profileDelta : ℝ} {y : Point}
    (hscale : 1 ≤ scale)
    (data : Data scale profileDelta)
    (entrance : Fin (coordinateCount scale profileDelta) →
      TerminalEntrance scale y)
    (exit : Fin (coordinateCount scale profileDelta) →
      TerminalExit scale y) :
    skeletonAtom start scale profileDelta y data entrance exit =
      (unmarkedFactor (start := start) hscale data entrance exit).event := by
  let code := rawCode data entrance exit
  by_cases hvalid : ValidTerminalSkeleton scale profileDelta y code
  · rw [unmarkedFactor_event_eq_validEvent hscale data entrance exit hvalid]
    exact (validUnmarkedComplementarySkeletonAtom_event_eq_stoppedTerminalSkeletonAtom
      code hscale hvalid).symm
  · change stoppedTerminalSkeletonAtom start scale profileDelta y code = _
    rw [stoppedTerminalSkeletonAtom_eq_empty_of_not_valid hvalid]
    symm
    apply eq_empty_iff_forall_notMem.mpr
    intro omega homega
    unfold ComplementarySkeletonAtom.event stoppedWordEvent at homega
    obtain ⟨code', _⟩ := Set.mem_iUnion.mp homega
    exact hvalid code'.1.2

theorem markedAtom_event
    {start scale : ℕ} {profileDelta : ℝ} {y : Point}
    (hscale : 1 ≤ scale)
    (data : Data scale profileDelta)
    (entrance : Fin (coordinateCount scale profileDelta) →
      TerminalEntrance scale y)
    (exit : Fin (coordinateCount scale profileDelta) →
      TerminalExit scale y)
    (visits : Fin (coordinateCount scale profileDelta) → ℕ) :
    markedAtom start scale profileDelta y data entrance exit visits =
      (markedFactor (start := start) hscale data entrance exit visits).event := by
  let code := rawCode data entrance exit
  by_cases hvalid : ValidTerminalSkeleton scale profileDelta y code
  · rw [markedFactor_event_eq_validEvent hscale data entrance exit visits hvalid]
    exact (validMarkedComplementarySkeletonAtom_event_eq_stoppedMarkedTerminalAtom
      code hscale hvalid visits).symm
  · change stoppedMarkedTerminalAtom start scale profileDelta y
      (code.1, (code.2.1, (code.2.2, visits))) = _
    rw [stoppedMarkedTerminalAtom_eq_empty_of_not_valid
      (code := (code.1, (code.2.1, (code.2.2, visits))))
      (by simpa only [forgetTerminalVisits] using hvalid)]
    symm
    apply eq_empty_iff_forall_notMem.mpr
    intro omega homega
    unfold ComplementarySkeletonAtom.event stoppedWordEvent at homega
    obtain ⟨code', _⟩ := Set.mem_iUnion.mp homega
    exact hvalid code'.1.2

theorem markedFactor_complementWord
    {start scale : ℕ} {profileDelta : ℝ} {y : Point}
    (hscale : 1 ≤ scale)
    (data : Data scale profileDelta)
    (entrance : Fin (coordinateCount scale profileDelta) →
      TerminalEntrance scale y)
    (exit : Fin (coordinateCount scale profileDelta) →
      TerminalExit scale y)
    (visits : Fin (coordinateCount scale profileDelta) → ℕ)
    (complement : Complement start scale profileDelta y data entrance exit) :
    (markedFactor (start := start) hscale data entrance exit visits).complementWord complement =
      (unmarkedFactor (start := start) hscale data entrance exit).complementWord complement := rfl

theorem unmarkedFactor_kernel
    {start scale : ℕ} {profileDelta : ℝ} {y : Point}
    (hscale : 1 ≤ scale)
    (data : Data scale profileDelta)
    (entrance : Fin (coordinateCount scale profileDelta) →
      TerminalEntrance scale y)
    (exit : Fin (coordinateCount scale profileDelta) →
      TerminalExit scale y)
    (j : Fin (coordinateCount scale profileDelta)) :
    (unmarkedFactor (start := start) hscale data entrance exit).kernel j =
      terminalSkeletonKernel (terminalOuterBoundary scale y)
        (entrance j).1 (exit j).1 := by
  unfold ComplementarySkeletonAtom.kernel unmarkedFactor
  rw [← fairSteps_stoppedWordEvent
    (prefixFree_boundaryExitWordCode (terminalOuterBoundary scale y)
      (entrance j).1 (exit j).1)]
  rw [← boundaryExitEndpointSteps_eq_stoppedWordEvent]
  rfl

theorem markedFactor_kernel
    {start scale : ℕ} {profileDelta : ℝ} {y : Point}
    (hscale : 2 ≤ scale)
    (data : Data scale profileDelta)
    (entrance : Fin (coordinateCount scale profileDelta) →
      TerminalEntrance scale y)
    (exit : Fin (coordinateCount scale profileDelta) →
      TerminalExit scale y)
    (visits : Fin (coordinateCount scale profileDelta) → ℕ)
    (j : Fin (coordinateCount scale profileDelta)) :
    (markedFactor (start := start) (by omega : 1 ≤ scale)
      data entrance exit visits).kernel j =
      terminalMarkedKernel (terminalOuterBoundary scale y) y
        (entrance j).1 (visits j) (exit j).1 := by
  unfold ComplementarySkeletonAtom.kernel markedFactor
  rw [← fairSteps_stoppedWordEvent
    (prefixFree_boundaryVisitExitWordCode (terminalOuterBoundary scale y) y
      (entrance j).1 (visits j) (exit j).1)]
  rw [← boundaryVisitExitAtom_eq_stoppedWordEvent _ _ _ _ _
    (center_not_mem_terminalOuterBoundary scale y hscale)]
  rfl

theorem skeletonAtom_pairwise
    (start scale : ℕ) (profileDelta : ℝ) (y : Point) :
    Pairwise fun i j : SkeletonIndex (Data scale profileDelta)
        (TerminalEntrance scale y) (TerminalExit scale y)
        (coordinateCount scale profileDelta) ↦
      Disjoint (indexedSkeletonAtom
          (skeletonAtom start scale profileDelta y) i)
        (indexedSkeletonAtom
          (skeletonAtom start scale profileDelta y) j) :=
  terminalSkeletonAtom_pairwise start scale profileDelta y

/-- The complete countable marked `y` insertion union. -/
def markedUnion
    (start scale : ℕ) (profileDelta : ℝ) (y : Point) : Set StepPath :=
  ⋃ index : SupportedMarkedIndex scale profileDelta y,
    restrictedMarkedAtom Set.univ
      (markedAtom start scale profileDelta y) index

/-- Add the visit vector observed at a fixed stopped horizon to a supported
unmarked skeleton index. -/
def observedMarkedIndex
    {scale : ℕ} {profileDelta : ℝ} {y : Point}
    (supported : SupportedSkeletonIndex scale profileDelta y)
    (omega : StepPath) (start horizon : ℕ) :
    SupportedMarkedIndex scale profileDelta y :=
  (supported.1, (supported.2.1, (supported.2.2,
    terminalVisitVector (trajectory (shiftSteps start omega))
      scale horizon profileDelta y)))

/-- Append the observed visit vector to a supported unmarked code without
re-running or reducing the terminal code extractor. -/
theorem extractMarkedTerminalCode_eq_eraseSupportedMarkedIndex
    {start scale horizon : ℕ} {profileDelta : ℝ} {y : Point}
    {omega : StepPath}
    (supported : SupportedSkeletonIndex scale profileDelta y)
    (hcode : extractTerminalSkeletonCode scale horizon profileDelta y
        (shiftSteps start omega) = eraseSupportedSkeletonIndex supported) :
    extractMarkedTerminalCode scale horizon profileDelta y
        (shiftSteps start omega) =
      eraseSupportedMarkedIndex
        (observedMarkedIndex supported omega start horizon) := by
  unfold extractMarkedTerminalCode
  rw [hcode]
  rfl

/-- A fixed-horizon supported unmarked atom lies in the marked union after
recording the visit vector observed on that same path. -/
theorem mem_markedUnion_of_mem_stoppedTerminalSkeletonCodeAtom
    {start scale horizon : ℕ} {profileDelta : ℝ} {y : Point}
    {omega : StepPath}
    (supported : SupportedSkeletonIndex scale profileDelta y)
    (hatom : omega ∈ stoppedTerminalSkeletonCodeAtom start scale horizon
      profileDelta y (eraseSupportedSkeletonIndex supported)) :
    omega ∈ markedUnion start scale profileDelta y := by
  unfold markedUnion
  apply Set.mem_iUnion.mpr
  refine ⟨observedMarkedIndex supported omega start horizon, ?_⟩
  rw [restrictedMarkedAtom, if_pos (Set.mem_univ _)]
  have hmarked : omega ∈ stoppedMarkedTerminalAtom start scale profileDelta y
      (eraseSupportedMarkedIndex
        (observedMarkedIndex supported omega start horizon)) := by
    apply Set.mem_iUnion.mpr
    refine ⟨horizon, ⟨hatom.1, ?_⟩⟩
    exact extractMarkedTerminalCode_eq_eraseSupportedMarkedIndex
      supported hatom.2
  simpa only [indexedMarkedAtom, markedAtom, terminalMarkedAtom] using hmarked

/-- A supported horizon-collapsed unmarked atom lies in the complete marked
union. -/
theorem mem_markedUnion_of_mem_supportedSkeletonAtom
    {start scale : ℕ} {profileDelta : ℝ} {y : Point}
    {omega : StepPath}
    (supported : SupportedSkeletonIndex scale profileDelta y)
    (hatom : omega ∈ indexedSkeletonAtom
      (terminalSkeletonAtom start scale profileDelta y) supported) :
    omega ∈ markedUnion start scale profileDelta y := by
  change omega ∈ stoppedTerminalSkeletonAtom start scale profileDelta y
    (eraseSupportedSkeletonIndex supported) at hatom
  obtain ⟨horizon, hhorizon⟩ := Set.mem_iUnion.mp hatom
  exact mem_markedUnion_of_mem_stoppedTerminalSkeletonCodeAtom
    supported hhorizon

/-- The complete supported marked union covers stopped success. -/
theorem stoppedSuccessfulPointEvent_subset_markedUnion
    {start scale : ℕ} {profileDelta : ℝ} {y : Point}
    (hscale : 1 ≤ scale) :
    stoppedSuccessfulPointEvent start scale profileDelta y ⊆
      markedUnion start scale profileDelta y := by
  intro omega homega
  rw [stoppedSuccessfulPointEvent_eq_iUnion_supportedSkeletonAtoms
    start scale profileDelta y hscale] at homega
  obtain ⟨supported, hsupported⟩ := Set.mem_iUnion.mp homega
  exact mem_markedUnion_of_mem_supportedSkeletonAtom supported hsupported

/-- The thick pair is covered by the marked `y` partition.  Since the visit
set in the far-pair upper constructor is `univ`, no terminal local-time
condition is imposed or duplicated here. -/
theorem thickPair_subset_markedUnion
    {start scale : ℕ} {profileDelta thickDelta : ℝ} {x y : Point}
    (hscale : 1 ≤ scale) :
    stoppedThickPointEvent start scale profileDelta thickDelta x ∩
        stoppedThickPointEvent start scale profileDelta thickDelta y ⊆
      markedUnion start scale profileDelta y := by
  intro omega homega
  obtain ⟨horizon, hexit, hy⟩ := homega.2
  exact stoppedSuccessfulPointEvent_subset_markedUnion hscale
    ⟨horizon, hexit, hy.1⟩

/-- At each source path, the merged pair extractor and the global `y`-only
partition agree on the essential asymmetry: the actual left bridges are
fixed, and the source belongs to the resulting right-only atom. -/
theorem source_mem_rightOnlyAtom_of_thickPair
    {start scale : ℕ} {profileDelta thickDelta : ℝ} {x y : Point}
    (hscale : 1 ≤ scale)
    (hlevel : separationLevel scale x y ≤ scale)
    {omega : StepPath}
    (homega : omega ∈
      stoppedThickPointEvent start scale profileDelta thickDelta x ∩
        stoppedThickPointEvent start scale profileDelta thickDelta y) :
    ∃ horizon : ℕ,
      ∃ hexit : IsOuterExitTime
          (trajectory (shiftSteps start omega)) scale horizon,
        ∃ hx : SuccessfulPoint (trajectory (shiftSteps start omega))
            scale horizon profileDelta x,
          ∃ hy : SuccessfulPoint (trajectory (shiftSteps start omega))
              scale horizon profileDelta y,
            omega ∈ (extractedRightOnlyUnmarkedAtom
              (omega := shiftSteps start omega) (start := start)
              hscale hlevel hexit hx hy hx.1 hy.1).event := by
  obtain ⟨hxSource, hySource⟩ := homega
  obtain ⟨hxHorizon, hxExit, hxThick⟩ := hxSource
  obtain ⟨hyHorizon, hyExit, hyThick⟩ := hySource
  have hhorizon : hyHorizon = hxHorizon :=
    isOuterExitTime_unique hyExit hxExit
  subst hyHorizon
  refine ⟨hxHorizon, hxExit, hxThick.1, hyThick.1, ?_⟩
  exact source_mem_extractedRightOnlyUnmarkedAtom hscale hlevel hxExit
    hxThick.1 hyThick.1 hxThick.1.1 hyThick.1.1

end

end Erdos1165.AsymmetricTerminalPartitionAdapter
