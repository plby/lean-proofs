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

import ErdosProblems.Erdos1165.SharedPrefixPairPartition
import ErdosProblems.Erdos1165.TerminalSkeletonWords

/-!
# Literal extraction of a stopped two-point code

This file is the pathwise part of the shared-prefix pair decomposition.  A
code records

* the actual HLOZ separation level and padded prefix scale;
* one copy of the complete stopped outer word;
* the left and right terminal entrance/exit vectors extracted from the same
  first-global-exit horizon; and
* in the marked code, both terminal visit vectors and the actual finite-
  horizon local times.

The common stopped word is intentionally retained once.  The terminal clocks
are the concrete clocks from `TerminalSkeletonWords`; there is no conditional
independence or measure factorization in this file.  Singleton coding fibres
are measurable, disjoint, and cover the successful pair source exactly.

The actual local-time marks make the upper containment direction honest:
every stopped thick pair lies in a marked fibre selected by its two recorded
local times.  Replacing those full local-time marks by only the selected
terminal visit vectors would require the false reverse of
`thickSuccessfulPoint_of_terminalExcursionVisits`; no such replacement is
made here.
-/

open MeasureTheory Set

namespace Erdos1165.SharedPrefixPairExtraction

open AppendixPair AppendixPairMoment Hitting
open MarkedSkeletonPartition Proposition13Measurability
open SharedPrefixPairPartition TerminalSkeletonWords ThickPoint

noncomputable section

/-- The common stopped outer word.  Its dependent length contains the block
prefix and all increments through the first outer-exit horizon. -/
abbrev StoppedOuterWord (start : ℕ) :=
  Σ horizon : ℕ, Fin (start + (horizon + 1)) → Direction

/-- Shared deterministic scale tags and the literal stopped outer word. -/
abbrev PairCommonCode (start : ℕ) :=
  ℕ × (ℕ × StoppedOuterWord start)

/-- The endpoint information retained from one point's terminal clocks. -/
abbrev TerminalBranchCode (m : ℕ) :=
  (Fin m → Point) × (Fin m → Point)

/-- The marked terminal data for one branch.  Besides the selected terminal
visit vector it records the actual local time through the common horizon. -/
abbrev TerminalMarkedBranchCode (m : ℕ) :=
  TerminalBranchCode m × ((Fin m → ℕ) × ℕ)

abbrev terminalCount (scale : ℕ) (profileDelta : ℝ) :=
  AppendixLocalTime.requiredTerminalCount scale profileDelta

/-- The countable unmarked pair-code type, in `Shared × (Left × Right)`
form for `SharedPrefixPairPartition`. -/
abbrev SharedPairSkeletonCode (start scale : ℕ) (profileDelta : ℝ) :=
  PairData (PairCommonCode start)
    (TerminalBranchCode (terminalCount scale profileDelta))
    (TerminalBranchCode (terminalCount scale profileDelta))

/-- Marked analogue of `SharedPairSkeletonCode`. -/
abbrev SharedPairMarkedCode (start scale : ℕ) (profileDelta : ℝ) :=
  PairData (PairCommonCode start)
    (TerminalMarkedBranchCode (terminalCount scale profileDelta))
    (TerminalMarkedBranchCode (terminalCount scale profileDelta))

theorem countable_sharedPairSkeletonCode
    (start scale : ℕ) (profileDelta : ℝ) :
    Countable (SharedPairSkeletonCode start scale profileDelta) :=
  inferInstance

theorem countable_sharedPairMarkedCode
    (start scale : ℕ) (profileDelta : ℝ) :
    Countable (SharedPairMarkedCode start scale profileDelta) :=
  inferInstance

/-! ## The exact remaining clock-alignment frontier -/

/-- Cross-branch non-overlap of the two concrete terminal interval families.
Each alternative says that one closed erased interval finishes before the
other begins.

For a genuinely complementary common skeleton, one needs this predicate for
the stopped walk whenever `separationLevel scale x y` is in the far range.
The present annular clock API proves well-formedness separately for `x` and
for `y`, but contains no theorem deriving this cross-branch ordering from
disc separation.  Therefore the extraction below retains the common stopped
outer word and does not claim that simultaneous two-family erasure is valid. -/
def TerminalPairClockAligned
    (s : WalkPath) (scale horizon : ℕ) (profileDelta : ℝ)
    (x y : Point) : Prop :=
  ∀ (i j : Fin (terminalCount scale profileDelta)),
    extractedExit s scale horizon x i ≤
        extractedEntrance s scale horizon y j ∨
      extractedExit s scale horizon y j ≤
        extractedEntrance s scale horizon x i

/-- Drop the complementary word data from a one-point terminal skeleton,
retaining just the post-split endpoint marks. -/
def terminalBranchCode
    {m : ℕ} (code : TerminalSkeletonCode m) : TerminalBranchCode m :=
  (code.2.1, code.2.2)

/-- Add the terminal visit vector and the actual full local time to one
branch's endpoint marks. -/
def terminalMarkedBranchCode
    {m : ℕ}
    (code : MarkedIndex (TerminalSkeletonData m) Point Point m)
    (localTime : ℕ) : TerminalMarkedBranchCode m :=
  ((code.2.1, code.2.2.1), (code.2.2.2, localTime))

/-- Fixed-horizon extraction of the shared unmarked pair code. -/
def fixedSharedPairSkeletonCode
    (start scale horizon : ℕ) (profileDelta : ℝ) (x y : Point)
    (omega : StepPath) : SharedPairSkeletonCode start scale profileDelta :=
  let left := extractTerminalSkeletonCode scale horizon profileDelta x
    (shiftSteps start omega)
  let right := extractTerminalSkeletonCode scale horizon profileDelta y
    (shiftSteps start omega)
  ((separationLevel scale x y,
      (pairPrefixScale scale (separationLevel scale x y),
        ⟨horizon, stepPrefix (start + (horizon + 1)) omega⟩)),
    (terminalBranchCode left, terminalBranchCode right))

/-- Fixed-horizon marked extraction from the same outer word and the same
terminal clocks. -/
def fixedSharedPairMarkedCode
    (start scale horizon : ℕ) (profileDelta : ℝ) (x y : Point)
    (omega : StepPath) : SharedPairMarkedCode start scale profileDelta :=
  let left := extractMarkedTerminalCode scale horizon profileDelta x
    (shiftSteps start omega)
  let right := extractMarkedTerminalCode scale horizon profileDelta y
    (shiftSteps start omega)
  ((separationLevel scale x y,
      (pairPrefixScale scale (separationLevel scale x y),
        ⟨horizon, stepPrefix (start + (horizon + 1)) omega⟩)),
    (terminalMarkedBranchCode left
        (localTimeThrough (shiftedWalk start omega) horizon x),
      terminalMarkedBranchCode right
        (localTimeThrough (shiftedWalk start omega) horizon y)))

/-- Total stopped pair code obtained by collapsing the unique first global
outer-exit horizon. -/
def stoppedSharedPairSkeletonCode
    (start scale : ℕ) (profileDelta : ℝ) (x y : Point)
    (omega : StepPath) : SharedPairSkeletonCode start scale profileDelta :=
  fixedSharedPairSkeletonCode start scale
    (stoppedOuterExitHorizon start scale omega) profileDelta x y omega

/-- Total marked stopped pair code. -/
def stoppedSharedPairMarkedCode
    (start scale : ℕ) (profileDelta : ℝ) (x y : Point)
    (omega : StepPath) : SharedPairMarkedCode start scale profileDelta :=
  fixedSharedPairMarkedCode start scale
    (stoppedOuterExitHorizon start scale omega) profileDelta x y omega

private lemma shiftSteps_congr_of_prefix
    {start horizon : ℕ} {omega omega' : StepPath}
    (hprefix : ∀ k < start + (horizon + 1), omega k = omega' k) :
    ∀ k < horizon + 1,
      shiftSteps start omega k = shiftSteps start omega' k := by
  intro k hk
  unfold shiftSteps
  exact hprefix (start + k) (by omega)

private lemma shiftedWalk_congr_of_prefix
    {start horizon : ℕ} {omega omega' : StepPath}
    (hprefix : ∀ k < start + (horizon + 1), omega k = omega' k) :
    ∀ k ≤ horizon,
      shiftedWalk start omega k = shiftedWalk start omega' k := by
  intro k hk
  exact trajectory_congr_of_incrementPrefix
    (shiftSteps_congr_of_prefix hprefix) (hk.trans (Nat.le_add_right horizon 1))

lemma fixedSharedPairSkeletonCode_congr_prefix
    {start scale horizon : ℕ} {profileDelta : ℝ} {x y : Point}
    {omega omega' : StepPath}
    (hprefix : ∀ k < start + (horizon + 1), omega k = omega' k) :
    fixedSharedPairSkeletonCode start scale horizon profileDelta x y omega =
      fixedSharedPairSkeletonCode start scale horizon profileDelta x y omega' := by
  have hblock := shiftSteps_congr_of_prefix hprefix
  have hleft := extractTerminalSkeletonCode_congr_prefix
    (scale := scale) (profileDelta := profileDelta) (x := x) hblock
  have hright := extractTerminalSkeletonCode_congr_prefix
    (scale := scale) (profileDelta := profileDelta) (x := y) hblock
  have hword : stepPrefix (start + (horizon + 1)) omega =
      stepPrefix (start + (horizon + 1)) omega' := by
    funext k
    exact hprefix k k.isLt
  unfold fixedSharedPairSkeletonCode
  rw [hleft, hright, hword]

lemma fixedSharedPairMarkedCode_congr_prefix
    {start scale horizon : ℕ} {profileDelta : ℝ} {x y : Point}
    {omega omega' : StepPath}
    (hprefix : ∀ k < start + (horizon + 1), omega k = omega' k) :
    fixedSharedPairMarkedCode start scale horizon profileDelta x y omega =
      fixedSharedPairMarkedCode start scale horizon profileDelta x y omega' := by
  have hblock := shiftSteps_congr_of_prefix hprefix
  have hwalk := shiftedWalk_congr_of_prefix hprefix
  have hleft := extractMarkedTerminalCode_congr_prefix
    (scale := scale) (profileDelta := profileDelta) (x := x) hblock
  have hright := extractMarkedTerminalCode_congr_prefix
    (scale := scale) (profileDelta := profileDelta) (x := y) hblock
  have hlocalLeft := localTimeThrough_congr_prefix hwalk x
  have hlocalRight := localTimeThrough_congr_prefix hwalk y
  have hword : stepPrefix (start + (horizon + 1)) omega =
      stepPrefix (start + (horizon + 1)) omega' := by
    funext k
    exact hprefix k k.isLt
  unfold fixedSharedPairMarkedCode
  rw [hleft, hright, hlocalLeft, hlocalRight, hword]

lemma measurableSet_fixedSharedPairSkeletonCode_fiber
    (start scale horizon : ℕ) (profileDelta : ℝ) (x y : Point)
    (code : SharedPairSkeletonCode start scale profileDelta) :
    MeasurableSet {omega : StepPath |
      fixedSharedPairSkeletonCode start scale horizon profileDelta x y omega =
        code} := by
  let N := start + (horizon + 1)
  let C : Set (Fin N → Direction) :=
    {word | fixedSharedPairSkeletonCode start scale horizon profileDelta x y
      (extendFiniteDirectionWord word) = code}
  have hC : MeasurableSet C := (Set.to_countable C).measurableSet
  have heq : {omega : StepPath |
      fixedSharedPairSkeletonCode start scale horizon profileDelta x y omega =
        code} = stepPrefix N ⁻¹' C := by
    ext omega
    change fixedSharedPairSkeletonCode start scale horizon profileDelta x y omega =
        code ↔ fixedSharedPairSkeletonCode start scale horizon profileDelta x y
          (extendFiniteDirectionWord (stepPrefix N omega)) = code
    have hcongr : fixedSharedPairSkeletonCode start scale horizon
        profileDelta x y omega =
        fixedSharedPairSkeletonCode start scale horizon profileDelta x y
          (extendFiniteDirectionWord (stepPrefix N omega)) := by
      apply fixedSharedPairSkeletonCode_congr_prefix
      intro k hk
      simp [N, extendFiniteDirectionWord, stepPrefix, hk]
    rw [hcongr]
  rw [heq]
  exact (measurable_stepPrefix N) hC

lemma measurableSet_fixedSharedPairMarkedCode_fiber
    (start scale horizon : ℕ) (profileDelta : ℝ) (x y : Point)
    (code : SharedPairMarkedCode start scale profileDelta) :
    MeasurableSet {omega : StepPath |
      fixedSharedPairMarkedCode start scale horizon profileDelta x y omega =
        code} := by
  let N := start + (horizon + 1)
  let C : Set (Fin N → Direction) :=
    {word | fixedSharedPairMarkedCode start scale horizon profileDelta x y
      (extendFiniteDirectionWord word) = code}
  have hC : MeasurableSet C := (Set.to_countable C).measurableSet
  have heq : {omega : StepPath |
      fixedSharedPairMarkedCode start scale horizon profileDelta x y omega =
        code} = stepPrefix N ⁻¹' C := by
    ext omega
    change fixedSharedPairMarkedCode start scale horizon profileDelta x y omega =
        code ↔ fixedSharedPairMarkedCode start scale horizon profileDelta x y
          (extendFiniteDirectionWord (stepPrefix N omega)) = code
    have hcongr : fixedSharedPairMarkedCode start scale horizon
        profileDelta x y omega =
        fixedSharedPairMarkedCode start scale horizon profileDelta x y
          (extendFiniteDirectionWord (stepPrefix N omega)) := by
      apply fixedSharedPairMarkedCode_congr_prefix
      intro k hk
      simp [N, extendFiniteDirectionWord, stepPrefix, hk]
    rw [hcongr]
  rw [heq]
  exact (measurable_stepPrefix N) hC

theorem measurableSet_stoppedSharedPairSkeletonCode_fiber
    (start scale : ℕ) (profileDelta : ℝ) (x y : Point)
    (code : SharedPairSkeletonCode start scale profileDelta) :
    MeasurableSet {omega : StepPath |
      stoppedSharedPairSkeletonCode start scale profileDelta x y omega = code} := by
  have heq : {omega : StepPath |
      stoppedSharedPairSkeletonCode start scale profileDelta x y omega = code} =
      ⋃ horizon : ℕ,
        {omega | stoppedOuterExitHorizon start scale omega = horizon} ∩
          {omega | fixedSharedPairSkeletonCode start scale horizon
            profileDelta x y omega = code} := by
    ext omega
    simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_ofPred_eq]
    constructor
    · intro hcode
      exact ⟨stoppedOuterExitHorizon start scale omega, rfl, hcode⟩
    · rintro ⟨horizon, hhorizon, hcode⟩
      unfold stoppedSharedPairSkeletonCode
      rwa [hhorizon]
  rw [heq]
  exact MeasurableSet.iUnion fun horizon ↦
    (measurableSet_stoppedOuterExitHorizon_eq start scale horizon).inter
      (measurableSet_fixedSharedPairSkeletonCode_fiber
        start scale horizon profileDelta x y code)

theorem measurableSet_stoppedSharedPairMarkedCode_fiber
    (start scale : ℕ) (profileDelta : ℝ) (x y : Point)
    (code : SharedPairMarkedCode start scale profileDelta) :
    MeasurableSet {omega : StepPath |
      stoppedSharedPairMarkedCode start scale profileDelta x y omega = code} := by
  have heq : {omega : StepPath |
      stoppedSharedPairMarkedCode start scale profileDelta x y omega = code} =
      ⋃ horizon : ℕ,
        {omega | stoppedOuterExitHorizon start scale omega = horizon} ∩
          {omega | fixedSharedPairMarkedCode start scale horizon
            profileDelta x y omega = code} := by
    ext omega
    simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_ofPred_eq]
    constructor
    · intro hcode
      exact ⟨stoppedOuterExitHorizon start scale omega, rfl, hcode⟩
    · rintro ⟨horizon, hhorizon, hcode⟩
      unfold stoppedSharedPairMarkedCode
      rwa [hhorizon]
  rw [heq]
  exact MeasurableSet.iUnion fun horizon ↦
    (measurableSet_stoppedOuterExitHorizon_eq start scale horizon).inter
      (measurableSet_fixedSharedPairMarkedCode_fiber
        start scale horizon profileDelta x y code)

/-! ## Literal fibres and their pathwise partition -/

/-- The source event on which both points have successful profiles at the
same unique global-exit horizon. -/
def stoppedSuccessfulPairEvent
    (start scale : ℕ) (profileDelta : ℝ) (x y : Point) : Set StepPath :=
  stoppedSuccessfulPointEvent start scale profileDelta x ∩
    stoppedSuccessfulPointEvent start scale profileDelta y

/-- One literal unmarked pair-code fibre. -/
def stoppedSharedPairSkeletonAtom
    (start scale : ℕ) (profileDelta : ℝ) (x y : Point)
    (code : SharedPairSkeletonCode start scale profileDelta) : Set StepPath :=
  codingFiber (stoppedSuccessfulPairEvent start scale profileDelta x y)
    (stoppedSharedPairSkeletonCode start scale profileDelta x y) code

/-- One marked pair-code fibre. -/
def stoppedSharedPairMarkedAtom
    (start scale : ℕ) (profileDelta : ℝ) (x y : Point)
    (code : SharedPairMarkedCode start scale profileDelta) : Set StepPath :=
  codingFiber (stoppedSuccessfulPairEvent start scale profileDelta x y)
    (stoppedSharedPairMarkedCode start scale profileDelta x y) code

theorem measurableSet_stoppedSuccessfulPairEvent
    (start scale : ℕ) (profileDelta : ℝ) (x y : Point) :
    MeasurableSet (stoppedSuccessfulPairEvent start scale profileDelta x y) :=
  (measurableSet_stoppedSuccessfulPointEvent start scale profileDelta x).inter
    (measurableSet_stoppedSuccessfulPointEvent start scale profileDelta y)

theorem measurableSet_stoppedSharedPairSkeletonAtom
    (start scale : ℕ) (profileDelta : ℝ) (x y : Point)
    (code : SharedPairSkeletonCode start scale profileDelta) :
    MeasurableSet
      (stoppedSharedPairSkeletonAtom start scale profileDelta x y code) :=
  codingFiber_measurable
    (measurableSet_stoppedSuccessfulPairEvent start scale profileDelta x y)
    (fun c ↦ measurableSet_stoppedSharedPairSkeletonCode_fiber
      start scale profileDelta x y c) code

theorem measurableSet_stoppedSharedPairMarkedAtom
    (start scale : ℕ) (profileDelta : ℝ) (x y : Point)
    (code : SharedPairMarkedCode start scale profileDelta) :
    MeasurableSet
      (stoppedSharedPairMarkedAtom start scale profileDelta x y code) :=
  codingFiber_measurable
    (measurableSet_stoppedSuccessfulPairEvent start scale profileDelta x y)
    (fun c ↦ measurableSet_stoppedSharedPairMarkedCode_fiber
      start scale profileDelta x y c) code

theorem stoppedSharedPairSkeletonAtom_pairwise
    (start scale : ℕ) (profileDelta : ℝ) (x y : Point) :
    Pairwise fun i j : SharedPairSkeletonCode start scale profileDelta ↦
      Disjoint
        (stoppedSharedPairSkeletonAtom start scale profileDelta x y i)
        (stoppedSharedPairSkeletonAtom start scale profileDelta x y j) :=
  codingFiber_pairwise _ _

theorem stoppedSharedPairMarkedAtom_pairwise
    (start scale : ℕ) (profileDelta : ℝ) (x y : Point) :
    Pairwise fun i j : SharedPairMarkedCode start scale profileDelta ↦
      Disjoint
        (stoppedSharedPairMarkedAtom start scale profileDelta x y i)
        (stoppedSharedPairMarkedAtom start scale profileDelta x y j) :=
  codingFiber_pairwise _ _

theorem stoppedSuccessfulPairEvent_eq_iUnion_skeletonAtoms
    (start scale : ℕ) (profileDelta : ℝ) (x y : Point) :
    stoppedSuccessfulPairEvent start scale profileDelta x y =
      ⋃ code : SharedPairSkeletonCode start scale profileDelta,
        stoppedSharedPairSkeletonAtom start scale profileDelta x y code := by
  symm
  exact iUnion_codingFiber _ _

theorem stoppedSuccessfulPairEvent_eq_iUnion_markedAtoms
    (start scale : ℕ) (profileDelta : ℝ) (x y : Point) :
    stoppedSuccessfulPairEvent start scale profileDelta x y =
      ⋃ code : SharedPairMarkedCode start scale profileDelta,
        stoppedSharedPairMarkedAtom start scale profileDelta x y code := by
  symm
  exact iUnion_codingFiber _ _

/-! ## Honest upper selection by the recorded full local times -/

/-- A marked pair code is selected when both recorded full local times cross
the thick threshold. -/
def selectedThickPairCode
    (scale : ℕ) (thickDelta : ℝ)
    {start : ℕ} {profileDelta : ℝ}
    (code : SharedPairMarkedCode start scale profileDelta) : Prop :=
  thickThreshold scale thickDelta ≤ (code.2.1.2.2 : ℝ) ∧
    thickThreshold scale thickDelta ≤ (code.2.2.2.2 : ℝ)

/-- Union of the marked fibres selected by their two actual local-time
marks. -/
def selectedThickPairMarkedAtoms
    (start scale : ℕ) (profileDelta thickDelta : ℝ) (x y : Point) :
    Set StepPath := by
  classical
  exact ⋃ code : SharedPairMarkedCode start scale profileDelta,
    if selectedThickPairCode scale thickDelta code then
      stoppedSharedPairMarkedAtom start scale profileDelta x y code else ∅

theorem measurableSet_selectedThickPairMarkedAtoms
    (start scale : ℕ) (profileDelta thickDelta : ℝ) (x y : Point) :
    MeasurableSet
      (selectedThickPairMarkedAtoms start scale profileDelta thickDelta x y) := by
  classical
  unfold selectedThickPairMarkedAtoms
  apply MeasurableSet.iUnion
  intro code
  by_cases hselected : selectedThickPairCode scale thickDelta code
  · rw [if_pos hselected]
    exact measurableSet_stoppedSharedPairMarkedAtom
      start scale profileDelta x y code
  · rw [if_neg hselected]
    exact MeasurableSet.empty

/-- Every stopped thick pair belongs to its unique marked code fibre, and the
two local-time fields of that code satisfy the selection predicate. -/
theorem stoppedThickPairEvent_subset_selectedMarkedAtoms
    (start scale : ℕ) (profileDelta thickDelta : ℝ) (x y : Point) :
    stoppedThickPointEvent start scale profileDelta thickDelta x ∩
        stoppedThickPointEvent start scale profileDelta thickDelta y ⊆
      selectedThickPairMarkedAtoms start scale profileDelta thickDelta x y := by
  rintro omega ⟨⟨horizon, hexit, hx⟩, ⟨horizon', hexit', hy⟩⟩
  have hhorizon : horizon = horizon' := isOuterExitTime_unique hexit hexit'
  subst horizon'
  have hcollapsed : stoppedOuterExitHorizon start scale omega = horizon :=
    stoppedOuterExitHorizon_eq_of_isOuterExitTime hexit
  let code := stoppedSharedPairMarkedCode start scale profileDelta x y omega
  have hselected : selectedThickPairCode scale thickDelta code := by
    change thickThreshold scale thickDelta ≤
        (localTimeThrough (shiftedWalk start omega)
          (stoppedOuterExitHorizon start scale omega) x : ℝ) ∧
      thickThreshold scale thickDelta ≤
        (localTimeThrough (shiftedWalk start omega)
          (stoppedOuterExitHorizon start scale omega) y : ℝ)
    rw [hcollapsed]
    exact ⟨hx.2, hy.2⟩
  apply Set.mem_iUnion.mpr
  refine ⟨code, ?_⟩
  rw [if_pos hselected]
  exact ⟨⟨⟨horizon, hexit, hx.1⟩, ⟨horizon, hexit, hy.1⟩⟩, rfl⟩

end

end Erdos1165.SharedPrefixPairExtraction
