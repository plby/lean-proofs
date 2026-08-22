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

import ErdosProblems.Erdos1165.SharedPrefixPairExtractedMarkedAtom

/-!
# A coarse stopped partition by the shared complementary pair skeleton

The earlier total pair code retained the complete stopped outer word.  Such
a code changes whenever a terminal bridge is replaced, so one of its fibres
cannot be an insertion family.  Here the common datum instead consists of
the merged complementary pieces and the finite chronological permutation.
The latter is essential compressed metadata: it says where the logical
left/right bridge coordinates are inserted, without retaining clock values
or bridge durations.

Left and right endpoint vectors are stored separately.  The marked code adds
only their two prescribed terminal visit vectors.  The resulting total codes
have measurable fibres and give disjoint exact covers of the separated
successful-pair source.
-/

open MeasureTheory Set

namespace Erdos1165.SharedPrefixPairCoarsePartition

open AppendixPair Hitting MarkedSkeletonPartition
open SharedPrefixPairExtraction SharedPrefixPairMergedSkeleton
open SharedPrefixPairExtractedAtom SharedPrefixPairExtractedMarkedAtom
open TerminalExcursionPathwise TerminalSkeletonWords ThickPoint

noncomputable section

/-- The shared compressed data used once by both branches: retained pieces
and the finite logical-to-chronological insertion order. -/
abbrev CoarsePairCommonCode (scale : ℕ) (profileDelta : ℝ) :=
  TerminalSkeletonData
      (terminalCount scale profileDelta + terminalCount scale profileDelta) ×
    (Fin (terminalCount scale profileDelta + terminalCount scale profileDelta) ≃
      Fin (terminalCount scale profileDelta + terminalCount scale profileDelta))

/-- One marked branch stores endpoints and the terminal visit vector, but no
copy of the shared complementary word. -/
abbrev CoarseTerminalMarkedBranchCode (m : ℕ) :=
  TerminalBranchCode m × (Fin m → ℕ)

/-- Coarse unmarked pair code. -/
abbrev CoarseSharedPairSkeletonCode (scale : ℕ) (profileDelta : ℝ) :=
  SharedPrefixPairPartition.PairData
    (CoarsePairCommonCode scale profileDelta)
    (TerminalBranchCode (terminalCount scale profileDelta))
    (TerminalBranchCode (terminalCount scale profileDelta))

/-- Coarse marked pair code. -/
abbrev CoarseSharedPairMarkedCode (scale : ℕ) (profileDelta : ℝ) :=
  SharedPrefixPairPartition.PairData
    (CoarsePairCommonCode scale profileDelta)
    (CoarseTerminalMarkedBranchCode (terminalCount scale profileDelta))
    (CoarseTerminalMarkedBranchCode (terminalCount scale profileDelta))

theorem countable_coarseSharedPairSkeletonCode
    (scale : ℕ) (profileDelta : ℝ) :
    Countable (CoarseSharedPairSkeletonCode scale profileDelta) :=
  inferInstance

theorem countable_coarseSharedPairMarkedCode
    (scale : ℕ) (profileDelta : ℝ) :
    Countable (CoarseSharedPairMarkedCode scale profileDelta) :=
  inferInstance

/-- Endpoint/visit projection of a one-point marked terminal code. -/
def coarseTerminalMarkedBranchCode
    {m : ℕ}
    (code : MarkedSkeletonPartition.MarkedIndex
      (TerminalSkeletonData m) Point Point m) :
    CoarseTerminalMarkedBranchCode m :=
  ((code.2.1, code.2.2.1), code.2.2.2)

/-- The actual shared complementary data of two fixed-horizon terminal
extractors. -/
def fixedCoarsePairCommonCode
    (scale horizon : ℕ) (profileDelta : ℝ) (x y : Point)
    (omega : StepPath) : CoarsePairCommonCode scale profileDelta :=
  let left := extractTimedTerminalSkeleton scale horizon profileDelta x omega
  let right := extractTimedTerminalSkeleton scale horizon profileDelta y omega
  ((compressTimedSkeleton omega
      (mergeTimedTerminalSkeleton left right)).1,
    chronologicalEquiv left right)

/-- Fixed-horizon unmarked coarse extraction from the post-`start` walk. -/
def fixedCoarseSharedPairSkeletonCode
    (start scale horizon : ℕ) (profileDelta : ℝ) (x y : Point)
    (omega : StepPath) : CoarseSharedPairSkeletonCode scale profileDelta :=
  let tail := shiftSteps start omega
  let left := extractTerminalSkeletonCode scale horizon profileDelta x tail
  let right := extractTerminalSkeletonCode scale horizon profileDelta y tail
  (fixedCoarsePairCommonCode scale horizon profileDelta x y tail,
    (terminalBranchCode left, terminalBranchCode right))

/-- Fixed-horizon marked coarse extraction from the same shared packet. -/
def fixedCoarseSharedPairMarkedCode
    (start scale horizon : ℕ) (profileDelta : ℝ) (x y : Point)
    (omega : StepPath) : CoarseSharedPairMarkedCode scale profileDelta :=
  let tail := shiftSteps start omega
  let left := extractMarkedTerminalCode scale horizon profileDelta x tail
  let right := extractMarkedTerminalCode scale horizon profileDelta y tail
  (fixedCoarsePairCommonCode scale horizon profileDelta x y tail,
    (coarseTerminalMarkedBranchCode left,
      coarseTerminalMarkedBranchCode right))

/-- The two coarse codes genuinely share the same one-copy complementary
datum; marking only appends branch visit vectors. -/
@[simp] theorem fixedCoarseSharedPairMarkedCode_common
    (start scale horizon : ℕ) (profileDelta : ℝ) (x y : Point)
    (omega : StepPath) :
    (fixedCoarseSharedPairMarkedCode start scale horizon
      profileDelta x y omega).1 =
      (fixedCoarseSharedPairSkeletonCode start scale horizon
        profileDelta x y omega).1 := rfl

/-- The visit vector actually recorded on the left branch. -/
def fixedCoarsePairLeftVisits
    (start scale horizon : ℕ) (profileDelta : ℝ) (x : Point)
    (omega : StepPath) : Fin (terminalCount scale profileDelta) → ℕ :=
  terminalVisitVector (trajectory (shiftSteps start omega))
    scale horizon profileDelta x

/-- The visit vector actually recorded on the right branch. -/
def fixedCoarsePairRightVisits
    (start scale horizon : ℕ) (profileDelta : ℝ) (y : Point)
    (omega : StepPath) : Fin (terminalCount scale profileDelta) → ℕ :=
  terminalVisitVector (trajectory (shiftSteps start omega))
    scale horizon profileDelta y

/-- The existing no-`hfirst` unmarked insertion atom, specialized to the
post-`start` walk from which the coarse code is extracted. -/
def coarsePairUnmarkedInsertionAtom
    {start scale horizon : ℕ} {profileDelta : ℝ} {x y : Point}
    {omega : StepPath}
    (hscale : 1 ≤ scale)
    (hlevel : separationLevel scale x y ≤ scale)
    (hexit : IsOuterExitTime
      (trajectory (shiftSteps start omega)) scale horizon)
    (hx : SuccessfulPoint (trajectory (shiftSteps start omega))
      scale horizon profileDelta x)
    (hy : SuccessfulPoint (trajectory (shiftSteps start omega))
      scale horizon profileDelta y)
    (hxbox : x ∈ candidateBox scale) (hybox : y ∈ candidateBox scale) :=
  extractedLogicalPairComplementarySkeletonAtom
    (start := start) (omega := shiftSteps start omega)
    hscale hlevel hexit hx hy hxbox hybox

/-- Marked insertion atom using exactly the left/right visit vectors stored
by `fixedCoarseSharedPairMarkedCode`. -/
def coarsePairMarkedInsertionAtom
    {start scale horizon : ℕ} {profileDelta : ℝ} {x y : Point}
    {omega : StepPath}
    (hscale : 1 ≤ scale)
    (hlevel : separationLevel scale x y ≤ scale)
    (hexit : IsOuterExitTime
      (trajectory (shiftSteps start omega)) scale horizon)
    (hx : SuccessfulPoint (trajectory (shiftSteps start omega))
      scale horizon profileDelta x)
    (hy : SuccessfulPoint (trajectory (shiftSteps start omega))
      scale horizon profileDelta y)
    (hxbox : x ∈ candidateBox scale) (hybox : y ∈ candidateBox scale) :=
  extractedLogicalPairMarkedComplementarySkeletonAtom
    (start := start) (omega := shiftSteps start omega)
    (fixedCoarsePairLeftVisits start scale horizon profileDelta x omega)
    (fixedCoarsePairRightVisits start scale horizon profileDelta y omega)
    hscale hlevel hexit hx hy hxbox hybox

/-- The source-specialized marked and unmarked atoms use the identical
common retained word. -/
@[simp] theorem coarsePairMarkedInsertionAtom_complementWord
    {start scale horizon : ℕ} {profileDelta : ℝ} {x y : Point}
    {omega : StepPath}
    (hscale : 1 ≤ scale)
    (hlevel : separationLevel scale x y ≤ scale)
    (hexit : IsOuterExitTime
      (trajectory (shiftSteps start omega)) scale horizon)
    (hx : SuccessfulPoint (trajectory (shiftSteps start omega))
      scale horizon profileDelta x)
    (hy : SuccessfulPoint (trajectory (shiftSteps start omega))
      scale horizon profileDelta y)
    (hxbox : x ∈ candidateBox scale) (hybox : y ∈ candidateBox scale)
    (pre : Fin start → Direction) :
    (coarsePairMarkedInsertionAtom hscale hlevel hexit hx hy
      hxbox hybox).complementWord pre =
      (coarsePairUnmarkedInsertionAtom hscale hlevel hexit hx hy
        hxbox hybox).complementWord pre := rfl

/-- Every extracted terminal entrance uses only the stopped prefix through
the sentinel increment `horizon`. -/
theorem extractTimedTerminalSkeleton_entrance_le_sentinel
    (scale horizon : ℕ) (profileDelta : ℝ) (x : Point)
    (omega : StepPath) (j : Fin (terminalCount scale profileDelta)) :
    (extractTimedTerminalSkeleton scale horizon profileDelta x omega).entrance j ≤
      horizon + 1 := by
  classical
  exact firstHitThrough_le_sentinel (trajectory omega)
    (terminalInnerBoundary scale x)
    (excursionStart (trajectory omega) (terminalOuterBoundary scale x)
      (terminalInnerBoundary scale x) horizon j) horizon

/-- Hence every entrance in the merged chronological family has the same
finite-prefix bound, without a success or well-formedness assumption. -/
theorem extractMergedTimedTerminalSkeleton_entrance_le_sentinel
    (scale horizon : ℕ) (profileDelta : ℝ) (x y : Point)
    (omega : StepPath)
    (k : Fin (terminalCount scale profileDelta +
      terminalCount scale profileDelta)) :
    (extractMergedTimedTerminalSkeleton scale horizon profileDelta x y omega).entrance k ≤
      horizon + 1 := by
  let left := extractTimedTerminalSkeleton scale horizon profileDelta x omega
  let right := extractTimedTerminalSkeleton scale horizon profileDelta y omega
  let q := chronologicalEquiv left right k
  have hq : pairEntrance left right q ≤ horizon + 1 := by
    obtain ⟨i | j, hqi⟩ := finSumFinEquiv.surjective q
    · rw [← hqi]
      unfold pairEntrance
      rw [finSumFinEquiv_apply_left, pairValue_castAdd]
      simpa [left] using
        extractTimedTerminalSkeleton_entrance_le_sentinel
          scale horizon profileDelta x omega i
    · rw [← hqi]
      unfold pairEntrance
      rw [finSumFinEquiv_apply_right, pairValue_natAdd]
      simpa [right] using
        extractTimedTerminalSkeleton_entrance_le_sentinel
          scale horizon profileDelta y omega j
  simpa [extractMergedTimedTerminalSkeleton, mergeTimedTerminalSkeleton,
    chronologicalValues, left, right, q] using hq

/-- The merged timed extractor is determined by the stopped finite prefix. -/
theorem extractMergedTimedTerminalSkeleton_congr_prefix
    {scale horizon : ℕ} {profileDelta : ℝ} {x y : Point}
    {omega omega' : StepPath}
    (hprefix : ∀ k < horizon + 1, omega k = omega' k) :
    extractMergedTimedTerminalSkeleton scale horizon profileDelta x y omega =
      extractMergedTimedTerminalSkeleton scale horizon profileDelta x y omega' := by
  unfold extractMergedTimedTerminalSkeleton
  rw [extractTimedTerminalSkeleton_congr_prefix hprefix,
    extractTimedTerminalSkeleton_congr_prefix hprefix]

/-- The complete compressed common datum, including its chronological order,
is determined by the same finite prefix. -/
theorem fixedCoarsePairCommonCode_congr_prefix
    {scale horizon : ℕ} {profileDelta : ℝ} {x y : Point}
    {omega omega' : StepPath}
    (hprefix : ∀ k < horizon + 1, omega k = omega' k) :
    fixedCoarsePairCommonCode scale horizon profileDelta x y omega =
      fixedCoarsePairCommonCode scale horizon profileDelta x y omega' := by
  let left :=
    extractTimedTerminalSkeleton scale horizon profileDelta x omega
  let right :=
    extractTimedTerminalSkeleton scale horizon profileDelta y omega
  let left' :=
    extractTimedTerminalSkeleton scale horizon profileDelta x omega'
  let right' :=
    extractTimedTerminalSkeleton scale horizon profileDelta y omega'
  have hleft : left = left' :=
    extractTimedTerminalSkeleton_congr_prefix hprefix
  have hright : right = right' :=
    extractTimedTerminalSkeleton_congr_prefix hprefix
  let merged :=
    mergeTimedTerminalSkeleton left right
  let merged' :=
    mergeTimedTerminalSkeleton left' right'
  have hmerged : merged = merged' := by
    dsimp only [merged, merged']
    rw [hleft, hright]
  have horder : chronologicalEquiv left right =
      chronologicalEquiv left' right' := by
    rw [hleft, hright]
  have hdata : (compressTimedSkeleton omega merged).1 =
      (compressTimedSkeleton omega' merged').1 := by
    rw [hmerged]
    apply TerminalSkeletonData.ext
    exact complementaryPieces_congr _ merged'.entrance merged'.exit hprefix
      (Nat.le_succ horizon)
      (extractMergedTimedTerminalSkeleton_entrance_le_sentinel
        scale horizon profileDelta x y omega')
  unfold fixedCoarsePairCommonCode
  change ((compressTimedSkeleton omega merged).1,
      chronologicalEquiv left right) =
    ((compressTimedSkeleton omega' merged').1,
      chronologicalEquiv left' right')
  exact Prod.ext hdata horder

private lemma shiftSteps_congr_of_prefix
    {start horizon : ℕ} {omega omega' : StepPath}
    (hprefix : ∀ k < start + (horizon + 1), omega k = omega' k) :
    ∀ k < horizon + 1,
      shiftSteps start omega k = shiftSteps start omega' k := by
  intro k hk
  unfold shiftSteps
  exact hprefix (start + k) (by omega)

theorem fixedCoarseSharedPairSkeletonCode_congr_prefix
    {start scale horizon : ℕ} {profileDelta : ℝ} {x y : Point}
    {omega omega' : StepPath}
    (hprefix : ∀ k < start + (horizon + 1), omega k = omega' k) :
    fixedCoarseSharedPairSkeletonCode start scale horizon profileDelta x y omega =
      fixedCoarseSharedPairSkeletonCode start scale horizon profileDelta x y omega' := by
  have htail := shiftSteps_congr_of_prefix hprefix
  have hcommon := fixedCoarsePairCommonCode_congr_prefix
    (scale := scale) (profileDelta := profileDelta) (x := x) (y := y) htail
  have hleft := extractTerminalSkeletonCode_congr_prefix
    (scale := scale) (profileDelta := profileDelta) (x := x) htail
  have hright := extractTerminalSkeletonCode_congr_prefix
    (scale := scale) (profileDelta := profileDelta) (x := y) htail
  dsimp only [fixedCoarseSharedPairSkeletonCode]
  rw [hcommon, hleft, hright]

theorem fixedCoarseSharedPairMarkedCode_congr_prefix
    {start scale horizon : ℕ} {profileDelta : ℝ} {x y : Point}
    {omega omega' : StepPath}
    (hprefix : ∀ k < start + (horizon + 1), omega k = omega' k) :
    fixedCoarseSharedPairMarkedCode start scale horizon profileDelta x y omega =
      fixedCoarseSharedPairMarkedCode start scale horizon profileDelta x y omega' := by
  have htail := shiftSteps_congr_of_prefix hprefix
  have hcommon := fixedCoarsePairCommonCode_congr_prefix
    (scale := scale) (profileDelta := profileDelta) (x := x) (y := y) htail
  have hleft := extractMarkedTerminalCode_congr_prefix
    (scale := scale) (profileDelta := profileDelta) (x := x) htail
  have hright := extractMarkedTerminalCode_congr_prefix
    (scale := scale) (profileDelta := profileDelta) (x := y) htail
  dsimp only [fixedCoarseSharedPairMarkedCode]
  rw [hcommon, hleft, hright]

theorem measurableSet_fixedCoarseSharedPairSkeletonCode_fiber
    (start scale horizon : ℕ) (profileDelta : ℝ) (x y : Point)
    (code : CoarseSharedPairSkeletonCode scale profileDelta) :
    MeasurableSet {omega : StepPath |
      fixedCoarseSharedPairSkeletonCode start scale horizon
        profileDelta x y omega = code} := by
  let N := start + (horizon + 1)
  let C : Set (Fin N → Direction) :=
    {word | fixedCoarseSharedPairSkeletonCode start scale horizon
      profileDelta x y (extendFiniteDirectionWord word) = code}
  have hC : MeasurableSet C := (Set.to_countable C).measurableSet
  have heq : {omega : StepPath |
      fixedCoarseSharedPairSkeletonCode start scale horizon
        profileDelta x y omega = code} = stepPrefix N ⁻¹' C := by
    ext omega
    change fixedCoarseSharedPairSkeletonCode start scale horizon
        profileDelta x y omega = code ↔
      fixedCoarseSharedPairSkeletonCode start scale horizon profileDelta x y
        (extendFiniteDirectionWord (stepPrefix N omega)) = code
    have hcongr := fixedCoarseSharedPairSkeletonCode_congr_prefix
      (start := start) (scale := scale) (horizon := horizon)
      (profileDelta := profileDelta) (x := x) (y := y)
      (omega := omega)
      (omega' := extendFiniteDirectionWord (stepPrefix N omega))
      (fun k hk ↦ by simp [N, extendFiniteDirectionWord, stepPrefix, hk])
    rw [hcongr]
  rw [heq]
  exact (measurable_stepPrefix N) hC

theorem measurableSet_fixedCoarseSharedPairMarkedCode_fiber
    (start scale horizon : ℕ) (profileDelta : ℝ) (x y : Point)
    (code : CoarseSharedPairMarkedCode scale profileDelta) :
    MeasurableSet {omega : StepPath |
      fixedCoarseSharedPairMarkedCode start scale horizon
        profileDelta x y omega = code} := by
  let N := start + (horizon + 1)
  let C : Set (Fin N → Direction) :=
    {word | fixedCoarseSharedPairMarkedCode start scale horizon
      profileDelta x y (extendFiniteDirectionWord word) = code}
  have hC : MeasurableSet C := (Set.to_countable C).measurableSet
  have heq : {omega : StepPath |
      fixedCoarseSharedPairMarkedCode start scale horizon
        profileDelta x y omega = code} = stepPrefix N ⁻¹' C := by
    ext omega
    change fixedCoarseSharedPairMarkedCode start scale horizon
        profileDelta x y omega = code ↔
      fixedCoarseSharedPairMarkedCode start scale horizon profileDelta x y
        (extendFiniteDirectionWord (stepPrefix N omega)) = code
    have hcongr := fixedCoarseSharedPairMarkedCode_congr_prefix
      (start := start) (scale := scale) (horizon := horizon)
      (profileDelta := profileDelta) (x := x) (y := y)
      (omega := omega)
      (omega' := extendFiniteDirectionWord (stepPrefix N omega))
      (fun k hk ↦ by simp [N, extendFiniteDirectionWord, stepPrefix, hk])
    rw [hcongr]
  rw [heq]
  exact (measurable_stepPrefix N) hC

/-- Collapse the unique stopped outer-exit horizon, without storing the
complete stopped outer word in the resulting code. -/
def stoppedCoarseSharedPairSkeletonCode
    (start scale : ℕ) (profileDelta : ℝ) (x y : Point)
    (omega : StepPath) : CoarseSharedPairSkeletonCode scale profileDelta :=
  fixedCoarseSharedPairSkeletonCode start scale
    (stoppedOuterExitHorizon start scale omega) profileDelta x y omega

/-- Marked horizon-collapsed coarse pair code. -/
def stoppedCoarseSharedPairMarkedCode
    (start scale : ℕ) (profileDelta : ℝ) (x y : Point)
    (omega : StepPath) : CoarseSharedPairMarkedCode scale profileDelta :=
  fixedCoarseSharedPairMarkedCode start scale
    (stoppedOuterExitHorizon start scale omega) profileDelta x y omega

theorem measurableSet_stoppedCoarseSharedPairSkeletonCode_fiber
    (start scale : ℕ) (profileDelta : ℝ) (x y : Point)
    (code : CoarseSharedPairSkeletonCode scale profileDelta) :
    MeasurableSet {omega : StepPath |
      stoppedCoarseSharedPairSkeletonCode start scale profileDelta x y omega =
        code} := by
  have heq : {omega : StepPath |
      stoppedCoarseSharedPairSkeletonCode start scale profileDelta x y omega =
        code} =
      ⋃ horizon : ℕ,
        {omega | stoppedOuterExitHorizon start scale omega = horizon} ∩
          {omega | fixedCoarseSharedPairSkeletonCode start scale horizon
            profileDelta x y omega = code} := by
    ext omega
    simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_ofPred_eq]
    constructor
    · intro hcode
      exact ⟨stoppedOuterExitHorizon start scale omega, rfl, hcode⟩
    · rintro ⟨horizon, hhorizon, hcode⟩
      unfold stoppedCoarseSharedPairSkeletonCode
      rwa [hhorizon]
  rw [heq]
  exact MeasurableSet.iUnion fun horizon ↦
    (measurableSet_stoppedOuterExitHorizon_eq start scale horizon).inter
      (measurableSet_fixedCoarseSharedPairSkeletonCode_fiber
        start scale horizon profileDelta x y code)

theorem measurableSet_stoppedCoarseSharedPairMarkedCode_fiber
    (start scale : ℕ) (profileDelta : ℝ) (x y : Point)
    (code : CoarseSharedPairMarkedCode scale profileDelta) :
    MeasurableSet {omega : StepPath |
      stoppedCoarseSharedPairMarkedCode start scale profileDelta x y omega =
        code} := by
  have heq : {omega : StepPath |
      stoppedCoarseSharedPairMarkedCode start scale profileDelta x y omega =
        code} =
      ⋃ horizon : ℕ,
        {omega | stoppedOuterExitHorizon start scale omega = horizon} ∩
          {omega | fixedCoarseSharedPairMarkedCode start scale horizon
            profileDelta x y omega = code} := by
    ext omega
    simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_ofPred_eq]
    constructor
    · intro hcode
      exact ⟨stoppedOuterExitHorizon start scale omega, rfl, hcode⟩
    · rintro ⟨horizon, hhorizon, hcode⟩
      unfold stoppedCoarseSharedPairMarkedCode
      rwa [hhorizon]
  rw [heq]
  exact MeasurableSet.iUnion fun horizon ↦
    (measurableSet_stoppedOuterExitHorizon_eq start scale horizon).inter
      (measurableSet_fixedCoarseSharedPairMarkedCode_fiber
        start scale horizon profileDelta x y code)

/-- Successful at both centres, restricted to the deterministic far regime. -/
def stoppedSeparatedSuccessfulPairEvent
    (start scale : ℕ) (profileDelta : ℝ) (x y : Point) : Set StepPath :=
  if separationLevel scale x y ≤ scale then
    stoppedSuccessfulPairEvent start scale profileDelta x y else ∅

theorem measurableSet_stoppedSeparatedSuccessfulPairEvent
    (start scale : ℕ) (profileDelta : ℝ) (x y : Point) :
    MeasurableSet
      (stoppedSeparatedSuccessfulPairEvent start scale profileDelta x y) := by
  unfold stoppedSeparatedSuccessfulPairEvent
  split_ifs
  · exact measurableSet_stoppedSuccessfulPairEvent
      start scale profileDelta x y
  · exact MeasurableSet.empty

@[simp] theorem stoppedSeparatedSuccessfulPairEvent_eq
    {start scale : ℕ} {profileDelta : ℝ} {x y : Point}
    (hlevel : separationLevel scale x y ≤ scale) :
    stoppedSeparatedSuccessfulPairEvent start scale profileDelta x y =
      stoppedSuccessfulPairEvent start scale profileDelta x y := by
  simp [stoppedSeparatedSuccessfulPairEvent, hlevel]

/-- One coarse unmarked fibre on the separated successful source. -/
def stoppedCoarseSharedPairSkeletonAtom
    (start scale : ℕ) (profileDelta : ℝ) (x y : Point)
    (code : CoarseSharedPairSkeletonCode scale profileDelta) : Set StepPath :=
  codingFiber
    (stoppedSeparatedSuccessfulPairEvent start scale profileDelta x y)
    (stoppedCoarseSharedPairSkeletonCode start scale profileDelta x y) code

/-- One coarse marked fibre on the separated successful source. -/
def stoppedCoarseSharedPairMarkedAtom
    (start scale : ℕ) (profileDelta : ℝ) (x y : Point)
    (code : CoarseSharedPairMarkedCode scale profileDelta) : Set StepPath :=
  codingFiber
    (stoppedSeparatedSuccessfulPairEvent start scale profileDelta x y)
    (stoppedCoarseSharedPairMarkedCode start scale profileDelta x y) code

theorem measurableSet_stoppedCoarseSharedPairSkeletonAtom
    (start scale : ℕ) (profileDelta : ℝ) (x y : Point)
    (code : CoarseSharedPairSkeletonCode scale profileDelta) :
    MeasurableSet
      (stoppedCoarseSharedPairSkeletonAtom
        start scale profileDelta x y code) :=
  codingFiber_measurable
    (measurableSet_stoppedSeparatedSuccessfulPairEvent
      start scale profileDelta x y)
    (fun c ↦ measurableSet_stoppedCoarseSharedPairSkeletonCode_fiber
      start scale profileDelta x y c) code

theorem measurableSet_stoppedCoarseSharedPairMarkedAtom
    (start scale : ℕ) (profileDelta : ℝ) (x y : Point)
    (code : CoarseSharedPairMarkedCode scale profileDelta) :
    MeasurableSet
      (stoppedCoarseSharedPairMarkedAtom
        start scale profileDelta x y code) :=
  codingFiber_measurable
    (measurableSet_stoppedSeparatedSuccessfulPairEvent
      start scale profileDelta x y)
    (fun c ↦ measurableSet_stoppedCoarseSharedPairMarkedCode_fiber
      start scale profileDelta x y c) code

theorem stoppedCoarseSharedPairSkeletonAtom_pairwise
    (start scale : ℕ) (profileDelta : ℝ) (x y : Point) :
    Pairwise fun i j : CoarseSharedPairSkeletonCode scale profileDelta ↦
      Disjoint
        (stoppedCoarseSharedPairSkeletonAtom
          start scale profileDelta x y i)
        (stoppedCoarseSharedPairSkeletonAtom
          start scale profileDelta x y j) :=
  codingFiber_pairwise _ _

theorem stoppedCoarseSharedPairMarkedAtom_pairwise
    (start scale : ℕ) (profileDelta : ℝ) (x y : Point) :
    Pairwise fun i j : CoarseSharedPairMarkedCode scale profileDelta ↦
      Disjoint
        (stoppedCoarseSharedPairMarkedAtom
          start scale profileDelta x y i)
        (stoppedCoarseSharedPairMarkedAtom
          start scale profileDelta x y j) :=
  codingFiber_pairwise _ _

/-- Exact disjoint fibre cover of the separated successful-pair source. -/
theorem stoppedSeparatedSuccessfulPairEvent_eq_iUnion_coarseSkeletonAtoms
    (start scale : ℕ) (profileDelta : ℝ) (x y : Point) :
    stoppedSeparatedSuccessfulPairEvent start scale profileDelta x y =
      ⋃ code : CoarseSharedPairSkeletonCode scale profileDelta,
        stoppedCoarseSharedPairSkeletonAtom
          start scale profileDelta x y code := by
  symm
  exact iUnion_codingFiber _ _

/-- Marked exact disjoint fibre cover of the same source. -/
theorem stoppedSeparatedSuccessfulPairEvent_eq_iUnion_coarseMarkedAtoms
    (start scale : ℕ) (profileDelta : ℝ) (x y : Point) :
    stoppedSeparatedSuccessfulPairEvent start scale profileDelta x y =
      ⋃ code : CoarseSharedPairMarkedCode scale profileDelta,
        stoppedCoarseSharedPairMarkedAtom
          start scale profileDelta x y code := by
  symm
  exact iUnion_codingFiber _ _

end

end Erdos1165.SharedPrefixPairCoarsePartition
