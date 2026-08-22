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

import ErdosProblems.Erdos1165.AnnularBridgeFactorization
import ErdosProblems.Erdos1165.AnnularProfileGapAtoms
import ErdosProblems.Erdos1165.TerminalSkeletonWords

/-!
# One-level complementary skeletons for an annular profile

At one fixed profile scale, the erased inner-to-outer gaps are chronological
and disjoint.  This file packages their actual clocks in the generic timed
skeleton representation and proves that every extracted word is precisely a
canonical count/endpoint word for the Appendix-A.6 kernel.

The construction is deliberately one-level: gaps at adjacent profile scales
are nested and must be disintegrated recursively, not flattened into a single
family of disjoint intervals.
-/

open Set

namespace Erdos1165.AnnularProfileLevelSkeleton

noncomputable section

open ThickPoint PlanarPotential TerminalExcursionPathwise TerminalSkeletonWords
open TerminalSequentialVisitLaw
open MarkedBridgeFactorization AnnularBoundaryExcursionKernel
open AnnularProfileClocks AnnularProfileGapAtoms

/-- The gap following parent excursion `i` ends before the inner hit of every
strictly later parent excursion. -/
lemma profileGapExitTime_le_profileInnerHitTime_of_lt
    (s : WalkPath) (n horizon : ℕ) (x : Point) (k : ℕ)
    {i j : ℕ} (hij : i < j) :
    profileGapExitTime s n horizon x k i ≤
      profileInnerHitTime s n horizon x k j := by
  classical
  unfold profileGapExitTime profileOuterHitTime profileInnerHitTime
  exact (excursionStart_le_finish s
      (profileOuterBoundary n k x) (profileInnerBoundary n k x)
      horizon (i + 1)).trans
    (excursionFinish_mono s
      (profileOuterBoundary n k x) (profileInnerBoundary n k x)
      horizon (Nat.succ_le_iff.mpr hij))

/-- Literal timed intervals for the first `parents` complete gaps at one
profile scale. -/
def extractTimedProfileLevelSkeleton
    (omega : StepPath) (n horizon : ℕ) (x : Point)
    (k parents : ℕ) : TimedTerminalSkeleton parents where
  horizon := horizon
  entrance := fun j ↦
    profileInnerHitTime (trajectory omega) n horizon x k j
  exit := fun j ↦
    profileGapExitTime (trajectory omega) n horizon x k j
  entrancePoint := fun j ↦
    profileGapStartPoint omega n horizon x k j
  exitPoint := fun j ↦
    profileGapExitPoint omega n horizon x k j

/-- Completion of every selected gap is exactly what is needed for the
single-level timed skeleton to be well formed. -/
theorem extractTimedProfileLevelSkeleton_wellFormed
    {omega : StepPath} {n horizon : ℕ} {x : Point}
    {k parents : ℕ}
    (hcomplete : ∀ j : Fin parents,
      profileGapExitTime (trajectory omega) n horizon x k j ≤ horizon) :
    (extractTimedProfileLevelSkeleton omega n horizon x k parents).WellFormed := by
  constructor
  · intro j
    exact ⟨profileInnerHitTime_le_profileGapExitTime
      (trajectory omega) n horizon x k j, hcomplete j⟩
  · intro i j hij
    exact profileGapExitTime_le_profileInnerHitTime_of_lt
      (trajectory omega) n horizon x k hij

/-- The exact stopped word cut out by one actual profile gap. -/
def profileGapStoppedWord
    (omega : StepPath) (n horizon : ℕ) (x : Point)
    (k j : ℕ) : StoppedWord :=
  ⟨profileGapLength omega n horizon x k j,
    stepPrefix (profileGapLength omega n horizon x k j)
      (profileGapFreshPath omega n horizon x k j)⟩

@[simp] theorem profileGapStoppedWord_length
    (omega : StepPath) (n horizon : ℕ) (x : Point)
    (k j : ℕ) :
    (profileGapStoppedWord omega n horizon x k j).1 =
      profileGapLength omega n horizon x k j := rfl

lemma profileGapFreshPath_mem_stoppedWordCylinder
    (omega : StepPath) (n horizon : ℕ) (x : Point)
    (k j : ℕ) :
    profileGapFreshPath omega n horizon x k j ∈
      stoppedWordCylinder (profileGapStoppedWord omega n horizon x k j) := by
  rfl

/-- The extracted finite gap word itself, rather than merely the infinite
fresh tail containing it, is a canonical literal count/endpoint code. -/
def profileGapBoundaryExcursionWordCode
    {omega : StepPath} {n horizon : ℕ} {x : Point} {k j : ℕ}
    (hcomplete : profileGapExitTime (trajectory omega) n horizon x k j ≤
      horizon) :
    BoundaryExcursionExitWordCode
      (profileOuterBoundary n k x)
      (profileInnerBoundary n k x)
      (profileInnerBoundary n (k + 1) x)
      (profileGapStartPoint omega n horizon x k j)
      (profileGapOffspringCount omega n horizon x k j)
      (profileGapExitPoint omega n horizon x k j) := by
  let word := profileGapStoppedWord omega n horizon x k j
  let fresh := profileGapFreshPath omega n horizon x k j
  have hmem : fresh ∈ stoppedWordCylinder word :=
    profileGapFreshPath_mem_stoppedWordCylinder omega n horizon x k j
  have hfirstActual := profileGap_absoluteBoundaryFirstAt hcomplete
  have htrajectory (q : ℕ) (hq : q ≤ word.1) :
      trajectoryFrom (profileGapStartPoint omega n horizon x k j)
          fresh q =
        trajectoryFrom (profileGapStartPoint omega n horizon x k j)
          (extendStoppedWord word) q :=
    trajectoryFrom_eq_extendStoppedWord_of_mem hmem _ hq
  have hfirst : AbsoluteBoundaryFirstAt (profileOuterBoundary n k x)
      (profileGapStartPoint omega n horizon x k j)
      (extendStoppedWord word) word.1 := by
    constructor
    · rw [← htrajectory word.1 le_rfl]
      exact hfirstActual.1
    · intro q hq
      rw [← htrajectory q hq.le]
      exact hfirstActual.2 q hq
  have hcount : boundaryExcursionCount
      (profileInnerBoundary n k x)
      (profileInnerBoundary n (k + 1) x)
      (profileGapStartPoint omega n horizon x k j)
      (extendStoppedWord word) word.1 =
        profileGapOffspringCount omega n horizon x k j := by
    symm
    apply boundaryExcursionCount_congr_prefix
    intro q hq
    exact htrajectory q hq
  have hexit : trajectoryFrom
      (profileGapStartPoint omega n horizon x k j)
      (extendStoppedWord word) word.1 =
        profileGapExitPoint omega n horizon x k j := by
    rw [← htrajectory word.1 le_rfl]
    have hactual :=
      profileGapFreshPath_mem_boundaryExcursionExitAtom hcomplete
    obtain ⟨gapHorizon, _hgapFirst, _hgapCount, hgapExit⟩ :=
      Set.mem_iUnion.mp hactual
    have hgapLength : gapHorizon = word.1 := by
      apply absoluteBoundaryFirstAt_unique _ hfirstActual
      exact _hgapFirst
    simpa only [hgapLength] using hgapExit
  exact ⟨word, hfirst, hcount, hexit⟩

@[simp] theorem profileGapBoundaryExcursionWordCode_val
    {omega : StepPath} {n horizon : ℕ} {x : Point} {k j : ℕ}
    (hcomplete : profileGapExitTime (trajectory omega) n horizon x k j ≤
      horizon) :
    (profileGapBoundaryExcursionWordCode hcomplete).1 =
      profileGapStoppedWord omega n horizon x k j := rfl

/-- Boundary-supported entrance states for one intermediate profile level. -/
abbrev ProfileLevelEntrance (n k : ℕ) (x : Point) :=
  {p : Point // p ∈ profileInnerBoundary n k x}

/-- Boundary-supported retained exit states for one intermediate level. -/
abbrev ProfileLevelExit (n k : ℕ) (x : Point) :=
  {p : Point // p ∈ profileOuterBoundary n k x}

theorem profileGapStartPoint_mem_innerBoundary
    {omega : StepPath} {n horizon : ℕ} {x : Point} {k j : ℕ}
    (hcomplete : profileGapExitTime (trajectory omega) n horizon x k j ≤
      horizon) :
    profileGapStartPoint omega n horizon x k j ∈
      profileInnerBoundary n k x := by
  apply profileInnerHit_mem_of_le
  exact (profileInnerHitTime_le_profileGapExitTime
    (trajectory omega) n horizon x k j).trans hcomplete

theorem profileGapExitPoint_mem_outerBoundary
    {omega : StepPath} {n horizon : ℕ} {x : Point} {k j : ℕ}
    (hcomplete : profileGapExitTime (trajectory omega) n horizon x k j ≤
      horizon) :
    profileGapExitPoint omega n horizon x k j ∈
      profileOuterBoundary n k x := by
  exact profileGapExit_mem_outerBoundary hcomplete

/-- The supported entrance vector carried by a completed one-level timed
skeleton. -/
def supportedProfileLevelEntrances
    {omega : StepPath} {n horizon : ℕ} {x : Point} {k parents : ℕ}
    (hcomplete : ∀ j : Fin parents,
      profileGapExitTime (trajectory omega) n horizon x k j ≤ horizon) :
    Fin parents → ProfileLevelEntrance n k x := fun j ↦
  ⟨profileGapStartPoint omega n horizon x k j,
    profileGapStartPoint_mem_innerBoundary (hcomplete j)⟩

/-- The supported retained outer-endpoint vector. -/
def supportedProfileLevelExits
    {omega : StepPath} {n horizon : ℕ} {x : Point} {k parents : ℕ}
    (hcomplete : ∀ j : Fin parents,
      profileGapExitTime (trajectory omega) n horizon x k j ≤ horizon) :
    Fin parents → ProfileLevelExit n k x := fun j ↦
  ⟨profileGapExitPoint omega n horizon x k j,
    profileGapExitPoint_mem_outerBoundary (hcomplete j)⟩

/-- Exact erasure/reinsertion identity for the disjoint gaps of one profile
level.  This is a finite-word identity, before any probabilistic estimate. -/
theorem reconstruct_extractedProfileLevelSkeleton
    {omega : StepPath} {n horizon : ℕ} {x : Point} {k parents : ℕ}
    (hcomplete : ∀ j : Fin parents,
      profileGapExitTime (trajectory omega) n horizon x k j ≤ horizon) :
    reconstructTerminalPacket
        (packetOfTimedSkeleton omega
          (extractTimedProfileLevelSkeleton omega n horizon x k parents)) =
      incrementSlice omega 0 horizon := by
  exact reconstruct_packetOfTimedSkeleton omega
    (extractTimedProfileLevelSkeleton omega n horizon x k parents)
    (extractTimedProfileLevelSkeleton_wellFormed hcomplete)

/-- For a fixed successful profile, all parent-gap intervals at one internal
scale form a concrete well-formed timed skeleton. -/
theorem fixedProfile_levelSkeleton_wellFormed
    {omega : StepPath} {n horizon : ℕ} {x : Point}
    {profileDelta : ℝ} {m : AppendixFirstMoment.Profile n}
    (hn : 1 ≤ n)
    (hexit : IsOuterExitTime (trajectory omega) n horizon)
    (hx : x ∈ candidateBox n)
    (hfixed : AnnularProfileLiteralAtoms.FixedSuccessfulProfile
      n profileDelta m (excursionProfile (trajectory omega) n horizon x))
    (i : Fin (n - 1)) :
    (extractTimedProfileLevelSkeleton omega n horizon x
      (AppendixFirstMoment.scaleIndex i) (m i)).WellFormed := by
  apply extractTimedProfileLevelSkeleton_wellFormed
  intro j
  exact fixedProfile_gapExit_le hn hexit hx
    (TerminalSkeletonWords.adjacent_trajectory_succ omega) hfixed i j

end

end Erdos1165.AnnularProfileLevelSkeleton
