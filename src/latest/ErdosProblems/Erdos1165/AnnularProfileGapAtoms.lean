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

import ErdosProblems.Erdos1165.AnnularBoundaryExcursionKernel

/-!
# Actual fixed-profile gaps as marked intermediate-annulus atoms

For a literal planar walk, this file extracts the fresh increment word in
each completed inner-to-outer profile gap.  It proves pathwise that the word
belongs to the joint excursion-count/outer-endpoint atom from
`AnnularBoundaryExcursionKernel`.  Thus its mark is the genuine number of
nested boundary excursions, not a target-point local time.
-/

open Set

namespace Erdos1165.AnnularProfileGapAtoms

noncomputable section

open ThickPoint PlanarPotential TerminalSequentialVisitLaw
open AnnularProfileClocks AnnularBoundaryExcursionKernel

def profileGapLength
    (omega : StepPath) (n horizon : ℕ) (x : Point) (k j : ℕ) : ℕ :=
  profileGapExitTime (trajectory omega) n horizon x k j -
    profileInnerHitTime (trajectory omega) n horizon x k j

def profileGapFreshPath
    (omega : StepPath) (n horizon : ℕ) (x : Point) (k j : ℕ) : StepPath :=
  shiftSteps (profileInnerHitTime (trajectory omega) n horizon x k j) omega

def profileGapStartPoint
    (omega : StepPath) (n horizon : ℕ) (x : Point) (k j : ℕ) : Point :=
  trajectory omega (profileInnerHitTime (trajectory omega) n horizon x k j)

def profileGapExitPoint
    (omega : StepPath) (n horizon : ℕ) (x : Point) (k j : ℕ) : Point :=
  trajectory omega (profileGapExitTime (trajectory omega) n horizon x k j)

/-- Genuine number of scale-`k+1` excursions inside one scale-`k` gap. -/
def profileGapOffspringCount
    (omega : StepPath) (n horizon : ℕ) (x : Point) (k j : ℕ) : ℕ :=
  boundaryExcursionCount
    (profileInnerBoundary n k x) (profileInnerBoundary n (k + 1) x)
    (profileGapStartPoint omega n horizon x k j)
    (profileGapFreshPath omega n horizon x k j)
    (profileGapLength omega n horizon x k j)

lemma profileGap_absoluteBoundaryFirstAt
    {omega : StepPath} {n horizon : ℕ} {x : Point} {k j : ℕ}
    (hcomplete : profileGapExitTime (trajectory omega) n horizon x k j ≤
      horizon) :
    AbsoluteBoundaryFirstAt (profileOuterBoundary n k x)
      (profileGapStartPoint omega n horizon x k j)
      (profileGapFreshPath omega n horizon x k j)
      (profileGapLength omega n horizon x k j) := by
  classical
  let a := profileInnerHitTime (trajectory omega) n horizon x k j
  let b := profileGapExitTime (trajectory omega) n horizon x k j
  have hab : a ≤ b := by
    exact profileInnerHitTime_le_profileGapExitTime
      (trajectory omega) n horizon x k j
  have hfirstComplete : firstHitThrough (trajectory omega)
      (profileOuterBoundary n k x) a horizon ≤ horizon := by
    rw [← profileGapExitTime_eq_firstHitThrough]
    exact hcomplete
  have hspec := firstHitThrough_spec_of_le (trajectory omega)
    (profileOuterBoundary n k x) a horizon hfirstComplete
  have hbFirst : b = firstHitThrough (trajectory omega)
      (profileOuterBoundary n k x) a horizon := by
    exact profileGapExitTime_eq_firstHitThrough
      (trajectory omega) n horizon x k j
  unfold AbsoluteBoundaryFirstAt
  constructor
  · unfold profileGapLength profileGapStartPoint profileGapFreshPath
    rw [trajectoryFrom_shiftSteps_eq, Nat.add_sub_of_le hab]
    rw [hbFirst]
    exact hspec.2.1
  · intro q hq
    unfold profileGapLength at hq
    unfold profileGapStartPoint profileGapFreshPath
    rw [trajectoryFrom_shiftSteps_eq]
    change q < b - a at hq
    change trajectory omega (a + q) ∉ profileOuterBoundary n k x
    rw [hbFirst] at hq
    apply hspec.2.2
    · omega
    · exact Nat.le_add_right a q

/-- The actual fresh gap is a member of the correct joint A.6 atom, with
its literal offspring count and exit point. -/
theorem profileGapFreshPath_mem_boundaryExcursionExitAtom
    {omega : StepPath} {n horizon : ℕ} {x : Point} {k j : ℕ}
    (hcomplete : profileGapExitTime (trajectory omega) n horizon x k j ≤
      horizon) :
    profileGapFreshPath omega n horizon x k j ∈
      boundaryExcursionExitAtom
        (profileOuterBoundary n k x)
        (profileInnerBoundary n k x)
        (profileInnerBoundary n (k + 1) x)
        (profileGapStartPoint omega n horizon x k j)
        (profileGapOffspringCount omega n horizon x k j)
        (profileGapExitPoint omega n horizon x k j) := by
  let a := profileInnerHitTime (trajectory omega) n horizon x k j
  let b := profileGapExitTime (trajectory omega) n horizon x k j
  have hab : a ≤ b :=
    profileInnerHitTime_le_profileGapExitTime
      (trajectory omega) n horizon x k j
  apply mem_iUnion.mpr
  refine ⟨profileGapLength omega n horizon x k j,
    profileGap_absoluteBoundaryFirstAt hcomplete, rfl, ?_⟩
  unfold profileGapLength profileGapFreshPath profileGapStartPoint
    profileGapExitPoint
  rw [trajectoryFrom_shiftSteps_eq, Nat.add_sub_of_le hab]

end

end Erdos1165.AnnularProfileGapAtoms
