/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
import ErdosProblems.Erdos1165.AnnularProfileChildWordIdentification
import ErdosProblems.Erdos1165.AnnularRecursiveProfileShapeFits

/-!
# Parsing an actual completed profile segment into a recursive code

The actual offspring counts supply the weak-composition genealogy, while
the child-word identification theorem identifies every deleted parent-local
return with its parent-major global child.  This file packages those facts
into a literal recursive profile code for every actual parent gap.
-/

namespace Erdos1165.AnnularRecursiveProfileActualParser

open AnnularProfileClocks AnnularProfileGapAtoms AnnularProfileLevelSkeleton
open AnnularProfileOffspringPartition AnnularProfileChildClockIdentification
open AnnularProfileChildWordIdentification AnnularOffspringScan
open AnnularExtractedProfileSpineCode AnnularOffspringKernelRadial
open AnnularRecursiveDecoratedProfileCode AnnularRecursiveProfileCodeAssembly
open AnnularRecursiveProfileShape AnnularRecursiveProfileShapeFits
open AnnularRecursiveProfileSourceParser
open MarkedBridgeFactorization PlanarPotential ProfileGapChain ThickPoint

noncomputable section

attribute [local instance] Classical.propDecidable

/-- Exact count and completion data for a nonempty consecutive segment of
profile levels. -/
inductive ActualProfileSegmentData
    (omega : StepPath) (n horizon : ℕ) (x : Point) :
    (k : ℕ) → List ℕ → Type
  | singleton (k a : ℕ) (hpositive : 0 < a)
      (hcount : profileCompletedCount (trajectory omega) n horizon x k = a)
      (hcomplete : ∀ i < a,
        profileGapExitTime (trajectory omega) n horizon x k i ≤ horizon) :
      ActualProfileSegmentData omega n horizon x k [a]
  | cons (k a b : ℕ) (rest : List ℕ) (hpositive : 0 < a)
      (hcount : profileCompletedCount (trajectory omega) n horizon x k = a)
      (hcomplete : ∀ i < a,
        profileGapExitTime (trajectory omega) n horizon x k i ≤ horizon)
      (tail : ActualProfileSegmentData omega n horizon x (k + 1) (b :: rest)) :
      ActualProfileSegmentData omega n horizon x k (a :: b :: rest)

namespace ActualProfileSegmentData

/-- The first count in an actual segment is positive. -/
def headPositive {omega : StepPath} {n horizon : ℕ} {x : Point} :
    ∀ {k a rest}, ActualProfileSegmentData omega n horizon x k (a :: rest) →
      0 < a
  | _, _, [], .singleton _ _ hpositive _ _ => hpositive
  | _, _, _ :: _, .cons _ _ _ _ hpositive _ _ _ => hpositive

/-- The first literal count is the actual completed count at the first
segment level. -/
def headCount {omega : StepPath} {n horizon : ℕ} {x : Point} :
    ∀ {k a rest}, ActualProfileSegmentData omega n horizon x k (a :: rest) →
      profileCompletedCount (trajectory omega) n horizon x k = a
  | _, _, [], .singleton _ _ _ hcount _ => hcount
  | _, _, _ :: _, .cons _ _ _ _ _ hcount _ _ => hcount

/-- Every first-level parent gap of an actual segment is complete. -/
def headComplete {omega : StepPath} {n horizon : ℕ} {x : Point} :
    ∀ {k a rest}, (data : ActualProfileSegmentData omega n horizon x k
      (a :: rest)) → ∀ i < a,
      profileGapExitTime (trajectory omega) n horizon x k i ≤ horizon
  | _, _, [], .singleton _ _ _ _ hcomplete => hcomplete
  | _, _, _ :: _, .cons _ _ _ _ _ _ hcomplete _ => hcomplete

/-- The tail of a segment with at least two levels. -/
def tail {omega : StepPath} {n horizon : ℕ} {x : Point}
    {k a b : ℕ} {rest : List ℕ} :
    ActualProfileSegmentData omega n horizon x k (a :: b :: rest) →
      ActualProfileSegmentData omega n horizon x (k + 1) (b :: rest)
  | .cons _ _ _ _ _ _ _ tail => tail

/-- The actual offspring weak composition at each successive pair of levels. -/
def gapChain
    {omega : StepPath} {n horizon : ℕ} {x : Point}
    (hn : 2 ≤ n) (hx : x ∈ candidateBox n) :
    ∀ {k a rest} (hk0 : 0 < k)
      (hdepth : k + rest.length ≤ n)
      (data : ActualProfileSegmentData omega n horizon x k (a :: rest)),
      GapChain (a :: rest)
  | _k, _a, [], _hk0, _hdepth, _data => ()
  | k, a, b :: rest, hk0, hdepth, data =>
      let tailData := data.tail
      (actualProfileOffspringGapPattern hn hk0 (by
          simp only [List.length_cons] at hdepth
          omega) hx data.headPositive data.headCount tailData.headCount
        data.headComplete,
      gapChain hn hx (by omega) (by
        simp only [List.length_cons] at hdepth
        omega) tailData)

end ActualProfileSegmentData

/-- The data carried by one consecutive pair of actual profile levels. -/
structure ActualProfileEdgeData
    (omega : StepPath) (n horizon : ℕ) (x : Point)
    (k parents children : ℕ) where
  hn : 2 ≤ n
  hk0 : 0 < k
  hk : k + 1 ≤ n
  hx : x ∈ candidateBox n
  hparents : 0 < parents
  hparentCount :
    profileCompletedCount (trajectory omega) n horizon x k = parents
  hchildCount :
    profileCompletedCount (trajectory omega) n horizon x (k + 1) = children
  hcomplete : ∀ i < parents,
    profileGapExitTime (trajectory omega) n horizon x k i ≤ horizon

namespace ActualProfileEdgeData

/-- Canonical parent-major child index of one local offspring slot. -/
noncomputable def childIndex
    {omega : StepPath} {n horizon : ℕ} {x : Point}
    {k parents children : ℕ}
    (edge : ActualProfileEdgeData omega n horizon x k parents children)
    (i : Fin parents)
    (j : Fin (profileGapOffspringCount omega n horizon x k i)) : Fin children :=
  actualProfileChildIndex edge.hn edge.hk0 edge.hk edge.hx edge.hparents
    edge.hparentCount edge.hchildCount edge.hcomplete i j

/-- Completion proof for the global child selected by a local slot. -/
theorem childComplete
    {omega : StepPath} {n horizon : ℕ} {x : Point}
    {k parents children : ℕ}
    (edge : ActualProfileEdgeData omega n horizon x k parents children)
    (i : Fin parents)
    (j : Fin (profileGapOffspringCount omega n horizon x k i)) :
    profileGapExitTime (trajectory omega) n horizon x (k + 1)
      (edge.childIndex i j) ≤ horizon :=
  profileGapExitTime_actualProfileChildIndex_le edge.hn edge.hk0 edge.hk
    edge.hx edge.hparents edge.hparentCount edge.hchildCount edge.hcomplete i j

/-- Supported entrance of an actual parent carried by an edge. -/
noncomputable def parentMiddle
    {omega : StepPath} {n horizon : ℕ} {x : Point}
    {k parents children : ℕ}
    (edge : ActualProfileEdgeData omega n horizon x k parents children)
    (i : Fin parents) :=
  actualProfileParentMiddle (edge.hcomplete i i.isLt)

/-- Supported exit of an actual parent carried by an edge. -/
noncomputable def parentOuter
    {omega : StepPath} {n horizon : ℕ} {x : Point}
    {k parents children : ℕ}
    (edge : ActualProfileEdgeData omega n horizon x k parents children)
    (i : Fin parents) :=
  actualProfileParentOuter (edge.hcomplete i i.isLt)

/-- Supported start point of a parent-major global child. -/
noncomputable def childMiddle
    {omega : StepPath} {n horizon : ℕ} {x : Point}
    {k parents children : ℕ}
    (edge : ActualProfileEdgeData omega n horizon x k parents children)
    (i : Fin parents)
    (j : Fin (profileGapOffspringCount omega n horizon x k i)) :
    ProfileCycleMiddlePoint n (k + 1) x :=
  ⟨profileGapStartPoint omega n horizon x (k + 1) (edge.childIndex i j),
    RealDiscFinite.mem_discBoundaryFinset.mpr
      (profileGapStartPoint_mem_innerBoundary (edge.childComplete i j))⟩

/-- Supported exit point of a parent-major global child. -/
noncomputable def childOuter
    {omega : StepPath} {n horizon : ℕ} {x : Point}
    {k parents children : ℕ}
    (edge : ActualProfileEdgeData omega n horizon x k parents children)
    (i : Fin parents)
    (j : Fin (profileGapOffspringCount omega n horizon x k i)) :
    ProfileCycleOuterPoint n (k + 1) x :=
  ⟨profileGapExitPoint omega n horizon x (k + 1) (edge.childIndex i j),
    RealDiscFinite.mem_discBoundaryFinset.mpr
      (profileGapExitPoint_mem_outerBoundary (edge.childComplete i j))⟩

/-- Extracted local inner endpoint of one actual parent. -/
noncomputable def extractedChildMiddle
    {omega : StepPath} {n horizon : ℕ} {x : Point}
    {k parents children : ℕ}
    (edge : ActualProfileEdgeData omega n horizon x k parents children)
    (i : Fin parents)
    (j : Fin (profileGapOffspringCount omega n horizon x k i)) :
    ProfileCycleInnerPoint n k x :=
  extractedProfileInnerPoint
    (actualProfileParentMiddle (edge.hcomplete i i.isLt))
    (actualProfileParentOuter (edge.hcomplete i i.isLt))
    (profileGapBoundaryExcursionWordCode (edge.hcomplete i i.isLt)) j

/-- Extracted local return endpoint of one actual parent. -/
noncomputable def extractedChildOuter
    {omega : StepPath} {n horizon : ℕ} {x : Point}
    {k parents children : ℕ}
    (edge : ActualProfileEdgeData omega n horizon x k parents children)
    (i : Fin parents)
    (j : Fin (profileGapOffspringCount omega n horizon x k i)) :
    ProfileCycleMiddlePoint n k x :=
  extractedProfileMiddlePoint edge.hn edge.hk0 edge.hk
    (actualProfileParentMiddle (edge.hcomplete i i.isLt))
    (actualProfileParentOuter (edge.hcomplete i i.isLt))
    (profileGapBoundaryExcursionWordCode (edge.hcomplete i i.isLt)) j.succ

/-- Underlying point of the global child entrance. -/
noncomputable def childMiddlePoint
    {omega : StepPath} {n horizon : ℕ} {x : Point}
    {k parents children : ℕ}
    (edge : ActualProfileEdgeData omega n horizon x k parents children)
    (i : Fin parents)
    (j : Fin (profileGapOffspringCount omega n horizon x k i)) : Point :=
  profileGapStartPoint omega n horizon x (k + 1) (edge.childIndex i j)

/-- Underlying point of the parent-local extracted child entrance. -/
noncomputable def extractedChildMiddlePoint
    {omega : StepPath} {n horizon : ℕ} {x : Point}
    {k parents children : ℕ}
    (edge : ActualProfileEdgeData omega n horizon x k parents children)
    (i : Fin parents)
    (j : Fin (profileGapOffspringCount omega n horizon x k i)) : Point :=
  trajectoryFrom (profileGapStartPoint omega n horizon x k i)
    (extendStoppedWord (profileGapStoppedWord omega n horizon x k i))
    (excursionFinish (profileGapWalk omega n horizon x k i)
      (profileInnerBoundary n k x) (profileInnerBoundary n (k + 1) x)
      (profileGapLength omega n horizon x k i) j)

/-- Underlying point of the global child exit. -/
noncomputable def childOuterPoint
    {omega : StepPath} {n horizon : ℕ} {x : Point}
    {k parents children : ℕ}
    (edge : ActualProfileEdgeData omega n horizon x k parents children)
    (i : Fin parents)
    (j : Fin (profileGapOffspringCount omega n horizon x k i)) : Point :=
  profileGapExitPoint omega n horizon x (k + 1) (edge.childIndex i j)

/-- Underlying point of the parent-local extracted child return. -/
noncomputable def extractedChildOuterPoint
    {omega : StepPath} {n horizon : ℕ} {x : Point}
    {k parents children : ℕ}
    (edge : ActualProfileEdgeData omega n horizon x k parents children)
    (i : Fin parents)
    (j : Fin (profileGapOffspringCount omega n horizon x k i)) : Point :=
  trajectoryFrom (profileGapStartPoint omega n horizon x k i)
    (extendStoppedWord (profileGapStoppedWord omega n horizon x k i))
    (excursionStart (profileGapWalk omega n horizon x k i)
      (profileInnerBoundary n k x) (profileInnerBoundary n (k + 1) x)
      (profileGapLength omega n horizon x k i) (j + 1))

/-- The supported start point of a parent-major global child is the inner
endpoint extracted from its actual parent word. -/
theorem actualProfileChildMiddle_eq_extracted
    {omega : StepPath} {n horizon k parents children : ℕ} {x : Point}
    (edge : ActualProfileEdgeData omega n horizon x k parents children)
    (i : Fin parents)
    (j : Fin (profileGapOffspringCount omega n horizon x k i)) :
    profileGapStartPoint omega n horizon x (k + 1) (edge.childIndex i j) =
      trajectoryFrom (profileGapStartPoint omega n horizon x k i)
        (extendStoppedWord (profileGapStoppedWord omega n horizon x k i))
        (excursionFinish (profileGapWalk omega n horizon x k i)
          (profileInnerBoundary n k x) (profileInnerBoundary n (k + 1) x)
          (profileGapLength omega n horizon x k i) j) := by
  classical
  unfold childIndex
  have hclocks := profileChildClocks_actualProfileChildIndex
    edge.hn edge.hk0 edge.hk edge.hx edge.hparents edge.hparentCount
    edge.hchildCount edge.hcomplete i j
  dsimp only at hclocks
  have hreturn := profileGapChildStart_succ_le
    edge.hn edge.hk0 edge.hk (edge.hcomplete i i.isLt) j.isLt
  have hfinish : profileGapChildFinish omega n horizon x k i j ≤
      profileGapLength omega n horizon x k i :=
    (TerminalExcursionPathwise.excursionFinish_le_next_start
      (profileGapWalk omega n horizon x k i)
      (profileInnerBoundary n k x) (profileInnerBoundary n (k + 1) x)
      (profileGapLength omega n horizon x k i) j).trans hreturn
  unfold profileGapStartPoint
  rw [hclocks.1]
  rw [← profileGapWalk_eq_trajectory_add omega n horizon x k i
    (excursionFinish (profileGapWalk omega n horizon x k i)
      (profileInnerBoundary n k x) (profileInnerBoundary n (k + 1) x)
      (profileGapLength omega n horizon x k i) j)]
  exact profileGapWalk_eq_extendStoppedWord_through hfinish

/-- The supported exit point of a parent-major global child is the following
middle endpoint extracted from its actual parent word. -/
theorem actualProfileChildOuter_eq_extracted
    {omega : StepPath} {n horizon k parents children : ℕ} {x : Point}
    (edge : ActualProfileEdgeData omega n horizon x k parents children)
    (i : Fin parents)
    (j : Fin (profileGapOffspringCount omega n horizon x k i)) :
    profileGapExitPoint omega n horizon x (k + 1) (edge.childIndex i j) =
      trajectoryFrom (profileGapStartPoint omega n horizon x k i)
        (extendStoppedWord (profileGapStoppedWord omega n horizon x k i))
        (excursionStart (profileGapWalk omega n horizon x k i)
          (profileInnerBoundary n k x) (profileInnerBoundary n (k + 1) x)
          (profileGapLength omega n horizon x k i) (j + 1)) := by
  classical
  unfold childIndex
  have hclocks := profileChildClocks_actualProfileChildIndex
    edge.hn edge.hk0 edge.hk edge.hx edge.hparents edge.hparentCount
    edge.hchildCount edge.hcomplete i j
  dsimp only at hclocks
  have hreturn := profileGapChildStart_succ_le
    edge.hn edge.hk0 edge.hk (edge.hcomplete i i.isLt) j.isLt
  unfold profileGapExitPoint
  rw [hclocks.2]
  rw [← profileGapWalk_eq_trajectory_add omega n horizon x k i
    (excursionStart (profileGapWalk omega n horizon x k i)
      (profileInnerBoundary n k x) (profileInnerBoundary n (k + 1) x)
      (profileGapLength omega n horizon x k i) (j + 1))]
  exact profileGapWalk_eq_extendStoppedWord_through hreturn

end ActualProfileEdgeData

namespace ActualProfileSegmentData

/-- The consecutive pair of head levels carried by a segment of length at
least two. -/
def edgeData
    {omega : StepPath} {n horizon : ℕ} {x : Point}
    (hn : 2 ≤ n) (hx : x ∈ candidateBox n)
    {k a b : ℕ} {rest : List ℕ} (hk0 : 0 < k)
    (hdepth : k + (b :: rest).length ≤ n)
    (data : ActualProfileSegmentData omega n horizon x k
      (a :: b :: rest)) :
    ActualProfileEdgeData omega n horizon x k a b where
  hn := hn
  hk0 := hk0
  hk := by simp only [List.length_cons] at hdepth; omega
  hx := hx
  hparents := data.headPositive
  hparentCount := data.headCount
  hchildCount := data.tail.headCount
  hcomplete := data.headComplete

/-- Ordered refinement trees read directly from the actual parent-major
offspring clocks of a complete profile segment. -/
def refinementTrees
    {omega : StepPath} {n horizon : ℕ} {x : Point}
    (hn : 2 ≤ n) (hx : x ∈ candidateBox n) :
    ∀ {k a rest} (hk0 : 0 < k)
      (hdepth : k + rest.length ≤ n)
      (data : ActualProfileSegmentData omega n horizon x k (a :: rest)),
      Fin a → ProfileRefinementTree
  | _k, _a, [], _hk0, _hdepth, _data => fun _ ↦ .leaf
  | k, _a, b :: rest, hk0, hdepth, data => fun i ↦
      let edge := edgeData hn hx hk0 hdepth data
      .node (ProfileRefinementForest.ofList (List.ofFn fun j :
        Fin (profileGapOffspringCount omega n horizon x k i) ↦
          refinementTrees hn hx (by omega) (by
            simp only [List.length_cons] at hdepth
            omega) data.tail (edge.childIndex i j)))

/-- Supported entrance of one actual parent in a segment. -/
noncomputable def parentMiddle
    {omega : StepPath} {n horizon : ℕ} {x : Point}
    {k a : ℕ} {rest : List ℕ}
    (data : ActualProfileSegmentData omega n horizon x k (a :: rest))
    (i : Fin a) :=
  actualProfileParentMiddle (data.headComplete i i.isLt)

/-- Supported exit of one actual parent in a segment. -/
noncomputable def parentOuter
    {omega : StepPath} {n horizon : ℕ} {x : Point}
    {k a : ℕ} {rest : List ℕ}
    (data : ActualProfileSegmentData omega n horizon x k (a :: rest))
    (i : Fin a) :=
  actualProfileParentOuter (data.headComplete i i.isLt)

/-- The actual refinement tree at a single parent index. -/
noncomputable def refinementTree
    {omega : StepPath} {n horizon : ℕ} {x : Point}
    (hn : 2 ≤ n) (hx : x ∈ candidateBox n)
    {k a : ℕ} {rest : List ℕ} (hk0 : 0 < k)
    (hdepth : k + rest.length ≤ n)
    (data : ActualProfileSegmentData omega n horizon x k (a :: rest))
    (i : Fin a) : ProfileRefinementTree :=
  refinementTrees hn hx hk0 hdepth data i

end ActualProfileSegmentData

end

end Erdos1165.AnnularRecursiveProfileActualParser
