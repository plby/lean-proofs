/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
import ErdosProblems.Erdos1165.AnnularProfileChildClockIdentification
import ErdosProblems.Erdos1165.AnnularRecursiveProfileSourceParser

/-!
# Identifying parent-local and global profile-child words

The parent-local child clocks have already been identified with their
parent-major global clocks.  Here we record the corresponding finite-word
identity: the deleted return word extracted from a parent gap is literally
the global stopped word of that child gap.
-/

namespace Erdos1165.AnnularProfileChildWordIdentification

open AnnularProfileClocks AnnularProfileGapAtoms AnnularProfileLevelSkeleton
open AnnularProfileChildClockIdentification AnnularOffspringScan
open AnnularExtractedProfileSpineCode AnnularOffspringKernelRadial
open AlternatingConcatPrefixFree
open AsymmetricSplitLevelSplice MarkedBridgeFactorization
open TerminalClockSplice TerminalExcursionPathwise TerminalSkeletonWords
open TerminalSequentialVisitLaw ThickPoint
open PlanarPotential

noncomputable section

attribute [local instance] Classical.propDecidable

/-- Erasing the stopped-word wrapper of an actual profile gap gives its
literal source increment slice. -/
@[simp] theorem profileGapStoppedWord_toList
    (omega : StepPath) (n horizon : ℕ) (x : Point) (k j : ℕ) :
    List.ofFn (profileGapStoppedWord omega n horizon x k j).2 =
      incrementSlice omega
        (profileInnerHitTime (trajectory omega) n horizon x k j)
        (profileGapExitTime (trajectory omega) n horizon x k j) := by
  rfl

/-- Inside the actual parent horizon, extending its finite stopped word is
the same as reading the corresponding shifted source increments. -/
theorem incrementSlice_extend_profileGapStoppedWord
    {omega : StepPath} {n horizon : ℕ} {x : Point} {k parent a b : ℕ}
    (hab : a ≤ b)
    (hb : b ≤ profileGapLength omega n horizon x k parent) :
    incrementSlice
        (extendStoppedWord
          (profileGapStoppedWord omega n horizon x k parent)) a b =
      incrementSlice omega
        (profileInnerHitTime (trajectory omega) n horizon x k parent + a)
        (profileInnerHitTime (trajectory omega) n horizon x k parent + b) := by
  apply List.ext_get
  · simp only [incrementSlice_length]
    omega
  · intro r hrLeft hrRight
    rw [List.get_eq_getElem, List.get_eq_getElem]
    simp only [incrementSlice, List.getElem_ofFn]
    have har : a + r < profileGapLength omega n horizon x k parent := by
      have hr : r < b - a := by
        simpa only [incrementSlice_length] using hrLeft
      omega
    have hprefix := congrFun
      (stepPrefix_extendStoppedWord
        (profileGapStoppedWord omega n horizon x k parent))
      ⟨a + r, har⟩
    simpa only [stepPrefix, profileGapStoppedWord, profileGapFreshPath,
      shiftSteps, Nat.add_assoc] using hprefix

/-- The supported middle endpoint of an actual completed parent gap. -/
def actualProfileParentMiddle
    {omega : StepPath} {n horizon : ℕ} {x : Point} {k parent : ℕ}
    (hcomplete : profileGapExitTime (trajectory omega) n horizon x k parent ≤
      horizon) : ProfileCycleMiddlePoint n k x :=
  ⟨profileGapStartPoint omega n horizon x k parent,
    RealDiscFinite.mem_discBoundaryFinset.mpr
      (profileGapStartPoint_mem_innerBoundary hcomplete)⟩

/-- The supported outer endpoint of an actual completed parent gap. -/
def actualProfileParentOuter
    {omega : StepPath} {n horizon : ℕ} {x : Point} {k parent : ℕ}
    (hcomplete : profileGapExitTime (trajectory omega) n horizon x k parent ≤
      horizon) : ProfileCycleOuterPoint n k x :=
  ⟨profileGapExitPoint omega n horizon x k parent,
    RealDiscFinite.mem_discBoundaryFinset.mpr
      (profileGapExitPoint_mem_outerBoundary hcomplete)⟩

/-- The actual fresh parent path and the extension of its literal stopped
word agree through the complete parent horizon. -/
theorem profileGapWalk_eq_extendStoppedWord_through
    {omega : StepPath} {n horizon : ℕ} {x : Point} {k parent r : ℕ}
    (hr : r ≤ profileGapLength omega n horizon x k parent) :
    profileGapWalk omega n horizon x k parent r =
      trajectoryFrom (profileGapStartPoint omega n horizon x k parent)
        (extendStoppedWord
          (profileGapStoppedWord omega n horizon x k parent)) r := by
  exact trajectoryFrom_eq_extendStoppedWord_of_mem
    (profileGapFreshPath_mem_stoppedWordCylinder
      omega n horizon x k parent)
    (profileGapStartPoint omega n horizon x k parent) hr

/-- The return clocks extracted from the canonical parent stopped word are
the actual local child clocks of the fresh parent gap. -/
theorem extractedProfileReturn_clocks_eq_actual
    {omega : StepPath} {n horizon : ℕ} {x : Point} {k parent : ℕ}
    (_hcomplete : profileGapExitTime (trajectory omega) n horizon x k parent ≤
      horizon) (j : ℕ) :
    let L := profileGapLength omega n horizon x k parent
    let actual := profileGapWalk omega n horizon x k parent
    let extended := trajectoryFrom
      (profileGapStartPoint omega n horizon x k parent)
      (extendStoppedWord (profileGapStoppedWord omega n horizon x k parent))
    excursionFinish extended (profileInnerBoundary n k x)
        (profileInnerBoundary n (k + 1) x) L j =
      excursionFinish actual (profileInnerBoundary n k x)
        (profileInnerBoundary n (k + 1) x) L j ∧
    excursionStart extended (profileInnerBoundary n k x)
        (profileInnerBoundary n (k + 1) x) L (j + 1) =
      excursionStart actual (profileInnerBoundary n k x)
        (profileInnerBoundary n (k + 1) x) L (j + 1) := by
  classical
  dsimp only
  have htraj : ∀ r ≤ profileGapLength omega n horizon x k parent,
      profileGapWalk omega n horizon x k parent r =
        trajectoryFrom (profileGapStartPoint omega n horizon x k parent)
          (extendStoppedWord
            (profileGapStoppedWord omega n horizon x k parent)) r :=
    fun r hr ↦ profileGapWalk_eq_extendStoppedWord_through hr
  constructor
  · symm
    exact excursionFinish_congr_prefix htraj
      (profileInnerBoundary n k x) (profileInnerBoundary n (k + 1) x) j
  · symm
    exact excursionStart_congr_prefix htraj
      (profileInnerBoundary n k x) (profileInnerBoundary n (k + 1) x) (j + 1)

/-- The canonical parent-local return code extracted from an actual completed
profile gap.  Naming this dependent object keeps downstream statements small. -/
noncomputable def actualExtractedProfileReturnWordCode
    {omega : StepPath} {n horizon : ℕ} {x : Point} {k parent : ℕ}
    (hn : 2 ≤ n) (hk0 : 0 < k) (hk : k + 1 ≤ n)
    (hcomplete : profileGapExitTime (trajectory omega) n horizon x k parent ≤
      horizon)
    (j : Fin (profileGapOffspringCount omega n horizon x k parent)) :=
  extractedProfileReturnWordCode hn hk0 hk
    (actualProfileParentMiddle hcomplete)
    (actualProfileParentOuter hcomplete)
    (profileGapBoundaryExcursionWordCode hcomplete) j

/-- The erased word of the return extracted from a canonical actual parent is
the corresponding source increment slice at the parent-local child clocks. -/
theorem actualExtractedProfileReturnWordCode_toList
    {omega : StepPath} {n horizon : ℕ} {x : Point} {k parent : ℕ}
    (hn : 2 ≤ n) (hk0 : 0 < k) (hk : k + 1 ≤ n)
    (hcomplete : profileGapExitTime (trajectory omega) n horizon x k parent ≤
      horizon)
    (j : Fin (profileGapOffspringCount omega n horizon x k parent)) :
    List.ofFn
        (actualExtractedProfileReturnWordCode hn hk0 hk hcomplete j).1.2 =
      incrementSlice omega
        (profileInnerHitTime (trajectory omega) n horizon x k parent +
          profileGapChildFinish omega n horizon x k parent j)
        (profileInnerHitTime (trajectory omega) n horizon x k parent +
          profileGapChildStart omega n horizon x k parent (j + 1)) := by
  classical
  have hclocks := extractedProfileReturn_clocks_eq_actual hcomplete (j : ℕ)
  dsimp only at hclocks
  have hslice : incrementSlice
        (extendStoppedWord
          (profileGapStoppedWord omega n horizon x k parent))
        (excursionFinish
          (trajectoryFrom (profileGapStartPoint omega n horizon x k parent)
            (extendStoppedWord
              (profileGapStoppedWord omega n horizon x k parent)))
          (profileInnerBoundary n k x) (profileInnerBoundary n (k + 1) x)
          (profileGapLength omega n horizon x k parent) j)
        (excursionStart
          (trajectoryFrom (profileGapStartPoint omega n horizon x k parent)
            (extendStoppedWord
              (profileGapStoppedWord omega n horizon x k parent)))
          (profileInnerBoundary n k x) (profileInnerBoundary n (k + 1) x)
          (profileGapLength omega n horizon x k parent) (j + 1)) =
      incrementSlice omega
        (profileInnerHitTime (trajectory omega) n horizon x k parent +
          profileGapChildFinish omega n horizon x k parent j)
        (profileInnerHitTime (trajectory omega) n horizon x k parent +
          profileGapChildStart omega n horizon x k parent (j + 1)) := by
    rw [hclocks.1, hclocks.2]
    apply incrementSlice_extend_profileGapStoppedWord
    · exact excursionFinish_le_next_start
        (profileGapWalk omega n horizon x k parent)
        (profileInnerBoundary n k x) (profileInnerBoundary n (k + 1) x)
        (profileGapLength omega n horizon x k parent) j
    · exact profileGapChildStart_succ_le hn hk0 hk hcomplete j.isLt
  calc
    List.ofFn
        (actualExtractedProfileReturnWordCode hn hk0 hk hcomplete j).1.2 =
      intervalWords
        (extendStoppedWord
          (profileGapBoundaryExcursionWordCode hcomplete).1)
        (extractTimedReturnSkeleton
          (extendStoppedWord
            (profileGapBoundaryExcursionWordCode hcomplete).1)
          (actualProfileParentMiddle hcomplete).1
          (profileInnerBoundary n k x) (profileInnerBoundary n (k + 1) x)
          (profileGapBoundaryExcursionWordCode hcomplete).1.1
          (profileGapOffspringCount omega n horizon x k parent)).entrance
        (extractTimedReturnSkeleton
          (extendStoppedWord
            (profileGapBoundaryExcursionWordCode hcomplete).1)
          (actualProfileParentMiddle hcomplete).1
          (profileInnerBoundary n k x) (profileInnerBoundary n (k + 1) x)
          (profileGapBoundaryExcursionWordCode hcomplete).1.1
          (profileGapOffspringCount omega n horizon x k parent)).exit j :=
      (by
        unfold actualExtractedProfileReturnWordCode
        exact extractedProfileReturnWordCode_toList hn hk0 hk
          (actualProfileParentMiddle hcomplete)
          (actualProfileParentOuter hcomplete)
          (profileGapBoundaryExcursionWordCode hcomplete) j)
    _ = _ := by
      simpa only [intervalWords, extractTimedReturnSkeleton,
        returnEntranceTime, returnExitTime, profileGapBoundaryExcursionWordCode_val,
        profileGapStoppedWord_length, actualProfileParentMiddle,
        profileGapChildFinish, profileGapChildStart]
        using hslice

/-- The stopped word of a global child at its parent-major index is exactly
the deleted return word extracted from that actual parent. -/
theorem profileGapStoppedWord_actualProfileChildIndex_eq_extracted
    {omega : StepPath} {n horizon k parents children : ℕ} {x : Point}
    (hn : 2 ≤ n) (hk0 : 0 < k) (hk : k + 1 ≤ n)
    (hx : x ∈ candidateBox n) (hparents : 0 < parents)
    (hparentCount :
      profileCompletedCount (trajectory omega) n horizon x k = parents)
    (hchildCount :
      profileCompletedCount (trajectory omega) n horizon x (k + 1) = children)
    (hcomplete : ∀ i < parents,
      profileGapExitTime (trajectory omega) n horizon x k i ≤ horizon)
    (i : Fin parents)
    (j : Fin (profileGapOffspringCount omega n horizon x k i)) :
    profileGapStoppedWord omega n horizon x (k + 1)
        (actualProfileChildIndex hn hk0 hk hx hparents hparentCount
          hchildCount hcomplete i j) =
      (actualExtractedProfileReturnWordCode hn hk0 hk
        (hcomplete i i.isLt) j).1 := by
  classical
  have hclocks := profileChildClocks_actualProfileChildIndex
    hn hk0 hk hx hparents hparentCount hchildCount hcomplete i j
  dsimp only at hclocks
  have hlocal := actualExtractedProfileReturnWordCode_toList
    hn hk0 hk (hcomplete i i.isLt) j
  have hglobal := profileGapStoppedWord_toList omega n horizon x (k + 1)
    (actualProfileChildIndex hn hk0 hk hx hparents hparentCount
      hchildCount hcomplete i j)
  have hslices := congrArg₂ (incrementSlice omega) hclocks.1 hclocks.2
  have hslices' :
      incrementSlice omega
          (profileInnerHitTime (trajectory omega) n horizon x (k + 1)
            (actualProfileChildIndex hn hk0 hk hx hparents hparentCount
              hchildCount hcomplete i j))
          (profileGapExitTime (trajectory omega) n horizon x (k + 1)
            (actualProfileChildIndex hn hk0 hk hx hparents hparentCount
              hchildCount hcomplete i j)) =
        incrementSlice omega
          (profileInnerHitTime (trajectory omega) n horizon x k i +
            profileGapChildFinish omega n horizon x k i j)
          (profileInnerHitTime (trajectory omega) n horizon x k i +
            profileGapChildStart omega n horizon x k i (j + 1)) := by
    simpa only [profileGapChildFinish, profileGapChildStart] using hslices
  have hsource :
      List.ofFn
          (profileGapStoppedWord omega n horizon x (k + 1)
            (actualProfileChildIndex hn hk0 hk hx hparents hparentCount
              hchildCount hcomplete i j)).2 =
        List.ofFn
          (actualExtractedProfileReturnWordCode hn hk0 hk
            (hcomplete i i.isLt) j).1.2 := by
    exact hglobal.trans (hslices'.trans hlocal.symm)
  exact (listStoppedWord_ofFn _).symm.trans
    ((congrArg listStoppedWord hsource).trans (listStoppedWord_ofFn _))

/-- Every parent-major child selected from a completed parent gap is itself a
completed global gap. -/
theorem profileGapExitTime_actualProfileChildIndex_le
    {omega : StepPath} {n horizon k parents children : ℕ} {x : Point}
    (hn : 2 ≤ n) (hk0 : 0 < k) (hk : k + 1 ≤ n)
    (hx : x ∈ candidateBox n) (hparents : 0 < parents)
    (hparentCount :
      profileCompletedCount (trajectory omega) n horizon x k = parents)
    (hchildCount :
      profileCompletedCount (trajectory omega) n horizon x (k + 1) = children)
    (hcomplete : ∀ i < parents,
      profileGapExitTime (trajectory omega) n horizon x k i ≤ horizon)
    (i : Fin parents)
    (j : Fin (profileGapOffspringCount omega n horizon x k i)) :
    profileGapExitTime (trajectory omega) n horizon x (k + 1)
        (actualProfileChildIndex hn hk0 hk hx hparents hparentCount
          hchildCount hcomplete i j) ≤ horizon := by
  have hclocks := profileChildClocks_actualProfileChildIndex
    hn hk0 hk hx hparents hparentCount hchildCount hcomplete i j
  dsimp only at hclocks
  rw [hclocks.2]
  have hreturn := profileGapChildStart_succ_le
    hn hk0 hk (hcomplete i i.isLt) j.isLt
  have horder := profileInnerHitTime_le_profileGapExitTime
    (trajectory omega) n horizon x k i
  change profileInnerHitTime (trajectory omega) n horizon x k i +
      profileGapChildStart omega n horizon x k i (j + 1) ≤ horizon
  calc
    _ ≤ profileInnerHitTime (trajectory omega) n horizon x k i +
        profileGapLength omega n horizon x k i :=
      Nat.add_le_add_left hreturn _
    _ = profileGapExitTime (trajectory omega) n horizon x k i := by
      unfold profileGapLength
      exact Nat.add_sub_of_le horder
    _ ≤ horizon := hcomplete i i.isLt

end

end Erdos1165.AnnularProfileChildWordIdentification
