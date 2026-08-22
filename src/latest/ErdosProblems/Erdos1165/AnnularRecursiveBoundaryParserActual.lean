/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
import ErdosProblems.Erdos1165.AnnularRecursiveBoundaryParser

/-!
# The local boundary parser agrees with the actual profile parser

The local parser is driven only by the literal stopped word.  On an actual
completed profile gap, its recursively read tree is therefore the canonical
actual-clock refinement tree.
-/

namespace Erdos1165.AnnularRecursiveBoundaryParserActual

open AnnularBoundaryExcursionKernel AnnularProfileClocks AnnularProfileGapAtoms
open AnnularProfileLevelSkeleton AnnularExtractedProfileSpineCode
open AlternatingConcatPrefixFree
open AnnularOffspringKernelRadial
open AnnularRecursiveBoundaryParser AnnularRecursiveProfileActualCode
open AnnularRecursiveDecoratedProfileCode
open AnnularRecursiveProfileShape
open AnnularRecursiveProfileSourceRecovery
open AnnularRecursiveProfileActualParser
open AnnularRecursiveProfileActualParser.ActualProfileEdgeData
open AnnularRecursiveProfileActualParser.ActualProfileSegmentData
open AnnularProfileChildWordIdentification
open MarkedBridgeFactorization ThickPoint

noncomputable section

/-- The ordinary first-exit view of an actual completed profile gap, with
arbitrary supported representatives of its two endpoints. -/
def actualBoundaryExitWordCodeAt
    {omega : StepPath} {n horizon k parent : ℕ} {x : Point}
    (hcomplete : profileGapExitTime (trajectory omega) n horizon x k parent ≤
      horizon)
    (u : ProfileCycleMiddlePoint n k x)
    (w : ProfileCycleOuterPoint n k x)
    (hu : profileGapStartPoint omega n horizon x k parent = u.1)
    (hw : profileGapExitPoint omega n horizon x k parent = w.1) :
    BoundaryExitWordCode (profileOuterBoundary n k x) u.1 w.1 :=
  actualLeafGapCodeAt hcomplete u w hu hw

@[simp] theorem actualBoundaryExitWordCodeAt_val
    {omega : StepPath} {n horizon k parent : ℕ} {x : Point}
    (hcomplete : profileGapExitTime (trajectory omega) n horizon x k parent ≤
      horizon)
    (u : ProfileCycleMiddlePoint n k x)
    (w : ProfileCycleOuterPoint n k x)
    (hu : profileGapStartPoint omega n horizon x k parent = u.1)
    (hw : profileGapExitPoint omega n horizon x k parent = w.1) :
    (actualBoundaryExitWordCodeAt hcomplete u w hu hw).1 =
      profileGapStoppedWord omega n horizon x k parent := rfl

private theorem sigmaBoundaryExcursionCode_eq_of_val_eq
    {outer middle inner : Set Point} {start exit : Point} {q r : ℕ}
    (hqr : q = r)
    (left : BoundaryExcursionExitWordCode outer middle inner start q exit)
    (right : BoundaryExcursionExitWordCode outer middle inner start r exit)
    (hval : left.1 = right.1) :
    (⟨q, left⟩ : Σ s, BoundaryExcursionExitWordCode
      outer middle inner start s exit) = ⟨r, right⟩ := by
  apply Sigma.ext hqr
  apply (Subtype.heq_iff_coe_eq (fun stopped ↦ by
    constructor
    · rintro ⟨hfirst, hcount, hend⟩
      exact ⟨hfirst, hcount.trans hqr, hend⟩
    · rintro ⟨hfirst, hcount, hend⟩
      exact ⟨hfirst, hcount.trans hqr.symm, hend⟩)).2
  exact hval

/-- The tree read from one already count-bearing internal parent.  Packaging
the count together with the dependent code makes count transports cheap. -/
private def parsedBoundaryExcursionTree
    (n : ℕ) (x : Point) (hn : 2 ≤ n) (depth k : ℕ)
    (hk0 : 0 < k) (hk : k + 1 ≤ n)
    (hdepth : k + 1 + depth ≤ n)
    (u : ProfileCycleMiddlePoint n k x)
    (w : ProfileCycleOuterPoint n k x)
    (pack : Σ q, BoundaryExcursionExitWordCode
      (profileOuterBoundary n k x) (profileInnerBoundary n k x)
      (profileInnerBoundary n (k + 1) x) u.1 q w.1) :
    ProfileRefinementTree :=
  .node (profileRefinementForestOfFin pack.1 fun j ↦
    (parseBoundaryGap n x hn depth (k + 1) (by omega) hdepth
      (extractedProfileInnerPoint u w pack.2 j)
      (extractedProfileMiddlePoint hn hk0 hk u w pack.2 j.succ)
      (extractedProfileReturnWordCode hn hk0 hk u w pack.2 j)).tree)

private theorem parsedProfileGapOfBoundaryExcursion_tree
    {n k q : ℕ} {x : Point}
    (hn : 2 ≤ n) (hk0 : 0 < k) (hk : k + 1 ≤ n)
    (u : ProfileCycleMiddlePoint n k x)
    (w : ProfileCycleOuterPoint n k x)
    (parent : BoundaryExcursionExitWordCode
      (profileOuterBoundary n k x) (profileInnerBoundary n k x)
      (profileInnerBoundary n (k + 1) x) u.1 q w.1)
    (children : (j : Fin q) → ActualParsedProfileGap n (k + 1) x
      (extractedProfileInnerPoint u w parent j)
      (extractedProfileMiddlePoint hn hk0 hk u w parent j.succ)) :
    (parsedProfileGapOfBoundaryExcursion hn hk0 hk u w parent children).tree =
      .node (profileRefinementForestOfFin q fun j ↦ (children j).tree) := by
  rfl

private theorem parseBoundaryGap_succ_tree
    {n k : ℕ} {x : Point} (hn : 2 ≤ n) (depth : ℕ)
    (hk0 : 0 < k) (hdepth : k + (depth + 1) ≤ n)
    (u : ProfileCycleMiddlePoint n k x)
    (w : ProfileCycleOuterPoint n k x)
    (source : BoundaryExitWordCode (profileOuterBoundary n k x) u.1 w.1) :
    let parent := boundaryExitWordAsExcursionCode u w source
    (parseBoundaryGap n x hn (depth + 1) k hk0 hdepth u w source).tree =
      .node (profileRefinementForestOfFin
        (boundaryExcursionCount (profileInnerBoundary n k x)
          (profileInnerBoundary n (k + 1) x) u.1
          (extendStoppedWord source.1) source.1.1) fun j ↦
        (parseBoundaryGap n x hn depth (k + 1) (by omega) (by omega)
          (extractedProfileInnerPoint u w parent j)
          (extractedProfileMiddlePoint hn hk0 (by omega) u w parent j.succ)
          (extractedProfileReturnWordCode hn hk0 (by omega)
            u w parent j)).tree) := by
  rfl

/-- Parsing an actual completed gap locally reads the same refinement tree
as the global actual-clock parser. -/
theorem parseBoundaryGap_actual_tree
    {omega : StepPath} {n horizon : ℕ} {x : Point}
    (hn : 2 ≤ n) (hx : x ∈ candidateBox n) (rest : List ℕ) :
    ∀ {k a : ℕ} (hk0 : 0 < k) (hdepth : k + rest.length ≤ n)
      (data : ActualProfileSegmentData omega n horizon x k (a :: rest))
      (i : Fin a) (u : ProfileCycleMiddlePoint n k x)
      (w : ProfileCycleOuterPoint n k x)
      (hu : profileGapStartPoint omega n horizon x k i = u.1)
      (hw : profileGapExitPoint omega n horizon x k i = w.1),
      (parseBoundaryGap n x hn rest.length k hk0 hdepth u w
        (actualBoundaryExitWordCodeAt (data.headComplete i i.isLt)
          u w hu hw)).tree =
        (actualParsedProfileGap hn hx rest hk0 hdepth data i u w hu hw).tree := by
  induction rest with
  | nil =>
      intro k a hk0 hdepth data i u w hu hw
      rfl
  | cons b rest ih =>
      intro k a hk0 hdepth data i u w hu hw
      let edge := data.edgeData hn hx hk0 hdepth
      let ParentCode := fun q0 : ℕ ↦ BoundaryExcursionExitWordCode
        (profileOuterBoundary n k x) (profileInnerBoundary n k x)
        (profileInnerBoundary n (k + 1) x) u.1 q0 w.1
      let parent : ParentCode
          (profileGapOffspringCount omega n horizon x k i) :=
        actualParentBoundaryCodeAt
          (edge.hcomplete i i.isLt) u w hu hw
      let source := actualBoundaryExitWordCodeAt
        (edge.hcomplete i i.isLt) u w hu hw
      let q := boundaryExcursionCount
        (profileInnerBoundary n k x) (profileInnerBoundary n (k + 1) x) u.1
        (extendStoppedWord source.1) source.1.1
      have hq : q = profileGapOffspringCount omega n horizon x k i := by
        have hqRaw := parent.2.2.1
        simpa only [q, source, actualBoundaryExitWordCodeAt,
          actualLeafGapCodeAt, parent] using hqRaw
      let localParent : ParentCode q :=
        boundaryExitWordAsExcursionCode u w source
      have hpack : (⟨q, localParent⟩ : Σ q0, ParentCode q0) =
          ⟨profileGapOffspringCount omega n horizon x k i, parent⟩ := by
        apply sigmaBoundaryExcursionCode_eq_of_val_eq hq
        rfl
      have hk : k + 1 ≤ n := by
        simp only [List.length_cons] at hdepth
        omega
      have childDepth : k + 1 + rest.length ≤ n := by
        simp only [List.length_cons] at hdepth
        omega
      simp only [List.length_cons]
      rw [parseBoundaryGap_succ_tree]
      rw [actualParsedProfileGap_cons]
      rw [parsedProfileGapOfBoundaryExcursion_tree]
      have htransport := congrArg
        (parsedBoundaryExcursionTree n x hn rest.length k hk0 hk
          childDepth u w) hpack
      simp only [parsedBoundaryExcursionTree] at htransport
      rw [htransport]
      apply congrArg ProfileRefinementTree.node
      rw [profileRefinementForestOfFin_eq_ofList_ofFn,
        profileRefinementForestOfFin_eq_ofList_ofFn]
      apply congrArg ProfileRefinementForest.ofList
      apply List.ofFn_inj.mpr
      funext j
      let childU := extractedProfileInnerPoint u w parent j
      let childW := extractedProfileMiddlePoint edge.hn edge.hk0 edge.hk
        u w parent j.succ
      let actualChildSource := actualBoundaryExitWordCodeAt
        (edge.childComplete i j) childU childW
        (childMiddlePoint_eq_extracted_at edge i u w hu hw j)
        (childOuterPoint_eq_extracted_at edge i u w hu hw j)
      let localChildSource := extractedProfileReturnWordCode
        edge.hn edge.hk0 edge.hk u w parent j
      have hsource : localChildSource = actualChildSource := by
        have hlist : List.ofFn localChildSource.1.2 =
            List.ofFn actualChildSource.1.2 := by
          calc
            List.ofFn localChildSource.1.2 =
                extractedProfileReturnList edge.hn edge.hk0 edge.hk
                  u w parent j :=
              (extractedProfileReturnList_eq_codeList
                edge.hn edge.hk0 edge.hk u w parent j).symm
            _ = extractedProfileReturnList edge.hn edge.hk0 edge.hk
                  (actualProfileParentMiddle (edge.hcomplete i i.isLt))
                  (actualProfileParentOuter (edge.hcomplete i i.isLt))
                  (profileGapBoundaryExcursionWordCode
                    (edge.hcomplete i i.isLt)) j :=
              (edgeExtractedProfileReturnListAt_eq
                edge i u w hu hw j).symm
            _ = List.ofFn
                  (profileGapStoppedWord omega n horizon x (k + 1)
                    (edge.childIndex i j)).2 :=
              (profileGapStoppedList_childIndex_eq_actualExtracted
                edge i j).symm
            _ = List.ofFn actualChildSource.1.2 := by
              rw [actualBoundaryExitWordCodeAt_val]
        apply Subtype.ext
        calc
          localChildSource.1 =
              listStoppedWord (List.ofFn localChildSource.1.2) :=
            (listStoppedWord_ofFn localChildSource.1).symm
          _ = listStoppedWord (List.ofFn actualChildSource.1.2) := by
            exact congrArg listStoppedWord hlist
          _ = actualChildSource.1 := listStoppedWord_ofFn actualChildSource.1
      have hih := ih (by omega) childDepth data.tail (edge.childIndex i j)
        childU childW
        (childMiddlePoint_eq_extracted_at edge i u w hu hw j)
        (childOuterPoint_eq_extracted_at edge i u w hu hw j)
      change (parseBoundaryGap n x hn rest.length (k + 1) (by omega)
          childDepth childU childW actualChildSource).tree = _ at hih
      rw [← hsource] at hih
      simpa only [localChildSource, childU, childW, parent] using hih

end

end Erdos1165.AnnularRecursiveBoundaryParserActual
