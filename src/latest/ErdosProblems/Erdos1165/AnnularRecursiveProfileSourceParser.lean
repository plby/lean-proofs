/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
import ErdosProblems.Erdos1165.AnnularExtractedProfileSpineCode
import ErdosProblems.Erdos1165.AnnularRecursiveProfileCodeAssembly
import ErdosProblems.Erdos1165.AnnularRecursiveProfileShape

/-!
# Source parser for literal recursive profile gaps

The extracted one-parent assembly contains the retained inward/escape spine
and every deleted child word exactly once.  This file supplies the structural
inverse of the recursive code assembler: recursively parsed child words are
attached to that assembly in chronological order.
-/

namespace Erdos1165.AnnularRecursiveProfileSourceParser

open AnnularDecoratedProfileCode AnnularErasedParentSpineProfileRow
open AnnularBoundaryExcursionKernel
open AnnularErasedParentSpineRowPartition
open AnnularExtractedProfileSpineCode AnnularOffspringKernelRadial
open AnnularProfileClocks AnnularRecursiveDecoratedProfileCode
open AnnularRecursiveProfileCodeAssembly AnnularRecursiveProfileShape
open MarkedBridgeFactorization ThickPoint

noncomputable section

private theorem middleStage_tail_castSucc
    {q : ℕ} (start : Point) (returnPoint : Fin (q + 1) → Point) :
    ∀ j : Fin q,
      middleStage (returnPoint 0) (fun i ↦ returnPoint i.succ) j.castSucc =
        middleStage start returnPoint j.succ.castSucc := by
  intro j
  cases q with
  | zero => exact Fin.elim0 j
  | succ q =>
      refine Fin.cases ?_ (fun i ↦ ?_) j
      · rfl
      · simp only [middleStage_succ_castSucc]
        congr 1

private theorem middleStage_tail_last
    {q : ℕ} (start : Point) (returnPoint : Fin (q + 1) → Point) :
    middleStage (returnPoint 0) (fun i ↦ returnPoint i.succ) (Fin.last q) =
      middleStage start returnPoint (Fin.last (q + 1)) := by
  cases q with
  | zero => rfl
  | succ q =>
      rw [middleStage_last_succ, middleStage_last_succ]
      congr 1

/-- Delete the first inward/child pair from a complete parent assembly. -/
def erasedParentAssemblyTail
    {q : ℕ} {retainedBoundary childBoundary : Set Point}
    {start : Point} {innerPoint returnPoint : Fin (q + 1) → Point}
    {outerPoint : Point}
    (code : ErasedParentAssemblyCode (q + 1) retainedBoundary childBoundary
      start innerPoint returnPoint outerPoint) :
    ErasedParentAssemblyCode q retainedBoundary childBoundary
      (returnPoint 0) (fun j ↦ innerPoint j.succ)
      (fun j ↦ returnPoint j.succ) outerPoint := by
  refine ⟨?_, ?_, ?_⟩
  · intro j
    let source := code.1 j.succ
    have hstart := middleStage_tail_castSucc start returnPoint j
    refine ⟨source.1, ?_, ?_⟩
    · simpa only [source, hstart] using source.2.1
    · simpa only [source, hstart] using source.2.2
  · exact fun j ↦ code.2.1 j.succ
  · let source := code.2.2
    have hstart := middleStage_tail_last start returnPoint
    refine ⟨source.1, ?_, ?_⟩
    · simpa only [source, hstart] using source.2.1
    · simpa only [source, hstart] using source.2.2

/-- Attach already parsed recursive children to a literal erased-parent
assembly. -/
def recursiveProfileForestCodeOfAssembly
    (n k : ℕ) (center : Point) :
    ∀ (q : ℕ) (childTree : Fin q → ProfileRefinementTree)
      (start : ProfileCycleMiddlePoint n k center)
      (innerPoint : Fin q → ProfileCycleInnerPoint n k center)
      (returnPoint : Fin q → ProfileCycleMiddlePoint n k center)
      (outerPoint : ProfileCycleOuterPoint n k center),
      ErasedParentAssemblyCode q
        (profileInnerBoundary n (k + 1) center ∪
          profileOuterBoundary n k center)
        (profileInnerBoundary n k center) start.1
        (fun j ↦ (innerPoint j).1) (fun j ↦ (returnPoint j).1)
        outerPoint.1 →
      ((j : Fin q) → RecursiveProfileGapCode n (k + 1) center
        (childTree j) (innerPoint j) (returnPoint j)) →
      RecursiveProfileForestCode n k center
        (ProfileRefinementForest.ofList (List.ofFn childTree)) start outerPoint
  | 0, _childTree, _start, _innerPoint, _returnPoint, _outerPoint,
      assembly, _children => by
        exact assembly.2.2
  | q + 1, childTree, start, innerPoint, returnPoint, outerPoint,
      assembly, children => by
        let tailTree : Fin q → ProfileRefinementTree :=
          fun j ↦ childTree j.succ
        have htree : List.ofFn childTree =
            childTree 0 :: List.ofFn tailTree := by
          exact List.ofFn_succ
        rw [htree, ProfileRefinementForest.ofList]
        refine ⟨innerPoint 0, returnPoint 0, ?_, children 0, ?_⟩
        · let source := assembly.1 0
          have hstart : middleStage start.1
              (fun j ↦ (returnPoint j).1) (0 : Fin (q + 1)).castSucc =
                start.1 := by
            rw [show (0 : Fin (q + 1)).castSucc =
              (0 : Fin (q + 1 + 1)) by ext; rfl]
            rfl
          refine ⟨source.1, ?_, ?_⟩
          · simpa only [source, hstart] using source.2.1
          · simpa only [source, hstart] using source.2.2
        · exact recursiveProfileForestCodeOfAssembly n k center q tailTree
            (returnPoint 0) (fun j ↦ innerPoint j.succ)
            (fun j ↦ returnPoint j.succ) outerPoint
            (erasedParentAssemblyTail assembly) (fun j ↦ children j.succ)

/-- Parse one genuine parent boundary-excursion word once every extracted
child return has itself been parsed recursively.  Exact source-word recovery
then reduces to the corresponding recovery statement for those children. -/
def recursiveProfileGapCodeOfBoundaryExcursion
    {n k q : ℕ} {center : Point}
    (hn : 2 ≤ n) (hk0 : 0 < k) (hk : k + 1 ≤ n)
    (u : ProfileCycleMiddlePoint n k center)
    (w : ProfileCycleOuterPoint n k center)
    (parent : BoundaryExcursionExitWordCode
      (profileOuterBoundary n k center)
      (profileInnerBoundary n k center)
      (profileInnerBoundary n (k + 1) center) u.1 q w.1)
    (childTree : Fin q → ProfileRefinementTree)
    (children : (j : Fin q) →
      RecursiveProfileGapCode n (k + 1) center (childTree j)
        (extractedProfileInnerPoint u w parent j)
        (extractedProfileMiddlePoint hn hk0 hk u w parent j.succ)) :
    RecursiveProfileGapCode n k center
      (.node (ProfileRefinementForest.ofList (List.ofFn childTree))) u w :=
  recursiveProfileForestCodeOfAssembly n k center q childTree u
    (extractedProfileInnerPoint u w parent)
    (fun j ↦ extractedProfileMiddlePoint hn hk0 hk u w parent j.succ) w
    (extractedProfileAssemblyCode hn hk0 hk u w parent) children

end

end Erdos1165.AnnularRecursiveProfileSourceParser
