/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
import ErdosProblems.Erdos1165.AsymmetricPaddedActiveFactorization
import ErdosProblems.Erdos1165.AnnularRecursiveProfileActualCode

/-!
# Assembly of a decorated active padded segment

This is the cast-free finite recursion which feeds one extracted padded
parent, together with recursively decorated deleted returns, into the
literal padded-prelude code space.
-/

namespace Erdos1165.AsymmetricPaddedCodeAssembly

open scoped BigOperators ENNReal

open AnnularErasedParentSpineRowPartition AnnularProfileClocks
open AnnularRecursiveDecoratedProfileCode
open AnnularRecursiveProfileCodeAssembly
open AnnularRecursiveProfileSourceParser
open AsymmetricPaddedPreludeCode AsymmetricPaddedRemoteRenewal
open MarkedBridgeFactorization ThickPoint

noncomputable section

/-- Mass of an erased padded parent after replacing each deleted literal
return by a recursive child code with the same endpoints. -/
def paddedDecoratedAssemblyMass
    (n p : ℕ) (center : Point) {q : ℕ}
    {retainedBoundary : Set Point}
    {u : PaddedMiddlePoint n p center}
    {innerPoint : Fin q → PaddedInnerPoint n p center}
    {returnPoint : Fin q → PaddedMiddlePoint n p center}
    {outerPoint : Point} {tree : Fin q → ProfileRefinementTree}
    (assembly : ErasedParentAssemblyCode q retainedBoundary
      (profileInnerBoundary n (p - 1) center) u.1
      (fun j ↦ (innerPoint j).1) (fun j ↦ (returnPoint j).1) outerPoint)
    (children : (j : Fin q) → RecursiveProfileGapCode n p center
      (tree j) (innerPoint j) (returnPoint j)) : ℝ≥0∞ :=
  (∏ j, stoppedWordMass (assembly.1 j).1) *
    (∏ j, recursiveProfileGapCodeMass n p center
      (tree j) (innerPoint j) (returnPoint j) (children j)) *
      stoppedWordMass assembly.2.2.1

/-- Literal direction list of the same decorated padded parent. -/
def paddedDecoratedAssemblyList
    (n p : ℕ) (center : Point) {q : ℕ}
    {retainedBoundary : Set Point}
    {u : PaddedMiddlePoint n p center}
    {innerPoint : Fin q → PaddedInnerPoint n p center}
    {returnPoint : Fin q → PaddedMiddlePoint n p center}
    {outerPoint : Point} {tree : Fin q → ProfileRefinementTree}
    (assembly : ErasedParentAssemblyCode q retainedBoundary
      (profileInnerBoundary n (p - 1) center) u.1
      (fun j ↦ (innerPoint j).1) (fun j ↦ (returnPoint j).1) outerPoint)
    (children : (j : Fin q) → RecursiveProfileGapCode n p center
      (tree j) (innerPoint j) (returnPoint j)) : List Direction :=
  interleavedErasedParentList q
    (fun j ↦ List.ofFn (assembly.1 j).1.2)
    (fun j ↦ recursiveProfileGapList n p center
      (tree j) (innerPoint j) (returnPoint j) (children j))
    (List.ofFn assembly.2.2.1.2)

/-- Cast-free list representation of a finite tree family. -/
def finTreeList : ∀ q : ℕ, (Fin q → ProfileRefinementTree) →
    List ProfileRefinementTree
  | 0, _tree => []
  | q + 1, tree => tree 0 :: finTreeList q (fun j ↦ tree j.succ)

@[simp] theorem finTreeList_eq_ofFn : ∀ (q : ℕ)
    (tree : Fin q → ProfileRefinementTree),
    finTreeList q tree = List.ofFn tree
  | 0, _tree => rfl
  | q + 1, tree => by
      rw [finTreeList, List.ofFn_succ, finTreeList_eq_ofFn]

/-- Consume one complete active padded parent, then continue with the
remaining segments and trees. -/
def paddedActiveCodeOfAssemblyFin
    (n l p : ℕ) (center : Point) :
    ∀ (q : ℕ) (tree : Fin q → ProfileRefinementTree)
      (u : PaddedMiddlePoint n p center)
      (innerPoint : Fin q → PaddedInnerPoint n p center)
      (returnPoint : Fin q → PaddedMiddlePoint n p center)
      (w : PaddedOuterPoint n l center),
      ErasedParentAssemblyCode q
        (profileInnerBoundary n p center ∪ profileInnerBoundary n l center)
        (profileInnerBoundary n (p - 1) center) u.1
        (fun j ↦ (innerPoint j).1) (fun j ↦ (returnPoint j).1) w.1 →
      ((j : Fin q) → RecursiveProfileGapCode n p center
        (tree j) (innerPoint j) (returnPoint j)) →
      ∀ {segments : List
          ((PaddedNearPoint n l center ⊕ PaddedMiddlePoint n p center) ×
            PaddedOuterPoint n l center)}
        {restTrees : List ProfileRefinementTree},
        PaddedPreludeMultiCode n l p center segments restTrees →
        PaddedPreludeMultiCode n l p center
          ((Sum.inr u, w) :: segments) (finTreeList q tree ++ restTrees)
  | 0, _tree, u, _innerPoint, _returnPoint, w, assembly, _children,
      segments, [], rest =>
      .activeEscapeDone assembly.2.2 rest
  | 0, _tree, u, _innerPoint, _returnPoint, w, assembly, _children,
      segments, _head :: _tail, rest =>
      .activeEscape assembly.2.2 rest
  | q + 1, tree, u, innerPoint, returnPoint, w, assembly, children,
      segments, restTrees, rest => by
      let firstSource := assembly.1 0
      have hstart : middleStage u.1
          (fun j ↦ (returnPoint j).1) (0 : Fin (q + 1)).castSucc = u.1 := by
        unfold middleStage
        rw [show ((0 : Fin (q + 1)).castSucc : Fin (q + 2)) = 0 by rfl,
          Fin.cons_zero]
      let first : BoundaryExitWordCode
          (profileInnerBoundary n p center ∪ profileInnerBoundary n l center)
          u.1 (innerPoint 0).1 := by
        refine ⟨firstSource.1, ?_, ?_⟩
        · simpa only [firstSource, hstart] using firstSource.2.1
        · simpa only [firstSource, hstart] using firstSource.2.2
      let tail := paddedActiveCodeOfAssemblyFin n l p center q
        (fun j ↦ tree j.succ) (returnPoint 0)
        (fun j ↦ innerPoint j.succ) (fun j ↦ returnPoint j.succ) w
        (erasedParentAssemblyTail assembly) (fun j ↦ children j.succ) rest
      exact PaddedPreludeMultiCode.activeChild
        (innerPoint 0) (returnPoint 0) first (children 0) tail

/-- The active-code constructor preserves the exact decorated product mass. -/
theorem paddedActiveCodeOfAssemblyFin_mass
    (n l p : ℕ) (center : Point) :
    ∀ (q : ℕ) (tree : Fin q → ProfileRefinementTree)
      (u : PaddedMiddlePoint n p center)
      (innerPoint : Fin q → PaddedInnerPoint n p center)
      (returnPoint : Fin q → PaddedMiddlePoint n p center)
      (w : PaddedOuterPoint n l center)
      (assembly : ErasedParentAssemblyCode q
        (profileInnerBoundary n p center ∪ profileInnerBoundary n l center)
        (profileInnerBoundary n (p - 1) center) u.1
        (fun j ↦ (innerPoint j).1) (fun j ↦ (returnPoint j).1) w.1)
      (children : (j : Fin q) → RecursiveProfileGapCode n p center
        (tree j) (innerPoint j) (returnPoint j))
      {segments : List
        ((PaddedNearPoint n l center ⊕ PaddedMiddlePoint n p center) ×
          PaddedOuterPoint n l center)}
      {restTrees : List ProfileRefinementTree}
      (rest : PaddedPreludeMultiCode n l p center segments restTrees),
      paddedPreludeMultiCodeMass n l p center
          (paddedActiveCodeOfAssemblyFin n l p center q tree u innerPoint
            returnPoint w assembly children rest) =
        paddedDecoratedAssemblyMass n p center assembly children *
          paddedPreludeMultiCodeMass n l p center rest
  | 0, _tree, _u, _innerPoint, _returnPoint, _w, assembly, _children,
      _segments, [], rest => by
      simp [paddedActiveCodeOfAssemblyFin, paddedDecoratedAssemblyMass,
        paddedPreludeMultiCodeMass]
  | 0, _tree, _u, _innerPoint, _returnPoint, _w, assembly, _children,
      _segments, _head :: _tail, rest => by
      simp [paddedActiveCodeOfAssemblyFin, paddedDecoratedAssemblyMass,
        paddedPreludeMultiCodeMass]
  | q + 1, tree, u, innerPoint, returnPoint, w, assembly, children,
      segments, restTrees, rest => by
      simp only [paddedActiveCodeOfAssemblyFin, finTreeList,
        List.cons_append, paddedPreludeMultiCodeMass]
      rw [paddedActiveCodeOfAssemblyFin_mass]
      unfold paddedDecoratedAssemblyMass
      rw [Fin.prod_univ_succ, Fin.prod_univ_succ]
      simp only [erasedParentAssemblyTail]
      ac_rfl

/-- The active-code constructor prepends exactly the decorated parent word
to the list of already completed coarse segment words. -/
theorem paddedActiveCodeOfAssemblyFin_words
    (n l p : ℕ) (center : Point) :
    ∀ (q : ℕ) (tree : Fin q → ProfileRefinementTree)
      (u : PaddedMiddlePoint n p center)
      (innerPoint : Fin q → PaddedInnerPoint n p center)
      (returnPoint : Fin q → PaddedMiddlePoint n p center)
      (w : PaddedOuterPoint n l center)
      (assembly : ErasedParentAssemblyCode q
        (profileInnerBoundary n p center ∪ profileInnerBoundary n l center)
        (profileInnerBoundary n (p - 1) center) u.1
        (fun j ↦ (innerPoint j).1) (fun j ↦ (returnPoint j).1) w.1)
      (children : (j : Fin q) → RecursiveProfileGapCode n p center
        (tree j) (innerPoint j) (returnPoint j))
      {segments : List
        ((PaddedNearPoint n l center ⊕ PaddedMiddlePoint n p center) ×
          PaddedOuterPoint n l center)}
      {restTrees : List ProfileRefinementTree}
      (rest : PaddedPreludeMultiCode n l p center segments restTrees),
      paddedPreludeMultiCodeWords n l p center
          (paddedActiveCodeOfAssemblyFin n l p center q tree u innerPoint
            returnPoint w assembly children rest) =
        paddedDecoratedAssemblyList n p center assembly children ::
          paddedPreludeMultiCodeWords n l p center rest
  | 0, _tree, _u, _innerPoint, _returnPoint, _w, assembly, _children,
      _segments, [], rest => by
      simp [paddedActiveCodeOfAssemblyFin, paddedPreludeMultiCodeWords,
        paddedDecoratedAssemblyList, interleavedErasedParentList]
  | 0, _tree, _u, _innerPoint, _returnPoint, _w, assembly, _children,
      _segments, _head :: _tail, rest => by
      simp [paddedActiveCodeOfAssemblyFin, paddedPreludeMultiCodeWords,
        paddedDecoratedAssemblyList, interleavedErasedParentList]
  | q + 1, tree, u, innerPoint, returnPoint, w, assembly, children,
      segments, restTrees, rest => by
      simp only [paddedActiveCodeOfAssemblyFin, finTreeList,
        List.cons_append, paddedPreludeMultiCodeWords]
      rw [paddedActiveCodeOfAssemblyFin_words]
      simp only [prependHead]
      congr 2

end

end Erdos1165.AsymmetricPaddedCodeAssembly
