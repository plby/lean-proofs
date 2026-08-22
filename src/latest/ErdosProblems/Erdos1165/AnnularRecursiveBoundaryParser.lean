/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
import ErdosProblems.Erdos1165.AnnularRecursiveProfileSourceRecovery

/-!
# Finite-depth recursive parsing of one boundary-exit word

The source parser used for a complete profile starts from global profile
clocks.  At the padded interface it is more convenient to parse each deleted
return from its own stopped word.  This file performs that local parse for a
prescribed remaining depth.  The resulting recursive code has the same
literal direction list as the input word and satisfies the physical fitting
predicate.
-/

namespace Erdos1165.AnnularRecursiveBoundaryParser

open AnnularBoundaryExcursionKernel AnnularErasedParentSpineRowPartition
open AnnularExtractedProfileSpineCode AnnularOffspringKernelRadial
open AnnularProfileClocks AnnularRecursiveDecoratedProfileCode
open AnnularRecursiveProfileActualCode
open AnnularRecursiveProfileCodeAssembly
open AnnularRecursiveProfileSourceRecovery
open MarkedBridgeFactorization ThickPoint

noncomputable section

/-- A finite-depth recursive parse of one literal profile-gap word. -/
structure ParsedBoundaryGap
    (n k : ℕ) (center : Point)
    (u : ProfileCycleMiddlePoint n k center)
    (w : ProfileCycleOuterPoint n k center)
    (source : BoundaryExitWordCode (profileOuterBoundary n k center)
      u.1 w.1) where
  tree : ProfileRefinementTree
  fits : profileRefinementTreeFits n k tree
  code : RecursiveProfileGapCode n k center tree u w
  list_eq : recursiveProfileGapList n k center tree u w code =
    List.ofFn source.1.2

/-- Forget the fitting and recovery certificates. -/
def ParsedBoundaryGap.toActual
    {n k : ℕ} {center : Point}
    {u : ProfileCycleMiddlePoint n k center}
    {w : ProfileCycleOuterPoint n k center}
    {source : BoundaryExitWordCode (profileOuterBoundary n k center)
      u.1 w.1}
    (parsed : ParsedBoundaryGap n k center u w source) :
    ActualParsedProfileGap n k center u w :=
  ⟨parsed.tree, parsed.code⟩

/-- The finite-family forest fits whenever each child fits one level deeper. -/
theorem profileRefinementForestFits_ofFin
    (n k q : ℕ) (tree : Fin q → ProfileRefinementTree)
    (hfits : ∀ j, profileRefinementTreeFits n (k + 1) (tree j)) :
    profileRefinementForestFits n k
      (profileRefinementForestOfFin q tree) := by
  induction q with
  | zero => simp [profileRefinementForestOfFin,
      profileRefinementForestFits]
  | succ q ih =>
      simp only [profileRefinementForestOfFin,
        profileRefinementForestFits]
      exact ⟨hfits 0, ih (fun j ↦ tree j.succ) (fun j ↦ hfits j.succ)⟩

/-- Regard an ordinary first-exit word as a parent with its canonically
counted next-level returns. -/
def boundaryExitWordAsExcursionCode
    {n k : ℕ} {center : Point}
    (u : ProfileCycleMiddlePoint n k center)
    (w : ProfileCycleOuterPoint n k center)
    (source : BoundaryExitWordCode (profileOuterBoundary n k center)
      u.1 w.1) :
    BoundaryExcursionExitWordCode
      (profileOuterBoundary n k center)
      (profileInnerBoundary n k center)
      (profileInnerBoundary n (k + 1) center) u.1
      (boundaryExcursionCount
        (profileInnerBoundary n k center)
        (profileInnerBoundary n (k + 1) center) u.1
        (extendStoppedWord source.1) source.1.1) w.1 :=
  ⟨source.1, source.2.1, rfl, source.2.2⟩

/-- Parse a boundary-exit word through exactly `depth` deeper profile
levels. -/
def parseBoundaryGap
    (n : ℕ) (center : Point) (hn : 2 ≤ n) :
    ∀ (depth k : ℕ) (hk0 : 0 < k) (hdepth : k + depth ≤ n)
      (u : ProfileCycleMiddlePoint n k center)
      (w : ProfileCycleOuterPoint n k center)
      (source : BoundaryExitWordCode (profileOuterBoundary n k center)
        u.1 w.1),
      ParsedBoundaryGap n k center u w source
  | 0, _k, _hk0, _hdepth, u, w, source =>
      { tree := .leaf
        fits := trivial
        code := source
        list_eq := rfl }
  | depth + 1, k, hk0, hdepth, u, w, source => by
      let q := boundaryExcursionCount
        (profileInnerBoundary n k center)
        (profileInnerBoundary n (k + 1) center) u.1
        (extendStoppedWord source.1) source.1.1
      let parent := boundaryExitWordAsExcursionCode u w source
      let innerPoint : Fin q → ProfileCycleInnerPoint n k center :=
        extractedProfileInnerPoint u w parent
      let returnPoint : Fin q → ProfileCycleMiddlePoint n k center :=
        fun j ↦ extractedProfileMiddlePoint hn hk0 (by omega) u w parent j.succ
      let childSource : (j : Fin q) → BoundaryExitWordCode
          (profileOuterBoundary n (k + 1) center)
          (innerPoint j).1 (returnPoint j).1 :=
        fun j ↦ extractedProfileReturnWordCode hn hk0 (by omega)
          u w parent j
      let childParsed : (j : Fin q) → ParsedBoundaryGap n (k + 1) center
          (innerPoint j) (returnPoint j) (childSource j) :=
        fun j ↦ parseBoundaryGap n center hn depth (k + 1) (by omega)
          (by omega) (innerPoint j) (returnPoint j) (childSource j)
      let actualChildren : (j : Fin q) → ActualParsedProfileGap
          n (k + 1) center (innerPoint j) (returnPoint j) :=
        fun j ↦ (childParsed j).toActual
      let actual := parsedProfileGapOfBoundaryExcursion hn hk0 (by omega)
        u w parent actualChildren
      refine
        { tree := actual.tree
          fits := ?_
          code := actual.code
          list_eq := ?_ }
      · change profileRefinementTreeFits n k
          (.node (profileRefinementForestOfFin q
            (fun j ↦ (childParsed j).tree)))
        exact ⟨by omega, profileRefinementForestFits_ofFin n k q
          (fun j ↦ (childParsed j).tree) (fun j ↦ (childParsed j).fits)⟩
      · change parsedProfileGapList actual = List.ofFn source.1.2
        have hchildren : ∀ j, parsedProfileGapList (actualChildren j) =
            extractedProfileReturnList hn hk0 (by omega) u w parent j := by
          intro j
          exact (childParsed j).list_eq.trans
            (extractedProfileReturnList_eq_codeList hn hk0 (by omega)
              u w parent j).symm
        exact (parsedProfileGapList_internal_eq_parent hn hk0 (by omega)
          u w parent actualChildren hchildren).trans (by rfl)

/-- The physical boundary word assembled from the local parse is literally
the source boundary word. -/
theorem boundaryWord_parseBoundaryGap
    (n : ℕ) (center : Point) (hn : 2 ≤ n)
    (depth k : ℕ) (hk0 : 0 < k) (hdepth : k + depth ≤ n)
    (u : ProfileCycleMiddlePoint n k center)
    (w : ProfileCycleOuterPoint n k center)
    (source : BoundaryExitWordCode (profileOuterBoundary n k center)
      u.1 w.1) :
    (recursiveProfileGapBoundaryExitWordCode n k center hn hk0
      (parseBoundaryGap n center hn depth k hk0 hdepth u w source).tree
      (parseBoundaryGap n center hn depth k hk0 hdepth u w source).fits
      u w
      (parseBoundaryGap n center hn depth k hk0 hdepth u w source).code).1 =
        source.1 := by
  rw [recursiveProfileGapBoundaryExitWordCode_val,
    (parseBoundaryGap n center hn depth k hk0 hdepth u w source).list_eq,
    AlternatingConcatPrefixFree.listStoppedWord_ofFn]

end

end Erdos1165.AnnularRecursiveBoundaryParser
