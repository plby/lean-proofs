/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
import ErdosProblems.Erdos1165.AnnularRecursiveProfileActualParser

/-!
# Literal recursive codes for actual profile segments

This file transports the canonical actual parent word to arbitrary supported
endpoint subtypes with the same underlying points.  Recursive calls can
therefore target the literal endpoints extracted by their parent without a
costly equality between dependent subtype packages.
-/

namespace Erdos1165.AnnularRecursiveProfileActualCode

open AnnularProfileClocks AnnularProfileGapAtoms AnnularProfileLevelSkeleton
open AnnularOffspringScan
open AnnularProfileChildWordIdentification AnnularExtractedProfileSpineCode
open AnnularErasedParentSpineRowPartition
open AnnularOffspringKernelRadial AnnularRecursiveDecoratedProfileCode
open AnnularRecursiveProfileActualParser
open AnnularRecursiveProfileActualParser.ActualProfileEdgeData
open AnnularRecursiveProfileActualParser.ActualProfileSegmentData
open AnnularRecursiveProfileCodeAssembly
open AnnularRecursiveProfileShape
open AnnularRecursiveProfileSourceParser
open ThickPoint

noncomputable section

attribute [local instance] Classical.propDecidable

/-- A refinement tree together with a literal code at fixed endpoints.  This
opaque wrapper prevents the equation compiler from repeatedly reducing the
recursive code family while it checks the actual-data recursion. -/
structure ActualParsedProfileGap
    (n k : ℕ) (x : Point)
    (u : ProfileCycleMiddlePoint n k x)
    (w : ProfileCycleOuterPoint n k x) where
  tree : ProfileRefinementTree
  code : RecursiveProfileGapCode n k x tree u w

/-- Transport the canonical actual parent word to supported endpoint subtype
representatives with the same underlying points. -/
def actualParentBoundaryCodeAt
    {omega : StepPath} {n horizon k parent : ℕ} {x : Point}
    (hcomplete : profileGapExitTime (trajectory omega) n horizon x k parent ≤
      horizon)
    (u : ProfileCycleMiddlePoint n k x)
    (w : ProfileCycleOuterPoint n k x)
    (hu : profileGapStartPoint omega n horizon x k parent = u.1)
    (hw : profileGapExitPoint omega n horizon x k parent = w.1) :
    AnnularBoundaryExcursionKernel.BoundaryExcursionExitWordCode
      (profileOuterBoundary n k x) (profileInnerBoundary n k x)
      (profileInnerBoundary n (k + 1) x) u.1
      (profileGapOffspringCount omega n horizon x k parent) w.1 := by
  let source := profileGapBoundaryExcursionWordCode hcomplete
  refine ⟨source.1, ?_, ?_, ?_⟩
  · simpa only [← hu] using source.2.1
  · simpa only [← hu] using source.2.2.1
  · simpa only [← hu, ← hw] using source.2.2.2

@[simp] theorem actualParentBoundaryCodeAt_val
    {omega : StepPath} {n horizon k parent : ℕ} {x : Point}
    (hcomplete : profileGapExitTime (trajectory omega) n horizon x k parent ≤
      horizon)
    (u : ProfileCycleMiddlePoint n k x)
    (w : ProfileCycleOuterPoint n k x)
    (hu : profileGapStartPoint omega n horizon x k parent = u.1)
    (hw : profileGapExitPoint omega n horizon x k parent = w.1) :
    (actualParentBoundaryCodeAt hcomplete u w hu hw).1 =
      profileGapStoppedWord omega n horizon x k parent := rfl

/-- Transporting endpoint subtype representatives does not alter the parent
walk read from its stopped word. -/
theorem actualParentBoundaryCodeAt_path_eq
    {omega : StepPath} {n horizon k parent : ℕ} {x : Point}
    (hcomplete : profileGapExitTime (trajectory omega) n horizon x k parent ≤
      horizon)
    (u : ProfileCycleMiddlePoint n k x)
    (w : ProfileCycleOuterPoint n k x)
    (hu : profileGapStartPoint omega n horizon x k parent = u.1)
    (hw : profileGapExitPoint omega n horizon x k parent = w.1) :
    PlanarPotential.trajectoryFrom
        (profileGapStartPoint omega n horizon x k parent)
        (MarkedBridgeFactorization.extendStoppedWord
          (profileGapStoppedWord omega n horizon x k parent)) =
      PlanarPotential.trajectoryFrom u.1
        (MarkedBridgeFactorization.extendStoppedWord
          (actualParentBoundaryCodeAt hcomplete u w hu hw).1) := by
  funext r
  exact congrArg₂
    (fun start word ↦ PlanarPotential.trajectoryFrom start
      (MarkedBridgeFactorization.extendStoppedWord word) r)
    hu (actualParentBoundaryCodeAt_val _ _ _ _ _).symm

@[simp] theorem actualParentBoundaryCodeAt_length
    {omega : StepPath} {n horizon k parent : ℕ} {x : Point}
    (hcomplete : profileGapExitTime (trajectory omega) n horizon x k parent ≤
      horizon)
    (u : ProfileCycleMiddlePoint n k x)
    (w : ProfileCycleOuterPoint n k x)
    (hu : profileGapStartPoint omega n horizon x k parent = u.1)
    (hw : profileGapExitPoint omega n horizon x k parent = w.1) :
    (actualParentBoundaryCodeAt hcomplete u w hu hw).1.1 =
      profileGapLength omega n horizon x k parent := by
  rw [actualParentBoundaryCodeAt_val]
  rfl

/-- Leaf actual profile word at transported supported endpoints. -/
def actualLeafGapCodeAt
    {omega : StepPath} {n horizon k parent : ℕ} {x : Point}
    (hcomplete : profileGapExitTime (trajectory omega) n horizon x k parent ≤
      horizon)
    (u : ProfileCycleMiddlePoint n k x)
    (w : ProfileCycleOuterPoint n k x)
    (hu : profileGapStartPoint omega n horizon x k parent = u.1)
    (hw : profileGapExitPoint omega n horizon x k parent = w.1) :
    RecursiveProfileGapCode n k x .leaf u w := by
  let source := actualParentBoundaryCodeAt hcomplete u w hu hw
  exact ⟨source.1, source.2.1, source.2.2.2⟩

@[simp] theorem actualLeafGapCodeAt_val
    {omega : StepPath} {n horizon k parent : ℕ} {x : Point}
    (hcomplete : profileGapExitTime (trajectory omega) n horizon x k parent ≤
      horizon)
    (u : ProfileCycleMiddlePoint n k x)
    (w : ProfileCycleOuterPoint n k x)
    (hu : profileGapStartPoint omega n horizon x k parent = u.1)
    (hw : profileGapExitPoint omega n horizon x k parent = w.1) :
    (actualLeafGapCodeAt hcomplete u w hu hw).1 =
      profileGapStoppedWord omega n horizon x k parent := rfl

/-- Package a transported actual leaf without exposing the recursive code
family to the later equation compiler. -/
def actualLeafParsedProfileGap
    {omega : StepPath} {n horizon k parent : ℕ} {x : Point}
    (hcomplete : profileGapExitTime (trajectory omega) n horizon x k parent ≤
      horizon)
    (u : ProfileCycleMiddlePoint n k x)
    (w : ProfileCycleOuterPoint n k x)
    (hu : profileGapStartPoint omega n horizon x k parent = u.1)
    (hw : profileGapExitPoint omega n horizon x k parent = w.1) :
    ActualParsedProfileGap n k x u w :=
  ⟨.leaf, actualLeafGapCodeAt hcomplete u w hu hw⟩

/-- A path and horizon equality identify the underlying extracted child
entrance point without unfolding a dependent parent code at the call site. -/
theorem sourcePath_finish_eq_extractedProfileInnerPoint
    {n k q : ℕ} {x : Point}
    (u : ProfileCycleMiddlePoint n k x)
    (w : ProfileCycleOuterPoint n k x)
    (parent : AnnularBoundaryExcursionKernel.BoundaryExcursionExitWordCode
      (profileOuterBoundary n k x) (profileInnerBoundary n k x)
      (profileInnerBoundary n (k + 1) x) u.1 q w.1)
    (sourcePath : WalkPath) (L : ℕ) (j : Fin q)
    (hpath : sourcePath = PlanarPotential.trajectoryFrom u.1
      (MarkedBridgeFactorization.extendStoppedWord parent.1))
    (hlen : L = parent.1.1) :
    sourcePath (excursionFinish sourcePath (profileInnerBoundary n k x)
      (profileInnerBoundary n (k + 1) x) L j) =
      (extractedProfileInnerPoint u w parent j).1 := by
  unfold extractedProfileInnerPoint
  rw [hpath, hlen]

/-- Corresponding identification for the following extracted return point. -/
theorem sourcePath_start_eq_extractedProfileMiddlePoint
    {n k q : ℕ} {x : Point}
    (hn : 2 ≤ n) (hk0 : 0 < k) (hk : k + 1 ≤ n)
    (u : ProfileCycleMiddlePoint n k x)
    (w : ProfileCycleOuterPoint n k x)
    (parent : AnnularBoundaryExcursionKernel.BoundaryExcursionExitWordCode
      (profileOuterBoundary n k x) (profileInnerBoundary n k x)
      (profileInnerBoundary n (k + 1) x) u.1 q w.1)
    (sourcePath : WalkPath) (L : ℕ) (j : Fin q)
    (hpath : sourcePath = PlanarPotential.trajectoryFrom u.1
      (MarkedBridgeFactorization.extendStoppedWord parent.1))
    (hlen : L = parent.1.1) :
    sourcePath (excursionStart sourcePath (profileInnerBoundary n k x)
      (profileInnerBoundary n (k + 1) x) L (j + 1)) =
      (extractedProfileMiddlePoint hn hk0 hk u w parent j.succ).1 := by
  unfold extractedProfileMiddlePoint
  rw [hpath, hlen]
  simp only [Fin.val_succ]

/-- The literal source finish equals the extracted entrance for transported
parent endpoint representatives. -/
theorem sourceFinish_eq_extracted_at
    {omega : StepPath} {n horizon k parents children : ℕ} {x : Point}
    (edge : ActualProfileEdgeData omega n horizon x k parents children)
    (i : Fin parents)
    (u : ProfileCycleMiddlePoint n k x)
    (w : ProfileCycleOuterPoint n k x)
    (hu : profileGapStartPoint omega n horizon x k i = u.1)
    (hw : profileGapExitPoint omega n horizon x k i = w.1)
    (j : Fin (profileGapOffspringCount omega n horizon x k i)) :
    (PlanarPotential.trajectoryFrom
      (profileGapStartPoint omega n horizon x k i)
      (MarkedBridgeFactorization.extendStoppedWord
        (profileGapStoppedWord omega n horizon x k i)))
      (excursionFinish
        (profileGapWalk omega n horizon x k i)
        (profileInnerBoundary n k x) (profileInnerBoundary n (k + 1) x)
        (profileGapLength omega n horizon x k i) j) =
      (extractedProfileInnerPoint u w
        (actualParentBoundaryCodeAt (edge.hcomplete i i.isLt) u w hu hw)
        j).1 := by
  let parent := actualParentBoundaryCodeAt
    (edge.hcomplete i i.isLt) u w hu hw
  let sourcePath := PlanarPotential.trajectoryFrom
    (profileGapStartPoint omega n horizon x k i)
    (MarkedBridgeFactorization.extendStoppedWord
      (profileGapStoppedWord omega n horizon x k i))
  let targetPath := PlanarPotential.trajectoryFrom u.1
    (MarkedBridgeFactorization.extendStoppedWord parent.1)
  have hpath : sourcePath = targetPath :=
    actualParentBoundaryCodeAt_path_eq _ _ _ _ _
  have hlen : parent.1.1 = profileGapLength omega n horizon x k i :=
    actualParentBoundaryCodeAt_length _ _ _ _ _
  rw [← (extractedProfileReturn_clocks_eq_actual
    (edge.hcomplete i i.isLt) j).1]
  exact sourcePath_finish_eq_extractedProfileInnerPoint u w parent
    sourcePath (profileGapLength omega n horizon x k i) j hpath hlen.symm

/-- The global child entrance equals the parent-local extracted entrance even
after transporting the parent endpoint subtype representatives. -/
theorem childMiddlePoint_eq_extracted_at
    {omega : StepPath} {n horizon k parents children : ℕ} {x : Point}
    (edge : ActualProfileEdgeData omega n horizon x k parents children)
    (i : Fin parents)
    (u : ProfileCycleMiddlePoint n k x)
    (w : ProfileCycleOuterPoint n k x)
    (hu : profileGapStartPoint omega n horizon x k i = u.1)
    (hw : profileGapExitPoint omega n horizon x k i = w.1)
    (j : Fin (profileGapOffspringCount omega n horizon x k i)) :
    profileGapStartPoint omega n horizon x (k + 1) (edge.childIndex i j) =
      (extractedProfileInnerPoint u w
        (actualParentBoundaryCodeAt (edge.hcomplete i i.isLt) u w hu hw)
        j).1 := by
  calc
    _ = (PlanarPotential.trajectoryFrom
          (profileGapStartPoint omega n horizon x k i)
          (MarkedBridgeFactorization.extendStoppedWord
            (profileGapStoppedWord omega n horizon x k i)))
        (excursionFinish
          (profileGapWalk omega n horizon x k i)
          (profileInnerBoundary n k x) (profileInnerBoundary n (k + 1) x)
          (profileGapLength omega n horizon x k i) j) :=
      edge.actualProfileChildMiddle_eq_extracted i j
    _ = _ := sourceFinish_eq_extracted_at edge i u w hu hw j

/-- The literal source return equals the transported extracted return. -/
theorem sourceStart_eq_extracted_at
    {omega : StepPath} {n horizon k parents children : ℕ} {x : Point}
    (edge : ActualProfileEdgeData omega n horizon x k parents children)
    (i : Fin parents)
    (u : ProfileCycleMiddlePoint n k x)
    (w : ProfileCycleOuterPoint n k x)
    (hu : profileGapStartPoint omega n horizon x k i = u.1)
    (hw : profileGapExitPoint omega n horizon x k i = w.1)
    (j : Fin (profileGapOffspringCount omega n horizon x k i)) :
    (PlanarPotential.trajectoryFrom
      (profileGapStartPoint omega n horizon x k i)
      (MarkedBridgeFactorization.extendStoppedWord
        (profileGapStoppedWord omega n horizon x k i)))
      (excursionStart
        (profileGapWalk omega n horizon x k i)
        (profileInnerBoundary n k x) (profileInnerBoundary n (k + 1) x)
        (profileGapLength omega n horizon x k i) (j + 1)) =
      (extractedProfileMiddlePoint edge.hn edge.hk0 edge.hk u w
        (actualParentBoundaryCodeAt (edge.hcomplete i i.isLt) u w hu hw)
        j.succ).1 := by
  let parent := actualParentBoundaryCodeAt
    (edge.hcomplete i i.isLt) u w hu hw
  let sourcePath := PlanarPotential.trajectoryFrom
    (profileGapStartPoint omega n horizon x k i)
    (MarkedBridgeFactorization.extendStoppedWord
      (profileGapStoppedWord omega n horizon x k i))
  let targetPath := PlanarPotential.trajectoryFrom u.1
    (MarkedBridgeFactorization.extendStoppedWord parent.1)
  have hpath : sourcePath = targetPath :=
    actualParentBoundaryCodeAt_path_eq _ _ _ _ _
  have hlen : parent.1.1 = profileGapLength omega n horizon x k i :=
    actualParentBoundaryCodeAt_length _ _ _ _ _
  rw [← (extractedProfileReturn_clocks_eq_actual
    (edge.hcomplete i i.isLt) j).2]
  exact sourcePath_start_eq_extractedProfileMiddlePoint
    edge.hn edge.hk0 edge.hk u w parent sourcePath
    (profileGapLength omega n horizon x k i) j hpath hlen.symm

/-- The global child exit equals the parent-local extracted return endpoint
after the same endpoint transport. -/
theorem childOuterPoint_eq_extracted_at
    {omega : StepPath} {n horizon k parents children : ℕ} {x : Point}
    (edge : ActualProfileEdgeData omega n horizon x k parents children)
    (i : Fin parents)
    (u : ProfileCycleMiddlePoint n k x)
    (w : ProfileCycleOuterPoint n k x)
    (hu : profileGapStartPoint omega n horizon x k i = u.1)
    (hw : profileGapExitPoint omega n horizon x k i = w.1)
    (j : Fin (profileGapOffspringCount omega n horizon x k i)) :
    profileGapExitPoint omega n horizon x (k + 1) (edge.childIndex i j) =
      (extractedProfileMiddlePoint edge.hn edge.hk0 edge.hk u w
        (actualParentBoundaryCodeAt (edge.hcomplete i i.isLt) u w hu hw)
        j.succ).1 := by
  calc
    _ = (PlanarPotential.trajectoryFrom
          (profileGapStartPoint omega n horizon x k i)
          (MarkedBridgeFactorization.extendStoppedWord
            (profileGapStoppedWord omega n horizon x k i)))
        (excursionStart
          (profileGapWalk omega n horizon x k i)
          (profileInnerBoundary n k x) (profileInnerBoundary n (k + 1) x)
          (profileGapLength omega n horizon x k i) (j + 1)) :=
      edge.actualProfileChildOuter_eq_extracted i j
    _ = _ := sourceStart_eq_extracted_at edge i u w hu hw j

/-- A forest read directly from a finite child family.  Unlike
`ofList (List.ofFn children)`, this presentation reduces definitionally at
successor cardinalities and therefore introduces no dependent casts in the
literal source parser. -/
def profileRefinementForestOfFin :
    (q : ℕ) → (Fin q → ProfileRefinementTree) → ProfileRefinementForest
  | 0, _children => .nil
  | q + 1, children =>
      .cons (children 0)
        (profileRefinementForestOfFin q (fun j ↦ children j.succ))

/-- The cast-free finite-family forest is the canonical list forest. -/
theorem profileRefinementForestOfFin_eq_ofList_ofFn :
    ∀ (q : ℕ) (children : Fin q → ProfileRefinementTree),
      profileRefinementForestOfFin q children =
        ProfileRefinementForest.ofList (List.ofFn children)
  | 0, _children => rfl
  | q + 1, children => by
      rw [List.ofFn_succ, ProfileRefinementForest.ofList,
        profileRefinementForestOfFin,
        profileRefinementForestOfFin_eq_ofList_ofFn]

/-- Cast-free structural inverse of an erased-parent assembly. -/
def recursiveProfileForestCodeOfAssemblyFin
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
        (profileRefinementForestOfFin q childTree) start outerPoint
  | 0, _childTree, _start, _innerPoint, _returnPoint, _outerPoint,
      assembly, _children => assembly.2.2
  | q + 1, childTree, start, innerPoint, returnPoint, outerPoint,
      assembly, children =>
      ⟨innerPoint 0, returnPoint 0, assembly.1 0, children 0,
        recursiveProfileForestCodeOfAssemblyFin n k center q
          (fun j ↦ childTree j.succ) (returnPoint 0)
          (fun j ↦ innerPoint j.succ) (fun j ↦ returnPoint j.succ)
          outerPoint (erasedParentAssemblyTail assembly)
          (fun j ↦ children j.succ)⟩

/-- Assemble one internal parsed node from a parent boundary excursion and
already parsed children. -/
def parsedProfileGapOfBoundaryExcursion
    {n k q : ℕ} {x : Point}
    (hn : 2 ≤ n) (hk0 : 0 < k) (hk : k + 1 ≤ n)
    (u : ProfileCycleMiddlePoint n k x)
    (w : ProfileCycleOuterPoint n k x)
    (parent : AnnularBoundaryExcursionKernel.BoundaryExcursionExitWordCode
      (profileOuterBoundary n k x) (profileInnerBoundary n k x)
      (profileInnerBoundary n (k + 1) x) u.1 q w.1)
    (childParsed : (j : Fin q) →
      ActualParsedProfileGap n (k + 1) x
        (extractedProfileInnerPoint u w parent j)
        (extractedProfileMiddlePoint hn hk0 hk u w parent j.succ)) :
    ActualParsedProfileGap n k x u w := by
  let childTree : Fin q → ProfileRefinementTree :=
    fun j ↦ (childParsed j).tree
  let childCodes : (j : Fin q) →
      RecursiveProfileGapCode n (k + 1) x (childTree j)
        (extractedProfileInnerPoint u w parent j)
        (extractedProfileMiddlePoint hn hk0 hk u w parent j.succ) :=
    fun j ↦ (childParsed j).code
  exact ⟨.node (profileRefinementForestOfFin q childTree),
    recursiveProfileForestCodeOfAssemblyFin n k x q childTree u
      (extractedProfileInnerPoint u w parent)
      (fun j ↦ extractedProfileMiddlePoint hn hk0 hk u w parent j.succ)
      w (extractedProfileAssemblyCode hn hk0 hk u w parent) childCodes⟩

/-- Parse one actual completed profile gap together with the refinement tree
actually read during recursion.  Keeping the tree in a sigma avoids forcing
the elaborator to normalize a large dependent tree index at every clause. -/
def actualParsedProfileGap
    {omega : StepPath} {n horizon : ℕ} {x : Point}
    (hn : 2 ≤ n) (hx : x ∈ candidateBox n) (rest : List ℕ) :
    ∀ {k a : ℕ},
      (hk0 : 0 < k) → (hdepth : k + rest.length ≤ n) →
      (data : ActualProfileSegmentData omega n horizon x k (a :: rest)) →
      (i : Fin a) →
      (u : ProfileCycleMiddlePoint n k x) →
      (w : ProfileCycleOuterPoint n k x) →
      profileGapStartPoint omega n horizon x k i = u.1 →
      profileGapExitPoint omega n horizon x k i = w.1 →
      ActualParsedProfileGap n k x u w :=
  List.rec (motive := fun rest ↦ ∀ {k a : ℕ},
      (hk0 : 0 < k) → (hdepth : k + rest.length ≤ n) →
      (data : ActualProfileSegmentData omega n horizon x k (a :: rest)) →
      (i : Fin a) →
      (u : ProfileCycleMiddlePoint n k x) →
      (w : ProfileCycleOuterPoint n k x) →
      profileGapStartPoint omega n horizon x k i = u.1 →
      profileGapExitPoint omega n horizon x k i = w.1 →
      ActualParsedProfileGap n k x u w)
    (fun _hk0 _hdepth data i u w hu hw ↦
      actualLeafParsedProfileGap (data.headComplete i i.isLt) u w hu hw)
    (fun b rest recurse {k a} hk0 hdepth data i u w hu hw ↦ by
      let edge := data.edgeData hn hx hk0 hdepth
      let childDepth : k + 1 + rest.length ≤ n := by
        simp only [List.length_cons] at hdepth
        omega
      let parent := actualParentBoundaryCodeAt
        (edge.hcomplete i i.isLt) u w hu hw
      apply parsedProfileGapOfBoundaryExcursion
        edge.hn edge.hk0 edge.hk u w parent
      intro j
      exact recurse (by omega) childDepth data.tail
          (edge.childIndex i j)
          (extractedProfileInnerPoint u w parent j)
          (extractedProfileMiddlePoint edge.hn edge.hk0 edge.hk
            u w parent j.succ)
          (childMiddlePoint_eq_extracted_at edge i u w hu hw j)
          (childOuterPoint_eq_extracted_at edge i u w hu hw j)
      )
    rest

/-- One-step equation of the actual parser at a nonterminal segment. -/
theorem actualParsedProfileGap_cons
    {omega : StepPath} {n horizon k a b : ℕ} {rest : List ℕ} {x : Point}
    (hn : 2 ≤ n) (hx : x ∈ candidateBox n) (hk0 : 0 < k)
    (hdepth : k + (b :: rest).length ≤ n)
    (data : ActualProfileSegmentData omega n horizon x k (a :: b :: rest))
    (i : Fin a) (u : ProfileCycleMiddlePoint n k x)
    (w : ProfileCycleOuterPoint n k x)
    (hu : profileGapStartPoint omega n horizon x k i = u.1)
    (hw : profileGapExitPoint omega n horizon x k i = w.1) :
    let edge := data.edgeData hn hx hk0 hdepth
    let parent := actualParentBoundaryCodeAt
      (edge.hcomplete i i.isLt) u w hu hw
    let childDepth : k + 1 + rest.length ≤ n := by
      simp only [List.length_cons] at hdepth
      omega
    let childParsed := fun j : Fin
        (profileGapOffspringCount omega n horizon x k i) ↦
      actualParsedProfileGap hn hx rest (by omega) childDepth data.tail
        (edge.childIndex i j)
        (extractedProfileInnerPoint u w parent j)
        (extractedProfileMiddlePoint edge.hn edge.hk0 edge.hk
          u w parent j.succ)
        (childMiddlePoint_eq_extracted_at edge i u w hu hw j)
        (childOuterPoint_eq_extracted_at edge i u w hu hw j)
    actualParsedProfileGap hn hx (b :: rest) hk0 hdepth data i u w hu hw =
      parsedProfileGapOfBoundaryExcursion
        edge.hn edge.hk0 edge.hk u w parent childParsed := rfl

/-- The tree read by the literal parser is exactly the canonical
parent-major refinement genealogy of the actual count segment. -/
theorem actualParsedProfileGap_tree
    {omega : StepPath} {n horizon : ℕ} {x : Point}
    (hn : 2 ≤ n) (hx : x ∈ candidateBox n) (rest : List ℕ) :
    ∀ {k a : ℕ} (hk0 : 0 < k) (hdepth : k + rest.length ≤ n)
      (data : ActualProfileSegmentData omega n horizon x k (a :: rest))
      (i : Fin a) (u : ProfileCycleMiddlePoint n k x)
      (w : ProfileCycleOuterPoint n k x)
      (hu : profileGapStartPoint omega n horizon x k i = u.1)
      (hw : profileGapExitPoint omega n horizon x k i = w.1),
      (actualParsedProfileGap hn hx rest hk0 hdepth data i u w hu hw).tree =
        refinementTrees hn hx hk0 hdepth data i := by
  induction rest with
  | nil =>
      intro k a hk0 hdepth data i u w hu hw
      rfl
  | cons b rest ih =>
      intro k a hk0 hdepth data i u w hu hw
      simp only [actualParsedProfileGap, List.rec]
      unfold parsedProfileGapOfBoundaryExcursion
      simp only [ActualParsedProfileGap.tree, refinementTrees]
      rw [profileRefinementForestOfFin_eq_ofList_ofFn]
      congr 3
      funext j
      apply ih (by omega) (by
        simp only [List.length_cons] at hdepth
        omega) data.tail ((data.edgeData hn hx hk0 hdepth).childIndex i j)
        (extractedProfileInnerPoint u w
          (actualParentBoundaryCodeAt
            ((data.edgeData hn hx hk0 hdepth).hcomplete i i.isLt)
              u w hu hw) j)
        (extractedProfileMiddlePoint
          (data.edgeData hn hx hk0 hdepth).hn
          (data.edgeData hn hx hk0 hdepth).hk0
          (data.edgeData hn hx hk0 hdepth).hk u w
          (actualParentBoundaryCodeAt
            ((data.edgeData hn hx hk0 hdepth).hcomplete i i.isLt)
              u w hu hw) j.succ)
        (childMiddlePoint_eq_extracted_at
          (data.edgeData hn hx hk0 hdepth) i u w hu hw j)
        (childOuterPoint_eq_extracted_at
          (data.edgeData hn hx hk0 hdepth) i u w hu hw j)

end

end Erdos1165.AnnularRecursiveProfileActualCode
