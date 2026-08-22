/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
import ErdosProblems.Erdos1165.AnnularRecursiveProfileActualCode

/-!
# Exact source recovery for actual recursive profile codes

The actual parser recursively replaces every deleted parent return by the
code parsed from the corresponding global child.  This file proves that the
literal recursive assembly nevertheless recovers the original stopped word
exactly.
-/

namespace Erdos1165.AnnularRecursiveProfileSourceRecovery

open AlternatingConcatPrefixFree AnnularErasedParentSpineRowPartition
open AnnularOffspringKernelRadial AnnularProfileClocks AnnularProfileGapAtoms
open AnnularProfileLevelSkeleton AnnularExtractedProfileSpineCode
open AnnularProfileChildClockIdentification
open AnnularProfileChildWordIdentification AnnularProfileNestedEdge
open AnnularProfileOffspringPartition
open AnnularRecursiveDecoratedProfileCode
open AnnularRecursiveProfileActualCode
open AnnularRecursiveProfileActualParser
open AnnularRecursiveProfileActualParser.ActualProfileEdgeData
open AnnularRecursiveProfileActualParser.ActualProfileSegmentData
open AnnularRecursiveProfileCodeAssembly AnnularRecursiveProfileShape
open AnnularRecursiveProfileShapeFits
open AnnularRecursiveProfileSourceParser
open MarkedBridgeFactorization ThickPoint

noncomputable section

attribute [local instance] Classical.propDecidable

/-- `ofFn` specialization of the forest depth constructor.  Keeping the
function opaque prevents the actual-clock indices from being normalized while
the generic forest theorem is applied. -/
theorem profileRefinementForestFits_ofFn
    {n k q : ℕ} (trees : Fin q → ProfileRefinementTree)
    (hfit : ∀ j, profileRefinementTreeFits n (k + 1) (trees j)) :
    profileRefinementForestFits n k
      (ProfileRefinementForest.ofList (List.ofFn trees)) := by
  apply profileRefinementForestFits_ofList
  intro child hchild
  rw [List.mem_ofFn] at hchild
  obtain ⟨j, rfl⟩ := hchild
  exact hfit j

/-- The literal deleted-return word depends only on the parent start and
stopped word, not on the endpoint subtype representatives or proof fields. -/
theorem extractedProfileReturnWordCode_stoppedWord_eq
    {n k q : ℕ} {x : Point}
    (hn : 2 ≤ n) (hk0 : 0 < k) (hk : k + 1 ≤ n)
    (u : ProfileCycleMiddlePoint n k x)
    (w : ProfileCycleOuterPoint n k x)
    (parent : AnnularBoundaryExcursionKernel.BoundaryExcursionExitWordCode
      (profileOuterBoundary n k x) (profileInnerBoundary n k x)
      (profileInnerBoundary n (k + 1) x) u.1 q w.1)
    (u' : ProfileCycleMiddlePoint n k x)
    (w' : ProfileCycleOuterPoint n k x)
    (parent' : AnnularBoundaryExcursionKernel.BoundaryExcursionExitWordCode
      (profileOuterBoundary n k x) (profileInnerBoundary n k x)
      (profileInnerBoundary n (k + 1) x) u'.1 q w'.1)
    (hu : u.1 = u'.1) (hword : parent.1 = parent'.1) (j : Fin q) :
    (extractedProfileReturnWordCode hn hk0 hk u w parent j).1 =
      (extractedProfileReturnWordCode hn hk0 hk u' w' parent' j).1 := by
  have hlist : List.ofFn
        (extractedProfileReturnWordCode hn hk0 hk u w parent j).1.2 =
      List.ofFn
        (extractedProfileReturnWordCode hn hk0 hk u' w' parent' j).1.2 := by
    rw [extractedProfileReturnWordCode_toList,
      extractedProfileReturnWordCode_toList]
    exact congrArg₂
      (fun start word ↦
        TerminalSkeletonWords.intervalWords (extendStoppedWord word)
          (AsymmetricSplitLevelSplice.extractTimedReturnSkeleton
            (extendStoppedWord word) start (profileInnerBoundary n k x)
            (profileInnerBoundary n (k + 1) x) word.1 q).entrance
          (AsymmetricSplitLevelSplice.extractTimedReturnSkeleton
            (extendStoppedWord word) start (profileInnerBoundary n k x)
            (profileInnerBoundary n (k + 1) x) word.1 q).exit j)
      hu hword
  calc
    _ = listStoppedWord (List.ofFn
        (extractedProfileReturnWordCode hn hk0 hk u w parent j).1.2) :=
      (listStoppedWord_ofFn _).symm
    _ = listStoppedWord (List.ofFn
        (extractedProfileReturnWordCode hn hk0 hk u' w' parent' j).1.2) :=
      congrArg listStoppedWord hlist
    _ = _ := listStoppedWord_ofFn _

/-- Proof-free data on which an extracted return list actually depends. -/
def rawExtractedProfileReturnList
    {n k q : ℕ} {x : Point}
    (start : Point) (word : StoppedWord) (j : Fin q) : List Direction :=
  TerminalSkeletonWords.intervalWords (extendStoppedWord word)
    (AsymmetricSplitLevelSplice.extractTimedReturnSkeleton
      (extendStoppedWord word) start (profileInnerBoundary n k x)
      (profileInnerBoundary n (k + 1) x) word.1 q).entrance
    (AsymmetricSplitLevelSplice.extractTimedReturnSkeleton
      (extendStoppedWord word) start (profileInnerBoundary n k x)
      (profileInnerBoundary n (k + 1) x) word.1 q).exit j

/-- The literal list form of one deleted return, factored through precisely
the proof-free source data used by the clock extractor. -/
def extractedProfileReturnList
    {n k q : ℕ} {x : Point}
    (_hn : 2 ≤ n) (_hk0 : 0 < k) (_hk : k + 1 ≤ n)
    (u : ProfileCycleMiddlePoint n k x)
    (_w : ProfileCycleOuterPoint n k x)
    (parent : AnnularBoundaryExcursionKernel.BoundaryExcursionExitWordCode
      (profileOuterBoundary n k x) (profileInnerBoundary n k x)
      (profileInnerBoundary n (k + 1) x) u.1 q _w.1)
    (j : Fin q) : List Direction :=
  rawExtractedProfileReturnList (n := n) (k := k) (x := x)
    u.1 parent.1 j

theorem extractedProfileReturnList_eq_raw
    {n k q : ℕ} {x : Point}
    (hn : 2 ≤ n) (hk0 : 0 < k) (hk : k + 1 ≤ n)
    (u : ProfileCycleMiddlePoint n k x)
    (w : ProfileCycleOuterPoint n k x)
    (parent : AnnularBoundaryExcursionKernel.BoundaryExcursionExitWordCode
      (profileOuterBoundary n k x) (profileInnerBoundary n k x)
      (profileInnerBoundary n (k + 1) x) u.1 q w.1)
    (j : Fin q) :
    extractedProfileReturnList hn hk0 hk u w parent j =
      rawExtractedProfileReturnList (n := n) (k := k) (x := x)
        u.1 parent.1 j := by
  rfl

/-- The proof-free return list is the list stored by the canonical extracted
return code. -/
theorem extractedProfileReturnList_eq_codeList
    {n k q : ℕ} {x : Point}
    (hn : 2 ≤ n) (hk0 : 0 < k) (hk : k + 1 ≤ n)
    (u : ProfileCycleMiddlePoint n k x)
    (w : ProfileCycleOuterPoint n k x)
    (parent : AnnularBoundaryExcursionKernel.BoundaryExcursionExitWordCode
      (profileOuterBoundary n k x) (profileInnerBoundary n k x)
      (profileInnerBoundary n (k + 1) x) u.1 q w.1)
    (j : Fin q) :
    extractedProfileReturnList hn hk0 hk u w parent j =
      List.ofFn
        (extractedProfileReturnWordCode hn hk0 hk u w parent j).1.2 := by
  exact (extractedProfileReturnWordCode_toList hn hk0 hk u w parent j).symm

/-- Return lists are invariant under transported endpoint representatives. -/
theorem extractedProfileReturnList_eq
    {n k q : ℕ} {x : Point}
    (hn : 2 ≤ n) (hk0 : 0 < k) (hk : k + 1 ≤ n)
    (u : ProfileCycleMiddlePoint n k x)
    (w : ProfileCycleOuterPoint n k x)
    (parent : AnnularBoundaryExcursionKernel.BoundaryExcursionExitWordCode
      (profileOuterBoundary n k x) (profileInnerBoundary n k x)
      (profileInnerBoundary n (k + 1) x) u.1 q w.1)
    (u' : ProfileCycleMiddlePoint n k x)
    (w' : ProfileCycleOuterPoint n k x)
    (parent' : AnnularBoundaryExcursionKernel.BoundaryExcursionExitWordCode
      (profileOuterBoundary n k x) (profileInnerBoundary n k x)
      (profileInnerBoundary n (k + 1) x) u'.1 q w'.1)
    (hu : u.1 = u'.1) (hword : parent.1 = parent'.1) (j : Fin q) :
    extractedProfileReturnList hn hk0 hk u w parent j =
      extractedProfileReturnList hn hk0 hk u' w' parent' j := by
  exact congrArg₂
    (fun start word ↦ rawExtractedProfileReturnList
      (n := n) (k := k) (x := x) start word j) hu hword

@[simp] theorem actualProfileParentMiddle_val
    {omega : StepPath} {n horizon k parent : ℕ} {x : Point}
    (hcomplete : profileGapExitTime (trajectory omega) n horizon x k parent ≤
      horizon) :
    (actualProfileParentMiddle hcomplete).1 =
      profileGapStartPoint omega n horizon x k parent := rfl

@[simp] theorem actualProfileParentOuter_val
    {omega : StepPath} {n horizon k parent : ℕ} {x : Point}
    (hcomplete : profileGapExitTime (trajectory omega) n horizon x k parent ≤
      horizon) :
    (actualProfileParentOuter hcomplete).1 =
      profileGapExitPoint omega n horizon x k parent := rfl

/-- Compact proof-free list extracted from one completed actual parent. -/
def actualExtractedProfileReturnList
    {omega : StepPath} {n horizon k parent : ℕ} {x : Point}
    (hn : 2 ≤ n) (hk0 : 0 < k) (hk : k + 1 ≤ n)
    (hcomplete : profileGapExitTime (trajectory omega) n horizon x k parent ≤
      horizon)
    (j : Fin (profileGapOffspringCount omega n horizon x k parent)) :
    List Direction :=
  extractedProfileReturnList hn hk0 hk
    (actualProfileParentMiddle hcomplete)
    (actualProfileParentOuter hcomplete)
    (profileGapBoundaryExcursionWordCode hcomplete) j

theorem actualExtractedProfileReturnList_eq_codeList
    {omega : StepPath} {n horizon k parent : ℕ} {x : Point}
    (hn : 2 ≤ n) (hk0 : 0 < k) (hk : k + 1 ≤ n)
    (hcomplete : profileGapExitTime (trajectory omega) n horizon x k parent ≤
      horizon)
    (j : Fin (profileGapOffspringCount omega n horizon x k parent)) :
    actualExtractedProfileReturnList hn hk0 hk hcomplete j =
      List.ofFn
        (actualExtractedProfileReturnWordCode hn hk0 hk hcomplete j).1.2 := by
  exact extractedProfileReturnList_eq_codeList hn hk0 hk
    (actualProfileParentMiddle hcomplete)
    (actualProfileParentOuter hcomplete)
    (profileGapBoundaryExcursionWordCode hcomplete) j

/-- The child clock theorem in the compact edge-data interface. -/
theorem profileGapStoppedWord_childIndex_eq_actualExtracted
    {omega : StepPath} {n horizon k parents children : ℕ} {x : Point}
    (edge : ActualProfileEdgeData omega n horizon x k parents children)
    (i : Fin parents)
    (j : Fin (profileGapOffspringCount omega n horizon x k i)) :
    profileGapStoppedWord omega n horizon x (k + 1) (edge.childIndex i j) =
      (extractedProfileReturnWordCode edge.hn edge.hk0 edge.hk
        (actualProfileParentMiddle (edge.hcomplete i i.isLt))
        (actualProfileParentOuter (edge.hcomplete i i.isLt))
        (profileGapBoundaryExcursionWordCode (edge.hcomplete i i.isLt))
        j).1 := by
  unfold childIndex
  simpa only [actualExtractedProfileReturnWordCode] using
    profileGapStoppedWord_actualProfileChildIndex_eq_extracted
      edge.hn edge.hk0 edge.hk edge.hx edge.hparents edge.hparentCount
      edge.hchildCount edge.hcomplete i j

/-- List-valued child recovery, factored out for the recursive induction. -/
theorem profileGapStoppedList_childIndex_eq_actualExtracted
    {omega : StepPath} {n horizon k parents children : ℕ} {x : Point}
    (edge : ActualProfileEdgeData omega n horizon x k parents children)
    (i : Fin parents)
    (j : Fin (profileGapOffspringCount omega n horizon x k i)) :
    List.ofFn
        (profileGapStoppedWord omega n horizon x (k + 1)
          (edge.childIndex i j)).2 =
      extractedProfileReturnList edge.hn edge.hk0 edge.hk
        (actualProfileParentMiddle (edge.hcomplete i i.isLt))
        (actualProfileParentOuter (edge.hcomplete i i.isLt))
        (profileGapBoundaryExcursionWordCode (edge.hcomplete i i.isLt)) j := by
  change List.ofFn
      (profileGapStoppedWord omega n horizon x (k + 1)
        (edge.childIndex i j)).2 =
    actualExtractedProfileReturnList edge.hn edge.hk0 edge.hk
      (edge.hcomplete i i.isLt) j
  rw [actualExtractedProfileReturnList_eq_codeList]
  exact congrArg (fun word : StoppedWord ↦ List.ofFn word.2)
    (profileGapStoppedWord_childIndex_eq_actualExtracted edge i j)

/-- Return-list transport expressed through the compact edge interface. -/
theorem edgeExtractedProfileReturnListAt_eq
    {omega : StepPath} {n horizon k parents children : ℕ} {x : Point}
    (edge : ActualProfileEdgeData omega n horizon x k parents children)
    (i : Fin parents)
    (u : ProfileCycleMiddlePoint n k x)
    (w : ProfileCycleOuterPoint n k x)
    (hu : profileGapStartPoint omega n horizon x k i = u.1)
    (hw : profileGapExitPoint omega n horizon x k i = w.1)
    (j : Fin (profileGapOffspringCount omega n horizon x k i)) :
    extractedProfileReturnList edge.hn edge.hk0 edge.hk
        (actualProfileParentMiddle (edge.hcomplete i i.isLt))
        (actualProfileParentOuter (edge.hcomplete i i.isLt))
        (profileGapBoundaryExcursionWordCode (edge.hcomplete i i.isLt)) j =
      extractedProfileReturnList edge.hn edge.hk0 edge.hk u w
        (actualParentBoundaryCodeAt (edge.hcomplete i i.isLt) u w hu hw) j := by
  unfold extractedProfileReturnList
  exact congrArg₂
    (fun start word ↦ rawExtractedProfileReturnList
      (n := n) (k := k) (x := x) start word j)
    ((actualProfileParentMiddle_val (edge.hcomplete i i.isLt)).trans hu)
    ((profileGapBoundaryExcursionWordCode_val
      (edge.hcomplete i i.isLt)).trans
        (actualParentBoundaryCodeAt_val
          (edge.hcomplete i i.isLt) u w hu hw).symm)

/-- Structural recovery of an erased-parent assembly after each deleted
child word has itself been recursively parsed. -/
theorem recursiveProfileForestList_ofAssembly_eq :
    ∀ {q n k : ℕ} {center : Point}
      (childTree : Fin q → ProfileRefinementTree)
      (start : ProfileCycleMiddlePoint n k center)
      (innerPoint : Fin q → ProfileCycleInnerPoint n k center)
      (returnPoint : Fin q → ProfileCycleMiddlePoint n k center)
      (outerPoint : ProfileCycleOuterPoint n k center)
      (assembly : ErasedParentAssemblyCode q
        (profileInnerBoundary n (k + 1) center ∪
          profileOuterBoundary n k center)
        (profileInnerBoundary n k center) start.1
        (fun j ↦ (innerPoint j).1) (fun j ↦ (returnPoint j).1)
        outerPoint.1)
      (children : (j : Fin q) → RecursiveProfileGapCode n (k + 1)
        center (childTree j) (innerPoint j) (returnPoint j)),
      (∀ j, recursiveProfileGapList n (k + 1) center (childTree j)
          (innerPoint j) (returnPoint j) (children j) =
        List.ofFn (assembly.2.1 j).1.2) →
      recursiveProfileForestList n k center
          (profileRefinementForestOfFin q childTree)
          start outerPoint
          (recursiveProfileForestCodeOfAssemblyFin n k center q childTree
            start innerPoint returnPoint outerPoint assembly children) =
        interleavedErasedParentList q
          (fun j ↦ List.ofFn (assembly.1 j).1.2)
          (fun j ↦ List.ofFn (assembly.2.1 j).1.2)
          (List.ofFn assembly.2.2.1.2) := by
  intro q
  induction q with
  | zero =>
      intro n k center childTree start innerPoint returnPoint outerPoint
        assembly children _hchildren
      rfl
  | succ q ih =>
      intro n k center childTree start innerPoint returnPoint outerPoint
        assembly children hchildren
      simp only [profileRefinementForestOfFin, recursiveProfileForestList,
        recursiveProfileForestCodeOfAssemblyFin,
        interleavedErasedParentList]
      rw [hchildren 0]
      congr 1
      apply ih (fun j : Fin q ↦ childTree j.succ)
        (returnPoint 0) (fun j ↦ innerPoint j.succ)
        (fun j ↦ returnPoint j.succ) outerPoint
        (erasedParentAssemblyTail assembly) (fun j ↦ children j.succ)
      intro j
      exact hchildren j.succ

/-- Literal direction list carried by a parsed gap. -/
def parsedProfileGapList
    {n k : ℕ} {x : Point}
    {u : ProfileCycleMiddlePoint n k x}
    {w : ProfileCycleOuterPoint n k x}
    (parsed : ActualParsedProfileGap n k x u w) : List Direction :=
  recursiveProfileGapList n k x parsed.tree u w parsed.code

/-- A parsed actual leaf stores its source word literally. -/
theorem parsedProfileGapList_actualLeaf_eq
    {omega : StepPath} {n horizon k parent : ℕ} {x : Point}
    (hcomplete : profileGapExitTime (trajectory omega) n horizon x k parent ≤
      horizon)
    (u : ProfileCycleMiddlePoint n k x)
    (w : ProfileCycleOuterPoint n k x)
    (hu : profileGapStartPoint omega n horizon x k parent = u.1)
    (hw : profileGapExitPoint omega n horizon x k parent = w.1) :
    parsedProfileGapList
        (actualLeafParsedProfileGap hcomplete u w hu hw) =
      List.ofFn (profileGapStoppedWord omega n horizon x k parent).2 := by
  unfold parsedProfileGapList actualLeafParsedProfileGap
  simp only [recursiveProfileGapList]
  exact congrArg (fun word ↦ List.ofFn word.2)
    (actualLeafGapCodeAt_val hcomplete u w hu hw)

/-- Generic internal-node recovery once every parsed child recovers the
corresponding deleted return word. -/
theorem parsedProfileGapList_internal_eq_parent
    {n k q : ℕ} {x : Point}
    (hn : 2 ≤ n) (hk0 : 0 < k) (hk : k + 1 ≤ n)
    (u : ProfileCycleMiddlePoint n k x)
    (w : ProfileCycleOuterPoint n k x)
    (parent : AnnularBoundaryExcursionKernel.BoundaryExcursionExitWordCode
      (profileOuterBoundary n k x) (profileInnerBoundary n k x)
      (profileInnerBoundary n (k + 1) x) u.1 q w.1)
    (children : (j : Fin q) → ActualParsedProfileGap n (k + 1) x
      (extractedProfileInnerPoint u w parent j)
      (extractedProfileMiddlePoint hn hk0 hk u w parent j.succ))
    (hchildren : ∀ j, parsedProfileGapList (children j) =
      extractedProfileReturnList hn hk0 hk u w parent j) :
    parsedProfileGapList
        (parsedProfileGapOfBoundaryExcursion hn hk0 hk u w parent children) =
      List.ofFn parent.1.2 := by
  let childTree : Fin q → ProfileRefinementTree :=
    fun j ↦ (children j).tree
  let assembly := extractedProfileAssemblyCode hn hk0 hk u w parent
  have hforest := recursiveProfileForestList_ofAssembly_eq childTree u
    (extractedProfileInnerPoint u w parent)
    (fun j ↦ extractedProfileMiddlePoint hn hk0 hk u w parent j.succ)
    w assembly (fun j ↦ (children j).code) (by
      intro j
      exact (hchildren j).trans
        (extractedProfileReturnList_eq_codeList hn hk0 hk u w parent j))
  have hparent := extractedProfileAssemblyWord_eq_parent
    hn hk0 hk u w parent
  have hparentList := congrArg (fun word ↦ List.ofFn word.2) hparent
  simp only [erasedParentAssemblyWord, listStoppedWord_toList] at hparentList
  unfold parsedProfileGapList parsedProfileGapOfBoundaryExcursion
  simp only [recursiveProfileGapList]
  exact hforest.trans hparentList

/-- The recursively parsed literal list of every actual completed gap is
exactly its original stopped-word list. -/
theorem parsedProfileGapList_actualParsed_eq
    {omega : StepPath} {n horizon : ℕ} {x : Point}
    (hn : 2 ≤ n) (hx : x ∈ candidateBox n) (rest : List ℕ) :
    ∀ {k a : ℕ} (hk0 : 0 < k) (hdepth : k + rest.length ≤ n)
      (data : ActualProfileSegmentData omega n horizon x k (a :: rest))
      (i : Fin a) (u : ProfileCycleMiddlePoint n k x)
      (w : ProfileCycleOuterPoint n k x)
      (hu : profileGapStartPoint omega n horizon x k i = u.1)
      (hw : profileGapExitPoint omega n horizon x k i = w.1),
      parsedProfileGapList
          (actualParsedProfileGap hn hx rest hk0 hdepth data i u w hu hw) =
        List.ofFn (profileGapStoppedWord omega n horizon x k i).2 := by
  induction rest with
  | nil =>
      intro k a hk0 hdepth data i u w hu hw
      exact parsedProfileGapList_actualLeaf_eq
        (data.headComplete i i.isLt) u w hu hw
  | cons b rest ih =>
      intro k a hk0 hdepth data i u w hu hw
      let edge := data.edgeData hn hx hk0 hdepth
      let parent := actualParentBoundaryCodeAt
        (edge.hcomplete i i.isLt) u w hu hw
      let childDepth : k + 1 + rest.length ≤ n := by
        simp only [List.length_cons] at hdepth
        omega
      let childParsed : (j : Fin
          (profileGapOffspringCount omega n horizon x k i)) →
          ActualParsedProfileGap n (k + 1) x
            (extractedProfileInnerPoint u w parent j)
            (extractedProfileMiddlePoint edge.hn edge.hk0 edge.hk
              u w parent j.succ) :=
        fun j ↦ actualParsedProfileGap hn hx rest (by omega) childDepth
          data.tail (edge.childIndex i j)
          (extractedProfileInnerPoint u w parent j)
          (extractedProfileMiddlePoint edge.hn edge.hk0 edge.hk
            u w parent j.succ)
          (childMiddlePoint_eq_extracted_at edge i u w hu hw j)
          (childOuterPoint_eq_extracted_at edge i u w hu hw j)
      have hchildren : ∀ j, parsedProfileGapList (childParsed j) =
          extractedProfileReturnList edge.hn edge.hk0 edge.hk
            u w parent j := by
        intro j
        have hparsed := ih (by omega) childDepth data.tail
          (edge.childIndex i j)
          (extractedProfileInnerPoint u w parent j)
          (extractedProfileMiddlePoint edge.hn edge.hk0 edge.hk
            u w parent j.succ)
          (childMiddlePoint_eq_extracted_at edge i u w hu hw j)
          (childOuterPoint_eq_extracted_at edge i u w hu hw j)
        have hsource := profileGapStoppedList_childIndex_eq_actualExtracted
          edge i j
        have htransport := edgeExtractedProfileReturnListAt_eq
          edge i u w hu hw j
        exact hparsed.trans (hsource.trans htransport)
      have hinternal := parsedProfileGapList_internal_eq_parent
        edge.hn edge.hk0 edge.hk u w parent childParsed hchildren
      have hdecomp : actualParsedProfileGap hn hx (b :: rest) hk0 hdepth
          data i u w hu hw =
          parsedProfileGapOfBoundaryExcursion
            edge.hn edge.hk0 edge.hk u w parent childParsed :=
        actualParsedProfileGap_cons hn hx hk0 hdepth data i u w hu hw
      rw [hdecomp]
      exact hinternal.trans (congrArg (fun word : StoppedWord ↦ List.ofFn word.2)
        (actualParentBoundaryCodeAt_val
          (edge.hcomplete i i.isLt) u w hu hw))

/-- The actual-clock refinement tree is the ordinary tree generated by its
canonical weak-composition chain. -/
theorem refinementTrees_eq_profileRefinementTrees
    {omega : StepPath} {n horizon : ℕ} {x : Point}
    (hn : 2 ≤ n) (hx : x ∈ candidateBox n) (rest : List ℕ) :
    ∀ {k a : ℕ} (hk0 : 0 < k) (hdepth : k + rest.length ≤ n)
      (data : ActualProfileSegmentData omega n horizon x k (a :: rest))
      (i : Fin a),
      refinementTrees hn hx hk0 hdepth data i =
        profileRefinementTrees a rest
          (data.gapChain hn hx hk0 hdepth) i := by
  induction rest with
  | nil =>
      intro k a hk0 hdepth data i
      rfl
  | cons b rest ih =>
      intro k a hk0 hdepth data i
      simp only [refinementTrees, profileRefinementTrees,
        ActualProfileSegmentData.gapChain]
      have htailDepth : k + 1 + rest.length ≤ n := by
        simp only [List.length_cons] at hdepth
        omega
      have hchildren :
          List.ofFn (fun j : Fin
              (profileGapOffspringCount omega n horizon x k i) ↦
            refinementTrees hn hx (by omega) htailDepth data.tail
              ((data.edgeData hn hx hk0 (by
                simpa only [List.length_cons] using hdepth)).childIndex i j)) =
          List.ofFn (fun j : Fin
              (profileGapOffspringCount omega n horizon x k i) ↦
            profileRefinementTrees b rest
              (data.tail.gapChain hn hx (by omega) htailDepth)
              ((gapChildIndexEquiv
                (actualProfileOffspringGapPattern hn hk0 (by omega) hx
                  data.headPositive data.headCount data.tail.headCount
                    data.headComplete))
                ⟨i, Fin.cast
                  (gapMultiplicity_actualProfileOffspringGapPattern
                    hn hk0 (by omega) hx data.headPositive data.headCount
                      data.tail.headCount data.headComplete i).symm j⟩)) := by
        rw [List.ofFn_inj]
        funext j
        simpa only [ActualProfileEdgeData.childIndex,
          actualProfileChildIndex] using
            (ih (by omega) htailDepth data.tail
              ((data.edgeData hn hx hk0 (by
                simpa only [List.length_cons] using hdepth)).childIndex i j))
      rw [hchildren]
      let hkNext : k + 1 ≤ n := by omega
      have hgapChain_irrel (hp : 0 < k + 1)
          (hd : k + 1 + rest.length ≤ n) :
          data.tail.gapChain hn hx hp hd =
            data.tail.gapChain hn hx (by omega) htailDepth := by
        congr
      have hpattern_irrel (hp : k + 1 ≤ n) :
          actualProfileOffspringGapPattern hn hk0 hp hx
              data.headPositive data.headCount data.tail.headCount
                data.headComplete =
            actualProfileOffspringGapPattern hn hk0 hkNext hx
              data.headPositive data.headCount data.tail.headCount
                data.headComplete := by
        congr
      simp only [hgapChain_irrel, hpattern_irrel,
        gapMultiplicity_actualProfileOffspringGapPattern]
      apply congrArg ProfileRefinementTree.node
      apply congrArg ProfileRefinementForest.ofList
      rw [List.ofFn_inj]
      funext j
      congr

/-- Every actual parent-major refinement tree fits in the supplied remaining
profile depth. -/
theorem profileRefinementTreeFits_actualRefinementTrees
    {omega : StepPath} {n horizon : ℕ} {x : Point}
    (hn : 2 ≤ n) (hx : x ∈ candidateBox n) (rest : List ℕ) :
    ∀ {k a : ℕ} (hk0 : 0 < k) (hdepth : k + rest.length ≤ n)
      (data : ActualProfileSegmentData omega n horizon x k (a :: rest))
      (i : Fin a),
      profileRefinementTreeFits n k
        (refinementTrees hn hx hk0 hdepth data i) := by
  intro k a hk0 hdepth data i
  rw [refinementTrees_eq_profileRefinementTrees hn hx rest hk0 hdepth data i]
  exact profileRefinementTreeFits_profileRefinementTrees rest
    (data.gapChain hn hx hk0 hdepth) i hdepth

/-- The exact parsed tree therefore satisfies the physical depth condition
required by the recursive first-boundary assembler. -/
theorem actualParsedProfileGap_fits
    {omega : StepPath} {n horizon : ℕ} {x : Point}
    (hn : 2 ≤ n) (hx : x ∈ candidateBox n) (rest : List ℕ)
    {k a : ℕ} (hk0 : 0 < k) (hdepth : k + rest.length ≤ n)
    (data : ActualProfileSegmentData omega n horizon x k (a :: rest))
    (i : Fin a) (u : ProfileCycleMiddlePoint n k x)
    (w : ProfileCycleOuterPoint n k x)
    (hu : profileGapStartPoint omega n horizon x k i = u.1)
    (hw : profileGapExitPoint omega n horizon x k i = w.1) :
    profileRefinementTreeFits n k
      (actualParsedProfileGap hn hx rest hk0 hdepth data i u w hu hw).tree := by
  rw [actualParsedProfileGap_tree]
  exact profileRefinementTreeFits_actualRefinementTrees
    hn hx rest hk0 hdepth data i

/-- The assembled boundary code of the actual parser stores exactly the
source profile-gap stopped word. -/
theorem recursiveProfileGapBoundaryExitWordCode_actualParsed_eq
    {omega : StepPath} {n horizon : ℕ} {x : Point}
    (hn : 2 ≤ n) (hx : x ∈ candidateBox n) (rest : List ℕ)
    {k a : ℕ} (hk0 : 0 < k) (hdepth : k + rest.length ≤ n)
    (data : ActualProfileSegmentData omega n horizon x k (a :: rest))
    (i : Fin a) (u : ProfileCycleMiddlePoint n k x)
    (w : ProfileCycleOuterPoint n k x)
    (hu : profileGapStartPoint omega n horizon x k i = u.1)
    (hw : profileGapExitPoint omega n horizon x k i = w.1) :
    let parsed := actualParsedProfileGap hn hx rest hk0 hdepth
      data i u w hu hw
    let hfit := actualParsedProfileGap_fits hn hx rest hk0 hdepth
      data i u w hu hw
    (recursiveProfileGapBoundaryExitWordCode n k x hn hk0 parsed.tree hfit
      u w parsed.code).1 = profileGapStoppedWord omega n horizon x k i := by
  dsimp only
  rw [recursiveProfileGapBoundaryExitWordCode_val]
  change listStoppedWord (parsedProfileGapList
    (actualParsedProfileGap hn hx rest hk0 hdepth data i u w hu hw)) = _
  rw [parsedProfileGapList_actualParsed_eq]
  exact listStoppedWord_ofFn _

end

end Erdos1165.AnnularRecursiveProfileSourceRecovery
