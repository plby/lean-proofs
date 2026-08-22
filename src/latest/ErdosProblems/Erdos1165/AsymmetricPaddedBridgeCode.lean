/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
import ErdosProblems.Erdos1165.AsymmetricPaddedCodeAssembly
import ErdosProblems.Erdos1165.AsymmetricPaddedBridgeLiteralFactorization

/-!
# Literal padded codes assembled from coarse bridges

A coarse bridge either exits before reaching the padded predecessor boundary,
or enters that boundary and exposes a finite family of deleted returns at the
padded scale.  Once recursive codes for those returns are supplied, this file
assembles all coarse bridges into one `PaddedPreludeMultiCode`.

The construction remembers no extra copy of a bridge.  Its chronological word
list is exactly the original coarse bridge list, hence its product mass is
exactly the original bridge-product mass.
-/

open scoped BigOperators ENNReal

namespace Erdos1165.AsymmetricPaddedBridgeCode

open AnnularErasedParentSpineRowPartition AnnularProfileClocks
open AnnularRecursiveDecoratedProfileCode
open AnnularRecursiveProfileCodeAssembly
open AlternatingConcatPrefixFree
open AsymmetricPaddedActiveFactorization
open AsymmetricPaddedBridgeLiteralFactorization
open AsymmetricPaddedCodeAssembly AsymmetricPaddedPreludeCode
open AsymmetricPaddedRemoteRenewal MarkedBridgeFactorization ThickPoint

noncomputable section

/-- One level-`l+1` to level-`l` coarse bridge with supported endpoints. -/
structure PaddedCoarseBridge (n l : ℕ) (center : Point) where
  start : PaddedNearPoint n l center
  endpoint : PaddedOuterPoint n l center
  bridge : BoundaryExitWordCode (profileInnerBoundary n l center)
    start.1 endpoint.1

/-- Initial-segment data seen by the padded multi-renewal. -/
def paddedCoarseBridgeSegments
    (n l p : ℕ) (center : Point) :
    List (PaddedCoarseBridge n l center) →
      List ((PaddedNearPoint n l center ⊕ PaddedMiddlePoint n p center) ×
        PaddedOuterPoint n l center)
  | [] => []
  | source :: sources =>
      (Sum.inl source.start, source.endpoint) ::
        paddedCoarseBridgeSegments n l p center sources

/-- Original chronological direction lists of the coarse bridges. -/
def paddedCoarseBridgeWords
    {n l : ℕ} {center : Point} :
    List (PaddedCoarseBridge n l center) → List (List Direction)
  | [] => []
  | source :: sources =>
      List.ofFn source.bridge.1.2 :: paddedCoarseBridgeWords sources

/-- Product mass of the original chronological coarse bridges. -/
def paddedCoarseBridgeMass
    {n l : ℕ} {center : Point}
    (sources : List (PaddedCoarseBridge n l center)) : ℝ≥0∞ :=
  (sources.map fun source ↦ stoppedWordMass source.bridge.1).prod

/-- A literal padded split whose deleted returns have been replaced by
recursive codes with exactly the same endpoint-supported words. -/
inductive PaddedBridgeDecoration
    (n l p : ℕ) (center : Point)
    (hn : 2 ≤ n) (hlp : l + 1 < p) (hp : p ≤ n)
    (source : PaddedCoarseBridge n l center) :
    List ProfileRefinementTree → Type
  | direct
      (first : BoundaryExitWordCode
        (profileInnerBoundary n (p - 1) center ∪
          profileInnerBoundary n l center)
        source.start.1 source.endpoint.1)
      (word_eq : first.1 = source.bridge.1) :
      PaddedBridgeDecoration n l p center hn hlp hp source []
  | entered
      (u : PaddedMiddlePoint n p center)
      (first : BoundaryExitWordCode
        (profileInnerBoundary n (p - 1) center ∪
          profileInnerBoundary n l center) source.start.1 u.1)
      (q : ℕ)
      (tree : Fin q → ProfileRefinementTree)
      (innerPoint : Fin q → PaddedInnerPoint n p center)
      (returnPoint : Fin q → PaddedMiddlePoint n p center)
      (assembly : ErasedParentAssemblyCode q
        (profileInnerBoundary n p center ∪ profileInnerBoundary n l center)
        (profileInnerBoundary n (p - 1) center) u.1
        (fun j ↦ (innerPoint j).1) (fun j ↦ (returnPoint j).1)
        source.endpoint.1)
      (children : (j : Fin q) → RecursiveProfileGapCode n p center
        (tree j) (innerPoint j) (returnPoint j))
      (word_eq : List.ofFn first.1.2 ++
          paddedDecoratedAssemblyList n p center assembly children =
        List.ofFn source.bridge.1.2) :
      PaddedBridgeDecoration n l p center hn hlp hp source
        (finTreeList q tree)

/-- A decorated erased parent has the same direction list as its ordinary
assembly whenever every replacement child has the deleted child's list. -/
theorem paddedDecoratedAssemblyList_eq_erasedParentAssemblyWord
    {n p q : ℕ} {center : Point} {retainedBoundary : Set Point}
    {u : PaddedMiddlePoint n p center}
    {innerPoint : Fin q → PaddedInnerPoint n p center}
    {returnPoint : Fin q → PaddedMiddlePoint n p center}
    {outerPoint : Point} {tree : Fin q → ProfileRefinementTree}
    (assembly : ErasedParentAssemblyCode q retainedBoundary
      (profileInnerBoundary n (p - 1) center) u.1
      (fun j ↦ (innerPoint j).1) (fun j ↦ (returnPoint j).1) outerPoint)
    (children : (j : Fin q) → RecursiveProfileGapCode n p center
      (tree j) (innerPoint j) (returnPoint j))
    (hchildren : ∀ j,
      recursiveProfileGapList n p center (tree j) (innerPoint j)
          (returnPoint j) (children j) =
        List.ofFn (assembly.2.1 j).1.2) :
    paddedDecoratedAssemblyList n p center assembly children =
      List.ofFn (erasedParentAssemblyWord assembly).2 := by
  unfold paddedDecoratedAssemblyList erasedParentAssemblyWord
  simp only [listStoppedWord_toList]
  congr 2
  funext j
  exact hchildren j

/-- Prepend one decorated coarse bridge to an already assembled padded code. -/
def PaddedBridgeDecoration.toCode
    {n l p : ℕ} {center : Point}
    {hn : 2 ≤ n} {hlp : l + 1 < p} {hp : p ≤ n}
    {source : PaddedCoarseBridge n l center}
    {trees : List ProfileRefinementTree}
    (decoration : PaddedBridgeDecoration n l p center hn hlp hp source trees)
    {segments : List
      ((PaddedNearPoint n l center ⊕ PaddedMiddlePoint n p center) ×
        PaddedOuterPoint n l center)}
    {restTrees : List ProfileRefinementTree}
    (rest : PaddedPreludeMultiCode n l p center segments restTrees) :
    PaddedPreludeMultiCode n l p center
      ((Sum.inl source.start, source.endpoint) :: segments)
      (trees ++ restTrees) := by
  cases decoration with
  | direct first word_eq =>
      exact .pendingDirect first rest
  | entered u first q tree innerPoint returnPoint assembly children word_eq =>
      exact .pendingEnter u first
        (paddedActiveCodeOfAssemblyFin n l p center q tree u
          innerPoint returnPoint source.endpoint assembly children rest)

/-- One decorated bridge contributes exactly its original direction word. -/
theorem PaddedBridgeDecoration.toCode_words
    {n l p : ℕ} {center : Point}
    {hn : 2 ≤ n} {hlp : l + 1 < p} {hp : p ≤ n}
    {source : PaddedCoarseBridge n l center}
    {trees : List ProfileRefinementTree}
    (decoration : PaddedBridgeDecoration n l p center hn hlp hp source trees)
    {segments : List
      ((PaddedNearPoint n l center ⊕ PaddedMiddlePoint n p center) ×
        PaddedOuterPoint n l center)}
    {restTrees : List ProfileRefinementTree}
    (rest : PaddedPreludeMultiCode n l p center segments restTrees) :
    paddedPreludeMultiCodeWords n l p center (decoration.toCode rest) =
      List.ofFn source.bridge.1.2 ::
        paddedPreludeMultiCodeWords n l p center rest := by
  cases decoration with
  | direct first word_eq =>
      simp only [PaddedBridgeDecoration.toCode, paddedPreludeMultiCodeWords]
      rw [word_eq]
  | entered u first q tree innerPoint returnPoint assembly children word_eq =>
      simp only [PaddedBridgeDecoration.toCode, paddedPreludeMultiCodeWords]
      rw [paddedActiveCodeOfAssemblyFin_words]
      simp only [prependHead]
      rw [word_eq]

/-- Chronological decorations of a complete list of coarse bridges. -/
inductive PaddedBridgeDecorationList
    (n l p : ℕ) (center : Point)
    (hn : 2 ≤ n) (hlp : l + 1 < p) (hp : p ≤ n) :
    List (PaddedCoarseBridge n l center) →
      List ProfileRefinementTree → Type
  | nil : PaddedBridgeDecorationList n l p center hn hlp hp [] []
  | cons {source sources localTrees restTrees}
      (head : PaddedBridgeDecoration n l p center hn hlp hp source localTrees)
      (tail : PaddedBridgeDecorationList n l p center hn hlp hp
        sources restTrees) :
      PaddedBridgeDecorationList n l p center hn hlp hp
        (source :: sources) (localTrees ++ restTrees)

/-- Assemble a chronological decoration list into one padded renewal code. -/
def PaddedBridgeDecorationList.toCode
    {n l p : ℕ} {center : Point}
    {hn : 2 ≤ n} {hlp : l + 1 < p} {hp : p ≤ n} :
    ∀ {sources : List (PaddedCoarseBridge n l center)}
      {trees : List ProfileRefinementTree},
      PaddedBridgeDecorationList n l p center hn hlp hp sources trees →
        PaddedPreludeMultiCode n l p center
          (paddedCoarseBridgeSegments n l p center sources) trees
  | [], [], .nil => .done
  | _, _, .cons head tail =>
      head.toCode tail.toCode

/-- The assembled multi-code recovers every original coarse bridge word. -/
theorem PaddedBridgeDecorationList.toCode_words
    {n l p : ℕ} {center : Point}
    {hn : 2 ≤ n} {hlp : l + 1 < p} {hp : p ≤ n} :
    ∀ {sources : List (PaddedCoarseBridge n l center)}
      {trees : List ProfileRefinementTree}
      (decorations : PaddedBridgeDecorationList n l p center hn hlp hp
        sources trees),
      paddedPreludeMultiCodeWords n l p center decorations.toCode =
        paddedCoarseBridgeWords sources
  | [], [], .nil => rfl
  | _, _, .cons head tail => by
      change paddedPreludeMultiCodeWords n l p center
          (head.toCode tail.toCode) = _
      rw [PaddedBridgeDecoration.toCode_words,
        PaddedBridgeDecorationList.toCode_words]
      rfl

private theorem stoppedWordListMass_paddedCoarseBridgeWords
    {n l : ℕ} {center : Point}
    (sources : List (PaddedCoarseBridge n l center)) :
    stoppedWordListMass (paddedCoarseBridgeWords sources) =
      paddedCoarseBridgeMass sources := by
  induction sources with
  | nil => rfl
  | cons source sources ih =>
      simp only [paddedCoarseBridgeWords, stoppedWordListMass,
        List.map_cons, List.prod_cons, listStoppedWord_ofFn,
        paddedCoarseBridgeMass]
      change stoppedWordMass source.bridge.1 *
          stoppedWordListMass (paddedCoarseBridgeWords sources) =
        stoppedWordMass source.bridge.1 * paddedCoarseBridgeMass sources
      rw [ih]

/-- Consequently the padded multi-code has exactly the original bridge
product mass. -/
theorem PaddedBridgeDecorationList.toCode_mass
    {n l p : ℕ} {center : Point}
    {hn : 2 ≤ n} {hlp : l + 1 < p} {hp : p ≤ n}
    {sources : List (PaddedCoarseBridge n l center)}
    {trees : List ProfileRefinementTree}
    (decorations : PaddedBridgeDecorationList n l p center hn hlp hp
      sources trees) :
    paddedPreludeMultiCodeMass n l p center decorations.toCode =
      paddedCoarseBridgeMass sources := by
  rw [paddedPreludeMultiCodeMass_eq_words,
    decorations.toCode_words]
  exact stoppedWordListMass_paddedCoarseBridgeWords sources

end

end Erdos1165.AsymmetricPaddedBridgeCode
