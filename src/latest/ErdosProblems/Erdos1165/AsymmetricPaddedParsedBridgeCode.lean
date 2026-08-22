/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
import ErdosProblems.Erdos1165.AnnularRecursiveBoundaryParser
import ErdosProblems.Erdos1165.AsymmetricPaddedBridgeCode

/-!
# Canonical recursive decoration of padded coarse bridges

Every deleted return exposed by the padded split is parsed recursively down
to the ambient terminal profile scale.  The resulting decorated padded code
still assembles to exactly the original list of coarse bridge words.
-/

namespace Erdos1165.AsymmetricPaddedParsedBridgeCode

open AnnularErasedParentSpineRowPartition AnnularRecursiveBoundaryParser
open AnnularRecursiveDecoratedProfileCode
open AnnularProfileClocks
open AnnularRecursiveProfileCodeAssembly
open AsymmetricPaddedActiveFactorization
open AsymmetricPaddedBridgeCode AsymmetricPaddedBridgeLiteralFactorization
open AsymmetricPaddedCodeAssembly AsymmetricPaddedRemoteRenewal
open AsymmetricPaddedPreludeCode
open MarkedBridgeFactorization ThickPoint

noncomputable section

/-- Trees obtained by canonically parsing every level-`p` return in one
padded coarse bridge.  This separate projection keeps later clock
identifications independent of the decoration certificates. -/
def parsedPaddedBridgeTrees
    {n l p : ℕ} {center : Point}
    (hn : 2 ≤ n) (hlp : l + 1 < p) (hp : p ≤ n)
    (source : PaddedCoarseBridge n l center) : List ProfileRefinementTree :=
  match paddedPreludeSplit (p := p) source.start source.endpoint
      source.bridge with
  | .direct _ _ => []
  | .entered u _ q parent _ =>
      finTreeList q fun j =>
        (parseBoundaryGap n center hn (n - p) p (by omega) (by omega)
          (extractedPaddedInnerPoint u source.endpoint parent j)
          (extractedPaddedMiddlePoint hn hlp hp u source.endpoint parent j.succ)
          (extractedPaddedReturnWordCode hn hlp hp u source.endpoint parent j)).tree

/-- The canonical tree list carries a literal padded decoration. -/
def parsedPaddedBridgeDecorationCore
    {n l p : ℕ} {center : Point}
    (hn : 2 ≤ n) (hlp : l + 1 < p) (hp : p ≤ n)
    (source : PaddedCoarseBridge n l center) :
    PaddedBridgeDecoration n l p center hn hlp hp source
      (parsedPaddedBridgeTrees hn hlp hp source) :=
  match hsplit : paddedPreludeSplit (p := p) source.start
      source.endpoint source.bridge with
  | .direct first word_eq => by
      simpa only [parsedPaddedBridgeTrees, hsplit] using
        (PaddedBridgeDecoration.direct first word_eq)
  | .entered u first q parent word_eq => by
      let innerPoint : Fin q → PaddedInnerPoint n p center :=
        extractedPaddedInnerPoint u source.endpoint parent
      let returnPoint : Fin q → PaddedMiddlePoint n p center :=
        fun j ↦ extractedPaddedMiddlePoint hn hlp hp u source.endpoint
          parent j.succ
      let childSource : (j : Fin q) → BoundaryExitWordCode
          (profileOuterBoundary n p center)
          (innerPoint j).1 (returnPoint j).1 :=
        fun j ↦ extractedPaddedReturnWordCode hn hlp hp u source.endpoint
          parent j
      let parsed : (j : Fin q) → ParsedBoundaryGap n p center
          (innerPoint j) (returnPoint j) (childSource j) :=
        fun j ↦ parseBoundaryGap n center hn (n - p) p (by omega)
          (by omega) (innerPoint j) (returnPoint j) (childSource j)
      let tree : Fin q → ProfileRefinementTree := fun j ↦ (parsed j).tree
      let children : (j : Fin q) → RecursiveProfileGapCode n p center
          (tree j) (innerPoint j) (returnPoint j) :=
        fun j ↦ (parsed j).code
      let assembly := extractedPaddedAssemblyCode hn hlp hp u
        source.endpoint parent
      have hchildren : ∀ j,
          recursiveProfileGapList n p center (tree j) (innerPoint j)
              (returnPoint j) (children j) =
            List.ofFn (assembly.2.1 j).1.2 := by
        intro j
        exact (parsed j).list_eq.trans (by rfl)
      have hassembly : paddedDecoratedAssemblyList n p center assembly
          children = List.ofFn parent.1.2 := by
        calc
          _ = List.ofFn (erasedParentAssemblyWord assembly).2 :=
            paddedDecoratedAssemblyList_eq_erasedParentAssemblyWord
              assembly children hchildren
          _ = List.ofFn parent.1.2 := congrArg
            (fun word : StoppedWord ↦ List.ofFn word.2)
            (extractedPaddedAssemblyWord_eq_parent hn hlp hp u
              source.endpoint parent)
      have result : PaddedBridgeDecoration n l p center hn hlp hp source
          (finTreeList q tree) := by
        refine .entered u first q tree innerPoint returnPoint assembly children ?_
        rw [hassembly]
        exact word_eq
      simpa only [parsedPaddedBridgeTrees, hsplit] using result

/-- Canonical recursive parse of every level-`p` return in one padded coarse
bridge. -/
def parsedPaddedBridgeDecoration
    {n l p : ℕ} {center : Point}
    (hn : 2 ≤ n) (hlp : l + 1 < p) (hp : p ≤ n)
    (source : PaddedCoarseBridge n l center) :
    Σ trees : List ProfileRefinementTree,
      PaddedBridgeDecoration n l p center hn hlp hp source trees :=
  ⟨parsedPaddedBridgeTrees hn hlp hp source,
    parsedPaddedBridgeDecorationCore hn hlp hp source⟩

/-- Canonically decorate every bridge in chronological order. -/
def parsedPaddedBridgeDecorationList
    {n l p : ℕ} {center : Point}
    (hn : 2 ≤ n) (hlp : l + 1 < p) (hp : p ≤ n) :
    ∀ sources : List (PaddedCoarseBridge n l center),
      Σ trees : List ProfileRefinementTree,
        PaddedBridgeDecorationList n l p center hn hlp hp sources trees
  | [] => ⟨[], .nil⟩
  | source :: sources =>
      let head := parsedPaddedBridgeDecoration hn hlp hp source
      let tail := parsedPaddedBridgeDecorationList hn hlp hp sources
      ⟨head.1 ++ tail.1, .cons head.2 tail.2⟩

/-- The canonical parsed decoration gives one literal padded code. -/
def parsedPaddedBridgeCode
    {n l p : ℕ} {center : Point}
    (hn : 2 ≤ n) (hlp : l + 1 < p) (hp : p ≤ n)
    (sources : List (PaddedCoarseBridge n l center)) :
    PaddedPreludeMultiCode n l p center
      (paddedCoarseBridgeSegments n l p center sources)
      (parsedPaddedBridgeDecorationList hn hlp hp sources).1 :=
  (parsedPaddedBridgeDecorationList hn hlp hp sources).2.toCode

@[simp] theorem parsedPaddedBridgeCode_words
    {n l p : ℕ} {center : Point}
    (hn : 2 ≤ n) (hlp : l + 1 < p) (hp : p ≤ n)
    (sources : List (PaddedCoarseBridge n l center)) :
    paddedPreludeMultiCodeWords n l p center
        (parsedPaddedBridgeCode hn hlp hp sources) =
      paddedCoarseBridgeWords sources := by
  exact (parsedPaddedBridgeDecorationList hn hlp hp sources).2.toCode_words

@[simp] theorem parsedPaddedBridgeCode_mass
    {n l p : ℕ} {center : Point}
    (hn : 2 ≤ n) (hlp : l + 1 < p) (hp : p ≤ n)
    (sources : List (PaddedCoarseBridge n l center)) :
    paddedPreludeMultiCodeMass n l p center
        (parsedPaddedBridgeCode hn hlp hp sources) =
      paddedCoarseBridgeMass sources := by
  exact (parsedPaddedBridgeDecorationList hn hlp hp sources).2.toCode_mass

end

end Erdos1165.AsymmetricPaddedParsedBridgeCode
