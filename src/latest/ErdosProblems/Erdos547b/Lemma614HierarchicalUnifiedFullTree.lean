/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.Lemma614HierarchicalFullTree
import ErdosProblems.Erdos547b.HierarchicalUnifiedRegularEmbedding

/-!
# Unified-pool full-tree transport

The unified-pool online constructor produces the same concrete hierarchical
copy as the ordinary cleaned-system constructor.  This file transports that
copy through special segmentation and the one-root branch presentation back
to the literal input tree.  In particular, the theorem below does not assume
a source copy or any of the hierarchy parent edges.
-/

open scoped SimpleGraph

noncomputable section

namespace Erdos547b.ZhaoLemma614HierarchicalUnifiedFullTree

open Finset Fintype SimpleGraph
open Erdos547b.ZhaoLemma59Part2Full
open Erdos547b.ZhaoLemma59SpecialSegmentation
open Erdos547b.ZhaoLemma59HierarchicalOnline
open Erdos547b.ZhaoLemma59HierarchicalSpecial
open Erdos547b.ZhaoLemma59HierarchicalUnifiedRegular
open Erdos547b.ZhaoClaim68BranchGraphTransport
open Erdos547b.ZhaoSingleTreeOrderedForest
open Erdos547b.ZhaoLemma614HierarchicalFullTree

universe u v

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {B : Type v} [Fintype B] [DecidableEq B]

/-- Transport any concrete embedding of the whole-tree hierarchy back to a
placement-preserving embedding of the literal tree. -/
def fullTreeRegularEmbeddingOfHierarchyEmbedding
    (T : SimpleGraph V) (hT : T.IsTree) (globalRoot : V)
    (special : Finset (WholeBranchVertex T hT globalRoot))
    (G : SimpleGraph B)
    (globalRootImage : Fin 1 → B)
    (rootCandidate :
      Fin (marks (wholeBranchForest T hT globalRoot) special).card → Finset B)
    (interiorCandidate :
      (i : Fin (marks (wholeBranchForest T hT globalRoot) special).card) →
        Fin ((wholeHierarchy T hT globalRoot special).segments.size i) →
          Finset B)
    (E : HierarchicalSegmentForest.HierarchicalCandidateEmbedding
      (wholeHierarchy T hT globalRoot special) G globalRootImage
        rootCandidate interiorCandidate) :
    FullTreeRegularEmbedding T hT globalRoot special G globalRootImage
      rootCandidate interiorCandidate := by
  let originalCopy : (wholeBranchForest T hT globalRoot).graph.Copy G :=
    copyOfHierarchicalCopy (wholeBranchForest T hT globalRoot) special G
      E.fullCopy
  let specialEmbedding : SpecialRegularEmbedding
      (wholeBranchForest T hT globalRoot) special G globalRootImage
        rootCandidate interiorCandidate :=
    { hierarchyEmbedding := E
      originalCopy := originalCopy
      originalCopy_apply := fun _x ↦ rfl }
  let orderedCopy : (wholeOrderedTree T hT globalRoot).graph.Copy G :=
    copyOfBranchForestCopy (wholeOrderedTree T hT globalRoot) G originalCopy
  let fullCopy : T.Copy G :=
    copyOfSingleOrderedCopy T hT globalRoot G orderedCopy
  exact
    { specialEmbedding := specialEmbedding
      fullCopy := fullCopy
      fullCopy_apply := by
        intro x
        change originalCopy (toWholeBranchForestVertex T hT globalRoot x) =
          E.fullCopy
            (unflatten (wholeBranchForest T hT globalRoot) special
              (toWholeBranchForestVertex T hT globalRoot x))
        rfl }

/-- Unified physical-pool counterpart of
`exists_fullTreeRegularEmbedding_of_cleanedRegularSystem`. -/
theorem exists_fullTreeRegularEmbedding_of_unifiedCleanedRegularSystem
    {Pool : Type*} [DecidableEq Pool]
    (T : SimpleGraph V) (hT : T.IsTree) (globalRoot : V)
    (special : Finset (WholeBranchVertex T hT globalRoot))
    (G : SimpleGraph B) [DecidableRel G.Adj]
    (globalRootImage : Fin 1 → B)
    (rootPool interiorPool :
      Fin (marks (wholeBranchForest T hT globalRoot) special).card → Pool)
    (rootCandidate :
      Fin (marks (wholeBranchForest T hT globalRoot) special).card → Finset B)
    (interiorCandidate :
      (i : Fin (marks (wholeBranchForest T hT globalRoot) special).card) →
        Fin ((wholeHierarchy T hT globalRoot special).segments.size i) →
          Finset B)
    (S : HierarchicalSegmentForest.UnifiedCleanedRegularSystem
      (wholeHierarchy T hT globalRoot special) G globalRootImage
        rootPool interiorPool rootCandidate interiorCandidate) :
    Nonempty (FullTreeRegularEmbedding T hT globalRoot special G
      globalRootImage rootCandidate interiorCandidate) := by
  obtain ⟨E⟩ :=
    HierarchicalSegmentForest.exists_hierarchicalUnifiedRegularEmbedding
      (wholeHierarchy T hT globalRoot special) G globalRootImage
        rootPool interiorPool rootCandidate interiorCandidate S
  exact ⟨fullTreeRegularEmbeddingOfHierarchyEmbedding T hT globalRoot special G
    globalRootImage rootCandidate interiorCandidate E⟩

/-- Copy-only spelling of the unified full-tree endpoint. -/
theorem exists_fullTreeCopy_of_unifiedCleanedRegularSystem
    {Pool : Type*} [DecidableEq Pool]
    (T : SimpleGraph V) (hT : T.IsTree) (globalRoot : V)
    (special : Finset (WholeBranchVertex T hT globalRoot))
    (G : SimpleGraph B) [DecidableRel G.Adj]
    (globalRootImage : Fin 1 → B)
    (rootPool interiorPool :
      Fin (marks (wholeBranchForest T hT globalRoot) special).card → Pool)
    (rootCandidate :
      Fin (marks (wholeBranchForest T hT globalRoot) special).card → Finset B)
    (interiorCandidate :
      (i : Fin (marks (wholeBranchForest T hT globalRoot) special).card) →
        Fin ((wholeHierarchy T hT globalRoot special).segments.size i) →
          Finset B)
    (S : HierarchicalSegmentForest.UnifiedCleanedRegularSystem
      (wholeHierarchy T hT globalRoot special) G globalRootImage
        rootPool interiorPool rootCandidate interiorCandidate) :
    Nonempty (T.Copy G) := by
  obtain ⟨E⟩ :=
    exists_fullTreeRegularEmbedding_of_unifiedCleanedRegularSystem
      T hT globalRoot special G globalRootImage rootPool interiorPool
        rootCandidate interiorCandidate S
  exact ⟨E.fullCopy⟩

/-- Literal containment conclusion used by Claim 6.16 and Claim 6.17. -/
theorem isContained_of_unifiedCleanedRegularSystem
    {Pool : Type*} [DecidableEq Pool]
    (T : SimpleGraph V) (hT : T.IsTree) (globalRoot : V)
    (special : Finset (WholeBranchVertex T hT globalRoot))
    (G : SimpleGraph B) [DecidableRel G.Adj]
    (globalRootImage : Fin 1 → B)
    (rootPool interiorPool :
      Fin (marks (wholeBranchForest T hT globalRoot) special).card → Pool)
    (rootCandidate :
      Fin (marks (wholeBranchForest T hT globalRoot) special).card → Finset B)
    (interiorCandidate :
      (i : Fin (marks (wholeBranchForest T hT globalRoot) special).card) →
        Fin ((wholeHierarchy T hT globalRoot special).segments.size i) →
          Finset B)
    (S : HierarchicalSegmentForest.UnifiedCleanedRegularSystem
      (wholeHierarchy T hT globalRoot special) G globalRootImage
        rootPool interiorPool rootCandidate interiorCandidate) :
    T.IsContained G :=
  (exists_fullTreeCopy_of_unifiedCleanedRegularSystem T hT globalRoot special G
    globalRootImage rootPool interiorPool rootCandidate interiorCandidate S).some.isContained

end Erdos547b.ZhaoLemma614HierarchicalUnifiedFullTree

#print axioms Erdos547b.ZhaoLemma614HierarchicalUnifiedFullTree.exists_fullTreeRegularEmbedding_of_unifiedCleanedRegularSystem
#print axioms Erdos547b.ZhaoLemma614HierarchicalUnifiedFullTree.isContained_of_unifiedCleanedRegularSystem
