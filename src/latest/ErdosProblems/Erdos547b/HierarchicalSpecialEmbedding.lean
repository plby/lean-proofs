/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.SpecialSegmentation
import ErdosProblems.Erdos547b.HierarchicalRegularEmbedding

/-!
# Zhao Lemma 5.9(2): arbitrary-special copy transport

This module joins the two concrete halves of the arbitrary-special
construction.  `SpecialSegmentation` replaces an ordered branch forest by
the hierarchy obtained by cutting above every requested special vertex.
`HierarchicalRegularEmbedding` realizes that hierarchy from actual cleaned
regular-pair data.  The theorem below transports the resulting copy back to
the original branch forest.

In particular, neither a copy of the hierarchy nor any of its parent edges
is a hypothesis of the public endpoint.
-/

open scoped SimpleGraph

noncomputable section

namespace Erdos547b.ZhaoLemma59HierarchicalSpecial

open Finset Fintype SimpleGraph
open Erdos547b.ZhaoLemma59Part2Full
open Erdos547b.ZhaoLemma59Hierarchical
open Erdos547b.ZhaoLemma59SpecialSegmentation
open Erdos547b.ZhaoLemma59HierarchicalOnline.HierarchicalSegmentForest
open Erdos547b.ZhaoLemma59HierarchicalRegular.HierarchicalSegmentForest

universe u

variable {r b c k : ℕ} {B : Type u}

/-- The concrete result retained by consumers which also need the segment
placement information.  `originalCopy` is a copy of the graph before
segmentation, not merely of the auxiliary hierarchy. -/
structure SpecialRegularEmbedding
    [Fintype B] [DecidableEq B]
    (F : OrderedBranchForest r b)
    (special : Finset (BranchVertex F))
    (G : SimpleGraph B)
    (originalImage : Fin r → B)
    (rootCandidate : Fin (marks F special).card → Finset B)
    (interiorCandidate :
      (i : Fin (marks F special).card) →
        Fin ((toHierarchicalSegmentForest F special).segments.size i) →
        Finset B) where
  hierarchyEmbedding :
    HierarchicalCandidateEmbedding (toHierarchicalSegmentForest F special) G
      originalImage rootCandidate interiorCandidate
  originalCopy : F.graph.Copy G
  originalCopy_apply : ∀ x,
    originalCopy x = hierarchyEmbedding.fullCopy
      (unflatten F special x)

/-- Arbitrary-special, no-copy-assumption realization.  The input record
contains only actual host sets, uniform pairs, cleaned-side inclusions, and
aggregate density/removal capacities.  The result contains a literal copy
of the original ordered branch forest and all placement information from the
hierarchical online construction. -/
theorem exists_specialRegularEmbedding
    [Fintype B] [DecidableEq B]
    (F : OrderedBranchForest r b)
    (special : Finset (BranchVertex F))
    (G : SimpleGraph B) [DecidableRel G.Adj]
    (rho : ℝ)
    (originalImage : Fin r → B)
    (rootGroup : Fin (marks F special).card → Fin c)
    (group : Fin (marks F special).card → Fin k)
    (rootCandidate : Fin (marks F special).card → Finset B)
    (interiorCandidate :
      (i : Fin (marks F special).card) →
        Fin ((toHierarchicalSegmentForest F special).segments.size i) →
        Finset B)
    (S : CleanedRegularSystem
        (toHierarchicalSegmentForest F special) G rho originalImage
        rootGroup group rootCandidate interiorCandidate) :
    Nonempty (SpecialRegularEmbedding F special G originalImage
      rootCandidate interiorCandidate) := by
  obtain ⟨E⟩ :=
    exists_hierarchicalRegularEmbedding (toHierarchicalSegmentForest F special)
      G rho originalImage rootGroup group rootCandidate interiorCandidate S
  let C : F.graph.Copy G :=
    copyOfHierarchicalCopy F special G E.fullCopy
  exact ⟨
    { hierarchyEmbedding := E
      originalCopy := C
      originalCopy_apply := fun _x ↦ rfl }⟩

/-- Copy-only spelling for the stability lemmas. -/
theorem exists_specialRegularCopy
    [Fintype B] [DecidableEq B]
    (F : OrderedBranchForest r b)
    (special : Finset (BranchVertex F))
    (G : SimpleGraph B) [DecidableRel G.Adj]
    (rho : ℝ)
    (originalImage : Fin r → B)
    (rootGroup : Fin (marks F special).card → Fin c)
    (group : Fin (marks F special).card → Fin k)
    (rootCandidate : Fin (marks F special).card → Finset B)
    (interiorCandidate :
      (i : Fin (marks F special).card) →
        Fin ((toHierarchicalSegmentForest F special).segments.size i) →
        Finset B)
    (S : CleanedRegularSystem
        (toHierarchicalSegmentForest F special) G rho originalImage
        rootGroup group rootCandidate interiorCandidate) :
    Nonempty (F.graph.Copy G) := by
  obtain ⟨E⟩ := exists_specialRegularEmbedding F special G rho originalImage
    rootGroup group rootCandidate interiorCandidate S
  exact ⟨E.originalCopy⟩

/-- Layer-preserving arbitrary-special endpoint.  This is the actual
three-layer arrow realization needed before the full-tree hierarchy absorbs
the Lemma-6.3 cut edges. -/
theorem exists_threeLayerCopy_of_cleanedRegularSystem
    [Fintype B] [DecidableEq B]
    (F : OrderedBranchForest r b)
    (G : SimpleGraph B) [DecidableRel G.Adj]
    (rootImage : Fin r → B) (special : Finset F.Vertex)
    (clusterTarget matchingTarget : Finset B)
    (hspecialOdd : special ⊆ F.oddVertices)
    (rho : ℝ)
    (rootGroup : Fin (marks F (branchSpecial F special)).card → Fin c)
    (group : Fin (marks F (branchSpecial F special)).card → Fin k)
    (rootCandidate :
      Fin (marks F (branchSpecial F special)).card → Finset B)
    (interiorCandidate :
      (i : Fin (marks F (branchSpecial F special)).card) →
        Fin ((toHierarchicalSegmentForest F
          (branchSpecial F special)).segments.size i) → Finset B)
    (S : CleanedRegularSystem
        (toHierarchicalSegmentForest F (branchSpecial F special)) G rho
        rootImage rootGroup group rootCandidate interiorCandidate)
    (hrootTarget : ∀ i, rootCandidate i ⊆ clusterTarget)
    (hinteriorTarget : ∀ i a, interiorCandidate i a ⊆ matchingTarget) :
    Nonempty (ThreeLayerCopy F G rootImage special
      clusterTarget matchingTarget) := by
  obtain ⟨E⟩ := exists_specialRegularEmbedding F (branchSpecial F special) G
    rho rootImage rootGroup group rootCandidate interiorCandidate S
  refine ⟨threeLayerCopyOfHierarchicalCopy F G rootImage special
    clusterTarget matchingTarget hspecialOdd E.hierarchyEmbedding.fullCopy ?_ ?_ ?_⟩
  · intro i
    exact E.hierarchyEmbedding.fullCopy_root i
  · intro i
    simpa only [HierarchicalSegmentForest.segmentRoot,
      E.hierarchyEmbedding.fullCopy_segment,
      E.hierarchyEmbedding.map_root] using
        hrootTarget i (E.hierarchyEmbedding.root_mem i)
  · intro i a ha
    let H := toHierarchicalSegmentForest F (branchSpecial F special)
    let a' : Fin (H.segments.size i) :=
      ⟨a.val, by simpa [H, toHierarchicalSegmentForest] using a.isLt⟩
    have ha' : a' ≠ H.segments.root i := by
      simpa [a', H, toHierarchicalSegmentForest] using ha
    have hmem := hinteriorTarget i a'
      (E.hierarchyEmbedding.map_nonroot i a' ha')
    rw [← E.hierarchyEmbedding.fullCopy_segment i a'] at hmem
    simpa [a', H, toHierarchicalSegmentForest] using hmem

end Erdos547b.ZhaoLemma59HierarchicalSpecial

#print axioms Erdos547b.ZhaoLemma59HierarchicalSpecial.exists_specialRegularEmbedding
#print axioms Erdos547b.ZhaoLemma59HierarchicalSpecial.exists_specialRegularCopy
#print axioms Erdos547b.ZhaoLemma59HierarchicalSpecial.exists_threeLayerCopy_of_cleanedRegularSystem
