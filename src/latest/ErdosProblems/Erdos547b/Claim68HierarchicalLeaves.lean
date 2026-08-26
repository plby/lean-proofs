/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.Claim68ConcreteLeaves
import ErdosProblems.Erdos547b.Claim616ResidualAllocation
import ErdosProblems.Erdos547b.Lemma614HierarchicalFullTree

/-!
# Claim 6.8 leaf completion from the hierarchical regular-system embedding

The large-level-one-leaf alternative in Claim 6.8 first embeds the literal
tree with those leaves deleted, while insisting that every surviving leaf
parent is sent to a large host vertex.  `Claim68ConcreteLeaves` proves that
those parents are precisely Zhao component roots.  The placement-sensitive
full-tree backend can therefore mark the component roots, retain their
root-candidate membership, and then add all deleted leaves by Hall's theorem.

The public endpoint below has no source-copy, containment, continuation, or
pointwise adjacency hypothesis.  Its host input is the concrete cleaned
regular system together with the statement that its root candidates are
subsets of the literal high-degree finset.
-/

open scoped SimpleGraph

noncomputable section

namespace Erdos547b.ZhaoClaim68HierarchicalLeaves

open Finset Fintype SimpleGraph
open Erdos547b.TreePartition
open Erdos547b.ZhaoClaim68ConcreteLeaves
open Erdos547b.ZhaoClaim616ResidualAllocation
open Erdos547b.ZhaoLemma59SpecialSegmentation
open Erdos547b.ZhaoLemma59HierarchicalRegular
open Erdos547b.ZhaoLemma614HierarchicalFullTree

universe u v

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {T : SimpleGraph V} [DecidableRel T.Adj]
variable {globalRoot : V} {small : ℕ}

/-- Host vertices with the exact degree needed for the Claim-6.8 Hall
completion. -/
def largeParentHostVertices
    {B : Type v} [Fintype B]
    (G : SimpleGraph B) [DecidableRel G.Adj] : Finset B :=
  Finset.univ.filter fun z => Fintype.card V - 1 ≤ G.degree z

@[simp] theorem mem_largeParentHostVertices
    {B : Type v} [Fintype B]
    (G : SimpleGraph B) [DecidableRel G.Adj] (z : B) :
    z ∈ largeParentHostVertices (V := V) G ↔
      Fintype.card V - 1 ≤ G.degree z := by
  simp [largeParentHostVertices]

/-- Every surviving canonical allocation boundary in the leaf-deleted
core.  Besides the component roots needed for leaf completion, this retains
the canonical root of every Zhao root-deleted branch; hence no hierarchy
segment crosses a branch-allocation boundary. -/
def leafCoreMarkedVertices
    (P : ZhaoForestPartition T globalRoot small) :
    Finset (LeafDeletedVertex P) :=
  Finset.univ.filter fun x ↦ x.1 ∈ allocationMarkedVertices P ∅

@[simp] theorem mem_leafCoreMarkedVertices
    (P : ZhaoForestPartition T globalRoot small) (x : LeafDeletedVertex P) :
    x ∈ leafCoreMarkedVertices P ↔
      x.1 ∈ allocationMarkedVertices P ∅ := by
  simp [leafCoreMarkedVertices]

theorem leafDeletedPartitionRoots_subset_leafCoreMarkedVertices
    (P : ZhaoForestPartition T globalRoot small) :
    leafDeletedPartitionRoots P ⊆ leafCoreMarkedVertices P := by
  intro x hx
  obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx
  apply (mem_leafCoreMarkedVertices P _).2
  apply partitionRoots_subset_allocationMarkedVertices P ∅
  exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩

/-- The marked coordinates for the leaf-deleted core. -/
abbrev leafCoreSpecial
    (P : ZhaoForestPartition T globalRoot small) (hT : T.IsTree) :=
  wholeSpecialCoordinates (leafDeletedCore P) (leafDeletedCore_isTree P hT)
    (leafDeletedGlobalRoot P) (leafCoreMarkedVertices P)

abbrev leafCoreHierarchy
    (P : ZhaoForestPartition T globalRoot small) (hT : T.IsTree) :=
  wholeHierarchy (leafDeletedCore P) (leafDeletedCore_isTree P hT)
    (leafDeletedGlobalRoot P) (leafCoreSpecial P hT)

def leafCoreHierarchyOriginalVertex
    (P : ZhaoForestPartition T globalRoot small) (hT : T.IsTree) :
    (leafCoreHierarchy P hT).Vertex → LeafDeletedVertex P :=
  wholeHierarchyOriginalVertex (leafDeletedCore P)
    (leafDeletedCore_isTree P hT) (leafDeletedGlobalRoot P)
      (leafCoreSpecial P hT)

/-- A concrete cleaned regular system for the literal leaf-deleted core,
with all root candidates inside the host high-degree set, gives a copy of
the original tree after the deleted leaves are restored. -/
theorem exists_fullCopy_of_leafCore_cleanedRegularSystem
    {B : Type v} [Fintype B] [DecidableEq B]
    {c k : ℕ}
    (P : ZhaoForestPartition T globalRoot small) (hT : T.IsTree)
    (hcard : 3 ≤ Fintype.card V)
    (Gpair Gdegree : SimpleGraph B)
    [DecidableRel Gpair.Adj] [DecidableRel Gdegree.Adj]
    (hgraph : Gpair ≤ Gdegree)
    (rho : ℝ)
    (globalRootImage : Fin 1 → B)
    (rootGroup : Fin
      (marks
        (wholeBranchForest (leafDeletedCore P) (leafDeletedCore_isTree P hT)
          (leafDeletedGlobalRoot P))
        (leafCoreSpecial P hT)).card → Fin c)
    (group : Fin
      (marks
        (wholeBranchForest (leafDeletedCore P) (leafDeletedCore_isTree P hT)
          (leafDeletedGlobalRoot P))
        (leafCoreSpecial P hT)).card → Fin k)
    (rootCandidate : Fin
      (marks
        (wholeBranchForest (leafDeletedCore P) (leafDeletedCore_isTree P hT)
          (leafDeletedGlobalRoot P))
        (leafCoreSpecial P hT)).card → Finset B)
    (interiorCandidate :
      (i : Fin
        (marks
          (wholeBranchForest (leafDeletedCore P) (leafDeletedCore_isTree P hT)
            (leafDeletedGlobalRoot P))
          (leafCoreSpecial P hT)).card) →
        Fin ((wholeHierarchy (leafDeletedCore P) (leafDeletedCore_isTree P hT)
          (leafDeletedGlobalRoot P) (leafCoreSpecial P hT)).segments.size i) →
          Finset B)
    (S :
      ZhaoLemma59HierarchicalRegular.HierarchicalSegmentForest.CleanedRegularSystem
        (wholeHierarchy (leafDeletedCore P) (leafDeletedCore_isTree P hT)
          (leafDeletedGlobalRoot P) (leafCoreSpecial P hT))
        Gpair rho globalRootImage rootGroup group rootCandidate interiorCandidate)
    (hglobalLarge : globalRootImage 0 ∈
      largeParentHostVertices (V := V) Gdegree)
    (hrootLarge : ∀ i,
      leafCoreHierarchyOriginalVertex P hT
          ((leafCoreHierarchy P hT).segmentRoot i) ∈
        leafDeletedPartitionRoots P →
      rootCandidate i ⊆ largeParentHostVertices (V := V) Gdegree) :
    Nonempty (T.Copy Gdegree) := by
  obtain ⟨E⟩ :=
    exists_fullTreeRegularEmbedding_of_cleanedRegularSystem
      (leafDeletedCore P) (leafDeletedCore_isTree P hT)
      (leafDeletedGlobalRoot P) (leafCoreSpecial P hT) Gpair rho
      globalRootImage rootGroup group rootCandidate interiorCandidate S
  let coreCopy : (leafDeletedCore P).Copy Gdegree :=
    (SimpleGraph.Copy.ofLE Gpair Gdegree hgraph).comp E.fullCopy
  have hcore_apply (y : LeafDeletedVertex P) :
      coreCopy y = E.fullCopy y := rfl
  apply exists_copy_of_originalLevelOneLeaves_core P hT hcard Gdegree coreCopy
  intro x
  let p : LeafDeletedVertex P :=
    ⟨originalLeafParent P hT x,
      originalLeafParent_not_mem P hT hcard x⟩
  rw [hcore_apply p]
  by_cases hp : p = leafDeletedGlobalRoot P
  · have hmap : E.fullCopy p = globalRootImage 0 := by
      rw [hp]
      exact E.map_globalRoot (leafDeletedCore P) (leafDeletedCore_isTree P hT)
        (leafDeletedGlobalRoot P) (leafCoreSpecial P hT) Gpair globalRootImage
        rootCandidate interiorCandidate
    rw [hmap]
    exact (mem_largeParentHostVertices (V := V) Gdegree _).mp hglobalLarge
  · have hpMarked : p ∈ leafDeletedPartitionRoots P := by
      exact originalLeafParentCore_mem_partitionRoots P hT hcard x
    have hpAllocationMarked : p ∈ leafCoreMarkedVertices P :=
      leafDeletedPartitionRoots_subset_leafCoreMarkedVertices P hpMarked
    obtain ⟨i, hiSource, hi⟩ := E.map_markedVertex_eq_segmentRoot
      (leafDeletedCore P) (leafDeletedCore_isTree P hT)
      (leafDeletedGlobalRoot P) (leafCoreMarkedVertices P) Gpair
      globalRootImage rootCandidate interiorCandidate p hpAllocationMarked hp
    have hiMarked : leafCoreHierarchyOriginalVertex P hT
        ((leafCoreHierarchy P hT).segmentRoot i) ∈
          leafDeletedPartitionRoots P := by
      have hpSource : leafCoreHierarchyOriginalVertex P hT
          (toWholeHierarchyVertex (leafDeletedCore P)
            (leafDeletedCore_isTree P hT) (leafDeletedGlobalRoot P)
              (leafCoreSpecial P hT) p) = p := by
        exact wholeHierarchyOriginal_toWholeHierarchyVertex
          (leafDeletedCore P) (leafDeletedCore_isTree P hT)
            (leafDeletedGlobalRoot P) (leafCoreSpecial P hT) p
      rw [← hiSource]
      rw [hpSource]
      exact hpMarked
    exact (mem_largeParentHostVertices (V := V) Gdegree _).mp
      (hrootLarge i hiMarked hi)

/-- Containment spelling used to contradict the nonembedding hypothesis in
Claim 6.8 and subsequently Claim 6.17. -/
theorem isContained_of_leafCore_cleanedRegularSystem
    {B : Type v} [Fintype B] [DecidableEq B]
    {c k : ℕ}
    (P : ZhaoForestPartition T globalRoot small) (hT : T.IsTree)
    (hcard : 3 ≤ Fintype.card V)
    (Gpair Gdegree : SimpleGraph B)
    [DecidableRel Gpair.Adj] [DecidableRel Gdegree.Adj]
    (hgraph : Gpair ≤ Gdegree)
    (rho : ℝ)
    (globalRootImage : Fin 1 → B)
    (rootGroup : Fin
      (marks
        (wholeBranchForest (leafDeletedCore P) (leafDeletedCore_isTree P hT)
          (leafDeletedGlobalRoot P))
        (leafCoreSpecial P hT)).card → Fin c)
    (group : Fin
      (marks
        (wholeBranchForest (leafDeletedCore P) (leafDeletedCore_isTree P hT)
          (leafDeletedGlobalRoot P))
        (leafCoreSpecial P hT)).card → Fin k)
    (rootCandidate : Fin
      (marks
        (wholeBranchForest (leafDeletedCore P) (leafDeletedCore_isTree P hT)
          (leafDeletedGlobalRoot P))
        (leafCoreSpecial P hT)).card → Finset B)
    (interiorCandidate :
      (i : Fin
        (marks
          (wholeBranchForest (leafDeletedCore P) (leafDeletedCore_isTree P hT)
            (leafDeletedGlobalRoot P))
          (leafCoreSpecial P hT)).card) →
        Fin ((wholeHierarchy (leafDeletedCore P) (leafDeletedCore_isTree P hT)
          (leafDeletedGlobalRoot P) (leafCoreSpecial P hT)).segments.size i) →
          Finset B)
    (S :
      ZhaoLemma59HierarchicalRegular.HierarchicalSegmentForest.CleanedRegularSystem
        (wholeHierarchy (leafDeletedCore P) (leafDeletedCore_isTree P hT)
          (leafDeletedGlobalRoot P) (leafCoreSpecial P hT))
        Gpair rho globalRootImage rootGroup group rootCandidate interiorCandidate)
    (hglobalLarge : globalRootImage 0 ∈
      largeParentHostVertices (V := V) Gdegree)
    (hrootLarge : ∀ i,
      leafCoreHierarchyOriginalVertex P hT
          ((leafCoreHierarchy P hT).segmentRoot i) ∈
        leafDeletedPartitionRoots P →
      rootCandidate i ⊆ largeParentHostVertices (V := V) Gdegree) :
    T.IsContained Gdegree := by
  exact (exists_fullCopy_of_leafCore_cleanedRegularSystem P hT hcard
    Gpair Gdegree hgraph rho
    globalRootImage rootGroup group rootCandidate interiorCandidate S
    hglobalLarge hrootLarge).some.isContained

end Erdos547b.ZhaoClaim68HierarchicalLeaves

#print axioms Erdos547b.ZhaoClaim68HierarchicalLeaves.exists_fullCopy_of_leafCore_cleanedRegularSystem
#print axioms Erdos547b.ZhaoClaim68HierarchicalLeaves.isContained_of_leafCore_cleanedRegularSystem
