/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.Claim68HierarchicalLeaves
import ErdosProblems.Erdos547b.HierarchicalTargetCleaning
import ErdosProblems.Erdos547b.Lemma614HierarchicalUnifiedFullTree

/-!
# Target-reservoir realization of the Claim 6.8 leaf alternative

This is the placement-sensitive leaf-completion endpoint for actual target
subreservoirs.  Regular-pair density remains attached to the whole cluster
pairs.  The hierarchy roots are chosen online from the supplied target
subreservoirs after deleting the explicit target-relative exceptional sets.
-/

open scoped SimpleGraph

noncomputable section

namespace Erdos547b.ZhaoClaim68TargetUnifiedLeaves

open Finset Fintype SimpleGraph
open Erdos547b.TreePartition
open Erdos547b.ZhaoClaim68ConcreteLeaves
open Erdos547b.ZhaoClaim68HierarchicalLeaves
open Erdos547b.ZhaoLemma59SpecialSegmentation
open Erdos547b.ZhaoLemma59Hierarchical
open Erdos547b.ZhaoLemma59HierarchicalOnline
open Erdos547b.ZhaoLemma59HierarchicalRegular
open Erdos547b.ZhaoLemma59HierarchicalTargetCleaning
open Erdos547b.ZhaoLemma59HierarchicalUnified
open Erdos547b.ZhaoLemma59HierarchicalUnifiedRegular
open Erdos547b.ZhaoLemma614HierarchicalFullTree
open Erdos547b.ZhaoLemma614HierarchicalUnifiedFullTree

universe u v

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {T : SimpleGraph V} [DecidableRel T.Adj]
variable {globalRoot : V} {small : ℕ}

/-- Target cleaning never enlarges a hierarchy-root reservoir. -/
theorem targetRootCandidate_subset_rootRaw
    {B : Type v} [Fintype B] [DecidableEq B]
    {r s c : ℕ}
    (F : HierarchicalSegmentForest r s)
    (G : SimpleGraph B) [DecidableRel G.Adj] (rho : ℝ)
    (rootGroup : Fin s → Fin c)
    (rootWhole rootRaw : Fin c → Finset B)
    (interiorWhole interiorRaw :
      (i : Fin s) → Fin (F.segments.size i) → Finset B)
    (reserved : Finset B) (i : Fin s) :
    HierarchicalSegmentForest.targetRootCandidate F G rho rootGroup
        rootWhole rootRaw interiorWhole interiorRaw reserved i ⊆
      rootRaw (rootGroup i) := by
  intro z hz
  have hzRaw := (Finset.mem_sdiff.mp hz).1
  simpa [HierarchicalSegmentForest.targetRootCandidate,
    HierarchicalSegmentForest.targetCoordinateCandidate,
    ZhaoLemma59HierarchicalRegular.HierarchicalSegmentForest.rawCandidate]
    using hzRaw

/-- A placement-preserving unified hierarchy embedding of the leaf-deleted
core is sufficient to restore every original level-one leaf. -/
theorem exists_fullCopy_of_leafCore_fullTreeRegularEmbedding
    {B : Type v} [Fintype B] [DecidableEq B]
    (P : ZhaoForestPartition T globalRoot small) (hT : T.IsTree)
    (hcard : 3 ≤ Fintype.card V)
    (Gpair Gdegree : SimpleGraph B)
    [DecidableRel Gdegree.Adj]
    (hgraph : Gpair ≤ Gdegree)
    (globalRootImage : Fin 1 → B)
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
        Fin ((leafCoreHierarchy P hT).segments.size i) → Finset B)
    (E : FullTreeRegularEmbedding
      (leafDeletedCore P) (leafDeletedCore_isTree P hT)
      (leafDeletedGlobalRoot P) (leafCoreSpecial P hT) Gpair
      globalRootImage rootCandidate interiorCandidate)
    (hglobalLarge : globalRootImage 0 ∈
      largeParentHostVertices (V := V) Gdegree)
    (hrootLarge : ∀ i,
      leafCoreHierarchyOriginalVertex P hT
          ((leafCoreHierarchy P hT).segmentRoot i) ∈
        leafDeletedPartitionRoots P →
      rootCandidate i ⊆ largeParentHostVertices (V := V) Gdegree) :
    Nonempty (T.Copy Gdegree) := by
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
  · have hpMarked : p ∈ leafDeletedPartitionRoots P :=
      originalLeafParentCore_mem_partitionRoots P hT hcard x
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
              (leafCoreSpecial P hT) p) = p :=
        wholeHierarchyOriginal_toWholeHierarchyVertex
          (leafDeletedCore P) (leafDeletedCore_isTree P hT)
            (leafDeletedGlobalRoot P) (leafCoreSpecial P hT) p
      rw [← hiSource, hpSource]
      exact hpMarked
    exact (mem_largeParentHostVertices (V := V) Gdegree _).mp
      (hrootLarge i hiMarked hi)

/-- Raw target-reservoir endpoint.  Its assumptions are aggregate capacity
and pool-separation statements; there is no pointwise source-degree, copy,
or restored-edge premise. -/
theorem exists_fullCopy_of_leafCore_targetUnifiedSystem
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
    (rootPool interiorPool : Fin
      (marks
        (wholeBranchForest (leafDeletedCore P) (leafDeletedCore_isTree P hT)
          (leafDeletedGlobalRoot P))
        (leafCoreSpecial P hT)).card → Fin k)
    (rootWhole rootRaw : Fin c → Finset B)
    (interiorWhole interiorRaw :
      (i : Fin
        (marks
          (wholeBranchForest (leafDeletedCore P) (leafDeletedCore_isTree P hT)
            (leafDeletedGlobalRoot P))
          (leafCoreSpecial P hT)).card) →
        Fin ((leafCoreHierarchy P hT).segments.size i) → Finset B)
    (reserved : Finset B)
    (hreserved : Finset.univ.image globalRootImage ⊆ reserved)
    (hattachOriginalCapacity : ∀ i q,
      (leafCoreHierarchy P hT).parent i = Sum.inl q →
      (HierarchicalSegmentForest.poolLoad (leafCoreHierarchy P hT)
          rootPool interiorPool (rootPool i) + 1 : ℝ) +
          #(HierarchicalSegmentForest.targetCoordinateRemoved
            (leafCoreHierarchy P hT) Gpair rho rootGroup rootWhole rootRaw
              interiorWhole interiorRaw i
                ((leafCoreHierarchy P hT).segments.root i) ∪ reserved) ≤
        (#((rootRaw (rootGroup i)).filter
          (Gpair.Adj (globalRootImage q))) : ℝ))
    (hattachCapacity : ∀ i j a,
      (leafCoreHierarchy P hT).parent i = Sum.inr ⟨j, a⟩ →
      (HierarchicalSegmentForest.poolLoad (leafCoreHierarchy P hT)
          rootPool interiorPool (rootPool i) + 1 : ℝ) +
          #(HierarchicalSegmentForest.targetCoordinateRemoved
            (leafCoreHierarchy P hT) Gpair rho rootGroup rootWhole rootRaw
              interiorWhole interiorRaw i
                ((leafCoreHierarchy P hT).segments.root i) ∪ reserved) ≤
        (Gpair.edgeDensity
          (HierarchicalSegmentForest.rawCandidate (leafCoreHierarchy P hT)
            rootGroup rootWhole interiorWhole j a)
          (rootWhole (rootGroup i)) - rho) * #(rootRaw (rootGroup i)))
    (hinternalCapacity : ∀ i a b,
      ((leafCoreHierarchy P hT).segments.tree i).Adj a b →
      b ≠ (leafCoreHierarchy P hT).segments.root i →
      (HierarchicalSegmentForest.poolLoad (leafCoreHierarchy P hT)
          rootPool interiorPool (interiorPool i) + 1 : ℝ) +
          #(HierarchicalSegmentForest.targetInteriorRemoved
            (leafCoreHierarchy P hT) Gpair rho rootGroup rootWhole rootRaw
              interiorWhole interiorRaw reserved i b) ≤
        (Gpair.edgeDensity
          (HierarchicalSegmentForest.rawCandidate (leafCoreHierarchy P hT)
            rootGroup rootWhole interiorWhole i a)
          (interiorWhole i b) - rho) * #(interiorRaw i b))
    (horiginalInjective : Function.Injective globalRootImage)
    (hrootRawDisjoint : ∀ i j, rootPool i ≠ rootPool j →
      Disjoint (rootRaw (rootGroup i)) (rootRaw (rootGroup j)))
    (hinteriorRawDisjoint : ∀ i a j b,
      interiorPool i ≠ interiorPool j →
      Disjoint (interiorRaw i a) (interiorRaw j b))
    (hrootInteriorRawDisjoint : ∀ i j a,
      rootPool i ≠ interiorPool j →
      Disjoint (rootRaw (rootGroup i)) (interiorRaw j a))
    (hglobalLarge : globalRootImage 0 ∈
      largeParentHostVertices (V := V) Gdegree)
    (hrootRawLarge : ∀ i,
      leafCoreHierarchyOriginalVertex P hT
          ((leafCoreHierarchy P hT).segmentRoot i) ∈
        leafDeletedPartitionRoots P →
      rootRaw (rootGroup i) ⊆ largeParentHostVertices (V := V) Gdegree) :
    Nonempty (T.Copy Gdegree) := by
  let rootCandidate := HierarchicalSegmentForest.targetRootCandidate
    (leafCoreHierarchy P hT) Gpair rho rootGroup rootWhole rootRaw
      interiorWhole interiorRaw reserved
  let interiorCandidate := HierarchicalSegmentForest.targetInteriorCandidate
    (leafCoreHierarchy P hT) Gpair rho rootGroup rootWhole rootRaw
      interiorWhole interiorRaw reserved
  let S := HierarchicalSegmentForest.targetUnifiedCleanedRegularSystem
    (leafCoreHierarchy P hT) Gpair rho globalRootImage rootGroup
      rootPool interiorPool rootWhole rootRaw interiorWhole interiorRaw reserved
      hreserved hattachOriginalCapacity hattachCapacity hinternalCapacity
      horiginalInjective hrootRawDisjoint hinteriorRawDisjoint
      hrootInteriorRawDisjoint
  obtain ⟨E⟩ :=
    exists_fullTreeRegularEmbedding_of_unifiedCleanedRegularSystem
      (leafDeletedCore P) (leafDeletedCore_isTree P hT)
      (leafDeletedGlobalRoot P) (leafCoreSpecial P hT) Gpair globalRootImage
      rootPool interiorPool rootCandidate interiorCandidate S
  apply exists_fullCopy_of_leafCore_fullTreeRegularEmbedding P hT hcard
    Gpair Gdegree hgraph globalRootImage rootCandidate interiorCandidate E
    hglobalLarge
  intro i hi
  exact (targetRootCandidate_subset_rootRaw (leafCoreHierarchy P hT) Gpair rho
    rootGroup rootWhole rootRaw interiorWhole interiorRaw reserved i).trans
      (hrootRawLarge i hi)

end Erdos547b.ZhaoClaim68TargetUnifiedLeaves

#print axioms Erdos547b.ZhaoClaim68TargetUnifiedLeaves.exists_fullCopy_of_leafCore_targetUnifiedSystem
