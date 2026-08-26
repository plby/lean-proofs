/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.Claim68
import ErdosProblems.Erdos547b.Lemma74
import ErdosProblems.Erdos547b.Lemma78Full

/-!
# The concrete leaf-completion data in Claim 6.8

The first paragraph of Zhao's Claim 6.8 deletes the original-tree leaves
which occur at level one of the cut forest.  This file constructs all of the
source-side data for putting those leaves back.  Thus a caller which has
actually constructed the leaf-deleted core copy only has to prove that the
images of the surviving parents are large host vertices.
-/

open scoped SimpleGraph

noncomputable section

namespace Erdos547b.ZhaoClaim68ConcreteLeaves

open Finset Fintype SimpleGraph
open Erdos547b.TreePartition
open Erdos547b.ZhaoClaim68

universe u v

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {T : SimpleGraph V} [DecidableRel T.Adj]
variable {globalRoot : V} {small : ℕ}

/-- The literal set `W₁` removed at the start of Claim 6.8. -/
def originalLevelOneLeaves
    (P : ZhaoForestPartition T globalRoot small) : Finset V :=
  partitionLevelOneLeaves P ∩ graphLeaves T

theorem globalRoot_mem_partitionRoots
    (P : ZhaoForestPartition T globalRoot small) :
    globalRoot ∈ partitionRoots P := by
  apply Finset.mem_image.mpr
  exact ⟨⟨0, P.numParts_pos⟩, Finset.mem_univ _, P.first_root⟩

theorem originalLevelOneLeaf_ne_globalRoot
    (P : ZhaoForestPartition T globalRoot small)
    (x : {x // x ∈ originalLevelOneLeaves P}) :
    x.1 ≠ globalRoot := by
  intro hx
  have hxLevel : x.1 ∈ partitionLevelOne P :=
    (Finset.mem_inter.mp (Finset.mem_inter.mp x.2).1).1
  have hxRoot : x.1 ∈ partitionRoots P := by
    simpa [hx] using globalRoot_mem_partitionRoots P
  exact Finset.disjoint_left.mp (partitionRoots_disjoint_levelOne P)
    hxRoot hxLevel

/-- The neighbor of an original level-one leaf towards the global root. -/
noncomputable def originalLeafParent
    (P : ZhaoForestPartition T globalRoot small) (hT : T.IsTree)
    (x : {x // x ∈ originalLevelOneLeaves P}) : V :=
  Erdos547b.TreePartition.parent hT globalRoot
    (originalLevelOneLeaf_ne_globalRoot P x)

theorem originalLevelOneLeaf_degree_one
    (P : ZhaoForestPartition T globalRoot small)
    (x : {x // x ∈ originalLevelOneLeaves P}) :
    T.degree x.1 = 1 := by
  exact (Finset.mem_filter.mp (Finset.mem_inter.mp x.2).2).2

theorem originalLeafParent_adj
    (P : ZhaoForestPartition T globalRoot small) (hT : T.IsTree)
    (x : {x // x ∈ originalLevelOneLeaves P}) :
    T.Adj (originalLeafParent P hT x) x.1 := by
  exact Erdos547b.TreePartition.parent_adj hT globalRoot
    (originalLevelOneLeaf_ne_globalRoot P x)

/-- When the tree has at least three vertices, the parent of a deleted leaf
is not itself one of the deleted leaves. -/
theorem originalLeafParent_not_mem
    (P : ZhaoForestPartition T globalRoot small) (hT : T.IsTree)
    (hcard : 3 ≤ Fintype.card V)
    (x : {x // x ∈ originalLevelOneLeaves P}) :
    originalLeafParent P hT x ∉ originalLevelOneLeaves P := by
  intro hp
  have hpDegree : T.degree (originalLeafParent P hT x) = 1 :=
    originalLevelOneLeaf_degree_one P
      ⟨originalLeafParent P hT x, hp⟩
  exact Erdos547b.ZhaoLemma78Full74.not_adj_of_both_degree_one_of_three_le_card
    T hT hpDegree (originalLevelOneLeaf_degree_one P x) hcard
      (originalLeafParent_adj P hT x)

/-- An original-tree leaf has no neighbor other than the canonical parent
towards the global root. -/
theorem originalLeaf_unique
    (P : ZhaoForestPartition T globalRoot small) (hT : T.IsTree)
    (x : {x // x ∈ originalLevelOneLeaves P}) (y : V)
    (hxy : T.Adj x.1 y) :
    y = originalLeafParent P hT x := by
  have hu := SimpleGraph.degree_eq_one_iff_existsUnique_adj.mp
    (originalLevelOneLeaf_degree_one P x)
  exact hu.unique hxy (originalLeafParent_adj P hT x).symm

/-- The parent of an original level-one leaf is the root of the Zhao
component in which that leaf occurs.  This is the source-side fact which
allows the hierarchical embedding to reserve large host vertices only for
the partition roots, rather than for an arbitrary set of possible parents. -/
theorem originalLeafParent_eq_partitionRoot
    (P : ZhaoForestPartition T globalRoot small) (hT : T.IsTree)
    (x : {x // x ∈ originalLevelOneLeaves P}) :
    ∃ i : Fin P.numParts, originalLeafParent P hT x = P.roots i := by
  have hxLevelOneLeaf : x.1 ∈ partitionLevelOneLeaves P :=
    (Finset.mem_inter.mp x.2).1
  have hxLevel : x.1 ∈ partitionLevelOne P :=
    (Finset.mem_inter.mp hxLevelOneLeaf).1
  obtain ⟨i, hi⟩ := (Finset.mem_filter.mp hxLevel).2
  have hiT : T.Adj (P.roots i) x.1 :=
    (SimpleGraph.deleteEdges_adj.mp hi).1
  exact ⟨i, (originalLeaf_unique P hT x (P.roots i) hiT.symm).symm⟩

/-- No Zhao component root is deleted in the Claim-6.8 leaf core. -/
theorem partitionRoot_not_mem_originalLevelOneLeaves
    (P : ZhaoForestPartition T globalRoot small) (i : Fin P.numParts) :
    P.roots i ∉ originalLevelOneLeaves P := by
  intro hi
  have hiRoot : P.roots i ∈ partitionRoots P := by
    apply Finset.mem_image.mpr
    exact ⟨i, Finset.mem_univ _, rfl⟩
  have hiLevel : P.roots i ∈ partitionLevelOne P :=
    (Finset.mem_inter.mp (Finset.mem_inter.mp hi).1).1
  exact Finset.disjoint_left.mp (partitionRoots_disjoint_levelOne P)
    hiRoot hiLevel

/-- Vertex type of the literal leaf-deleted core used in Claim 6.8. -/
abbrev LeafDeletedVertex
    (P : ZhaoForestPartition T globalRoot small) :=
  {x : V // x ∉ originalLevelOneLeaves P}

@[simp] theorem card_leafDeletedVertex
    (P : ZhaoForestPartition T globalRoot small) :
    Fintype.card (LeafDeletedVertex P) =
      Fintype.card V - (originalLevelOneLeaves P).card := by
  simpa only [LeafDeletedVertex, Fintype.card_coe] using
    Fintype.card_subtype_compl
      (fun x : V ↦ x ∈ originalLevelOneLeaves P)

/-- The elementary source-size saving used when the large-leaf alternative
invokes Lemma 6.5 on the leaf-deleted core. -/
theorem card_leafDeletedVertex_le
    (P : ZhaoForestPartition T globalRoot small) (coreBound : ℕ)
    (hlarge : Fintype.card V ≤
      coreBound + (originalLevelOneLeaves P).card) :
    Fintype.card (LeafDeletedVertex P) ≤ coreBound := by
  rw [card_leafDeletedVertex]
  omega

/-- The literal induced graph left after deleting the original level-one
leaves. -/
abbrev leafDeletedCore
    (P : ZhaoForestPartition T globalRoot small) :
    SimpleGraph (LeafDeletedVertex P) :=
  T.induce ((originalLevelOneLeaves P : Set V)ᶜ)

/-- The global root as a vertex of the leaf-deleted core. -/
def leafDeletedGlobalRoot
    (P : ZhaoForestPartition T globalRoot small) : LeafDeletedVertex P :=
  ⟨globalRoot, by
    intro hr
    have hrRoot : globalRoot ∈ partitionRoots P :=
      globalRoot_mem_partitionRoots P
    have hrLevel : globalRoot ∈ partitionLevelOne P :=
      (Finset.mem_inter.mp (Finset.mem_inter.mp hr).1).1
    exact Finset.disjoint_left.mp (partitionRoots_disjoint_levelOne P)
      hrRoot hrLevel⟩

/-- Simultaneously deleting the original level-one leaves preserves the
tree.  This supplies the source tree required by the no-oracle hierarchical
regular-system backend. -/
theorem leafDeletedCore_isTree
    (P : ZhaoForestPartition T globalRoot small) (hT : T.IsTree) :
    (leafDeletedCore P).IsTree := by
  refine ⟨?_, hT.isAcyclic.induce _⟩
  apply Erdos547b.connected_induce_compl_of_leaves T
    (originalLevelOneLeaves P : Set V) hT.connected
  · intro v hv
    change v ∈ originalLevelOneLeaves P at hv
    exact (Finset.mem_filter.mp (Finset.mem_inter.mp hv).2).2
  · exact ⟨globalRoot, (leafDeletedGlobalRoot P).2⟩

/-- A partition root as a literal vertex of the leaf-deleted core. -/
def leafDeletedPartitionRoot
    (P : ZhaoForestPartition T globalRoot small) (i : Fin P.numParts) :
    LeafDeletedVertex P :=
  ⟨P.roots i, partitionRoot_not_mem_originalLevelOneLeaves P i⟩

/-- The finite marked set of all Zhao component roots in the leaf-deleted
core. -/
def leafDeletedPartitionRoots
    (P : ZhaoForestPartition T globalRoot small) :
    Finset (LeafDeletedVertex P) :=
  Finset.univ.image (leafDeletedPartitionRoot P)

/-- Every canonical leaf parent is represented by one of the marked core
partition roots. -/
theorem originalLeafParentCore_mem_partitionRoots
    (P : ZhaoForestPartition T globalRoot small) (hT : T.IsTree)
    (hcard : 3 ≤ Fintype.card V)
    (x : {x // x ∈ originalLevelOneLeaves P}) :
    (⟨originalLeafParent P hT x,
        originalLeafParent_not_mem P hT hcard x⟩ : LeafDeletedVertex P) ∈
      leafDeletedPartitionRoots P := by
  obtain ⟨i, hi⟩ := originalLeafParent_eq_partitionRoot P hT x
  apply Finset.mem_image.mpr
  refine ⟨i, Finset.mem_univ _, ?_⟩
  exact Subtype.ext hi.symm

/-- Package an actually constructed core copy and the large-parent degree
fact into the exact leaf-completion certificate.  No embedding continuation
or global containment statement is an input. -/
noncomputable def leafCompletionCertificateOfCoreCopy
    {B : Type v} [Fintype B] [DecidableEq B]
    (P : ZhaoForestPartition T globalRoot small) (hT : T.IsTree)
    (hcard : 3 ≤ Fintype.card V)
    (G : SimpleGraph B) [DecidableRel G.Adj]
    (coreCopy :
      (T.induce ((originalLevelOneLeaves P : Set V)ᶜ)).Copy G)
    (hdegree : ∀ x, Fintype.card V - 1 ≤
      G.degree (coreCopy
        ⟨originalLeafParent P hT x, originalLeafParent_not_mem P hT hcard x⟩)) :
    LeafCompletionCertificate T G (originalLevelOneLeaves P) where
  parent := originalLeafParent P hT
  parent_not_mem := originalLeafParent_not_mem P hT hcard
  parent_adj := originalLeafParent_adj P hT
  leaf_unique := originalLeaf_unique P hT
  coreCopy := coreCopy
  parentDegree := hdegree

/-- Direct full-copy endpoint for the actual Claim-6.8 leaf set. -/
theorem exists_copy_of_originalLevelOneLeaves_core
    {B : Type v} [Fintype B] [DecidableEq B]
    (P : ZhaoForestPartition T globalRoot small) (hT : T.IsTree)
    (hcard : 3 ≤ Fintype.card V)
    (G : SimpleGraph B) [DecidableRel G.Adj]
    (coreCopy :
      (T.induce ((originalLevelOneLeaves P : Set V)ᶜ)).Copy G)
    (hdegree : ∀ x, Fintype.card V - 1 ≤
      G.degree (coreCopy
        ⟨originalLeafParent P hT x, originalLeafParent_not_mem P hT hcard x⟩)) :
    Nonempty (T.Copy G) := by
  let C := leafCompletionCertificateOfCoreCopy P hT hcard G coreCopy hdegree
  obtain ⟨F, -, -⟩ := exists_copy_of_induce_compl_of_leaves
    T G (originalLevelOneLeaves P) C.parent C.parent_not_mem C.parent_adj
      C.leaf_unique C.coreCopy C.parentDegree
  exact ⟨F⟩

end Erdos547b.ZhaoClaim68ConcreteLeaves

#print axioms Erdos547b.ZhaoClaim68ConcreteLeaves.exists_copy_of_originalLevelOneLeaves_core
