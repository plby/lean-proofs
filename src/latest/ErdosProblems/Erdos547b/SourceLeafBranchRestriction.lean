/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.SourcePartitionReconnectedGraph
import ErdosProblems.Erdos547b.Claim68ConcreteLeaves

/-!
# The actual original-level-one leaf deletion removes whole branches

Every removed branch is a singleton. All original component roots and
every recorded cut parent survive the deletion.
-/

open scoped SimpleGraph Classical
noncomputable section

namespace Erdos547b.ZhaoSourceLeafBranchRestriction

open Finset SimpleGraph Erdos547b.TreePartition
open Erdos547b.ZhaoSourcePartitionReconnectedGraph Erdos547b.ZhaoSourcePartitionCutCoordinates
open Erdos547b.ZhaoSourceRestrictedCutCoordinates Erdos547b.ZhaoLemma58CutForestReconstruction
open Erdos547b.ZhaoClaim68ConcreteLeaves Erdos547b.ZhaoClaim68 Erdos547b.ZhaoClaim68BranchAdapter
open Erdos547b.ZhaoClaim617BranchCount

variable {U : Type*} [Fintype U] [DecidableEq U]
variable {T : SimpleGraph U} [DecidableRel T.Adj]
variable {globalRoot : U} {small : ℕ} (P : ZhaoForestPartition T globalRoot small)

theorem branch_leaf_coordinate_root
    (j : Fin (Fintype.card (ChildKey P.orderedForest))) (a : Fin ((branchForest P).branches.size j))
    (h : coordinateVertex P (Sum.inr ⟨j, a⟩) ∈ originalLevelOneLeaves P) :
    a = (branchForest P).branches.root j := by
  have hlevel := (Finset.mem_inter.mp (Finset.mem_inter.mp h).1).1
  obtain ⟨i, hi⟩ := (Finset.mem_filter.mp hlevel).2
  have hm := (cutBranchGraphIso P).toHom.map_rel hi
  change (branchForest P).graph.Adj (cutBranchGraphIso P (P.roots i))
    (cutBranchGraphIso P (coordinateVertex P (Sum.inr ⟨j, a⟩))) at hm
  rw [cutBranchGraphIso_root, cutBranchGraphIso_coordinateVertex] at hm
  exact hm.2

theorem branch_mem_originalLeaves_iff
    (j : Fin (Fintype.card (ChildKey P.orderedForest))) (a : Fin ((branchForest P).branches.size j)) :
    coordinateVertex P (Sum.inr ⟨j, a⟩) ∈ originalLevelOneLeaves P ↔
      actualBranchRoot P j ∈ originalLevelOneLeaves P := by
  constructor
  · intro h
    rw [branch_leaf_coordinate_root P j a h] at h
    simpa only [coordinateVertex, actualBranchRoot_eq_partitionBranchEquiv] using h
  · intro h
    have hsize := (actualBranchRoot_mem_levelOneLeaves_iff P j).mp (Finset.mem_inter.mp h).1
    have ha : a = (branchForest P).branches.root j := by
      apply Fin.ext
      have ha := a.isLt
      have hr := ((branchForest P).branches.root j).isLt
      omega
    rw [ha]
    simpa only [coordinateVertex, actualBranchRoot_eq_partitionBranchEquiv] using h

def keptBranches : Finset (Fin (Fintype.card (ChildKey P.orderedForest))) :=
  Finset.univ.filter fun j => actualBranchRoot P j ∉ originalLevelOneLeaves P

theorem retained_iff_not_originalLeaves (x : (branchForest P).Vertex) :
    retained (branchForest P) (keptBranches P) x ↔ coordinateVertex P x ∉ originalLevelOneLeaves P := by
  cases x with
  | inl i =>
      exact iff_of_true trivial (partitionRoot_not_mem_originalLevelOneLeaves P i)
  | inr a =>
      rcases a with ⟨j, a⟩
      change j ∈ keptBranches P ↔ _
      simp only [keptBranches, Finset.mem_filter, Finset.mem_univ, true_and,
        branch_mem_originalLeaves_iff]

theorem parent_not_originalLeaves (i : Fin P.numParts) (hi : i.val ≠ 0) :
    P.parent i hi ∉ originalLevelOneLeaves P := by
  intro h
  have hlevel := (Finset.mem_inter.mp (Finset.mem_inter.mp h).1).1
  obtain ⟨j, hj⟩ := (Finset.mem_filter.mp hlevel).2
  have hunique := SimpleGraph.degree_eq_one_iff_existsUnique_adj.mp
    (originalLevelOneLeaf_degree_one P ⟨P.parent i hi, h⟩)
  have heq : P.roots j = P.roots i := hunique.unique
    (SimpleGraph.deleteEdges_adj.mp hj).1.symm (P.cut_adj i hi).symm
  rw [heq] at hj
  apply (SimpleGraph.deleteEdges_adj.mp hj).2
  exact Finset.mem_image.mpr ⟨⟨i, hi⟩, Finset.mem_univ _, rfl⟩

theorem partitionParent_retained (i : Fin P.numParts) (hi : i.val ≠ 0) :
    retained (branchForest P) (keptBranches P) (partitionParent P i hi) := by
  rw [retained_iff_not_originalLeaves, partitionParent_vertex]
  exact parent_not_originalLeaves P i hi

end Erdos547b.ZhaoSourceLeafBranchRestriction

#print axioms Erdos547b.ZhaoSourceLeafBranchRestriction.branch_mem_originalLeaves_iff
#print axioms Erdos547b.ZhaoSourceLeafBranchRestriction.parent_not_originalLeaves
#print axioms Erdos547b.ZhaoSourceLeafBranchRestriction.partitionParent_retained
