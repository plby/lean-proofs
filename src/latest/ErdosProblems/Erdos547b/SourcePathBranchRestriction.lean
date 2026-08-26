/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.Claim617CleanSelection
import ErdosProblems.Erdos547b.RootTwoPathCoreGraph
import ErdosProblems.Erdos547b.SourceRestrictedCutCoordinates
import ErdosProblems.Erdos547b.SourcePartitionReconnectedGraph

/-!
# Postponed paths remove exactly their selected original branches

Every component root and recorded cut parent survives. This is the literal
source restriction needed by the switched matching's core embedding.
-/

open scoped SimpleGraph Classical
noncomputable section

namespace Erdos547b.ZhaoSourcePathBranchRestriction

open Finset SimpleGraph Erdos547b.TreePartition
open Erdos547b.ZhaoClaim617CleanLoss Erdos547b.ZhaoClaim617CleanSelection
open Erdos547b.ZhaoClaim617RootPaths Erdos547b.ZhaoClaim617BranchCount
open Erdos547b.ZhaoClaim68 Erdos547b.ZhaoClaim68BranchAdapter
open Erdos547b.ZhaoSourcePartitionCutCoordinates Erdos547b.ZhaoSourceRestrictedCutCoordinates

variable {U : Type*} [Fintype U] [DecidableEq U]
variable {T : SimpleGraph U} [DecidableRel T.Adj]
variable {globalRoot : U} {small p : ℕ} (P : ZhaoForestPartition T globalRoot small)
variable (hp : p ≤ (cleanBranches P).card)

def selectedBranches : Finset (Fin (Fintype.card (ChildKey P.orderedForest))) :=
  Finset.univ.image fun i : Fin p => (selectedBranch P hp i).1.1

theorem selectedBranches_card : (selectedBranches P hp).card = p := by
  have hinj : Function.Injective (fun i : Fin p => (selectedBranch P hp i).1.1) := by
    intro i j h
    apply selectedBranch_injective P hp
    exact Subtype.ext (Subtype.ext h)
  rw [selectedBranches, Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]

def keptBranches : Finset (Fin (Fintype.card (ChildKey P.orderedForest))) :=
  Finset.univ \ selectedBranches P hp

theorem mem_removed_iff (x : U) :
    x ∈ (selectedPaths P hp).removedSet ↔
      ∃ i, x = (selectedPaths P hp).middle i ∨ x = (selectedPaths P hp).leaf i := by
  simp only [RootTwoPathSystem.removedSet, RootTwoPathSystem.leafSet, Finset.mem_union,
    Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro (⟨i, hi⟩ | ⟨i, hi⟩)
    · exact ⟨i, Or.inl hi.symm⟩
    · exact ⟨i, Or.inr hi.symm⟩
  · rintro ⟨i, hi | hi⟩
    · exact Or.inl ⟨i, hi.symm⟩
    · exact Or.inr ⟨i, hi.symm⟩

private theorem coordinateVertex_branch
    (j : Fin (Fintype.card (ChildKey P.orderedForest)))
    (a : Fin ((branchForest P).branches.size j)) :
    coordinateVertex P (Sum.inr ⟨j, a⟩) =
      P.fromOrderedForestVertex (branchVertexEquiv P.orderedForest j a).1 := rfl

theorem branch_mem_removed_iff
    (j : Fin (Fintype.card (ChildKey P.orderedForest)))
    (a : Fin ((branchForest P).branches.size j)) :
    coordinateVertex P (Sum.inr ⟨j, a⟩) ∈ (selectedPaths P hp).removedSet ↔
      j ∈ selectedBranches P hp := by
  have hspec (i : Fin p) :
      (branchVertexEquiv P.orderedForest j a).1 ∈
          branchSet P.orderedForest (selectedBranch P hp i).1.1 ↔
        coordinateVertex P (Sum.inr ⟨j, a⟩) = (selectedPaths P hp).middle i ∨
        coordinateVertex P (Sum.inr ⟨j, a⟩) = (selectedPaths P hp).leaf i :=
    cleanPaths_branchSet_iff P (selectedBranch P hp i) _
  constructor
  · intro hx
    obtain ⟨i, hi⟩ := (mem_removed_iff P hp _).mp hx
    have hi' := (hspec i).mpr hi
    have hji : j = (selectedBranch P hp i).1.1 := by
      by_contra hne
      exact Set.disjoint_left.mp (branchSet_disjoint P.orderedForest hne)
        (branchVertexEquiv P.orderedForest j a).2 hi'
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, hji.symm⟩
  · intro hj
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hj
    apply (mem_removed_iff P hp _).mpr
    refine ⟨i, (hspec i).mp ?_⟩
    rw [hi]
    exact (branchVertexEquiv P.orderedForest j a).2

theorem root_not_removed (i : Fin P.numParts) :
    P.roots i ∉ (selectedPaths P hp).removedSet := by
  intro h
  obtain ⟨j, hj | hj⟩ := (mem_removed_iff P hp _).mp h
  · exact selectedPaths_middle_not_root P hp j
      (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, hj⟩)
  · exact selectedPaths_leaf_not_root P hp j
      (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, hj⟩)

theorem retained_iff_not_removed (x : (branchForest P).Vertex) :
    retained (branchForest P) (keptBranches P hp) x ↔
      coordinateVertex P x ∉ (selectedPaths P hp).removedSet := by
  cases x with
  | inl i => exact iff_of_true trivial (root_not_removed P hp i)
  | inr z =>
      rcases z with ⟨j, a⟩
      change j ∈ keptBranches P hp ↔ _
      simp only [keptBranches, Finset.mem_sdiff, Finset.mem_univ, true_and,
        branch_mem_removed_iff]

theorem parent_not_removed (i : Fin P.numParts) (hi : i.val ≠ 0) :
    P.parent i hi ∉ (selectedPaths P hp).removedSet := by
  intro h
  have hparent : P.parent i hi ∈ partitionParents P :=
    Finset.mem_image.mpr ⟨⟨i, hi⟩, Finset.mem_univ _, rfl⟩
  obtain ⟨j, hj | hj⟩ := (mem_removed_iff P hp _).mp h
  · exact selectedPaths_middle_not_parent P hp j (hj ▸ hparent)
  · exact selectedPaths_leaf_not_parent P hp j (hj ▸ hparent)

theorem partitionParent_retained (i : Fin P.numParts) (hi : i.val ≠ 0) :
    retained (branchForest P) (keptBranches P hp) (partitionParent P i hi) := by
  rw [retained_iff_not_removed, partitionParent_vertex]
  exact parent_not_removed P hp i hi

end Erdos547b.ZhaoSourcePathBranchRestriction

#print axioms Erdos547b.ZhaoSourcePathBranchRestriction.selectedBranches_card
#print axioms Erdos547b.ZhaoSourcePathBranchRestriction.branch_mem_removed_iff
#print axioms Erdos547b.ZhaoSourcePathBranchRestriction.partitionParent_retained
