/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.SourcePartitionCutCoordinates

/-!
# Literal original-branch marks supplied by the actual cut coordinates

Every branch-coordinate cut parent is marked. All marks have rooted colour
zero, and the sum of their cardinalities is bounded by the number of parts.
-/

open scoped SimpleGraph BigOperators Classical
noncomputable section

namespace Erdos547b.ZhaoSourcePartitionCutMarks

open Finset SimpleGraph Erdos547b.TreePartition
open Erdos547b.ZhaoSourcePartitionCutCoordinates Erdos547b.ZhaoSourceGlobalPrefixState
open Erdos547b.ZhaoClaim617BranchCount
open Erdos547b.ZhaoClaim68 Erdos547b.ZhaoClaim68BranchAdapter

variable {U : Type*} [Fintype U] [DecidableEq U]
variable {T : SimpleGraph U} [DecidableRel T.Adj]
variable {globalRoot : U} {small : ℕ}
variable (P : ZhaoForestPartition T globalRoot small)

def parentCoordinates : Finset (CutCoordinate (branchForest P).branches P.numParts) :=
  Finset.univ.image (fun i : {i : Fin P.numParts // i.val ≠ 0} => partitionParent P i.1 i.2)

def branchMarks (j : Fin (Fintype.card (ChildKey P.orderedForest))) :
    Finset (Fin ((branchForest P).branches.size j)) :=
  Finset.univ.filter fun a => Sum.inr ⟨j, a⟩ ∈ parentCoordinates P

theorem branchMarks_color (hT : T.IsTree)
    (j : Fin (Fintype.card (ChildKey P.orderedForest)))
    (a : Fin ((branchForest P).branches.size j)) (ha : a ∈ branchMarks P j) :
    ((branchForest P).branches.isTree j).coloringTwoOfVert ((branchForest P).branches.root j) a = 0 := by
  obtain ⟨i, _, hi⟩ := Finset.mem_image.mp (Finset.mem_filter.mp ha).2
  have h := partitionParent_color P hT i.1 i.2
  rw [hi] at h
  exact h

theorem parentCoordinates_card_le : (parentCoordinates P).card ≤ P.numParts := by
  have h := Finset.card_image_le
    (s := (Finset.univ : Finset {i : Fin P.numParts // i.val ≠ 0}))
    (f := fun i => partitionParent P i.1 i.2)
  have ht : Fintype.card {i : Fin P.numParts // i.val ≠ 0} ≤ P.numParts := by
    simpa only [Fintype.card_fin] using Fintype.card_subtype_le (fun i : Fin P.numParts => i.val ≠ 0)
  exact h.trans (by simpa only [Finset.card_univ] using ht)

theorem sum_branchMarks_card_le : (∑ j, (branchMarks P j).card) ≤ P.numParts := by
  let coords := Finset.univ.sigma (branchMarks P)
  let inject : (Σ j, Fin ((branchForest P).branches.size j)) →
      CutCoordinate (branchForest P).branches P.numParts := Sum.inr
  have hinj : Function.Injective inject := fun _ _ h => Sum.inr.inj h
  have hsub : coords.image inject ⊆ parentCoordinates P := by
    intro v hv
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hv
    exact (Finset.mem_filter.mp (Finset.mem_sigma.mp ha).2).2
  have h := (Finset.card_le_card hsub).trans (parentCoordinates_card_le P)
  rw [Finset.card_image_of_injective _ hinj] at h
  simpa only [coords, Finset.card_sigma] using h

theorem branch_parent_mem_marks (i : Fin P.numParts) (hi : i.val ≠ 0)
    (j : Fin (Fintype.card (ChildKey P.orderedForest)))
    (a : Fin ((branchForest P).branches.size j))
    (hparent : partitionParent P i hi = Sum.inr ⟨j, a⟩) : a ∈ branchMarks P j := by
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
    Finset.mem_image.mpr ⟨⟨i, hi⟩, Finset.mem_univ _, hparent⟩⟩

end Erdos547b.ZhaoSourcePartitionCutMarks

#print axioms Erdos547b.ZhaoSourcePartitionCutMarks.branchMarks_color
#print axioms Erdos547b.ZhaoSourcePartitionCutMarks.sum_branchMarks_card_le
#print axioms Erdos547b.ZhaoSourcePartitionCutMarks.branch_parent_mem_marks
