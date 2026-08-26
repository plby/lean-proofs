/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.SourcePartitionCutMarks
import ErdosProblems.Erdos547b.SourceMarkedCutCoordinates

/-!
# Actual cut parents satisfy the combined marked-coordinate invariant
-/

open scoped SimpleGraph Classical
noncomputable section

namespace Erdos547b.ZhaoSourcePartitionCutMarks

open Finset SimpleGraph Erdos547b.TreePartition
open Erdos547b.ZhaoSourcePartitionCutCoordinates Erdos547b.ZhaoSourceMarkedGlobalPrefix
open Erdos547b.ZhaoClaim617BranchCount Erdos547b.ZhaoClaim68BranchAdapter

variable {U : Type*} [Fintype U] [DecidableEq U]
variable {T : SimpleGraph U} [DecidableRel T.Adj]
variable {globalRoot : U} {small : ℕ}
variable (P : ZhaoForestPartition T globalRoot small)

theorem partitionParent_marked
    (selected : Finset (Fin (Fintype.card (ChildKey P.orderedForest))))
    (i : Fin P.numParts) (hi : i.val ≠ 0) :
    coordinateMarked (branchForest P).branches (branchMarks P) selected (partitionParent P i hi) := by
  cases hparent : partitionParent P i hi with
  | inl j => trivial
  | inr a =>
      intro _
      exact branch_parent_mem_marks P i hi a.1 a.2 hparent

end Erdos547b.ZhaoSourcePartitionCutMarks

#print axioms Erdos547b.ZhaoSourcePartitionCutMarks.partitionParent_marked
