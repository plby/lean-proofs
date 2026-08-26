/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.SourcePathCoreMass
import ErdosProblems.Erdos547b.SourceExceptionalFamilies

/-! # Retaining whole branches does not increase either source-side mass -/

open scoped SimpleGraph BigOperators Classical
noncomputable section

namespace Erdos547b.ZhaoSourcePathCoreSideMass

open Finset SimpleGraph Erdos547b.TreePartition
open Erdos547b.ZhaoSourcePathCoreMass Erdos547b.ZhaoSourcePathBranchRestriction
open Erdos547b.ZhaoSourceReconnectedTwoRowCopy Erdos547b.ZhaoSourceExceptionalFamilies
open Erdos547b.ZhaoClaim615SourceSelection Erdos547b.ZhaoClaim617CleanLoss
open Erdos547b.ZhaoClaim617BranchCount Erdos547b.ZhaoClaim616SourceBridge
open Erdos547b.ZhaoClaim616HierarchyAttachments

variable {U : Type*} [Fintype U] [DecidableEq U]
variable {T : SimpleGraph U} [DecidableRel T.Adj]
variable {globalRoot : U} {small p : ℕ} (P : ZhaoForestPartition T globalRoot small)
variable (hp : p ≤ (cleanBranches P).card)

theorem coreMass_le_original (s : Fin 2) :
    coreMass P hp s ≤ (branchMass P (sideBranches P s) : ℝ) := by
  let index : Fin (keptBranches P hp).card → BranchIndex P :=
    fun i => (OrderedBranchForest.selectedEquiv (keptBranches P hp) i).val
  let source := sideFamily (coreForest P hp) (componentReservoirSide P) s
  have hinj : Function.Injective index := by
    intro i j hij
    exact (OrderedBranchForest.selectedEquiv (keptBranches P hp)).injective (Subtype.ext hij)
  have hsub : source.image index ⊆ sideBranches P s := by
    intro j hj
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
    exact (mem_sideBranches P s _).mpr (Finset.mem_filter.mp hi).2
  have heq : coreMass P hp s =
      ∑ j ∈ source.image index, ((branchForest P).branches.size j : ℝ) := by
    rw [Finset.sum_image (fun _ _ _ _ h => hinj h)]
    rfl
  rw [heq]
  calc
    _ ≤ ∑ j ∈ sideBranches P s, ((branchForest P).branches.size j : ℝ) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => Nat.cast_nonneg _)
    _ = (branchMass P (sideBranches P s) : ℝ) := by simp only [branchMass, Nat.cast_sum]

end Erdos547b.ZhaoSourcePathCoreSideMass

#print axioms Erdos547b.ZhaoSourcePathCoreSideMass.coreMass_le_original
