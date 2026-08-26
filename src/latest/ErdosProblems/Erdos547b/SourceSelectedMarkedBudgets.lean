/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.SourceSelectedGroupMass
import ErdosProblems.Erdos547b.SourcePartitionCutMarks
import ErdosProblems.Erdos547b.SourceFreshPartitionBounds

/-!
# Actual source budgets for every processed selected-forest prefix

Branch orders, cut-parent mark counts and total source mass come from the
same fresh partition and selected F0 certificate. No occupancy assumption
or arbitrary optional-mark set is required.
-/

open scoped SimpleGraph BigOperators Classical
noncomputable section

namespace Erdos547b.ZhaoSourceSelectedMarkedBudgets

open Finset SimpleGraph Erdos547b.TreePartition
open Erdos547b.ZhaoSourceDegreeFormRootRows Erdos547b.ZhaoSourceNearFullMatching
open Erdos547b.ZhaoSourceSelectedGroupMass Erdos547b.ZhaoSourceClaim616Selection
open Erdos547b.ZhaoSourceParameterSchedule Erdos547b.ZhaoSourceDegreeFormBounds
open Erdos547b.ZhaoSourceFreshChunkBounds Erdos547b.ZhaoSourceFreshPartitionBounds
open Erdos547b.ZhaoSourcePartitionCutMarks Erdos547b.ZhaoSourceCrossingClusters
open Erdos547b.ZhaoClaim617BranchCount Erdos547b.ZhaoClaim616SourceBridge
open Erdos547b.ZhaoClaim616HierarchyClassification Erdos547b.ZhaoEvenReducedPadding
open Erdos547b.ZhaoClaim68BranchAdapter

variable {α : ℚ} {hostN q M : ℕ}
variable {G : SimpleGraph (Fin hostN)} [DecidableRel G.Adj]
variable (W : Witness α q M G) (Q : Certificate W) (S : CleanSourceWitness W Q)
variable {fb : ℝ} (O : Output W Q S fb) (C : Finset (EvenPadding (Index W)))
variable {U : Type*} [Fintype U] [DecidableEq U]
variable {T : SimpleGraph U} [DecidableRel T.Adj] {root : U}
variable (P : ZhaoForestPartition T root (freshBranchBound α W.clusterSize))

theorem prefix_marks_bound
    (hα : 0 < α) (hα1 : α ≤ 1 / 4) (hhost : hostN = 2 * q)
    (horder : orderThreshold α M ≤ q) (hcard : Fintype.card U = q + 1)
    (processed : Finset (Fin (Fintype.card (ChildKey P.orderedForest)))) :
    (∑ j ∈ processed, ((branchMarks P j).card : ℝ)) ≤ (epsilon α : ℝ) * W.clusterSize := by
  subst hostN
  have hroot := freshPartition_root_bound hα hα1 W horder hcard P
  have hall : (∑ j, ((branchMarks P j).card : ℝ)) ≤ (P.numParts : ℝ) := by
    exact_mod_cast sum_branchMarks_card_le P
  exact (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ processed)
    (by intros; positivity)).trans (hall.trans hroot)

theorem prefix_mass_bound
    (hα : 0 < α) (hα1 : α ≤ 1 / 4) (hhost : hostN = 2 * q)
    (horder : orderThreshold α M ≤ q) (hCcard : C.card = crossingScale W)
    (F : SelectedF0Within (branchForest P) (halfBranches P)
      (selectionTarget W Q S O C) (freshBranchBound α W.clusterSize))
    (processed : Finset (Fin (Fintype.card (ChildKey P.orderedForest))))
    (hprocessed : processed ⊆ F.selected) :
    (∑ j ∈ processed, ((branchForest P).branches.size j : ℝ)) <
      (5 / 2 + (epsilon α : ℝ)) * C.card * W.clusterSize := by
  have h := selected_mass_bound W Q S O C hα hα1 hhost horder hCcard P F
  have heq : (OrderedBranchForest.edgeDemand F.toSelectedF0.forest : ℝ) =
      ∑ j ∈ F.selected, ((branchForest P).branches.size j : ℝ) := by
    rw [SelectedF0.forest, OrderedBranchForest.edgeDemand_restrict, Nat.cast_sum]
  rw [heq] at h
  exact (Finset.sum_le_sum_of_subset_of_nonneg hprocessed (by intros; positivity)).trans_lt h

theorem selected_branch_bounds
    (F : SelectedF0Within (branchForest P) (halfBranches P)
      (selectionTarget W Q S O C) (freshBranchBound α W.clusterSize))
    (j : Fin (Fintype.card (ChildKey P.orderedForest))) (hj : j ∈ F.selected) :
    3 ≤ (branchForest P).branches.size j ∧
      (branchForest P).branches.size j ≤ freshBranchBound α W.clusterSize := by
  exact ⟨(OrderedBranchForest.mem_largeBranches _ _).mp (F.selected_large hj),
    canonical_branch_size_le_small P j⟩

end Erdos547b.ZhaoSourceSelectedMarkedBudgets

#print axioms Erdos547b.ZhaoSourceSelectedMarkedBudgets.prefix_marks_bound
#print axioms Erdos547b.ZhaoSourceSelectedMarkedBudgets.prefix_mass_bound
#print axioms Erdos547b.ZhaoSourceSelectedMarkedBudgets.selected_branch_bounds
