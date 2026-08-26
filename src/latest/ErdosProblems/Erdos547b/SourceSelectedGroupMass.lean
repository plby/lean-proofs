/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.SourceClaim616Selection

/-!
# The selected forest's mass fits the private-group allocation

The bound retains the literal incident matching, rounded target, and fresh
branch overshoot. It applies to the same selected forest already constructed.
-/

open scoped SimpleGraph BigOperators Classical
noncomputable section

namespace Erdos547b.ZhaoSourceSelectedGroupMass

open Finset SimpleGraph Erdos547b.TreePartition
open Erdos547b.ZhaoSourceClaim616Selection Erdos547b.ZhaoSourceCrossingClusters
open Erdos547b.ZhaoSourceNearFullMatching Erdos547b.ZhaoSourceDegreeFormRootRows
open Erdos547b.ZhaoSourceDegreeFormBounds Erdos547b.ZhaoSourceParameterSchedule
open Erdos547b.ZhaoSourceFreshChunkBounds Erdos547b.ZhaoSourceExceptionalRowBounds
open Erdos547b.ZhaoSourceLargeExceptionalForcing Erdos547b.ZhaoEvenReducedPadding
open Erdos547b.ZhaoClaim616 Erdos547b.ZhaoClaim616SourceBridge
open Erdos547b.ZhaoClaim617BranchCount

variable {α : ℚ} {hostN q M : ℕ}
variable {G : SimpleGraph (Fin hostN)} [DecidableRel G.Adj]
variable (W : Witness α q M G) (Q : Certificate W) (S : CleanSourceWitness W Q)
variable {fb : ℝ} (O : Output W Q S fb) (C : Finset (EvenPadding (Index W)))

theorem target_overshoot_bound
    (hα : 0 < α) (hα1 : α ≤ 1 / 4) (hhost : hostN = 2 * q)
    (horder : orderThreshold α M ≤ q) (hCcard : C.card = crossingScale W) :
    (selectionTarget W Q S O C : ℝ) + freshBranchBound α W.clusterSize <
      (5 / 2 + (epsilon α : ℝ)) * C.card * W.clusterSize := by
  subst hostN
  have hr : (1 : ℝ) ≤ crossingScale W := by
    exact_mod_cast (scale_bounds W Q S O hα hα1 rfl horder).1
  have hεN := epsilon_mul_clusterSize_gt_two hα hα1 W horder
  have hε : (0 : ℝ) < epsilon α := by exact_mod_cast (parameter_pos hα).2.2.2.2.2.2.2
  have hm : (freshBranchBound α W.clusterSize : ℝ) ≤ (epsilon α : ℝ) * W.clusterSize / 2 :=
    Nat.floor_le (by positivity)
  have hrεN := mul_le_mul_of_nonneg_right hr
    (show (0 : ℝ) ≤ (epsilon α : ℝ) * W.clusterSize by positivity)
  have hovershoot : 1 + (freshBranchBound α W.clusterSize : ℝ) ≤
      (epsilon α : ℝ) * crossingScale W * W.clusterSize := by
    nlinarith only [hrεN, hm, hεN]
  have hMcard : (MatchingDecomposition.MzeroEdges O.D C).card ≤ crossingScale W :=
    (MatchingDecomposition.Mzero_edge_card_le O.D C).trans_eq hCcard
  have hMcardR : ((MatchingDecomposition.MzeroEdges O.D C).card : ℝ) ≤ crossingScale W := by
    exact_mod_cast hMcard
  have hA := (sideWeight_sum_le W Q S 0 (MatchingDecomposition.MzeroEdges O.D C)).trans
    (mul_le_mul_of_nonneg_left hMcardR (by positivity : 0 ≤ 2 * (W.clusterSize : ℝ)))
  have hnonneg : 0 ≤ (∑ e ∈ MatchingDecomposition.MzeroEdges O.D C, sideWeight W Q S 0 e) +
      (crossingScale W : ℝ) * W.clusterSize / 2 := by
    exact add_nonneg (Finset.sum_nonneg (fun e _ => sideWeight_nonneg W Q S 0 e)) (by positivity)
  have htarget : (selectionTarget W Q S O C : ℝ) <
      (∑ e ∈ MatchingDecomposition.MzeroEdges O.D C, sideWeight W Q S 0 e) +
        (crossingScale W : ℝ) * W.clusterSize / 2 + 1 := Nat.ceil_lt_add_one hnonneg
  rw [hCcard]
  nlinarith only [htarget, hA, hovershoot]

theorem selected_mass_bound
    (hα : 0 < α) (hα1 : α ≤ 1 / 4) (hhost : hostN = 2 * q)
    (horder : orderThreshold α M ≤ q) (hCcard : C.card = crossingScale W)
    {U : Type*} [Fintype U] [DecidableEq U]
    {T : SimpleGraph U} [DecidableRel T.Adj] {root : U} {small : ℕ}
    (P : ZhaoForestPartition T root small)
    (F : SelectedF0Within (branchForest P) (halfBranches P)
      (selectionTarget W Q S O C) (freshBranchBound α W.clusterSize)) :
    (OrderedBranchForest.edgeDemand F.toSelectedF0.forest : ℝ) <
      (5 / 2 + (epsilon α : ℝ)) * C.card * W.clusterSize := by
  have hu : (OrderedBranchForest.edgeDemand F.toSelectedF0.forest : ℝ) <
      (selectionTarget W Q S O C : ℝ) + freshBranchBound α W.clusterSize := by
    exact_mod_cast F.upper
  exact hu.trans (target_overshoot_bound W Q S O C hα hα1 hhost horder hCcard)

end Erdos547b.ZhaoSourceSelectedGroupMass

#print axioms Erdos547b.ZhaoSourceSelectedGroupMass.target_overshoot_bound
#print axioms Erdos547b.ZhaoSourceSelectedGroupMass.selected_mass_bound
