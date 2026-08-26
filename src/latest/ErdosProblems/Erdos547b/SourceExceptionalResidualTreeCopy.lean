/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.SourceExceptionalTreeCopy
import ErdosProblems.Erdos547b.SourceExceptionalRowBounds
import ErdosProblems.Erdos547b.ExceptionalResidualAllocation

/-!
# Construct the residual source matchings and the complete tree

The large-case discrepancy controls the literal cleaned source rows.
Their totals, capacities, branch mass and all residual loss margins are
proved, so only the exceptional selection and its genuine gain remain.
-/

open scoped SimpleGraph BigOperators Classical
noncomputable section

namespace Erdos547b.ZhaoSourceExceptionalResidualTreeCopy

open Finset SimpleGraph Erdos547b.TreePartition
open Erdos547b.ZhaoSourceExceptionalTreeCopy Erdos547b.ZhaoSourceExceptionalFamilies
open Erdos547b.ZhaoSourceExceptionalRowBounds Erdos547b.ZhaoExceptionalResidualAllocation
open Erdos547b.ZhaoSourceCapacityBudgetMargins Erdos547b.ZhaoSourceFamilyCapacity
open Erdos547b.ZhaoSourceDegreeFormRootRows Erdos547b.ZhaoSourceDegreeFormBounds
open Erdos547b.ZhaoSourceParameterSchedule Erdos547b.ZhaoSourceFreshChunkBounds
open Erdos547b.ZhaoSourceEmbeddingHost Erdos547b.ZhaoSourceParentCleanup
open Erdos547b.ZhaoLemma611Full Erdos547b.ZhaoClaim617BranchCount
open Erdos547b.ZhaoClaim616SourceBridge Erdos547b.ZhaoClaim615SourceSelection
open Erdos547b.ZhaoSourceTwoSideFamilyAdvance

variable {α : ℚ} {hostN q M : ℕ}
variable {G : SimpleGraph (Fin hostN)} [DecidableRel G.Adj]
variable (W : Witness α q M G) (Q : Certificate W) (S : CleanSourceWitness W Q)
variable {U : Type*} [Fintype U] [DecidableEq U]
variable {T : SimpleGraph U} [DecidableRel T.Adj]
variable (hT : T.IsTree) {globalRoot : U} {small : ℕ}
variable (P : ZhaoForestPartition T globalRoot small)

include hT in
theorem exists_treeCopy_of_largeExceptionalSaving
    (hα : 0 < α) (hα1 : α ≤ 1 / 4) (hhost : hostN = 2 * q)
    (horder : orderThreshold α M ≤ q) (hcard : Fintype.card U = q + 1)
    (s : Fin 2) (selected : Finset (BranchIndex P))
    (hselected : selected ⊆ sideBranches P s)
    (kind : FamilyKind) (hkind : kind.Valid α)
    (hbranch : ∀ i ∈ selected, kind.BranchValid (branchForest P).branches i)
    (E0 : Finset (MatchingEdge Q.claim67.M)) (hE0 : E0 ⊆ awayEdges W Q)
    (hedge : ∀ e ∈ E0, edgeValid W Q S (rootCluster W Q s) kind e)
    (hsaving : (∑ e ∈ E0, sideWeight W Q S s e) + (eta α : ℝ) ^ 3 * q ≤
      (branchMass P selected : ℝ))
    (hbudget0 : (branchMass P selected : ℝ) + 3 * (gamma α : ℝ) * q ≤
      ∑ e ∈ E0, idealCapacity W Q S (rootCluster W Q s) kind e)
    (hrows : ∀ R ⊆ awayEdges W Q,
      |(∑ e ∈ R, sideWeight W Q S s e) - (∑ e ∈ R, sideWeight W Q S (otherSide s) e)| ≤
        15 * (fourthRoot α : ℝ) * q)
    (hsmall : ∀ i, (branchForest P).branches.size i ≤ freshBranchBound α W.clusterSize)
    (hroots : (P.numParts : ℝ) ≤ (epsilon α : ℝ) * W.clusterSize) :
    Nonempty (T.Copy (embeddingHost W)) := by
  have hg : (0 : ℝ) ≤ gamma α := by exact_mod_cast (parameter_pos hα).2.2.2.2.2.2.1.le
  have ht : (0 : ℝ) ≤ fourthRoot α := by exact_mod_cast (parameter_pos hα).2.2.2.1.le
  have hN : (0 : ℝ) < W.clusterSize := by exact_mod_cast W.clusterSize_pos
  obtain ⟨E1, Eb, hE1, hEb, h1b, _hcover, hbudget1, hbudgetb⟩ :=
    exists_large_residual_allocation (awayEdges W Q) E0 (sideWeight W Q S s)
      (sideWeight W Q S (otherSide s)) q (10 * (fourthRoot α : ℝ) ^ 2)
      ((eta α : ℝ) ^ 3 * q) (branchMass P selected) (branchMass P (sideBranches P s \ selected))
      (branchMass P (sideBranches P (otherSide s))) (3 * (gamma α : ℝ) * q)
      (2 * W.clusterSize) (15 * (fourthRoot α : ℝ) * q) hE0 (by positivity)
      (fun e _ => sideWeight_le W Q S s e) (Nat.cast_nonneg _) (Nat.cast_nonneg _)
      (by positivity) (by positivity) (awayWeight_lower W Q S hα hα1 hhost horder s)
      (exceptional_mass_le P hcard s selected hselected) hsaving
      (large_residual_margin W hα hα1 hhost horder)
      (fun R hR => (le_abs_self _).trans (hrows R hR))
  have h01 : Disjoint E0 E1 := by
    rw [Finset.disjoint_left]
    intro e he0 he1
    exact (Finset.mem_sdiff.mp (hE1 he1)).2 he0
  have h0b : Disjoint E0 Eb := by
    rw [Finset.disjoint_left]
    intro e he0 heb
    exact (Finset.mem_sdiff.mp (hEb heb)).2 he0
  have haway : E0 ∪ E1 ∪ Eb ⊆ awayEdges W Q :=
    Finset.union_subset (Finset.union_subset hE0 (hE1.trans Finset.sdiff_subset))
      (hEb.trans Finset.sdiff_subset)
  exact exists_treeCopy_of_exceptionalBudgets W Q S hT P hα hα1 hhost horder s selected
    hselected kind hkind hbranch E0 E1 Eb h01 h0b h1b haway hedge hbudget0 hbudget1
    hbudgetb.le hsmall hroots

include hT in
theorem exists_treeCopy_of_smallExceptionalSaving
    (hα : 0 < α) (hα1 : α ≤ 1 / 4) (hhost : hostN = 2 * q)
    (horder : orderThreshold α M ≤ q) (hcard : Fintype.card U = q + 1)
    (s : Fin 2) (selected : Finset (BranchIndex P))
    (hselected : selected ⊆ sideBranches P s)
    (kind : FamilyKind) (hkind : kind.Valid α)
    (hbranch : ∀ i ∈ selected, kind.BranchValid (branchForest P).branches i)
    (E0 Eb : Finset (MatchingEdge Q.claim67.M))
    (hE0 : E0 ⊆ awayEdges W Q) (hEb : Eb ⊆ awayEdges W Q) (h0b : Disjoint E0 Eb)
    (hedge : ∀ e ∈ E0, edgeValid W Q S (rootCluster W Q s) kind e)
    (hsaving : (∑ e ∈ E0, sideWeight W Q S s e) + (eta α : ℝ) ^ 3 * q ≤
      (branchMass P selected : ℝ))
    (hbudget0 : (branchMass P selected : ℝ) + 3 * (gamma α : ℝ) * q ≤
      ∑ e ∈ E0, idealCapacity W Q S (rootCluster W Q s) kind e)
    (hbudgetb : (branchMass P (sideBranches P (otherSide s)) : ℝ) + 3 * (gamma α : ℝ) * q ≤
      ∑ e ∈ Eb, sideWeight W Q S (otherSide s) e)
    (hcost : (∑ e ∈ Eb, sideWeight W Q S s e) ≤ 4 * (fourthRoot α : ℝ) * q)
    (hsmall : ∀ i, (branchForest P).branches.size i ≤ freshBranchBound α W.clusterSize)
    (hroots : (P.numParts : ℝ) ≤ (epsilon α : ℝ) * W.clusterSize) :
    Nonempty (T.Copy (embeddingHost W)) := by
  let E1 := awayEdges W Q \ (E0 ∪ Eb)
  have hbudget1 := small_residual_budget (awayEdges W Q) E0 Eb (sideWeight W Q S s)
    q (10 * (fourthRoot α : ℝ) ^ 2) ((eta α : ℝ) ^ 3 * q)
    (branchMass P selected) (branchMass P (sideBranches P s \ selected))
    (branchMass P (sideBranches P (otherSide s))) (3 * (gamma α : ℝ) * q)
    (4 * (fourthRoot α : ℝ) * q) hE0 hEb h0b (Nat.cast_nonneg _)
    (awayWeight_lower W Q S hα hα1 hhost horder s)
    (exceptional_mass_le P hcard s selected hselected) hsaving hcost
    (small_residual_margin hα hα1)
  have h01 : Disjoint E0 E1 := by
    rw [Finset.disjoint_left]
    intro e he0 he1
    exact (Finset.mem_sdiff.mp he1).2 (Finset.mem_union_left _ he0)
  have h1b : Disjoint E1 Eb := by
    rw [Finset.disjoint_left]
    intro e he1 heb
    exact (Finset.mem_sdiff.mp he1).2 (Finset.mem_union_right _ heb)
  have haway : E0 ∪ E1 ∪ Eb ⊆ awayEdges W Q :=
    Finset.union_subset (Finset.union_subset hE0 Finset.sdiff_subset) hEb
  exact exists_treeCopy_of_exceptionalBudgets W Q S hT P hα hα1 hhost horder s selected
    hselected kind hkind hbranch E0 E1 Eb h01 h0b h1b haway hedge hbudget0 hbudget1
    hbudgetb hsmall hroots

end Erdos547b.ZhaoSourceExceptionalResidualTreeCopy

#print axioms Erdos547b.ZhaoSourceExceptionalResidualTreeCopy.exists_treeCopy_of_largeExceptionalSaving
#print axioms Erdos547b.ZhaoSourceExceptionalResidualTreeCopy.exists_treeCopy_of_smallExceptionalSaving
