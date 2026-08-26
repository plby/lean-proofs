/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.SourceOrdinaryTwoFamilyTreeCopy
import ErdosProblems.Erdos547b.SourceRawDiscrepancyNumerics
import ErdosProblems.Erdos547b.Lemma613Allocation

/-!
# Raw source-row discrepancy from actual tree noncontainment

The finite allocation lemma, all its source-scale gates, and both actual
root assignments are now combined. No row normalization or embedding
continuation is retained in the resulting discrepancy bound.
-/

open scoped SimpleGraph BigOperators Classical
noncomputable section

namespace Erdos547b.ZhaoSourceRawDiscrepancy

open Finset SimpleGraph Erdos547b.TreePartition
open Erdos547b.ZhaoSourceOrdinaryTwoFamilyTreeCopy Erdos547b.ZhaoSourceRawDiscrepancyNumerics
open Erdos547b.ZhaoLemma613Allocation Erdos547b.ZhaoSourceExceptionalFamilies
open Erdos547b.ZhaoSourceExceptionalRowBounds Erdos547b.ZhaoSourceDegreeFormRootRows
open Erdos547b.ZhaoSourceDegreeFormBounds Erdos547b.ZhaoSourceParameterSchedule
open Erdos547b.ZhaoSourceFreshChunkBounds Erdos547b.ZhaoSourceEmbeddingHost
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
theorem raw_discrepancy_lt_of_not_copy
    (hα : 0 < α) (hα1 : α ≤ 1 / 4) (hhost : hostN = 2 * q)
    (horder : orderThreshold α M ≤ q) (hcard : Fintype.card U = q + 1)
    (hminor : (fourthRoot α : ℝ) * q ≤ (branchMass P (sideBranches P 1) : ℝ))
    (hsmall : ∀ i, (branchForest P).branches.size i ≤ freshBranchBound α W.clusterSize)
    (hroots : (P.numParts : ℝ) ≤ (epsilon α : ℝ) * W.clusterSize)
    (hnot : ¬Nonempty (T.Copy (embeddingHost W)))
    (R : Finset (MatchingEdge Q.claim67.M)) (hR : R ⊆ awayEdges W Q) :
    |(∑ e ∈ R, sideWeight W Q S 0 e) - (∑ e ∈ R, sideWeight W Q S 1 e)| <
      15 * (fourthRoot α : ℝ) * q := by
  have hEmpty : branchMass P ∅ = 0 := Finset.sum_empty
  have hforest : (branchMass P (sideBranches P 0) : ℝ) +
      (branchMass P (sideBranches P 1) : ℝ) ≤ q := by
    simpa only [hEmpty, Nat.cast_zero, zero_add, Finset.sdiff_empty,
      show otherSide (0 : Fin 2) = 1 from rfl] using
      exceptional_mass_le P hcard 0 ∅ (Finset.empty_subset _)
  have hmajorNat : branchMass P (sideBranches P 1) ≤ branchMass P (sideBranches P 0) := by
    simpa only [sideBranches_zero, sideBranches_one] using
      Erdos547b.ZhaoClaim615SourceTotalMass.branchMass_minor_le_half P
  have hmajor : (branchMass P (sideBranches P 1) : ℝ) ≤ branchMass P (sideBranches P 0) := by
    exact_mod_cast hmajorNat
  have hhalf : (branchMass P (sideBranches P 1) : ℝ) ≤ (q : ℝ) / 2 := by
    linarith only [hforest, hmajor]
  obtain ⟨hδone, hδt, hfirst, hbudget, hroom, hlarge⟩ :=
    actual_raw_gates W hα hα1 hhost horder (branchMass P (sideBranches P 1)) hhalf
  have hq : (0 : ℝ) < q := by
    have hh := W.five_ordinaryParts_le_host
    have hp := W.ordinaryParts_pos
    have hqNat : 0 < q := by omega
    exact_mod_cast hqNat
  have ht : (0 : ℝ) < fourthRoot α := by exact_mod_cast (parameter_pos hα).2.2.2.1
  have hg : (0 : ℝ) ≤ gamma α := by exact_mod_cast (parameter_pos hα).2.2.2.2.2.2.1.le
  have hN : (0 : ℝ) < W.clusterSize := by exact_mod_cast W.clusterSize_pos
  have hfb : (0 : ℝ) < branchMass P (sideBranches P 1) := (mul_pos ht hq).trans_le hminor
  by_contra hdiscrepancy
  have hallocation := exists_allocation_or_swap_of_raw_discrepancy (awayEdges W Q) R
    (sideWeight W Q S 0) (sideWeight W Q S 1) q (10 * (fourthRoot α : ℝ) ^ 2)
    (fourthRoot α : ℝ) (branchMass P (sideBranches P 0)) (branchMass P (sideBranches P 1))
    (3 * (gamma α : ℝ) * q) (2 * W.clusterSize) hR
    (fun e _ => sideWeight_nonneg W Q S 0 e) (fun e _ => sideWeight_nonneg W Q S 1 e)
    (fun e _ => sideWeight_le W Q S 0 e) (fun e _ => sideWeight_le W Q S 1 e)
    (by positivity) hq (by positivity) hδone ht.le hδt hfb (by positivity)
    (awayWeight_lower W Q S hα hα1 hhost horder 0) (awayWeight_lower W Q S hα hα1 hhost horder 1)
    (le_of_not_gt hdiscrepancy) hminor hhalf hforest hfirst hbudget hroom hlarge
  exact hnot (exists_treeCopy_of_twoRowAllocationOrSwap W Q S hT P hα hα1 hhost horder
    hallocation hsmall hroots)

include hT in
theorem raw_discrepancy_lt_anySide
    (hα : 0 < α) (hα1 : α ≤ 1 / 4) (hhost : hostN = 2 * q)
    (horder : orderThreshold α M ≤ q) (hcard : Fintype.card U = q + 1)
    (hminor : (fourthRoot α : ℝ) * q ≤ (branchMass P (sideBranches P 1) : ℝ))
    (hsmall : ∀ i, (branchForest P).branches.size i ≤ freshBranchBound α W.clusterSize)
    (hroots : (P.numParts : ℝ) ≤ (epsilon α : ℝ) * W.clusterSize)
    (hnot : ¬Nonempty (T.Copy (embeddingHost W)))
    (s : Fin 2) (R : Finset (MatchingEdge Q.claim67.M)) (hR : R ⊆ awayEdges W Q) :
    |(∑ e ∈ R, sideWeight W Q S s e) - (∑ e ∈ R, sideWeight W Q S (otherSide s) e)| <
      15 * (fourthRoot α : ℝ) * q := by
  have h := raw_discrepancy_lt_of_not_copy W Q S hT P hα hα1 hhost horder hcard
    hminor hsmall hroots hnot R hR
  fin_cases s
  · exact h
  · change |(∑ e ∈ R, sideWeight W Q S 1 e) - (∑ e ∈ R, sideWeight W Q S 0 e)| < _
    rw [abs_sub_comm]
    exact h

end Erdos547b.ZhaoSourceRawDiscrepancy

#print axioms Erdos547b.ZhaoSourceRawDiscrepancy.raw_discrepancy_lt_of_not_copy
#print axioms Erdos547b.ZhaoSourceRawDiscrepancy.raw_discrepancy_lt_anySide
