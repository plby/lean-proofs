/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.SourceLargeExceptionalForcing
import ErdosProblems.Erdos547b.SourceSmallReservation

/-!
# Actual exceptional forcing in the small opposite-family case

Choose the opposite-family reservation first, then select exceptional
edges avoiding it. The source target depends on that actual exceptional
selection. Both concrete gains and all source budgets are discharged.
-/

open scoped SimpleGraph BigOperators Classical
noncomputable section

namespace Erdos547b.ZhaoSourceSmallExceptionalForcing

open Finset SimpleGraph Erdos547b.TreePartition
open Erdos547b.ZhaoSourceLargeExceptionalForcing Erdos547b.ZhaoSourceSmallReservation
open Erdos547b.ZhaoSourceExceptionalCountBounds Erdos547b.ZhaoSourceExceptionalIdealGains
open Erdos547b.ZhaoSourceExceptionalResidualTreeCopy Erdos547b.ZhaoSourceExceptionalFamilies
open Erdos547b.ZhaoSourceExceptionalRowBounds Erdos547b.ZhaoSourceCapacityBudgetMargins
open Erdos547b.ZhaoSourceFamilyCapacity Erdos547b.ZhaoSourceDegreeFormRootRows
open Erdos547b.ZhaoSourceDegreeFormBounds Erdos547b.ZhaoSourceParameterSchedule
open Erdos547b.ZhaoSourceFreshChunkBounds Erdos547b.ZhaoSourceEmbeddingHost
open Erdos547b.ZhaoSourceParentCleanup Erdos547b.ZhaoSourceActualChunkEmbedding
open Erdos547b.ZhaoLemma611Full Erdos547b.ZhaoClaim617BranchCount
open Erdos547b.ZhaoClaim616SourceBridge Erdos547b.ZhaoClaim615SourceSelection
open Erdos547b.ZhaoSourceTwoSideFamilyAdvance Erdos547b.ZhaoEvenReducedPadding
open Erdos547b.ZhaoLemma615

variable {α : ℚ} {hostN q M : ℕ}
variable {G : SimpleGraph (Fin hostN)} [DecidableRel G.Adj]
variable (W : Witness α q M G) (Q : Certificate W) (S : CleanSourceWitness W Q)

theorem exists_subset_exceptionalCount_avoiding {E : Type*} [DecidableEq E]
    (hα : 0 < α) (family forbidden : Finset E)
    (hlarge : (eta α : ℝ) * paddedHalf (Index W) ≤ family.card)
    (hforbidden : (forbidden.card : ℝ) ≤ (eta α : ℝ) * paddedHalf (Index W) / 2) :
    ∃ E0 ⊆ family, Disjoint E0 forbidden ∧ E0.card = exceptionalCount W := by
  have heta : (0 : ℝ) ≤ eta α := by exact_mod_cast (parameter_pos hα).2.2.1.le
  have hceil : (exceptionalCount W : ℝ) < (eta α : ℝ) * paddedHalf (Index W) / 2 + 1 :=
    Nat.ceil_lt_add_one (by positivity)
  have hroomR : ((exceptionalCount W + forbidden.card : ℕ) : ℝ) < (family.card + 1 : ℕ) := by
    push_cast
    linarith only [hceil, hlarge, hforbidden]
  have hroom : exceptionalCount W + forbidden.card < family.card + 1 := by exact_mod_cast hroomR
  have hinter : (family ∩ forbidden).card ≤ forbidden.card := Finset.card_le_card Finset.inter_subset_right
  have hsplit := Finset.card_sdiff_add_card_inter family forbidden
  have hcount : exceptionalCount W ≤ (family \ forbidden).card := by omega
  obtain ⟨E0, hE0, hE0card⟩ := Finset.exists_subset_card_eq hcount
  refine ⟨E0, hE0.trans Finset.sdiff_subset, ?_, hE0card⟩
  rw [Finset.disjoint_left]
  intro e he hf
  exact (Finset.mem_sdiff.mp (hE0 he)).2 hf

variable {U : Type*} [Fintype U] [DecidableEq U]
variable {T : SimpleGraph U} [DecidableRel T.Adj]
variable (hT : T.IsTree) {globalRoot : U} {small : ℕ}
variable (P : ZhaoForestPartition T globalRoot small)

include hT in
theorem exists_treeCopy_of_smallUnbalancedFamily
    (hα : 0 < α) (hα1 : α ≤ 1 / 4) (hhost : hostN = 2 * q)
    (horder : orderThreshold α M ≤ q) (hcard : Fintype.card U = q + 1) (s : Fin 2)
    (hfamily : (eta α : ℝ) * paddedHalf (Index W) ≤ (unbalancedAway W Q S s).card)
    (hmass : (α : ℝ) / 32 * q ≤ (branchMass P (balancedSideBranches P s ((α : ℝ) / 16)) : ℝ))
    (hother : (branchMass P (sideBranches P (otherSide s)) : ℝ) ≤ (fourthRoot α : ℝ) * q)
    (hsmall : ∀ i, (branchForest P).branches.size i ≤ freshBranchBound α W.clusterSize)
    (hroots : (P.numParts : ℝ) ≤ (epsilon α : ℝ) * W.clusterSize) :
    Nonempty (T.Copy (embeddingHost W)) := by
  obtain ⟨Eb, hEb, hbudgetb, _hupperb, _hcountb, hhalf, hcost⟩ := exists_smallReservation W Q S
    hα hα1 hhost horder (otherSide s) (branchMass P (sideBranches P (otherSide s))) (Nat.cast_nonneg _) hother
  obtain ⟨E0, hE0, h0b, hcount⟩ := exists_subset_exceptionalCount_avoiding W hα
    (unbalancedAway W Q S s) Eb hfamily hhalf
  obtain ⟨havailable, hgain⟩ := actual_half_selection_gates W hα hα1 hhost horder
  have hweight := sideWeight_sum_le W Q S s E0
  rw [hcount] at hweight
  have ha : (0 : ℝ) < α := by exact_mod_cast hα
  have ha4Q : 4 * α ≤ 1 := by linarith only [hα1]
  have ha4 : (4 : ℝ) * (α : ℝ) ≤ 1 := by exact_mod_cast ha4Q
  have hr0 : 0 ≤ (α : ℝ) / 16 := by positivity
  have hr1 : (α : ℝ) / 16 ≤ 1 / 2 := by linarith only [ha4]
  have heta : (0 : ℝ) ≤ eta α := by exact_mod_cast (parameter_pos hα).2.2.1.le
  have hslack : 0 < freshBranchBound α W.clusterSize := by
    subst hostN
    exact (degreeForm_fresh_chunk_gates hα hα1 W horder).1
  have hnonneg : 0 ≤ (∑ e ∈ E0, sideWeight W Q S s e) + (eta α : ℝ) ^ 3 * q :=
    add_nonneg (Finset.sum_nonneg (fun e _ => sideWeight_nonneg W Q S s e)) (by positivity)
  have hgap : ∀ e ∈ E0, (eta α : ℝ) ≤
      |rootDensity W S (Sum.inl (rootCluster W Q s)) (edgeVertex W Q e 1) -
        rootDensity W S (Sum.inl (rootCluster W Q s)) (edgeVertex W Q e 0)| := by
    intro e he
    change (eta α : ℝ) ≤ |sideDensity W Q S s e 1 - sideDensity W Q S s e 0|
    rw [abs_sub_comm]
    exact (mem_unbalancedEdges.mp (hE0 he)).2
  have hcapacity := threshold_idealGain_sum W Q S (rootCluster W Q s) ((α : ℝ) / 16)
    (eta α : ℝ) hr0 hr1 E0 hgap
  rw [hcount] at hcapacity
  obtain ⟨F0, hbudget0⟩ := exists_selectedF0_with_idealBudget W Q S (rootCluster W Q s) P
    (balancedSideBranches P s ((α : ℝ) / 16)) (eta α : ℝ) (freshBranchBound α W.clusterSize)
    (.threshold ((α : ℝ) / 16)) E0 hslack (fun i _ => hsmall i) hnonneg
    (by linarith only [hweight, havailable, hmass]) (by linarith only [hgain, hcapacity])
  apply exists_treeCopy_of_smallExceptionalSaving W Q S hT P hα hα1 hhost horder hcard s
    F0.selected (F0.selected_available.trans (Finset.filter_subset _ _)) (.threshold ((α : ℝ) / 16))
    ⟨hr0, hr1⟩ (fun i hi => balancedSide_branchValid P s ((α : ℝ) / 16) i (F0.selected_available hi))
    E0 Eb (hE0.trans (unbalancedEdges_subset _ _ _)) hEb h0b (fun _ _ => trivial)
    (selected_real_lower P F0)
  · simpa only [branchMass, Nat.cast_sum] using hbudget0
  · exact hbudgetb
  · exact hcost s
  · exact hsmall
  · exact hroots

include hT in
theorem exists_treeCopy_of_smallNonextremeFamily
    (hα : 0 < α) (hα1 : α ≤ 1 / 4) (hhost : hostN = 2 * q)
    (horder : orderThreshold α M ≤ q) (hcard : Fintype.card U = q + 1) (s : Fin 2)
    (hfamily : (eta α : ℝ) * paddedHalf (Index W) ≤ (nonextremeAway W Q S s).card)
    (hmass : (q : ℝ) / 2 - 12 * (fourthRoot α : ℝ) ^ 2 * q ≤
      (branchMass P (nontrivialSideBranches P s) : ℝ))
    (hother : (branchMass P (sideBranches P (otherSide s)) : ℝ) ≤ (fourthRoot α : ℝ) * q)
    (hsmall : ∀ i, (branchForest P).branches.size i ≤ freshBranchBound α W.clusterSize)
    (hroots : (P.numParts : ℝ) ≤ (epsilon α : ℝ) * W.clusterSize) :
    Nonempty (T.Copy (embeddingHost W)) := by
  obtain ⟨Eb, hEb, hbudgetb, _hupperb, _hcountb, hhalf, hcost⟩ := exists_smallReservation W Q S
    hα hα1 hhost horder (otherSide s) (branchMass P (sideBranches P (otherSide s))) (Nat.cast_nonneg _) hother
  obtain ⟨E0, hE0, h0b, hcount⟩ := exists_subset_exceptionalCount_avoiding W hα
    (nonextremeAway W Q S s) Eb hfamily hhalf
  obtain ⟨havailable, hgain⟩ := actual_nonextreme_gates W hα hα1 hhost horder
  have hweight := sideWeight_sum_le W Q S s E0
  rw [hcount] at hweight
  have heta : (0 : ℝ) ≤ eta α := by exact_mod_cast (parameter_pos hα).2.2.1.le
  have hslack : 0 < freshBranchBound α W.clusterSize := by
    subst hostN
    exact (degreeForm_fresh_chunk_gates hα hα1 W horder).1
  have hnonneg : 0 ≤ (∑ e ∈ E0, sideWeight W Q S s e) + (eta α : ℝ) ^ 3 * q :=
    add_nonneg (Finset.sum_nonneg (fun e _ => sideWeight_nonneg W Q S s e)) (by positivity)
  have hcapacity := appendix_idealGain_sum W Q S (rootCluster W Q s) (eta α : ℝ) E0
  rw [hcount] at hcapacity
  obtain ⟨F0, hbudget0⟩ := exists_selectedF0_with_idealBudget W Q S (rootCluster W Q s) P
    (nontrivialSideBranches P s) (eta α : ℝ) (freshBranchBound α W.clusterSize)
    (.appendix (eta α : ℝ)) E0 hslack (fun i _ => hsmall i) hnonneg
    (by linarith only [hweight, havailable, hmass]) (by linarith only [hgain, hcapacity])
  apply exists_treeCopy_of_smallExceptionalSaving W Q S hT P hα hα1 hhost horder hcard s
    F0.selected (F0.selected_available.trans (Finset.filter_subset _ _)) (.appendix (eta α : ℝ))
    (eta_appendix_valid hα hα1)
    (fun i hi => nontrivialSide_branchValid P s (eta α : ℝ) i (F0.selected_available hi))
    E0 Eb (hE0.trans (nonextremeEdges_subset _ _ _)) hEb h0b
  · intro e he c
    have h := (mem_nonextremeEdges.mp (hE0 he)).2
    fin_cases c
    · exact ⟨h.1, h.2.1⟩
    · exact h.2.2
  · exact selected_real_lower P F0
  · simpa only [branchMass, Nat.cast_sum] using hbudget0
  · exact hbudgetb
  · exact hcost s
  · exact hsmall
  · exact hroots

end Erdos547b.ZhaoSourceSmallExceptionalForcing

#print axioms Erdos547b.ZhaoSourceSmallExceptionalForcing.exists_subset_exceptionalCount_avoiding
#print axioms Erdos547b.ZhaoSourceSmallExceptionalForcing.exists_treeCopy_of_smallUnbalancedFamily
#print axioms Erdos547b.ZhaoSourceSmallExceptionalForcing.exists_treeCopy_of_smallNonextremeFamily
