/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.SourceSmallExceptionalForcing
import ErdosProblems.Erdos547b.SourceBalancedForestMass

/-!
# Use the verified balanced source mass for the Appendix case

Balanced branches are nontrivial. Their smaller source mass already pays
the actual half-count target, and the Appendix gain is at least the
unbalanced gain. No Claim-6.8 mass estimate is needed for this step.
-/

open scoped SimpleGraph BigOperators Classical
noncomputable section

namespace Erdos547b.ZhaoSourceNonextremeBalancedForcing

open Finset SimpleGraph Erdos547b.TreePartition
open Erdos547b.ZhaoSourceSmallExceptionalForcing Erdos547b.ZhaoSourceBalancedForestMass
open Erdos547b.ZhaoSourceLargeExceptionalForcing Erdos547b.ZhaoSourceSmallReservation
open Erdos547b.ZhaoSourceExceptionalCountBounds Erdos547b.ZhaoSourceExceptionalIdealGains
open Erdos547b.ZhaoSourceExceptionalResidualTreeCopy Erdos547b.ZhaoSourceExceptionalFamilies
open Erdos547b.ZhaoSourceExceptionalRowBounds Erdos547b.ZhaoSourceCapacityBudgetMargins
open Erdos547b.ZhaoSourceFamilyCapacity Erdos547b.ZhaoSourceDegreeFormRootRows
open Erdos547b.ZhaoSourceDegreeFormBounds Erdos547b.ZhaoSourceParameterSchedule
open Erdos547b.ZhaoSourceFreshChunkBounds Erdos547b.ZhaoSourceEmbeddingHost
open Erdos547b.ZhaoSourceParentCleanup Erdos547b.ZhaoLemma611Full
open Erdos547b.ZhaoClaim617BranchCount Erdos547b.ZhaoClaim616SourceBridge
open Erdos547b.ZhaoClaim615SourceSelection Erdos547b.ZhaoClaim615SourceFamilyTarget
open Erdos547b.ZhaoSourceTwoSideFamilyAdvance Erdos547b.ZhaoEvenReducedPadding
open Erdos547b.ZhaoLemma615

variable {α : ℚ} {hostN q M : ℕ}
variable {G : SimpleGraph (Fin hostN)} [DecidableRel G.Adj]
variable (W : Witness α q M G) (Q : Certificate W) (S : CleanSourceWitness W Q)
variable {U : Type*} [Fintype U] [DecidableEq U]
variable {T : SimpleGraph U} [DecidableRel T.Adj]
variable (hT : T.IsTree) {globalRoot : U} {small : ℕ}
variable (P : ZhaoForestPartition T globalRoot small)

theorem exists_balancedSelection_with_appendixBudget
    (hα : 0 < α) (hα1 : α ≤ 1 / 4) (hhost : hostN = 2 * q)
    (horder : orderThreshold α M ≤ q) (s : Fin 2)
    (E0 : Finset (MatchingEdge Q.claim67.M)) (hcount : E0.card = exceptionalCount W)
    (hmass : (α : ℝ) / 32 * q ≤ (branchMass P (balancedSideBranches P s ((α : ℝ) / 16)) : ℝ))
    (hsmall : ∀ i, (branchForest P).branches.size i ≤ freshBranchBound α W.clusterSize) :
    ∃ F0 : SelectedF0 P (balancedSideBranches P s ((α : ℝ) / 16))
        (exceptionalForestTarget (∑ e ∈ E0, sideWeight W Q S s e) (eta α : ℝ) q)
        (freshBranchBound α W.clusterSize),
      (branchMass P F0.selected : ℝ) + 3 * (gamma α : ℝ) * q ≤
        ∑ e ∈ E0, idealCapacity W Q S (rootCluster W Q s) (.appendix (eta α : ℝ)) e := by
  have havailable := (actual_half_selection_gates W hα hα1 hhost horder).1
  have hgain := (actual_nonextreme_gates W hα hα1 hhost horder).2
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
  obtain ⟨F0, hbudget⟩ := exists_selectedF0_with_idealBudget W Q S (rootCluster W Q s) P
    (balancedSideBranches P s ((α : ℝ) / 16)) (eta α : ℝ) (freshBranchBound α W.clusterSize)
    (.appendix (eta α : ℝ)) E0 hslack (fun i _ => hsmall i) hnonneg
    (by linarith only [hweight, havailable, hmass]) (by linarith only [hgain, hcapacity])
  exact ⟨F0, by simpa only [branchMass, Nat.cast_sum] using hbudget⟩

include hT in
theorem exists_treeCopy_of_largeNonextremeBalanced
    (hα : 0 < α) (hα1 : α ≤ 1 / 4) (hhost : hostN = 2 * q)
    (horder : orderThreshold α M ≤ q) (hcard : Fintype.card U = q + 1) (s : Fin 2)
    (hfamily : (eta α : ℝ) * paddedHalf (Index W) ≤ (nonextremeAway W Q S s).card)
    (hmass : (α : ℝ) / 32 * q ≤ (branchMass P (balancedSideBranches P s ((α : ℝ) / 16)) : ℝ))
    (hrows : ∀ R ⊆ awayEdges W Q,
      |(∑ e ∈ R, sideWeight W Q S s e) - (∑ e ∈ R, sideWeight W Q S (otherSide s) e)| ≤
        15 * (fourthRoot α : ℝ) * q)
    (hsmall : ∀ i, (branchForest P).branches.size i ≤ freshBranchBound α W.clusterSize)
    (hroots : (P.numParts : ℝ) ≤ (epsilon α : ℝ) * W.clusterSize) :
    Nonempty (T.Copy (embeddingHost W)) := by
  obtain ⟨E0, hE0, hcount⟩ := exists_subset_exceptionalCount W hα (nonextremeAway W Q S s) hfamily
  obtain ⟨F0, hbudget⟩ := exists_balancedSelection_with_appendixBudget W Q S P hα hα1
    hhost horder s E0 hcount hmass hsmall
  have ha : (0 : ℝ) < α := by exact_mod_cast hα
  apply exists_treeCopy_of_largeExceptionalSaving W Q S hT P hα hα1 hhost horder hcard s
    F0.selected (F0.selected_available.trans (Finset.filter_subset _ _)) (.appendix (eta α : ℝ))
    (eta_appendix_valid hα hα1)
    (fun i hi => balancedSide_nontrivial P s ((α : ℝ) / 16) (by positivity) i (F0.selected_available hi))
    E0 (hE0.trans (nonextremeEdges_subset _ _ _))
  · intro e he c
    have h := (mem_nonextremeEdges.mp (hE0 he)).2
    fin_cases c
    · exact ⟨h.1, h.2.1⟩
    · exact h.2.2
  · exact selected_real_lower P F0
  · exact hbudget
  · exact hrows
  · exact hsmall
  · exact hroots

include hT in
theorem exists_treeCopy_of_smallNonextremeBalanced
    (hα : 0 < α) (hα1 : α ≤ 1 / 4) (hhost : hostN = 2 * q)
    (horder : orderThreshold α M ≤ q) (hcard : Fintype.card U = q + 1) (s : Fin 2)
    (hfamily : (eta α : ℝ) * paddedHalf (Index W) ≤ (nonextremeAway W Q S s).card)
    (hmass : (α : ℝ) / 32 * q ≤ (branchMass P (balancedSideBranches P s ((α : ℝ) / 16)) : ℝ))
    (hother : (branchMass P (sideBranches P (otherSide s)) : ℝ) ≤ (fourthRoot α : ℝ) * q)
    (hsmall : ∀ i, (branchForest P).branches.size i ≤ freshBranchBound α W.clusterSize)
    (hroots : (P.numParts : ℝ) ≤ (epsilon α : ℝ) * W.clusterSize) :
    Nonempty (T.Copy (embeddingHost W)) := by
  obtain ⟨Eb, hEb, hbudgetb, _hupperb, _hcountb, hhalf, hcost⟩ := exists_smallReservation W Q S
    hα hα1 hhost horder (otherSide s) (branchMass P (sideBranches P (otherSide s))) (Nat.cast_nonneg _) hother
  obtain ⟨E0, hE0, h0b, hcount⟩ := exists_subset_exceptionalCount_avoiding W hα
    (nonextremeAway W Q S s) Eb hfamily hhalf
  obtain ⟨F0, hbudget⟩ := exists_balancedSelection_with_appendixBudget W Q S P hα hα1
    hhost horder s E0 hcount hmass hsmall
  have ha : (0 : ℝ) < α := by exact_mod_cast hα
  apply exists_treeCopy_of_smallExceptionalSaving W Q S hT P hα hα1 hhost horder hcard s
    F0.selected (F0.selected_available.trans (Finset.filter_subset _ _)) (.appendix (eta α : ℝ))
    (eta_appendix_valid hα hα1)
    (fun i hi => balancedSide_nontrivial P s ((α : ℝ) / 16) (by positivity) i (F0.selected_available hi))
    E0 Eb (hE0.trans (nonextremeEdges_subset _ _ _)) hEb h0b
  · intro e he c
    have h := (mem_nonextremeEdges.mp (hE0 he)).2
    fin_cases c
    · exact ⟨h.1, h.2.1⟩
    · exact h.2.2
  · exact selected_real_lower P F0
  · exact hbudget
  · exact hbudgetb
  · exact hcost s
  · exact hsmall
  · exact hroots

end Erdos547b.ZhaoSourceNonextremeBalancedForcing

#print axioms Erdos547b.ZhaoSourceNonextremeBalancedForcing.exists_balancedSelection_with_appendixBudget
#print axioms Erdos547b.ZhaoSourceNonextremeBalancedForcing.exists_treeCopy_of_largeNonextremeBalanced
#print axioms Erdos547b.ZhaoSourceNonextremeBalancedForcing.exists_treeCopy_of_smallNonextremeBalanced
