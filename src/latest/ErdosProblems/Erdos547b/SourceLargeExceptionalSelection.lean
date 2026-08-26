/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.SourceExceptionalResidualTreeCopy

/-!
# Actual exceptional selection and complete embedding in the large case

Starting from a literal exceptional edge set, select the forest only after
its source row is known. The gain pays that selected forest, and the
residual source allocation constructs the rest of the tree. The remaining
input gates are exactly the source-mass and exceptional-gain inequalities.
-/

open scoped SimpleGraph BigOperators Classical
noncomputable section

namespace Erdos547b.ZhaoSourceLargeExceptionalSelection

open Finset SimpleGraph Erdos547b.TreePartition
open Erdos547b.ZhaoSourceExceptionalResidualTreeCopy Erdos547b.ZhaoSourceExceptionalFamilies
open Erdos547b.ZhaoSourceExceptionalIdealGains Erdos547b.ZhaoSourceExceptionalRowBounds
open Erdos547b.ZhaoSourceCapacityBudgetMargins Erdos547b.ZhaoSourceFamilyCapacity
open Erdos547b.ZhaoSourceDegreeFormRootRows Erdos547b.ZhaoSourceDegreeFormBounds
open Erdos547b.ZhaoSourceParameterSchedule Erdos547b.ZhaoSourceFreshChunkBounds
open Erdos547b.ZhaoSourceEmbeddingHost Erdos547b.ZhaoSourceParentCleanup
open Erdos547b.ZhaoSourceActualChunkEmbedding Erdos547b.ZhaoLemma611Full
open Erdos547b.ZhaoClaim617BranchCount Erdos547b.ZhaoClaim616SourceBridge
open Erdos547b.ZhaoClaim615SourceSelection Erdos547b.ZhaoSourceTwoSideFamilyAdvance

variable {α : ℚ} {hostN q M : ℕ}
variable {G : SimpleGraph (Fin hostN)} [DecidableRel G.Adj]
variable (W : Witness α q M G) (Q : Certificate W) (S : CleanSourceWitness W Q)
variable {U : Type*} [Fintype U] [DecidableEq U]
variable {T : SimpleGraph U} [DecidableRel T.Adj]
variable (hT : T.IsTree) {globalRoot : U} {small : ℕ}
variable (P : ZhaoForestPartition T globalRoot small)

include hT in
theorem exists_treeCopy_of_largeUnbalanced
    (hα : 0 < α) (hα1 : α ≤ 1 / 4) (hhost : hostN = 2 * q)
    (horder : orderThreshold α M ≤ q) (hcard : Fintype.card U = q + 1)
    (s : Fin 2) (ratio : ℝ) (hratio : 0 ≤ ratio) (hratio1 : ratio ≤ 1 / 2)
    (E0 : Finset (MatchingEdge Q.claim67.M)) (hE0 : E0 ⊆ awayEdges W Q)
    (hgap : ∀ e ∈ E0, (eta α : ℝ) ≤
      |rootDensity W S (Sum.inl (rootCluster W Q s)) (edgeVertex W Q e 1) -
        rootDensity W S (Sum.inl (rootCluster W Q s)) (edgeVertex W Q e 0)|)
    (hmass : (∑ e ∈ E0, sideWeight W Q S s e) + (eta α : ℝ) ^ 3 * q ≤
      (branchMass P (balancedSideBranches P s ratio) : ℝ))
    (hgain : (eta α : ℝ) ^ 3 * q + 1 + freshBranchBound α W.clusterSize +
      3 * (gamma α : ℝ) * q ≤ ratio * (eta α : ℝ) * W.clusterSize * E0.card)
    (hrows : ∀ R ⊆ awayEdges W Q,
      |(∑ e ∈ R, sideWeight W Q S s e) - (∑ e ∈ R, sideWeight W Q S (otherSide s) e)| ≤
        15 * (fourthRoot α : ℝ) * q)
    (hsmall : ∀ i, (branchForest P).branches.size i ≤ freshBranchBound α W.clusterSize)
    (hroots : (P.numParts : ℝ) ≤ (epsilon α : ℝ) * W.clusterSize) :
    Nonempty (T.Copy (embeddingHost W)) := by
  have heta : (0 : ℝ) ≤ eta α := by exact_mod_cast (parameter_pos hα).2.2.1.le
  have hslack : 0 < freshBranchBound α W.clusterSize := by
    subst hostN
    exact (degreeForm_fresh_chunk_gates hα hα1 W horder).1
  have hnonneg : 0 ≤ (∑ e ∈ E0, sideWeight W Q S s e) + (eta α : ℝ) ^ 3 * q :=
    add_nonneg (Finset.sum_nonneg (fun e _ => sideWeight_nonneg W Q S s e)) (by positivity)
  have hweight := threshold_idealGain_sum W Q S (rootCluster W Q s) ratio (eta α : ℝ)
    hratio hratio1 E0 hgap
  obtain ⟨F0, hbudget⟩ := exists_selectedF0_with_idealBudget W Q S (rootCluster W Q s) P
    (balancedSideBranches P s ratio) (eta α : ℝ) (freshBranchBound α W.clusterSize)
    (.threshold ratio) E0 hslack (fun i _ => hsmall i) hnonneg hmass
    (by linarith only [hgain, hweight])
  apply exists_treeCopy_of_largeExceptionalSaving W Q S hT P hα hα1 hhost horder hcard
    s F0.selected (F0.selected_available.trans (Finset.filter_subset _ _)) (.threshold ratio)
    ⟨hratio, hratio1⟩ (fun i hi => balancedSide_branchValid P s ratio i (F0.selected_available hi))
    E0 hE0 (fun _ _ => trivial) (selected_real_lower P F0)
  · simpa only [branchMass, Nat.cast_sum] using hbudget
  · exact hrows
  · exact hsmall
  · exact hroots

include hT in
theorem exists_treeCopy_of_largeNonextreme
    (hα : 0 < α) (hα1 : α ≤ 1 / 4) (hhost : hostN = 2 * q)
    (horder : orderThreshold α M ≤ q) (hcard : Fintype.card U = q + 1)
    (s : Fin 2) (E0 : Finset (MatchingEdge Q.claim67.M)) (hE0 : E0 ⊆ awayEdges W Q)
    (hedge : ∀ e ∈ E0, ∀ c, (eta α : ℝ) ≤
        rootDensity W S (Sum.inl (rootCluster W Q s)) (edgeVertex W Q e c) ∧
      rootDensity W S (Sum.inl (rootCluster W Q s)) (edgeVertex W Q e c) ≤ 1 - (eta α : ℝ))
    (hmass : (∑ e ∈ E0, sideWeight W Q S s e) + (eta α : ℝ) ^ 3 * q ≤
      (branchMass P (nontrivialSideBranches P s) : ℝ))
    (hgain : (eta α : ℝ) ^ 3 * q + 1 + freshBranchBound α W.clusterSize +
      3 * (gamma α : ℝ) * q ≤ (eta α : ℝ) * W.clusterSize * E0.card)
    (hrows : ∀ R ⊆ awayEdges W Q,
      |(∑ e ∈ R, sideWeight W Q S s e) - (∑ e ∈ R, sideWeight W Q S (otherSide s) e)| ≤
        15 * (fourthRoot α : ℝ) * q)
    (hsmall : ∀ i, (branchForest P).branches.size i ≤ freshBranchBound α W.clusterSize)
    (hroots : (P.numParts : ℝ) ≤ (epsilon α : ℝ) * W.clusterSize) :
    Nonempty (T.Copy (embeddingHost W)) := by
  have heta : (0 : ℝ) ≤ eta α := by exact_mod_cast (parameter_pos hα).2.2.1.le
  have hslack : 0 < freshBranchBound α W.clusterSize := by
    subst hostN
    exact (degreeForm_fresh_chunk_gates hα hα1 W horder).1
  have hnonneg : 0 ≤ (∑ e ∈ E0, sideWeight W Q S s e) + (eta α : ℝ) ^ 3 * q :=
    add_nonneg (Finset.sum_nonneg (fun e _ => sideWeight_nonneg W Q S s e)) (by positivity)
  have hweight := appendix_idealGain_sum W Q S (rootCluster W Q s) (eta α : ℝ) E0
  obtain ⟨F0, hbudget⟩ := exists_selectedF0_with_idealBudget W Q S (rootCluster W Q s) P
    (nontrivialSideBranches P s) (eta α : ℝ) (freshBranchBound α W.clusterSize)
    (.appendix (eta α : ℝ)) E0 hslack (fun i _ => hsmall i) hnonneg hmass
    (by linarith only [hgain, hweight])
  apply exists_treeCopy_of_largeExceptionalSaving W Q S hT P hα hα1 hhost horder hcard
    s F0.selected (F0.selected_available.trans (Finset.filter_subset _ _)) (.appendix (eta α : ℝ))
    (eta_appendix_valid hα hα1)
    (fun i hi => nontrivialSide_branchValid P s (eta α : ℝ) i (F0.selected_available hi))
    E0 hE0 hedge (selected_real_lower P F0)
  · simpa only [branchMass, Nat.cast_sum] using hbudget
  · exact hrows
  · exact hsmall
  · exact hroots

end Erdos547b.ZhaoSourceLargeExceptionalSelection

#print axioms Erdos547b.ZhaoSourceLargeExceptionalSelection.exists_treeCopy_of_largeUnbalanced
#print axioms Erdos547b.ZhaoSourceLargeExceptionalSelection.exists_treeCopy_of_largeNonextreme
