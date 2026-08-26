/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.SourceLargeExceptionalSelection
import ErdosProblems.Erdos547b.SourceExceptionalCountBounds
import ErdosProblems.Erdos547b.Lemma615

/-!
# Large-case exceptional family forcing with actual selections

The exceptional matching is chosen from the paper's finite filters.
Its exact ceiling count supplies all selection and gain gates from the
actual source schedule. The remaining forest-mass and raw discrepancy
premises are the preceding source claims, not embedding callbacks.
-/

open scoped SimpleGraph BigOperators Classical
noncomputable section

namespace Erdos547b.ZhaoSourceLargeExceptionalForcing

open Finset SimpleGraph Erdos547b.TreePartition
open Erdos547b.ZhaoSourceLargeExceptionalSelection Erdos547b.ZhaoSourceExceptionalCountBounds
open Erdos547b.ZhaoSourceExceptionalFamilies Erdos547b.ZhaoSourceExceptionalRowBounds
open Erdos547b.ZhaoSourceDegreeFormRootRows Erdos547b.ZhaoSourceDegreeFormBounds
open Erdos547b.ZhaoSourceParameterSchedule Erdos547b.ZhaoSourceFreshChunkBounds
open Erdos547b.ZhaoSourceEmbeddingHost Erdos547b.ZhaoSourceParentCleanup
open Erdos547b.ZhaoSourceActualChunkEmbedding Erdos547b.ZhaoLemma611Full
open Erdos547b.ZhaoClaim617BranchCount Erdos547b.ZhaoClaim616SourceBridge
open Erdos547b.ZhaoClaim615SourceSelection Erdos547b.ZhaoSourceTwoSideFamilyAdvance
open Erdos547b.ZhaoEvenReducedPadding Erdos547b.ZhaoLemma615

variable {α : ℚ} {hostN q M : ℕ}
variable {G : SimpleGraph (Fin hostN)} [DecidableRel G.Adj]
variable (W : Witness α q M G) (Q : Certificate W) (S : CleanSourceWitness W Q)

abbrev sideDensity (s : Fin 2) (e : MatchingEdge Q.claim67.M) (c : Fin 2) :=
  rootDensity W S (Sum.inl (rootCluster W Q s)) (edgeVertex W Q e c)

abbrev unbalancedAway (s : Fin 2) :=
  unbalancedEdges (awayEdges W Q) (sideDensity W Q S s) (eta α : ℝ)

abbrev nonextremeAway (s : Fin 2) :=
  nonextremeEdges (awayEdges W Q) (sideDensity W Q S s) (eta α : ℝ)

theorem exists_subset_exceptionalCount {E : Type*} [DecidableEq E]
    (hα : 0 < α) (family : Finset E)
    (hlarge : (eta α : ℝ) * paddedHalf (Index W) ≤ family.card) :
    ∃ E0 ⊆ family, E0.card = exceptionalCount W := by
  apply Finset.exists_subset_card_eq
  apply Nat.ceil_le.mpr
  have heta : (0 : ℝ) ≤ eta α := by exact_mod_cast (parameter_pos hα).2.2.1.le
  have hprod : 0 ≤ (eta α : ℝ) * paddedHalf (Index W) := by positivity
  linarith only [hlarge, hprod]

theorem sideWeight_sum_le (s : Fin 2) (edges : Finset (MatchingEdge Q.claim67.M)) :
    (∑ e ∈ edges, sideWeight W Q S s e) ≤ 2 * (W.clusterSize : ℝ) * edges.card := by
  have h := Finset.sum_le_sum (fun e (_ : e ∈ edges) => sideWeight_le W Q S s e)
  simpa only [Finset.sum_const, nsmul_eq_mul, mul_comm (edges.card : ℝ)] using h

variable {U : Type*} [Fintype U] [DecidableEq U]
variable {T : SimpleGraph U} [DecidableRel T.Adj]
variable (hT : T.IsTree) {globalRoot : U} {small : ℕ}
variable (P : ZhaoForestPartition T globalRoot small)

include hT in
theorem exists_treeCopy_of_largeUnbalancedFamily
    (hα : 0 < α) (hα1 : α ≤ 1 / 4) (hhost : hostN = 2 * q)
    (horder : orderThreshold α M ≤ q) (hcard : Fintype.card U = q + 1)
    (s : Fin 2)
    (hfamily : (eta α : ℝ) * paddedHalf (Index W) ≤ (unbalancedAway W Q S s).card)
    (hmass : (α : ℝ) / 32 * q ≤ (branchMass P (balancedSideBranches P s ((α : ℝ) / 16)) : ℝ))
    (hrows : ∀ R ⊆ awayEdges W Q,
      |(∑ e ∈ R, sideWeight W Q S s e) - (∑ e ∈ R, sideWeight W Q S (otherSide s) e)| ≤
        15 * (fourthRoot α : ℝ) * q)
    (hsmall : ∀ i, (branchForest P).branches.size i ≤ freshBranchBound α W.clusterSize)
    (hroots : (P.numParts : ℝ) ≤ (epsilon α : ℝ) * W.clusterSize) :
    Nonempty (T.Copy (embeddingHost W)) := by
  obtain ⟨E0, hE0, hcount⟩ := exists_subset_exceptionalCount W hα (unbalancedAway W Q S s) hfamily
  obtain ⟨havailable, hgain⟩ := actual_half_selection_gates W hα hα1 hhost horder
  have hweight := sideWeight_sum_le W Q S s E0
  rw [hcount] at hweight
  have hαR : (0 : ℝ) < α := by exact_mod_cast hα
  have h4Q : 4 * α ≤ 1 := by linarith only [hα1]
  have h4R : (4 : ℝ) * (α : ℝ) ≤ 1 := by exact_mod_cast h4Q
  apply exists_treeCopy_of_largeUnbalanced W Q S hT P hα hα1 hhost horder hcard s
    ((α : ℝ) / 16) (by positivity) (by linarith only [h4R]) E0
    (hE0.trans (unbalancedEdges_subset _ _ _))
  · intro e he
    have hgap := (mem_unbalancedEdges.mp (hE0 he)).2
    change (eta α : ℝ) ≤ |sideDensity W Q S s e 1 - sideDensity W Q S s e 0|
    rw [abs_sub_comm]
    exact hgap
  · linarith only [hweight, havailable, hmass]
  · simpa only [hcount] using hgain
  · exact hrows
  · exact hsmall
  · exact hroots

include hT in
theorem exists_treeCopy_of_largeNonextremeFamily
    (hα : 0 < α) (hα1 : α ≤ 1 / 4) (hhost : hostN = 2 * q)
    (horder : orderThreshold α M ≤ q) (hcard : Fintype.card U = q + 1)
    (s : Fin 2)
    (hfamily : (eta α : ℝ) * paddedHalf (Index W) ≤ (nonextremeAway W Q S s).card)
    (hmass : (q : ℝ) / 2 - 12 * (fourthRoot α : ℝ) ^ 2 * q ≤
      (branchMass P (nontrivialSideBranches P s) : ℝ))
    (hrows : ∀ R ⊆ awayEdges W Q,
      |(∑ e ∈ R, sideWeight W Q S s e) - (∑ e ∈ R, sideWeight W Q S (otherSide s) e)| ≤
        15 * (fourthRoot α : ℝ) * q)
    (hsmall : ∀ i, (branchForest P).branches.size i ≤ freshBranchBound α W.clusterSize)
    (hroots : (P.numParts : ℝ) ≤ (epsilon α : ℝ) * W.clusterSize) :
    Nonempty (T.Copy (embeddingHost W)) := by
  obtain ⟨E0, hE0, hcount⟩ := exists_subset_exceptionalCount W hα (nonextremeAway W Q S s) hfamily
  obtain ⟨havailable, hgain⟩ := actual_nonextreme_gates W hα hα1 hhost horder
  have hweight := sideWeight_sum_le W Q S s E0
  rw [hcount] at hweight
  apply exists_treeCopy_of_largeNonextreme W Q S hT P hα hα1 hhost horder hcard s E0
    (hE0.trans (nonextremeEdges_subset _ _ _))
  · intro e he c
    have hedge := (mem_nonextremeEdges.mp (hE0 he)).2
    fin_cases c
    · exact ⟨hedge.1, hedge.2.1⟩
    · exact hedge.2.2
  · linarith only [hweight, havailable, hmass]
  · simpa only [hcount] using hgain
  · exact hrows
  · exact hsmall
  · exact hroots

end Erdos547b.ZhaoSourceLargeExceptionalForcing

#print axioms Erdos547b.ZhaoSourceLargeExceptionalForcing.exists_subset_exceptionalCount
#print axioms Erdos547b.ZhaoSourceLargeExceptionalForcing.exists_treeCopy_of_largeUnbalancedFamily
#print axioms Erdos547b.ZhaoSourceLargeExceptionalForcing.exists_treeCopy_of_largeNonextremeFamily
