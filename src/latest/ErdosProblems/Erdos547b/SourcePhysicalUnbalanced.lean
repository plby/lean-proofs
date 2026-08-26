/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.SourcePhysicalRowError
import ErdosProblems.Erdos547b.SourceMatchingGeometry
import ErdosProblems.Erdos547b.SourceLargeExceptionalForcing

/-! # Charge physical row discrepancies to source discrepancies and bad targets -/

open scoped SimpleGraph Classical
noncomputable section

namespace Erdos547b.ZhaoSourcePhysicalUnbalanced

open Finset SimpleGraph Erdos547b.ZhaoStability Erdos547b.ZhaoLemma615
open Erdos547b.ZhaoLemma611Full Erdos547b.ZhaoClaim616
open Erdos547b.ZhaoSourceDegreeFormRootRows Erdos547b.ZhaoSourceParameterSchedule
open Erdos547b.ZhaoSourceTwoSidedRows Erdos547b.ZhaoSourceThresholdGraphs
open Erdos547b.ZhaoSourcePhysicalRowError Erdos547b.ZhaoSourceMatchingGeometry
open Erdos547b.ZhaoRichClaim61Lemma611 Erdos547b.ZhaoEvenReducedPadding
open Erdos547b.ZhaoSourceLargeExceptionalForcing

theorem unbalanced_card_le_source_add_bad
    {K : Type*} [Fintype K] [DecidableEq K]
    {R : SimpleGraph K} [DecidableRel R.Adj]
    (M : R.Subgraph) (hM : M.IsMatching) (L B : Finset K)
    (physical source : K → ℝ) (ε η : ℝ) (hε : 2 * ε ≤ η)
    (herror : ∀ e : MatchingEdge M, ∀ c : Fin 2,
      orientedEndpoint M L e c ∉ B →
        |source (orientedEndpoint M L e c) - physical (orientedEndpoint M L e c)| ≤ ε) :
    (unbalancedEdges (allMatchingEdges M) (fun e c => physical (orientedEndpoint M L e c))
      (2 * η)).card ≤
    (unbalancedEdges (allMatchingEdges M) (fun e c => source (orientedEndpoint M L e c)) η).card +
      B.card := by
  let Bad := incidentCoverEdges M L B
  have hsub : unbalancedEdges (allMatchingEdges M)
      (fun e c => physical (orientedEndpoint M L e c)) (2 * η) ⊆
      unbalancedEdges (allMatchingEdges M) (fun e c => source (orientedEndpoint M L e c)) η ∪ Bad := by
    intro e he
    by_cases hb : e ∈ Bad
    · exact Finset.mem_union_right _ hb
    · have hn : orientedEndpoint M L e 0 ∉ B ∧ orientedEndpoint M L e 1 ∉ B := by
        simpa only [Bad, incidentCoverEdges, Finset.mem_filter, mem_allMatchingEdges,
          true_and, not_or] using hb
      apply Finset.mem_union_left
      apply mem_unbalancedEdges.mpr
      refine ⟨(mem_unbalancedEdges.mp he).1, ?_⟩
      exact source_gap_of_physical_gap (herror e 0 hn.1) (herror e 1 hn.2) hε
        (mem_unbalancedEdges.mp he).2
  exact (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans
    (Nat.add_le_add_left (incidentCoverEdges_card_le M hM L B) _))

variable {α : ℚ} {hostN q M : ℕ}
variable {G : SimpleGraph (Fin hostN)} [DecidableRel G.Adj]
variable (W : Witness α q M G) (Q : Certificate W) (S : TwoSidedSource W Q)

def physicalUnbalanced (C : EvenPadding (Index W)) : Finset (MatchingEdge Q.claim67.M) :=
  unbalancedEdges (allMatchingEdges Q.claim67.M)
    (fun e c => density W C (orientedEndpoint Q.claim67.M (padFinset (large W)) e c))
    (2 * (eta α : ℝ))

theorem physicalUnbalanced_A_card_le (hα : 0 < α)
    (hε : 2 * (epsilon α : ℝ) ≤ eta α) :
    ((physicalUnbalanced W Q (Sum.inl Q.A)).card : ℝ) ≤
      (unbalancedAway W Q S.clean 0).card +
        2 * (rootTypicality α : ℝ) * Fintype.card (Index W) + 4 := by
  let B : Finset (EvenPadding (Index W)) := padFinset S.badA ∪ {Sum.inl Q.A, Sum.inl Q.B}
  have herror (e : MatchingEdge Q.claim67.M) (c : Fin 2)
      (he : orientedEndpoint Q.claim67.M (padFinset (large W)) e c ∉ B) :
      |rootDensity W S.clean (Sum.inl Q.A)
          (orientedEndpoint Q.claim67.M (padFinset (large W)) e c) -
        density W (Sum.inl Q.A) (orientedEndpoint Q.claim67.M (padFinset (large W)) e c)| ≤
          (epsilon α : ℝ) := by
    obtain ⟨j, hj⟩ := pairVertex_real W Q.claim67.M e c
    change orientedEndpoint Q.claim67.M (padFinset (large W)) e c = Sum.inl j at hj
    rw [hj] at he ⊢
    have hjnot : j ∉ S.badA ∧ j ≠ Q.A ∧ j ≠ Q.B := by
      simpa only [B, Finset.mem_union, mem_padFinset_inl, Finset.mem_insert,
        Finset.mem_singleton, Sum.inl.injEq, not_or] using he
    exact source_density_error_A W Q S hα hjnot.2.1 hjnot.2.2 hjnot.1
  have htransfer := unbalanced_card_le_source_add_bad Q.claim67.M Q.claim67.isMatching
    (padFinset (large W)) B (density W (Sum.inl Q.A)) (rootDensity W S.clean (Sum.inl Q.A))
    (epsilon α : ℝ) (eta α : ℝ) hε herror
  have hsource := unbalanced_all_card_le_away_add_two Q.claim67 (Sum.inl Q.A) (Sum.inl Q.B)
    (rootDensity W S.clean) (eta α : ℝ)
  have hB : B.card ≤ S.badA.card + 2 := by
    exact (Finset.card_union_le _ _).trans (by
      rw [card_padFinset]
      exact Nat.add_le_add_left Finset.card_le_two _)
  have hcard : (physicalUnbalanced W Q (Sum.inl Q.A)).card ≤
      (unbalancedAway W Q S.clean 0).card + S.badA.card + 4 := by
    change (physicalUnbalanced W Q (Sum.inl Q.A)).card ≤ _ at htransfer
    change (physicalUnbalanced W Q (Sum.inl Q.A)).card ≤
      (unbalancedEdges (allMatchingEdges Q.claim67.M)
        (sideDensity W Q S.clean 0) (eta α : ℝ)).card + B.card at htransfer
    change (unbalancedEdges (allMatchingEdges Q.claim67.M)
      (sideDensity W Q S.clean 0) (eta α : ℝ)).card ≤
        (unbalancedAway W Q S.clean 0).card + 2 at hsource
    omega
  have hcardR : ((physicalUnbalanced W Q (Sum.inl Q.A)).card : ℝ) ≤
      (unbalancedAway W Q S.clean 0).card + S.badA.card + 4 := by exact_mod_cast hcard
  linarith only [hcardR, S.badA_card]

end Erdos547b.ZhaoSourcePhysicalUnbalanced

#print axioms Erdos547b.ZhaoSourcePhysicalUnbalanced.unbalanced_card_le_source_add_bad
#print axioms Erdos547b.ZhaoSourcePhysicalUnbalanced.physicalUnbalanced_A_card_le
