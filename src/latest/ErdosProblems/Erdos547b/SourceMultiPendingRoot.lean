/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.SourcePendingRootSelection
import ErdosProblems.Erdos547b.SourcePendingInitialRoot

/-!
# Simultaneous actual root choice for up to three pending pairs

The concrete union of fixed-pair bad sets fits the existing reconnection
margin. One root then works for all active pending pairs, the opposite
root reservoir, and almost all unused pairs. The empty fixed set is allowed.
-/

open scoped SimpleGraph BigOperators Classical
noncomputable section

namespace Erdos547b.ZhaoSourceMultiPendingRoot

open Finset SimpleGraph
open Erdos547b.ZhaoStability Erdos547b.ZhaoDegreeForm Erdos547b.ZhaoEvenReducedPadding
open Erdos547b.ZhaoLemma611Full Erdos547b.ZhaoRichClaim61Lemma611
open Erdos547b.ZhaoSourceParameterSchedule Erdos547b.ZhaoSourceDegreeFormRootRows
open Erdos547b.ZhaoSourceEmbeddingHost Erdos547b.ZhaoSourceOnlineMatchingRoot
open Erdos547b.ZhaoSourceParentCleanup Erdos547b.ZhaoSourceRootReconnection
open Erdos547b.ZhaoSourceRootExclusions Erdos547b.ZhaoSourcePendingRootSelection
open Erdos547b.ZhaoSourcePendingInitialRoot

private theorem epsilon_le_rootTypicality {α : ℚ} (hα : 0 < α) (hα1 : α ≤ 1 / 4) :
    (epsilon α : ℝ) ≤ (rootTypicality α : ℝ) := by
  have hδ := rootTypicality_margin hα hα1
  have hσ := (reservoir_cleanup_bounds hα hα1).2.1
  have hδ1 : rootTypicality α ≤ 1 := by linarith only [hδ.2, hσ]
  have hp := mul_le_mul_of_nonneg_left hδ1 hδ.1.le
  have hs := rootTypicality_sq α
  have he : epsilon α ≤ rootTypicality α := by nlinarith only [hp, hs]
  exact_mod_cast he

variable {α : ℚ} {hostN q M : ℕ}
variable {G : SimpleGraph (Fin hostN)} [DecidableRel G.Adj]
variable (W : Witness α q M G) (Q : Certificate W)

def multiForbidden (S : CleanSourceWitness W Q) (s t : Fin 2)
    (fixed : Finset (MatchingEdge Q.claim67.M)) (used : Finset (Fin hostN)) : Finset (Fin hostN) :=
  used ∪ fixed.biUnion (badForEdge W Q S (rootCluster W Q s)) ∪
    badToward W Q (Sum.inl (rootCluster W Q s)) t

theorem card_multiForbidden_le (hα : 0 < α) (hα1 : α ≤ 1 / 4)
    (S : CleanSourceWitness W Q) (s t : Fin 2)
    (fixed : Finset (MatchingEdge Q.claim67.M))
    (hfixed : fixed ⊆ edgesAwayFromDistinguished Q.claim67.M (padFinset (large W))
      (Sum.inl Q.A) (Sum.inl Q.B)) (hcount : fixed.card ≤ 3)
    (used : Finset (Fin hostN)) (hused : (used.card : ℝ) ≤ (epsilon α : ℝ) * W.clusterSize) :
    ((multiForbidden W Q S s t fixed used).card : ℝ) ≤
      (3 * (rootTypicality α : ℝ) + 6 * (epsilon α : ℝ)) * W.clusterSize := by
  have hε : (0 : ℝ) ≤ epsilon α := by exact_mod_cast (parameter_pos hα).2.2.2.2.2.2.2.le
  have hN : (0 : ℝ) ≤ W.clusterSize := Nat.cast_nonneg _
  have hbi : ((fixed.biUnion (badForEdge W Q S (rootCluster W Q s))).card : ℝ) ≤
      (fixed.card : ℝ) * (2 * (epsilon α : ℝ) * W.clusterSize) := by
    calc
      _ ≤ ∑ e ∈ fixed, ((badForEdge W Q S (rootCluster W Q s) e).card : ℝ) := by
        exact_mod_cast Finset.card_biUnion_le
          (s := fixed) (t := badForEdge W Q S (rootCluster W Q s))
      _ ≤ ∑ _e ∈ fixed, 2 * (epsilon α : ℝ) * W.clusterSize := by
        apply Finset.sum_le_sum
        intro e he
        exact card_badForEdge_le W Q hα hα1 S _ (rootCluster_cases W Q s) e (hfixed he)
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
  have hcountR : (fixed.card : ℝ) ≤ 3 := by exact_mod_cast hcount
  have hbiSix : ((fixed.biUnion (badForEdge W Q S (rootCluster W Q s))).card : ℝ) ≤
      6 * (epsilon α : ℝ) * W.clusterSize := by
    have hh := mul_le_mul_of_nonneg_right hcountR (by positivity :
      (0 : ℝ) ≤ 2 * (epsilon α : ℝ) * W.clusterSize)
    nlinarith only [hbi, hh]
  have hr := card_badToward_le W Q hα hα1 (Sum.inl (rootCluster W Q s)) t
  have hc : (padCluster (clusterVertices (assignment W)) (Sum.inl (rootCluster W Q s))).card =
      W.clusterSize := by
    change (clusterVertices (assignment W) (rootCluster W Q s)).card = _
    rw [clusterVertices_partitionAssignment]
    exact W.equal_clusters _ (rootCluster W Q s).2
  rw [hc] at hr
  have hu : ((multiForbidden W Q S s t fixed used).card : ℝ) ≤ (used.card : ℝ) +
      ((fixed.biUnion (badForEdge W Q S (rootCluster W Q s))).card : ℝ) +
        (badToward W Q (Sum.inl (rootCluster W Q s)) t).card := by
    have h := Finset.card_union_le (used ∪ fixed.biUnion (badForEdge W Q S (rootCluster W Q s)))
      (badToward W Q (Sum.inl (rootCluster W Q s)) t)
    exact_mod_cast h.trans (Nat.add_le_add_right (Finset.card_union_le _ _) _)
  have heδ := mul_le_mul_of_nonneg_right (epsilon_le_rootTypicality hα hα1) hN
  have hδ : (0 : ℝ) ≤ rootTypicality α := by exact_mod_cast (rootTypicality_margin hα hα1).1.le
  have hδN := mul_nonneg hδ hN
  nlinarith only [hu, hused, hbiSix, hr, heδ, hδN]

/-- All fixed-pair constraints follow from avoiding the concrete union. -/
theorem fixed_eligible_of_not_mem_multiForbidden
    (S : CleanSourceWitness W Q) (s t : Fin 2)
    (fixed : Finset (MatchingEdge Q.claim67.M))
    (hfixed : fixed ⊆ edgesAwayFromDistinguished Q.claim67.M (padFinset (large W))
      (Sum.inl Q.A) (Sum.inl Q.B)) (used : Finset (Fin hostN))
    (z : Fin hostN) (hz : z ∈ reservoir W Q s)
    (hfresh : z ∉ multiForbidden W Q S s t fixed used) :
    ∀ e ∈ fixed, EligibleRoot W Q S (rootCluster W Q s) e z := by
  intro e he
  apply eligibleRoot_of_not_mem_badForEdge W Q S _ (rootCluster_cases W Q s)
    e (hfixed he) z (reservoir_subset W Q s hz)
  intro hbad
  apply hfresh
  exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨e, he, hbad⟩))

/-- The common-pool selector is independent of how that pool was obtained. -/
theorem exists_multi_eligible_from_pool
    (hα : 0 < α) (hα1 : α ≤ 1 / 4)
    (S : CleanSourceWitness W Q) (s t : Fin 2)
    (fixed : Finset (MatchingEdge Q.claim67.M))
    (hfixed : fixed ⊆ edgesAwayFromDistinguished Q.claim67.M (padFinset (large W))
      (Sum.inl Q.A) (Sum.inl Q.B)) (used : Finset (Fin hostN))
    (remaining : Finset (MatchingEdge Q.claim67.M))
    (hremaining : remaining ⊆ edgesAwayFromDistinguished Q.claim67.M (padFinset (large W))
      (Sum.inl Q.A) (Sum.inl Q.B))
    (pool : Finset (Fin hostN))
    (hpool : pool ⊆ reservoir W Q s \ multiForbidden W Q S s t fixed used)
    (hpoolCard : (rootTypicality α : ℝ) * W.clusterSize < pool.card) :
    ∃ z ∈ pool, z ∉ used ∧ (∀ e ∈ fixed, EligibleRoot W Q S (rootCluster W Q s) e z) ∧
      ((padGraph (reduced W)).Adj (Sum.inl (rootCluster W Q s)) (Sum.inl (rootCluster W Q t)) →
        ((densityCutoff α : ℝ) - (epsilon α : ℝ)) * (sourceQuota W : ℝ) ≤
          (#((reservoir W Q t).filter ((embeddingHost W).Adj z)) : ℝ)) ∧
      ∃ bad ⊆ remaining,
        (bad.card : ℝ) ≤ 2 * (rootTypicality α : ℝ) * remaining.card ∧
        ∀ e ∈ remaining \ bad, EligibleRoot W Q S (rootCluster W Q s) e z := by
  obtain ⟨z, hz, bad, hb, hcount, hgood⟩ := exists_eligible_root_most_edges
    W Q hα hα1 S (rootCluster W Q s) (rootCluster_cases W Q s) remaining hremaining pool
      (hpool.trans (Finset.sdiff_subset.trans (reservoir_subset W Q s))) hpoolCard
  obtain ⟨hzR, hzFresh⟩ := Finset.mem_sdiff.mp (hpool hz)
  have hnotUsed : z ∉ used := fun hu => hzFresh (Finset.mem_union_left _ (Finset.mem_union_left _ hu))
  have hnotReservoir : z ∉ badToward W Q (Sum.inl (rootCluster W Q s)) t :=
    fun hr => hzFresh (Finset.mem_union_right _ hr)
  refine ⟨z, hz, hnotUsed, fixed_eligible_of_not_mem_multiForbidden W Q S s t fixed hfixed
    used z hzR hzFresh, ?_, bad, hb, hcount, hgood⟩
  intro hadj
  exact degree_into_reservoir_of_not_mem_badToward W Q (Sum.inl (rootCluster W Q s))
    t z (reservoir_subset W Q s hzR) hnotReservoir hadj

/-- A cut-adjacent root works simultaneously on up to three active pairs. -/
theorem exists_multi_eligible_after_parent_degree
    (hα : 0 < α) (hα1 : α ≤ 1 / 4)
    (S : CleanSourceWitness W Q) (s t : Fin 2) (v : Fin hostN)
    (hdegree : ((densityCutoff α : ℝ) - (epsilon α : ℝ)) * (sourceQuota W : ℝ) ≤
      (#((reservoir W Q s).filter ((embeddingHost W).Adj v)) : ℝ))
    (fixed : Finset (MatchingEdge Q.claim67.M))
    (hfixed : fixed ⊆ edgesAwayFromDistinguished Q.claim67.M (padFinset (large W))
      (Sum.inl Q.A) (Sum.inl Q.B)) (hcount : fixed.card ≤ 3)
    (used : Finset (Fin hostN)) (hused : (used.card : ℝ) ≤ (epsilon α : ℝ) * W.clusterSize)
    (remaining : Finset (MatchingEdge Q.claim67.M))
    (hremaining : remaining ⊆ edgesAwayFromDistinguished Q.claim67.M (padFinset (large W))
      (Sum.inl Q.A) (Sum.inl Q.B)) :
    ∃ z ∈ reservoir W Q s, (embeddingHost W).Adj v z ∧ z ∉ used ∧
      (∀ e ∈ fixed, EligibleRoot W Q S (rootCluster W Q s) e z) ∧
      ((padGraph (reduced W)).Adj (Sum.inl (rootCluster W Q s)) (Sum.inl (rootCluster W Q t)) →
        ((densityCutoff α : ℝ) - (epsilon α : ℝ)) * (sourceQuota W : ℝ) ≤
          (#((reservoir W Q t).filter ((embeddingHost W).Adj z)) : ℝ)) ∧
      ∃ bad ⊆ remaining,
        (bad.card : ℝ) ≤ 2 * (rootTypicality α : ℝ) * remaining.card ∧
        ∀ e ∈ remaining \ bad, EligibleRoot W Q S (rootCluster W Q s) e z := by
  let excluded := multiForbidden W Q S s t fixed used
  obtain ⟨z, hz, hfresh, hfixedGood, hroot, hremainingGood⟩ := exists_multi_eligible_from_pool
    W Q hα hα1 S s t fixed hfixed used remaining hremaining (parentPool W Q s v excluded)
    (by intro z hz; obtain ⟨hm, _, hn⟩ := (mem_parentPool W Q).mp hz; exact Finset.mem_sdiff.mpr ⟨hm, hn⟩)
    (parentPool_large_of_degree W Q hα hα1 s v hdegree excluded
      (card_multiForbidden_le W Q hα hα1 S s t fixed hfixed hcount used hused))
  obtain ⟨hzR, hzAdj, _⟩ := (mem_parentPool W Q).mp hz
  exact ⟨z, hzR, hzAdj, hfresh, hfixedGood, hroot, hremainingGood⟩

/-- The initial root satisfies the same simultaneous constraints, without
any cut-parent premise. An empty fixed-edge set needs no arbitrary edge. -/
theorem exists_initial_multi_eligible_root
    (hα : 0 < α) (hα1 : α ≤ 1 / 4)
    (S : CleanSourceWitness W Q) (s t : Fin 2)
    (fixed : Finset (MatchingEdge Q.claim67.M))
    (hfixed : fixed ⊆ edgesAwayFromDistinguished Q.claim67.M (padFinset (large W))
      (Sum.inl Q.A) (Sum.inl Q.B)) (hcount : fixed.card ≤ 3)
    (used : Finset (Fin hostN)) (hused : (used.card : ℝ) ≤ (epsilon α : ℝ) * W.clusterSize)
    (remaining : Finset (MatchingEdge Q.claim67.M))
    (hremaining : remaining ⊆ edgesAwayFromDistinguished Q.claim67.M (padFinset (large W))
      (Sum.inl Q.A) (Sum.inl Q.B)) :
    ∃ z ∈ reservoir W Q s, z ∉ used ∧
      (∀ e ∈ fixed, EligibleRoot W Q S (rootCluster W Q s) e z) ∧
      ((padGraph (reduced W)).Adj (Sum.inl (rootCluster W Q s)) (Sum.inl (rootCluster W Q t)) →
        ((densityCutoff α : ℝ) - (epsilon α : ℝ)) * (sourceQuota W : ℝ) ≤
          (#((reservoir W Q t).filter ((embeddingHost W).Adj z)) : ℝ)) ∧
      ∃ bad ⊆ remaining,
        (bad.card : ℝ) ≤ 2 * (rootTypicality α : ℝ) * remaining.card ∧
        ∀ e ∈ remaining \ bad, EligibleRoot W Q S (rootCluster W Q s) e z := by
  let excluded := multiForbidden W Q S s t fixed used
  obtain ⟨z, hz, hfresh, hfixedGood, hroot, hremainingGood⟩ := exists_multi_eligible_from_pool
    W Q hα hα1 S s t fixed hfixed used remaining hremaining (reservoir W Q s \ excluded)
    (Finset.Subset.refl _)
    (initialPool_large W Q hα hα1 s excluded
      (card_multiForbidden_le W Q hα hα1 S s t fixed hfixed hcount used hused))
  exact ⟨z, (Finset.mem_sdiff.mp hz).1, hfresh, hfixedGood, hroot, hremainingGood⟩

end Erdos547b.ZhaoSourceMultiPendingRoot

#print axioms Erdos547b.ZhaoSourceMultiPendingRoot.card_multiForbidden_le
#print axioms Erdos547b.ZhaoSourceMultiPendingRoot.fixed_eligible_of_not_mem_multiForbidden
#print axioms Erdos547b.ZhaoSourceMultiPendingRoot.exists_multi_eligible_from_pool
#print axioms Erdos547b.ZhaoSourceMultiPendingRoot.exists_multi_eligible_after_parent_degree
#print axioms Erdos547b.ZhaoSourceMultiPendingRoot.exists_initial_multi_eligible_root
