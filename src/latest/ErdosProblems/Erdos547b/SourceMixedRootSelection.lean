/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.SourceMixedRootRequirements

/-!
# One actual root for mixed threshold and Appendix families

The same chosen root obeys all concrete active requirements, is fresh and
cut-adjacent when needed, retains its opposite-reservoir degree, and works
on the designated targets of almost all unused matching edges.
-/

open scoped SimpleGraph Classical
noncomputable section

namespace Erdos547b.ZhaoSourceMixedRootSelection

open Finset SimpleGraph
open Erdos547b.ZhaoStability Erdos547b.ZhaoDegreeForm Erdos547b.ZhaoEvenReducedPadding
open Erdos547b.ZhaoLemma611Full Erdos547b.ZhaoRichClaim61Lemma611
open Erdos547b.ZhaoSourceParameterSchedule Erdos547b.ZhaoSourceDegreeFormRootRows
open Erdos547b.ZhaoSourceEmbeddingHost Erdos547b.ZhaoSourceActualChunkEmbedding
open Erdos547b.ZhaoSourceActualPartThreeStep Erdos547b.ZhaoSourceParentCleanup
open Erdos547b.ZhaoSourceRootReconnection Erdos547b.ZhaoSourceRootExclusions
open Erdos547b.ZhaoSourcePendingRootSelection Erdos547b.ZhaoSourcePendingInitialRoot
open Erdos547b.ZhaoSourceLiveMatchingRoot Erdos547b.ZhaoSourceMixedRootRequirements

variable {α : ℚ} {hostN q M : ℕ}
variable {G : SimpleGraph (Fin hostN)} [DecidableRel G.Adj]
variable (W : Witness α q M G) (Q : Certificate W)

/-- The incidence choice preserves every already imposed concrete pending
constraint, independently of how the eligible root pool was obtained. -/
theorem exists_mixed_root_from_pool
    (hα : 0 < α) (hα1 : α ≤ 1 / 4)
    (S : CleanSourceWitness W Q) (s t : Fin 2) {k : ℕ}
    (requirements : Fin k → Requirement W Q)
    (hvalid : ∀ j, requirementValid W Q S (rootCluster W Q s) (requirements j))
    (used : Finset (Fin hostN)) (remaining : Finset (MatchingEdge Q.claim67.M))
    (hremaining : remaining ⊆ edgesAwayFromDistinguished Q.claim67.M (padFinset (large W))
      (Sum.inl Q.A) (Sum.inl Q.B))
    (raw : MatchingEdge Q.claim67.M → Fin 2 → Finset (Fin hostN))
    (hraw : ∀ e ∈ remaining, ∀ c, raw e c ⊆ edgeWhole W Q e c)
    (hrawLarge : ∀ e ∈ remaining, ∀ c, (epsilon α : ℝ) * W.clusterSize ≤ (raw e c).card)
    (pool : Finset (Fin hostN))
    (hpool : pool ⊆ reservoir W Q s \ mixedForbidden W Q S s t requirements used)
    (hpoolCard : (rootTypicality α : ℝ) * W.clusterSize < pool.card) :
    ∃ z ∈ pool, z ∉ used ∧
      (∀ j, requirementGood W Q S (rootCluster W Q s) (requirements j) z) ∧
      ((padGraph (reduced W)).Adj (Sum.inl (rootCluster W Q s)) (Sum.inl (rootCluster W Q t)) →
        ((densityCutoff α : ℝ) - (epsilon α : ℝ)) * (sourceQuota W : ℝ) ≤
          (#((reservoir W Q t).filter ((embeddingHost W).Adj z)) : ℝ)) ∧
      ∃ bad ⊆ remaining, (bad.card : ℝ) ≤ 2 * (rootTypicality α : ℝ) * remaining.card ∧
        ∀ e ∈ remaining \ bad, EligibleLiveRoot W Q S (rootCluster W Q s) e (raw e) z := by
  obtain ⟨z, hz, bad, hb, hcount, hgood⟩ := exists_live_eligible_root_most_edges W Q hα hα1 S
    (rootCluster W Q s) (rootCluster_cases W Q s) remaining hremaining raw hraw hrawLarge pool
    (hpool.trans (Finset.sdiff_subset.trans (reservoir_subset W Q s))) hpoolCard
  obtain ⟨hzR, hzFresh⟩ := Finset.mem_sdiff.mp (hpool hz)
  have hnotUsed : z ∉ used := fun hu => hzFresh (Finset.mem_union_left _ (Finset.mem_union_left _ hu))
  have hnotReservoir : z ∉ badToward W Q (Sum.inl (rootCluster W Q s)) t :=
    fun hr => hzFresh (Finset.mem_union_right _ hr)
  refine ⟨z, hz, hnotUsed,
    requirements_good_of_not_mem_mixedForbidden W Q S s t requirements hvalid used z hzR hzFresh,
    ?_, bad, hb, hcount, hgood⟩
  intro hadj
  exact degree_into_reservoir_of_not_mem_badToward W Q (Sum.inl (rootCluster W Q s))
    t z (reservoir_subset W Q s hzR) hnotReservoir hadj

/-- A previously embedded cut parent supplies the current root pool.
The mixed pending exclusions fit the same checked source margin. -/
theorem exists_mixed_root_after_parent_degree
    (hα : 0 < α) (hα1 : α ≤ 1 / 4)
    (S : CleanSourceWitness W Q) (s t : Fin 2) (v : Fin hostN)
    (hdegree : ((densityCutoff α : ℝ) - (epsilon α : ℝ)) * (sourceQuota W : ℝ) ≤
      (#((reservoir W Q s).filter ((embeddingHost W).Adj v)) : ℝ))
    {k : ℕ} (hk : k ≤ 3) (requirements : Fin k → Requirement W Q)
    (hvalid : ∀ j, requirementValid W Q S (rootCluster W Q s) (requirements j))
    (used : Finset (Fin hostN)) (hused : (used.card : ℝ) ≤ (epsilon α : ℝ) * W.clusterSize)
    (remaining : Finset (MatchingEdge Q.claim67.M))
    (hremaining : remaining ⊆ edgesAwayFromDistinguished Q.claim67.M (padFinset (large W))
      (Sum.inl Q.A) (Sum.inl Q.B))
    (raw : MatchingEdge Q.claim67.M → Fin 2 → Finset (Fin hostN))
    (hraw : ∀ e ∈ remaining, ∀ c, raw e c ⊆ edgeWhole W Q e c)
    (hrawLarge : ∀ e ∈ remaining, ∀ c, (epsilon α : ℝ) * W.clusterSize ≤ (raw e c).card) :
    ∃ z ∈ reservoir W Q s, (embeddingHost W).Adj v z ∧ z ∉ used ∧
      (∀ j, requirementGood W Q S (rootCluster W Q s) (requirements j) z) ∧
      ((padGraph (reduced W)).Adj (Sum.inl (rootCluster W Q s)) (Sum.inl (rootCluster W Q t)) →
        ((densityCutoff α : ℝ) - (epsilon α : ℝ)) * (sourceQuota W : ℝ) ≤
          (#((reservoir W Q t).filter ((embeddingHost W).Adj z)) : ℝ)) ∧
      ∃ bad ⊆ remaining, (bad.card : ℝ) ≤ 2 * (rootTypicality α : ℝ) * remaining.card ∧
        ∀ e ∈ remaining \ bad, EligibleLiveRoot W Q S (rootCluster W Q s) e (raw e) z := by
  let excluded := mixedForbidden W Q S s t requirements used
  obtain ⟨z, hz, hfresh, hfixed, hroot, hremainingGood⟩ := exists_mixed_root_from_pool W Q hα hα1
    S s t requirements hvalid used remaining hremaining raw hraw hrawLarge (parentPool W Q s v excluded)
    (by intro z hz; obtain ⟨hm, _, hn⟩ := (mem_parentPool W Q).mp hz; exact Finset.mem_sdiff.mpr ⟨hm, hn⟩)
    (parentPool_large_of_degree W Q hα hα1 s v hdegree excluded
      (card_mixedForbidden_le W Q hα hα1 S s t hk requirements hvalid used hused))
  obtain ⟨hzR, hzAdj, _⟩ := (mem_parentPool W Q).mp hz
  exact ⟨z, hzR, hzAdj, hfresh, hfixed, hroot, hremainingGood⟩

/-- The initial root has the same mixed guarantees without a fictitious
cut parent. No pending edge is needed when every requirement is absent. -/
theorem exists_initial_mixed_root
    (hα : 0 < α) (hα1 : α ≤ 1 / 4)
    (S : CleanSourceWitness W Q) (s t : Fin 2)
    {k : ℕ} (hk : k ≤ 3) (requirements : Fin k → Requirement W Q)
    (hvalid : ∀ j, requirementValid W Q S (rootCluster W Q s) (requirements j))
    (used : Finset (Fin hostN)) (hused : (used.card : ℝ) ≤ (epsilon α : ℝ) * W.clusterSize)
    (remaining : Finset (MatchingEdge Q.claim67.M))
    (hremaining : remaining ⊆ edgesAwayFromDistinguished Q.claim67.M (padFinset (large W))
      (Sum.inl Q.A) (Sum.inl Q.B))
    (raw : MatchingEdge Q.claim67.M → Fin 2 → Finset (Fin hostN))
    (hraw : ∀ e ∈ remaining, ∀ c, raw e c ⊆ edgeWhole W Q e c)
    (hrawLarge : ∀ e ∈ remaining, ∀ c, (epsilon α : ℝ) * W.clusterSize ≤ (raw e c).card) :
    ∃ z ∈ reservoir W Q s, z ∉ used ∧
      (∀ j, requirementGood W Q S (rootCluster W Q s) (requirements j) z) ∧
      ((padGraph (reduced W)).Adj (Sum.inl (rootCluster W Q s)) (Sum.inl (rootCluster W Q t)) →
        ((densityCutoff α : ℝ) - (epsilon α : ℝ)) * (sourceQuota W : ℝ) ≤
          (#((reservoir W Q t).filter ((embeddingHost W).Adj z)) : ℝ)) ∧
      ∃ bad ⊆ remaining, (bad.card : ℝ) ≤ 2 * (rootTypicality α : ℝ) * remaining.card ∧
        ∀ e ∈ remaining \ bad, EligibleLiveRoot W Q S (rootCluster W Q s) e (raw e) z := by
  let excluded := mixedForbidden W Q S s t requirements used
  obtain ⟨z, hz, hfresh, hfixed, hroot, hremainingGood⟩ := exists_mixed_root_from_pool W Q hα hα1
    S s t requirements hvalid used remaining hremaining raw hraw hrawLarge (reservoir W Q s \ excluded)
    (Finset.Subset.refl _)
    (initialPool_large W Q hα hα1 s excluded
      (card_mixedForbidden_le W Q hα hα1 S s t hk requirements hvalid used hused))
  exact ⟨z, (Finset.mem_sdiff.mp hz).1, hfresh, hfixed, hroot, hremainingGood⟩

end Erdos547b.ZhaoSourceMixedRootSelection

#print axioms Erdos547b.ZhaoSourceMixedRootSelection.exists_mixed_root_from_pool
#print axioms Erdos547b.ZhaoSourceMixedRootSelection.exists_mixed_root_after_parent_degree
#print axioms Erdos547b.ZhaoSourceMixedRootSelection.exists_initial_mixed_root
