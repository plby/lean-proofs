/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.SourceRootExclusions

/-!
# A pending-compatible root from an actual cut-parent degree

Only the parent's literal degree into the current root reservoir is used.
Consequently the parent may be either an embedded internal vertex or an
earlier root. The output retains source-degree eligibility, which supports
the fixed pending orientation, as well as almost-all-unused-edge access.
-/

open scoped SimpleGraph Classical
noncomputable section

namespace Erdos547b.ZhaoSourcePendingRootSelection

open Finset SimpleGraph
open Erdos547b.ZhaoStability Erdos547b.ZhaoDegreeForm Erdos547b.ZhaoEvenReducedPadding
open Erdos547b.ZhaoLemma611Full Erdos547b.ZhaoRichClaim61Lemma611
open Erdos547b.ZhaoSourceParameterSchedule Erdos547b.ZhaoSourceDegreeFormRootRows
open Erdos547b.ZhaoSourceEmbeddingHost Erdos547b.ZhaoSourceActualChunkEmbedding
open Erdos547b.ZhaoSourceOnlineMatchingRoot Erdos547b.ZhaoSourceParentCleanup
open Erdos547b.ZhaoSourceRootReconnection Erdos547b.ZhaoSourceRootExclusions

variable {α : ℚ} {hostN q M : ℕ}
variable {G : SimpleGraph (Fin hostN)} [DecidableRel G.Adj]
variable (W : Witness α q M G) (Q : Certificate W)

/-- The reconnection pool estimate depends on the actual parent degree,
not on whether the parent is internal or is itself a chosen root. -/
theorem parentPool_large_of_degree (hα : 0 < α) (hα1 : α ≤ 1 / 4)
    (s : Fin 2) (v : Fin hostN)
    (hdegree : ((densityCutoff α : ℝ) - (epsilon α : ℝ)) * (sourceQuota W : ℝ) ≤
      (#((reservoir W Q s).filter ((embeddingHost W).Adj v)) : ℝ))
    (excluded : Finset (Fin hostN))
    (hexcluded : (excluded.card : ℝ) ≤
      (3 * (rootTypicality α : ℝ) + 6 * (epsilon α : ℝ)) * W.clusterSize) :
    (rootTypicality α : ℝ) * W.clusterSize < (parentPool W Q s v excluded).card := by
  have hmargin : 4 * (rootTypicality α : ℝ) + 8 * (epsilon α : ℝ) <
      ((densityCutoff α : ℝ) - (epsilon α : ℝ)) * (2 * (fourthRoot α : ℝ) ^ 2) := by
    exact_mod_cast reconnection_margin hα hα1
  have hε : (0 : ℝ) < epsilon α := by exact_mod_cast (parameter_pos hα).2.2.2.2.2.2.2
  have hδ : (0 : ℝ) < rootTypicality α := by
    exact_mod_cast (rootTypicality_margin hα hα1).1
  have hdε : (0 : ℝ) ≤ (densityCutoff α : ℝ) - (epsilon α : ℝ) := by
    by_contra h
    have hnonpos := mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge h)
      (by positivity : (0 : ℝ) ≤ 2 * (fourthRoot α : ℝ) ^ 2)
    linarith only [hmargin, hnonpos, hε, hδ]
  have hN : (0 : ℝ) < W.clusterSize := by exact_mod_cast W.clusterSize_pos
  have hquota : 2 * (fourthRoot α : ℝ) ^ 2 * W.clusterSize ≤ (sourceQuota W : ℝ) :=
    Nat.le_ceil _
  have hscaled := mul_lt_mul_of_pos_right hmargin hN
  have hquotaScaled := mul_le_mul_of_nonneg_left hquota hdε
  have hcard : (#((reservoir W Q s).filter ((embeddingHost W).Adj v)) : ℝ) ≤
      (parentPool W Q s v excluded).card + (excluded.card : ℝ) := by
    exact_mod_cast (Finset.card_le_card_sdiff_add_card
      (s := (reservoir W Q s).filter ((embeddingHost W).Adj v)) (t := excluded))
  have hεN := mul_pos hε hN
  nlinarith only [hscaled, hquotaScaled, hdegree, hcard, hexcluded, hεN]

/-- Choose the current root with its fixed pending-edge degree bounds,
future opposite-reservoir degree, and eligibility on almost all unused
edges. Every constraint is discharged from actual source data. -/
theorem exists_eligible_root_after_parent_degree
    (hα : 0 < α) (hα1 : α ≤ 1 / 4)
    (S : CleanSourceWitness W Q) (s t : Fin 2) (v : Fin hostN)
    (hdegree : ((densityCutoff α : ℝ) - (epsilon α : ℝ)) * (sourceQuota W : ℝ) ≤
      (#((reservoir W Q s).filter ((embeddingHost W).Adj v)) : ℝ))
    (fixed : MatchingEdge Q.claim67.M)
    (hfixed : fixed ∈ edgesAwayFromDistinguished Q.claim67.M (padFinset (large W))
      (Sum.inl Q.A) (Sum.inl Q.B))
    (used : Finset (Fin hostN)) (hused : (used.card : ℝ) ≤ (epsilon α : ℝ) * W.clusterSize)
    (remaining : Finset (MatchingEdge Q.claim67.M))
    (hremaining : remaining ⊆ edgesAwayFromDistinguished Q.claim67.M
      (padFinset (large W)) (Sum.inl Q.A) (Sum.inl Q.B)) :
    ∃ z ∈ reservoir W Q s, (embeddingHost W).Adj v z ∧ z ∉ used ∧
      EligibleRoot W Q S (rootCluster W Q s) fixed z ∧
      ((padGraph (reduced W)).Adj (Sum.inl (rootCluster W Q s)) (Sum.inl (rootCluster W Q t)) →
        ((densityCutoff α : ℝ) - (epsilon α : ℝ)) * (sourceQuota W : ℝ) ≤
          (#((reservoir W Q t).filter ((embeddingHost W).Adj z)) : ℝ)) ∧
      ∃ bad ⊆ remaining,
        (bad.card : ℝ) ≤ 2 * (rootTypicality α : ℝ) * remaining.card ∧
        ∀ e ∈ remaining \ bad, EligibleRoot W Q S (rootCluster W Q s) e z := by
  let excluded := forbidden W Q S s t fixed used
  have hpool := parentPool_large_of_degree W Q hα hα1 s v hdegree excluded
    (card_forbidden_le W Q hα hα1 S s t fixed hfixed used hused)
  obtain ⟨z, hz, bad, hb, hcount, hgood⟩ := exists_eligible_root_most_edges
    W Q hα hα1 S (rootCluster W Q s) (rootCluster_cases W Q s) remaining hremaining
      (parentPool W Q s v excluded) (parentPool_subset W Q s v excluded) hpool
  obtain ⟨hzR, hzAdj, hzFresh⟩ := (mem_parentPool W Q).mp hz
  have hnotUsed : z ∉ used := fun hu => hzFresh (Finset.mem_union_left _ (Finset.mem_union_left _ hu))
  have hnotEdge : z ∉ badForEdge W Q S (rootCluster W Q s) fixed :=
    fun he => hzFresh (Finset.mem_union_left _ (Finset.mem_union_right _ he))
  have hnotReservoir : z ∉ badToward W Q (Sum.inl (rootCluster W Q s)) t :=
    fun hr => hzFresh (Finset.mem_union_right _ hr)
  have hzWhole := reservoir_subset W Q s hzR
  refine ⟨z, hzR, hzAdj, hnotUsed,
    eligibleRoot_of_not_mem_badForEdge W Q S _ (rootCluster_cases W Q s)
      fixed hfixed z hzWhole hnotEdge, ?_, bad, hb, hcount, hgood⟩
  intro hrootAdj
  exact degree_into_reservoir_of_not_mem_badToward W Q (Sum.inl (rootCluster W Q s))
    t z hzWhole hnotReservoir hrootAdj

end Erdos547b.ZhaoSourcePendingRootSelection

#print axioms Erdos547b.ZhaoSourcePendingRootSelection.parentPool_large_of_degree
#print axioms Erdos547b.ZhaoSourcePendingRootSelection.exists_eligible_root_after_parent_degree
