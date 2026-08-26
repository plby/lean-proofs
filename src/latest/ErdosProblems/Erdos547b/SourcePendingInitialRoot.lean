/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.SourcePendingRootSelection

/-!
# Initial pending-root selection without a cut-parent constraint

The raw root reservoir itself leaves a sufficiently large pool after the
same concrete used-root, fixed-edge, and opposite-reservoir exclusions.
This supplies the first root, where no parent adjacency is required.
-/

open scoped SimpleGraph Classical
noncomputable section

namespace Erdos547b.ZhaoSourcePendingInitialRoot

open Finset SimpleGraph
open Erdos547b.ZhaoStability Erdos547b.ZhaoDegreeForm Erdos547b.ZhaoEvenReducedPadding
open Erdos547b.ZhaoLemma611Full Erdos547b.ZhaoRichClaim61Lemma611
open Erdos547b.ZhaoSourceParameterSchedule Erdos547b.ZhaoSourceDegreeFormRootRows
open Erdos547b.ZhaoSourceEmbeddingHost Erdos547b.ZhaoSourceActualChunkEmbedding
open Erdos547b.ZhaoSourceOnlineMatchingRoot Erdos547b.ZhaoSourceParentCleanup
open Erdos547b.ZhaoSourceRootExclusions

variable {α : ℚ} {hostN q M : ℕ}
variable {G : SimpleGraph (Fin hostN)} [DecidableRel G.Adj]
variable (W : Witness α q M G) (Q : Certificate W)

theorem initialPool_large (hα : 0 < α) (hα1 : α ≤ 1 / 4)
    (s : Fin 2) (excluded : Finset (Fin hostN))
    (hexcluded : (excluded.card : ℝ) ≤
      (3 * (rootTypicality α : ℝ) + 6 * (epsilon α : ℝ)) * W.clusterSize) :
    (rootTypicality α : ℝ) * W.clusterSize < ((reservoir W Q s) \ excluded).card := by
  obtain ⟨hσ, _, _, hdσ, hεd, _⟩ := reservoir_cleanup_bounds hα hα1
  have hδ := (rootTypicality_margin hα hα1).2
  have hmarginQ : 4 * rootTypicality α + 6 * epsilon α < 2 * fourthRoot α ^ 2 := by
    linarith only [hδ, hσ, hdσ, hεd]
  have hmargin : 4 * (rootTypicality α : ℝ) + 6 * (epsilon α : ℝ) <
      2 * (fourthRoot α : ℝ) ^ 2 := by exact_mod_cast hmarginQ
  have hN : (0 : ℝ) < W.clusterSize := by exact_mod_cast W.clusterSize_pos
  have hscaled := mul_lt_mul_of_pos_right hmargin hN
  have hquota : 2 * (fourthRoot α : ℝ) ^ 2 * W.clusterSize ≤ (sourceQuota W : ℝ) :=
    Nat.le_ceil _
  have hcard : ((reservoir W Q s).card : ℝ) ≤
      (((reservoir W Q s) \ excluded).card : ℝ) + (excluded.card : ℝ) := by
    exact_mod_cast (Finset.card_le_card_sdiff_add_card (s := reservoir W Q s) (t := excluded))
  rw [reservoir_card] at hcard
  nlinarith only [hscaled, hquota, hcard, hexcluded]

/-- Select the first root with the same pending and future-root guarantees
as a later cut-adjacent root, but without imposing a fictitious parent. -/
theorem exists_initial_eligible_root
    (hα : 0 < α) (hα1 : α ≤ 1 / 4)
    (S : CleanSourceWitness W Q) (s t : Fin 2)
    (fixed : MatchingEdge Q.claim67.M)
    (hfixed : fixed ∈ edgesAwayFromDistinguished Q.claim67.M (padFinset (large W))
      (Sum.inl Q.A) (Sum.inl Q.B))
    (used : Finset (Fin hostN)) (hused : (used.card : ℝ) ≤ (epsilon α : ℝ) * W.clusterSize)
    (remaining : Finset (MatchingEdge Q.claim67.M))
    (hremaining : remaining ⊆ edgesAwayFromDistinguished Q.claim67.M
      (padFinset (large W)) (Sum.inl Q.A) (Sum.inl Q.B)) :
    ∃ z ∈ reservoir W Q s, z ∉ used ∧
      EligibleRoot W Q S (rootCluster W Q s) fixed z ∧
      ((padGraph (reduced W)).Adj (Sum.inl (rootCluster W Q s)) (Sum.inl (rootCluster W Q t)) →
        ((densityCutoff α : ℝ) - (epsilon α : ℝ)) * (sourceQuota W : ℝ) ≤
          (#((reservoir W Q t).filter ((embeddingHost W).Adj z)) : ℝ)) ∧
      ∃ bad ⊆ remaining,
        (bad.card : ℝ) ≤ 2 * (rootTypicality α : ℝ) * remaining.card ∧
        ∀ e ∈ remaining \ bad, EligibleRoot W Q S (rootCluster W Q s) e z := by
  let excluded := forbidden W Q S s t fixed used
  let pool := (reservoir W Q s) \ excluded
  have hpool := initialPool_large W Q hα hα1 s excluded
    (card_forbidden_le W Q hα hα1 S s t fixed hfixed used hused)
  obtain ⟨z, hz, bad, hb, hcount, hgood⟩ := exists_eligible_root_most_edges
    W Q hα hα1 S (rootCluster W Q s) (rootCluster_cases W Q s) remaining hremaining pool
      (Finset.sdiff_subset.trans (reservoir_subset W Q s)) hpool
  obtain ⟨hzR, hzFresh⟩ := Finset.mem_sdiff.mp hz
  have hnotUsed : z ∉ used := fun hu => hzFresh (Finset.mem_union_left _ (Finset.mem_union_left _ hu))
  have hnotEdge : z ∉ badForEdge W Q S (rootCluster W Q s) fixed :=
    fun he => hzFresh (Finset.mem_union_left _ (Finset.mem_union_right _ he))
  have hnotReservoir : z ∉ badToward W Q (Sum.inl (rootCluster W Q s)) t :=
    fun hr => hzFresh (Finset.mem_union_right _ hr)
  have hzWhole := reservoir_subset W Q s hzR
  refine ⟨z, hzR, hnotUsed,
    eligibleRoot_of_not_mem_badForEdge W Q S _ (rootCluster_cases W Q s)
      fixed hfixed z hzWhole hnotEdge, ?_, bad, hb, hcount, hgood⟩
  intro hrootAdj
  exact degree_into_reservoir_of_not_mem_badToward W Q (Sum.inl (rootCluster W Q s))
    t z hzWhole hnotReservoir hrootAdj

end Erdos547b.ZhaoSourcePendingInitialRoot

#print axioms Erdos547b.ZhaoSourcePendingInitialRoot.initialPool_large
#print axioms Erdos547b.ZhaoSourcePendingInitialRoot.exists_initial_eligible_root
