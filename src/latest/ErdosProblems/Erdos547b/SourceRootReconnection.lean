/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.SourceParentCleanup

/-!
# Root selection adjacent to an already embedded cut parent

The permanent cleanup supplies a genuine live parent-neighbor pool.
The source parameter schedule pays for used roots and additional local
exclusions before the almost-all-unused-edges root selector is applied.
-/

open scoped SimpleGraph Classical
noncomputable section

namespace Erdos547b.ZhaoSourceRootReconnection

open Finset SimpleGraph
open Erdos547b.ZhaoStability Erdos547b.ZhaoDegreeForm Erdos547b.ZhaoEvenReducedPadding
open Erdos547b.ZhaoLemma611Full Erdos547b.ZhaoRichClaim61Lemma611
open Erdos547b.ZhaoSourceParameterSchedule Erdos547b.ZhaoSourceDegreeFormRootRows
open Erdos547b.ZhaoSourceEmbeddingHost Erdos547b.ZhaoSourceActualChunkEmbedding
open Erdos547b.ZhaoSourceOnlineMatchingRoot Erdos547b.ZhaoSourceParentCleanup
open Erdos547b.ZhaoSourceDegreeFormBounds

/-- The actual source scales leave room for the constrained root pool,
used roots, and the fixed-pair exclusions at a pending-bin transition. -/
theorem reconnection_margin {α : ℚ} (hα : 0 < α) (hα1 : α ≤ 1 / 4) :
    4 * rootTypicality α + 8 * epsilon α <
      (densityCutoff α - epsilon α) * (2 * fourthRoot α ^ 2) := by
  obtain ⟨_, _, _, _, hd, _, hg, he⟩ := parameter_pos hα
  obtain ⟨_, _, _, _, _, hgd, heg⟩ := parameter_upper_bounds hα hα1
  obtain ⟨hσ, hσsmall, _, hdσ, _, hd1⟩ := reservoir_cleanup_bounds hα hα1
  have hg1 : gamma α ≤ 1 := by linarith only [hgd, hd1]
  have hd10 : degreeError α ^ 10 ≤ 1 := by
    simpa only [one_pow] using pow_le_pow_left₀ hd.le hd1 10
  have hd12 : degreeError α ^ 12 ≤ degreeError α ^ 2 := by
    calc
      degreeError α ^ 12 = degreeError α ^ 2 * degreeError α ^ 10 := by ring
      _ ≤ degreeError α ^ 2 * 1 := mul_le_mul_of_nonneg_left hd10 (sq_nonneg _)
      _ = degreeError α ^ 2 := mul_one _
  have hgd2 : gamma α ≤ degreeError α ^ 2 / 1000000 :=
    div_le_div_of_nonneg_right hd12 (by norm_num)
  have hδg : rootTypicality α ≤ gamma α / 1000 :=
    div_le_div_of_nonneg_right (pow_succ_le_self hg.le hg1 5) (by norm_num)
  have hd2σ := mul_le_mul_of_nonneg_left hdσ hd.le
  have hprod := mul_pos hd hσ
  have hstrong : 16 * (rootTypicality α + epsilon α) <
      densityCutoff α * fourthRoot α ^ 2 := by
    unfold densityCutoff
    nlinarith only [hgd2, hδg, heg, hd2σ, hprod]
  have heσ : epsilon α * fourthRoot α ^ 2 ≤ epsilon α := by
    have hσ1 : fourthRoot α ^ 2 ≤ 1 := by linarith only [hσsmall]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hσ1 he.le
  have hδ := (rootTypicality_margin hα hα1).1
  nlinarith only [hstrong, heσ, he, hδ]

variable {α : ℚ} {hostN q M : ℕ}
variable {G : SimpleGraph (Fin hostN)} [DecidableRel G.Adj]
variable (W : Witness α q M G) (Q : Certificate W)

def parentPool (s : Fin 2) (v : Fin hostN) (excluded : Finset (Fin hostN)) :
    Finset (Fin hostN) :=
  ((reservoir W Q s).filter ((embeddingHost W).Adj v)) \ excluded

theorem mem_parentPool {s : Fin 2} {v z : Fin hostN} {excluded : Finset (Fin hostN)} :
    z ∈ parentPool W Q s v excluded ↔
      z ∈ reservoir W Q s ∧ (embeddingHost W).Adj v z ∧ z ∉ excluded := by
  simp only [parentPool, Finset.mem_sdiff, Finset.mem_filter, and_assoc]

theorem parentPool_subset (s : Fin 2) (v : Fin hostN) (excluded : Finset (Fin hostN)) :
    parentPool W Q s v excluded ⊆
      clusterVertices (assignment W) (rootCluster W Q s) := by
  intro z hz
  exact reservoir_subset W Q s ((mem_parentPool W Q).mp hz).1

/-- A retained cut parent provides a pool large enough for the actual
online selector, after all exclusions within the explicit source budget. -/
theorem parentPool_large
    (hα : 0 < α) (hα1 : α ≤ 1 / 4)
    (e : MatchingEdge Q.claim67.M) (c s : Fin 2) (v : Fin hostN)
    (hv : v ∈ edgeWhole W Q e c \ deleted W Q e c)
    (hadj : (padGraph (reduced W)).Adj (edgeVertex W Q e c) (Sum.inl (rootCluster W Q s)))
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
  have hσ : (0 : ℝ) < (fourthRoot α : ℝ) ^ 2 := by
    exact_mod_cast (reservoir_cleanup_bounds hα hα1).1
  have hdε : (0 : ℝ) ≤ (densityCutoff α : ℝ) - (epsilon α : ℝ) := by
    by_contra h
    have hnonpos := mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge h) (by positivity :
      (0 : ℝ) ≤ 2 * (fourthRoot α : ℝ) ^ 2)
    linarith only [hmargin, hnonpos, hε, hδ]
  have hN : (0 : ℝ) < W.clusterSize := by exact_mod_cast W.clusterSize_pos
  have hquota : 2 * (fourthRoot α : ℝ) ^ 2 * W.clusterSize ≤ (sourceQuota W : ℝ) :=
    Nat.le_ceil _
  have hscaled := mul_lt_mul_of_pos_right hmargin hN
  have hquotaScaled := mul_le_mul_of_nonneg_left hquota hdε
  have hdegree := parent_degree_into_reservoir W Q e c s v hv hadj
  have hcard : (#((reservoir W Q s).filter ((embeddingHost W).Adj v)) : ℝ) ≤
      (parentPool W Q s v excluded).card + (excluded.card : ℝ) := by
    exact_mod_cast (Finset.card_le_card_sdiff_add_card
      (s := (reservoir W Q s).filter ((embeddingHost W).Adj v)) (t := excluded))
  have hεN := mul_pos hε hN
  nlinarith only [hscaled, hquotaScaled, hdegree, hcard, hexcluded, hεN]

/-- Reconnect a new root to its actual old parent and simultaneously
obtain proved Part-1 access on almost all unused matching edges. -/
theorem exists_root_partOne_access_after_parent
    (hα : 0 < α) (hα1 : α ≤ 1 / 4)
    (hhost : hostN = 2 * q) (horder : orderThreshold α M ≤ q)
    (S : CleanSourceWitness W Q)
    (parentEdge : MatchingEdge Q.claim67.M) (c s : Fin 2) (v : Fin hostN)
    (hv : v ∈ edgeWhole W Q parentEdge c \ deleted W Q parentEdge c)
    (hadj : (padGraph (reduced W)).Adj (edgeVertex W Q parentEdge c)
      (Sum.inl (rootCluster W Q s)))
    (excluded : Finset (Fin hostN))
    (hexcluded : (excluded.card : ℝ) ≤
      (3 * (rootTypicality α : ℝ) + 6 * (epsilon α : ℝ)) * W.clusterSize)
    (remaining : Finset (MatchingEdge Q.claim67.M))
    (hremaining : remaining ⊆ edgesAwayFromDistinguished Q.claim67.M
      (padFinset (large W)) (Sum.inl Q.A) (Sum.inl Q.B)) :
    ∃ z ∈ reservoir W Q s, (embeddingHost W).Adj v z ∧ z ∉ excluded ∧
      ∃ bad ⊆ remaining,
        (bad.card : ℝ) ≤ 2 * (rootTypicality α : ℝ) * remaining.card ∧
        ∀ e ∈ remaining \ bad, PartOneAccess W Q S (rootCluster W Q s) e z := by
  have hC : rootCluster W Q s = Q.A ∨ rootCluster W Q s = Q.B := by
    unfold rootCluster
    split_ifs <;> simp_all only [true_or, or_true]
  obtain ⟨z, hz, bad, hb, hcount, hgood⟩ := exists_root_partOne_access_most_edges
    W Q hα hα1 hhost horder S (rootCluster W Q s) hC remaining hremaining
      (parentPool W Q s v excluded) (parentPool_subset W Q s v excluded)
      (parentPool_large W Q hα hα1 parentEdge c s v hv hadj excluded hexcluded)
  obtain ⟨hzR, hzAdj, hzFresh⟩ := (mem_parentPool W Q).mp hz
  exact ⟨z, hzR, hzAdj, hzFresh, bad, hb, hcount, hgood⟩

end Erdos547b.ZhaoSourceRootReconnection

#print axioms Erdos547b.ZhaoSourceRootReconnection.reconnection_margin
#print axioms Erdos547b.ZhaoSourceRootReconnection.mem_parentPool
#print axioms Erdos547b.ZhaoSourceRootReconnection.parentPool_subset
#print axioms Erdos547b.ZhaoSourceRootReconnection.parentPool_large
#print axioms Erdos547b.ZhaoSourceRootReconnection.exists_root_partOne_access_after_parent
