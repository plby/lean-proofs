/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.SourceLiveRootExclusions
import ErdosProblems.Erdos547b.SourceOnlineMatchingRoot

/-!
# Almost-all-unused selection with edge-dependent live targets

Each matching edge supplies its own two actual large target subsets.
Threshold families may use whole endpoints; Part-3 families may use
their cleaned initial live sets. One incidence selection serves both.
-/

open scoped SimpleGraph Classical
noncomputable section

namespace Erdos547b.ZhaoSourceLiveMatchingRoot

open Finset SimpleGraph
open Erdos547b.ZhaoStability Erdos547b.ZhaoDegreeForm Erdos547b.ZhaoEvenReducedPadding
open Erdos547b.ZhaoLemma611Full Erdos547b.ZhaoRichClaim61Lemma611
open Erdos547b.ZhaoSourceParameterSchedule Erdos547b.ZhaoSourceDegreeFormRootRows
open Erdos547b.ZhaoSourceEmbeddingHost Erdos547b.ZhaoSourceActualChunkEmbedding
open Erdos547b.ZhaoSourceActualPartThreeStep Erdos547b.ZhaoSourceOnlineRootSelection

variable {α : ℚ} {hostN q M : ℕ}
variable {G : SimpleGraph (Fin hostN)} [DecidableRel G.Adj]
variable (W : Witness α q M G) (Q : Certificate W)

/-- A single root works on the designated large targets of all but a
square-root fraction of unused edges, even when those targets differ by family. -/
theorem exists_live_eligible_root_most_edges
    (hα : 0 < α) (hα1 : α ≤ 1 / 4)
    (S : CleanSourceWitness W Q) (C : Index W) (hC : C = Q.A ∨ C = Q.B)
    (remaining : Finset (MatchingEdge Q.claim67.M))
    (hremaining : remaining ⊆ edgesAwayFromDistinguished Q.claim67.M
      (padFinset (large W)) (Sum.inl Q.A) (Sum.inl Q.B))
    (raw : MatchingEdge Q.claim67.M → Fin 2 → Finset (Fin hostN))
    (hraw : ∀ e ∈ remaining, ∀ c, raw e c ⊆ edgeWhole W Q e c)
    (hrawLarge : ∀ e ∈ remaining, ∀ c, (epsilon α : ℝ) * W.clusterSize ≤ (raw e c).card)
    (pool : Finset (Fin hostN))
    (hpool : pool ⊆ clusterVertices (assignment W) C)
    (hpoolCard : (rootTypicality α : ℝ) * W.clusterSize < pool.card) :
    ∃ z ∈ pool, ∃ bad ⊆ remaining,
      (bad.card : ℝ) ≤ 2 * (rootTypicality α : ℝ) * remaining.card ∧
      ∀ e ∈ remaining \ bad, EligibleLiveRoot W Q S C e (raw e) z := by
  let J : Finset (MatchingEdge Q.claim67.M × Fin 2) :=
    (remaining ×ˢ Finset.univ).filter fun p =>
      0 < rootDensity W S (Sum.inl C) (edgeVertex W Q p.1 p.2)
  let whole := fun p : MatchingEdge Q.claim67.M × Fin 2 => edgeWhole W Q p.1 p.2
  let source := fun p : MatchingEdge Q.claim67.M × Fin 2 =>
    rootDensity W S (Sum.inl C) (edgeVertex W Q p.1 p.2)
  have hJ : J ⊆ remaining ×ˢ Finset.univ := Finset.filter_subset _ _
  have hmem (p) (hp : p ∈ J) : p.1 ∈ remaining := (Finset.mem_product.mp (hJ hp)).1
  have hpair (p) (hp : p ∈ J) :
      (embeddingHost W).IsUniform (epsilon α : ℝ)
          (clusterVertices (assignment W) C) (whole p) ∧
        source p ≤ (embeddingHost W).edgeDensity (clusterVertices (assignment W) C) (whole p) +
          (epsilon α : ℝ) := by
    have hn := endpoint_ne_distinguished_of_mem_away Q.claim67.M (padFinset (large W))
      (Sum.inl Q.A) (Sum.inl Q.B) (hremaining (hmem p hp)) p.2
    have hpos : 0 < source p := (Finset.mem_filter.mp hp).2
    rcases hC with rfl | rfl
    · have h := source_pair_A W S hn.1 hn.2 hpos
      exact ⟨h.1, h.2.2⟩
    · have h := source_pair_B W S hn.1 hn.2 hpos
      exact ⟨h.1, h.2.2⟩
  obtain ⟨_, _, _, _, heSmall, hdOne⟩ := reservoir_cleanup_bounds hα hα1
  have heOneQ : epsilon α ≤ 1 := by linarith only [heSmall, hdOne]
  have heOne : (epsilon α : ℝ) ≤ 1 := by exact_mod_cast heOneQ
  have he : (0 : ℝ) ≤ epsilon α := by exact_mod_cast (parameter_pos hα).2.2.2.2.2.2.2.le
  have hδ : (0 : ℝ) < rootTypicality α := by exact_mod_cast (rootTypicality_margin hα hα1).1
  have heδ : (epsilon α : ℝ) ≤ (rootTypicality α : ℝ) ^ 2 := by
    exact_mod_cast (rootTypicality_sq α).symm.le
  have hrootCard : (clusterVertices (assignment W) C).card = W.clusterSize := by
    rw [clusterVertices_partitionAssignment]
    exact W.equal_clusters C.1 C.2
  obtain ⟨z, hz, D, hDJ, hDcard, hgood⟩ := exists_root_source_lower_most (embeddingHost W)
    (clusterVertices (assignment W) C) pool J whole (fun p => raw p.1 p.2) source (epsilon α : ℝ)
    (rootTypicality α : ℝ) heOne hδ heδ (fun p hp => (hpair p hp).1)
    (fun p hp => hraw p.1 (hmem p hp) p.2)
    (fun p hp => by simpa only [whole, edgeWhole_card] using hrawLarge p.1 (hmem p hp) p.2)
    (fun p hp => (hpair p hp).2) hpool (by simpa only [hrootCard] using hpoolCard)
  obtain ⟨hbad, hbadCard, hclean⟩ := projected_bad_edges remaining D (hDJ.trans hJ)
  have hJcard : J.card ≤ 2 * remaining.card := by
    have h := Finset.card_le_card hJ
    simpa only [Finset.card_product, Finset.card_univ, Fintype.card_fin, Nat.mul_comm] using h
  have hbadR : ((D.image Prod.fst).card : ℝ) ≤ 2 * (rootTypicality α : ℝ) * remaining.card := by
    have h1 : ((D.image Prod.fst).card : ℝ) ≤ D.card := by exact_mod_cast hbadCard
    have h2 : (J.card : ℝ) ≤ 2 * remaining.card := by exact_mod_cast hJcard
    have h3 := mul_le_mul_of_nonneg_left h2 hδ.le
    linarith only [h1, hDcard, h3]
  refine ⟨z, hz, D.image Prod.fst, hbad, hbadR, ?_⟩
  intro e heGood c
  by_cases hpos : 0 < rootDensity W S (Sum.inl C) (edgeVertex W Q e c)
  · have hpJ : (e, c) ∈ J := Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr ⟨(Finset.mem_sdiff.mp heGood).1, Finset.mem_univ c⟩, hpos⟩
    have hdegree := hgood (e, c) (Finset.mem_sdiff.mpr ⟨hpJ, hclean e heGood c⟩)
    simpa only [source, Erdos547EC2.degreeInto] using hdegree
  · have hcoeff : rootDensity W S (Sum.inl C) (edgeVertex W Q e c) - 2 * (epsilon α : ℝ) ≤ 0 := by
      linarith only [le_of_not_gt hpos, he]
    exact (mul_nonpos_of_nonpos_of_nonneg hcoeff (Nat.cast_nonneg (raw e c).card)).trans
      (Nat.cast_nonneg _)

end Erdos547b.ZhaoSourceLiveMatchingRoot

#print axioms Erdos547b.ZhaoSourceLiveMatchingRoot.exists_live_eligible_root_most_edges
