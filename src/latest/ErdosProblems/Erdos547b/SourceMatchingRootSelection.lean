/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.SourceMatchingChunkEmbedding
import ErdosProblems.Erdos547b.SourceOnlineRootSelection

/-!
# Root selection for an arbitrary physical reduced matching

The prescribed root pool may already include parent and reservoir
restrictions. Bad target incidences are projected to actual edge indices.
-/

open scoped SimpleGraph Classical
noncomputable section

namespace Erdos547b.ZhaoSourceMatchingRootSelection

open Finset SimpleGraph Erdos547b.ZhaoStability Erdos547b.ZhaoDegreeForm
open Erdos547b.ZhaoSourceDegreeFormRootRows Erdos547b.ZhaoSourceParameterSchedule
open Erdos547b.ZhaoSourceMatchingGeometry Erdos547b.ZhaoSourceEmbeddingHost
open Erdos547b.ZhaoSourceOnlineRootSelection Erdos547b.ZhaoLemma611Full
open Erdos547b.ZhaoEvenReducedPadding
open Erdos547b.RegularPair Erdos547b.ZhaoSourceFreshChunkBounds
open Erdos547b.ZhaoSourceDegreeFormBounds Erdos547b.ZhaoLemma58GroupedSmallForest
open Erdos547b.ZhaoLemma58ThresholdResidualCapacity
open Erdos547b.ZhaoSourceMatchingChunkEmbedding

variable {α : ℚ} {hostN q M : ℕ}
variable {G : SimpleGraph (Fin hostN)} [DecidableRel G.Adj]
variable (W : Witness α q M G) (Q : Certificate W) (S : CleanSourceWitness W Q)
variable (P : (padGraph (reduced W)).Subgraph)

def EligibleRoot (C : Index W) (e : MatchingEdge P) (z : Fin hostN) : Prop :=
  ∀ c, 0 < rootDensity W S (Sum.inl C) (pairVertex W P e c) →
    (rootDensity W S (Sum.inl C) (pairVertex W P e c) - 2 * (epsilon α : ℝ)) * W.clusterSize ≤
      (#((pairWhole W P e c).filter ((embeddingHost W).Adj z)) : ℝ)

theorem EligibleRoot.exists_chunk
    (hα : 0 < α) (hα1 : α ≤ 1 / 4) (hhost : hostN = 2 * q)
    (horder : orderThreshold α M ≤ q)
    (C : Index W) (hC : C = Q.A ∨ C = Q.B) (e : MatchingEdge P) (z : Fin hostN)
    (hz : EligibleRoot W Q S P C e z)
    {b : ℕ} (F : OrderedRootedForest b) (deleted : Fin 2 → Finset (Fin hostN))
    (hsmall : ∀ i, F.size i ≤ freshBranchBound α W.clusterSize)
    (hmass : (F.order : ℝ) ≤
      (rootDensity W S (Sum.inl C) (pairVertex W P e 0) +
        rootDensity W S (Sum.inl C) (pairVertex W P e 1) -
        2 * (gamma α : ℝ) - 3 * (epsilon α : ℝ)) * W.clusterSize)
    (hdeleted : ∀ c, deleted c ⊆ pairWhole W P e c)
    (hdeletedCard : ∀ c, (deleted c).card ≤ freshDeletionBudget α W.clusterSize) :
    ∃ orient : Fin b → Fin 2 ≃ Fin 2,
      Nonempty (DynamicAttachedForestEmbedding F (embeddingHost W) (fun _ => z) orient
        (residualSide (pairWhole W P e) deleted)) := by
  by_cases hle : rootDensity W S (Sum.inl C) (pairVertex W P e 0) ≤
      rootDensity W S (Sum.inl C) (pairVertex W P e 1)
  · exact exists_partOne_chunk W Q S P hα hα1 hhost horder C hC e F (fun _ => z)
      deleted 0 1 (by decide) hle hsmall hmass hdeleted hdeletedCard (fun _ c hp => hz c hp)
  · have hge := le_of_not_ge hle
    apply exists_partOne_chunk W Q S P hα hα1 hhost horder C hC e F (fun _ => z)
      deleted 1 0 (by decide) hge hsmall _ hdeleted hdeletedCard (fun _ c hp => hz c hp)
    rw [add_comm (rootDensity W S (Sum.inl C) (pairVertex W P e 0))
      (rootDensity W S (Sum.inl C) (pairVertex W P e 1))] at hmass
    exact hmass

theorem exists_eligible_root_most_edges
    (hα : 0 < α) (hα1 : α ≤ 1 / 4)
    (C : Index W) (hC : C = Q.A ∨ C = Q.B)
    (remaining : Finset (MatchingEdge P))
    (haway : ∀ e ∈ remaining, ∀ c, pairVertex W P e c ≠ Sum.inl Q.A ∧
      pairVertex W P e c ≠ Sum.inl Q.B)
    (pool : Finset (Fin hostN)) (hpool : pool ⊆ clusterVertices (assignment W) C)
    (hpoolCard : (rootTypicality α : ℝ) * W.clusterSize < pool.card) :
    ∃ z ∈ pool, ∃ bad ⊆ remaining,
      (bad.card : ℝ) ≤ 2 * (rootTypicality α : ℝ) * remaining.card ∧
      ∀ e ∈ remaining \ bad, EligibleRoot W Q S P C e z := by
  let J : Finset (MatchingEdge P × Fin 2) :=
    (remaining ×ˢ Finset.univ).filter fun ec =>
      0 < rootDensity W S (Sum.inl C) (pairVertex W P ec.1 ec.2)
  let whole := fun ec : MatchingEdge P × Fin 2 => pairWhole W P ec.1 ec.2
  let source := fun ec : MatchingEdge P × Fin 2 =>
    rootDensity W S (Sum.inl C) (pairVertex W P ec.1 ec.2)
  have hJ : J ⊆ remaining ×ˢ Finset.univ := Finset.filter_subset _ _
  have hpair (ec) (hec : ec ∈ J) :
      (embeddingHost W).IsUniform (epsilon α : ℝ) (clusterVertices (assignment W) C) (whole ec) ∧
        source ec ≤ (embeddingHost W).edgeDensity (clusterVertices (assignment W) C) (whole ec) +
          (epsilon α : ℝ) := by
    have he : ec.1 ∈ remaining := (Finset.mem_product.mp (hJ hec)).1
    have hn := haway ec.1 he ec.2
    have hpos : 0 < source ec := (Finset.mem_filter.mp hec).2
    rcases hC with rfl | rfl
    · have h := source_pair_A W S hn.1 hn.2 hpos
      exact ⟨h.1, h.2.2⟩
    · have h := source_pair_B W S hn.1 hn.2 hpos
      exact ⟨h.1, h.2.2⟩
  obtain ⟨_, _, _, _, heSmall, hdOne⟩ := reservoir_cleanup_bounds hα hα1
  have heOneQ : epsilon α ≤ 1 := by linarith only [heSmall, hdOne]
  have heOne : (epsilon α : ℝ) ≤ 1 := by exact_mod_cast heOneQ
  have hδ : (0 : ℝ) < rootTypicality α := by exact_mod_cast (rootTypicality_margin hα hα1).1
  have heδ : (epsilon α : ℝ) ≤ (rootTypicality α : ℝ) ^ 2 := by
    exact_mod_cast (rootTypicality_sq α).symm.le
  have hrootCard : (clusterVertices (assignment W) C).card = W.clusterSize := by
    rw [clusterVertices_partitionAssignment]
    exact W.equal_clusters C.1 C.2
  obtain ⟨z, hz, D, hDJ, hDcard, hgood⟩ := exists_root_source_lower_most (embeddingHost W)
    (clusterVertices (assignment W) C) pool J whole whole source (epsilon α : ℝ)
    (rootTypicality α : ℝ) heOne hδ heδ (fun ec hec => (hpair ec hec).1)
    (fun _ _ => Finset.Subset.refl _) (fun ec _ => by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right heOne (Nat.cast_nonneg (whole ec).card))
    (fun ec hec => (hpair ec hec).2) hpool (by simpa only [hrootCard] using hpoolCard)
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
  intro e he c hpos
  have hpJ : (e, c) ∈ J := Finset.mem_filter.mpr
    ⟨Finset.mem_product.mpr ⟨(Finset.mem_sdiff.mp he).1, Finset.mem_univ c⟩, hpos⟩
  have hdegree := hgood (e, c) (Finset.mem_sdiff.mpr ⟨hpJ, hclean e he c⟩)
  simpa only [source, whole, pairWhole_card, Erdos547EC2.degreeInto] using hdegree

end Erdos547b.ZhaoSourceMatchingRootSelection

#print axioms Erdos547b.ZhaoSourceMatchingRootSelection.exists_eligible_root_most_edges
#print axioms Erdos547b.ZhaoSourceMatchingRootSelection.EligibleRoot.exists_chunk
