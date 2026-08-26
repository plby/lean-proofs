/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.SourceActualChunkEmbedding
import ErdosProblems.Erdos547b.SourceOnlineRootSelection

/-!
# A prescribed-pool root eligible for almost all actual matching edges

Only positive source entries are put in the target list. Each retained
edge then supplies exactly the parent-neighbor hypotheses of the actual
fresh-chunk embedding, with the same selected root on every retained edge.
-/

open scoped SimpleGraph Classical
noncomputable section

namespace Erdos547b.ZhaoSourceOnlineMatchingRoot

open Finset SimpleGraph
open Erdos547b.ZhaoStability Erdos547b.ZhaoDegreeForm Erdos547b.ZhaoEvenReducedPadding
open Erdos547b.ZhaoLemma611Full Erdos547b.ZhaoRichClaim61Lemma611
open Erdos547b.ZhaoSourceParameterSchedule Erdos547b.ZhaoSourceDegreeFormRootRows
open Erdos547b.ZhaoSourceEmbeddingHost Erdos547b.ZhaoSourceOnlineRootSelection
open Erdos547b.ZhaoSourceActualChunkEmbedding
open Erdos547b.RegularPair Erdos547b.ZhaoLemma58GroupedSmallForest
open Erdos547b.ZhaoSourceDegreeFormBounds Erdos547b.ZhaoSourceFreshChunkBounds
open Erdos547b.ZhaoLemma58ThresholdResidualCapacity

variable {α : ℚ} {hostN q M : ℕ}
variable {G : SimpleGraph (Fin hostN)} [DecidableRel G.Adj]
variable (W : Witness α q M G) (Q : Certificate W)

def EligibleRoot (S : CleanSourceWitness W Q) (C : Index W)
    (e : MatchingEdge Q.claim67.M) (z : Fin hostN) : Prop :=
  ∀ c, 0 < rootDensity W S (Sum.inl C) (edgeVertex W Q e c) →
    (rootDensity W S (Sum.inl C) (edgeVertex W Q e c) - 2 * (epsilon α : ℝ)) * W.clusterSize ≤
      (#((edgeWhole W Q e c).filter ((embeddingHost W).Adj z)) : ℝ)

/-- The literal Part-1 real capacity, symmetric in the matching endpoints. -/
def partOneCapacity (S : CleanSourceWitness W Q) (C : Index W)
    (e : MatchingEdge Q.claim67.M) : ℝ :=
  (rootDensity W S (Sum.inl C) (edgeVertex W Q e 0) +
    rootDensity W S (Sum.inl C) (edgeVertex W Q e 1) -
    2 * (gamma α : ℝ) - 3 * (epsilon α : ℝ)) * W.clusterSize

/-- All branch chunks within the source capacity can be embedded on this
edge with the prescribed root. This is proved from actual root degrees. -/
def PartOneAccess (S : CleanSourceWitness W Q) (C : Index W)
    (e : MatchingEdge Q.claim67.M) (z : Fin hostN) : Prop :=
  ∀ (b : ℕ) (F : OrderedRootedForest b) (deleted : Fin 2 → Finset (Fin hostN)),
    (∀ i, F.size i ≤ freshBranchBound α W.clusterSize) →
    (F.order : ℝ) ≤ partOneCapacity W Q S C e →
    (∀ c, deleted c ⊆ edgeWhole W Q e c) →
    (∀ c, (deleted c).card ≤ freshDeletionBudget α W.clusterSize) →
    ∃ orient : Fin b → Fin 2 ≃ Fin 2,
      Nonempty (DynamicAttachedForestEmbedding F (embeddingHost W) (fun _ => z) orient
        (residualSide (edgeWhole W Q e) deleted))

/-- An eligible root supplies actual graph embeddings, with the low/high
orientation chosen here and every source-parameter gate already discharged. -/
theorem EligibleRoot.partOneAccess
    (hα : 0 < α) (hα1 : α ≤ 1 / 4)
    (hhost : hostN = 2 * q) (horder : orderThreshold α M ≤ q)
    (S : CleanSourceWitness W Q) (C : Index W) (hC : C = Q.A ∨ C = Q.B)
    (e : MatchingEdge Q.claim67.M) (z : Fin hostN) (hz : EligibleRoot W Q S C e z) :
    PartOneAccess W Q S C e z := by
  intro b F deleted hsmall hmass hdeleted hdeletedCard
  by_cases hle : rootDensity W S (Sum.inl C) (edgeVertex W Q e 0) ≤
      rootDensity W S (Sum.inl C) (edgeVertex W Q e 1)
  · exact exists_actual_partOne_chunk W Q hα hα1 hhost horder S C hC e F (fun _ => z)
      deleted 0 1 (by decide) hle hsmall hmass hdeleted hdeletedCard (fun _ c hp => hz c hp)
  · have hge := le_of_not_ge hle
    apply exists_actual_partOne_chunk W Q hα hα1 hhost horder S C hC e F (fun _ => z)
      deleted 1 0 (by decide) hge hsmall _ hdeleted hdeletedCard (fun _ c hp => hz c hp)
    rw [partOneCapacity,
      add_comm (rootDensity W S (Sum.inl C) (edgeVertex W Q e 0))
        (rootDensity W S (Sum.inl C) (edgeVertex W Q e 1))] at hmass
    exact hmass

/-- Choose an actual root in the live pool; at most a square-root fraction
of the unused matching edges fail the fresh-chunk source-degree bounds. -/
theorem exists_eligible_root_most_edges
    (hα : 0 < α) (hα1 : α ≤ 1 / 4)
    (S : CleanSourceWitness W Q) (C : Index W) (hC : C = Q.A ∨ C = Q.B)
    (remaining : Finset (MatchingEdge Q.claim67.M))
    (hremaining : remaining ⊆ edgesAwayFromDistinguished Q.claim67.M
      (padFinset (large W)) (Sum.inl Q.A) (Sum.inl Q.B))
    (pool : Finset (Fin hostN))
    (hpool : pool ⊆ clusterVertices (assignment W) C)
    (hpoolCard : (rootTypicality α : ℝ) * W.clusterSize < pool.card) :
    ∃ z ∈ pool, ∃ bad ⊆ remaining,
      (bad.card : ℝ) ≤ 2 * (rootTypicality α : ℝ) * remaining.card ∧
      ∀ e ∈ remaining \ bad, EligibleRoot W Q S C e z := by
  let J : Finset (MatchingEdge Q.claim67.M × Fin 2) :=
    (remaining ×ˢ Finset.univ).filter fun p =>
      0 < rootDensity W S (Sum.inl C) (edgeVertex W Q p.1 p.2)
  let whole := fun p : MatchingEdge Q.claim67.M × Fin 2 => edgeWhole W Q p.1 p.2
  let source := fun p : MatchingEdge Q.claim67.M × Fin 2 =>
    rootDensity W S (Sum.inl C) (edgeVertex W Q p.1 p.2)
  have hJ : J ⊆ remaining ×ˢ Finset.univ := Finset.filter_subset _ _
  have hpair (p) (hp : p ∈ J) :
      (embeddingHost W).IsUniform (epsilon α : ℝ)
          (clusterVertices (assignment W) C) (whole p) ∧
        source p ≤ (embeddingHost W).edgeDensity (clusterVertices (assignment W) C) (whole p) +
          (epsilon α : ℝ) := by
    have he : p.1 ∈ remaining := (Finset.mem_product.mp (hJ hp)).1
    have hn := endpoint_ne_distinguished_of_mem_away Q.claim67.M (padFinset (large W))
      (Sum.inl Q.A) (Sum.inl Q.B) (hremaining he) p.2
    have hpos : 0 < source p := (Finset.mem_filter.mp hp).2
    rcases hC with rfl | rfl
    · have h := source_pair_A W S hn.1 hn.2 hpos
      exact ⟨h.1, h.2.2⟩
    · have h := source_pair_B W S hn.1 hn.2 hpos
      exact ⟨h.1, h.2.2⟩
  obtain ⟨_, _, _, _, heSmall, hdOne⟩ := reservoir_cleanup_bounds hα hα1
  have heOneQ : epsilon α ≤ 1 := by linarith only [heSmall, hdOne]
  have heOne : (epsilon α : ℝ) ≤ 1 := by exact_mod_cast heOneQ
  have hδ : (0 : ℝ) < rootTypicality α := by
    exact_mod_cast (rootTypicality_margin hα hα1).1
  have heδ : (epsilon α : ℝ) ≤ (rootTypicality α : ℝ) ^ 2 := by
    exact_mod_cast (rootTypicality_sq α).symm.le
  have hrootCard : (clusterVertices (assignment W) C).card = W.clusterSize := by
    rw [clusterVertices_partitionAssignment]
    exact W.equal_clusters C.1 C.2
  obtain ⟨z, hz, D, hDJ, hDcard, hgood⟩ := exists_root_source_lower_most (embeddingHost W)
    (clusterVertices (assignment W) C) pool J whole whole source (epsilon α : ℝ)
    (rootTypicality α : ℝ) heOne hδ heδ (fun p hp => (hpair p hp).1)
    (fun _ _ => Finset.Subset.refl _) (fun p _ => by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right heOne (Nat.cast_nonneg (whole p).card))
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
  intro e he c hpos
  have hpJ : (e, c) ∈ J := Finset.mem_filter.mpr
    ⟨Finset.mem_product.mpr ⟨(Finset.mem_sdiff.mp he).1, Finset.mem_univ c⟩, hpos⟩
  have hdegree := hgood (e, c) (Finset.mem_sdiff.mpr ⟨hpJ, hclean e he c⟩)
  simpa only [source, whole, edgeWhole_card, Erdos547EC2.degreeInto] using hdegree

/-- Source-faithful root choice with actual Part-1 graph access on every
surviving unused matching edge. The root is fixed across all these edges. -/
theorem exists_root_partOne_access_most_edges
    (hα : 0 < α) (hα1 : α ≤ 1 / 4)
    (hhost : hostN = 2 * q) (horder : orderThreshold α M ≤ q)
    (S : CleanSourceWitness W Q) (C : Index W) (hC : C = Q.A ∨ C = Q.B)
    (remaining : Finset (MatchingEdge Q.claim67.M))
    (hremaining : remaining ⊆ edgesAwayFromDistinguished Q.claim67.M
      (padFinset (large W)) (Sum.inl Q.A) (Sum.inl Q.B))
    (pool : Finset (Fin hostN))
    (hpool : pool ⊆ clusterVertices (assignment W) C)
    (hpoolCard : (rootTypicality α : ℝ) * W.clusterSize < pool.card) :
    ∃ z ∈ pool, ∃ bad ⊆ remaining,
      (bad.card : ℝ) ≤ 2 * (rootTypicality α : ℝ) * remaining.card ∧
      ∀ e ∈ remaining \ bad, PartOneAccess W Q S C e z := by
  obtain ⟨z, hz, bad, hb, hcount, hgood⟩ :=
    exists_eligible_root_most_edges W Q hα hα1 S C hC remaining hremaining pool hpool hpoolCard
  exact ⟨z, hz, bad, hb, hcount, fun e he =>
    EligibleRoot.partOneAccess W Q hα hα1 hhost horder S C hC e z (hgood e he)⟩

end Erdos547b.ZhaoSourceOnlineMatchingRoot

#print axioms Erdos547b.ZhaoSourceOnlineMatchingRoot.exists_eligible_root_most_edges
#print axioms Erdos547b.ZhaoSourceOnlineMatchingRoot.EligibleRoot.partOneAccess
#print axioms Erdos547b.ZhaoSourceOnlineMatchingRoot.exists_root_partOne_access_most_edges
