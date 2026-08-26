/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.SourceFreshChunkBounds
import ErdosProblems.Erdos547b.SourceEmbeddingHost

/-!
# Part-1 chunks on actual source matching edges

The cluster sizes, disjointness, regularity, density cutoff, and numerical
gates are supplied by the degree-form construction. Remaining inputs are
the branch mass, actual prescribed-root degrees, and the literal permanent
deletion sets used by the online embedding.
-/

open scoped SimpleGraph Classical
noncomputable section

namespace Erdos547b.ZhaoSourceActualChunkEmbedding

open Finset SimpleGraph
open Erdos547b.RegularPair Erdos547b.ZhaoStability Erdos547b.ZhaoDegreeForm
open Erdos547b.ZhaoSection6Dichotomy Erdos547b.ZhaoEvenReducedPadding
open Erdos547b.ZhaoLemma611Full Erdos547b.ZhaoRichClaim61Lemma611
open Erdos547b.ZhaoSourceParameterSchedule Erdos547b.ZhaoSourceDegreeFormBounds
open Erdos547b.ZhaoSourceDegreeFormRootRows Erdos547b.ZhaoSourceEmbeddingHost
open Erdos547b.ZhaoSourceFreshChunkEmbedding Erdos547b.ZhaoSourceFreshChunkBounds
open Erdos547b.ZhaoLemma58GroupedSmallForest Erdos547b.ZhaoLemma58ThresholdResidualCapacity

variable {α : ℚ} {hostN q M : ℕ}
variable {G : SimpleGraph (Fin hostN)} [DecidableRel G.Adj]
variable (W : Witness α q M G) (Q : Certificate W)

abbrev edgeVertex (e : MatchingEdge Q.claim67.M) (c : Fin 2) :=
  orientedEndpoint Q.claim67.M (padFinset (large W)) e c

abbrev edgeWhole (e : MatchingEdge Q.claim67.M) (c : Fin 2) :=
  padCluster (clusterVertices (assignment W)) (edgeVertex W Q e c)

theorem edge_pair_adj (e : MatchingEdge Q.claim67.M) :
    (padGraph (reduced W)).Adj (edgeVertex W Q e 0) (edgeVertex W Q e 1) :=
  Q.claim67.M.adj_sub (orientedEndpoint_adj Q.claim67.M (padFinset (large W)) e)

theorem edgeWhole_card (e : MatchingEdge Q.claim67.M) (c : Fin 2) :
    (edgeWhole W Q e c).card = W.clusterSize := by
  have hreal {x y : EvenPadding (Index W)} (hxy : (padGraph (reduced W)).Adj x y) :
      ∃ i : Index W, x = Sum.inl i := by
    cases x with
    | inl i => exact ⟨i, rfl⟩
    | inr d => exact (padGraph_not_adj_inr_left (reduced W) d y hxy).elim
  have hvertex : ∃ i : Index W, edgeVertex W Q e c = Sum.inl i := by
    rcases OrderedRootedForest.fin_two_eq_zero_or_one c with rfl | rfl
    · exact hreal (edge_pair_adj W Q e)
    · exact hreal (edge_pair_adj W Q e).symm
  obtain ⟨i, hi⟩ := hvertex
  change (padCluster (clusterVertices (assignment W)) (edgeVertex W Q e c)).card = _
  rw [hi]
  change (clusterVertices (assignment W) i).card = _
  rw [clusterVertices_partitionAssignment]
  exact W.equal_clusters i.1 i.2

theorem edgeWhole_disjoint (e : MatchingEdge Q.claim67.M) :
    Disjoint (edgeWhole W Q e 0) (edgeWhole W Q e 1) := by
  have hne := (edge_pair_adj W Q e).ne
  have h := clusterVertices_disjoint (padAssignment (assignment W)) hne
  simpa only [clusterVertices_padAssignment] using h

theorem source_entry_le_one (S : CleanSourceWitness W Q) (C : Index W)
    (hC : C = Q.A ∨ C = Q.B) (x : EvenPadding (Index W)) :
    rootDensity W S (Sum.inl C) x ≤ 1 := by
  have hN : (0 : ℝ) < W.clusterSize := by exact_mod_cast W.clusterSize_pos
  have hcard : (padCluster (fun i : Index W => i.1) x).card ≤ W.clusterSize := by
    cases x with
    | inl i => exact (W.equal_clusters i.1 i.2).le
    | inr d => simp [padCluster]
  have hrow (z : Fin hostN) :
      rootedSourceDensity S.source (padCluster (fun i : Index W => i.1)) W.clusterSize z x ≤ 1 := by
    apply (div_le_one hN).mpr
    exact_mod_cast (Finset.card_filter_le _ _).trans hcard
  rcases hC with rfl | rfl
  · rw [rootDensity, twoRootSourceDensity_row_A]
    exact hrow S.zA
  · have hAB : (Sum.inl Q.A : EvenPadding (Index W)) ≠ Sum.inl Q.B := by
      exact fun h => Q.adj.ne (Sum.inl.inj h)
    rw [rootDensity, twoRootSourceDensity_row_B _ _ _ _ _ _ _ hAB]
    exact hrow S.zB

/-- The actual source matching instantiates the concrete Part-1 graph
embedding. Neither regular-pair facts nor scalar gates are extra inputs. -/
theorem exists_actual_partOne_chunk
    (hα : 0 < α) (hα1 : α ≤ 1 / 4)
    (hhost : hostN = 2 * q) (horder : orderThreshold α M ≤ q)
    (S : CleanSourceWitness W Q) (C : Index W) (hC : C = Q.A ∨ C = Q.B)
    (e : MatchingEdge Q.claim67.M) {b : ℕ} (F : OrderedRootedForest b)
    (parent : Fin b → Fin hostN) (deleted : Fin 2 → Finset (Fin hostN))
    (lowSide highSide : Fin 2) (hsides : highSide ≠ lowSide)
    (hlowHigh : rootDensity W S (Sum.inl C) (edgeVertex W Q e lowSide) ≤
      rootDensity W S (Sum.inl C) (edgeVertex W Q e highSide))
    (hsmall : ∀ i, F.size i ≤ freshBranchBound α W.clusterSize)
    (hmass : (F.order : ℝ) ≤
      (rootDensity W S (Sum.inl C) (edgeVertex W Q e lowSide) +
        rootDensity W S (Sum.inl C) (edgeVertex W Q e highSide) -
        2 * (gamma α : ℝ) - 3 * (epsilon α : ℝ)) * W.clusterSize)
    (hdeleted : ∀ c, deleted c ⊆ edgeWhole W Q e c)
    (hdeletedCard : ∀ c, (deleted c).card ≤ freshDeletionBudget α W.clusterSize)
    (hparent : ∀ i c, 0 < rootDensity W S (Sum.inl C) (edgeVertex W Q e c) →
      (rootDensity W S (Sum.inl C) (edgeVertex W Q e c) - 2 * (epsilon α : ℝ)) * W.clusterSize ≤
        (#((edgeWhole W Q e c).filter ((embeddingHost W).Adj (parent i))) : ℝ)) :
    ∃ orient : Fin b → Fin 2 ≃ Fin 2,
      Nonempty (DynamicAttachedForestEmbedding F (embeddingHost W) parent orient
        (residualSide (edgeWhole W Q e) deleted)) := by
  subst hostN
  obtain ⟨_, hround, hparentMargin, hcomponent⟩ := degreeForm_fresh_chunk_gates hα hα1 W horder
  obtain ⟨_, _, _, _, _, hd, hγ, hε⟩ := parameter_pos hα
  have hγOne : gamma α ≤ 1 := by
    have hγd := (parameter_upper_bounds hα hα1).2.2.2.2.2.1
    have hdOne := (reservoir_cleanup_bounds hα hα1).2.2.2.2.2
    linarith only [hγd, hdOne]
  have hεd : epsilon α ≤ densityCutoff α := by
    have hp := regularity_product_margin hα hα1
    have hm := mul_le_mul_of_nonneg_left hγOne hd.le
    linarith only [hp, hm, hε]
  have hpair := (embedding_pair_realization W).pair_of_adj _ _ (edge_pair_adj W Q e)
  have hsources (c : Fin 2) : rootDensity W S (Sum.inl C) (edgeVertex W Q e c) =
      if c = lowSide then rootDensity W S (Sum.inl C) (edgeVertex W Q e lowSide)
      else rootDensity W S (Sum.inl C) (edgeVertex W Q e highSide) := by
    by_cases hc : c = lowSide
    · rw [if_pos hc, hc]
    · have hch : c = highSide := by
        apply Fin.ext
        have hcl : c.val ≠ lowSide.val := fun h => hc (Fin.ext h)
        have hhl : highSide.val ≠ lowSide.val := fun h => hsides (Fin.ext h)
        omega
      rw [if_neg hc, hch]
  apply exists_partOne_fresh_chunk_embedding F (embeddingHost W) parent (edgeWhole W Q e) deleted
    W.clusterSize (freshDeletionBudget α W.clusterSize) (freshBranchBound α W.clusterSize)
    (rootDensity W S (Sum.inl C) (edgeVertex W Q e lowSide))
    (rootDensity W S (Sum.inl C) (edgeVertex W Q e highSide))
    (gamma α : ℝ) (epsilon α : ℝ) (epsilon α : ℝ) (densityCutoff α : ℝ)
    lowSide highSide hsides W.clusterSize_pos (by exact_mod_cast hγ) hlowHigh
    (source_entry_le_one W Q S C hC _) (by exact_mod_cast hε.le) (by exact_mod_cast hε.le)
    (by exact_mod_cast hεd) hsmall hmass hround (edgeWhole_card W Q e) hdeleted hdeletedCard
    (edgeWhole_disjoint W Q e) hpair.1 hpair.2
  · intro i c hpos
    rw [← hsources c] at hpos ⊢
    exact hparent i c hpos
  · exact hparentMargin
  · exact hcomponent

end Erdos547b.ZhaoSourceActualChunkEmbedding

#print axioms Erdos547b.ZhaoSourceActualChunkEmbedding.edgeWhole_card
#print axioms Erdos547b.ZhaoSourceActualChunkEmbedding.edgeWhole_disjoint
#print axioms Erdos547b.ZhaoSourceActualChunkEmbedding.source_entry_le_one
#print axioms Erdos547b.ZhaoSourceActualChunkEmbedding.exists_actual_partOne_chunk
