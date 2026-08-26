/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.SourceMatchingGeometry
import ErdosProblems.Erdos547b.SourceActualChunkEmbedding

/-!
# Actual small-branch chunks on arbitrary reduced matching edges

The source roots and density rows still come from the original certificate;
the physical edge is independent of its old matching. The existing local
threshold proof supplies the copy from literal parent degrees.
-/

open scoped SimpleGraph Classical
noncomputable section

namespace Erdos547b.ZhaoSourceMatchingChunkEmbedding

open Finset SimpleGraph Erdos547b.RegularPair
open Erdos547b.ZhaoSourceDegreeFormRootRows Erdos547b.ZhaoSourceParameterSchedule
open Erdos547b.ZhaoSourceDegreeFormBounds Erdos547b.ZhaoSourceFreshChunkBounds
open Erdos547b.ZhaoSourceMatchingGeometry Erdos547b.ZhaoSourceEmbeddingHost
open Erdos547b.ZhaoSourceFreshChunkEmbedding Erdos547b.ZhaoSourceActualChunkEmbedding
open Erdos547b.ZhaoLemma611Full Erdos547b.ZhaoLemma58GroupedSmallForest
open Erdos547b.ZhaoLemma58ThresholdResidualCapacity Erdos547b.ZhaoEvenReducedPadding

variable {α : ℚ} {hostN q M : ℕ}
variable {G : SimpleGraph (Fin hostN)} [DecidableRel G.Adj]
variable (W : Witness α q M G) (Q : Certificate W) (S : CleanSourceWitness W Q)
variable (P : (padGraph (reduced W)).Subgraph)

theorem exists_partOne_chunk
    (hα : 0 < α) (hα1 : α ≤ 1 / 4)
    (hhost : hostN = 2 * q) (horder : orderThreshold α M ≤ q)
    (C : Index W) (hC : C = Q.A ∨ C = Q.B)
    (e : MatchingEdge P) {b : ℕ} (F : OrderedRootedForest b)
    (parent : Fin b → Fin hostN) (deleted : Fin 2 → Finset (Fin hostN))
    (lowSide highSide : Fin 2) (hsides : highSide ≠ lowSide)
    (hlowHigh : rootDensity W S (Sum.inl C) (pairVertex W P e lowSide) ≤
      rootDensity W S (Sum.inl C) (pairVertex W P e highSide))
    (hsmall : ∀ i, F.size i ≤ freshBranchBound α W.clusterSize)
    (hmass : (F.order : ℝ) ≤
      (rootDensity W S (Sum.inl C) (pairVertex W P e lowSide) +
        rootDensity W S (Sum.inl C) (pairVertex W P e highSide) -
        2 * (gamma α : ℝ) - 3 * (epsilon α : ℝ)) * W.clusterSize)
    (hdeleted : ∀ c, deleted c ⊆ pairWhole W P e c)
    (hdeletedCard : ∀ c, (deleted c).card ≤ freshDeletionBudget α W.clusterSize)
    (hparent : ∀ i c, 0 < rootDensity W S (Sum.inl C) (pairVertex W P e c) →
      (rootDensity W S (Sum.inl C) (pairVertex W P e c) - 2 * (epsilon α : ℝ)) * W.clusterSize ≤
        (#((pairWhole W P e c).filter ((embeddingHost W).Adj (parent i))) : ℝ)) :
    ∃ orient : Fin b → Fin 2 ≃ Fin 2,
      Nonempty (DynamicAttachedForestEmbedding F (embeddingHost W) parent orient
        (residualSide (pairWhole W P e) deleted)) := by
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
  have hpair := pair_regular W P e
  have hsources (c : Fin 2) : rootDensity W S (Sum.inl C) (pairVertex W P e c) =
      if c = lowSide then rootDensity W S (Sum.inl C) (pairVertex W P e lowSide)
      else rootDensity W S (Sum.inl C) (pairVertex W P e highSide) := by
    by_cases hc : c = lowSide
    · rw [if_pos hc, hc]
    · have hch : c = highSide := by
        apply Fin.ext
        have hcl : c.val ≠ lowSide.val := fun h => hc (Fin.ext h)
        have hhl : highSide.val ≠ lowSide.val := fun h => hsides (Fin.ext h)
        omega
      rw [if_neg hc, hch]
  apply exists_partOne_fresh_chunk_embedding F (embeddingHost W) parent (pairWhole W P e) deleted
    W.clusterSize (freshDeletionBudget α W.clusterSize) (freshBranchBound α W.clusterSize)
    (rootDensity W S (Sum.inl C) (pairVertex W P e lowSide))
    (rootDensity W S (Sum.inl C) (pairVertex W P e highSide))
    (gamma α : ℝ) (epsilon α : ℝ) (epsilon α : ℝ) (densityCutoff α : ℝ)
    lowSide highSide hsides W.clusterSize_pos (by exact_mod_cast hγ) hlowHigh
    (source_entry_le_one W Q S C hC _) (by exact_mod_cast hε.le) (by exact_mod_cast hε.le)
    (by exact_mod_cast hεd) hsmall hmass hround (pairWhole_card W P e) hdeleted hdeletedCard
    (pairWhole_disjoint W P e) hpair.1 hpair.2
  · intro i c hpos
    rw [← hsources c] at hpos ⊢
    exact hparent i c hpos
  · exact hparentMargin
  · exact hcomponent

end Erdos547b.ZhaoSourceMatchingChunkEmbedding

#print axioms Erdos547b.ZhaoSourceMatchingChunkEmbedding.exists_partOne_chunk
