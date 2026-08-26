/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.SourcePartThreeUnorderedStep
import ErdosProblems.Erdos547b.SourceActualPartTwoPlan

/-!
# The live Part-3 step on the literal degree-form matching

All regular-pair and component margins are supplied by the existing source
schedule. The new root predicate explicitly tests the current live sets.
Nonextreme source entries preserve positive support at every branch root.
The current endpoint order is chosen locally, not imposed on the stored state.
-/

open scoped SimpleGraph Classical
noncomputable section

namespace Erdos547b.ZhaoSourceActualPartThreeStep

open Finset SimpleGraph Erdos547b.RegularPair
open Erdos547b.ZhaoLemma611Full Erdos547b.ZhaoLemma58GroupedSmallForest
open Erdos547b.ZhaoSourceDegreeFormRootRows Erdos547b.ZhaoSourceDegreeFormBounds
open Erdos547b.ZhaoSourceParameterSchedule Erdos547b.ZhaoSourceFreshChunkBounds
open Erdos547b.ZhaoSourceEmbeddingHost Erdos547b.ZhaoSourceActualChunkEmbedding
open Erdos547b.ZhaoSourcePartThreeResidualNumerics Erdos547b.ZhaoSourcePartThreeLiveStep

variable {α : ℚ} {hostN q M : ℕ}
variable {G : SimpleGraph (Fin hostN)} [DecidableRel G.Adj]
variable (W : Witness α q M G) (Q : Certificate W)

/-- This is a live-set degree test, distinct from whole-pair eligibility. -/
def EligibleLiveRoot (S : CleanSourceWitness W Q) (C : Index W)
    (e : MatchingEdge Q.claim67.M) (live : Fin 2 → Finset (Fin hostN)) (z : Fin hostN) : Prop :=
  ∀ c, (rootDensity W S (Sum.inl C) (edgeVertex W Q e c) - 2 * (epsilon α : ℝ)) *
    (live c).card ≤ (#((live c).filter ((embeddingHost W).Adj z)) : ℝ)

/-- The source schedule constructs one genuine nonextreme owner-batch
embedding and retains the actual residual invariant and positive support. -/
theorem exists_actual_partThree_step
    (hα : 0 < α) (hα1 : α ≤ 1 / 4)
    (hhost : hostN = 2 * q) (horder : orderThreshold α M ≤ q)
    (S : CleanSourceWitness W Q) (C : Index W) (e : MatchingEdge Q.claim67.M)
    {b : ℕ} (F : OrderedRootedForest b) (live : Fin 2 → Finset (Fin hostN))
    (lambda : ℝ) (hlambda : (densityCutoff α : ℝ) ≤ lambda) (hlambdaHalf : lambda ≤ 1 / 2)
    (hsource : ∀ c, lambda ≤ rootDensity W S (Sum.inl C) (edgeVertex W Q e c) ∧
      rootDensity W S (Sum.inl C) (edgeVertex W Q e c) ≤ 1 - lambda)
    (hlive : ∀ c, live c ⊆ edgeWhole W Q e c)
    (hinv : ResidualInvariant
      (rootDensity W S (Sum.inl C) (edgeVertex W Q e 0))
      (rootDensity W S (Sum.inl C) (edgeVertex W Q e 1))
      W.clusterSize ((epsilon α : ℝ) * W.clusterSize)
      ((W.clusterSize : ℝ) - (live 0).card) ((W.clusterSize : ℝ) - (live 1).card))
    (hbudget : ((W.clusterSize : ℝ) - (live 0).card) +
      ((W.clusterSize : ℝ) - (live 1).card) + F.order ≤
      (rootDensity W S (Sum.inl C) (edgeVertex W Q e 0) +
        rootDensity W S (Sum.inl C) (edgeVertex W Q e 1) + lambda) * W.clusterSize -
          2 * ((gamma α : ℝ) * W.clusterSize) - 24 * ((epsilon α : ℝ) * W.clusterSize))
    (hlower : ∀ i, 2 ≤ F.size i)
    (hsmall : ∀ i, F.size i ≤ freshBranchBound α W.clusterSize)
    (z : Fin hostN) (hz : EligibleLiveRoot W Q S C e live z) :
    ∃ orient : Fin b → Fin 2 ≃ Fin 2,
      ∃ E : DynamicAttachedForestEmbedding F (embeddingHost W) (fun _ => z) orient live,
        ResidualInvariant
          (rootDensity W S (Sum.inl C) (edgeVertex W Q e 0))
          (rootDensity W S (Sum.inl C) (edgeVertex W Q e 1))
          W.clusterSize ((epsilon α : ℝ) * W.clusterSize)
          ((W.clusterSize : ℝ) - (live 0 \ E.used 0).card)
          ((W.clusterSize : ℝ) - (live 1 \ E.used 1).card) ∧
        ∀ i, 0 < rootDensity W S (Sum.inl C) (edgeVertex W Q e (orient i 0)) := by
  subst hostN
  have hscale := (epsilon_mul_clusterSize_gt_two hα hα1 W horder).le
  have hg : (0 : ℝ) < gamma α := by exact_mod_cast (parameter_pos hα).2.2.2.2.2.2.1
  have he : (0 : ℝ) < epsilon α := by exact_mod_cast (parameter_pos hα).2.2.2.2.2.2.2
  have hd : (0 : ℝ) < densityCutoff α := by exact_mod_cast (parameter_pos hα).2.2.2.2.2.1
  have hlambdaPos : 0 < lambda := hd.trans_le hlambda
  have hN : (0 : ℝ) ≤ W.clusterSize := Nat.cast_nonneg _
  have heγ : epsilon α ≤ gamma α := by
    have h := (parameter_upper_bounds hα hα1).2.2.2.2.2.2
    have hgQ := (parameter_pos hα).2.2.2.2.2.2.1
    linarith only [h, hgQ]
  have hγOne : gamma α ≤ 1 := by
    have h := (parameter_upper_bounds hα hα1).2.2.2.2.2.1
    have hdOne := (reservoir_cleanup_bounds hα hα1).2.2.2.2.2
    linarith only [h, hdOne]
  have hp : 10 * (epsilon α : ℝ) < (densityCutoff α : ℝ) * (gamma α : ℝ) := by
    exact_mod_cast regularity_product_margin hα hα1
  have heCut : (epsilon α : ℝ) ≤ densityCutoff α := by
    have hγOneR : (gamma α : ℝ) ≤ 1 := by exact_mod_cast hγOne
    have hm := mul_le_mul_of_nonneg_left hγOneR hd.le
    nlinarith only [hp, hm, he]
  have hfactor : 0 ≤ (densityCutoff α : ℝ) - (epsilon α : ℝ) := sub_nonneg.mpr heCut
  have hgate : 8 * (epsilon α : ℝ) ≤ lambda * (gamma α : ℝ) := by
    have hm := mul_le_mul_of_nonneg_right hlambda hg.le
    linarith only [hp, hm, he]
  have hdegree (c : Fin 2) :
      rootDensity W S (Sum.inl C) (edgeVertex W Q e c) * (live c).card -
        2 * ((epsilon α : ℝ) * W.clusterSize) ≤
          (#((live c).filter ((embeddingHost W).Adj z)) : ℝ) := by
    have hliveN : ((live c).card : ℝ) ≤ W.clusterSize := by
      exact_mod_cast (Finset.card_le_card (hlive c)).trans_eq (edgeWhole_card W Q e c)
    have hm := mul_le_mul_of_nonneg_left hliveN he.le
    nlinarith only [hz c, hm]
  have hcomponent (i : Fin b) : (F.size i : ℝ) + (epsilon α : ℝ) * W.clusterSize ≤
      ((densityCutoff α : ℝ) - (epsilon α : ℝ)) * ((gamma α : ℝ) * W.clusterSize) := by
    have hs : (F.size i : ℝ) ≤ freshBranchBound α W.clusterSize := by exact_mod_cast hsmall i
    have hlocal := (degreeForm_fresh_chunk_gates hα hα1 W horder).2.2.2
    have hm := mul_le_mul_of_nonneg_left
      (sub_le_self ((gamma α : ℝ) * W.clusterSize) (Nat.cast_nonneg (freshDeletionBudget α W.clusterSize))) hfactor
    linarith only [hs, hlocal, hm]
  have hpair := (embedding_pair_realization W).pair_of_adj _ _ (edge_pair_adj W Q e)
  obtain ⟨orient, E, hnew⟩ := exists_partThree_live_step_unordered F (embeddingHost W) z
    (edgeWhole W Q e) live W.clusterSize (freshBranchBound α W.clusterSize)
    (gamma α : ℝ) (epsilon α : ℝ) (epsilon α : ℝ) (densityCutoff α : ℝ)
    lambda (rootDensity W S (Sum.inl C) (edgeVertex W Q e 0))
    (rootDensity W S (Sum.inl C) (edgeVertex W Q e 1))
    hscale hg.le hlambdaPos.le hlambdaHalf (hsource 0).1 (hsource 0).2 (hsource 1).1 (hsource 1).2
    hgate (edgeWhole_card W Q e) hlive (hdegree 0) (hdegree 1) hinv hbudget hlower hsmall
    (Nat.floor_le (by positivity)) hpair.1 (edgeWhole_disjoint W Q e) hpair.2 hfactor
    (by nlinarith only [hscale])
    (by exact_mod_cast mul_le_mul_of_nonneg_right heγ (Nat.cast_nonneg W.clusterSize : (0 : ℚ) ≤ W.clusterSize))
    hcomponent
  exact ⟨orient, E, hnew, fun i => hlambdaPos.trans_le (hsource (orient i 0)).1⟩

end Erdos547b.ZhaoSourceActualPartThreeStep

#print axioms Erdos547b.ZhaoSourceActualPartThreeStep.exists_actual_partThree_step
