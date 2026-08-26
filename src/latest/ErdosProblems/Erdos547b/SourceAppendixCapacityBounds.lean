/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.SourceFamilyCapacity
import ErdosProblems.Erdos547b.SourcePartialUsedCard

/-!
# The Appendix chunk capacity pays every actual prefix budget

Permanent deletions cost at most six epsilon-cluster orders in total.
Exact partial image counts and source disjointness then supply the current
batch budget, and the root-selection size gate follows before root choice.
-/

open scoped SimpleGraph BigOperators Classical
noncomputable section

namespace Erdos547b.ZhaoSourceAppendixCapacityBounds

open Finset SimpleGraph Erdos547b.RegularPair
open Erdos547b.ZhaoLemma611Full Erdos547b.ZhaoSourceDegreeFormRootRows
open Erdos547b.ZhaoSourceParameterSchedule Erdos547b.ZhaoSourceDegreeFormBounds
open Erdos547b.ZhaoSourceActualChunkEmbedding Erdos547b.ZhaoSourceEmbeddingHost
open Erdos547b.ZhaoSourceParentCleanup Erdos547b.ZhaoSourceFreshChunkBounds
open Erdos547b.ZhaoSourceFamilyCapacity Erdos547b.ZhaoLemma58ThresholdResidualCapacity
open Erdos547b.ZhaoLemma58DynamicBatchAppend Erdos547b.ZhaoSourcePartThreeResidualNumerics

variable {α : ℚ} {hostN q M : ℕ}
variable {G : SimpleGraph (Fin hostN)} [DecidableRel G.Adj]
variable (W : Witness α q M G) (Q : Certificate W)

theorem card_deleted_le_three_error (hα : 0 < α) (hα1 : α ≤ 1 / 4)
    (hhost : hostN = 2 * q) (horder : orderThreshold α M ≤ q)
    (e : MatchingEdge Q.claim67.M) (c : Fin 2) :
    ((deleted W Q e c).card : ℝ) ≤ 3 * ((epsilon α : ℝ) * W.clusterSize) := by
  subst hostN
  have hscale := (epsilon_mul_clusterSize_gt_two hα hα1 W horder).le
  have he : (0 : ℝ) < epsilon α := by exact_mod_cast (parameter_pos hα).2.2.2.2.2.2.2
  have hcard : ((deleted W Q e c).card : ℝ) ≤ freshDeletionBudget α W.clusterSize := by
    exact_mod_cast card_deleted_le W Q hα hα1 e c
  have hc := Nat.ceil_lt_add_one (show 0 ≤ 2 * (epsilon α : ℝ) * W.clusterSize by positivity)
  unfold freshDeletionBudget at hcard
  nlinarith only [hcard, hc, hscale]

/-- The conservative fresh capacity pays the effective live budget for
any next batch disjoint from the actually copied source indices. -/
theorem effective_batch_budget (hα : 0 < α) (hα1 : α ≤ 1 / 4)
    (hhost : hostN = 2 * q) (horder : orderThreshold α M ≤ q)
    (S : CleanSourceWitness W Q) (C : Index W) (e : MatchingEdge Q.claim67.M)
    (lambda : ℝ) {b : ℕ} (F : OrderedRootedForest b)
    (hfits : (F.order : ℝ) ≤ capacity W Q S C (.appendix lambda) e)
    (parent : Fin b → Fin hostN) (orient : Fin b → Fin 2 ≃ Fin 2) (selected batch : Finset (Fin b))
    (E : PartialDynamicAttachedForestEmbedding F (embeddingHost W) parent orient
      (residualSide (edgeWhole W Q e) (deleted W Q e)) selected)
    (hdisjoint : Disjoint selected batch) :
    ((W.clusterSize : ℝ) - (residualSide (edgeWhole W Q e) (deleted W Q e) 0 \ E.used 0).card) +
      ((W.clusterSize : ℝ) - (residualSide (edgeWhole W Q e) (deleted W Q e) 1 \ E.used 1).card) +
      (∑ i ∈ batch, F.size i : ℕ) ≤
      (rootDensity W S (Sum.inl C) (edgeVertex W Q e 0) +
        rootDensity W S (Sum.inl C) (edgeVertex W Q e 1) + lambda) * W.clusterSize -
          2 * ((gamma α : ℝ) * W.clusterSize) - 24 * ((epsilon α : ℝ) * W.clusterSize) := by
  have hmass := E.occupied_add_batch_le (edgeWhole W Q e) (deleted W Q e) W.clusterSize
    (edgeWhole_card W Q e) (deleted_subset W Q e) batch hdisjoint
  have h0 := card_deleted_le_three_error W Q hα hα1 hhost horder e 0
  have h1 := card_deleted_le_three_error W Q hα hα1 hhost horder e 1
  change (F.order : ℝ) ≤
    (rootDensity W S (Sum.inl C) (edgeVertex W Q e 0) +
      rootDensity W S (Sum.inl C) (edgeVertex W Q e 1) + lambda -
      2 * (gamma α : ℝ) - 30 * (epsilon α : ℝ)) * W.clusterSize at hfits
  change ((W.clusterSize : ℝ) - ((edgeWhole W Q e 0 \ deleted W Q e 0) \ E.used 0).card) +
    ((W.clusterSize : ℝ) - ((edgeWhole W Q e 1 \ deleted W Q e 1) \ E.used 1).card) + _ ≤ _
  exact hmass.trans (by nlinarith only [hfits, h0, h1])

/-- The actual prefix's source budget and trichotomy supply both live
regularity gates without a degree hypothesis on an unchosen current root. -/
theorem live_large_before_root (hα : 0 < α) (hα1 : α ≤ 1 / 4)
    (hhost : hostN = 2 * q) (horder : orderThreshold α M ≤ q)
    (S : CleanSourceWitness W Q) (C : Index W) (e : MatchingEdge Q.claim67.M)
    (lambda : ℝ) (hkind : (FamilyKind.appendix lambda).Valid α)
    (hedge : edgeValid W Q S C (.appendix lambda) e)
    {b : ℕ} (F : OrderedRootedForest b)
    (hfits : (F.order : ℝ) ≤ capacity W Q S C (.appendix lambda) e)
    (parent : Fin b → Fin hostN) (orient : Fin b → Fin 2 ≃ Fin 2) (selected : Finset (Fin b))
    (E : PartialDynamicAttachedForestEmbedding F (embeddingHost W) parent orient
      (residualSide (edgeWhole W Q e) (deleted W Q e)) selected)
    (hinv : ResidualInvariant
      (rootDensity W S (Sum.inl C) (edgeVertex W Q e 0))
      (rootDensity W S (Sum.inl C) (edgeVertex W Q e 1))
      W.clusterSize ((epsilon α : ℝ) * W.clusterSize)
      ((W.clusterSize : ℝ) - (residualSide (edgeWhole W Q e) (deleted W Q e) 0 \ E.used 0).card)
      ((W.clusterSize : ℝ) - (residualSide (edgeWhole W Q e) (deleted W Q e) 1 \ E.used 1).card)) :
    ∀ c, (epsilon α : ℝ) * W.clusterSize ≤
      (residualSide (edgeWhole W Q e) (deleted W Q e) c \ E.used c).card := by
  let live := fun c => residualSide (edgeWhole W Q e) (deleted W Q e) c \ E.used c
  have hbudget := effective_batch_budget W Q hα hα1 hhost horder S C e lambda F hfits
    parent orient selected ∅ E (by simp)
  simp only [Finset.sum_empty, Nat.cast_zero, add_zero] at hbudget
  have hN : (0 : ℝ) ≤ W.clusterSize := Nat.cast_nonneg _
  have herror : 0 ≤ (epsilon α : ℝ) * W.clusterSize := by
    have he : (0 : ℝ) < epsilon α := by exact_mod_cast (parameter_pos hα).2.2.2.2.2.2.2
    positivity
  have hcard (c : Fin 2) : ((live c).card : ℝ) ≤ W.clusterSize := by
    exact_mod_cast (Finset.card_le_card (Finset.sdiff_subset.trans (Finset.sdiff_subset :
      residualSide (edgeWhole W Q e) (deleted W Q e) c ⊆ edgeWhole W Q e c))).trans_eq (edgeWhole_card W Q e c)
  have hlambda : 0 ≤ lambda := by
    have hd : (0 : ℝ) < densityCutoff α := by exact_mod_cast (parameter_pos hα).2.2.2.2.2.1
    exact hd.le.trans hkind.1
  have hres := live_reserve_of_source_budget W.clusterSize lambda
    (rootDensity W S (Sum.inl C) (edgeVertex W Q e 0))
    (rootDensity W S (Sum.inl C) (edgeVertex W Q e 1))
    ((epsilon α : ℝ) * W.clusterSize) ((gamma α : ℝ) * W.clusterSize)
    ((W.clusterSize : ℝ) - (live 0).card) ((W.clusterSize : ℝ) - (live 1).card) 0
    hN hlambda herror (hedge 0).1 (hedge 0).2 (hedge 1).1 (hedge 1).2
    (sub_nonneg.mpr (hcard 0)) (sub_le_self _ (Nat.cast_nonneg _))
    (sub_nonneg.mpr (hcard 1)) (sub_le_self _ (Nat.cast_nonneg _)) le_rfl hinv
    (by simpa only [add_zero] using hbudget)
  simp only [sub_sub_cancel] at hres
  have heγ : (epsilon α : ℝ) ≤ gamma α := by
    have h := (parameter_upper_bounds hα hα1).2.2.2.2.2.2
    have hg := (parameter_pos hα).2.2.2.2.2.2.1
    have hQ : epsilon α ≤ gamma α := by linarith only [h, hg]
    exact_mod_cast hQ
  have hm := mul_le_mul_of_nonneg_right heγ hN
  intro c
  rcases OrderedRootedForest.fin_two_eq_zero_or_one c with rfl | rfl
  · exact hm.trans hres.1
  · exact hm.trans hres.2

end Erdos547b.ZhaoSourceAppendixCapacityBounds

#print axioms Erdos547b.ZhaoSourceAppendixCapacityBounds.card_deleted_le_three_error
#print axioms Erdos547b.ZhaoSourceAppendixCapacityBounds.effective_batch_budget
#print axioms Erdos547b.ZhaoSourceAppendixCapacityBounds.live_large_before_root
