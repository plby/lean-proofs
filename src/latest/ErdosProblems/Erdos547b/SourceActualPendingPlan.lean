/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.SourcePendingPairPlan
import ErdosProblems.Erdos547b.SourceParentCleanup
import ErdosProblems.Erdos547b.SourcePendingInterval

/-!
# Sequential pending-pair access on the actual source matching

The degree-form witness supplies every pair and parameter gate. The plan
fixes its orientation once and then extends each literal branch prefix
when that branch's actual outer root has been chosen. No future root map
or graph realization is an input to the plan constructor.
-/

open scoped SimpleGraph Classical
noncomputable section

namespace Erdos547b.ZhaoSourceActualPendingPlan

open Finset SimpleGraph
open Erdos547b.RegularPair Erdos547b.ZhaoStability Erdos547b.ZhaoDegreeForm
open Erdos547b.ZhaoEvenReducedPadding Erdos547b.ZhaoLemma611Full
open Erdos547b.ZhaoSourceParameterSchedule Erdos547b.ZhaoSourceDegreeFormBounds
open Erdos547b.ZhaoSourceDegreeFormRootRows Erdos547b.ZhaoSourceEmbeddingHost
open Erdos547b.ZhaoSourceActualChunkEmbedding Erdos547b.ZhaoSourceOnlineMatchingRoot
open Erdos547b.ZhaoSourceParentCleanup Erdos547b.ZhaoSourceFreshChunkBounds
open Erdos547b.ZhaoSourcePendingPairPlan Erdos547b.ZhaoLemma58GroupedSmallForest
open Erdos547b.ZhaoLemma58DynamicBatchAppend Erdos547b.ZhaoLemma58ThresholdResidualCapacity
open Erdos547b.ZhaoSourcePendingInterval

variable {α : ℚ} {hostN q M : ℕ}
variable {G : SimpleGraph (Fin hostN)} [DecidableRel G.Adj]
variable (W : Witness α q M G) (Q : Certificate W)

structure ActualPendingPlan (S : CleanSourceWitness W Q) (C : Index W)
    (e : MatchingEdge Q.claim67.M) {b : ℕ} (F : OrderedRootedForest b) where
  orient : Fin b → Fin 2 ≃ Fin 2
  root_positive : ∀ i, 0 < rootDensity W S (Sum.inl C) (edgeVertex W Q e (branchRootSide F orient i))
  step : ∀ (i : Fin b) (parent : Fin b → Fin hostN)
    (E : PartialDynamicAttachedForestEmbedding F (embeddingHost W) parent orient
      (residualSide (edgeWhole W Q e) (deleted W Q e)) (Finset.Iio i)) (z : Fin hostN),
    EligibleRoot W Q S C e z →
    ∃ E' : PartialDynamicAttachedForestEmbedding F (embeddingHost W) (Function.update parent i z) orient
        (residualSide (edgeWhole W Q e) (deleted W Q e)) (Finset.Iio i ∪ {i}),
      ∀ j hj, E'.forestCopy.componentCopy j (Finset.mem_union_left _ hj) = E.forestCopy.componentCopy j hj

private theorem exists_ordered_actual_pending_plan
    (hα : 0 < α) (hα1 : α ≤ 1 / 4)
    (hhost : hostN = 2 * q) (horder : orderThreshold α M ≤ q)
    (S : CleanSourceWitness W Q) (C : Index W) (hC : C = Q.A ∨ C = Q.B)
    (e : MatchingEdge Q.claim67.M) {b : ℕ} (F : OrderedRootedForest b)
    (lowSide highSide : Fin 2) (hsides : highSide ≠ lowSide)
    (hlowHigh : rootDensity W S (Sum.inl C) (edgeVertex W Q e lowSide) ≤
      rootDensity W S (Sum.inl C) (edgeVertex W Q e highSide))
    (hsmall : ∀ i, F.size i ≤ freshBranchBound α W.clusterSize)
    (hmass : (F.order : ℝ) ≤
      (rootDensity W S (Sum.inl C) (edgeVertex W Q e lowSide) +
        rootDensity W S (Sum.inl C) (edgeVertex W Q e highSide) -
        2 * (gamma α : ℝ) - 3 * (epsilon α : ℝ)) * W.clusterSize) :
    Nonempty (ActualPendingPlan W Q S C e F) := by
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
  obtain ⟨orient, hpositive, hstep⟩ := exists_pending_pair_plan F (embeddingHost W)
    (edgeWhole W Q e) (deleted W Q e) W.clusterSize (freshDeletionBudget α W.clusterSize)
    (freshBranchBound α W.clusterSize)
    (rootDensity W S (Sum.inl C) (edgeVertex W Q e lowSide))
    (rootDensity W S (Sum.inl C) (edgeVertex W Q e highSide))
    (gamma α : ℝ) (epsilon α : ℝ) (epsilon α : ℝ) (densityCutoff α : ℝ)
    lowSide highSide hsides W.clusterSize_pos (by exact_mod_cast hγ) hlowHigh
    (source_entry_le_one W Q S C hC _) (by exact_mod_cast hε.le) (by exact_mod_cast hε.le)
    (by exact_mod_cast hεd) hsmall hmass hround (edgeWhole_card W Q e)
    (deleted_subset W Q e) (card_deleted_le W Q hα hα1 e) (edgeWhole_disjoint W Q e)
    hpair.1 hpair.2 hparentMargin hcomponent
  refine ⟨⟨orient, ?_, ?_⟩⟩
  · intro i
    rw [hsources]
    exact hpositive i
  · intro i parent E z hz
    apply hstep i parent E z
    intro c hp
    rw [← hsources c] at hp ⊢
    exact hz c hp

/-- The actual Part-1 capacity supplies a fixed pending plan. Every
eligible root may be revealed only when its next branch is processed. -/
theorem exists_actual_pending_plan
    (hα : 0 < α) (hα1 : α ≤ 1 / 4)
    (hhost : hostN = 2 * q) (horder : orderThreshold α M ≤ q)
    (S : CleanSourceWitness W Q) (C : Index W) (hC : C = Q.A ∨ C = Q.B)
    (e : MatchingEdge Q.claim67.M) {b : ℕ} (F : OrderedRootedForest b)
    (hsmall : ∀ i, F.size i ≤ freshBranchBound α W.clusterSize)
    (hmass : (F.order : ℝ) ≤ partOneCapacity W Q S C e) :
    Nonempty (ActualPendingPlan W Q S C e F) := by
  by_cases hle : rootDensity W S (Sum.inl C) (edgeVertex W Q e 0) ≤
      rootDensity W S (Sum.inl C) (edgeVertex W Q e 1)
  · exact exists_ordered_actual_pending_plan W Q hα hα1 hhost horder S C hC e F
      0 1 (by decide) hle hsmall hmass
  · apply exists_ordered_actual_pending_plan W Q hα hα1 hhost horder S C hC e F
      1 0 (by decide) (le_of_not_ge hle) hsmall
    rw [partOneCapacity,
      add_comm (rootDensity W S (Sum.inl C) (edgeVertex W Q e 0))
        (rootDensity W S (Sum.inl C) (edgeVertex W Q e 1))] at hmass
    exact hmass

/-- Once this owner's root is chosen, extend its consecutive branch
interval in the actual cleaned pair, preserving all earlier copies. -/
theorem ActualPendingPlan.extend_interval
    {S : CleanSourceWitness W Q} {C : Index W} {e : MatchingEdge Q.claim67.M}
    {b : ℕ} {F : OrderedRootedForest b} (P : ActualPendingPlan W Q S C e F)
    (parent : Fin b → Fin hostN) (lo hi : ℕ) (hle : lo ≤ hi) (hhi : hi ≤ b)
    (E : PartialDynamicAttachedForestEmbedding F (embeddingHost W) parent P.orient
      (residualSide (edgeWhole W Q e) (deleted W Q e)) (branchPrefix lo))
    (z : Fin hostN) (hz : EligibleRoot W Q S C e z)
    (hparent : ∀ i : Fin b, lo ≤ i.val → i.val < hi → parent i = z) :
    ∃ E' : PartialDynamicAttachedForestEmbedding F (embeddingHost W) parent P.orient
        (residualSide (edgeWhole W Q e) (deleted W Q e)) (branchPrefix hi),
      ∀ j hj, E'.forestCopy.componentCopy j (branchPrefix_mono hle hj) =
        E.forestCopy.componentCopy j hj := by
  exact exists_interval_extension F (embeddingHost W) parent P.orient
    (residualSide (edgeWhole W Q e) (deleted W Q e)) z
    (fun i p E => P.step i p E z hz) lo hi hle hhi E hparent

end Erdos547b.ZhaoSourceActualPendingPlan

#print axioms Erdos547b.ZhaoSourceActualPendingPlan.exists_actual_pending_plan
#print axioms Erdos547b.ZhaoSourceActualPendingPlan.ActualPendingPlan.extend_interval
