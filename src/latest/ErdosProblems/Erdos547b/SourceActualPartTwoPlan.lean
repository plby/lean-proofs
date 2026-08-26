/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.SourceClassifiedPendingPlan

/-!
# Balanced-branch pending access on the literal source matching

The Part-2 capacity gain is retained in the actual graph constructor.
Every parameter gate comes from the same degree-form witness as Part 1.
The resulting plan uses only the original positive-entry root tests.
-/

open scoped SimpleGraph Classical
noncomputable section

namespace Erdos547b.ZhaoSourceActualPartTwoPlan

open Finset SimpleGraph
open Erdos547b.RegularPair Erdos547b.ZhaoStability Erdos547b.ZhaoDegreeForm
open Erdos547b.ZhaoEvenReducedPadding Erdos547b.ZhaoLemma611Full
open Erdos547b.ZhaoSourceParameterSchedule Erdos547b.ZhaoSourceDegreeFormBounds
open Erdos547b.ZhaoSourceDegreeFormRootRows Erdos547b.ZhaoSourceEmbeddingHost
open Erdos547b.ZhaoSourceActualChunkEmbedding Erdos547b.ZhaoSourceOnlineMatchingRoot
open Erdos547b.ZhaoSourceParentCleanup Erdos547b.ZhaoSourceFreshChunkBounds
open Erdos547b.ZhaoLemma58GroupedSmallForest Erdos547b.ZhaoLemma54ThresholdSourceNumerics
open Erdos547b.ZhaoSourceActualPendingPlan Erdos547b.ZhaoSourceClassifiedPendingPlan

variable {α : ℚ} {hostN q M : ℕ}
variable {G : SimpleGraph (Fin hostN)} [DecidableRel G.Adj]
variable (W : Witness α q M G) (Q : Certificate W)

/-- The symmetric form of the genuine Part-2 pair capacity. -/
def partTwoCapacity (S : CleanSourceWitness W Q) (C : Index W) (ratio : ℝ)
    (e : MatchingEdge Q.claim67.M) : ℝ :=
  partOneCapacity W Q S C e + ratio / (1 - ratio) *
    |rootDensity W S (Sum.inl C) (edgeVertex W Q e 1) -
      rootDensity W S (Sum.inl C) (edgeVertex W Q e 0)| * W.clusterSize

/-- A classified threshold display on this exact edge constructs an
actual pending plan, with no predetermined future outer roots. -/
theorem exists_actual_pending_plan_of_numerics
    (hα : 0 < α) (hα1 : α ≤ 1 / 4)
    (hhost : hostN = 2 * q) (horder : orderThreshold α M ≤ q)
    (S : CleanSourceWitness W Q) (C : Index W) (hC : C = Q.A ∨ C = Q.B)
    (e : MatchingEdge Q.claim67.M) {b : ℕ} (F : OrderedRootedForest b)
    (ratio : ℝ) (lowSide highSide : Fin 2) (hsides : highSide ≠ lowSide)
    (D : ClassifiedThresholdOwnerNumerics F ratio
      (rootDensity W S (Sum.inl C) (edgeVertex W Q e lowSide))
      (rootDensity W S (Sum.inl C) (edgeVertex W Q e highSide))
      (gamma α : ℝ) (epsilon α : ℝ) W.clusterSize (freshBranchBound α W.clusterSize)) :
    Nonempty (ActualPendingPlan W Q S C e F) := by
  subst hostN
  obtain ⟨_, _, hparentMargin, hcomponent⟩ := degreeForm_fresh_chunk_gates hα hα1 W horder
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
  obtain ⟨orient, hpositive, hstep⟩ := exists_pending_pair_plan_of_numerics F (embeddingHost W)
    (edgeWhole W Q e) (deleted W Q e) W.clusterSize (freshDeletionBudget α W.clusterSize)
    (freshBranchBound α W.clusterSize) ratio
    (rootDensity W S (Sum.inl C) (edgeVertex W Q e lowSide))
    (rootDensity W S (Sum.inl C) (edgeVertex W Q e highSide))
    (gamma α : ℝ) (epsilon α : ℝ) (epsilon α : ℝ) (densityCutoff α : ℝ)
    lowSide highSide hsides D W.clusterSize_pos (by exact_mod_cast hγ)
    (source_entry_le_one W Q S C hC _) (by exact_mod_cast hε.le) (by exact_mod_cast hεd)
    (edgeWhole_card W Q e) (deleted_subset W Q e) (card_deleted_le W Q hα hα1 e)
    (edgeWhole_disjoint W Q e) hpair.1 hpair.2 hparentMargin hcomponent
  refine ⟨⟨orient, ?_, ?_⟩⟩
  · intro i
    rw [hsources]
    exact hpositive i
  · intro i parent E z hz
    apply hstep i parent E z
    intro c hp
    rw [← hsources c] at hp ⊢
    exact hz c hp

/-- On numerically ordered endpoints, the balanced branch ratios and
their full Part-2 mass construct the plan. -/
theorem exists_ordered_actual_partTwo_plan
    (hα : 0 < α) (hα1 : α ≤ 1 / 4)
    (hhost : hostN = 2 * q) (horder : orderThreshold α M ≤ q)
    (S : CleanSourceWitness W Q) (C : Index W) (hC : C = Q.A ∨ C = Q.B)
    (e : MatchingEdge Q.claim67.M) {b : ℕ} (F : OrderedRootedForest b)
    (ratio : ℝ) (lowSide highSide : Fin 2) (hsides : highSide ≠ lowSide)
    (P : PartTwoLocalData F Finset.univ ratio
      (rootDensity W S (Sum.inl C) (edgeVertex W Q e lowSide))
      (rootDensity W S (Sum.inl C) (edgeVertex W Q e highSide))
      (gamma α : ℝ) (epsilon α : ℝ) W.clusterSize)
    (hsmall : ∀ i, F.size i ≤ freshBranchBound α W.clusterSize) :
    Nonempty (ActualPendingPlan W Q S C e F) := by
  subst hostN
  have hε : (0 : ℝ) ≤ epsilon α := by
    exact_mod_cast (parameter_pos hα).2.2.2.2.2.2.2.le
  let D := ClassifiedThresholdOwnerNumerics.of_partTwoLocalData F ratio
    (rootDensity W S (Sum.inl C) (edgeVertex W Q e lowSide))
    (rootDensity W S (Sum.inl C) (edgeVertex W Q e highSide))
    (gamma α : ℝ) (epsilon α : ℝ) W.clusterSize (freshBranchBound α W.clusterSize)
    P (Nat.cast_nonneg _) (partTwo_high_target_nonneg F _ _ _ _ _ _ P (Nat.cast_nonneg _) hε)
    hε hsmall (degreeForm_fresh_chunk_gates hα hα1 W horder).2.1
  exact exists_actual_pending_plan_of_numerics W Q hα hα1 rfl horder S C hC e F ratio
    lowSide highSide hsides D

/-- The literal matching need not be oriented by source density. Ordering
its endpoints turns the absolute-gap capacity into the Part-2 display. -/
theorem exists_actual_partTwo_plan
    (hα : 0 < α) (hα1 : α ≤ 1 / 4)
    (hhost : hostN = 2 * q) (horder : orderThreshold α M ≤ q)
    (S : CleanSourceWitness W Q) (C : Index W) (hC : C = Q.A ∨ C = Q.B)
    (e : MatchingEdge Q.claim67.M) {b : ℕ} (F : OrderedRootedForest b)
    (ratio : ℝ) (hratio : 0 ≤ ratio) (hratioHalf : ratio ≤ 1 / 2)
    (hlower : ∀ i, ratio ≤ (#(colourClass F i 0) : ℝ) / F.size i)
    (hupper : ∀ i, (#(colourClass F i 0) : ℝ) / F.size i ≤ 1 - ratio)
    (hsmall : ∀ i, F.size i ≤ freshBranchBound α W.clusterSize)
    (hmass : (F.order : ℝ) ≤ partTwoCapacity W Q S C ratio e) :
    Nonempty (ActualPendingPlan W Q S C e F) := by
  by_cases hle : rootDensity W S (Sum.inl C) (edgeVertex W Q e 0) ≤
      rootDensity W S (Sum.inl C) (edgeVertex W Q e 1)
  · apply exists_ordered_actual_partTwo_plan W Q hα hα1 hhost horder S C hC e F ratio
      0 1 (by decide) _ hsmall
    refine ⟨hratio, hratioHalf, hle, fun i _ => hlower i, fun i _ => hupper i, ?_⟩
    simpa [partTwoCapacity, partOneCapacity, OrderedRootedForest.order,
      abs_of_nonneg (sub_nonneg.mpr hle)] using hmass
  · apply exists_ordered_actual_partTwo_plan W Q hα hα1 hhost horder S C hC e F ratio
      1 0 (by decide) _ hsmall
    refine ⟨hratio, hratioHalf, le_of_not_ge hle, fun i _ => hlower i, fun i _ => hupper i, ?_⟩
    rw [partTwoCapacity, partOneCapacity, abs_sub_comm,
      abs_of_nonneg (sub_nonneg.mpr (le_of_not_ge hle)),
      add_comm (rootDensity W S (Sum.inl C) (edgeVertex W Q e 0))
        (rootDensity W S (Sum.inl C) (edgeVertex W Q e 1))] at hmass
    simpa [OrderedRootedForest.order] using hmass

end Erdos547b.ZhaoSourceActualPartTwoPlan

#print axioms Erdos547b.ZhaoSourceActualPartTwoPlan.exists_actual_pending_plan_of_numerics
#print axioms Erdos547b.ZhaoSourceActualPartTwoPlan.exists_ordered_actual_partTwo_plan
#print axioms Erdos547b.ZhaoSourceActualPartTwoPlan.exists_actual_partTwo_plan
