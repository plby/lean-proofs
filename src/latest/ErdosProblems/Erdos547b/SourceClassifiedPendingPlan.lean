/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.SourceActualPendingPlan

/-!
# Classified pending plans with the balanced-branch capacity gain

The threshold prefix kernel is independent of the ratio being zero.
This file exposes that general kernel and constructs its numerical input
from Part 2 of the small-forest lemma. Future outer roots are still revealed
only at their actual branch step, without changing the fixed orientation.
-/

open scoped SimpleGraph Classical
noncomputable section

namespace Erdos547b.ZhaoSourceClassifiedPendingPlan

open Finset SimpleGraph
open Erdos547b.RegularPair Erdos547b.ZhaoLemma58GroupedSmallForest
open Erdos547b.ZhaoLemma54ThresholdOrientation Erdos547b.ZhaoLemma54ThresholdNumerics
open Erdos547b.ZhaoLemma54CanonicalThresholdOrientation Erdos547b.ZhaoLemma54ThresholdSourceNumerics
open Erdos547b.ZhaoLemma58OwnerLocalStep Erdos547b.ZhaoLemma58ThresholdResidualCapacity
open Erdos547b.ZhaoLemma58DynamicBatchAppend Erdos547b.ZhaoSourceFreshChunkEmbedding
open Erdos547b.ZhaoSourcePendingBranchStep

/-- Part-2 mass pays the nonnegative high target required by the threshold
numerics. It is not an additional density hypothesis. -/
theorem partTwo_high_target_nonneg {b : ℕ} (F : OrderedRootedForest b)
    (ratio dx dy γ ε N : ℝ)
    (P : PartTwoLocalData F Finset.univ ratio dx dy γ ε N)
    (hN : 0 ≤ N) (hε : 0 ≤ ε) : 0 ≤ (dy - γ) * N := by
  have hmass : (F.order : ℝ) ≤ (dx + dy - 2 * γ - 3 * ε) * N +
      ratio / (1 - ratio) * (dy - dx) * N := by
    simpa [OrderedRootedForest.order] using P.mass_le
  have hload := partTwo_balanced_load_le_high ratio dx dy γ ε N F.order 0
    P.c_nonneg P.c_le_half P.low_le_high hN hε hmass (mul_nonneg hε hN)
  have horder : (0 : ℝ) ≤ F.order := Nat.cast_nonneg _
  linarith only [hload, horder]

/-- A classified numerical display yields a source-only orientation and
actual, image-preserving extensions at every later eligible root. -/
theorem exists_pending_pair_plan_of_numerics
    {b : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
    (F : OrderedRootedForest b) (H : SimpleGraph V) [DecidableRel H.Adj]
    (whole deleted : Fin 2 → Finset V)
    (N L small : ℕ) (ratio dx dy γ ε ρ d : ℝ)
    (lowSide highSide : Fin 2) (hsides : highSide ≠ lowSide)
    (D : ClassifiedThresholdOwnerNumerics F ratio dx dy γ ε N small)
    (hN : 0 < N) (hγ : 0 < γ) (hdy : dy ≤ 1)
    (hρ : 0 ≤ ρ) (hρd : ρ ≤ d)
    (hwhole : ∀ c, (whole c).card = N)
    (hdeleted : ∀ c, deleted c ⊆ whole c)
    (hdeletedCard : ∀ c, (deleted c).card ≤ L)
    (hdisjoint : Disjoint (whole 0) (whole 1))
    (huniform : H.IsUniform ρ (whole 0) (whole 1))
    (hdensity : d ≤ H.edgeDensity (whole 0) (whole 1))
    (hparentMargin : (L : ℝ) + 2 ≤ (γ - 3 * ρ) * N)
    (hcomponent : (small : ℝ) + ρ * N + 1 ≤ (d - ρ) * (γ * N - L)) :
    ∃ orient : Fin b → Fin 2 ≃ Fin 2,
      (∀ i, 0 < if branchRootSide F orient i = lowSide then dx else dy) ∧
      ∀ (i : Fin b) (parent : Fin b → V)
        (E : PartialDynamicAttachedForestEmbedding F H parent orient
          (residualSide whole deleted) (Finset.Iio i)) (z : V),
        (∀ c, 0 < (if c = lowSide then dx else dy) →
          ((if c = lowSide then dx else dy) - 2 * ρ) * N ≤
            (#((whole c).filter (H.Adj z)) : ℝ)) →
        ∃ E' : PartialDynamicAttachedForestEmbedding F H (Function.update parent i z) orient
            (residualSide whole deleted) (Finset.Iio i ∪ {i}),
          ∀ j hj, E'.forestCopy.componentCopy j (Finset.mem_union_left _ hj) =
            E.forestCopy.componentCopy j hj := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hγdy : γ ≤ dy := by nlinarith only [D.high_target_nonneg, hNR]
  let O := canonicalActualThresholdSwitchOrientation F small (thresholdLowBudget dx γ N)
    (thresholdHighBudget dy γ N) lowSide highSide D.small hsides (D.suffix_display highSide)
  refine ⟨O.orient, ?_, ?_⟩
  · intro i
    by_cases hc : branchRootSide F O.orient i = lowSide
    · rw [if_pos hc]
      have hlowNonzero : thresholdLowBudget dx γ N ≠ 0 := by
        intro hz
        have hcut : O.cutoff = 0 := by
          change maximalFittingCutoff F (canonicalPrefixBalancedOrientation F small D.small)
            (thresholdLowBudget dx γ N) = 0
          rw [hz]
          exact maximalFittingCutoff_eq_zero_of_budget_zero F _
        exact (O.late_root_high i (by rw [hcut]; exact Nat.zero_le _)) hc
      have ht : 0 ≤ (dx - γ) * (N : ℝ) := by
        by_contra hn
        exact hlowNonzero (thresholdLowBudget_eq_zero_of_nonpos (le_of_not_ge hn))
      nlinarith only [ht, hNR, hγ]
    · rw [if_neg hc]
      exact hγ.trans_le hγdy
  · intro i parent E z hz
    let K := classifiedFreshChunkData F H (fun _ => z) whole deleted N L small ratio dx dy γ ε ρ d
      lowSide highSide hsides D hN hγ hγdy hdy hρ hρd hwhole hdeleted hdeletedCard
      hdisjoint huniform hdensity (fun _ c hp => hz c hp) hparentMargin hcomponent
    exact exists_next_prefix_of_thresholdData F H parent whole
      (residualSide whole deleted) ρ d i z K E

end Erdos547b.ZhaoSourceClassifiedPendingPlan

#print axioms Erdos547b.ZhaoSourceClassifiedPendingPlan.partTwo_high_target_nonneg
#print axioms Erdos547b.ZhaoSourceClassifiedPendingPlan.exists_pending_pair_plan_of_numerics
