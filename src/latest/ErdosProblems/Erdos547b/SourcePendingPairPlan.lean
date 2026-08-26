/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.SourcePendingBranchStep

/-!
# A fixed source-only orientation with sequential root access

One orientation is selected before the pending roots are revealed. Every
later eligible current root gives a genuine branch-prefix extension in
that same orientation. A branch root always uses a positive source entry.
-/

open scoped SimpleGraph Classical
noncomputable section

namespace Erdos547b.ZhaoSourcePendingPairPlan

open Finset SimpleGraph
open Erdos547b.RegularPair Erdos547b.ZhaoLemma58GroupedSmallForest
open Erdos547b.ZhaoLemma54ThresholdOrientation Erdos547b.ZhaoLemma54ThresholdNumerics
open Erdos547b.ZhaoLemma54CanonicalThresholdOrientation Erdos547b.ZhaoLemma54ThresholdSourceNumerics
open Erdos547b.ZhaoLemma58OwnerLocalStep Erdos547b.ZhaoLemma58ThresholdResidualCapacity
open Erdos547b.ZhaoLemma58DynamicBatchAppend Erdos547b.ZhaoSourceFreshChunkEmbedding
open Erdos547b.ZhaoSourcePendingBranchStep

/-- Source mass and the established fresh-pair gates give one orientation
which accepts each root when it is actually chosen. Future roots are not
premises, and every previous branch copy is preserved by each extension. -/
theorem exists_pending_pair_plan
    {b : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
    (F : OrderedRootedForest b) (H : SimpleGraph V) [DecidableRel H.Adj]
    (whole deleted : Fin 2 → Finset V)
    (N L small : ℕ) (dx dy γ ε ρ d : ℝ)
    (lowSide highSide : Fin 2) (hsides : highSide ≠ lowSide)
    (hN : 0 < N) (hγ : 0 < γ) (hlowHigh : dx ≤ dy) (hdy : dy ≤ 1)
    (hε : 0 ≤ ε) (hρ : 0 ≤ ρ) (hρd : ρ ≤ d)
    (hsmall : ∀ i, F.size i ≤ small)
    (hmass : (F.order : ℝ) ≤ (dx + dy - 2 * γ - 3 * ε) * N)
    (hround : (2 : ℝ) + 3 * small ≤ 3 * (ε * N))
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
  have hγdy : γ ≤ dy := by
    by_contra hnot
    have hneg : dx + dy - 2 * γ - 3 * ε < 0 := by
      have hdyγ := lt_of_not_ge hnot
      linarith only [hlowHigh, hdyγ, hε]
    have hnegative := mul_neg_of_neg_of_pos hneg hNR
    have horder : (0 : ℝ) ≤ F.order := Nat.cast_nonneg _
    linarith only [hmass, hnegative, horder]
  let D := ClassifiedThresholdOwnerNumerics.of_partOneMass F dx dy γ ε N small
    hlowHigh hNR.le (mul_nonneg (sub_nonneg.mpr hγdy) hNR.le) hε hsmall hmass hround
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
    let K := classifiedFreshChunkData F H (fun _ => z) whole deleted N L small 0 dx dy γ ε ρ d
      lowSide highSide hsides D hN hγ hγdy hdy hρ hρd hwhole hdeleted hdeletedCard
      hdisjoint huniform hdensity (fun _ c hp => hz c hp) hparentMargin hcomponent
    exact exists_next_prefix_of_thresholdData F H parent whole
      (residualSide whole deleted) ρ d i z K E

end Erdos547b.ZhaoSourcePendingPairPlan

#print axioms Erdos547b.ZhaoSourcePendingPairPlan.exists_pending_pair_plan
