import ErdosProblems.Erdos327.Analytic.SourceSmallBlocks
import ErdosProblems.Erdos327.Analytic.MixedSmallBlocks
import ErdosProblems.Erdos327.Analytic.TailInstantiation

/-!
# Reduction to the two scheduled analytic sums

The regularity tails are already unconditional.  This module packages the
remaining source and mixed dyadic sums into the exact interface consumed by
the canonical construction.
-/

namespace Erdos327.Analytic

open Finset Real

noncomputable section

/-- Exponential weight used on the rough source endpoint in the mixed
estimate. -/
def mixedSourceWeightBase : ℝ := 2.48933

/-- Exponential weight used on the odd endpoint in the mixed estimate. -/
def mixedOddWeightBase : ℝ := 1.34288

theorem mixedSourceWeightBase_gt_one :
    1 < mixedSourceWeightBase := by
  norm_num [mixedSourceWeightBase]

theorem mixedOddWeightBase_gt_one :
    1 < mixedOddWeightBase := by
  norm_num [mixedOddWeightBase]

theorem mixedRegularityExponent_nonneg :
    0 ≤ sourceAnatomySlope * log mixedSourceWeightBase +
      oddAnatomySlope * log mixedOddWeightBase := by
  have hqb : 0 < log mixedSourceWeightBase :=
    log_pos mixedSourceWeightBase_gt_one
  have hqo : 0 < log mixedOddWeightBase :=
    log_pos mixedOddWeightBase_gt_one
  exact add_nonneg
    (mul_nonneg sourceAnatomySlope_nonneg hqb.le)
    (mul_nonneg oddAnatomySlope_nonneg hqo.le)

/-- Once the two displayed scheduled sums meet their density budgets, all
four canonical estimates hold and both conclusions of Erdős 327 follow.
No asymptotic estimate is hidden in this theorem. -/
theorem erdos327FullConclusion_of_scheduled_sums
    {L : ℕ} {Kb Ko : ℝ} (hL : 3 ≤ L)
    {N₀ : ℕ}
    (hlarge : ∀ N ≥ N₀, L ≤ N)
    (hmodulus :
      ∀ N ≥ N₀, 4 * roughPrimeModulus L ≤ N)
    (hKb :
      roughCenteredTailConstant sourceAnatomySlope sourceTailBase *
          sourceTailBase ^ (-Kb) ≤ 1 / 8)
    (hKo :
      2 * unrestrictedCenteredTailConstant
          oddAnatomySlope oddTailBase *
          oddTailBase ^ (-Ko) ≤
        Erdos327.roughDensity L / 64)
    (hsource :
      ∀ N ≥ N₀,
        (∑ j ∈ range (Nat.log 2 N + 1),
          sourceRefinedScheduledBlockBound
            L N sourceAnatomySlope Kb j) ≤
          (N : ℝ) * Erdos327.roughDensity L / 16)
    (hmixed :
      ∀ N ≥ N₀,
        (∑ j ∈ range (Nat.log 2 N + 1),
          mixedRefinedScheduledBlockBound
            L N sourceAnatomySlope Kb
              oddAnatomySlope Ko
              mixedSourceWeightBase mixedOddWeightBase j) + 1 ≤
          (N : ℝ) * Erdos327.roughDensity L / 64) :
    Erdos327.Erdos327FullConclusion := by
  apply Erdos327.erdos327FullConclusion_of_canonical_estimates
    (Ab := sourceAnatomySlope) (Kb := Kb)
    (Ao := oddAnatomySlope) (Ko := Ko)
    hL hmodulus
  intro N hN
  have hLN := hlarge N hN
  have hN2 : 2 ≤ N := by omega
  have hsourceCard :=
    card_rankBad_le_refinedScheduled_sum
      (L := L) (N := N) (A := sourceAnatomySlope) (K := Kb)
      hL hN2 sourceAnatomySlope_nonneg
  have hmixedCard :=
    card_mixedEdges_le_refinedScheduled_sum_add_one
      (L := L) (N := N)
      (Ab := sourceAnatomySlope) (Kb := Kb)
      (Ao := oddAnatomySlope) (Ko := Ko)
      (qb := mixedSourceWeightBase) (qo := mixedOddWeightBase)
      hL hN2 mixedSourceWeightBase_gt_one
      mixedOddWeightBase_gt_one mixedRegularityExponent_nonneg
  exact
    ⟨irregularRoughSource_le_one_eighth
        hL hLN hN2 hKb,
      hsourceCard.trans (hsource N hN),
      irregularOddHost_le_one_sixty_fourth
        hL (by omega) (by omega) hKo,
      hmixedCard.trans (hmixed N hN)⟩

/-- The source scheduled sum alone yields Sawin's positive-density
two-admissible conclusion. -/
theorem erdos327SecondConclusion_of_scheduled_source
    {L : ℕ} {Kb : ℝ} (hL : 3 ≤ L)
    {N₀ : ℕ}
    (hlarge : ∀ N ≥ N₀, L ≤ N)
    (hmodulus :
      ∀ N ≥ N₀, 4 * roughPrimeModulus L ≤ N)
    (hKb :
      roughCenteredTailConstant sourceAnatomySlope sourceTailBase *
          sourceTailBase ^ (-Kb) ≤ 1 / 8)
    (hsource :
      ∀ N ≥ N₀,
        (∑ j ∈ range (Nat.log 2 N + 1),
          sourceRefinedScheduledBlockBound
            L N sourceAnatomySlope Kb j) ≤
          (N : ℝ) * Erdos327.roughDensity L / 16) :
    Erdos327.Erdos327SecondConclusion := by
  apply Erdos327.erdos327SecondConclusion_of_canonical_estimates
    (Ab := sourceAnatomySlope) (Kb := Kb) hL hmodulus
  intro N hN
  have hLN := hlarge N hN
  have hN2 : 2 ≤ N := by omega
  exact
    ⟨irregularRoughSource_le_one_eighth
        hL hLN hN2 hKb,
      (card_rankBad_le_refinedScheduled_sum
        (L := L) (N := N)
        (A := sourceAnatomySlope) (K := Kb)
        hL hN2 sourceAnatomySlope_nonneg).trans
          (hsource N hN)⟩

end

end Erdos327.Analytic
