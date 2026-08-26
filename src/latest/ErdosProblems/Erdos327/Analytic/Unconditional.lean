import ErdosProblems.Erdos327.Analytic.SourceFinalSummation
import ErdosProblems.Erdos327.Analytic.MixedFinalSummation

/-!
# Unconditional resolution of Erdős Problem 327

The source cutoff is chosen along the coupled sequence used in the source
summation.  Since that sequence tends to infinity, the same cutoff can also
be chosen to satisfy the mixed scheduled estimate and the odd-host anatomy
tail.  The four resulting canonical estimates give both conclusions.
-/

namespace Erdos327.Analytic

open Filter Finset Real

open scoped BigOperators

noncomputable section

/-- Unconditional proof of both asymptotic conclusions of Erdős Problem 327. -/
theorem erdos327FullConclusion_unconditional :
    Erdos327.Erdos327FullConclusion := by
  obtain ⟨K, hK⟩ := exists_sourceTailBudget
  have hmixedJ :
      ∀ᶠ J : ℕ in atTop,
        ∃ N₀ : ℕ, ∀ N ≥ N₀,
          (∑ j ∈ range (Nat.log 2 N + 1),
            mixedRefinedScheduledBlockBound
              (sourceCoupledCutoff J) N
                sourceAnatomySlope K
                oddAnatomySlope
                  (oddBudget (sourceCoupledCutoff J))
                mixedSourceWeightBase mixedOddWeightBase j) + 1 ≤
            (N : ℝ) *
              Erdos327.roughDensity (sourceCoupledCutoff J) / 64 :=
    tendsto_sourceCoupledCutoff_atTop.eventually
      (eventually_exists_forall_sum_mixedRefined_add_one_le_roughDensity K)
  have hoddJ :
      ∀ᶠ J : ℕ in atTop,
        2 * unrestrictedCenteredTailConstant
            oddAnatomySlope oddTailBase *
            oddTailBase ^ (-oddBudget (sourceCoupledCutoff J)) ≤
          Erdos327.roughDensity (sourceCoupledCutoff J) / 64 :=
    tendsto_sourceCoupledCutoff_atTop.eventually
      eventually_oddBudget_meets_tail
  obtain ⟨J, hsource, hmixed, hodd⟩ :=
    ((eventually_exists_forall_card_rankBad_le_roughDensity K).and
      (hmixedJ.and hoddJ)).exists
  rcases hsource with ⟨Ns, hsource⟩
  rcases hmixed with ⟨Nm, hmixed⟩
  let L : ℕ := sourceCoupledCutoff J
  let N₀ : ℕ :=
    max Ns (max Nm (max L (4 * roughPrimeModulus L)))
  have hL : 3 ≤ L := by
    dsimp [L]
    exact three_le_sourceCoupledCutoff J
  apply Erdos327.erdos327FullConclusion_of_canonical_estimates
    (Ab := sourceAnatomySlope) (Kb := K)
    (Ao := oddAnatomySlope) (Ko := oddBudget L)
    hL
  · intro N hN
    exact
      (le_trans
        (le_max_right L (4 * roughPrimeModulus L))
        (le_trans
          (le_max_right Nm (max L (4 * roughPrimeModulus L)))
          (le_max_right Ns
            (max Nm (max L (4 * roughPrimeModulus L)))))).trans hN
  · intro N hN
    have hNs : Ns ≤ N :=
      (le_max_left Ns
        (max Nm (max L (4 * roughPrimeModulus L)))).trans hN
    have hNm : Nm ≤ N :=
      (le_trans
        (le_max_left Nm (max L (4 * roughPrimeModulus L)))
        (le_max_right Ns
          (max Nm (max L (4 * roughPrimeModulus L))))).trans hN
    have hLN : L ≤ N :=
      (le_trans
        (le_max_left L (4 * roughPrimeModulus L))
        (le_trans
          (le_max_right Nm (max L (4 * roughPrimeModulus L)))
          (le_max_right Ns
            (max Nm (max L (4 * roughPrimeModulus L)))))).trans hN
    have hN2 : 2 ≤ N := by omega
    have hsourceN :
        ((Erdos327.rankBad (Erdos327.upto N)
          (regularSource L sourceAnatomySlope K N)
          ArithmeticFunction.cardFactors).card : ℝ) ≤
            (N : ℝ) * Erdos327.roughDensity L / 16 := by
      simpa [L] using hsource N hNs
    have hoddL :
        2 * unrestrictedCenteredTailConstant
            oddAnatomySlope oddTailBase *
            oddTailBase ^ (-oddBudget L) ≤
          Erdos327.roughDensity L / 64 := by
      simpa [L] using hodd
    have hmixedSum :
        (∑ j ∈ range (Nat.log 2 N + 1),
          mixedRefinedScheduledBlockBound
            L N sourceAnatomySlope K
              oddAnatomySlope (oddBudget L)
              mixedSourceWeightBase mixedOddWeightBase j) + 1 ≤
            (N : ℝ) * Erdos327.roughDensity L / 64 := by
      simpa [L] using hmixed N hNm
    have hmixedCard :=
      card_mixedEdges_le_refinedScheduled_sum_add_one
        (L := L) (N := N)
        (Ab := sourceAnatomySlope) (Kb := K)
        (Ao := oddAnatomySlope) (Ko := oddBudget L)
        (qb := mixedSourceWeightBase) (qo := mixedOddWeightBase)
        hL hN2 mixedSourceWeightBase_gt_one
        mixedOddWeightBase_gt_one mixedRegularityExponent_nonneg
    exact
      ⟨irregularRoughSource_le_one_eighth
          hL hLN hN2 hK,
        hsourceN,
        irregularOddHost_le_one_sixty_fourth
          hL (by omega) (by omega) hoddL,
        hmixedCard.trans hmixedSum⟩

/-- The first, formerly open, asymptotic conclusion as a standalone theorem. -/
theorem erdos327Conclusion_unconditional :
    Erdos327.Erdos327Conclusion :=
  erdos327FullConclusion_unconditional.1

end

end Erdos327.Analytic
