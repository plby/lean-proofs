import ErdosProblems.Erdos327.Analytic.SourceTerminalSummation
import ErdosProblems.Erdos327.Analytic.SourceBoundarySummation
import ErdosProblems.Erdos327.Analytic.SourceErrorCoupling
import ErdosProblems.Erdos327.Analytic.FinalThresholds

/-!
# Final assembly of the source scheduled sum

The supported Euler main term is partitioned into the normalized bulk,
strict terminal, cutoff transition, and positive small-residual ranges.
The zero residual range contributes exactly zero.  Coupling the killed
prefix to the roughness cutoff then closes the source estimate.
-/

namespace Erdos327.Analytic

open Filter Finset Real

noncomputable section

theorem sourceScheduledEulerBlockMain_nonneg
    (L N : ℕ) (K : ℝ) (j : ℕ) :
    0 ≤ sourceScheduledEulerBlockMain
      L N sourceAnatomySlope K j := by
  unfold sourceScheduledEulerBlockMain sourceDyadicBudget
    sourceScheduledEulerSieveMain sourceDyadicResidualMoment
  positivity

theorem sourceScheduledEulerBlockMain_eq_zero_of_residual_eq_zero
    {L N j : ℕ} {K : ℝ}
    (hzero : 2 * N / dyadicScale j ^ 2 = 0) :
    sourceScheduledEulerBlockMain
      L N sourceAnatomySlope K j = 0 := by
  unfold sourceScheduledEulerBlockMain sourceDyadicResidualMoment
  rw [hzero]
  simp

/-- Exact four-range partition of the support-preserving source Euler
main sum. -/
theorem sum_sourceSupportedEulerBlockMain_eq_four_ranges
    {L N J M : ℕ} {K : ℝ}
    (hL : 3 ≤ L)
    (hdom : ∀ j ≥ J, 32 * sieveRadius j ≤ j) :
    (∑ j ∈ Ico J M,
      sourceSupportedEulerBlockMain L N K j) =
      (∑ j ∈ sourceBulkIndexSet L N J M,
        sourceScheduledEulerBlockMain
          L N sourceAnatomySlope K j) +
      (∑ j ∈ sourceTerminalIndexSet L N J M,
        sourceScheduledEulerBlockMain
          L N sourceAnatomySlope K j) +
      (∑ j ∈ sourceTransitionIndexSet L J M,
        sourceScheduledEulerBlockMain
          L N sourceAnatomySlope K j) +
      ∑ j ∈ sourceSmallResidualIndexSet L N J M,
        sourceScheduledEulerBlockMain
          L N sourceAnatomySlope K j := by
  rw [sourceBulkIndexSet, sourceTerminalIndexSet,
    sourceTransitionIndexSet, sourceSmallResidualIndexSet]
  simp_rw [sum_filter]
  rw [← sum_add_distrib, ← sum_add_distrib, ← sum_add_distrib]
  apply sum_congr rfl
  intro j hj
  have hjJ : J ≤ j := (mem_Ico.mp hj).1
  have hjdom : 32 * sieveRadius j ≤ j := hdom j hjJ
  let X : ℕ := dyadicScale j
  let Y : ℕ := 2 * N / X ^ 2
  by_cases hnear : L ≤ 8 * X
  · rw [sourceSupportedEulerBlockMain, if_pos (by simpa [X] using hnear)]
    by_cases hXL : X < L
    · have hnLX : ¬L ≤ X := by omega
      simp [hjdom, X, Y, hXL, hnLX, hnear]
    · have hLX : L ≤ X := Nat.le_of_not_gt hXL
      have hntrans : ¬X < L := by omega
      by_cases hY0 : Y = 0
      · have hnLY : ¬L ≤ Y := by
          dsimp [Y] at hY0 ⊢
          omega
        have hnYpos : ¬0 < Y := by omega
        rw [sourceScheduledEulerBlockMain_eq_zero_of_residual_eq_zero
          (K := K) (by simpa [X, Y] using hY0)]
        simp [hjdom, X, Y, hLX, hntrans, hnLY, hnYpos]
      · have hYpos : 0 < Y := Nat.pos_of_ne_zero hY0
        by_cases hYL : Y < L
        · have hnLY : ¬L ≤ Y := by omega
          have hnXY : ¬X ≤ Y := by omega
          have hYX : Y < X := by omega
          simp [hjdom, X, Y, hLX, hntrans, hYpos, hYL, hnLY,
            hnXY, hYX]
        · have hLY : L ≤ Y := Nat.le_of_not_gt hYL
          by_cases hXY : X ≤ Y
          · have hnYX : ¬Y < X := by omega
            simp [hjdom, X, Y, hLX, hLY, hXY, hnYX,
              hntrans, hYpos, hYL]
          · have hYX : Y < X := Nat.lt_of_not_ge hXY
            simp [hjdom, X, Y, hLX, hLY, hXY, hYX,
              hntrans, hYpos, hYL]
  · have hfar : 8 * X < L := Nat.lt_of_not_ge hnear
    have hnLX : ¬L ≤ X := by
      omega
    have hntransition : ¬(X < L ∧ L ≤ 8 * X) := by
      intro h
      exact hnear h.2
    rw [sourceSupportedEulerBlockMain, if_neg (by simpa [X] using hnear)]
    simp [hjdom, X, Y, hnLX, hntransition]

theorem sourceBulkIndexSet_mono_start
    {L N J₀ J M : ℕ} {K : ℝ}
    (hJJ : J₀ ≤ J) :
    (∑ j ∈ sourceBulkIndexSet L N J M,
      sourceScheduledEulerBlockMain
        L N sourceAnatomySlope K j) ≤
      ∑ j ∈ sourceBulkIndexSet L N J₀ M,
        sourceScheduledEulerBlockMain
          L N sourceAnatomySlope K j := by
  apply sum_le_sum_of_subset_of_nonneg
  · intro j hj
    rw [sourceBulkIndexSet, mem_filter] at hj ⊢
    exact ⟨mem_Ico.mpr
      ⟨hJJ.trans (mem_Ico.mp hj.1).1, (mem_Ico.mp hj.1).2⟩,
      hj.2⟩
  · intro j hjBig hjSmall
    exact sourceScheduledEulerBlockMain_nonneg L N K j

theorem sourceTerminalIndexSet_mono_start
    {L N J₀ J M : ℕ} {K : ℝ}
    (hJJ : J₀ ≤ J) :
    (∑ j ∈ sourceTerminalIndexSet L N J M,
      sourceScheduledEulerBlockMain
        L N sourceAnatomySlope K j) ≤
      ∑ j ∈ sourceTerminalIndexSet L N J₀ M,
        sourceScheduledEulerBlockMain
          L N sourceAnatomySlope K j := by
  apply sum_le_sum_of_subset_of_nonneg
  · intro j hj
    rw [sourceTerminalIndexSet, mem_filter] at hj ⊢
    exact ⟨mem_Ico.mpr
      ⟨hJJ.trans (mem_Ico.mp hj.1).1, (mem_Ico.mp hj.1).2⟩,
      hj.2⟩
  · intro j hjBig hjSmall
    exact sourceScheduledEulerBlockMain_nonneg L N K j

/-- For every fixed source budget, all sufficiently late coupled
prefixes admit a final `N` threshold beyond which the canonical
bad-source count fits its `1/16` rough-density budget. -/
theorem eventually_exists_forall_card_rankBad_le_roughDensity
    (K : ℝ) :
    ∀ᶠ J : ℕ in atTop,
      ∃ N₀ : ℕ, ∀ N ≥ N₀,
        ((Erdos327.rankBad (Erdos327.upto N)
          (regularSource (sourceCoupledCutoff J)
            sourceAnatomySlope K N)
          ArithmeticFunction.cardFactors).card : ℝ) ≤
          (N : ℝ) *
            Erdos327.roughDensity (sourceCoupledCutoff J) / 16 := by
  rcases (eventually_atTop.1
    eventually_forall_sourceExactRefinedBlock_le_supported_main_add_error)
      with ⟨Js, hpoint⟩
  rcases (eventually_atTop.1 eventually_sieveSchedule_dominates) with
    ⟨Jd, hdom⟩
  obtain ⟨Jb, hJb1, hbulk⟩ :=
    exists_sourceBulk_start_for_roughDensity K
  obtain ⟨Jt, Nt, hJt1, hterminal⟩ :=
    exists_sourceTerminal_start_for_roughDensity K
  have htransitionL :=
    eventually_sum_sourceEulerMain_transition_le_roughDensity K
  have htransitionJ :
      ∀ᶠ J : ℕ in atTop,
        ∀ N J' M : ℕ,
          (∑ j ∈ sourceTransitionIndexSet
              (sourceCoupledCutoff J) J' M,
            sourceScheduledEulerBlockMain
              (sourceCoupledCutoff J) N sourceAnatomySlope K j) ≤
            (N : ℝ) *
              Erdos327.roughDensity (sourceCoupledCutoff J) / 64 :=
    tendsto_sourceCoupledCutoff_atTop.eventually htransitionL
  filter_upwards
    [eventually_ge_atTop (max (max (max Js Jd) Jb) Jt),
      htransitionJ,
      eventually_sourceScheduledErrorTail_le_roughDensity K]
      with J hJall htransition herror
  let L : ℕ := sourceCoupledCutoff J
  have hJs : Js ≤ J :=
    le_trans (le_max_left Js Jd)
      (le_trans (le_max_left (max Js Jd) Jb)
        (le_trans (le_max_left (max (max Js Jd) Jb) Jt) hJall))
  have hJd : Jd ≤ J :=
    le_trans (le_max_right Js Jd)
      (le_trans (le_max_left (max Js Jd) Jb)
        (le_trans (le_max_left (max (max Js Jd) Jb) Jt) hJall))
  have hJb : Jb ≤ J :=
    le_trans (le_max_right (max Js Jd) Jb)
      (le_trans (le_max_left (max (max Js Jd) Jb) Jt) hJall)
  have hJt : Jt ≤ J :=
    (le_max_right (max (max Js Jd) Jb) Jt).trans hJall
  have hJ1 : 1 ≤ J := hJb1.trans hJb
  have hL : 3 ≤ L := three_le_sourceCoupledCutoff J
  have hdomJ : ∀ j ≥ J, 32 * sieveRadius j ≤ j := by
    intro j hj
    exact hdom j (hJd.trans hj)
  have hpointJ :
      ∀ j ≥ J, ∀ N : ℕ,
        sourceExactRefinedScheduledBlockBound
            L N sourceAnatomySlope K j ≤
          sourceSupportedEulerBlockMain L N K j +
            sourceScheduledErrorBlockBound N K j := by
    intro j hj N
    exact hpoint j (hJs.trans hj) L K hL N
  have hsmallEps :
      0 < Erdos327.roughDensity L / 128 :=
    div_pos (Erdos327.roughDensity_pos hL) (by norm_num)
  have hsmallEventually :=
    eventually_sum_sourceEulerMain_smallResidual_le
      L K hL hsmallEps
  rcases (eventually_atTop.1 hsmallEventually) with
    ⟨Ns, hsmall⟩
  let N₀ : ℕ := max Nt (max Ns (max 2 (2 ^ J)))
  refine ⟨N₀, ?_⟩
  intro N hN
  have hNt : Nt ≤ N :=
    (le_max_left Nt (max Ns (max 2 (2 ^ J)))).trans hN
  have hNs : Ns ≤ N :=
    (le_trans (le_max_left Ns (max 2 (2 ^ J)))
      (le_max_right Nt (max Ns (max 2 (2 ^ J))))).trans hN
  have hN2 : 2 ≤ N :=
    (le_trans (le_max_left 2 (2 ^ J))
      (le_trans (le_max_right Ns (max 2 (2 ^ J)))
        (le_max_right Nt (max Ns (max 2 (2 ^ J)))))).trans hN
  have hpowN : 2 ^ J ≤ N :=
    (le_trans (le_max_right 2 (2 ^ J))
      (le_trans (le_max_right Ns (max 2 (2 ^ J)))
        (le_max_right Nt (max Ns (max 2 (2 ^ J)))))).trans hN
  have hJM : J ≤ Nat.log 2 N + 1 :=
    (Nat.le_log_of_pow_le (by norm_num) hpowN).trans
      (Nat.le_add_right _ _)
  let M : ℕ := Nat.log 2 N + 1
  have hprefix :
      (∑ j ∈ range J,
        sourceExactRefinedScheduledBlockBound
          L N sourceAnatomySlope K j) = 0 := by
    exact sum_sourceExactRefinedScheduledBlockBound_range_eq_zero
      (by
        dsimp [L]
        exact eight_dyadicScale_lt_sourceCoupledCutoff J)
  have hlate :
      (∑ j ∈ Ico J M,
        sourceExactRefinedScheduledBlockBound
          L N sourceAnatomySlope K j) ≤
        (∑ j ∈ Ico J M,
          sourceSupportedEulerBlockMain L N K j) +
        ∑ j ∈ Ico J M,
          sourceScheduledErrorBlockBound N K j := by
    calc
      _ ≤
        ∑ j ∈ Ico J M,
          (sourceSupportedEulerBlockMain L N K j +
            sourceScheduledErrorBlockBound N K j) := by
              apply sum_le_sum
              intro j hj
              exact hpointJ j (mem_Ico.mp hj).1 N
      _ = _ := by rw [sum_add_distrib]
  have hbulkJ :
      (∑ j ∈ sourceBulkIndexSet L N J M,
        sourceScheduledEulerBlockMain
          L N sourceAnatomySlope K j) ≤
        (N : ℝ) * Erdos327.roughDensity L / 64 :=
    (sourceBulkIndexSet_mono_start
      (L := L) (N := N) (J₀ := Jb) (J := J)
      (M := M) (K := K) hJb).trans
      (hbulk L N M hL)
  have hterminalJ :
      (∑ j ∈ sourceTerminalIndexSet L N J M,
        sourceScheduledEulerBlockMain
          L N sourceAnatomySlope K j) ≤
        (N : ℝ) * Erdos327.roughDensity L / 64 :=
    (sourceTerminalIndexSet_mono_start
      (L := L) (N := N) (J₀ := Jt) (J := J)
      (M := M) (K := K) hJt).trans
      (hterminal L N M hL hNt)
  have htransitionJ' :
      (∑ j ∈ sourceTransitionIndexSet L J M,
        sourceScheduledEulerBlockMain
          L N sourceAnatomySlope K j) ≤
        (N : ℝ) * Erdos327.roughDensity L / 64 := by
    simpa [L] using htransition N J M
  have hsmallJ :
      (∑ j ∈ sourceSmallResidualIndexSet L N J M,
        sourceScheduledEulerBlockMain
          L N sourceAnatomySlope K j) ≤
        (Erdos327.roughDensity L / 128) * (N : ℝ) :=
    hsmall N hNs J M
  have herrorJ :
      (∑ j ∈ Ico J M,
        sourceScheduledErrorBlockBound N K j) ≤
        (N : ℝ) * Erdos327.roughDensity L / 128 := by
    simpa [L] using herror N M
  have hmain :
      (∑ j ∈ Ico J M,
        sourceSupportedEulerBlockMain L N K j) ≤
        7 * ((N : ℝ) * Erdos327.roughDensity L) / 128 := by
    rw [sum_sourceSupportedEulerBlockMain_eq_four_ranges hL hdomJ]
    linarith
  have hglobal :=
    card_rankBad_le_exactRefinedScheduled_sum
      (L := L) (N := N)
      (A := sourceAnatomySlope) (K := K)
      hL hN2 sourceAnatomySlope_nonneg
  calc
    ((Erdos327.rankBad (Erdos327.upto N)
        (regularSource L sourceAnatomySlope K N)
        ArithmeticFunction.cardFactors).card : ℝ)
        ≤
      ∑ j ∈ range M,
        sourceExactRefinedScheduledBlockBound
          L N sourceAnatomySlope K j := by
            simpa [M] using hglobal
    _ =
      (∑ j ∈ range J,
        sourceExactRefinedScheduledBlockBound
          L N sourceAnatomySlope K j) +
      ∑ j ∈ Ico J M,
        sourceExactRefinedScheduledBlockBound
          L N sourceAnatomySlope K j :=
      (sum_range_add_sum_Ico _ hJM).symm
    _ =
      ∑ j ∈ Ico J M,
        sourceExactRefinedScheduledBlockBound
          L N sourceAnatomySlope K j := by rw [hprefix, zero_add]
    _ ≤
      (∑ j ∈ Ico J M,
        sourceSupportedEulerBlockMain L N K j) +
      ∑ j ∈ Ico J M,
        sourceScheduledErrorBlockBound N K j := hlate
    _ ≤
      7 * ((N : ℝ) * Erdos327.roughDensity L) / 128 +
        ((N : ℝ) * Erdos327.roughDensity L / 128) :=
      add_le_add hmain herrorJ
    _ = (N : ℝ) * Erdos327.roughDensity L / 16 := by ring

/-- Unconditional positive-density construction for the second part of
Erdős 327.  This is the formal counterpart of the result proved by
Sawin, obtained here from the audited scheduled source argument. -/
theorem erdos327SecondConclusion_unconditional :
    Erdos327.Erdos327SecondConclusion := by
  obtain ⟨K, hK⟩ := exists_sourceTailBudget
  obtain ⟨J, Ns, hsource⟩ :=
    (eventually_exists_forall_card_rankBad_le_roughDensity K).exists
  let L : ℕ := sourceCoupledCutoff J
  let N₀ : ℕ :=
    max Ns (max L (4 * roughPrimeModulus L))
  have hL : 3 ≤ L := by
    dsimp [L]
    exact three_le_sourceCoupledCutoff J
  apply Erdos327.erdos327SecondConclusion_of_canonical_estimates
    (Ab := sourceAnatomySlope) (Kb := K) hL
  · intro N hN
    exact
      (le_trans (le_max_right L (4 * roughPrimeModulus L))
        (le_max_right Ns (max L (4 * roughPrimeModulus L)))).trans hN
  · intro N hN
    have hNs : Ns ≤ N :=
      (le_max_left Ns (max L (4 * roughPrimeModulus L))).trans hN
    have hLN : L ≤ N :=
      (le_trans (le_max_left L (4 * roughPrimeModulus L))
        (le_max_right Ns (max L (4 * roughPrimeModulus L)))).trans hN
    have hN2 : 2 ≤ N := by omega
    exact
      ⟨irregularRoughSource_le_one_eighth
          hL hLN hN2 hK,
        hsource N hNs⟩

end

end Erdos327.Analytic
