import ErdosProblems.Erdos327.Analytic.SourceScheduledSummation

/-!
# Support-preserving reduction of the source scheduled sum

Blocks with `8 * X < L` are exactly empty.  The first scheduled
reduction harmlessly retained their Euler main terms; for the final
partition it is cleaner to keep this exact support condition.
-/

namespace Erdos327.Analytic

open Filter Finset

noncomputable section

/-- Euler main term restricted to the exact nonempty source support. -/
def sourceSupportedEulerBlockMain
    (L N : ℕ) (K : ℝ) (j : ℕ) : ℝ :=
  if L ≤ 8 * dyadicScale j then
    sourceScheduledEulerBlockMain
      L N sourceAnatomySlope K j
  else 0

theorem sourceSupportedEulerBlockMain_nonneg
    (L N : ℕ) (K : ℝ) (j : ℕ) :
    0 ≤ sourceSupportedEulerBlockMain L N K j := by
  unfold sourceSupportedEulerBlockMain
  split_ifs
  · unfold sourceScheduledEulerBlockMain
      sourceDyadicBudget sourceScheduledEulerSieveMain
      sourceDyadicResidualMoment
    positivity
  · norm_num

/-- Eventual pointwise reduction retaining the exact support of the
Euler main contribution. -/
theorem eventually_forall_sourceExactRefinedBlock_le_supported_main_add_error :
    ∀ᶠ j : ℕ in atTop,
      ∀ L : ℕ, ∀ K : ℝ, 3 ≤ L → ∀ N : ℕ,
        sourceExactRefinedScheduledBlockBound
            L N sourceAnatomySlope K j ≤
          sourceSupportedEulerBlockMain L N K j +
            sourceScheduledErrorBlockBound N K j := by
  filter_upwards
    [eventually_forall_sourceExactRefinedBlock_le_main_add_error]
      with j hj
  intro L K hL N
  by_cases hnear : L ≤ 8 * dyadicScale j
  · simpa [sourceSupportedEulerBlockMain, hnear] using
      hj L K hL N
  · have hfar : 8 * dyadicScale j < L := by omega
    rw [sourceExactRefinedScheduledBlockBound, if_pos hfar,
      sourceSupportedEulerBlockMain, if_neg hnear]
    unfold sourceScheduledErrorBlockBound sourceBudgetConstant
    positivity

/-- Uniform finite-sum reduction with a supported Euler main term and an
arbitrarily small linear error. -/
theorem exists_forall_sourceExactScheduled_sum_le_initial_add_supported_main_add_error
    (K : ℝ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ J : ℕ,
      (∀ j ≥ J, 32 * sieveRadius j ≤ j) ∧
      ∀ L : ℕ, 3 ≤ L → ∀ N M : ℕ, J ≤ M →
        (∑ j ∈ range M,
          sourceExactRefinedScheduledBlockBound
            L N sourceAnatomySlope K j) ≤
          (∑ j ∈ range J,
            sourceExactRefinedScheduledBlockBound
              L N sourceAnatomySlope K j) +
          (∑ j ∈ Ico J M,
            sourceSupportedEulerBlockMain L N K j) +
          ε * (N : ℝ) := by
  rcases (eventually_atTop.1
    eventually_forall_sourceExactRefinedBlock_le_supported_main_add_error)
      with ⟨Js, hJs⟩
  obtain ⟨Je, hJe⟩ :=
    exists_sourceScheduledError_tail_le K hε
  rcases (eventually_atTop.1 eventually_sieveSchedule_dominates) with
    ⟨Jd, hJd⟩
  let J := max (max Js Je) Jd
  refine ⟨J, ?_, ?_⟩
  · intro j hj
    exact hJd j ((le_max_right (max Js Je) Jd).trans hj)
  · intro L hL N M hJM
    have hlate :
        (∑ j ∈ Ico J M,
          sourceExactRefinedScheduledBlockBound
            L N sourceAnatomySlope K j) ≤
          ∑ j ∈ Ico J M,
            (sourceSupportedEulerBlockMain L N K j +
              sourceScheduledErrorBlockBound N K j) := by
      apply sum_le_sum
      intro j hj
      exact hJs j
        ((le_max_left Js Je).trans
          ((le_max_left (max Js Je) Jd).trans
            (mem_Ico.mp hj).1))
        L K hL N
    have herror :
        (∑ j ∈ Ico J M,
          sourceScheduledErrorBlockBound N K j) ≤
          ε * (N : ℝ) :=
      hJe J
        ((le_max_right Js Je).trans
          (le_max_left (max Js Je) Jd))
        N M
    calc
      (∑ j ∈ range M,
          sourceExactRefinedScheduledBlockBound
            L N sourceAnatomySlope K j) =
        (∑ j ∈ range J,
          sourceExactRefinedScheduledBlockBound
            L N sourceAnatomySlope K j) +
        ∑ j ∈ Ico J M,
          sourceExactRefinedScheduledBlockBound
            L N sourceAnatomySlope K j :=
        (sum_range_add_sum_Ico _ hJM).symm
      _ ≤
        (∑ j ∈ range J,
          sourceExactRefinedScheduledBlockBound
            L N sourceAnatomySlope K j) +
        ∑ j ∈ Ico J M,
          (sourceSupportedEulerBlockMain L N K j +
            sourceScheduledErrorBlockBound N K j) :=
        add_le_add_right hlate _
      _ =
        (∑ j ∈ range J,
          sourceExactRefinedScheduledBlockBound
            L N sourceAnatomySlope K j) +
        (∑ j ∈ Ico J M,
          sourceSupportedEulerBlockMain L N K j) +
        ∑ j ∈ Ico J M,
          sourceScheduledErrorBlockBound N K j := by
        rw [sum_add_distrib]
        ring
      _ ≤
        (∑ j ∈ range J,
          sourceExactRefinedScheduledBlockBound
            L N sourceAnatomySlope K j) +
        (∑ j ∈ Ico J M,
          sourceSupportedEulerBlockMain L N K j) +
        ε * (N : ℝ) :=
        add_le_add_right herror _

/-- Supported-main reduction for the canonical bad-source count. -/
theorem exists_forall_card_rankBad_le_supported_main_add_error
    (K : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ J : ℕ,
      (∀ j ≥ J, 32 * sieveRadius j ≤ j) ∧
      ∀ L : ℕ, 3 ≤ L →
        8 * dyadicScale J < L →
        ∀ N : ℕ, 2 ≤ N →
          J ≤ Nat.log 2 N + 1 →
          ((Erdos327.rankBad (Erdos327.upto N)
            (regularSource L sourceAnatomySlope K N)
            ArithmeticFunction.cardFactors).card : ℝ) ≤
            (∑ j ∈ Ico J (Nat.log 2 N + 1),
              sourceSupportedEulerBlockMain L N K j) +
            ε * (N : ℝ) := by
  obtain ⟨J, hdom, hJ⟩ :=
    exists_forall_sourceExactScheduled_sum_le_initial_add_supported_main_add_error
      K hε
  refine ⟨J, hdom, ?_⟩
  intro L hL hfar N hN hJlog
  have hprefix :
      (∑ j ∈ range J,
        sourceExactRefinedScheduledBlockBound
          L N sourceAnatomySlope K j) = 0 :=
    sum_sourceExactRefinedScheduledBlockBound_range_eq_zero hfar
  have hglobal :=
    card_rankBad_le_exactRefinedScheduled_sum
      (L := L) (N := N)
      (A := sourceAnatomySlope) (K := K)
      hL hN sourceAnatomySlope_nonneg
  exact hglobal.trans
    (by
      simpa [hprefix] using
        hJ L hL N (Nat.log 2 N + 1) hJlog)

end

end Erdos327.Analytic
