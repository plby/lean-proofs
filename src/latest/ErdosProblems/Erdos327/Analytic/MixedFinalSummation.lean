import ErdosProblems.Erdos327.Analytic.MixedBudgetSummation
import ErdosProblems.Erdos327.Analytic.MixedBoundarySummation
import ErdosProblems.Erdos327.Analytic.FinalThresholds

/-!
# Final summation of the mixed scheduled estimate

This module combines the resolved bulk, finite-sieve error, terminal,
boundary, and exceptional-endpoint estimates.  Each of the five pieces is
allocated `1 / 512` of the rough density; their total is strictly below the
`1 / 64` budget required by the canonical construction.
-/

namespace Erdos327.Analytic

open Filter Finset Real

open scoped BigOperators

noncomputable section

/-- The complete refined mixed scheduled sum, including its single possible
exceptional endpoint, eventually fits the canonical `1 / 64` budget. -/
theorem eventually_exists_forall_sum_mixedRefined_add_one_le_roughDensity
    (Kb : ℝ) :
    ∀ᶠ L : ℕ in atTop,
      ∃ N₀ : ℕ, ∀ N ≥ N₀,
        (∑ j ∈ range (Nat.log 2 N + 1),
          mixedRefinedScheduledBlockBound
            L N sourceAnatomySlope Kb
              oddAnatomySlope (oddBudget L)
              mixedSourceWeightBase mixedOddWeightBase j) + 1 ≤
          (N : ℝ) * Erdos327.roughDensity L / 64 := by
  obtain ⟨J, hdecomp⟩ :=
    exists_sum_mixedCanonicalUnresolved_eq_terminal_add_boundary
  filter_upwards
    [eventually_sum_mixedCanonicalBulkMain_le_roughDensity_div
        Kb (512 : ℝ) (by norm_num),
      eventually_sum_mixedCanonicalGoodSieveError_le_roughDensity_div
        Kb (512 : ℝ) (by norm_num),
      eventually_sum_mixedCanonicalTerminalMain_le_roughDensity_div
        Kb (512 : ℝ) (by norm_num),
      eventually_sum_mixedCanonicalBoundaryBlock_le_roughDensity Kb,
      eventually_mixedCanonicalUnresolved_prefix_eq_zero J Kb,
      eventually_ge_atTop 17] with
      L hbulk herror hterminal hboundary hprefix hL
  have hL3 : 3 ≤ L := by omega
  rcases eventually_atTop.1 hterminal with ⟨Nt, hNt⟩
  rcases eventually_atTop.1 hboundary with ⟨Nb, hNb⟩
  obtain ⟨No, hNo⟩ :=
    exists_nat_forall_one_le_nat_mul_roughDensity_div
      hL3 (D := (512 : ℝ)) (by norm_num)
  let N₀ : ℕ := max Nt (max Nb (max No (max (2 ^ J) 2)))
  refine ⟨N₀, ?_⟩
  intro N hN
  have hNtN : Nt ≤ N :=
    (le_max_left Nt (max Nb (max No (max (2 ^ J) 2)))).trans hN
  have hNbN : Nb ≤ N :=
    (le_trans (le_max_left Nb (max No (max (2 ^ J) 2)))
      (le_max_right Nt (max Nb (max No (max (2 ^ J) 2))))).trans hN
  have hNoN : No ≤ N :=
    (le_trans (le_max_left No (max (2 ^ J) 2))
      (le_trans (le_max_right Nb (max No (max (2 ^ J) 2)))
        (le_max_right Nt
          (max Nb (max No (max (2 ^ J) 2)))))).trans hN
  have hpowN : 2 ^ J ≤ N :=
    (le_trans (le_max_left (2 ^ J) 2)
      (le_trans (le_max_right No (max (2 ^ J) 2))
        (le_trans (le_max_right Nb (max No (max (2 ^ J) 2)))
          (le_max_right Nt
            (max Nb (max No (max (2 ^ J) 2))))))).trans hN
  let M : ℕ := Nat.log 2 N + 1
  have hJM : J ≤ M := by
    dsimp [M]
    exact (Nat.le_log_of_pow_le (by norm_num) hpowN).trans
      (Nat.le_add_right _ _)
  have hunresolved :
      (∑ j ∈ range M,
        mixedCanonicalUnresolvedBlock
          L N Kb (oddBudget L) j) ≤
        (∑ j ∈ range M,
          mixedCanonicalTerminalMainContribution
            L N Kb (oddBudget L) j) +
        ∑ j ∈ range M,
          mixedCanonicalBoundaryBlock
            L N Kb (oddBudget L) j := by
    have hsplit :
        (∑ j ∈ range M,
          mixedCanonicalUnresolvedBlock
            L N Kb (oddBudget L) j) =
          (∑ j ∈ range J,
            mixedCanonicalUnresolvedBlock
              L N Kb (oddBudget L) j) +
          ∑ j ∈ Ico J M,
            mixedCanonicalUnresolvedBlock
              L N Kb (oddBudget L) j :=
      (sum_range_add_sum_Ico _ hJM).symm
    have htail :=
      hdecomp J le_rfl L N M Kb (oddBudget L)
    have hterminalTail :
        (∑ j ∈ Ico J M,
          mixedCanonicalTerminalMainContribution
            L N Kb (oddBudget L) j) ≤
          ∑ j ∈ range M,
            mixedCanonicalTerminalMainContribution
              L N Kb (oddBudget L) j := by
      apply sum_le_sum_of_subset_of_nonneg
      · intro j hj
        exact mem_range.mpr (mem_Ico.mp hj).2
      · intro j hjBig hjSmall
        exact mixedCanonicalTerminalMainContribution_nonneg hL3
    have hboundaryTail :
        (∑ j ∈ Ico J M,
          mixedCanonicalBoundaryBlock
            L N Kb (oddBudget L) j) ≤
          ∑ j ∈ range M,
            mixedCanonicalBoundaryBlock
              L N Kb (oddBudget L) j := by
      apply sum_le_sum_of_subset_of_nonneg
      · intro j hj
        exact mem_range.mpr (mem_Ico.mp hj).2
      · intro j hjBig hjSmall
        exact mixedCanonicalBoundaryBlock_nonneg hL3
    calc
      (∑ j ∈ range M,
          mixedCanonicalUnresolvedBlock
            L N Kb (oddBudget L) j) =
        (∑ j ∈ range J,
          mixedCanonicalUnresolvedBlock
            L N Kb (oddBudget L) j) +
        ∑ j ∈ Ico J M,
          mixedCanonicalUnresolvedBlock
            L N Kb (oddBudget L) j := hsplit
      _ =
        ∑ j ∈ Ico J M,
          mixedCanonicalUnresolvedBlock
            L N Kb (oddBudget L) j := by
          rw [hprefix N, zero_add]
      _ =
        (∑ j ∈ Ico J M,
          mixedCanonicalTerminalMainContribution
            L N Kb (oddBudget L) j) +
        ∑ j ∈ Ico J M,
          mixedCanonicalBoundaryBlock
            L N Kb (oddBudget L) j := htail
      _ ≤
        (∑ j ∈ range M,
          mixedCanonicalTerminalMainContribution
            L N Kb (oddBudget L) j) +
        ∑ j ∈ range M,
          mixedCanonicalBoundaryBlock
            L N Kb (oddBudget L) j :=
        add_le_add hterminalTail hboundaryTail
  have hrefined :=
    sum_mixedRefinedScheduledBlockBound_le_resolved_add_unresolved
      (L := L) (N := N) (M := M)
      (Kb := Kb) (Ko := oddBudget L) hL3
  have hterminalN := hNt N hNtN M
  have hboundaryN := hNb N hNbN M
  have hone := hNo N hNoN
  have hρ0 : 0 ≤ Erdos327.roughDensity L :=
    (Erdos327.roughDensity_pos hL3).le
  calc
    (∑ j ∈ range (Nat.log 2 N + 1),
        mixedRefinedScheduledBlockBound
          L N sourceAnatomySlope Kb
            oddAnatomySlope (oddBudget L)
            mixedSourceWeightBase mixedOddWeightBase j) + 1 =
      (∑ j ∈ range M,
        mixedRefinedScheduledBlockBound
          L N sourceAnatomySlope Kb
            oddAnatomySlope (oddBudget L)
            mixedSourceWeightBase mixedOddWeightBase j) + 1 := by
        rfl
    _ ≤
      ((∑ j ∈ range M,
          mixedCanonicalBulkMainContribution
            L N Kb (oddBudget L) j) +
        (∑ j ∈ range M,
          mixedCanonicalGoodSieveErrorContribution
            L N Kb (oddBudget L) j) +
        (∑ j ∈ range M,
          mixedCanonicalTerminalMainContribution
            L N Kb (oddBudget L) j) +
        (∑ j ∈ range M,
          mixedCanonicalBoundaryBlock
            L N Kb (oddBudget L) j)) + 1 := by
      gcongr
      exact hrefined.trans (by linarith [hunresolved])
    _ ≤
      ((N : ℝ) * Erdos327.roughDensity L / 512 +
        (N : ℝ) * Erdos327.roughDensity L / 512 +
        (N : ℝ) * Erdos327.roughDensity L / 512 +
        (N : ℝ) * Erdos327.roughDensity L / 512) +
        (N : ℝ) * Erdos327.roughDensity L / 512 := by
      linarith [hbulk N M, herror N M,
        hterminalN, hboundaryN, hone]
    _ ≤ (N : ℝ) * Erdos327.roughDensity L / 64 := by
      have hx :
          0 ≤ (N : ℝ) * Erdos327.roughDensity L :=
        mul_nonneg (Nat.cast_nonneg N) hρ0
      nlinarith

end

end Erdos327.Analytic
