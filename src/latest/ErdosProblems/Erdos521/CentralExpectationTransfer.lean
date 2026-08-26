/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Expectation transfer from actual central roots to the capped window statistic.
Formal proof: Codex.
-/
import ErdosProblems.Erdos521.CentralComparisonProbability
import ErdosProblems.Erdos521.NatExpectationError

namespace Erdos521

open MeasureTheory Filter
open scoped Topology

theorem eventually_central_expectation_error_bounded :
    ∃ A : ℝ, ∀ᶠ j : ℕ in atTop,
      |(∫ ε, (centralRootCount ε j : ℝ) ∂sequenceLaw) -
        (∫ ε, (centralCappedCount ε j : ℝ) ∂sequenceLaw)| ≤ A := by
  obtain ⟨C, _, hprob⟩ := eventually_central_disagreement_probability
  obtain ⟨B, hB, hmom⟩ := centralRootCount_moments 8 (by norm_num)
  refine ⟨C + B + 256, ?_⟩
  filter_upwards [hprob, hmom, eventually_ge_atTop 1] with j hp hx hj
  have hj₁ : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hj₀ : (0 : ℝ) < j := lt_of_lt_of_le zero_lt_one hj₁
  have h := abs_integral_nat_sub_le_error sequenceLaw (centralRootCount_aemeasurable j)
    (centralCappedCount_measurable j).aemeasurable (2 ^ j) (j * windowCapScale j)
    (fun ε ↦ centralRootCount_le ε j) (fun ε ↦ centralCappedCount_le ε j)
    (pow_pos hj₀ 3)
  have hcanc : (j : ℝ) ^ 3 * (j : ℝ) ^ (-3 : ℝ) = 1 := by
    rw [Real.rpow_neg (Nat.cast_nonneg j), Real.rpow_ofNat]
    exact mul_inv_cancel₀ (pow_ne_zero _ hj₀.ne')
  have hp' : (j : ℝ) ^ 3 * sequenceLaw.real {ε | centralRootCount ε j ≠ centralCappedCount ε j} ≤ C := by
    calc
      _ ≤ (j : ℝ) ^ 3 * (C * (j : ℝ) ^ (-3 : ℝ)) := mul_le_mul_of_nonneg_left hp (by positivity)
      _ = C := by rw [← mul_assoc, mul_comm ((j : ℝ) ^ 3) C, mul_assoc, hcanc, mul_one]
  have hx' : (∫ ε, (centralRootCount ε j : ℝ) ^ 8 ∂sequenceLaw) ≤ (j : ℝ) ^ 21 * B :=
    hx.trans (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hj₁ (by norm_num)) hB.le)
  have hy := integral_cappedCentralNatSum_pow_le hj 8 (dyadicFineGrid j) (fun _ ↦ fineGridLength j)
  have hy' : (∫ ε, (centralCappedCount ε j : ℝ) ^ 8 ∂sequenceLaw) ≤ 256 * (j : ℝ) ^ 21 := by
    calc
      _ ≤ (2 * (j : ℝ) ^ 2) ^ 8 := hy
      _ = 256 * (j : ℝ) ^ 16 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hj₁ (by norm_num)) (by norm_num)
  have hm : ((∫ ε, (centralRootCount ε j : ℝ) ^ 8 ∂sequenceLaw) +
      (∫ ε, (centralCappedCount ε j : ℝ) ^ 8 ∂sequenceLaw)) / ((j : ℝ) ^ 3) ^ 7 ≤ B + 256 := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < ((j : ℝ) ^ 3) ^ 7)).mpr
    calc
      _ ≤ (j : ℝ) ^ 21 * B + 256 * (j : ℝ) ^ 21 := add_le_add hx' hy'
      _ = _ := by ring
  exact h.trans (by linarith)

theorem central_expectation_error_div_index_tendsto_zero :
    Tendsto (fun j : ℕ ↦ ((∫ ε, (centralRootCount ε j : ℝ) ∂sequenceLaw) -
      (∫ ε, (centralCappedCount ε j : ℝ) ∂sequenceLaw)) / j) atTop (𝓝 0) := by
  obtain ⟨A, hA⟩ := eventually_central_expectation_error_bounded
  apply tendsto_bdd_div_atTop_nhds_zero (b := -A) (B := A)
  · exact hA.mono (fun _ h ↦ (abs_le.mp h).1)
  · exact hA.mono (fun _ h ↦ (abs_le.mp h).2)
  · exact tendsto_natCast_atTop_atTop

theorem centralCappedCount_mean_div_index_limit :
    Tendsto (fun j : ℕ ↦ (∫ ε, (centralCappedCount ε j : ℝ) ∂sequenceLaw) / j)
      atTop (𝓝 (Real.log 2 / (2 * Real.pi))) := by
  have h := centralRootCount_mean_div_index_limit.sub central_expectation_error_div_index_tendsto_zero
  simp only [sub_zero] at h
  convert h using 1
  funext j
  simp only [sub_div]
  ring

end Erdos521
