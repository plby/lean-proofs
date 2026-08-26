/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Uniform comparison of each central-bin root count with its fine sign grid.
Formal proof: Codex.
-/
import ErdosProblems.Erdos521.FineGridTwoRoots
import ErdosProblems.Erdos521.SimpleRootProbability

namespace Erdos521

open MeasureTheory Filter
open scoped BigOperators

theorem eventually_fineGrid_root_disagreement :
    ∀ᶠ j : ℕ in atTop, ∀ k ∈ mainBinSet j,
      sequenceLaw.real {ε | intervalRootCount ε (2 ^ j) (dyadicPoint k) (dyadicPoint (k + 1)) ≠
        gridSignChanges ε (2 ^ j) (dyadicFineGrid j k) (fineGridLength j)} ≤
        (((2 ^ j : ℕ) : ℝ)) ^ (-1 : ℝ) +
          (3 * fineGridSmallBallConstant + 96) * (fineGridLength j : ℝ) * fineGridThreshold j := by
  obtain ⟨C, _, hsimple⟩ := simpleRoot_bulk_probability
  have hdegree : Tendsto (fun j : ℕ ↦ (2 : ℕ) ^ j) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  filter_upwards [hdegree.eventually hsimple, eventually_mainBin_lower, eventually_mainBin_bulk C,
    eventually_fineGrid_two_roots, eventually_mainBin_fine_zero_probability, eventually_ge_atTop 1]
    with j hj hl hu htwo hzero hj₁
  intro k hk
  have hj₀ : 0 < j := by omega
  have hM : 1 ≤ fineGridLength j := fineGridLength_pos hj₀
  have hM' : (1 : ℝ) ≤ fineGridLength j := by exact_mod_cast hM
  have hpoint : (∑ i ∈ Finset.range (fineGridLength j + 1), sequenceLaw.real
      {ε | powerSum ε (2 ^ j + 1) (dyadicFineGrid j k i) = 0}) ≤
      ((fineGridLength j : ℝ) + 1) * (fineGridSmallBallConstant * fineGridThreshold j) := by
    have h := Finset.sum_le_sum (fun i (hi : i ∈ Finset.range (fineGridLength j + 1)) ↦
      hzero k hk (dyadicFineGrid j k i)
        (dyadicFineGrid_mem hj₀ k (i := i) (by have := Finset.mem_range.mp hi; omega)))
    simpa only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one] using h
  have hcells : (∑ i ∈ Finset.range (fineGridLength j), sequenceLaw.real
      {ε | 2 ≤ intervalRootCount ε (2 ^ j) (dyadicFineGrid j k i) (dyadicFineGrid j k (i + 1))}) ≤
      (fineGridLength j : ℝ) * ((fineGridSmallBallConstant + 96) * fineGridThreshold j) := by
    have h := Finset.sum_le_sum (fun i (hi : i ∈ Finset.range (fineGridLength j)) ↦
      htwo k hk i (Finset.mem_range.mp hi))
    simpa only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] using h
  have hdouble := hj (dyadicPoint k) (dyadicPoint (k + 1)) (hl k hk) (hu k hk)
  have h := rootCount_signGrid_probability (2 ^ j) (fineGridLength j) (dyadicFineGrid j k)
    (dyadicFineGrid_mono j k) (δ := 0) (τ := 0) (by norm_num) (by norm_num)
  simp only [dyadicFineGrid_zero, dyadicFineGrid_end hj₀, abs_nonpos_iff] at h
  have hnonneg : 0 ≤ fineGridSmallBallConstant * fineGridThreshold j :=
    mul_nonneg fineGridSmallBallConstant_pos.le (fineGridThreshold_pos hj₀).le
  have hMbound := mul_le_mul_of_nonneg_right (show (fineGridLength j : ℝ) + 1 ≤ 2 * fineGridLength j by linarith) hnonneg
  nlinarith

end Erdos521
