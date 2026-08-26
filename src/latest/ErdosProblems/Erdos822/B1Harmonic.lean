/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos822.B1Asymptotic
import ErdosProblems.Erdos822.FinsetSumUnion

/-!
# Reciprocal B1 error with a fixed ambient cutoff

For `K = log₂ N`, use the dyadic intervals with indices `K/2 ≤ j < K`.
Their endpoints have double logarithm within one of the ambient double
logarithm.  The B1 cutoff remains `b1Cutoff N` in every one of these
intervals.  This uniformity is essential for deleting the B1 failures from
the harmonic mass of the structured small factors.
-/

namespace Erdos822

open Filter
open scoped BigOperators

noncomputable def b1FailureBlock (y j : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Ioc (2 ^ j) (2 ^ (j + 1))).filter
    fun k ↦ ¬ TotientSquareRich k y

noncomputable def b1UpperHalfFailures (N : ℕ) : Finset ℕ :=
  (Finset.Ico (Nat.log 2 N / 2) (Nat.log 2 N)).biUnion
    (b1FailureBlock (b1Cutoff N))

theorem b1FailureBlock_card_le (y j : ℕ) :
    (b1FailureBlock y j).card ≤ (b1FailureIndices (2 ^ (j + 1)) y).card := by
  classical
  apply Finset.card_le_card_of_injOn (fun k ↦ k - 1)
  · intro k hk
    obtain ⟨hkI, hkfail⟩ := Finset.mem_filter.mp hk
    obtain ⟨hklo, hkhi⟩ := Finset.mem_Ioc.mp hkI
    have hkpos : 0 < k := (by positivity : 0 < 2 ^ j).trans hklo
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_range.mpr (by change k - 1 < 2 ^ (j + 1); omega), ?_⟩
    simpa [Nat.sub_add_cancel (show 1 ≤ k by omega)] using hkfail
  · intro k hk k' hk' heq
    change k - 1 = k' - 1 at heq
    have hklo := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hk).1).1
    have hk'lo := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hk').1).1
    have hpow : 0 < 2 ^ j := by positivity
    omega

theorem sum_inv_b1FailureBlock_le_card_div (y j : ℕ) :
    ∑ k ∈ b1FailureBlock y j, (1 : ℝ) / k ≤
      ((b1FailureIndices (2 ^ (j + 1)) y).card : ℝ) / (2 : ℝ) ^ j := by
  classical
  calc
    (∑ k ∈ b1FailureBlock y j, (1 : ℝ) / k) ≤
        ∑ _k ∈ b1FailureBlock y j, (1 : ℝ) / (2 : ℝ) ^ j := by
      apply Finset.sum_le_sum
      intro k hk
      have hklo := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hk).1).1
      exact one_div_le_one_div_of_le (by positivity) (by exact_mod_cast hklo.le)
    _ = ((b1FailureBlock y j).card : ℝ) / (2 : ℝ) ^ j := by
      simp [div_eq_mul_inv]
    _ ≤ ((b1FailureIndices (2 ^ (j + 1)) y).card : ℝ) / (2 : ℝ) ^ j :=
      div_le_div_of_nonneg_right (by exact_mod_cast b1FailureBlock_card_le y j)
        (by positivity)

/-- The B1 variance estimate is uniform over all dyadic blocks in the
upper half of the logarithmic small-factor range. -/
theorem eventually_b1FailureBlock_card_mul_cutoff_sq_le :
    ∀ᶠ N : ℕ in atTop, ∀ j ∈ Finset.Ico (Nat.log 2 N / 2) (Nat.log 2 N),
      ((b1FailureIndices (2 ^ (j + 1)) (b1Cutoff N)).card : ℝ) *
        (b1Cutoff N : ℝ) ^ 2 ≤ 3072 * (2 : ℝ) ^ (j + 1) := by
  obtain ⟨T₀, hT₀⟩ := eventually_atTop.mp
    eventually_card_b1FailureIndices_mul_doubleLog_le
  filter_upwards [tendsto_natLog_two_atTop.eventually_ge_atTop (2 * T₀),
      tendsto_b1Cutoff_atTop.eventually_ge_atTop 8,
      tendsto_b1DoubleLog_atTop.eventually_ge_atTop 2] with N hK hy hZ2
  intro j hj
  obtain ⟨hjlo, hjhi⟩ := Finset.mem_Ico.mp hj
  let y := b1Cutoff N
  let Z := b1DoubleLog N
  let T := 2 ^ (j + 1)
  let Zt := b1DoubleLog T
  have hT : T₀ ≤ T := by
    have hTj : T₀ ≤ j + 1 := by omega
    exact hTj.trans Nat.lt_two_pow_self.le
  have hZZt : Z ≤ Zt + 1 := by
    have hKj : Nat.log 2 N ≤ (j + 1) * 2 := by omega
    have hlog := Nat.log_mono_right (b := 2) hKj
    rw [Nat.log_mul_base (by norm_num) (by omega)] at hlog
    simpa [Z, Zt, T, b1DoubleLog, Nat.log_pow (by norm_num : 1 < 2)] using hlog
  have hZt1 : 1 ≤ Zt := by change 2 ≤ Z at hZ2; omega
  have hypos : (0 : ℝ) < y := by exact_mod_cast (show 0 < y by dsimp [y]; omega)
  have hy4 : y ^ 4 ≤ Z := nthRoot_pow_le (by norm_num)
  have hy3 : 512 ≤ y ^ 3 :=
    (by norm_num : 512 ≤ 8 ^ 3).trans (Nat.pow_le_pow_left hy 3)
  have hy512 : 512 * y ≤ Z := by
    calc
      512 * y ≤ y ^ 3 * y := Nat.mul_le_mul_right y hy3
      _ = y ^ 4 := by ring
      _ ≤ Z := hy4
  have hy256 : 256 * y ≤ Zt := by
    have hy1 : 1 ≤ y := by dsimp [y]; omega
    omega
  have hbound := hT₀ T hT y hy256
  have hy4R : (y : ℝ) ^ 4 ≤ 2 * Zt := by
    exact_mod_cast (show y ^ 4 ≤ 2 * Zt by omega)
  have hmul := mul_le_mul_of_nonneg_left hy4R
    (show (0 : ℝ) ≤ (b1FailureIndices T y).card by positivity)
  have hsq : (y : ℝ) ^ 2 * (((b1FailureIndices T y).card : ℝ) * (y : ℝ) ^ 2) ≤
      (y : ℝ) ^ 2 * (3072 * T) := by nlinarith
  have hfinal := (mul_le_mul_iff_right₀ (sq_pos_of_pos hypos)).mp hsq
  simpa only [T, y, Nat.cast_pow, Nat.cast_ofNat] using hfinal

theorem eventually_sum_inv_b1FailureBlock_mul_cutoff_sq_le :
    ∀ᶠ N : ℕ in atTop, ∀ j ∈ Finset.Ico (Nat.log 2 N / 2) (Nat.log 2 N),
      (∑ k ∈ b1FailureBlock (b1Cutoff N) j, (1 : ℝ) / k) *
        (b1Cutoff N : ℝ) ^ 2 ≤ 6144 := by
  filter_upwards [eventually_b1FailureBlock_card_mul_cutoff_sq_le] with N hN
  intro j hj
  have h := hN j hj
  have hmass := sum_inv_b1FailureBlock_le_card_div (b1Cutoff N) j
  have hmassMul := mul_le_mul_of_nonneg_right hmass (sq_nonneg (b1Cutoff N : ℝ))
  calc
    (∑ k ∈ b1FailureBlock (b1Cutoff N) j, (1 : ℝ) / k) * (b1Cutoff N : ℝ) ^ 2 ≤
        (((b1FailureIndices (2 ^ (j + 1)) (b1Cutoff N)).card : ℝ) *
          (b1Cutoff N : ℝ) ^ 2) / (2 : ℝ) ^ j := by
      simpa [div_mul_eq_mul_div] using hmassMul
    _ ≤ (3072 * (2 : ℝ) ^ (j + 1)) / (2 : ℝ) ^ j :=
      div_le_div_of_nonneg_right h (by positivity)
    _ = 6144 := by rw [pow_succ]; field_simp; norm_num

/-- Summing the uniform block bound controls the reciprocal error with the
ambient cutoff held fixed. -/
theorem eventually_sum_inv_b1UpperHalfFailures_mul_cutoff_sq_le :
    ∀ᶠ N : ℕ in atTop,
      (∑ k ∈ b1UpperHalfFailures N, (1 : ℝ) / k) * (b1Cutoff N : ℝ) ^ 2 ≤
        6144 * (Nat.log 2 N : ℝ) := by
  filter_upwards [eventually_sum_inv_b1FailureBlock_mul_cutoff_sq_le] with N hN
  have hunion := sum_biUnion_le_sum
    (Finset.Ico (Nat.log 2 N / 2) (Nat.log 2 N))
    (b1FailureBlock (b1Cutoff N)) (fun k ↦ (1 : ℝ) / k)
    (fun j hj k hk ↦ by positivity)
  calc
    (∑ k ∈ b1UpperHalfFailures N, (1 : ℝ) / k) * (b1Cutoff N : ℝ) ^ 2 ≤
        (∑ j ∈ Finset.Ico (Nat.log 2 N / 2) (Nat.log 2 N),
          ∑ k ∈ b1FailureBlock (b1Cutoff N) j, (1 : ℝ) / k) *
            (b1Cutoff N : ℝ) ^ 2 :=
      mul_le_mul_of_nonneg_right hunion (sq_nonneg _)
    _ = ∑ j ∈ Finset.Ico (Nat.log 2 N / 2) (Nat.log 2 N),
        (∑ k ∈ b1FailureBlock (b1Cutoff N) j, (1 : ℝ) / k) *
          (b1Cutoff N : ℝ) ^ 2 := by rw [Finset.sum_mul]
    _ ≤ ∑ _j ∈ Finset.Ico (Nat.log 2 N / 2) (Nat.log 2 N), (6144 : ℝ) :=
      Finset.sum_le_sum hN
    _ = ((Finset.Ico (Nat.log 2 N / 2) (Nat.log 2 N)).card : ℝ) * 6144 := by simp
    _ ≤ 6144 * (Nat.log 2 N : ℝ) := by
      have hcard : (Finset.Ico (Nat.log 2 N / 2) (Nat.log 2 N)).card ≤ Nat.log 2 N := by
        simp
      exact_mod_cast (show (Finset.Ico (Nat.log 2 N / 2) (Nat.log 2 N)).card * 6144 ≤
        6144 * Nat.log 2 N by omega)

/-- The reciprocal B1 error is negligible compared with `log N`. -/
theorem eventually_sum_inv_b1UpperHalfFailures_le_log
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop,
      ∑ k ∈ b1UpperHalfFailures N, (1 : ℝ) / k ≤ ε * Real.log (N : ℝ) := by
  have hyT : Tendsto (fun N ↦ (b1Cutoff N : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp tendsto_b1Cutoff_atTop
  filter_upwards [eventually_sum_inv_b1UpperHalfFailures_mul_cutoff_sq_le,
      hyT.eventually_ge_atTop (max 1 (18432 / ε)),
      eventually_ge_atTop 4] with N hN hy hN4
  have hy1 : (1 : ℝ) ≤ b1Cutoff N := (le_max_left _ _).trans hy
  have hypos : (0 : ℝ) < b1Cutoff N := zero_lt_one.trans_le hy1
  have hysq : (b1Cutoff N : ℝ) ≤ (b1Cutoff N : ℝ) ^ 2 := by nlinarith
  have hyε : 18432 ≤ ε * (b1Cutoff N : ℝ) ^ 2 := by
    have hle : 18432 / ε ≤ (b1Cutoff N : ℝ) := (le_max_right _ _).trans hy
    have hmul := (div_le_iff₀ hε).mp hle
    nlinarith
  have hscale := Erdos387.binaryLogScale_cast_le_three_mul_log hN4
  have hK : (Nat.log 2 N : ℝ) ≤ 3 * Real.log (N : ℝ) := by
    simp only [Erdos387.binaryLogScale, Nat.cast_add, Nat.cast_one] at hscale
    linarith
  have hlog : 0 ≤ Real.log (N : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))
  have hmul := mul_le_mul_of_nonneg_right hyε hlog
  have hsq : (b1Cutoff N : ℝ) ^ 2 *
      (∑ k ∈ b1UpperHalfFailures N, (1 : ℝ) / k) ≤
        (b1Cutoff N : ℝ) ^ 2 * (ε * Real.log (N : ℝ)) := by nlinarith
  exact (mul_le_mul_iff_right₀ (sq_pos_of_pos hypos)).mp hsq

#print axioms eventually_sum_inv_b1UpperHalfFailures_le_log

end Erdos822
