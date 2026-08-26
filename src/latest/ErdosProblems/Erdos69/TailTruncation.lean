import ErdosProblems.Erdos69.TailCancellation
import ErdosProblems.Erdos69.PointwiseTail

/-! # Exact truncation of the signed arithmetic tails -/

open scoped BigOperators

namespace Erdos69.Elementary

noncomputable def arithmeticTailTerm (m P n k : ℕ) : ℝ :=
  ∑ i : PatternLabel m, (patternSign m i : ℝ) *
    (omegaCount (n + patternDilation m P i * (k + 1) - patternOffset m P i) : ℝ) /
      2 ^ (k + 1)

noncomputable def arithmeticTail (m P n : ℕ) : ℝ := ∑' k, arithmeticTailTerm m P n k

theorem summable_arithmeticTailTerm (m P n : ℕ) : Summable (arithmeticTailTerm m P n) := by
  apply summable_sum
  intro i hi
  have h := (summable_omega_affine_tail n (patternDilation m P i) (patternOffset m P i) 0
    (patternDilation_pos m P i)).mul_left (patternSign m i : ℝ)
  simpa only [Nat.zero_add, Nat.add_comm 1, mul_div_assoc] using h

theorem arithmeticTailTerm_initial_zero (m P n k : ℕ) (hk : k < 6 * m) :
    arithmeticTailTerm m P n k = 0 := by
  unfold arithmeticTailTerm
  rw [← Finset.sum_div, initial_arithmetic_cancellation m P n (k + 1)
    (by omega) (by omega) (fun a ↦ (omegaCount a : ℝ)), zero_div]

theorem signed_dilatedTail_eq_arithmeticTail (m P n : ℕ)
    (hn : ∀ i, n ≡ patternOffset m P i [MOD patternDilation m P i])
    (hb : ∀ i, patternOffset m P i ≤ n) :
    (∑ i : PatternLabel m, (patternSign m i : ℝ) *
      dilatedPositiveTail (patternDilation m P i)
        ((n - patternOffset m P i) / patternDilation m P i)) = arithmeticTail m P n := by
  have heq (i : PatternLabel m) :
      (patternSign m i : ℝ) * dilatedPositiveTail (patternDilation m P i)
        ((n - patternOffset m P i) / patternDilation m P i) =
      ∑' k : ℕ, (patternSign m i : ℝ) *
        (omegaCount (n + patternDilation m P i * (k + 1) - patternOffset m P i) : ℝ) /
          2 ^ (k + 1) := by
    rw [dilatedPositiveTail, ← tsum_mul_left]
    apply tsum_congr
    intro k
    rw [dilation_quotient_shift (patternDilation_pos m P i) (hb i) (hn i)]
    ring
  simp_rw [heq]
  unfold arithmeticTail arithmeticTailTerm
  apply (Summable.tsum_finsetSum _).symm
  intro i hi
  have h := (summable_omega_affine_tail n (patternDilation m P i) (patternOffset m P i) 0
    (patternDilation_pos m P i)).mul_left (patternSign m i : ℝ)
  simpa only [Nat.zero_add, Nat.add_comm 1, mul_div_assoc] using h

theorem arithmeticTail_split (m P n H : ℕ) :
    arithmeticTail m P n =
      (∑ k ∈ Finset.range H, arithmeticTailTerm m P n (6 * m + k)) +
        ∑' k, arithmeticTailTerm m P n (k + (6 * m + H)) := by
  have h := (summable_arithmeticTailTerm m P n).sum_add_tsum_nat_add (6 * m + H)
  rw [Finset.sum_range_add] at h
  have hzero : (∑ k ∈ Finset.range (6 * m), arithmeticTailTerm m P n k) = 0 := by
    exact Finset.sum_eq_zero (fun k hk ↦ arithmeticTailTerm_initial_zero m P n k
      (Finset.mem_range.mp hk))
  rw [hzero, zero_add] at h
  exact h.symm

theorem retained_sum_eq_prefix (m P n H : ℕ) (q : ℝ) :
    (∑ r ∈ retainedShifts m P H, shiftCoefficient m P H q r * omegaCount (n + r)) =
      q * ∑ k ∈ Finset.range H, arithmeticTailTerm m P n (6 * m + k) := by
  rw [sum_grouped_shift_test, Fintype.sum_prod_type, Finset.sum_comm,
    ← Fin.sum_univ_eq_sum_range (fun k ↦ arithmeticTailTerm m P n (6 * m + k)) H,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  unfold arithmeticTailTerm
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hle : patternOffset m P i ≤ patternDilation m P i * (6 * m + 1 + k.val) := by
    unfold patternOffset patternDilation roughDilation
    have hh := patternIntercept_le_digit_mul (by omega : 6 * m ≤ 6 * m + 1 + k.val) i
    nlinarith
  have heq : n + termShift m P H (i, k) =
      n + patternDilation m P i * (6 * m + k.val + 1) - patternOffset m P i := by
    unfold termShift patternShift
    rw [show 6 * m + 1 + k.val = 6 * m + k.val + 1 by omega] at hle ⊢
    dsimp only
    omega
  simp only [termCoefficient, heq]
  rw [show 6 * m + 1 + k.val = 6 * m + k.val + 1 by omega]
  ring

theorem arithmetic_remainder_abs_le (m P n L : ℕ) :
    |∑' k, arithmeticTailTerm m P n (k + L)| ≤
      ∑ i : PatternLabel m,
        (Real.log (n + patternDilation m P i : ℕ) / Real.log 2 + L + 2) / 2 ^ L := by
  let g : PatternLabel m → ℕ → ℝ := fun i k ↦
    (omegaCount (n + patternDilation m P i * (L + 1 + k) - patternOffset m P i) : ℝ) /
      2 ^ (L + 1 + k)
  have hg (i : PatternLabel m) : Summable (g i) :=
    summable_omega_affine_tail n _ _ L (patternDilation_pos m P i)
  have hgn (i : PatternLabel m) (k : ℕ) : 0 ≤ g i k := by dsimp [g]; positivity
  have hpoint (k : ℕ) : arithmeticTailTerm m P n (k + L) =
      ∑ i : PatternLabel m, (patternSign m i : ℝ) * g i k := by
    unfold arithmeticTailTerm
    apply Finset.sum_congr rfl
    intro i hi
    dsimp [g]
    rw [show k + L + 1 = L + 1 + k by omega]
    ring
  simp_rw [hpoint]
  rw [Summable.tsum_finsetSum (fun i _ ↦ (hg i).mul_left (patternSign m i : ℝ))]
  simp_rw [Summable.tsum_mul_left _ (hg _)]
  calc
    _ ≤ ∑ i : PatternLabel m, |(patternSign m i : ℝ) * ∑' k, g i k| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i : PatternLabel m, ∑' k, g i k := by
      simp [abs_mul, patternSign_abs_real, abs_of_nonneg (tsum_nonneg (hgn _))]
    _ ≤ _ := Finset.sum_le_sum (fun i _ ↦ omega_affine_tail_le n _ _ L
      (patternDilation_pos m P i))

theorem arithmeticTail_truncation_error (m P n H : ℕ) (q : ℝ) :
    |q * arithmeticTail m P n -
      ∑ r ∈ retainedShifts m P H, shiftCoefficient m P H q r * omegaCount (n + r)| ≤
      |q| * ∑ i : PatternLabel m,
        (Real.log (n + patternDilation m P i : ℕ) / Real.log 2 + (6 * m + H) + 2) /
          2 ^ (6 * m + H) := by
  rw [retained_sum_eq_prefix, arithmeticTail_split m P n H, mul_add, add_sub_cancel_left,
    abs_mul]
  simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using
    mul_le_mul_of_nonneg_left (arithmetic_remainder_abs_le m P n (6 * m + H)) (abs_nonneg q)

end Erdos69.Elementary
