import ErdosProblems.Erdos1188.PrimePolynomial

/- Ported from Lean 4.31.0 to 4.33.0; module names and elaboration options adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# A linear-times-binary-log prime bound and asymptotically sharp frame cutoff
-/

namespace Erdos1188

open scoped BigOperators

noncomputable section

/-- A convenient direct form of Mathlib's explicit Chebyshev lower bound. -/
theorem primeCounting_ge_quarter_div_log (n : ℕ) (hn : 256 ≤ n) :
    (n : ℝ) / (4 * Real.log n) ≤ (Nat.primeCounting n : ℝ) := by
  have hN : (256 : ℝ) ≤ n := by exact_mod_cast hn
  have hN0 : (0 : ℝ) ≤ n := by positivity
  have hN1 : (1 : ℝ) < n := lt_of_lt_of_le (by norm_num) hN
  have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have h := Real.lt_log_one_add_of_pos (x := (1 : ℝ)) (by norm_num)
    norm_num at h ⊢
    linarith
  have hsqrtN1 : Real.sqrt ((n : ℝ) + 1) ≤ (n : ℝ) / 8 := by
    rw [Real.sqrt_le_iff]
    constructor
    · positivity
    · have hprod : 0 ≤ ((n : ℝ) - 256) * ((n : ℝ) + 192) := by positivity
      nlinarith
  have hlogN1 : Real.log ((n : ℝ) + 1) ≤ (n : ℝ) / 4 := by
    have hnonneg : (0 : ℝ) ≤ (n : ℝ) + 1 := by positivity
    have h := Real.log_le_rpow_div hnonneg (show (0 : ℝ) < 1 / 2 by norm_num)
    rw [← Real.sqrt_eq_rpow] at h
    norm_num at h ⊢
    linarith
  have hnum : (n : ℝ) / 4 ≤
      (n : ℝ) * Real.log 2 - Real.log ((n : ℝ) + 1) := by
    nlinarith
  calc
    (n : ℝ) / (4 * Real.log n) = ((n : ℝ) / 4) / Real.log n := by ring
    _ ≤ ((n : ℝ) * Real.log 2 - Real.log ((n : ℝ) + 1)) / Real.log n :=
      (div_le_div_iff_of_pos_right (Real.log_pos hN1)).2 hnum
    _ ≤ (Nat.primeCounting n : ℝ) := Chebyshev.pi_ge n

/-- Explicit near-linear bound for the indexed primes, in terms of the binary
logarithm `r=floor(log₂(i+1))+1`. -/
theorem nthPrime_le_binary_log (i : ℕ) :
    nthPrime i ≤
      128 * (Nat.log 2 (i + 1) + 1) * 2 ^ (Nat.log 2 (i + 1) + 1) := by
  let s := i + 1
  let r := Nat.log 2 s + 1
  let N := 128 * r * 2 ^ r
  have hr1 : 1 ≤ r := by simp [r]
  have hsPow : s < 2 ^ r := by
    simpa [r] using Nat.lt_pow_succ_log_self (b := 2) (by decide) s
  have hN : 256 ≤ N := by
    have hp : 2 ≤ 2 ^ r := by
      simpa using (Nat.pow_le_pow_right (n := 2) (by decide) hr1)
    simp only [N]
    nlinarith
  have hlog2nonneg : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hlog2le : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (x := (2 : ℝ)) (by norm_num)
    norm_num at h ⊢
    exact h
  have hlogN : Real.log N ≤ 9 * (r : ℝ) := by
    have hr0 : (r : ℝ) ≠ 0 := by positivity
    have hp0 : ((2 ^ r : ℕ) : ℝ) ≠ 0 := by positivity
    have h128 : (128 : ℝ) = 2 ^ 7 := by norm_num
    have hlogr : Real.log (r : ℝ) ≤ r := Real.log_le_self (by positivity)
    have hlogpow : Real.log ((2 ^ r : ℕ) : ℝ) = (r : ℝ) * Real.log 2 := by
      rw [Nat.cast_pow, Real.log_pow]
      norm_num
    have hlog128 : Real.log (128 : ℝ) = 7 * Real.log 2 := by
      rw [h128, Real.log_pow]
      norm_num
    rw [show (N : ℝ) = (128 : ℝ) * r * (2 ^ r : ℕ) by norm_num [N],
      Real.log_mul (by positivity) hp0, Real.log_mul (by norm_num) hr0,
      hlog128, hlogpow]
    have hrR : (1 : ℝ) ≤ r := by exact_mod_cast hr1
    nlinarith
  have hlogpos : 0 < Real.log N := Real.log_pos (by
    exact_mod_cast (lt_of_lt_of_le (by decide : 1 < 256) hN))
  have hsdiv : (s : ℝ) ≤ (N : ℝ) / (4 * Real.log N) := by
    rw [le_div_iff₀ (mul_pos (by norm_num) hlogpos)]
    calc
      (s : ℝ) * (4 * Real.log N) ≤ (s : ℝ) * (4 * (9 * r)) := by
        gcongr
      _ ≤ ((2 ^ r : ℕ) : ℝ) * (4 * (9 * r)) := by
        apply mul_le_mul_of_nonneg_right
        · exact_mod_cast hsPow.le
        · positivity
      _ ≤ (N : ℝ) := by
        rw [show (N : ℝ) = 128 * (r : ℝ) * (2 ^ r : ℕ) by norm_num [N]]
        have hr : (0 : ℝ) ≤ r := by positivity
        have hp : (0 : ℝ) ≤ (2 ^ r : ℕ) := by positivity
        nlinarith [mul_nonneg hr hp]
  have hpiR : (s : ℝ) ≤ Nat.primeCounting N :=
    le_trans hsdiv (primeCounting_ge_quarter_div_log N hN)
  have hpi : s ≤ Nat.primeCounting N := by exact_mod_cast hpiR
  have hi : i < Nat.primeCounting N := by simp [s] at hpi ⊢; omega
  rw [Nat.primeCounting] at hi
  exact Nat.le_of_lt_succ
    ((Nat.lt_nth_iff_count_lt Nat.infinite_setOf_prime).mp hi)

/-- A common upper scale for all of the first `m` indexed primes. -/
def binaryPrimeScale (m : ℕ) : ℕ :=
  128 * (Nat.log 2 m + 1) * 2 ^ (Nat.log 2 m + 1)

theorem basePrimeProduct_le_binaryScale (m : ℕ) :
    (∏ i : Fin m, nthPrime i.val) ≤ (binaryPrimeScale m) ^ m := by
  calc
    (∏ i : Fin m, nthPrime i.val) ≤ ∏ _i : Fin m, binaryPrimeScale m := by
      apply Finset.prod_le_prod (fun _ _ => Nat.zero_le _)
      intro i _
      apply le_trans (nthPrime_le_binary_log i.val)
      unfold binaryPrimeScale
      have hr : Nat.log 2 (i.val + 1) + 1 ≤ Nat.log 2 m + 1 := by
        exact Nat.add_le_add_right (Nat.log_mono_right (by omega)) 1
      simpa [Nat.mul_assoc] using Nat.mul_le_mul_left 128
        (Nat.mul_le_mul hr (Nat.pow_le_pow_right (n := 2) (by decide) hr))
    _ = (binaryPrimeScale m) ^ m := by simp

/-- The near-optimal explicit cutoff. -/
def linearLogPrimeCutoff (m : ℕ) : ℕ :=
  2 ^ m * (binaryPrimeScale m) ^ m

theorem extendedPrimeProduct_le_linearLogCutoff (m P : ℕ)
    (hP : P ≤ 2 ^ (m - 1)) :
    P * (∏ i : Fin m, nthPrime i.val) ≤ linearLogPrimeCutoff m := by
  unfold linearLogPrimeCutoff
  apply Nat.mul_le_mul
  · exact le_trans hP (Nat.pow_le_pow_right (by decide) (Nat.sub_le m 1))
  · exact basePrimeProduct_le_binaryScale m

/-- Asymptotically sharp explicit parametric lower bound from the frame
construction. -/
theorem explicit_linearLog_cutoff_lower (m : ℕ) (hm : 6 ≤ m) :
    2 ^ (2 ^ (m - 2)) ≤ coveringCount (linearLogPrimeCutoff m) := by
  obtain ⟨P, _, hPlo, hPhi, hcount⟩ := exists_large_prime_frame_count m hm
  let k := P - 1
  let t := 2 ^ (m - 2)
  have ht_le_k : t ≤ k := by simp only [t, k]; omega
  have ht4 : 4 ≤ t := by
    have hexp : 2 ≤ m - 2 := by omega
    simpa [t] using (Nat.pow_le_pow_right (n := 2) (by decide) hexp)
  have hk4 : 4 ≤ k := le_trans ht4 ht_le_k
  have hpowm : 2 ^ m = 2 * 2 ^ (m - 1) := by
    calc
      2 ^ m = 2 ^ ((m - 1) + 1) := by congr 1 <;> omega
      _ = 2 ^ (m - 1) * 2 := by rw [pow_succ]
      _ = 2 * 2 ^ (m - 1) := Nat.mul_comm _ _
  have h2k : 2 * k ≤ 2 ^ m - 1 := by
    simp only [k]
    rw [hpowm]
    omega
  have hbin : 2 ^ k ≤ (2 ^ m - 1).choose k :=
    two_pow_le_choose_of_two_mul_le (2 ^ m - 1) k hk4 h2k
  have htk : 2 ^ t ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) ht_le_k
  have hperiod := extendedPrimeProduct_le_linearLogCutoff m P hPhi
  exact le_trans htk <| le_trans hbin <| le_trans hcount
    (coveringCount_mono hperiod)

/-- Stronger form obtained by counting all injections rather than only their
ranges. -/
theorem explicit_linearLog_cutoff_lower_strong (m : ℕ) (hm : 6 ≤ m) :
    2 ^ ((m - 1) * 2 ^ (m - 2)) ≤
      coveringCount (linearLogPrimeCutoff m) := by
  obtain ⟨P, _, hPlo, hPhi, hcount⟩ :=
    exists_large_prime_frame_descFactorial_count m hm
  have hdesc := two_pow_mul_le_descFactorial m P (by omega) hPlo hPhi
  have hperiod := extendedPrimeProduct_le_linearLogCutoff m P hPhi
  exact hdesc.trans (hcount.trans (coveringCount_mono hperiod))

end

end Erdos1188
