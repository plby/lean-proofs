import ErdosProblems.Erdos1188.ExplicitLower
import Mathlib.NumberTheory.Chebyshev

/- Ported from Lean 4.31.0 to 4.33.0; module names and elaboration options adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Polynomial upper bound for indexed primes and a sharper cutoff
-/

namespace Erdos1188

open scoped BigOperators

noncomputable section

/-- A direct consequence of Mathlib's explicit Chebyshev lower bound:
`π(n) ≥ sqrt(n)/8` for `n≥256`. -/
theorem primeCounting_ge_sqrt_div_eight (n : ℕ) (hn : 256 ≤ n) :
    Real.sqrt n / 8 ≤ (Nat.primeCounting n : ℝ) := by
  have hN : (256 : ℝ) ≤ n := by exact_mod_cast hn
  have hN0 : (0 : ℝ) ≤ n := by positivity
  have hN1 : (1 : ℝ) < n := lt_of_lt_of_le (by norm_num) hN
  have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have h := Real.lt_log_one_add_of_pos (x := (1 : ℝ)) (by norm_num)
    norm_num at h ⊢
    linarith
  have hlogN : Real.log (n : ℝ) ≤ 2 * Real.sqrt n := by
    have h := Real.log_le_rpow_div hN0 (show (0 : ℝ) < 1 / 2 by norm_num)
    rw [← Real.sqrt_eq_rpow] at h
    norm_num at h ⊢
    linarith
  have hsqrt_sq : (Real.sqrt n) ^ 2 = (n : ℝ) := Real.sq_sqrt hN0
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
  have hleft : Real.sqrt n / 8 * Real.log n ≤ (n : ℝ) / 4 := by
    have hsqrt : 0 ≤ Real.sqrt n := Real.sqrt_nonneg _
    nlinarith
  have hdiv : Real.sqrt n / 8 ≤
      ((n : ℝ) * Real.log 2 - Real.log ((n : ℝ) + 1)) / Real.log n := by
    rw [le_div_iff₀ (Real.log_pos hN1)]
    exact le_trans hleft hnum
  exact le_trans hdiv (Chebyshev.pi_ge n)

/-- A completely explicit polynomial upper bound on the indexed primes. -/
theorem nthPrime_le_quadratic (i : ℕ) :
    nthPrime i ≤ (16 * (i + 1)) ^ 2 := by
  let N := (16 * (i + 1)) ^ 2
  have hN : 256 ≤ N := by
    simp only [N]
    nlinarith [Nat.zero_le i]
  have hpi := primeCounting_ge_sqrt_div_eight N hN
  have hsqrt : Real.sqrt N = (16 * (i + 1) : ℕ) := by
    rw [show (N : ℝ) = ((16 * (i + 1) : ℕ) : ℝ) ^ 2 by norm_num [N]]
    rw [Real.sqrt_sq_eq_abs, abs_of_nonneg]
    positivity
  rw [hsqrt] at hpi
  norm_num at hpi
  have hpi' : ((2 * (i + 1) : ℕ) : ℝ) ≤ Nat.primeCounting N := by
    push_cast
    linarith
  have hpinat : 2 * (i + 1) ≤ Nat.primeCounting N := by exact_mod_cast hpi'
  have hi : i < Nat.primeCounting N := by omega
  rw [Nat.primeCounting] at hi
  exact Nat.le_of_lt_succ
    ((Nat.lt_nth_iff_count_lt Nat.infinite_setOf_prime).mp hi)

/-- Product form of the quadratic prime bound. -/
theorem basePrimeProduct_le_quadratic (m : ℕ) :
    (∏ i : Fin m, nthPrime i.val) ≤ ((16 * m) ^ 2) ^ m := by
  calc
    (∏ i : Fin m, nthPrime i.val) ≤ ∏ _i : Fin m, (16 * m) ^ 2 := by
      apply Finset.prod_le_prod (fun _ _ => Nat.zero_le _)
      intro i _
      exact le_trans (nthPrime_le_quadratic i.val)
        (Nat.pow_le_pow_left (by omega : 16 * (i.val + 1) ≤ 16 * m) 2)
    _ = ((16 * m) ^ 2) ^ m := by simp

/-- The sharper explicit cutoff used by the quadratic-prime construction. -/
def quadraticPrimeCutoff (m : ℕ) : ℕ :=
  2 ^ m * ((16 * m) ^ 2) ^ m

theorem extendedPrimeProduct_le_quadraticCutoff (m P : ℕ)
    (hP : P ≤ 2 ^ (m - 1)) :
    P * (∏ i : Fin m, nthPrime i.val) ≤ quadraticPrimeCutoff m := by
  unfold quadraticPrimeCutoff
  apply Nat.mul_le_mul
  · exact le_trans hP (Nat.pow_le_pow_right (by decide) (Nat.sub_le m 1))
  · exact basePrimeProduct_le_quadratic m

/-- Sharpened fully explicit bound with a cutoff whose logarithm is
`2m log m + O(m)`. -/
theorem explicit_quadratic_cutoff_lower (m : ℕ) (hm : 6 ≤ m) :
    2 ^ (2 ^ (m - 2)) ≤ coveringCount (quadraticPrimeCutoff m) := by
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
  have hperiod := extendedPrimeProduct_le_quadraticCutoff m P hPhi
  exact le_trans htk <| le_trans hbin <| le_trans hcount
    (coveringCount_mono hperiod)

end

end Erdos1188
