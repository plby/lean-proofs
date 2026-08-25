import ErdosProblems.Erdos387.UniformAnalyticInputs

/-!
# Enough primes for every small modulus

At height `2^k`, the unconditional shifted Siegel--Walfisz theorem supplies
more than `2*k^D` primes congruent to one modulo each prime at most `k^D`.
The exponent `D` is fixed before taking the limit in `k`.
-/

namespace Erdos694

open Filter

lemma eventually_dyadic_primes (D : ℕ) :
    ∀ᶠ k : ℕ in atTop, ∀ q : ℕ, q.Prime → q ≤ k ^ D →
      2 * k ^ D ≤ ((Finset.Ioc (2 ^ k) (2 * 2 ^ k)).filter
        (fun p => p.Prime ∧ p % q = 1 % q)).card := by
  obtain ⟨X₀, hX₀⟩ := Erdos387.shiftedSiegelWalfiszLower D
  have hpow : Tendsto (fun k : ℕ => (2 : ℕ) ^ k) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by decide)
  have hpoly : ∀ᶠ k : ℕ in atTop,
      16 * (k ^ D) ^ 2 * (k + 1) ≤ 2 ^ k := by
    have h := (isLittleO_pow_const_const_pow_of_one_lt (R := ℝ) (D + D + 1)
      (by norm_num : (1 : ℝ) < 2)).bound (by norm_num : (0 : ℝ) < 1 / 32)
    filter_upwards [h, eventually_ge_atTop 1] with k hk hk1
    simp only [Real.norm_eq_abs,
      abs_of_nonneg (show (0 : ℝ) ≤ (k : ℝ) ^ (D + D + 1) by positivity),
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ k)] at hk
    have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk1
    have hle : (16 : ℝ) * ((k : ℝ) ^ D) ^ 2 * (k + 1) ≤ (2 : ℝ) ^ k := by
      rw [pow_add, pow_add, pow_one] at hk
      nlinarith [mul_le_mul_of_nonneg_left hkR (sq_nonneg ((k : ℝ) ^ D))]
    exact_mod_cast hle
  filter_upwards [hpow.eventually_ge_atTop X₀, hpoly] with k hk₀ hk
  intro q hq hqY
  have hscale : q ≤ (Nat.log 2 (2 ^ k) + 1) ^ D := by
    rw [Nat.log_pow (by decide)]
    exact hqY.trans (Nat.pow_le_pow_left (Nat.le_succ k) D)
  have hc := hX₀ (2 ^ k) q 1 0 hk₀ hq.two_le hscale (Nat.zero_le _)
    (Nat.coprime_one_left q)
  simp only [Nat.sub_zero, Nat.log_pow (by decide : 1 < 2)] at hc
  apply le_trans _ hc
  apply (Nat.le_div_iff_mul_le (by have := hq.pos; positivity)).mpr
  calc
    2 * k ^ D * (8 * q * (k + 1)) ≤
        2 * k ^ D * (8 * k ^ D * (k + 1)) := by gcongr
    _ = 16 * (k ^ D) ^ 2 * (k + 1) := by ring
    _ ≤ 2 ^ k := hk

end Erdos694
