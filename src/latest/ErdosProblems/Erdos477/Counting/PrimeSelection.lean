/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
A small prime avoiding a given nonzero integer, using Chebyshev's proved lower bound.
Formal author: Codex.
-/

import Mathlib

namespace Erdos477.Counting

open Filter

lemma exists_theta_linear_lower : ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
    Real.log 2 / 2 * N ≤ Chebyshev.theta N := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hevent : ∀ᶠ x : ℝ in atTop, Real.log x ≤ Real.log 2 / 16 * Real.sqrt x := by
    filter_upwards [(isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).bound
      (show 0 < Real.log 2 / 16 by positivity)] with x hx
    have hx' : |Real.log x| ≤ Real.log 2 / 16 * Real.sqrt x := by
      simpa only [Real.norm_eq_abs, ← Real.sqrt_eq_rpow,
        abs_of_nonneg (Real.sqrt_nonneg x)] using hx
    exact (le_abs_self _).trans hx'
  obtain ⟨A, hA⟩ := eventually_atTop.mp hevent
  refine ⟨⌈max 4 A⌉₊, ?_⟩
  intro N hN
  have hbase : max 4 A ≤ (N : ℝ) := (Nat.le_ceil _).trans (Nat.cast_le.mpr hN)
  have hN4 : (4 : ℝ) ≤ N := (le_max_left _ _).trans hbase
  have hN0 : (0 : ℝ) ≤ N := by linarith
  have hNpos : (0 : ℝ) < N := by linarith
  have hlog := hA N ((le_max_right _ _).trans hbase)
  have hsqrt : Real.sqrt N ≤ (N : ℝ) := Real.sqrt_le_self_iff.mpr (Or.inr (by linarith))
  have herror : 2 * Real.sqrt N * Real.log N ≤ Real.log 2 / 8 * N := by
    have hm := mul_le_mul_of_nonneg_left hlog (show 0 ≤ 2 * Real.sqrt N by positivity)
    have heq := congrArg (fun x : ℝ => Real.log 2 * x) (Real.sq_sqrt hN0)
    nlinarith only [hm, heq]
  have hlogN1 : Real.log ((N : ℝ) + 1) ≤ Real.log 2 + Real.log N := by
    have h := Real.log_le_log (show 0 < (N : ℝ) + 1 by positivity)
      (show (N : ℝ) + 1 ≤ 2 * N by linarith)
    rwa [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hNpos.ne'] at h
  have hsmall : Real.log ((N : ℝ) + 1) ≤ 5 * Real.log 2 / 16 * N := by
    have hm := mul_le_mul_of_nonneg_left hsqrt (show 0 ≤ Real.log 2 / 16 by positivity)
    have hn := mul_le_mul_of_nonneg_left hN4 hlog2.le
    nlinarith only [hlogN1, hlog, hm, hn]
  have htheta := Chebyshev.theta_ge N
  nlinarith only [htheta, herror, hsmall, mul_nonneg hlog2.le hN0]

/-- Every nonzero integer has a prime nondivisor of size logarithmic in
its absolute value. The constant is absolute, not dependent on the integer. -/
theorem exists_small_prime_nondivisor : ∃ C : ℝ, 0 < C ∧ ∀ D : ℤ, D ≠ 0 →
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ C * (Real.log |(D : ℝ)| + 1) ∧ ¬ (p : ℤ) ∣ D := by
  obtain ⟨N₀, htheta⟩ := exists_theta_linear_lower
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let C : ℝ := N₀ + 4 / Real.log 2 + 1
  refine ⟨C, by dsimp only [C]; positivity, ?_⟩
  intro D hD
  let L : ℝ := Real.log |(D : ℝ)|
  have hDabs : (1 : ℝ) ≤ |(D : ℝ)| := by
    exact_mod_cast (Int.one_le_abs hD)
  have hL : 0 ≤ L := Real.log_nonneg hDabs
  let N : ℕ := N₀ + ⌈4 * (L + 1) / Real.log 2⌉₊
  have hN0 : N₀ ≤ N := Nat.le_add_right _ _
  have hNlower : 4 * (L + 1) / Real.log 2 ≤ (N : ℝ) := by
    have h := Nat.le_ceil (4 * (L + 1) / Real.log 2)
    dsimp only [N]
    push_cast
    linarith [show (0 : ℝ) ≤ N₀ from Nat.cast_nonneg N₀]
  have hthetaL : L < Chebyshev.theta N := by
    have hn := (div_le_iff₀ hlog2).mp hNlower
    have ht := htheta N hN0
    nlinarith only [hn, ht, hL]
  have hNupper : (N : ℝ) ≤ C * (L + 1) := by
    have hceil := Nat.ceil_lt_add_one (show 0 ≤ 4 * (L + 1) / Real.log 2 by positivity)
    dsimp only [N, C]
    push_cast
    have hN0nonneg : (0 : ℝ) ≤ N₀ := Nat.cast_nonneg _
    have hprod := mul_nonneg hN0nonneg hL
    simp only [div_eq_mul_inv] at hceil ⊢
    nlinarith only [hceil, hprod, hL]
  have hex : ∃ p ∈ Nat.primesLE N, ¬ (p : ℤ) ∣ D := by
    by_contra h
    push Not at h
    have hprod : primorial N ∣ D.natAbs := by
      apply Finset.prod_primes_dvd D.natAbs
      · intro p hp
        exact (Nat.prime_of_mem_primesLE hp).prime
      · intro p hp
        exact Int.natCast_dvd.mp (h p hp)
    have hle : primorial N ≤ D.natAbs := Nat.le_of_dvd (Int.natAbs_pos.mpr hD) hprod
    have hlog := Real.log_le_log (Nat.cast_pos.mpr (primorial_pos N))
      (show (primorial N : ℝ) ≤ D.natAbs by exact_mod_cast hle)
    have heq : Chebyshev.theta N = Real.log (primorial N) := by
      rw [Chebyshev.theta_eq_log_primorial, Nat.floor_natCast]
    have hcast : (D.natAbs : ℝ) = |(D : ℝ)| := by
      simpa only [Int.cast_natCast, Int.cast_abs] using
        congrArg (fun z : ℤ => (z : ℝ)) (Int.natCast_natAbs D)
    rw [← heq, hcast] at hlog
    exact (not_lt_of_ge hlog) hthetaL
  obtain ⟨p, hp, hpd⟩ := hex
  exact ⟨p, (Nat.mem_primesLE.mp hp).2,
    (Nat.cast_le.mpr (Nat.mem_primesLE.mp hp).1).trans hNupper, hpd⟩

#print axioms exists_small_prime_nondivisor
-- 'Erdos477.Counting.exists_small_prime_nondivisor' depends on axioms:
-- [propext, Classical.choice, Quot.sound]

end Erdos477.Counting
