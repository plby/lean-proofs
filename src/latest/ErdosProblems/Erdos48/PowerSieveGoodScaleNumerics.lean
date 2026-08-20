/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos48.PowerSievePrimeChainAssembly
import ErdosProblems.Erdos746.Asymptotics

/-!
# Elementary numerical inequalities for the power-sieve good scale

The analytic part of the argument supplies a shifted-smooth lower bound of
order `x / (q log x L^2)` and a prime-chain harmonic budget of order
`1 / (log x L^2)`.  This file verifies that, at the integer power scale, the
two finite inequalities required by `FLPAnalyticScale` hold for every
sufficiently large base.
-/

namespace Erdos48

open Filter
open scoped Topology

noncomputable section

private theorem eventually_const_mul_log_le_pow_six (C : ℝ) :
    ∀ᶠ n : ℕ in atTop,
      C * Real.log (n : ℝ) ≤ (n : ℝ) ^ 6 := by
  by_cases hC : C ≤ 0
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have hlog : 0 ≤ Real.log (n : ℝ) :=
      Real.log_nonneg (by exact_mod_cast hn)
    exact (mul_nonpos_of_nonpos_of_nonneg hC hlog).trans (by positivity)
  · have hCpos : 0 < C := lt_of_not_ge hC
    have hsmall := Erdos746.eventually_log_rpow_le_mul_rpow
      (1 : ℝ) (a := 6) (η := 1 / C) (by norm_num) (by positivity)
    filter_upwards [hsmall, eventually_ge_atTop 1] with n hn hn1
    have h := mul_le_mul_of_nonneg_left hn hCpos.le
    rw [Real.rpow_one] at h
    field_simp [hCpos.ne'] at h
    simpa [Real.rpow_natCast] using h

private theorem powerSieve_two_mul_denominator_mul_const_le
    (K L : ℕ) (hL : 1 ≤ L) :
    ∀ᶠ n : ℕ in atTop,
      2 * (960000000000 * (L : ℝ) ^ 4 *
          Real.log (powerSieveX n L : ℝ)) * K ≤
        (powerSieveX n L : ℝ) := by
  let C : ℝ :=
    2 * (960000000000 * (L : ℝ) ^ 4) * K * (240 * (L : ℝ))
  have hdecay := eventually_const_mul_log_le_pow_six C
  filter_upwards [hdecay, eventually_ge_atTop 1] with n hn hn1
  have hpow : (n : ℝ) ^ 6 ≤ (n : ℝ) ^ (240 * L) := by
    exact pow_le_pow_right₀ (by exact_mod_cast hn1) (by omega)
  rw [powerSieveX, Nat.cast_pow, Real.log_pow]
  calc
    2 * (960000000000 * (L : ℝ) ^ 4 *
          (((240 * L : ℕ) : ℝ) * Real.log (n : ℝ))) * K =
        C * Real.log (n : ℝ) := by
      dsimp [C]
      push_cast
      ring
    _ ≤ (n : ℝ) ^ 6 := hn
    _ ≤ (n : ℝ) ^ (240 * L) := hpow

private theorem powerSieve_three_mul_smooth_mul_denominator_le
    (L : ℕ) (hL : 1 ≤ L) :
    ∀ᶠ n : ℕ in atTop,
      3 * (powerSieveSmoothBound n L : ℝ) *
          (960000000000 * (L : ℝ) ^ 4 *
            Real.log (powerSieveX n L : ℝ)) ≤
        (powerSieveX n L : ℝ) := by
  let C : ℝ :=
    3 * (960000000000 * (L : ℝ) ^ 4) * (240 * (L : ℝ))
  have hdecay := eventually_const_mul_log_le_pow_six C
  filter_upwards [hdecay, eventually_ge_atTop 1] with n hn hn1
  have hExp : (120 * L - 6) + 6 = 120 * L := by omega
  have hpower :
      (powerSieveSmoothBound n L : ℝ) * (n : ℝ) ^ 6 =
        (n : ℝ) ^ (120 * L) := by
    rw [powerSieveSmoothBound, Nat.cast_pow, ← pow_add, hExp]
  have hmono : (n : ℝ) ^ (120 * L) ≤ (n : ℝ) ^ (240 * L) := by
    exact pow_le_pow_right₀ (by exact_mod_cast hn1) (by omega)
  rw [powerSieveX, Nat.cast_pow, Real.log_pow]
  calc
    3 * (((n ^ (120 * L - 6) : ℕ) : ℝ)) *
          (960000000000 * (L : ℝ) ^ 4 *
            (((240 * L : ℕ) : ℝ) * Real.log (n : ℝ))) =
        (powerSieveSmoothBound n L : ℝ) *
          (C * Real.log (n : ℝ)) := by
      dsimp [C, powerSieveSmoothBound]
      push_cast
      ring
    _ ≤ (powerSieveSmoothBound n L : ℝ) * (n : ℝ) ^ 6 := by
      gcongr
    _ = (n : ℝ) ^ (120 * L) := hpower
    _ ≤ (n : ℝ) ^ (240 * L) := hmono

private theorem root_mul_div_add_one_le_three_mul
    {u q : ℕ} (hq : q.Prime) (hqu : q ≤ u) :
    (q : ℝ) * (((u / (q - 1) + 1 : ℕ) : ℝ)) ≤ 3 * (u : ℝ) := by
  have hqTwo : 2 ≤ q := hq.two_le
  have hdiv : (q - 1) * (u / (q - 1)) ≤ u := Nat.mul_div_le _ _
  have hnat : q * (u / (q - 1) + 1) ≤ 3 * u := by
    have hqtwo : q ≤ 2 * (q - 1) := by omega
    nlinarith
  exact_mod_cast hnat

private theorem powerSieve_card_numeric
    {K n L : ℕ} (hL : 1 ≤ L) (hn : 2 ≤ n)
    (hden : 2 * (960000000000 * (L : ℝ) ^ 4 *
        Real.log (powerSieveX n L : ℝ)) * K ≤
      (powerSieveX n L : ℝ)) :
    (K : ℝ) + ((powerSieveX n L + 1 : ℕ) : ℝ) / 2 *
        powerSievePrimeChainBudget n L ≤
      powerSieveRawLower n L 2 := by
  have hxPos : (0 : ℝ) < powerSieveX n L := by
    exact_mod_cast pow_pos (by omega : 0 < n) (240 * L)
  have hlog : 0 < Real.log (powerSieveX n L : ℝ) := by
    apply Real.log_pos
    exact_mod_cast one_lt_pow₀ (by omega : 1 < n) (by omega : 240 * L ≠ 0)
  have hD : 0 < 960000000000 * (L : ℝ) ^ 4 *
      Real.log (powerSieveX n L : ℝ) := by positivity
  have hxOne : (1 : ℝ) ≤ powerSieveX n L := by
    exact_mod_cast Nat.one_le_pow (240 * L) n (by omega)
  unfold powerSievePrimeChainBudget powerSieveRawLower
  push_cast
  have hRhs :
      (powerSieveX n L : ℝ) /
          (240000000000 * (L : ℝ) ^ 4 * 2 *
            Real.log (powerSieveX n L : ℝ)) =
        (2 * (powerSieveX n L : ℝ)) /
          (960000000000 * (L : ℝ) ^ 4 *
            Real.log (powerSieveX n L : ℝ)) := by
    field_simp [hD.ne']
    ring
  rw [hRhs]
  apply (le_div_iff₀ hD).2
  have hK : (K : ℝ) *
      (960000000000 * (L : ℝ) ^ 4 *
        Real.log (powerSieveX n L : ℝ)) ≤
      (powerSieveX n L : ℝ) / 2 := by
    nlinarith
  have hx1 : ((powerSieveX n L : ℝ) + 1) / 2 ≤
      powerSieveX n L := by linarith
  field_simp [hD.ne']
  nlinarith

private theorem powerSieve_count_numeric
    {n L q : ℕ} (hL : 1 ≤ L) (hn : 2 ≤ n)
    (hq : q.Prime) (hqu : q ≤ powerSieveSmoothBound n L)
    (hden : 3 * (powerSieveSmoothBound n L : ℝ) *
        (960000000000 * (L : ℝ) ^ 4 *
          Real.log (powerSieveX n L : ℝ)) ≤
      (powerSieveX n L : ℝ)) :
    (((powerSieveSmoothBound n L) / (q - 1) + 1 : ℕ) : ℝ) +
        ((powerSieveX n L + 1 : ℕ) : ℝ) / q *
          powerSievePrimeChainBudget n L ≤
      powerSieveRawLower n L q := by
  let x : ℝ := powerSieveX n L
  let u : ℝ := powerSieveSmoothBound n L
  let D : ℝ := 960000000000 * (L : ℝ) ^ 4 * Real.log x
  have hxPos : 0 < x := by
    dsimp [x, powerSieveX]
    exact_mod_cast pow_pos (by omega : 0 < n) (240 * L)
  have hxOne : 1 ≤ x := by
    dsimp [x, powerSieveX]
    exact_mod_cast Nat.one_le_pow (240 * L) n (by omega)
  have hqPos : (0 : ℝ) < q := by exact_mod_cast hq.pos
  have hlog : 0 < Real.log x := by
    dsimp [x]
    apply Real.log_pos
    exact_mod_cast one_lt_pow₀ (by omega : 1 < n) (by omega : 240 * L ≠ 0)
  have hD : 0 < D := by dsimp [D]; positivity
  have hroot : (q : ℝ) *
      (((powerSieveSmoothBound n L / (q - 1) + 1 : ℕ) : ℝ)) ≤
      3 * u := by
    simpa only [u] using root_mul_div_add_one_le_three_mul hq hqu
  have hrootD : (q : ℝ) *
      (((powerSieveSmoothBound n L / (q - 1) + 1 : ℕ) : ℝ)) * D ≤ x := by
    calc
      (q : ℝ) *
          (((powerSieveSmoothBound n L / (q - 1) + 1 : ℕ) : ℝ)) * D ≤
        (3 * u) * D := mul_le_mul_of_nonneg_right hroot hD.le
      _ ≤ x := by simpa only [x, u, D] using hden
  unfold powerSievePrimeChainBudget powerSieveRawLower
  push_cast
  change ((powerSieveSmoothBound n L / (q - 1) : ℕ) : ℝ) + 1 +
      (x + 1) / (q : ℝ) * (1 / D) ≤ _
  have hRaw :
      (powerSieveX n L : ℝ) /
          (240000000000 * (L : ℝ) ^ 4 * (q : ℝ) *
            Real.log (powerSieveX n L : ℝ)) =
        4 * x / ((q : ℝ) * D) := by
    dsimp [x, D]
    field_simp [hqPos.ne', hlog.ne']
    ring
  rw [hRaw]
  rw [one_div]
  apply (le_div_iff₀ (mul_pos hqPos hD)).2
  have hx1 : x + 1 ≤ 2 * x := by linarith
  have hrootD' : (q : ℝ) *
      (((powerSieveSmoothBound n L / (q - 1) : ℕ) : ℝ) + 1) * D ≤ x := by
    simpa only [Nat.cast_add, Nat.cast_one] using hrootD
  calc
    ((((powerSieveSmoothBound n L / (q - 1) : ℕ) : ℝ) + 1) +
          (x + 1) / (q : ℝ) * D⁻¹) * ((q : ℝ) * D) =
        (q : ℝ) *
            (((powerSieveSmoothBound n L / (q - 1) : ℕ) : ℝ) + 1) * D +
          (x + 1) := by field_simp [hqPos.ne', hD.ne']
    _ ≤ x + 2 * x := add_le_add hrootD' hx1
    _ ≤ 4 * x := by linarith

/-- For a fixed power-sieve exponent and target cardinality, the two
numerical inequalities needed by the prime-chain constructor hold
simultaneously for all sufficiently large bases. -/
theorem eventually_powerSieve_goodScale_numerics (K L : ℕ) (hL : 1 ≤ L) :
    ∀ᶠ n : ℕ in atTop,
      (K : ℝ) + ((powerSieveX n L + 1 : ℕ) : ℝ) / 2 *
          powerSievePrimeChainBudget n L ≤
        powerSieveRawLower n L 2 ∧
      ∀ q : ℕ, q.Prime → q ≤ powerSieveSmoothBound n L →
        (((powerSieveSmoothBound n L) / (q - 1) + 1 : ℕ) : ℝ) +
            ((powerSieveX n L + 1 : ℕ) : ℝ) / q *
              powerSievePrimeChainBudget n L ≤
          powerSieveRawLower n L q := by
  have hcard := powerSieve_two_mul_denominator_mul_const_le K L hL
  have hcount := powerSieve_three_mul_smooth_mul_denominator_le L hL
  filter_upwards [hcard, hcount, eventually_ge_atTop 2] with n hcard hcount hn
  exact ⟨powerSieve_card_numeric hL hn hcard,
    fun q hq hqu ↦ powerSieve_count_numeric hL hn hq hqu hcount⟩

end

end Erdos48
