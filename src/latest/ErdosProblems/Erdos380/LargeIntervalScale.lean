import ErdosProblems.Erdos380.ShortExcessNegligible

/-! # Intervals with a large greatest prime factor contribute negligibly -/

open Filter
open scoped Topology

namespace Erdos380

theorem eventually_largeIntervalPrime_scale_bound : ∀ᶠ N : ℕ in atTop,
    ((badPointsWithLargeIntervalPrime N (largePrimeScale N)).card : ℝ) ≤
      8000 * N / (scaleBase N : ℝ) ^ 2002 := by
  obtain ⟨E, N₀, hbound⟩ := exists_largeIntervalPrime_card_bound
  filter_upwards [eventually_ge_atTop N₀, eventually_scaleBase_pow_le 6000,
    eventually_log_pow_le_scaleBase 1, eventually_initial_short_error_bound E]
      with N hN hpow hlog hinit
  have hS1 := one_le_scaleBase N
  have hS1R : (1 : ℝ) ≤ scaleBase N := by exact_mod_cast hS1
  have hSpos : (0 : ℝ) < scaleBase N := by linarith
  have hH : 0 < squareScale N := pow_pos (by omega : 0 < scaleBase N) 3000
  have hHsq : squareScale N ^ 2 ≤ 2 * N := by
    change (scaleBase N ^ 3000) ^ 2 ≤ 2 * N
    rw [← pow_mul]
    exact hpow.trans (by omega)
  have hD : 1 ≤ largePrimeScale N := one_le_pow₀ hS1
  have hcount := hbound N hN (squareScale N) (largePrimeScale N) hH hHsq hD
  have hE : (E : ℝ) ≤ 4 * N / (scaleBase N : ℝ) ^ 2002 := by
    have hnon : (0 : ℝ) ≤ (Nat.sqrt N : ℝ) + 2 * shortWidth N := by positivity
    linarith
  have hlog' : Real.log (N : ℝ) ≤ scaleBase N := by simpa only [pow_one] using hlog
  have hfirst : 7680 * (N : ℝ) * Real.log N / squareScale N ≤
      7680 * N / (scaleBase N : ℝ) ^ 2002 := by
    calc
      _ ≤ 7680 * (N : ℝ) * scaleBase N / (scaleBase N : ℝ) ^ 3000 := by
        rw [squareScale, Nat.cast_pow]
        exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hlog' (by positivity)) (by positivity)
      _ = 7680 * ((N : ℝ) / (scaleBase N : ℝ) ^ 2999) := by
        have h := scale_quotient_succ_mul N 2999
        calc
          _ = 7680 * (((N : ℝ) / (scaleBase N : ℝ) ^ (2999 + 1)) * scaleBase N) := by ring
          _ = _ := by rw [h]
      _ ≤ 7680 * ((N : ℝ) / (scaleBase N : ℝ) ^ 2002) :=
        mul_le_mul_of_nonneg_left (scale_quotient_mono N (by decide : 2002 ≤ 2999)) (by norm_num)
      _ = _ := by ring
  have hsecond : (16 * squareScale N + 4 : ℝ) * N / largePrimeScale N ≤
      20 * N / (scaleBase N : ℝ) ^ 2002 := by
    have hH1 : (1 : ℝ) ≤ squareScale N := by exact_mod_cast (one_le_pow₀ hS1 : 1 ≤ scaleBase N ^ 3000)
    have hcoef : (16 * squareScale N + 4 : ℝ) ≤ 20 * squareScale N := by linarith
    calc
      _ ≤ (20 * squareScale N : ℝ) * N / largePrimeScale N :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hcoef (Nat.cast_nonneg N)) (Nat.cast_nonneg _)
      _ = 20 * ((N : ℝ) / (scaleBase N : ℝ) ^ 3000) := by
        rw [squareScale, largePrimeScale, Nat.cast_pow, Nat.cast_pow,
          show 6000 = 3000 + 3000 from rfl, pow_add]
        field_simp
      _ ≤ 20 * ((N : ℝ) / (scaleBase N : ℝ) ^ 2002) :=
        mul_le_mul_of_nonneg_left (scale_quotient_mono N (by decide : 2002 ≤ 3000)) (by norm_num)
      _ = _ := by ring
  have hnon : 0 ≤ (N : ℝ) / (scaleBase N : ℝ) ^ 2002 := by positivity
  simp only [mul_div_assoc] at hcount hE hfirst hsecond ⊢
  linarith

end Erdos380
