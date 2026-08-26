import ErdosProblems.Erdos4.EulerDensityBounds
import Mathlib.NumberTheory.Chebyshev

/-!
# Elementary prime supply in fixed-ratio intervals

Chebyshev's lower bound and his eventual upper bound suffice to supply
many primes in `(n,16n]`. This avoids using the prime number theorem or
any prime-distribution result in progressions for the source and reserve
prime sets.
-/

open Filter
open scoped BigOperators Topology

namespace Erdos4.ChebyshevIntervals

theorem eventually_log_succ_small :
    ∀ᶠ n : ℕ in atTop, Real.log (n + 1 : ℕ) ≤ (Real.log 2 / 2) * n := by
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hsmall := (Real.isLittleO_log_id_atTop.comp_tendsto
    (tendsto_natCast_atTop_atTop (R := ℝ))).bound (show 0 < Real.log 2 / 4 by positivity)
  filter_upwards [eventually_ge_atTop 4, hsmall] with n hn hs
  have hnR : (4 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  simp only [Function.comp_apply, id_eq, Real.norm_eq_abs,
    abs_of_nonneg (show (0 : ℝ) ≤ n from Nat.cast_nonneg n)] at hs
  have hlog : Real.log (n : ℝ) ≤ (Real.log 2 / 4) * n := (le_abs_self _).trans hs
  have harg : ((n + 1 : ℕ) : ℝ) ≤ 2 * (n : ℝ) := by push_cast; linarith
  have hc := Real.log_le_log (by positivity : (0 : ℝ) < ((n + 1 : ℕ) : ℝ)) harg
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hnpos.ne'] at hc
  nlinarith [mul_nonneg hlog2.le (sub_nonneg.mpr hnR)]

theorem eventually_primeCounting_lower :
    ∀ᶠ n : ℕ in atTop, 2 ≤ n ∧
      (Real.log 2 / 2) * n / Real.log n ≤ (Nat.primeCounting n : ℝ) := by
  filter_upwards [eventually_ge_atTop 2, eventually_log_succ_small] with n hn hs
  refine ⟨hn, ?_⟩
  have hlog : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast hn)
  calc
    _ ≤ ((n : ℝ) * Real.log 2 - Real.log (n + 1 : ℕ)) / Real.log n :=
      div_le_div_of_nonneg_right (by linarith) hlog.le
    _ ≤ _ := by simpa only [Nat.cast_add, Nat.cast_one] using Chebyshev.pi_ge n

theorem eventually_primeCounting_upper :
    ∀ᶠ n : ℕ in atTop,
      (Nat.primeCounting n : ℝ) ≤ (3 * Real.log 2) * n / Real.log n := by
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have h4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  have hupper := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually
    (Chebyshev.eventually_primeCounting_le hlog2)
  filter_upwards [hupper] with n hn
  simp only [Nat.floor_natCast, h4] at hn
  exact hn.trans_eq (by ring)

def primeInterval (a b : ℕ) : Finset ℕ := b.primesLE \ a.primesLE

theorem mem_primeInterval {a b p : ℕ} : p ∈ primeInterval a b ↔ p.Prime ∧ a < p ∧ p ≤ b := by
  simp only [primeInterval, Finset.mem_sdiff, Nat.mem_primesLE]
  constructor
  · rintro ⟨⟨hpb, hp⟩, hnot⟩
    exact ⟨hp, lt_of_not_ge (fun hpa => hnot ⟨hpa, hp⟩), hpb⟩
  · rintro ⟨hp, hap, hpb⟩
    exact ⟨⟨hpb, hp⟩, fun hh => (not_le_of_gt hap) hh.1⟩

theorem card_primeInterval {a b : ℕ} (hab : a ≤ b) :
    ((primeInterval a b).card : ℝ) = (Nat.primeCounting b : ℝ) - Nat.primeCounting a := by
  have hsub := Nat.primesLE_mono hab
  rw [primeInterval, Finset.card_sdiff_of_subset hsub, Nat.cast_sub (Finset.card_le_card hsub),
    Nat.primesLE_card_eq_primeCounting, Nat.primesLE_card_eq_primeCounting]

/-- A fixed-ratio interval provides a positive elementary prime budget. -/
theorem eventually_primeInterval_lower :
    ∀ᶠ n : ℕ in atTop, 16 ≤ n ∧
      Real.log 2 * n / Real.log n ≤ ((primeInterval n (16 * n)).card : ℝ) := by
  have hmul : Tendsto (fun n : ℕ => 16 * n) atTop atTop :=
    tendsto_atTop_mono (fun n => by omega : ∀ n : ℕ, n ≤ 16 * n) tendsto_id
  filter_upwards [eventually_ge_atTop 16, hmul.eventually eventually_primeCounting_lower,
    eventually_primeCounting_upper] with n hn hlo hup
  refine ⟨hn, ?_⟩
  have hnR : (16 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hlog : 0 < Real.log (n : ℝ) := Real.log_pos (by linarith)
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hlog16 : Real.log (16 : ℝ) ≤ Real.log n := Real.log_le_log (by norm_num) hnR
  have hlogN : Real.log (16 * n : ℕ) ≤ 2 * Real.log n := by
    rw [Nat.cast_mul, Nat.cast_ofNat, Real.log_mul (by norm_num) hnpos.ne']
    linarith
  have hmain : 4 * Real.log 2 * n / Real.log n ≤ (Nat.primeCounting (16 * n) : ℝ) := by
    calc
      _ = (Real.log 2 / 2) * (16 * n : ℕ) / (2 * Real.log n) := by push_cast; ring
      _ ≤ (Real.log 2 / 2) * (16 * n : ℕ) / Real.log (16 * n : ℕ) :=
        div_le_div_of_nonneg_left (by positivity)
          (Real.log_pos (by exact_mod_cast hlo.1)) hlogN
      _ ≤ _ := hlo.2
  rw [card_primeInterval (by omega : n ≤ 16 * n)]
  calc
    _ = 4 * Real.log 2 * n / Real.log n - (3 * Real.log 2) * n / Real.log n := by ring
    _ ≤ _ := sub_le_sub hmain hup

end Erdos4.ChebyshevIntervals
