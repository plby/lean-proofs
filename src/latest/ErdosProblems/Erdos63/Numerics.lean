/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import Mathlib

/-!
# Numerical lemmas for Erdős Problem 63

The Liu--Montgomery input used in the solution supplies cycles of every even
length in an interval of the form

`[(Real.log ell) ^ 8, ell]`.

This file isolates the elementary fact which turns such an interval into a
dyadic cycle length.  The chosen exponent is the exponent of the largest
power of two at most `ell`.  Consequently that power is strictly larger than
`ell / 2`; the standard estimate `(log ell) ^ 8 ≤ ell / 2` then puts it in the
required interval.
-/

namespace Erdos63.Numerics

open Filter Asymptotics

/-- Every sufficiently large real `ell` satisfies `(log ell) ^ 8 ≤ ell / 2`. -/
theorem eventually_log_pow_eight_le_half :
    ∀ᶠ ell : ℝ in atTop, Real.log ell ^ 8 ≤ ell / 2 := by
  have hsmall :=
    (Real.isLittleO_pow_log_id_atTop (n := 8)).bound
      (show (0 : ℝ) < 1 / 2 by norm_num)
  filter_upwards [hsmall, eventually_ge_atTop (0 : ℝ)] with ell hell hell_nonneg
  have hpow_abs : |Real.log ell| ^ 8 = Real.log ell ^ 8 := by
    rw [← abs_pow, abs_of_nonneg (by positivity : 0 ≤ Real.log ell ^ 8)]
  simpa [Real.norm_eq_abs, hpow_abs, abs_of_nonneg hell_nonneg, div_eq_mul_inv,
    mul_comm] using hell

/--
If `ell` is at least `2 ^ N` and its logarithmic lower endpoint is at most
`ell / 2`, then the interval `[(log ell)^8, ell]` contains an even dyadic
integer `2 ^ n` with `n ≥ N`.
-/
theorem exists_two_pow_in_log_interval {ell : ℝ} {N : ℕ} (hN : 1 ≤ N)
    (hlarge : (2 : ℝ) ^ N ≤ ell)
    (hlog : Real.log ell ^ 8 ≤ ell / 2) :
    ∃ n : ℕ, N ≤ n ∧ Even (2 ^ n) ∧
      Real.log ell ^ 8 ≤ (2 ^ n : ℕ) ∧ (2 ^ n : ℕ) ≤ ell := by
  have hell_one : (1 : ℝ) ≤ ell := by
    calc
      (1 : ℝ) ≤ (2 : ℝ) ^ N := one_le_pow₀ (by norm_num)
      _ ≤ ell := hlarge
  obtain ⟨n, hn_upper, hn_next⟩ :=
    exists_nat_pow_near (x := ell) (y := (2 : ℝ)) hell_one (by norm_num)
  have hn_ge : N ≤ n := by
    by_contra hn
    have hsucc : n + 1 ≤ N := by omega
    have hpows : (2 : ℝ) ^ (n + 1) ≤ (2 : ℝ) ^ N := by
      gcongr
      norm_num
    exact (not_lt_of_ge (hpows.trans hlarge)) hn_next
  have hn_pos : n ≠ 0 := by omega
  have hn_even : Even (2 ^ n) := (Nat.even_pow).2 ⟨by norm_num, hn_pos⟩
  have hn_lower_real : Real.log ell ^ 8 ≤ (2 : ℝ) ^ n := by
    calc
      Real.log ell ^ 8 ≤ ell / 2 := hlog
      _ ≤ (2 : ℝ) ^ n := by
        rw [pow_succ] at hn_next
        nlinarith
  have hn_lower : Real.log ell ^ 8 ≤ (2 ^ n : ℕ) := by
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using hn_lower_real
  have hn_upper' : (2 ^ n : ℕ) ≤ ell := by
    exact_mod_cast hn_upper
  exact ⟨n, hn_ge, hn_even, hn_lower, hn_upper'⟩

/--
Predicate-valued form of `exists_two_pow_in_log_interval`.  It can be applied
directly to an assertion that every even integer in the Liu--Montgomery
interval occurs as a cycle length.
-/
theorem exists_two_pow_of_even_log_interval {ell : ℝ} {N : ℕ} (hN : 1 ≤ N)
    (hlarge : (2 : ℝ) ^ N ≤ ell)
    (hlog : Real.log ell ^ 8 ≤ ell / 2) (P : ℕ → Prop)
    (hinterval : ∀ m : ℕ, Even m → Real.log ell ^ 8 ≤ m → m ≤ ell → P m) :
    ∃ n : ℕ, N ≤ n ∧ P (2 ^ n) := by
  obtain ⟨n, hn, heven, hlower, hupper⟩ :=
    exists_two_pow_in_log_interval hN hlarge hlog
  exact ⟨n, hn, hinterval (2 ^ n) heven hlower hupper⟩

/--
Along any filter on which `ell` tends to infinity, dyadic integers of
arbitrarily large exponent eventually lie in `[(log ell)^8, ell]`.
-/
theorem eventually_exists_two_pow_in_log_interval {α : Type*} {l : Filter α}
    {ell : α → ℝ} (hell : Tendsto ell l atTop) (N : ℕ) :
    ∀ᶠ a in l, ∃ n : ℕ, N ≤ n ∧ Even (2 ^ n) ∧
      Real.log (ell a) ^ 8 ≤ (2 ^ n : ℕ) ∧ (2 ^ n : ℕ) ≤ ell a := by
  have hlog := hell.eventually eventually_log_pow_eight_le_half
  have hlarge := hell.eventually (eventually_ge_atTop ((2 : ℝ) ^ (max N 1)))
  filter_upwards [hlog, hlarge] with a ha_log ha_large
  obtain ⟨n, hn, heven, hlower, hupper⟩ :=
    exists_two_pow_in_log_interval (N := max N 1) (le_max_right _ _) ha_large ha_log
  exact ⟨n, (le_max_left _ _).trans hn, heven, hlower, hupper⟩

/--
Abstract Liu--Montgomery wrapper.  If, eventually, a predicate holds for every
even integer in the logarithmic interval, then it eventually holds at a power
of two with exponent beyond any prescribed cutoff.
-/
theorem eventually_exists_two_pow_of_even_log_interval {α : Type*} {l : Filter α}
    {ell : α → ℝ} (hell : Tendsto ell l atTop) (P : α → ℕ → Prop)
    (hinterval : ∀ᶠ a in l, ∀ m : ℕ, Even m →
      Real.log (ell a) ^ 8 ≤ m → m ≤ ell a → P a m) (N : ℕ) :
    ∀ᶠ a in l, ∃ n : ℕ, N ≤ n ∧ P a (2 ^ n) := by
  filter_upwards [eventually_exists_two_pow_in_log_interval hell N, hinterval]
    with a ha hcycle
  obtain ⟨n, hn, heven, hlower, hupper⟩ := ha
  exact ⟨n, hn, hcycle (2 ^ n) heven hlower hupper⟩

/--
Unfiltered form of the numerical reduction.  It is enough to have
Liu--Montgomery intervals with arbitrarily large upper endpoint: for every
exponent cutoff, one of those intervals supplies a dyadic value past the
cutoff.  The logarithmic estimate is discharged internally.
-/
theorem exists_two_pow_of_arbitrarily_large_even_log_intervals (P : ℕ → Prop)
    (hinterval : ∀ B : ℝ, ∃ ell : ℝ, B ≤ ell ∧
      ∀ m : ℕ, Even m → Real.log ell ^ 8 ≤ m → m ≤ ell → P m) (N : ℕ) :
    ∃ n : ℕ, N ≤ n ∧ P (2 ^ n) := by
  obtain ⟨L, hL⟩ := Filter.eventually_atTop.mp eventually_log_pow_eight_le_half
  obtain ⟨ell, hell, hell_interval⟩ :=
    hinterval (max L ((2 : ℝ) ^ (max N 1)))
  have hlog : Real.log ell ^ 8 ≤ ell / 2 :=
    hL ell ((le_max_left _ _).trans hell)
  have hlarge : (2 : ℝ) ^ (max N 1) ≤ ell :=
    (le_max_right _ _).trans hell
  obtain ⟨n, hn, heven, hlower, hupper⟩ :=
    exists_two_pow_in_log_interval (N := max N 1) (le_max_right _ _) hlarge hlog
  exact ⟨n, (le_max_left _ _).trans hn,
    hell_interval (2 ^ n) heven hlower hupper⟩

end Erdos63.Numerics
