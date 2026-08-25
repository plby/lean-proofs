/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import PrimeNumberTheoremAnd.Consequences
import ErdosProblems.Erdos822.Core

/-!
# Prime intervals for Erdős Problem 822

The outer layer of GIL needs primes in `(X/2,X]`.  This file starts the
analytic bridge by recording the scale-change and logarithm comparisons
used to turn the repository's prime number theorem into a uniform lower
bound for such half-intervals.
-/

namespace Erdos822

open Filter Real

/-- Division by two tends to infinity on the positive real scale. -/
lemma real_div_two_tendsto_atTop :
    Tendsto (fun x : ℝ ↦ x / 2) atTop atTop := by
  simpa [div_eq_mul_inv] using
    tendsto_id.atTop_mul_pos (by positivity : (0 : ℝ) < (2 : ℝ)⁻¹)
      tendsto_const_nhds

/-- Eventually `log (x/2)` is at least four-fifths of `log x`.  This
elementary comparison is the denominator bookkeeping in the half-interval
prime count. -/
lemma eventually_four_fifths_log_le_log_half :
    ∀ᶠ x : ℝ in atTop,
      (4 / 5 : ℝ) * Real.log x ≤ Real.log (x / 2) := by
  have hlog := Real.tendsto_log_atTop.eventually
    (eventually_ge_atTop (5 * Real.log 2))
  filter_upwards [hlog, eventually_ge_atTop (2 : ℝ)] with x hxlog hx2
  have hxpos : 0 < x := by linarith
  rw [Real.log_div hxpos.ne' (by norm_num : (2 : ℝ) ≠ 0)]
  nlinarith

/-- A quantitative half-interval consequence of the repository's proved
prime number theorem.  The deliberately weak constant `1/10` is more than
enough for the outer layer of GIL. -/
theorem eventually_primeCounting_half_interval_lower :
    ∀ᶠ x : ℝ in atTop,
      x / (10 * Real.log x) ≤
        (Nat.primeCounting ⌊x⌋₊ : ℝ) -
          (Nat.primeCounting ⌊x / 2⌋₊ : ℝ) := by
  obtain ⟨e, he, hpi⟩ := pi_alt
  have hesmall := he.bound (by norm_num : (0 : ℝ) < 1 / 10)
  have hehalf := real_div_two_tendsto_atTop.eventually hesmall
  filter_upwards [hesmall, hehalf, eventually_four_fifths_log_le_log_half,
      eventually_ge_atTop (2 : ℝ)] with x hex hehx hlogcmp hx2
  have hxpos : 0 < x := by linarith
  have hxhalfpos : 0 < x / 2 := by positivity
  have hlogpos : 0 < Real.log x :=
    Real.log_pos (by linarith)
  have hloghalfpos : 0 < Real.log (x / 2) := by
    have : 0 < (4 / 5 : ℝ) * Real.log x := by positivity
    linarith
  have hexabs : |e x| ≤ (1 / 10 : ℝ) := by simpa [Real.norm_eq_abs] using hex
  have hehxabs : |e (x / 2)| ≤ (1 / 10 : ℝ) := by
    simpa [Real.norm_eq_abs] using hehx
  have hexlower : (9 / 10 : ℝ) ≤ 1 + e x := by
    linarith [neg_le_abs (e x)]
  have hehxupper : 1 + e (x / 2) ≤ (11 / 10 : ℝ) := by
    linarith [le_abs_self (e (x / 2))]
  have hfirst :
      (9 / 10 : ℝ) * x / Real.log x ≤
        (1 + e x) * x / Real.log x := by
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hexlower hxpos.le) hlogpos.le
  have hsecond :
      (1 + e (x / 2)) * (x / 2) / Real.log (x / 2) ≤
        (7 / 10 : ℝ) * x / Real.log x := by
    calc
      (1 + e (x / 2)) * (x / 2) / Real.log (x / 2) ≤
          (11 / 10 : ℝ) * (x / 2) / Real.log (x / 2) := by
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right hehxupper hxhalfpos.le) hloghalfpos.le
      _ ≤ (7 / 10 : ℝ) * x / Real.log x := by
        rw [div_le_div_iff₀ hloghalfpos hlogpos]
        nlinarith [mul_nonneg hxpos.le hlogpos.le]
  rw [hpi x, hpi (x / 2)]
  calc
    x / (10 * Real.log x) =
        (1 / 10 : ℝ) * x / Real.log x := by ring
    _ ≤ (9 / 10 : ℝ) * x / Real.log x -
        (7 / 10 : ℝ) * x / Real.log x := by
      have hscale :
          (1 / 10 : ℝ) * x / Real.log x ≤
            (1 / 5 : ℝ) * x / Real.log x := by
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right (by norm_num) hxpos.le) hlogpos.le
      calc
        (1 / 10 : ℝ) * x / Real.log x ≤
            (1 / 5 : ℝ) * x / Real.log x := hscale
        _ = (9 / 10 : ℝ) * x / Real.log x -
            (7 / 10 : ℝ) * x / Real.log x := by ring
    _ ≤ (1 + e x) * x / Real.log x -
        (1 + e (x / 2)) * (x / 2) / Real.log (x / 2) :=
      sub_le_sub hfirst hsecond

/-- Natural-number form of the preceding half-interval estimate. -/
theorem eventually_primeCounting_nat_half_interval_lower :
    ∀ᶠ n : ℕ in atTop,
      (n : ℝ) / (10 * Real.log n) ≤
        (Nat.primeCounting n : ℝ) -
          (Nat.primeCounting (n / 2) : ℝ) := by
  have h := tendsto_natCast_atTop_atTop.eventually
    eventually_primeCounting_half_interval_lower
  filter_upwards [h] with n hn
  have hfloor : ⌊(n : ℝ) / 2⌋₊ = n / 2 :=
    Nat.floor_div_eq_div n 2
  have hnfloor : ⌊(n : ℝ)⌋₊ = n := Nat.floor_natCast n
  rw [hfloor, hnfloor] at hn
  exact hn

/-- The exact bridge between the prime-counting function and the finite set
of primes in a closed-right interval.  We keep the left endpoint open because
that is the convention used by the outer GIL construction. -/
theorem card_filter_Ioc_prime_eq_primeCounting_sub (a b : ℕ) (hab : a ≤ b) :
    ((Finset.Ioc a b).filter Nat.Prime).card =
      Nat.primeCounting b - Nat.primeCounting a := by
  have hsubset : Nat.primesLE a ⊆ Nat.primesLE b :=
    Nat.primesLE_mono hab
  have hinterval :
      (Finset.Ioc a b).filter Nat.Prime =
        Nat.primesLE b \ Nat.primesLE a := by
    ext p
    simp [Nat.mem_primesLE]
    grind
  rw [hinterval, Finset.card_sdiff_of_subset hsubset,
    Nat.primesLE_card_eq_primeCounting, Nat.primesLE_card_eq_primeCounting]

/-- The finite set of primes in `(n/2,n]` eventually has the expected
order of magnitude from below.  This is the form used later when one outer
prime is chosen after a cofactor has been fixed. -/
theorem eventually_card_filter_Ioc_prime_half_interval_lower :
    ∀ᶠ n : ℕ in atTop,
      (n : ℝ) / (10 * Real.log n) ≤
        (((Finset.Ioc (n / 2) n).filter Nat.Prime).card : ℝ) := by
  filter_upwards [eventually_primeCounting_nat_half_interval_lower] with n hn
  have hdiv : n / 2 ≤ n := Nat.div_le_self n 2
  have hpi : Nat.primeCounting (n / 2) ≤ Nat.primeCounting n :=
    Nat.monotone_primeCounting hdiv
  rw [card_filter_Ioc_prime_eq_primeCounting_sub (n / 2) n hdiv,
    Nat.cast_sub hpi]
  exact hn

/-- Threshold form of the eventual half-interval estimate.  This is useful
when the quotient scale varies with a cofactor but is uniformly bounded
below. -/
theorem exists_card_filter_Ioc_prime_half_interval_lower_threshold :
    ∃ T : ℕ, ∀ n : ℕ, T ≤ n →
      (n : ℝ) / (10 * Real.log n) ≤
        (((Finset.Ioc (n / 2) n).filter Nat.Prime).card : ℝ) := by
  rcases Filter.eventually_atTop.1
      eventually_card_filter_Ioc_prime_half_interval_lower with ⟨T, hT⟩
  exact ⟨T, hT⟩

/-- Integer division associates in exactly the way needed by the outer
interval `(x/(2m),x/m]`.  Consequently its cardinality is the same
prime-counting difference as the half interval at the quotient scale. -/
theorem card_filter_outer_interval_eq_primeCounting_sub (x m : ℕ) :
    ((Finset.Ioc (x / (2 * m)) (x / m)).filter Nat.Prime).card =
      Nat.primeCounting (x / m) - Nat.primeCounting ((x / m) / 2) := by
  have hlower : x / (2 * m) = (x / m) / 2 := by
    calc
      x / (2 * m) = x / (m * 2) := by rw [Nat.mul_comm 2 m]
      _ = (x / m) / 2 := (Nat.div_div_eq_div_mul x m 2).symm
  rw [hlower]
  exact card_filter_Ioc_prime_eq_primeCounting_sub ((x / m) / 2) (x / m)
    (Nat.div_le_self (x / m) 2)

/-- For a fixed positive cofactor, the outer prime interval eventually has
the PNT lower bound at quotient scale. -/
theorem eventually_card_filter_outer_interval_lower_of_ne_zero (m : ℕ)
    (hm : m ≠ 0) :
    ∀ᶠ x : ℕ in atTop,
      ((x / m : ℕ) : ℝ) / (10 * Real.log (x / m : ℕ)) ≤
        (((Finset.Ioc (x / (2 * m)) (x / m)).filter Nat.Prime).card : ℝ) := by
  have hquotient := (Nat.tendsto_div_const_atTop hm).eventually
    eventually_card_filter_Ioc_prime_half_interval_lower
  filter_upwards [hquotient] with x hx
  rw [card_filter_outer_interval_eq_primeCounting_sub,
    ← card_filter_Ioc_prime_eq_primeCounting_sub ((x / m) / 2) (x / m)
      (Nat.div_le_self (x / m) 2)]
  exact hx

end Erdos822
