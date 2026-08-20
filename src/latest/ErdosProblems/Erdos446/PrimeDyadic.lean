/-
Copyright (c) 2026 The Formal Conjectures Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors
-/

import ErdosProblems.Erdos446.FordModuli
import BoundedGaps.PrimeNumberTheorem.Analytic.PrimeCounting

/-!
# Erdős Problem 446: reciprocal primes in dyadic intervals

The prime number theorem supplies uniform upper and lower bounds for the
number, and hence for the reciprocal mass, of primes in `(x, 2x]`.
-/

namespace Erdos446

open Filter Finset Real
open scoped BigOperators Topology
open Asymptotics

/-- The primes in the half-open dyadic interval `(x, 2x]`. -/
def dyadicPrimes (x : ℕ) : Finset ℕ :=
  Nat.primesLE (2 * x) \ Nat.primesLE x

/-- The reciprocal prime mass in `(x, 2x]`. -/
noncomputable def dyadicPrimeMass (x : ℕ) : ℝ :=
  ∑ p ∈ dyadicPrimes x, 1 / (p : ℝ)

theorem mem_dyadicPrimes {x p : ℕ} :
    p ∈ dyadicPrimes x ↔ x < p ∧ p ≤ 2 * x ∧ p.Prime := by
  simp only [dyadicPrimes, Finset.mem_sdiff, Nat.mem_primesLE, not_and_or,
    not_le]
  aesop

/-- A fixed-relative-error form of the prime number theorem. -/
theorem eventually_primeCounting_tenth_bounds :
    ∀ᶠ x : ℕ in atTop,
      (9 / 10 : ℝ) * ((x : ℝ) / Real.log (x : ℝ)) ≤
          (Nat.primeCounting x : ℝ) ∧
      (Nat.primeCounting x : ℝ) ≤
          (11 / 10 : ℝ) * ((x : ℝ) / Real.log (x : ℝ)) := by
  have hpnt :=
    BoundedGaps.PrimeNumberTheorem.primeCounting_natCast_isEquivalent
  have herr := hpnt.isLittleO.def (show (0 : ℝ) < 1 / 10 by norm_num)
  have hmainPos : ∀ᶠ x : ℕ in atTop,
      0 ≤ (x : ℝ) / Real.log (x : ℝ) := by
    filter_upwards [eventually_ge_atTop 3] with x hx
    positivity
  filter_upwards [herr, hmainPos] with x hx hpos
  simp only [Pi.sub_apply, Real.norm_eq_abs, abs_of_nonneg hpos] at hx
  constructor <;> linarith [le_abs_self
    ((Nat.primeCounting x : ℝ) - (x : ℝ) / Real.log (x : ℝ)),
    neg_abs_le
      ((Nat.primeCounting x : ℝ) - (x : ℝ) / Real.log (x : ℝ))]

/-- Eventually `log (2x)` differs from `log x` by at most ten percent. -/
theorem eventually_log_two_mul_le_eleven_tenths :
    ∀ᶠ x : ℕ in atTop,
      Real.log (2 * x : ℝ) ≤
        (11 / 10 : ℝ) * Real.log (x : ℝ) := by
  have hlogTop : Tendsto (fun x : ℕ ↦ Real.log (x : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hevent : ∀ᶠ x : ℕ in atTop,
      10 * Real.log 2 ≤ Real.log (x : ℝ) :=
    hlogTop.eventually (eventually_ge_atTop (10 * Real.log 2))
  filter_upwards [hevent, eventually_ge_atTop 1] with x hx hxone
  have hxpos : (0 : ℝ) < x := by exact_mod_cast (show 0 < x by omega)
  rw [show (2 * x : ℝ) = 2 * (x : ℝ) by norm_num,
    Real.log_mul (by norm_num) hxpos.ne']
  linarith

/-- The PNT gives a two-sided dyadic prime-count estimate with explicit,
non-optimal absolute constants. -/
theorem eventually_dyadicPrimes_card_bounds :
    ∀ᶠ x : ℕ in atTop,
      (1 / 2 : ℝ) * ((x : ℝ) / Real.log (x : ℝ)) ≤
          (dyadicPrimes x).card ∧
      ((dyadicPrimes x).card : ℝ) ≤
          3 * ((x : ℝ) / Real.log (x : ℝ)) := by
  have hpnt := eventually_primeCounting_tenth_bounds
  have htwoTop : Tendsto (fun x : ℕ ↦ 2 * x) atTop atTop := by
    refine Filter.tendsto_atTop_mono' atTop ?_ Filter.tendsto_id
    filter_upwards with x
    simpa only [id_eq] using (show x ≤ 2 * x by omega)
  have hpntTwo := htwoTop.eventually eventually_primeCounting_tenth_bounds
  have hlog := eventually_log_two_mul_le_eleven_tenths
  have hlogPos : ∀ᶠ x : ℕ in atTop, 0 < Real.log (x : ℝ) := by
    filter_upwards [eventually_ge_atTop 3] with x hx
    exact Real.log_pos (by exact_mod_cast (show 1 < x by omega))
  filter_upwards [hpnt, hpntTwo, hlog, hlogPos, eventually_ge_atTop 3]
      with x hx hxTwo hlog hlogPos hxthree
  norm_num [Nat.cast_mul] at hxTwo
  have hlogTwoPos : 0 < Real.log (2 * x : ℝ) := by
    exact Real.log_pos (by exact_mod_cast (show 1 < 2 * x by omega))
  have hmono : Nat.primesLE x ⊆ Nat.primesLE (2 * x) :=
    Nat.primesLE_mono (by omega)
  have hcard : (dyadicPrimes x).card =
      Nat.primeCounting (2 * x) - Nat.primeCounting x := by
    rw [dyadicPrimes, Finset.card_sdiff_of_subset hmono,
      Nat.primesLE_card_eq_primeCounting,
      Nat.primesLE_card_eq_primeCounting]
  have hpiMono : Nat.primeCounting x ≤ Nat.primeCounting (2 * x) := by
    simpa [← Nat.primesLE_card_eq_primeCounting] using
      Finset.card_le_card hmono
  have hcardR : ((dyadicPrimes x).card : ℝ) =
      (Nat.primeCounting (2 * x) : ℝ) - (Nat.primeCounting x : ℝ) := by
    rw [hcard, Nat.cast_sub hpiMono]
  rw [hcardR]
  constructor
  · have hratio :
        (x : ℝ) / Real.log (x : ℝ) ≤
          (11 / 10 : ℝ) *
            ((x : ℝ) / Real.log (2 * x : ℝ)) := by
      have hxnonneg : (0 : ℝ) ≤ x := by positivity
      have hmul :
          (x : ℝ) * Real.log (2 * x : ℝ) ≤
            ((11 / 10 : ℝ) * (x : ℝ)) * Real.log (x : ℝ) := by
        nlinarith [mul_nonneg hxnonneg
          (sub_nonneg.mpr hlog)]
      calc
        (x : ℝ) / Real.log (x : ℝ) ≤
            ((11 / 10 : ℝ) * (x : ℝ)) /
              Real.log (2 * x : ℝ) :=
          (div_le_div_iff₀ hlogPos hlogTwoPos).2 hmul
        _ = (11 / 10 : ℝ) *
            ((x : ℝ) / Real.log (2 * x : ℝ)) := by ring
    have hmainNonneg : 0 ≤ (x : ℝ) / Real.log (x : ℝ) := by positivity
    calc
      (1 / 2 : ℝ) * ((x : ℝ) / Real.log (x : ℝ))
          ≤ (59 / 110 : ℝ) * ((x : ℝ) / Real.log (x : ℝ)) := by
            exact mul_le_mul_of_nonneg_right (by norm_num) hmainNonneg
      _ ≤ (9 / 10 : ℝ) *
              ((2 * x : ℝ) / Real.log (2 * x : ℝ)) -
            (11 / 10 : ℝ) *
              ((x : ℝ) / Real.log (x : ℝ)) := by
            have hscaled := mul_le_mul_of_nonneg_left hratio
              (show (0 : ℝ) ≤ 18 / 11 by norm_num)
            calc
              (59 / 110 : ℝ) * ((x : ℝ) / Real.log (x : ℝ)) =
                  (18 / 11 : ℝ) * ((x : ℝ) / Real.log (x : ℝ)) -
                    (11 / 10 : ℝ) * ((x : ℝ) / Real.log (x : ℝ)) := by ring
              _ ≤ (18 / 10 : ℝ) *
                    ((x : ℝ) / Real.log (2 * x : ℝ)) -
                    (11 / 10 : ℝ) * ((x : ℝ) / Real.log (x : ℝ)) := by
                      exact sub_le_sub_right (by nlinarith) _
              _ = (9 / 10 : ℝ) *
                    ((2 * x : ℝ) / Real.log (2 * x : ℝ)) -
                    (11 / 10 : ℝ) * ((x : ℝ) / Real.log (x : ℝ)) := by
                      norm_num [Nat.cast_mul]
                      ring
      _ ≤ (Nat.primeCounting (2 * x) : ℝ) -
            (Nat.primeCounting x : ℝ) := sub_le_sub hxTwo.1 hx.2
  · calc
      (Nat.primeCounting (2 * x) : ℝ) -
            (Nat.primeCounting x : ℝ)
          ≤ (Nat.primeCounting (2 * x) : ℝ) := by
            have hpiNonneg : (0 : ℝ) ≤ (Nat.primeCounting x : ℝ) := by positivity
            linarith
      _ ≤ (11 / 10 : ℝ) *
          ((2 * x : ℝ) / Real.log (2 * x : ℝ)) := hxTwo.2
      _ ≤ 3 * ((x : ℝ) / Real.log (x : ℝ)) := by
        have hlogMono : Real.log (x : ℝ) ≤ Real.log (2 * x : ℝ) := by
          apply Real.log_le_log (by positivity)
          exact_mod_cast (show x ≤ 2 * x by omega)
        rw [show (2 * x : ℝ) = 2 * (x : ℝ) by norm_num]
        have hdiv : (x : ℝ) / Real.log (2 * x : ℝ) ≤
            (x : ℝ) / Real.log (x : ℝ) := by
          exact div_le_div_of_nonneg_left (by positivity) hlogPos hlogMono
        have hmainNonneg : 0 ≤ (x : ℝ) / Real.log (x : ℝ) := by positivity
        calc
          (11 / 10 : ℝ) *
              ((2 * x : ℝ) / Real.log (2 * x : ℝ)) =
              (22 / 10 : ℝ) *
                ((x : ℝ) / Real.log (2 * x : ℝ)) := by
                  norm_num [Nat.cast_mul]
                  ring
          _ ≤ (22 / 10 : ℝ) *
                ((x : ℝ) / Real.log (x : ℝ)) :=
            mul_le_mul_of_nonneg_left hdiv (by norm_num)
          _ ≤ 3 * ((x : ℝ) / Real.log (x : ℝ)) :=
            mul_le_mul_of_nonneg_right (by norm_num) hmainNonneg

/-- Reciprocal prime mass in a large dyadic interval is comparable with
`1 / log x`. -/
theorem eventually_dyadicPrimeMass_bounds :
    ∀ᶠ x : ℕ in atTop,
      (1 / 4 : ℝ) / Real.log (x : ℝ) ≤ dyadicPrimeMass x ∧
      dyadicPrimeMass x ≤ 3 / Real.log (x : ℝ) := by
  filter_upwards [eventually_dyadicPrimes_card_bounds,
      eventually_ge_atTop 3] with x hx hxthree
  have hxpos : (0 : ℝ) < x := by positivity
  have hlogPos : 0 < Real.log (x : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < x by omega))
  have hlower :
      ((dyadicPrimes x).card : ℝ) * (1 / (2 * x : ℝ)) ≤
        dyadicPrimeMass x := by
    rw [dyadicPrimeMass]
    calc
      ((dyadicPrimes x).card : ℝ) * (1 / (2 * x : ℝ)) =
          ∑ p ∈ dyadicPrimes x, 1 / (2 * x : ℝ) := by
            simp [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ p ∈ dyadicPrimes x, 1 / (p : ℝ) := by
        apply Finset.sum_le_sum
        intro p hp
        have hpPos : (0 : ℝ) < p := by
          exact_mod_cast (mem_dyadicPrimes.mp hp).2.2.pos
        exact one_div_le_one_div_of_le hpPos
          (by exact_mod_cast (mem_dyadicPrimes.mp hp).2.1)
  have hupper : dyadicPrimeMass x ≤
      ((dyadicPrimes x).card : ℝ) * (1 / (x : ℝ)) := by
    rw [dyadicPrimeMass]
    calc
      ∑ p ∈ dyadicPrimes x, 1 / (p : ℝ) ≤
          ∑ p ∈ dyadicPrimes x, 1 / (x : ℝ) := by
        apply Finset.sum_le_sum
        intro p hp
        exact one_div_le_one_div_of_le hxpos
          (by exact_mod_cast (mem_dyadicPrimes.mp hp).1.le)
      _ = ((dyadicPrimes x).card : ℝ) * (1 / (x : ℝ)) := by
        simp [Finset.sum_const, nsmul_eq_mul]
  constructor
  · calc
      (1 / 4 : ℝ) / Real.log (x : ℝ) =
          ((1 / 2 : ℝ) * ((x : ℝ) / Real.log (x : ℝ))) *
            (1 / (2 * x : ℝ)) := by field_simp; ring
      _ ≤ ((dyadicPrimes x).card : ℝ) * (1 / (2 * x : ℝ)) := by
        exact mul_le_mul_of_nonneg_right hx.1 (by positivity)
      _ ≤ dyadicPrimeMass x := hlower
  · calc
      dyadicPrimeMass x ≤
          ((dyadicPrimes x).card : ℝ) * (1 / (x : ℝ)) := hupper
      _ ≤ (3 * ((x : ℝ) / Real.log (x : ℝ))) *
          (1 / (x : ℝ)) := by
        exact mul_le_mul_of_nonneg_right hx.2 (by positivity)
      _ = 3 / Real.log (x : ℝ) := by field_simp

end Erdos446
