/-
Copyright (c) 2026 The Formal Conjectures Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors
-/

import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# From weighted prime-ideal sums to counting functions

This file isolates the analytic conversion used after a prime ideal theorem.
It is deliberately independent of number fields: the arithmetic construction
of the counting, Chebyshev, and von Mangoldt functions supplies the hypotheses.
-/

namespace Erdos980.NaturalChebotarev.PrimeIdealTheorem

open Asymptotics Filter

noncomputable section

open scoped BigOperators

/-- The logarithm used to remove the Chebyshev weight at a natural endpoint. -/
def endpointLog (n : ℕ) : ℝ := Real.log (n : ℝ)

/-- Count a nonnegative multiplicity sequence supported on possible prime
norms.  Starting at `2` records the only support fact needed for logarithmic
deweighting. -/
def multiplicityCount (a : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ m ∈ Finset.Icc 2 n, a m

/-- The associated Chebyshev-weighted sum. -/
def multiplicityChebyshev (a : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ m ∈ Finset.Icc 2 n, a m * Real.log (m : ℝ)

theorem multiplicityCount_nonneg {a : ℕ → ℝ}
    (ha : ∀ m, 0 ≤ a m) (n : ℕ) :
    0 ≤ multiplicityCount a n := by
  exact Finset.sum_nonneg fun m _ ↦ ha m

theorem multiplicityChebyshev_nonneg {a : ℕ → ℝ}
    (ha : ∀ m, 0 ≤ a m) (n : ℕ) :
    0 ≤ multiplicityChebyshev a n := by
  apply Finset.sum_nonneg
  intro m hm
  have hm2 : 2 ≤ m := (Finset.mem_Icc.mp hm).1
  exact mul_nonneg (ha m) (Real.log_nonneg (by exact_mod_cast hm2.trans' (by norm_num)))

/-- On nonnegative multiplicities, every logarithmic weight at an endpoint
`m ≤ n` is at most `log n`.  This is the elementary lower half of the
deweighting sandwich. -/
theorem multiplicityChebyshev_le_log_mul_count
    {a : ℕ → ℝ} (ha : ∀ m, 0 ≤ a m) {n : ℕ} (hn : 2 ≤ n) :
    multiplicityChebyshev a n ≤
      endpointLog n * multiplicityCount a n := by
  rw [multiplicityChebyshev, multiplicityCount, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro m hm
  have hmIcc := Finset.mem_Icc.mp hm
  have hmpos : (0 : ℝ) < (m : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) hmIcc.1)
  have hnpos : (0 : ℝ) < (n : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) hn)
  have hmn : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hmIcc.2
  have hlog : Real.log (m : ℝ) ≤ Real.log (n : ℝ) :=
    Real.strictMonoOn_log.monotoneOn hmpos hnpos hmn
  simpa only [endpointLog, mul_comm] using
    mul_le_mul_of_nonneg_left hlog (ha m)

/-- In quotient form, the weighted sum is a lower bound for the unweighted
count.  This formulation is the one used in asymptotic squeeze arguments. -/
theorem multiplicityChebyshev_div_log_le_count
    {a : ℕ → ℝ} (ha : ∀ m, 0 ≤ a m) {n : ℕ} (hn : 2 ≤ n) :
    multiplicityChebyshev a n / endpointLog n ≤ multiplicityCount a n := by
  have hlog : 0 < endpointLog n := by
    rw [endpointLog]
    exact Real.log_pos (by exact_mod_cast (lt_of_lt_of_le (by norm_num : 1 < 2) hn))
  apply (div_le_iff₀ hlog).2
  simpa only [mul_comm] using multiplicityChebyshev_le_log_mul_count ha hn

/-- The prime-number-theorem scale on natural endpoints. -/
def pntScale (c : ℝ) : ℕ → ℝ :=
  (fun n : ℕ ↦ c * (n : ℝ)) / endpointLog

@[simp]
theorem pntScale_apply (c : ℝ) (n : ℕ) :
    pntScale c n = c * ((n : ℝ) / endpointLog n) := by
  simp [pntScale, div_eq_mul_inv, mul_assoc]

/-- Dividing a Chebyshev-weighted asymptotic by the endpoint logarithm gives
the expected prime-counting main term.

No positivity assumption on `c` is needed for this purely asymptotic step.
In an application, `weighted` is the sum of `log (Norm P)` over the prime
ideals (or Frobenius classes) being counted. -/
theorem weighted_div_log_isEquivalent
    {weighted : ℕ → ℝ} (c : ℝ)
    (hweighted : weighted ~[atTop] (fun n ↦ c * (n : ℝ))) :
    weighted / endpointLog ~[atTop] pntScale c := by
  exact hweighted.div
    (Asymptotics.IsEquivalent.refl : endpointLog ~[atTop] endpointLog)

/-- Generic weighted-to-unweighted conversion.

The first hypothesis is the Chebyshev-weighted prime(-ideal) theorem.  The
second is exactly the deweighting estimate normally proved by finite Abel
summation (or by splitting the sum at `x^(1-ε)`).  Its statement makes the
arithmetic obligation explicit: after division by the endpoint logarithm,
the discrepancy between the actual nonnegative multiplicity count and the
weighted sum must be negligible on the `x / log x` scale.

This theorem is also valid for multisets: `count` may count prime ideals of a
given norm with multiplicity rather than merely indicate whether an integer
is a prime norm. -/
theorem count_isEquivalent_of_weighted
    {count weighted : ℕ → ℝ} (c : ℝ)
    (hweighted : weighted ~[atTop] (fun n ↦ c * (n : ℝ)))
    (hdeweight :
      (count - weighted / endpointLog) =o[atTop] pntScale c) :
    count ~[atTop] pntScale c := by
  have hmain := weighted_div_log_isEquivalent c hweighted
  rw [show count = weighted / endpointLog + (count - weighted / endpointLog) by
    funext n
    simp only [Pi.add_apply, Pi.sub_apply, Pi.div_apply]
    ring]
  exact hmain.add_isLittleO hdeweight

/-- Remove a negligible prime-power contribution from a von-Mangoldt-style
prime-ideal theorem.  The convention `mangoldt - weighted` is useful because
this difference is nonnegative in the usual application. -/
theorem weighted_isEquivalent_of_mangoldt
    {mangoldt weighted main : ℕ → ℝ}
    (hmangoldt : mangoldt ~[atTop] main)
    (hprimePowers : (mangoldt - weighted) =o[atTop] main) :
    weighted ~[atTop] main := by
  rw [show weighted = mangoldt - (mangoldt - weighted) by
    funext n
    simp only [Pi.sub_apply]
    ring]
  exact hmangoldt.sub_isLittleO hprimePowers

/-- Combined `ψ → θ → π` conversion for a prime-norm multiplicity sequence.

The two error hypotheses correspond to the two elementary arithmetic facts
which remain after a `ψ(x) ~ c x` prime ideal theorem:

* higher prime powers contribute `o(x)`;
* removal of the logarithmic prime weight contributes `o(x / log x)`.

Both are explicit inputs, so users of this theorem cannot silently identify
the weighted and unweighted counting functions. -/
theorem count_isEquivalent_of_mangoldt
    {count weighted mangoldt : ℕ → ℝ} (c : ℝ)
    (hmangoldt : mangoldt ~[atTop] (fun n ↦ c * (n : ℝ)))
    (hprimePowers :
      (mangoldt - weighted) =o[atTop] (fun n ↦ c * (n : ℝ)))
    (hdeweight :
      (count - weighted / endpointLog) =o[atTop] pntScale c) :
    count ~[atTop] pntScale c := by
  apply count_isEquivalent_of_weighted c
  · exact weighted_isEquivalent_of_mangoldt hmangoldt hprimePowers
  · exact hdeweight

end

end Erdos980.NaturalChebotarev.PrimeIdealTheorem
