/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import ErdosProblems.Erdos182.JSGlobalParameters
import ErdosProblems.Erdos182.JSCodegreeCleaning

/-!
# Power estimates for the Janzer--Sudakov codegree-cleaning cutoff

This file verifies the integer power inequality needed to instantiate the
caller-chosen-cutoff form of codegree cleaning on every global degree bucket.
All divisions are natural-number divisions, so the proof explicitly accounts
for their rounding.
-/

namespace Erdos182
namespace JSGlobalParameters

open Filter

/-- The elementary exponent inequality behind the caller-chosen codegree
cleaning cutoff.  The left maximum degree is `2^T`, while the codegree cutoff
is `2^(T-T/(2*k))`. -/
theorem cleaning_power_le_cutoff_pow {k T : ℕ} (hk : 0 < k)
    (hlog : Nat.clog 2 (k ^ (k + 1)) ≤ T / 2) :
    k ^ (k + 1) * (2 ^ T) ^ (k - 1) ≤
      (2 ^ (T - T / (2 * k))) ^ k := by
  have hklog : k ^ (k + 1) ≤ 2 ^ Nat.clog 2 (k ^ (k + 1)) :=
    Nat.le_pow_clog (by omega) _
  have hfactor : k ^ (k + 1) ≤ 2 ^ (T / 2) :=
    hklog.trans (Nat.pow_le_pow_right (by omega) hlog)
  have hdiv : k * (T / (2 * k)) ≤ T / 2 := by
    apply (Nat.le_div_iff_mul_le (by omega : 0 < 2)).2
    calc
      k * (T / (2 * k)) * 2 = (2 * k) * (T / (2 * k)) := by ring
      _ ≤ T := Nat.mul_div_le T (2 * k)
  have hexp : T / 2 + T * (k - 1) ≤ (T - T / (2 * k)) * k := by
    let q := T / (2 * k)
    have hqk : q * k ≤ T / 2 := by simpa [q, mul_comm] using hdiv
    have hhalf : T / 2 + T / 2 ≤ T := by omega
    have hsum : q * k + T / 2 ≤ T := by
      calc
        q * k + T / 2 ≤ T / 2 + T / 2 := Nat.add_le_add_right hqk _
        _ ≤ T := hhalf
    have hrem : T / 2 ≤ T - q * k :=
      Nat.le_sub_of_add_le (by simpa [add_comm] using hsum)
    calc
      T / 2 + T * (k - 1) ≤ (T - q * k) + T * (k - 1) := by gcongr
      _ = (T - q) * k := by
        rw [Nat.sub_mul]
        have hkdecomp : T * k = T * (k - 1) + T := by
          conv_lhs => rw [show k = (k - 1) + 1 by omega]
          ring
        rw [hkdecomp, Nat.add_sub_assoc (hqk.trans (Nat.div_le_self _ _))]
        ring
  calc
    k ^ (k + 1) * (2 ^ T) ^ (k - 1) ≤
        2 ^ (T / 2) * (2 ^ T) ^ (k - 1) := by gcongr
    _ = 2 ^ (T / 2 + T * (k - 1)) := by
      rw [← pow_mul]
      exact (pow_add _ _ _).symm
    _ ≤ 2 ^ ((T - T / (2 * k)) * k) :=
      Nat.pow_le_pow_right (by omega) hexp
    _ = (2 ^ (T - T / (2 * k))) ^ k := by rw [pow_mul]

/-- The literal `D+1` form consumed by codegree cleaning. -/
theorem cleaning_power_le_cutoff_succ_pow {k T : ℕ} (hk : 0 < k)
    (hlog : Nat.clog 2 (k ^ (k + 1)) ≤ T / 2) :
    k ^ (k + 1) * (2 ^ T) ^ (k - 1) ≤
      (2 ^ (T - T / (2 * k)) + 1) ^ k := by
  exact (cleaning_power_le_cutoff_pow hk hlog).trans
    (Nat.pow_le_pow_left (Nat.le_succ _) _)

/-- Every global upper exponent is at least the initial `10*r` budget. -/
theorem ten_mul_le_upperExponent (r Delta i q : ℕ) :
    10 * r ≤ upperExponent r Delta i q := by
  have hone : 1 ≤ 2 ^ i * ell Delta := by
    exact Nat.one_le_iff_ne_zero.mpr
      (mul_ne_zero (pow_ne_zero _ (by omega)) (ne_of_gt (ell_pos Delta)))
  calc
    10 * r ≤ 10 * r + q + 1 := by omega
    _ ≤ (10 * r + q + 1) * (2 ^ i * ell Delta) :=
      Nat.le_mul_of_pos_right _ hone
    _ = upperExponent r Delta i q := by
      simp [upperExponent, slots, slotWidth]

/-- The sharper lower bound retaining the iterated-logarithm factor. -/
theorem ten_mul_ell_le_upperExponent (r Delta i q : ℕ) :
    10 * r * ell Delta ≤ upperExponent r Delta i q := by
  have hpow : 1 ≤ 2 ^ i := Nat.one_le_two_pow
  calc
    10 * r * ell Delta ≤ (10 * r + q + 1) * ell Delta := by
      gcongr
      omega
    _ ≤ (10 * r + q + 1) * (2 ^ i * ell Delta) := by
      gcongr
      simpa [mul_comm] using Nat.le_mul_of_pos_right (ell Delta) hpow
    _ = upperExponent r Delta i q := by
      simp [upperExponent, slots, slotWidth]

/-- A threshold on the global parameter `r` makes the cleaning power estimate
hold for every `Delta` and every bucket, with no asymptotics left. -/
theorem cleaning_power_upperExponent_of_clog_le_five_mul
    {k r Delta i q : ℕ} (hk : 0 < k)
    (hr : Nat.clog 2 (k ^ (k + 1)) ≤ 5 * r) :
    k ^ (k + 1) * (2 ^ upperExponent r Delta i q) ^ (k - 1) ≤
      (2 ^ (upperExponent r Delta i q -
        upperExponent r Delta i q / (2 * k)) + 1) ^ k := by
  apply cleaning_power_le_cutoff_succ_pow hk
  apply (Nat.le_div_iff_mul_le (by omega : 0 < 2)).2
  calc
    Nat.clog 2 (k ^ (k + 1)) * 2 ≤ (5 * r) * 2 := by gcongr
    _ = 10 * r := by ring
    _ ≤ upperExponent r Delta i q := ten_mul_le_upperExponent _ _ _ _

private theorem ell_ge_of_double_pow_le {B Delta : ℕ}
    (hDelta : 2 ^ (2 ^ B) ≤ Delta) : B ≤ ell Delta := by
  have hinner : 2 ^ B ≤ Nat.log 2 Delta := by
    calc
      2 ^ B = Nat.log 2 (2 ^ (2 ^ B)) := by
        rw [Nat.log_pow (by omega : 1 < 2)]
      _ ≤ Nat.log 2 Delta := Nat.log_mono_right hDelta
  have houter : B ≤ Nat.log 2 (Nat.log 2 Delta) := by
    calc
      B = Nat.log 2 (2 ^ B) := by
        rw [Nat.log_pow (by omega : 1 < 2)]
      _ ≤ Nat.log 2 (Nat.log 2 Delta) := Nat.log_mono_right hinner
  simp only [ell]
  omega

/-- For fixed positive `k,r`, the caller-cutoff power condition holds
eventually in `Delta`, uniformly over every global degree bucket. -/
theorem eventually_cleaning_power_upperExponent (k r : ℕ)
    (hk : 0 < k) (hr : 0 < r) :
    ∀ᶠ Delta : ℕ in atTop, ∀ i q : ℕ,
      k ^ (k + 1) * (2 ^ upperExponent r Delta i q) ^ (k - 1) ≤
        (2 ^ (upperExponent r Delta i q -
          upperExponent r Delta i q / (2 * k)) + 1) ^ k := by
  let B := Nat.clog 2 (k ^ (k + 1))
  filter_upwards [eventually_ge_atTop (2 ^ (2 ^ B))] with Delta hDelta
  intro i q
  apply cleaning_power_le_cutoff_succ_pow hk
  have hBell : B ≤ ell Delta := ell_ge_of_double_pow_le hDelta
  apply (Nat.le_div_iff_mul_le (by omega : 0 < 2)).2
  calc
    B * 2 ≤ ell Delta * 2 := by gcongr
    _ ≤ 10 * r * ell Delta := by
      have hell : 1 ≤ ell Delta := ell_pos Delta
      have hr' : 1 ≤ r := hr
      nlinarith
    _ ≤ upperExponent r Delta i q := ten_mul_ell_le_upperExponent _ _ _ _

end JSGlobalParameters
end Erdos182
