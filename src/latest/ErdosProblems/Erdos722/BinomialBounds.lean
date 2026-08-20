/-
Copyright 2026 The Lean-Proofs Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
import Mathlib

/-!
# Elementary lower bounds for fixed binomial coefficients

These estimates provide the explicit polynomial lower bounds used in the
regularity boost and its Bernoulli tail calculation.
-/

namespace Erdos722.BinomialBounds

open Finset

noncomputable section

/-- The standard descending-factorial lower bound, specialized to reals. -/
theorem pow_sub_div_factorial_le_choose (m s : ℕ) :
    (((m + 1 - s : ℕ) : ℝ) ^ s) / (s.factorial : ℝ) ≤
      (Nat.choose m s : ℝ) := by
  exact Nat.pow_le_choose s m

/-- If `n` is at least twice the fixed shift and order, then every factor
in `choose (n-a) s` is at least `n/2`. -/
theorem half_pow_div_factorial_le_choose_sub
    (n a s : ℕ) (hn : 2 * (a + s) ≤ n) :
    (((n : ℝ) / 2) ^ s) / (s.factorial : ℝ) ≤
      (Nat.choose (n - a) s : ℝ) := by
  have hbaseNat : n ≤ 2 * (n - a + 1 - s) := by omega
  have hbase : (n : ℝ) / 2 ≤ (n - a + 1 - s : ℕ) := by
    rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 2)]
    exact_mod_cast (by simpa [Nat.mul_comm] using hbaseNat)
  exact (div_le_div_of_nonneg_right
      (pow_le_pow_left₀ (by positivity) hbase s)
      (by positivity : (0 : ℝ) ≤ s.factorial)).trans
    (pow_sub_div_factorial_le_choose (n - a) s)

/-- A denominator-free version convenient for natural-number comparisons.
-/
theorem pow_le_factorial_mul_choose_sub
    (n a s : ℕ) (hn : 2 * (a + s) ≤ n) :
    n ^ s ≤ 2 ^ s * s.factorial * Nat.choose (n - a) s := by
  have h := half_pow_div_factorial_le_choose_sub n a s hn
  have hfac : (0 : ℝ) < s.factorial := by positivity
  have htwo : (0 : ℝ) < (2 : ℝ) ^ s := by positivity
  have hreal : ((n : ℝ) ^ s) ≤
      (((2 ^ s * s.factorial * Nat.choose (n - a) s : ℕ) : ℝ)) := by
    push_cast
    rw [div_pow] at h
    have h' := (div_le_iff₀ hfac).mp h
    have h'' := (div_le_iff₀ htwo).mp h'
    calc
      (n : ℝ) ^ s ≤
          ((Nat.choose (n - a) s : ℝ) * s.factorial) * 2 ^ s := h''
      _ = 2 ^ s * (s.factorial : ℝ) * Nat.choose (n - a) s := by ring
  exact_mod_cast hreal

end

end Erdos722.BinomialBounds
