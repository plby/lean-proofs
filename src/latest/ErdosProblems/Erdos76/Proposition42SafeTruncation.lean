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
# The safe truncation arithmetic in Proposition 4.2

For a monochromatic use of Corollary 2.12, the missing capacity on the two
parts is `k + r`, not `m + r`.  Consequently the cross packing can safely be
truncated at

`r = min(|X₁|,|X₂|) - k - 4`.

At this safe value the master inequality is already contradictory except in
one exact boundary configuration.  Isolating that configuration prevents an
unsound use of the larger truncation value printed in the source proof.
-/

namespace Erdos76

/-- The safe-truncation master inequality leaves only
`n=24, k=3, m=0, (|X₁|,|X₂|)=(11,13)`. -/
theorem proposition42_safe_truncation_boundary_from_parts
    (n k m a b : ℕ)
    (hn : 22 ≤ n)
    (hk : k ≤ n / 8)
    (hm : m ≤ k)
    (hab : a + b = n)
    (habOrder : a ≤ b)
    (hpart : k + 4 ≤ a)
    (hmaster :
      2 * ((a - k - 4 : ℕ) : ℝ) - (n : ℝ) / 4 +
          3 * (m : ℝ) - (k : ℝ) +
            ((n : ℝ) / 2 - (a : ℝ)) ^ 2 ≤ 0) :
    n = 24 ∧ k = 3 ∧ m = 0 ∧ a = 11 ∧ b = 13 := by
  have hka : k + 4 ≤ a := hpart
  have hsub : a - k - 4 + k + 4 = a := by omega
  have hsubR : (((a - k - 4 : ℕ) : ℝ)) =
      (a : ℝ) - k - 4 := by
    have hkA : k ≤ a := by omega
    have hfour : 4 ≤ a - k := by omega
    rw [Nat.cast_sub hfour, Nat.cast_sub hkA]
    push_cast
    rfl
  rw [hsubR] at hmaster
  have hk8 : 8 * k ≤ n := by omega
  have hkR : (8 : ℝ) * k ≤ n := by exact_mod_cast hk8
  have hmR : (0 : ℝ) ≤ m := by positivity
  have habR : (a : ℝ) + b = n := by exact_mod_cast hab
  have horderR : (a : ℝ) ≤ b := by exact_mod_cast habOrder
  have hsquare : 0 ≤ ((n : ℝ) / 2 - (a : ℝ) - 1) ^ 2 := sq_nonneg _
  have hnUpper : n ≤ 24 := by
    have hnR : (22 : ℝ) ≤ n := by exact_mod_cast hn
    by_contra h
    have hn25R : (25 : ℝ) ≤ n := by exact_mod_cast (by omega : 25 ≤ n)
    nlinarith
  interval_cases n <;>
    norm_num at hk hmaster hab ⊢
  · have hk2 : k ≤ 2 := hk
    have hk2R : (k : ℝ) ≤ 2 := by exact_mod_cast hk2
    nlinarith [sq_nonneg ((11 : ℝ) - a - 1)]
  · have hk2 : k ≤ 2 := hk
    have hk2R : (k : ℝ) ≤ 2 := by exact_mod_cast hk2
    nlinarith [sq_nonneg (((23 : ℝ) / 2) - a - 1)]
  · have hk3 : k ≤ 3 := hk
    have hk3R : (k : ℝ) ≤ 3 := by exact_mod_cast hk3
    have hnonneg :
        0 ≤ ((12 : ℝ) - a - 1) ^ 2 + 3 * m + 3 * (3 - k) := by
      positivity
    have hkEq : k = 3 := by
      by_contra h
      have hk2 : k ≤ 2 := by omega
      have hk2R : (k : ℝ) ≤ 2 := by exact_mod_cast hk2
      nlinarith [sq_nonneg ((12 : ℝ) - a - 1)]
    have hmEq : m = 0 := by
      subst k
      have hm3 : m ≤ 3 := hm
      by_contra h
      have hm1 : 1 ≤ m := by omega
      have hm1R : (1 : ℝ) ≤ m := by exact_mod_cast hm1
      nlinarith [sq_nonneg ((12 : ℝ) - a - 1)]
    subst k
    subst m
    have haR : (a : ℝ) = 11 := by
      have hsq0 : ((12 : ℝ) - a - 1) ^ 2 ≤ 0 := by
        nlinarith
      nlinarith [sq_nonneg ((12 : ℝ) - a - 1)]
    have haEq : a = 11 := by exact_mod_cast haR
    subst a
    omega

end Erdos76
