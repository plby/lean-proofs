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

import ErdosProblems.Erdos13.Erdos13Additive

/-!
# The Lev--Smelianski lower bound

This file proves the normalized self-sum form of the `3k - 4` theorem.  The
proof is the cyclic-reduction argument of Lev and Smelianski: reduce modulo
the diameter, apply Kneser's theorem to the reduced sumset, and count the
integer lifts of its stabilizer cosets.
-/

open scoped Pointwise

namespace Erdos874

/-- **Lev--Smelianski's self-sum inequality.**

Let `A` be a normalized finite set of natural numbers with endpoints `0` and
`q`.  Then its ordinary pair sumset has at least

`min (q + |A|) (3|A| - 3)`

elements.  The gcd-one hypothesis is the normalization that rules out a
proper common-difference progression. -/
theorem lev_smelianski_self_sum
    (A : Finset ℕ) {q : ℕ}
    (hA0 : 0 ∈ A) (hqA : q ∈ A)
    (hA_le : ∀ a ∈ A, a ≤ q)
    (hgcd : A.gcd id = 1) (hk : 3 ≤ A.card) :
    min (q + A.card) (3 * A.card - 3) ≤ (A + A).card := by
  have hq : 0 < q := by
    by_contra hq0
    have hqzero : q = 0 := Nat.eq_zero_of_not_pos hq0
    have hsub : A ⊆ {0} := by
      intro a ha
      simp only [Finset.mem_singleton]
      have := hA_le a ha
      omega
    have hcardle : A.card ≤ 1 := by
      simpa using Finset.card_le_card hsub
    omega
  have hAIcc : A ⊆ Finset.Icc 0 q := by
    intro a ha
    simp only [Finset.mem_Icc]
    exact ⟨Nat.zero_le a, hA_le a ha⟩
  have hgcdNat : A.gcd (fun n : ℕ => n) = 1 := by
    change A.gcd (fun n : ℕ => n) = 1 at hgcd
    exact hgcd
  have hgcd' : (A ∪ A).gcd (fun n => (n : ℤ)) = 1 := by
    rw [Finset.union_self, Erdos13Additive.nat_int_finset_gcd, hgcdNat]
    norm_num
  have h := Erdos13Additive.ruzsa_normalized_diameter_bound
    hAIcc hAIcc (le_refl q) hq hA0 hqA hA0 hqA hgcd'
  simp only [Nat.min_self] at h
  convert h using 1 <;> omega

end Erdos874
