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

import ErdosProblems.Erdos444.Basic

/-!
# Erdős Problem 444: the bounded reciprocal-mass case

If the partial reciprocal sums of an infinite set `A` are uniformly bounded,
then the required ratios are unbounded on every tail.  The proof is elementary:
an arbitrarily large finite subset of `A \ {0}` consists of divisors of its
product, while the denominator remains uniformly bounded.
-/

open scoped BigOperators

namespace Erdos444

/-- If the reciprocal masses at natural cutoffs are uniformly bounded, then
the ratios in Problem 444 are unbounded on every natural tail. -/
theorem tailUnbounded_ratioNat_of_reciprocalMass_bounded
    (A : Set ℕ) (hA : A.Infinite) (k : ℕ) (B : ℝ)
    (hB : ∀ x, reciprocalMassNat A x ≤ B) :
    tailUnbounded (ratioNat A k) := by
  intro C X
  by_cases hC : C < 0
  · exact ⟨X, le_rfl, hC.trans_le (ratioNat_nonneg A k X)⟩
  have hC0 : 0 ≤ C := le_of_not_gt hC
  have hB0 : 0 ≤ B := (reciprocalMassNat_nonneg A 0).trans (hB 0)
  obtain ⟨m, hm⟩ : ∃ m : ℕ, C * B ^ k < m := exists_nat_gt (C * B ^ k)
  have hmpos : 0 < m := by
    by_contra hm0
    have hmzero : m = 0 := Nat.eq_zero_of_not_pos hm0
    rw [hmzero, Nat.cast_zero] at hm
    exact (not_lt_of_ge (mul_nonneg hC0 (pow_nonneg hB0 k))) hm
  have hApos : (A \ {0}).Infinite := hA.sdiff (Set.finite_singleton 0)
  obtain ⟨S, hSsub, hScard⟩ := hApos.exists_subset_card_eq m
  have hS : ∀ a ∈ S, a ∈ A ∧ a ≠ 0 := by
    intro a ha
    have ha' := hSsub ha
    exact ⟨ha'.1, by simpa using ha'.2⟩
  let p : ℕ := ∏ a ∈ S, a
  let x : ℕ := max X (p + 1)
  refine ⟨x, le_max_left X (p + 1), ?_⟩
  have hpne : p ≠ 0 := by
    dsimp [p]
    exact Finset.prod_ne_zero_iff.mpr fun a ha ↦ (hS a ha).2
  have hp : 0 < p := Nat.pos_of_ne_zero hpne
  have hpx : p < x := by
    exact (Nat.lt_succ_self p).trans_le (le_max_right X (p + 1))
  have hnumNat : m ≤ maxDivisorCountNat A x := by
    rw [← hScard]
    exact (card_le_divisorCount_prod A S hS).trans
      (divisorCount_le_maxDivisorCountNat hp hpx)
  have hmasspos : 0 < reciprocalMassNat A x := by
    obtain ⟨a, ha⟩ := S.nonempty_iff_ne_empty.mpr (by
      intro hSempty
      have : S.card = 0 := by simp [hSempty]
      omega)
    have hadiv : a ∣ p := by
      dsimp [p]
      exact Finset.dvd_prod_of_mem id ha
    have hapos : 0 < a := Nat.pos_of_ne_zero (hS a ha).2
    have hap : a ≤ p := Nat.le_of_dvd hp hadiv
    exact reciprocalMassNat_pos_of_mem (hS a ha).1 hapos (hap.trans_lt hpx)
  have hdenpos : 0 < reciprocalMassNat A x ^ k := pow_pos hmasspos k
  have hdenle : reciprocalMassNat A x ^ k ≤ B ^ k :=
    pow_le_pow_left₀ (reciprocalMassNat_nonneg A x) (hB x) k
  have hCdenle : C * reciprocalMassNat A x ^ k ≤ C * B ^ k :=
    mul_le_mul_of_nonneg_left hdenle hC0
  have hmreal : (m : ℝ) ≤ (maxDivisorCountNat A x : ℝ) := by
    exact_mod_cast hnumNat
  rw [ratioNat]
  exact (lt_div_iff₀ hdenpos).mpr (hCdenle.trans_lt (hm.trans_le hmreal))

/-- The real-cutoff form of the bounded reciprocal-mass case. -/
theorem tailUnbounded_ratio_of_reciprocalMass_bounded
    (A : Set ℕ) (hA : A.Infinite) (k : ℕ) (B : ℝ)
    (hB : ∀ x, reciprocalMass A x ≤ B) :
    tailUnbounded (ratio A k) := by
  have hBN : ∀ x, reciprocalMassNat A x ≤ B := by
    intro x
    simpa using hB (x : ℝ)
  have hnat := tailUnbounded_ratioNat_of_reciprocalMass_bounded A hA k B hBN
  intro C X
  obtain ⟨N, hXN⟩ := exists_nat_ge X
  obtain ⟨n, hNn, hn⟩ := hnat C N
  refine ⟨(n : ℝ), hXN.trans ?_, ?_⟩
  · exact_mod_cast hNn
  · simpa using hn

end Erdos444
