/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.

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

import ErdosProblems.Erdos223.Basic
import ErdosProblems.Erdos223.CarrierEven
import ErdosProblems.Erdos223.ExactLower
import ErdosProblems.Erdos223.LenzOptimization
import ErdosProblems.Erdos223.SevenCounterexample

/-!
# Candidate exact values, verified branches, and the dimension-seven exception

This file packages the candidate formulas in Swanepoel's published exact
theorem.  The balanced complete multipartite contribution is
`turanNumber p n`; the remaining summands count diameter pairs within the
circle and sphere carriers of an optimized Lenz configuration.  It proves
the construction lower bounds in every advertised branch, the matching
upper bounds in dimension four and every even dimension at least six, and an
explicit infinite family refuting the seven-dimensional branch.  No claim is
made here that the remaining dimension-five or odd-dimensional upper bounds
follow from the flawed universal carrier-classification argument.
-/

namespace Erdos223

/-- Swanepoel's candidate eventual value for the number of diameter pairs in
dimension `d`.  Making the definition total is convenient for stating both
the verified exact branches and the seven-dimensional disproof.

The four branches are, in order, dimensions four, five, even dimensions at
least six, and odd dimensions at least seven. -/
def exactValue (d n : ℕ) : ℕ :=
  if d = 4 then
    turanNumber 2 n + ceilQuot n 2 + fourCorrection n
  else if d = 5 then
    turanNumber 2 n + n
  else if d % 2 = 0 then
    turanNumber (d / 2) n + d / 2
  else
    turanNumber (d / 2) n + ceilQuot n (d / 2) + (d / 2 - 1)

@[simp] theorem exactValue_four (n : ℕ) :
    exactValue 4 n =
      turanNumber 2 n + ceilQuot n 2 + if n % 4 = 3 then 0 else 1 := by
  simp [exactValue, fourCorrection]

theorem exactValue_four_of_mod_ne_three {n : ℕ} (hn : n % 4 ≠ 3) :
    exactValue 4 n = turanNumber 2 n + ceilQuot n 2 + 1 := by
  simp [exactValue, fourCorrection, hn]

theorem exactValue_four_of_mod_eq_three {n : ℕ} (hn : n % 4 = 3) :
    exactValue 4 n = turanNumber 2 n + ceilQuot n 2 := by
  simp [exactValue, fourCorrection, hn]

@[simp] theorem exactValue_five (n : ℕ) :
    exactValue 5 n = turanNumber 2 n + n := by
  simp [exactValue]

theorem exactValue_even {d : ℕ} (hd4 : d ≠ 4) (hd5 : d ≠ 5)
    (heven : d % 2 = 0) (n : ℕ) :
    exactValue d n = turanNumber (d / 2) n + d / 2 := by
  simp [exactValue, hd4, hd5, heven]

theorem exactValue_even_of_six_le {d : ℕ} (hd : 6 ≤ d) (heven : Even d)
    (n : ℕ) : exactValue d n = turanNumber (d / 2) n + d / 2 := by
  apply exactValue_even (by omega) (by omega)
  exact Nat.even_iff.mp heven

theorem exactValue_odd {d : ℕ} (hd4 : d ≠ 4) (hd5 : d ≠ 5)
    (hodd : d % 2 ≠ 0) (n : ℕ) :
    exactValue d n =
      turanNumber (d / 2) n + ceilQuot n (d / 2) + (d / 2 - 1) := by
  simp [exactValue, hd4, hd5, hodd]

theorem exactValue_odd_of_seven_le {d : ℕ} (hd : 7 ≤ d) (hodd : Odd d)
    (n : ℕ) : exactValue d n =
      turanNumber (d / 2) n + ceilQuot n (d / 2) + (d / 2 - 1) := by
  apply exactValue_odd (by omega) (by omega)
  intro heven
  exact (Nat.not_even_iff_odd.mpr hodd) (Nat.even_iff.mpr heven)

/-- On multiples of three, the proposed seven-dimensional odd formula has
this elementary polynomial form. -/
theorem exactValue_seven_three_mul (m : ℕ) :
    exactValue 7 (3 * m) = 3 * m ^ 2 + m + 2 := by
  rw [exactValue_odd (by omega) (by omega) (by norm_num)]
  simp [turanNumber_eq_div_mod, ceilQuot]
  omega

/-- The arithmetic interface used by the shifted-three-circle construction.
Any configuration attaining its certified count already beats the proposed
seven-dimensional value once each circle contains at least three points. -/
theorem exactValue_seven_three_mul_lt_f_of_construction_lower
    (m : ℕ) (hm : 3 ≤ m)
    (hlower : 3 * m ^ 2 + 2 * m + 1 ≤ f 7 (3 * m)) :
    exactValue 7 (3 * m) < f 7 (3 * m) := by
  rw [exactValue_seven_three_mul]
  exact lt_of_lt_of_le (by omega) hlower

/-- The shifted-three-circle configuration strictly improves on the
proposed seven-dimensional value for every odd number of at least three
points on each circle. -/
theorem exactValue_seven_three_mul_lt_f
    {m : ℕ} (hm : 3 ≤ m) (hodd : m % 2 = 1) :
    exactValue 7 (3 * m) < f 7 (3 * m) :=
  exactValue_seven_three_mul_lt_f_of_construction_lower m hm
    (seven_shifted_three_circle_lower hm hodd)

/-- The seven-dimensional branch of Swanepoel's proposed exact formula
fails arbitrarily far out.  Taking `m = 2N + 3` supplies an odd circle size
large enough for a counterexample beyond any prescribed threshold `N`. -/
theorem infinitely_often_exactValue_seven_lt_f :
    ∀ N, ∃ n, N ≤ n ∧ exactValue 7 n < f 7 n := by
  intro N
  let m := 2 * N + 3
  have hm : 3 ≤ m := by omega
  have hodd : m % 2 = 1 := by omega
  exact ⟨3 * m, by omega, exactValue_seven_three_mul_lt_f hm hodd⟩

/-- Combine eventual upper and lower estimates with possibly different
thresholds.  This is the final order-theoretic step in each dimensional
branch of Swanepoel's theorem. -/
private theorem eventually_eq_of_eventually_le_of_eventually_ge
    {g h : ℕ → ℕ}
    (hu : ∃ N, ∀ n, N ≤ n → g n ≤ h n)
    (hl : ∃ N, ∀ n, N ≤ n → h n ≤ g n) :
    ∃ N, ∀ n, N ≤ n → g n = h n := by
  obtain ⟨Nu, hu⟩ := hu
  obtain ⟨Nl, hl⟩ := hl
  refine ⟨max Nu Nl, fun n hn ↦ le_antisymm (hu n ?_) (hl n ?_)⟩
  · exact le_trans (Nat.le_max_left _ _) hn
  · exact le_trans (Nat.le_max_right _ _) hn

/-- The explicit Lenz configurations give Swanepoel's candidate value as an
eventual lower bound in every dimension at least six.  This theorem is kept
separate from any classification-based upper bound: its threshold is fully
explicit and no stability input is needed. -/
theorem eventually_exactValue_le_f_of_six_le (d : ℕ) (hd : 6 ≤ d) :
    ∃ N, ∀ n, N ≤ n → exactValue d n ≤ f d n := by
  by_cases heven : Even d
  · refine ⟨2 * (d / 2), fun n hn ↦ ?_⟩
    rw [exactValue_even_of_six_le hd heven]
    exact ExactLower.even_exact_lower hd heven hn
  · have hodd : Odd d := Nat.not_even_iff_odd.mp heven
    have hd7 : 7 ≤ d := by
      by_contra h
      have hdeq : d = 6 := by omega
      subst d
      exact heven (by decide)
    refine ⟨3 * (d / 2), fun n hn ↦ ?_⟩
    rw [exactValue_odd_of_seven_le hd7 hodd]
    exact ExactLower.odd_exact_lower hd7 hodd hn

/-- The sharp four-dimensional construction.  The active circle is chosen
as the odd side of a balanced bipartition of `n + 1`, except in the
exceptional residue class `n ≡ 3 (mod 4)`, where it is the even side.
This is exactly the source of `fourCorrection`. -/
theorem eventually_exactValue_le_f_four :
    ∃ N, ∀ n, N ≤ n → exactValue 4 n ≤ f 4 n := by
  refine ⟨8, fun n hn ↦ ?_⟩
  simpa [exactValue, fourCorrection] using ExactLower.four_exact_lower hn

/-- The sharp five-dimensional construction.  The residue-zero case uses
the odd cospherical `2m - 2` construction in three dimensions; the other
three residues use the explicit active-circle/large-sphere join. -/
theorem eventually_exactValue_le_f_five :
    ∃ N, ∀ n, N ≤ n → exactValue 5 n ≤ f 5 n := by
  refine ⟨16, fun n hn ↦ ?_⟩
  simpa [exactValue] using ExactLower.five_exact_lower hn

/-- All four explicit construction families, packaged as an eventual lower
bound by the candidate value.  In dimension seven this remains valid,
although the shifted-circle family below shows it is not sharp. -/
theorem eventually_exactValue_le_f (d : ℕ) (hd : 4 ≤ d) :
    ∃ N, ∀ n, N ≤ n → exactValue d n ≤ f d n := by
  by_cases hd4 : d = 4
  · subst d
    exact eventually_exactValue_le_f_four
  by_cases hd5 : d = 5
  · subst d
    exact eventually_exactValue_le_f_five
  exact eventually_exactValue_le_f_of_six_le d (by omega)

/-- The unconditional four-dimensional carrier classification, rewritten
in terms of `exactValue`. -/
theorem eventually_f_le_exactValue_four :
    ∃ N, ∀ n, N ≤ n → f 4 n ≤ exactValue 4 n := by
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1
    EvenExceptionalRemoval.eventually_f_four_le_exactValue
  refine ⟨N, fun n hn ↦ ?_⟩
  simpa [exactValue, fourCorrection] using hN n hn

/-- The exact eventual value in dimension four, including the exceptional
residue class modulo four. -/
theorem eventually_f_eq_exactValue_four :
    ∃ N, ∀ n, N ≤ n → f 4 n = exactValue 4 n :=
  eventually_eq_of_eventually_le_of_eventually_ge
    eventually_f_le_exactValue_four eventually_exactValue_le_f_four

/-- The unconditional carrier-classification upper bound in even dimensions
at least six, rewritten in terms of `exactValue`. -/
theorem eventually_f_le_exactValue_of_even {d : ℕ} (hd : 6 ≤ d)
    (heven : Even d) :
    ∃ N, ∀ n, N ≤ n → f d n ≤ exactValue d n := by
  have hp : 3 ≤ d / 2 := by omega
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1
    (EvenExceptionalRemoval.eventually_f_even_le_turanNumber_add (d / 2) hp)
  refine ⟨N, fun n hn ↦ ?_⟩
  have h := hN n hn
  rw [Nat.two_mul_div_two_of_even heven] at h
  rwa [exactValue_even_of_six_le hd heven]

/-- Swanepoel's exact eventual formula in every even dimension at least
six. -/
theorem eventually_f_eq_exactValue_of_even {d : ℕ} (hd : 6 ≤ d)
    (heven : Even d) :
    ∃ N, ∀ n, N ≤ n → f d n = exactValue d n :=
  eventually_eq_of_eventually_le_of_eventually_ge
    (eventually_f_le_exactValue_of_even hd heven)
    (eventually_exactValue_le_f_of_six_le d hd)

end Erdos223
