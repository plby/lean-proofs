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

import ErdosProblems.Erdos1165.ExternalGreenRenewal
import ErdosProblems.Erdos1165.ExternalGreenTail
import ErdosProblems.Erdos1165.ExternalReturnRecurrence
import ErdosProblems.Erdos1165.QuantitativeRenewal
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# Coefficient bounds for the external Green function

This file proves the elementary induction which turns the exact recurrence
for the return coefficients of the retained-block walk into uniform
reciprocal bounds.  It then records the logarithmic truncated-Green and
dyadic-increment consequences needed by the renewal tail estimate.
-/

open Filter MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

namespace Erdos1165.ExternalGreenCoeff

open ExternalWalk ExternalOnePoint ExternalGreenRenewal LazyDecomposition
open Erdos1165.QuantitativeRenewal
open Erdos1165.ExternalReturnRecurrence

/-! ## Initial external return coefficients -/

@[simp] theorem externalReturnProbability_zero (o : Orientation) :
    externalReturnProbability o 0 = 1 := by
  cases o <;>
    norm_num [externalReturnProbability, externalReturningWords,
      externalWordDisplacement]

theorem externalReturnProbability_one (o : Orientation) :
    externalReturnProbability o 1 = 1 / 5 := by
  have hcount : (externalReturningWords o 1).card = 3 := by
    cases o <;> decide
  rw [externalReturnProbability, hcount]
  norm_num

theorem externalReturnProbability_two (o : Orientation) :
    externalReturnProbability o 2 = 29 / 225 := by
  have hcount : (externalReturningWords o 2).card = 29 := by
    cases o <;> decide
  rw [externalReturnProbability, hcount]
  norm_num

/-! ## The recurrence induction -/

/-- The rational supersolution used for the upper coefficient estimate. -/
private lemma recurrence_upper_arithmetic (n : ℕ) (hn : 2 ≤ n) :
    ((195 : ℝ) * n ^ 2 + 195 * n + 45) * (1 / (n + 1 : ℝ)) +
        29 * n ^ 2 * (1 / (n : ℝ)) +
          n * (n - 1) * (1 / (n - 1 : ℝ)) ≤
      225 * (n + 1) ^ 2 * (1 / (n + 2 : ℝ)) := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  have hn10 : (n : ℝ) - 1 ≠ 0 := by linarith
  have hn1p : (n : ℝ) + 1 ≠ 0 := by positivity
  have hn2p : (n : ℝ) + 2 ≠ 0 := by positivity
  field_simp
  nlinarith

/-- The rational subsolution used for the lower coefficient estimate. -/
private lemma recurrence_lower_arithmetic (n : ℕ) (hn : 3 ≤ n) :
    225 * (n + 1) ^ 2 * (1 / (5 * (n + 1) : ℝ)) ≤
      ((195 : ℝ) * n ^ 2 + 195 * n + 45) * (1 / (5 * n : ℝ)) +
        29 * n ^ 2 * (1 / (5 * (n - 1) : ℝ)) +
          n * (n - 1) * (1 / (5 * (n - 2) : ℝ)) := by
  have hnR : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  have hn10 : (n : ℝ) - 1 ≠ 0 := by linarith
  have hn20 : (n : ℝ) - 2 ≠ 0 := by linarith
  have hn1p : (n : ℝ) + 1 ≠ 0 := by positivity
  have hn3 : 0 ≤ (n : ℝ) - 3 := by linarith
  have hpoly : 0 ≤
      (76 : ℝ) * ((n : ℝ) - 3) ^ 2 +
        261 * ((n : ℝ) - 3) + 189 := by positivity
  have hnum : 0 ≤ (76 : ℝ) * n ^ 2 - 195 * n + 90 := by
    nlinarith [hpoly]
  have hnpos : 0 < (n : ℝ) := by linarith
  have hn1pos : 0 < (n : ℝ) - 1 := by linarith
  have hn2pos : 0 < (n : ℝ) - 2 := by linarith
  have hdenpos : 0 < (n : ℝ) * (n - 1) * (n - 2) :=
    mul_pos (mul_pos hnpos hn1pos) hn2pos
  apply sub_nonneg.mp
  have hid :
      (((195 : ℝ) * n ^ 2 + 195 * n + 45) * (1 / (5 * n : ℝ)) +
          29 * n ^ 2 * (1 / (5 * (n - 1) : ℝ)) +
            n * (n - 1) * (1 / (5 * (n - 2) : ℝ))) -
          225 * (n + 1) ^ 2 * (1 / (5 * (n + 1) : ℝ)) =
        ((76 : ℝ) * n ^ 2 - 195 * n + 90) /
          (5 * (n * (n - 1) * (n - 2))) := by
    field_simp
    ring
  rw [hid]
  exact div_nonneg hnum (by positivity)

private lemma recurrence_upper_two_fifths_arithmetic (n : ℕ) (hn : 2 ≤ n) :
    ((195 : ℝ) * n ^ 2 + 195 * n + 45) *
          (2 / (5 * (n + 1)) : ℝ) +
        29 * n ^ 2 * (2 / (5 * n) : ℝ) +
          n * (n - 1) * (2 / (5 * (n - 1)) : ℝ) ≤
      225 * (n + 1) ^ 2 * (2 / (5 * (n + 2)) : ℝ) := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  have hn10 : (n : ℝ) - 1 ≠ 0 := by linarith
  have hn1p : (n : ℝ) + 1 ≠ 0 := by positivity
  have hn2p : (n : ℝ) + 2 ≠ 0 := by positivity
  field_simp
  nlinarith

/-- A positive sequence satisfying the external-walk recurrence and its first
three values is bounded above by `1/(n+1)`.

Keeping this induction abstract isolates all coefficient extraction from the
subsequent real inequalities. -/
theorem upper_reciprocal_of_recurrence
    (q : ℕ → ℝ)
    (hq0 : q 0 = 1) (hq1 : q 1 = 1 / 5) (hq2 : q 2 = 29 / 225)
    (hrec : ∀ n : ℕ, 2 ≤ n →
      225 * (n + 1 : ℝ) ^ 2 * q (n + 1) =
        ((195 : ℝ) * n ^ 2 + 195 * n + 45) * q n +
          29 * n ^ 2 * q (n - 1) + n * (n - 1) * q (n - 2)) :
    ∀ n, q n ≤ 1 / (n + 1 : ℝ) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      rcases n with _ | _ | _ | n
      · norm_num [hq0]
      · norm_num [hq1]
      · norm_num [hq2]
      · let N := n + 2
        have hN : 2 ≤ N := by omega
        have hqN := ih N (by omega)
        have hqNm1 := ih (N - 1) (by omega)
        have hqNm2 := ih (N - 2) (by omega)
        have hqNm1' : q (N - 1) ≤ 1 / (N : ℝ) := by
          convert hqNm1 using 1
          rw [Nat.cast_sub (by omega)]
          norm_num
        have hqNm2' : q (N - 2) ≤ 1 / (N - 1 : ℝ) := by
          convert hqNm2 using 1
          rw [Nat.cast_sub (by omega)]
          norm_num
          ring
        have hA : 0 ≤ (195 : ℝ) * N ^ 2 + 195 * N + 45 := by positivity
        have hB : 0 ≤ (29 : ℝ) * N ^ 2 := by positivity
        have hC : 0 ≤ (N : ℝ) * (N - 1) := by
          have : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
          positivity
        have hden : 0 < (225 : ℝ) * (N + 1) ^ 2 := by positivity
        have hmul : (225 * (N + 1 : ℝ) ^ 2) * q (N + 1) ≤
            (225 * (N + 1 : ℝ) ^ 2) * (1 / (N + 2 : ℝ)) := by
          calc
            (225 * (N + 1 : ℝ) ^ 2) * q (N + 1) =
              ((195 : ℝ) * N ^ 2 + 195 * N + 45) * q N +
                29 * N ^ 2 * q (N - 1) + N * (N - 1) * q (N - 2) := by
              exact hrec N hN
            _ ≤
              ((195 : ℝ) * N ^ 2 + 195 * N + 45) *
                  (1 / (N + 1 : ℝ)) +
                29 * N ^ 2 * (1 / (N : ℝ)) +
                  N * (N - 1) * (1 / (N - 1 : ℝ)) := by
              gcongr
            _ ≤ 225 * (N + 1) ^ 2 * (1 / (N + 2 : ℝ)) :=
              recurrence_upper_arithmetic N hN
        have hstep : q (N + 1) ≤ 1 / (N + 2 : ℝ) :=
          (mul_le_mul_iff_of_pos_left hden).mp hmul
        convert hstep using 1 <;> (norm_num [N]; ring)

/-- The same recurrence has the uniform lower bound `1/(5n)` at every
positive index. -/
theorem lower_reciprocal_of_recurrence
    (q : ℕ → ℝ)
    (hq1 : q 1 = 1 / 5) (hq2 : q 2 = 29 / 225)
    (hq3 : q 3 = 303 / 3375)
    (hrec : ∀ n : ℕ, 2 ≤ n →
      225 * (n + 1 : ℝ) ^ 2 * q (n + 1) =
        ((195 : ℝ) * n ^ 2 + 195 * n + 45) * q n +
          29 * n ^ 2 * q (n - 1) + n * (n - 1) * q (n - 2)) :
    ∀ n : ℕ, 1 ≤ n → 1 / (5 * (n : ℝ)) ≤ q n := by
  intro n hn
  induction n using Nat.strong_induction_on with
  | h n ih =>
      rcases n with _ | _ | _ | _ | n
      · omega
      · norm_num [hq1]
      · norm_num [hq2]
      · norm_num [hq3]
      · let N := n + 3
        have hN : 3 ≤ N := by omega
        have hqN := ih N (by omega) (by omega)
        have hqNm1 := ih (N - 1) (by omega) (by omega)
        have hqNm2 := ih (N - 2) (by omega) (by omega)
        have hqNm1' : 1 / (5 * (N - 1 : ℝ)) ≤ q (N - 1) := by
          convert hqNm1 using 1
          rw [Nat.cast_sub (by omega)]
          norm_num
        have hqNm2' : 1 / (5 * (N - 2 : ℝ)) ≤ q (N - 2) := by
          convert hqNm2 using 1
          rw [Nat.cast_sub (by omega)]
          norm_num
        have hden : 0 < (225 : ℝ) * (N + 1) ^ 2 := by positivity
        have hmul : (225 * (N + 1 : ℝ) ^ 2) *
              (1 / (5 * (N + 1) : ℝ)) ≤
            (225 * (N + 1 : ℝ) ^ 2) * q (N + 1) := by
          calc
            (225 * (N + 1 : ℝ) ^ 2) * (1 / (5 * (N + 1) : ℝ)) ≤
                ((195 : ℝ) * N ^ 2 + 195 * N + 45) *
                    (1 / (5 * N : ℝ)) +
                  29 * N ^ 2 * (1 / (5 * (N - 1) : ℝ)) +
                    N * (N - 1) * (1 / (5 * (N - 2) : ℝ)) :=
              recurrence_lower_arithmetic N hN
            _ ≤ ((195 : ℝ) * N ^ 2 + 195 * N + 45) * q N +
                29 * N ^ 2 * q (N - 1) + N * (N - 1) * q (N - 2) := by
              have hA : 0 ≤ (195 : ℝ) * N ^ 2 + 195 * N + 45 := by positivity
              have hB : 0 ≤ (29 : ℝ) * N ^ 2 := by positivity
              have hC : 0 ≤ (N : ℝ) * (N - 1) := by
                have : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
                positivity
              gcongr
            _ = (225 * (N + 1 : ℝ) ^ 2) * q (N + 1) :=
              (hrec N (by omega)).symm
        have hstep : 1 / (5 * (N + 1) : ℝ) ≤ q (N + 1) :=
          (mul_le_mul_iff_of_pos_left hden).mp hmul
        convert hstep using 1 <;> (norm_num [N]; ring)

/-- Starting at time one, the external recurrence has the sharper
supersolution `2/(5(n+1))`.  Treating time three as a base case avoids the
exceptional mass `q 0 = 1`, which is not on this scale. -/
theorem upper_two_fifths_reciprocal_of_recurrence
    (q : ℕ → ℝ)
    (hq1 : q 1 = 1 / 5) (hq2 : q 2 = 29 / 225)
    (hq3 : q 3 = 303 / 3375)
    (hrec : ∀ n : ℕ, 2 ≤ n →
      225 * (n + 1 : ℝ) ^ 2 * q (n + 1) =
        ((195 : ℝ) * n ^ 2 + 195 * n + 45) * q n +
          29 * n ^ 2 * q (n - 1) + n * (n - 1) * q (n - 2)) :
    ∀ n : ℕ, 1 ≤ n → q n ≤ 2 / (5 * (n + 1) : ℝ) := by
  intro n hn
  induction n using Nat.strong_induction_on with
  | h n ih =>
      rcases n with _ | _ | _ | _ | n
      · omega
      · norm_num [hq1]
      · norm_num [hq2]
      · norm_num [hq3]
      · let N := n + 3
        have hN : 3 ≤ N := by omega
        have hqN := ih N (by omega) (by omega)
        have hqNm1 := ih (N - 1) (by omega) (by omega)
        have hqNm2 := ih (N - 2) (by omega) (by omega)
        have hqNm1' : q (N - 1) ≤ 2 / (5 * N : ℝ) := by
          convert hqNm1 using 1
          rw [Nat.cast_sub (by omega)]
          norm_num
        have hqNm2' : q (N - 2) ≤ 2 / (5 * (N - 1) : ℝ) := by
          convert hqNm2 using 1
          rw [Nat.cast_sub (by omega)]
          norm_num
          ring
        have hA : 0 ≤ (195 : ℝ) * N ^ 2 + 195 * N + 45 := by positivity
        have hB : 0 ≤ (29 : ℝ) * N ^ 2 := by positivity
        have hC : 0 ≤ (N : ℝ) * (N - 1) := by
          have : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
          positivity
        have hden : 0 < (225 : ℝ) * (N + 1) ^ 2 := by positivity
        have hmul : (225 * (N + 1 : ℝ) ^ 2) * q (N + 1) ≤
            (225 * (N + 1 : ℝ) ^ 2) *
              (2 / (5 * (N + 2)) : ℝ) := by
          calc
            (225 * (N + 1 : ℝ) ^ 2) * q (N + 1) =
                ((195 : ℝ) * N ^ 2 + 195 * N + 45) * q N +
                  29 * N ^ 2 * q (N - 1) + N * (N - 1) * q (N - 2) :=
              hrec N (by omega)
            _ ≤ ((195 : ℝ) * N ^ 2 + 195 * N + 45) *
                    (2 / (5 * (N + 1)) : ℝ) +
                  29 * N ^ 2 * (2 / (5 * N) : ℝ) +
                    N * (N - 1) * (2 / (5 * (N - 1)) : ℝ) := by
              gcongr
            _ ≤ (225 * (N + 1 : ℝ) ^ 2) *
                (2 / (5 * (N + 2)) : ℝ) :=
              recurrence_upper_two_fifths_arithmetic N (by omega)
        have hstep : q (N + 1) ≤ 2 / (5 * (N + 2) : ℝ) :=
          (mul_le_mul_iff_of_pos_left hden).mp hmul
        convert hstep using 1 <;> (norm_num [N]; ring)

/-! ## Concrete coefficient bounds for the retained-block walk -/

/-- The third return probability, obtained from the exact recurrence at
`n = 2`. -/
theorem externalReturnProbability_three (o : Orientation) :
    externalReturnProbability o 3 = 303 / 3375 := by
  have h := externalReturnProbability_recurrence o 2 (by norm_num)
  rw [externalReturnProbability_zero, externalReturnProbability_one,
    externalReturnProbability_two] at h
  norm_num at h ⊢
  linarith

/-- A uniform reciprocal upper bound, including time zero. -/
theorem externalReturnProbability_le_one_over_succ (o : Orientation) (n : ℕ) :
    externalReturnProbability o n ≤ 1 / (n + 1 : ℝ) := by
  exact upper_reciprocal_of_recurrence
    (externalReturnProbability o)
    (externalReturnProbability_zero o)
    (externalReturnProbability_one o)
    (externalReturnProbability_two o)
    (externalReturnProbability_recurrence o) n

/-- The sharper reciprocal upper bound valid at every positive time. -/
theorem externalReturnProbability_le_two_fifths (o : Orientation) (n : ℕ)
    (hn : 1 ≤ n) :
    externalReturnProbability o n ≤ 2 / (5 * (n + 1) : ℝ) := by
  exact upper_two_fifths_reciprocal_of_recurrence
    (externalReturnProbability o)
    (externalReturnProbability_one o)
    (externalReturnProbability_two o)
    (externalReturnProbability_three o)
    (externalReturnProbability_recurrence o) n hn

/-- A coarse `B/n` version of the sharp coefficient upper bound, convenient
for distant-horizon Green increments. -/
theorem externalReturnProbability_le_two_fifths_div (o : Orientation) (n : ℕ)
    (hn : 0 < n) :
    externalReturnProbability o n ≤ (2 / 5 : ℝ) / n := by
  refine (externalReturnProbability_le_two_fifths o n hn).trans ?_
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1R : (0 : ℝ) < n + 1 := by positivity
  apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < 5 * (n + 1)) hnR).2
  nlinarith

/-- The same upper coefficient estimate in the genuine renewal API. -/
theorem externalRenewalReturnProbability_le_two_fifths
    (o : Orientation) (n : ℕ) (hn : 1 ≤ n) :
    ExternalRenewal.externalReturnProbability o n ≤
      2 / (5 * (n + 1) : ℝ) := by
  rw [← ExternalGreenRenewal.externalReturnProbability_eq_renewal]
  exact externalReturnProbability_le_two_fifths o n hn

/-- A reciprocal lower bound valid at every positive time. -/
theorem one_div_five_mul_le_externalReturnProbability (o : Orientation) (n : ℕ)
    (hn : 1 ≤ n) :
    1 / (5 * (n : ℝ)) ≤ externalReturnProbability o n := by
  exact lower_reciprocal_of_recurrence
    (externalReturnProbability o)
    (externalReturnProbability_one o)
    (externalReturnProbability_two o)
    (externalReturnProbability_three o)
    (externalReturnProbability_recurrence o) n hn

/-- The requested lower reciprocal bound with the same `(n+1)` denominator
as the upper estimate. -/
theorem one_div_five_mul_succ_le_externalReturnProbability
    (o : Orientation) (n : ℕ) :
    1 / (5 * (n + 1) : ℝ) ≤ externalReturnProbability o n := by
  rcases n with _ | n
  · norm_num [externalReturnProbability_zero]
  · apply le_trans ?_
      (one_div_five_mul_le_externalReturnProbability o (n + 1) (by omega))
    apply one_div_le_one_div_of_le (by positivity)
    norm_num only [Nat.cast_add, Nat.cast_one]
    linarith

/-! ## Remainder bounds used by distant-horizon renewal -/

/-- A sharp-leading Green upper bound immediately bounds the accumulated
reciprocal coefficient remainder.  This direction uses the integral lower
bound `log (N+1) ≤ H_N`, so it loses no leading constant. -/
theorem reciprocalRemainderSum_le_of_truncatedGreen_le
    (q : ℕ → ℝ) (a E : ℝ) (N : ℕ)
    (hq0 : q 0 = 1) (ha : 0 ≤ a)
    (hG : RenewalTail.truncatedGreen q N ≤
      1 + a * Real.log (N + 1) + E) :
    reciprocalRemainderSum q a N ≤ E := by
  have hh : Real.log (N + 1 : ℝ) ≤ (harmonic N : ℝ) :=
    by simpa only [Nat.cast_add, Nat.cast_one] using log_add_one_le_harmonic N
  have hah : a * Real.log (N + 1 : ℝ) ≤ a * (harmonic N : ℝ) :=
    mul_le_mul_of_nonneg_left hh ha
  rw [truncatedGreen_eq_harmonic_add_remainder q a N hq0] at hG
  linarith

/-- A reciprocal pointwise upper bound controls a distant Green increment.
This is the coarse input needed only for the numerator of the quantitative
renewal estimate. -/
theorem truncatedGreen_increment_le_of_reciprocal_upper
    (q : ℕ → ℝ) (C : ℝ) (m n : ℕ)
    (hC : 0 ≤ C)
    (hq : ∀ k : ℕ, 1 ≤ k → q k ≤ C / k) :
    RenewalTail.truncatedGreen q (n + m) -
        RenewalTail.truncatedGreen q m ≤
      C * (n : ℝ) / (m + 1 : ℝ) := by
  rw [truncatedGreen_add_sub]
  calc
    (∑ j ∈ Finset.range n, q (m + 1 + j)) ≤
        ∑ j ∈ Finset.range n, C / (m + 1 + j : ℕ) := by
      apply Finset.sum_le_sum
      intro j hj
      exact hq (m + 1 + j) (by omega)
    _ = C * (∑ j ∈ Finset.range n, (1 : ℝ) / (m + 1 + j)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      push_cast
      ring
    _ ≤ C * ((n : ℝ) / (m + 1 : ℝ)) := by
      exact mul_le_mul_of_nonneg_left (sum_range_reciprocal_add_le m n) hC
    _ = C * (n : ℝ) / (m + 1 : ℝ) := by ring

/-- Consequently, subtracting any nonnegative reciprocal main term can only
decrease the distant remainder increment. -/
theorem reciprocalRemainderSum_increment_le_of_reciprocal_upper
    (q : ℕ → ℝ) (a C : ℝ) (m n : ℕ)
    (hq0 : q 0 = 1) (ha : 0 ≤ a) (hC : 0 ≤ C)
    (hq : ∀ k : ℕ, 1 ≤ k → q k ≤ C / k) :
    reciprocalRemainderSum q a (n + m) -
        reciprocalRemainderSum q a m ≤
      C * (n : ℝ) / (m + 1 : ℝ) := by
  have hG := truncatedGreen_increment_le_of_reciprocal_upper q C m n hC hq
  rw [truncatedGreen_eq_harmonic_add_remainder q a (n + m) hq0,
    truncatedGreen_eq_harmonic_add_remainder q a m hq0] at hG
  have hh : (0 : ℝ) ≤ (harmonic (n + m) : ℝ) - harmonic m := by
    apply sub_nonneg.mpr
    rw [harmonic, harmonic]
    push_cast
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · exact Finset.range_mono (Nat.le_add_left m n)
    · intro i hi hnot
      positivity
  nlinarith [mul_nonneg ha hh]

/-- A reciprocal lower coefficient bound gives a fixed positive amount of
Green mass on every dyadic interval. -/
theorem truncatedGreen_dyadic_increment_ge_of_reciprocal_lower
    (q : ℕ → ℝ) (c : ℝ) (n : ℕ) (hn : 1 ≤ n)
    (hc : 0 ≤ c)
    (hq : ∀ k : ℕ, 1 ≤ k → c / k ≤ q k) :
    c / 2 ≤ RenewalTail.truncatedGreen q (2 * n) -
      RenewalTail.truncatedGreen q n := by
  rw [show 2 * n = n + n by omega, truncatedGreen_add_sub]
  calc
    c / 2 = ∑ _j ∈ Finset.range n, c / (2 * n : ℝ) := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
      field_simp
    _ ≤ ∑ j ∈ Finset.range n, q (n + 1 + j) := by
      apply Finset.sum_le_sum
      intro j hj
      rw [Finset.mem_range] at hj
      apply (show c / (2 * n : ℝ) ≤ c / (n + 1 + j : ℕ) from ?_).trans
        (hq (n + 1 + j) (by omega))
      have hkpos : (0 : ℝ) < ((n + 1 + j : ℕ) : ℝ) := by positivity
      have hk : (n + 1 + j : ℕ) ≤ 2 * n := by omega
      have hkR : ((n + 1 + j : ℕ) : ℝ) ≤ ((2 * n : ℕ) : ℝ) := by
        exact_mod_cast hk
      have hrecip : (1 : ℝ) / (2 * n : ℕ) ≤ 1 / (n + 1 + j : ℕ) :=
        one_div_le_one_div_of_le hkpos hkR
      norm_num only [Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat] at hrecip ⊢
      simpa only [div_eq_mul_inv, one_mul] using
        mul_le_mul_of_nonneg_left hrecip hc

/-! ## Concrete truncated-Green estimates -/

/-- The complete truncated Green sum is dominated termwise by the harmonic
sum with the same number of terms. -/
theorem externalTruncatedGreenCount_le_harmonic (o : Orientation) (N : ℕ) :
    externalTruncatedGreenCount o N ≤ (harmonic (N + 1) : ℝ) := by
  rw [externalTruncatedGreenCount, harmonic]
  simp only [Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
  apply Finset.sum_le_sum
  intro n hn
  simpa only [inv_eq_one_div, Nat.cast_add, Nat.cast_one] using
    externalReturnProbability_le_one_over_succ o n

/-- A completely explicit logarithmic upper bound.  The constant `3` is
chosen only to make the estimate uniform down to `N = 0`. -/
theorem externalTruncatedGreenCount_le_three_mul_log (o : Orientation) (N : ℕ) :
    externalTruncatedGreenCount o N ≤
      3 * Real.log ((N : ℝ) + 2) := by
  calc
    externalTruncatedGreenCount o N ≤ (harmonic (N + 1) : ℝ) :=
      externalTruncatedGreenCount_le_harmonic o N
    _ ≤ 1 + Real.log ((N : ℝ) + 1) := by
      simpa only [Nat.cast_add, Nat.cast_one] using harmonic_le_one_add_log (N + 1)
    _ ≤ 3 * Real.log ((N : ℝ) + 2) := by
      have hlogmono : Real.log ((N : ℝ) + 1) ≤
          Real.log ((N : ℝ) + 2) := by
        apply Real.log_le_log (by positivity)
        linarith
      have hlogtwo : Real.log 2 ≤ Real.log ((N : ℝ) + 2) := by
        apply Real.log_le_log (by norm_num)
        have hN : (0 : ℝ) ≤ N := by positivity
        linarith
      nlinarith [Real.log_two_gt_d9]

/-- Every dyadic annulus contains a fixed positive amount of return mass. -/
theorem one_tenth_le_externalTruncatedGreenCount_dyadic_increment
    (o : Orientation) (n : ℕ) (hn : 1 ≤ n) :
    1 / 10 ≤ externalTruncatedGreenCount o (2 * n) -
      externalTruncatedGreenCount o n := by
  change 1 / 10 ≤
    RenewalTail.truncatedGreen (externalReturnProbability o) (2 * n) -
      RenewalTail.truncatedGreen (externalReturnProbability o) n
  have h := truncatedGreen_dyadic_increment_ge_of_reciprocal_lower
    (externalReturnProbability o) (1 / 5) n hn (by norm_num)
    (fun k hk ↦ by
      have hl := one_div_five_mul_le_externalReturnProbability o k hk
      convert hl using 1 <;> field_simp)
  norm_num at h ⊢
  exact h

/-- Conversely, the return mass in a dyadic annulus is at most `2/5`. -/
theorem externalTruncatedGreenCount_dyadic_increment_le_two_fifths
    (o : Orientation) (n : ℕ) :
    externalTruncatedGreenCount o (2 * n) -
        externalTruncatedGreenCount o n ≤ 2 / 5 := by
  change RenewalTail.truncatedGreen (externalReturnProbability o) (2 * n) -
      RenewalTail.truncatedGreen (externalReturnProbability o) n ≤ 2 / 5
  rw [show 2 * n = n + n by omega]
  calc
    RenewalTail.truncatedGreen (externalReturnProbability o) (n + n) -
        RenewalTail.truncatedGreen (externalReturnProbability o) n ≤
      (2 / 5 : ℝ) * (n : ℝ) / (n + 1 : ℝ) := by
        exact truncatedGreen_increment_le_of_reciprocal_upper
          (externalReturnProbability o) (2 / 5) n n (by norm_num)
          (fun k hk ↦ externalReturnProbability_le_two_fifths_div o k (by omega))
    _ ≤ 2 / 5 := by
      have hn0 : (0 : ℝ) ≤ n := by positivity
      have hfrac : (n : ℝ) / (n + 1 : ℝ) ≤ 1 := by
        rw [div_le_one (by positivity)]
        linarith
      calc
        (2 / 5 : ℝ) * (n : ℝ) / (n + 1 : ℝ) =
            (2 / 5 : ℝ) * ((n : ℝ) / (n + 1 : ℝ)) := by ring
        _ ≤ (2 / 5 : ℝ) * 1 :=
          mul_le_mul_of_nonneg_left hfrac (by norm_num)
        _ = 2 / 5 := by ring

/-- ENNReal version of the logarithmic Green upper bound. -/
theorem externalTruncatedGreen_le_three_mul_log (o : Orientation) (n : ℕ) :
    ExternalRenewal.externalTruncatedGreen o n ≤
      ENNReal.ofReal (3 * Real.log ((n : ℝ) + 2)) := by
  have hlog : 0 ≤ Real.log ((n : ℝ) + 2) := by
    apply Real.log_nonneg
    have hn : (0 : ℝ) ≤ n := by positivity
    linarith
  apply (ENNReal.toReal_le_toReal
    (ExternalRenewal.externalTruncatedGreen_ne_top o n) ENNReal.ofReal_ne_top).mp
  rw [ExternalRenewal.externalTruncatedGreen_toReal,
    ENNReal.toReal_ofReal (mul_nonneg (by norm_num) hlog)]
  rw [← externalTruncatedGreenCount_eq_renewal]
  exact externalTruncatedGreenCount_le_three_mul_log o n

/-- The dyadic upper increment supplies the concrete decrement needed by
the renewal/geometric-tail lemma. -/
theorem externalTruncatedGreen_sub_one_le_sub_three_fifths
    (o : Orientation) (n : ℕ) :
    ExternalRenewal.externalTruncatedGreen o (2 * n) - 1 ≤
      ExternalRenewal.externalTruncatedGreen o n - ENNReal.ofReal (3 / 5) := by
  have hc : ENNReal.ofReal (3 / 5) ≤
      ExternalRenewal.externalTruncatedGreen o n := by
    exact (show ENNReal.ofReal (3 / 5) ≤ 1 by norm_num).trans
      (ExternalRenewal.one_le_externalTruncatedGreen o n)
  apply (ENNReal.toReal_le_toReal
    (ENNReal.sub_ne_top (ExternalRenewal.externalTruncatedGreen_ne_top o (2 * n)))
    (ENNReal.sub_ne_top (ExternalRenewal.externalTruncatedGreen_ne_top o n))).mp
  rw [ENNReal.toReal_sub_of_le
      (ExternalRenewal.one_le_externalTruncatedGreen o (2 * n))
      (ExternalRenewal.externalTruncatedGreen_ne_top o (2 * n)),
    ENNReal.toReal_sub_of_le hc
      (ExternalRenewal.externalTruncatedGreen_ne_top o n),
    ExternalRenewal.externalTruncatedGreen_toReal,
    ExternalRenewal.externalTruncatedGreen_toReal,
    ENNReal.toReal_one, ENNReal.toReal_ofReal (by norm_num)]
  rw [← externalTruncatedGreenCount_eq_renewal,
    ← externalTruncatedGreenCount_eq_renewal]
  nlinarith [externalTruncatedGreenCount_dyadic_increment_le_two_fifths o n]

/-- Fully concrete logarithmic-scale local-time tail obtained by
instantiating `ExternalGreenTail`. -/
theorem externalOriginLocalTime_tail_le_concrete
    (o : Orientation) (r n : ℕ) :
    externalBlocks o {η | r + 1 ≤ externalOriginLocalTime o η n} ≤
      (1 - ENNReal.ofReal (3 / 5) /
        ENNReal.ofReal (3 * Real.log ((n : ℝ) + 2))) ^ r := by
  exact ExternalRenewal.externalOriginLocalTime_tail_le_logarithmic
    o r n (ENNReal.ofReal (3 / 5)) 3
    (externalTruncatedGreen_sub_one_le_sub_three_fifths o n)
    (externalTruncatedGreen_le_three_mul_log o n)

end Erdos1165.ExternalGreenCoeff
