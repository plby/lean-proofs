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
import ErdosProblems.Erdos19.Pippenger.PippengerSpencerInnerMarginal
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Data.Nat.Choose.Sum

/-!
# Analytic trajectory for the sharp fixed-length inner marginal

This file isolates the dependency-free real analysis used by the inner
nibble.  The discrete trajectory is the explicit Euler recurrence for
`y' = -y^k`; its live-edge probabilities are `y^k`, and those probabilities
telescope to the full unit mass as the uncovered density tends to zero.
-/

open Finset Real
open scoped BigOperators Topology

namespace Erdos76

noncomputable section

namespace FiniteHypergraph

/-! ### Weighted binomial sums

The all-order zero-count argument produces error terms weighted by
`choose a j * c^j`.  The following elementary identities keep the resulting
loss in product form.  In particular, the first two moments cost polynomial
factors in `a` rather than an additional exponential estimate. -/

/-- The real binomial generating function with the unit factor suppressed. -/
lemma sum_natCast_choose_mul_pow (a : ℕ) (c : ℝ) :
    (∑ j ∈ range (a + 1), (a.choose j : ℝ) * c ^ j) = (1 + c) ^ a := by
  have h := add_pow c 1 a
  calc
    (∑ j ∈ range (a + 1), (a.choose j : ℝ) * c ^ j) =
        (c + 1) ^ a := by
      rw [h]
      apply sum_congr rfl
      intro j _
      simp
      ring
    _ = (1 + c) ^ a := by rw [add_comm]

/-- The first moment of the real binomial generating function. -/
lemma sum_natCast_mul_choose_mul_pow (a : ℕ) (c : ℝ) :
    (∑ j ∈ range (a + 1),
      (j : ℝ) * (a.choose j : ℝ) * c ^ j) =
      (a : ℝ) * c * (1 + c) ^ (a - 1) := by
  cases a with
  | zero => simp
  | succ n =>
      have hchoose (j : ℕ) :
          ((j + 1 : ℕ) * (n + 1).choose (j + 1) : ℝ) =
            ((n + 1 : ℕ) * n.choose j : ℝ) := by
        have h :
            (((n + 1).choose (j + 1) * (j + 1) : ℕ) : ℝ) =
              (((n + 1) * n.choose j : ℕ) : ℝ) := by
          exact_mod_cast (Nat.add_one_mul_choose_eq n j).symm
        simpa [mul_comm] using h
      calc
        (∑ j ∈ range (n + 1 + 1),
            (j : ℝ) * ((n + 1).choose j : ℝ) * c ^ j) =
            ∑ j ∈ range (n + 1),
              ((j + 1 : ℕ) : ℝ) * ((n + 1).choose (j + 1) : ℝ) *
                c ^ (j + 1) := by
          rw [sum_range_succ']
          simp
        _ = ∑ j ∈ range (n + 1),
              ((n + 1 : ℕ) : ℝ) * (n.choose j : ℝ) * c ^ (j + 1) := by
          apply sum_congr rfl
          intro j _
          rw [hchoose]
        _ = ((n + 1 : ℕ) : ℝ) * c *
              (∑ j ∈ range (n + 1), (n.choose j : ℝ) * c ^ j) := by
          rw [Finset.mul_sum]
          apply sum_congr rfl
          intro j _
          rw [pow_succ]
          ring
        _ = ((n + 1 : ℕ) : ℝ) * c * (1 + c) ^ n := by
          rw [sum_natCast_choose_mul_pow]
        _ = ((n + 1 : ℕ) : ℝ) * c *
              (1 + c) ^ (n + 1 - 1) := by simp

/-- The second factorial moment of the real binomial generating function. -/
lemma sum_natCast_mul_pred_mul_choose_mul_pow (a : ℕ) (c : ℝ) :
    (∑ j ∈ range (a + 1),
      (j : ℝ) * ((j : ℝ) - 1) * (a.choose j : ℝ) * c ^ j) =
      (a : ℝ) * ((a : ℝ) - 1) * c ^ 2 *
        (1 + c) ^ (a - 2) := by
  rcases a with (_ | _ | n)
  · simp
  · norm_num [sum_range_succ]
  · have hchoose (j : ℕ) :
        (((j + 2) * (j + 1) * (n + 2).choose (j + 2) : ℕ) : ℝ) =
          (((n + 2) * (n + 1) * n.choose j : ℕ) : ℝ) := by
      have hNat :
          (j + 2) * (j + 1) * (n + 2).choose (j + 2) =
            (n + 2) * (n + 1) * n.choose j := by
        calc
          (j + 2) * (j + 1) * (n + 2).choose (j + 2) =
              ((n + 2).choose (j + 2) * (j + 2)) * (j + 1) := by
            ac_rfl
          _ = ((n + 2) * (n + 1).choose (j + 1)) * (j + 1) := by
            rw [← Nat.add_one_mul_choose_eq (n + 1) (j + 1)]
          _ = (n + 2) * ((n + 1).choose (j + 1) * (j + 1)) := by
            ac_rfl
          _ = (n + 2) * ((n + 1) * n.choose j) := by
            rw [← Nat.add_one_mul_choose_eq n j]
          _ = (n + 2) * (n + 1) * n.choose j := by
            ac_rfl
      exact_mod_cast hNat
    calc
      (∑ j ∈ range (n + 2 + 1),
          (j : ℝ) * ((j : ℝ) - 1) * ((n + 2).choose j : ℝ) * c ^ j) =
          ∑ j ∈ range (n + 1),
            (((j + 2) : ℕ) : ℝ) * ((((j + 2) : ℕ) : ℝ) - 1) *
              ((n + 2).choose (j + 2) : ℝ) * c ^ (j + 2) := by
        rw [sum_range_succ', sum_range_succ']
        simp
        apply sum_congr rfl
        intro j _
        push_cast
        ring
      _ = ∑ j ∈ range (n + 1),
            (((n + 2) * (n + 1) : ℕ) : ℝ) * (n.choose j : ℝ) *
              c ^ (j + 2) := by
        apply sum_congr rfl
        intro j _
        have hj :
            ((j : ℝ) + 2) * ((j : ℝ) + 1) *
                ((n + 2).choose (j + 2) : ℝ) =
              ((n : ℝ) + 2) * ((n : ℝ) + 1) * (n.choose j : ℝ) := by
          simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one]
            using hchoose j
        rw [pow_add]
        calc
          (((j + 2 : ℕ) : ℝ) * (((j + 2 : ℕ) : ℝ) - 1) *
              ((n + 2).choose (j + 2) : ℝ)) * (c ^ j * c ^ 2) =
              (((j : ℝ) + 2) * ((j : ℝ) + 1) *
                ((n + 2).choose (j + 2) : ℝ)) * (c ^ j * c ^ 2) := by
            push_cast
            ring
          _ = (((n : ℝ) + 2) * ((n : ℝ) + 1) * (n.choose j : ℝ)) *
                (c ^ j * c ^ 2) := by rw [hj]
          _ = ((((n + 2) * (n + 1) : ℕ) : ℝ) * (n.choose j : ℝ)) *
                (c ^ j * c ^ 2) := by
            push_cast
            ring
      _ = (((n + 2) * (n + 1) : ℕ) : ℝ) * c ^ 2 *
            (∑ j ∈ range (n + 1), (n.choose j : ℝ) * c ^ j) := by
        rw [Finset.mul_sum]
        apply sum_congr rfl
        intro j _
        rw [pow_add]
        ring
      _ = (((n + 2) * (n + 1) : ℕ) : ℝ) * c ^ 2 *
            (1 + c) ^ n := by
        rw [sum_natCast_choose_mul_pow]
      _ = (((n + 2 : ℕ) : ℝ) * (((n + 2 : ℕ) : ℝ) - 1)) * c ^ 2 *
            (1 + c) ^ (n + 2 - 2) := by
        have hsub : n + 2 - 2 = n := by omega
        rw [hsub]
        push_cast
        ring

/-- The ordinary second moment of the real binomial generating function. -/
lemma sum_natCast_sq_mul_choose_mul_pow (a : ℕ) (c : ℝ) :
    (∑ j ∈ range (a + 1),
      (j : ℝ) ^ 2 * (a.choose j : ℝ) * c ^ j) =
      (a : ℝ) * c * (1 + c) ^ (a - 1) +
        (a : ℝ) * ((a : ℝ) - 1) * c ^ 2 *
          (1 + c) ^ (a - 2) := by
  rw [← sum_natCast_mul_choose_mul_pow a c,
    ← sum_natCast_mul_pred_mul_choose_mul_pow a c, ← sum_add_distrib]
  apply sum_congr rfl
  intro j _
  ring

/-- Exact summation of the affine-in-`j` error profile arising from
sequentially choosing distinct anchored edges. -/
lemma sum_choose_mul_pow_mul_affine_pred
    (a : ℕ) (c theta₀ theta₁ : ℝ) :
    (∑ j ∈ range (a + 1),
      (a.choose j : ℝ) * c ^ j *
        ((j : ℝ) * theta₀ +
          (j : ℝ) * ((j : ℝ) - 1) * theta₁)) =
      theta₀ * ((a : ℝ) * c * (1 + c) ^ (a - 1)) +
        theta₁ * ((a : ℝ) * ((a : ℝ) - 1) * c ^ 2 *
          (1 + c) ^ (a - 2)) := by
  calc
    (∑ j ∈ range (a + 1),
      (a.choose j : ℝ) * c ^ j *
        ((j : ℝ) * theta₀ +
          (j : ℝ) * ((j : ℝ) - 1) * theta₁)) =
        (∑ j ∈ range (a + 1),
          (j : ℝ) * (a.choose j : ℝ) * c ^ j) * theta₀ +
        (∑ j ∈ range (a + 1),
          (j : ℝ) * ((j : ℝ) - 1) *
            (a.choose j : ℝ) * c ^ j) * theta₁ := by
      rw [Finset.sum_mul, Finset.sum_mul, ← sum_add_distrib]
      apply sum_congr rfl
      intro j _
      ring
    _ = theta₀ * ((a : ℝ) * c * (1 + c) ^ (a - 1)) +
        theta₁ * ((a : ℝ) * ((a : ℝ) - 1) * c ^ 2 *
          (1 + c) ^ (a - 2)) := by
      rw [sum_natCast_mul_choose_mul_pow,
        sum_natCast_mul_pred_mul_choose_mul_pow]
      ring

/-- Degree normalization of the bad-family envelope at shifted index
`j = m+1`. -/
lemma badFamilyEnvelope_shift_eq
    (m : ℕ) (a C D beta : ℝ) (hD : D ≠ 0) :
    (beta / D) ^ (m + 1) * (a ^ 2 * C * (a * D) ^ m) =
      (a ^ 2 * (C / D)) * beta * (a * beta) ^ m := by
  rw [pow_succ, div_pow, mul_pow, mul_pow]
  field_simp [hD]

/-- Summing the bad-family envelope over `1 ≤ j ≤ a` after
`p = beta/D`.  The shifted `range a` index is `j-1`. -/
lemma sum_badFamilyEnvelope_shift_eq
    (a : ℕ) (C D beta : ℝ) (hD : D ≠ 0) :
    (∑ m ∈ range a,
      (beta / D) ^ (m + 1) *
        (((a : ℝ) ^ 2) * C * (((a : ℝ) * D) ^ m))) =
      ((a : ℝ) ^ 2 * (C / D)) * beta *
        ∑ m ∈ range a, (((a : ℝ) * beta) ^ m) := by
  rw [Finset.mul_sum]
  apply sum_congr rfl
  intro m _
  exact badFamilyEnvelope_shift_eq m (a : ℝ) C D beta hD

/-- If `C/D ≤ eta`, the complete bad-family contribution is bounded by
the corresponding finite geometric envelope. -/
lemma sum_badFamilyEnvelope_shift_le_of_codegree
    (a : ℕ) {C D beta eta : ℝ}
    (hD : 0 < D) (hbeta₀ : 0 ≤ beta) (hC₀ : 0 ≤ C)
    (hcodeg : C ≤ eta * D) :
    (∑ m ∈ range a,
      (beta / D) ^ (m + 1) *
        (((a : ℝ) ^ 2) * C * (((a : ℝ) * D) ^ m))) ≤
      eta * ((a : ℝ) ^ 2) * beta *
        ∑ m ∈ range a, (((a : ℝ) * beta) ^ m) := by
  rw [sum_badFamilyEnvelope_shift_eq a C D beta hD.ne']
  have heta₀ : 0 ≤ eta := by
    have hD₀ : 0 ≤ D := hD.le
    by_contra heta
    have : eta * D < 0 := mul_neg_of_neg_of_pos (lt_of_not_ge heta) hD
    linarith
  have hratio : C / D ≤ eta := (div_le_iff₀ hD).2 (by
    simpa [mul_comm] using hcodeg)
  have hsum₀ : 0 ≤ ∑ m ∈ range a, (((a : ℝ) * beta) ^ m) :=
    sum_nonneg fun m _ ↦ pow_nonneg
      (mul_nonneg (Nat.cast_nonneg a) hbeta₀) m
  have hfactor₀ : 0 ≤ (a : ℝ) ^ 2 * beta *
      ∑ m ∈ range a, (((a : ℝ) * beta) ^ m) :=
    mul_nonneg
      (mul_nonneg (sq_nonneg (a : ℝ)) hbeta₀) hsum₀
  calc
    ((a : ℝ) ^ 2 * (C / D)) * beta *
          ∑ m ∈ range a, (((a : ℝ) * beta) ^ m) =
        (C / D) * (((a : ℝ) ^ 2 * beta *
          ∑ m ∈ range a, (((a : ℝ) * beta) ^ m))) := by ring
    _ ≤ eta * (((a : ℝ) ^ 2 * beta *
          ∑ m ∈ range a, (((a : ℝ) * beta) ^ m))) :=
      mul_le_mul_of_nonneg_right hratio hfactor₀
    _ = eta * ((a : ℝ) ^ 2) * beta *
          ∑ m ∈ range a, (((a : ℝ) * beta) ^ m) := by ring

/-- Termwise normalized power loss for a sequential lower factor. -/
lemma normalized_sequential_power_deficit_le
    (j : ℕ) {ell theta₀ theta₁ beta : ℝ}
    (hell₀ : 0 ≤ ell) (hell₁ : ell ≤ 1)
    (hprofile : 1 - ell ≤ theta₀ + ((j : ℝ) - 1) * theta₁)
    (hbeta₀ : 0 ≤ beta) :
    beta ^ j * (1 - ell ^ j) ≤
      beta ^ j * ((j : ℝ) * theta₀ +
        (j : ℝ) * ((j : ℝ) - 1) * theta₁) := by
  have hpowOrder : ell ^ j ≤ (1 : ℝ) ^ j :=
    pow_le_pow_left₀ hell₀ hell₁ j
  have hmax : max |(1 : ℝ)| |ell| = 1 := by
    rw [abs_one, abs_of_nonneg hell₀, max_eq_left hell₁]
  have hpowAbs := abs_pow_sub_pow_le (a := (1 : ℝ)) (b := ell) (n := j)
  rw [abs_of_nonneg (sub_nonneg.mpr hpowOrder),
    abs_of_nonneg (sub_nonneg.mpr hell₁), hmax] at hpowAbs
  simp only [one_pow, mul_one] at hpowAbs
  have hpow : 1 - ell ^ j ≤ (j : ℝ) * (1 - ell) := by
    simpa [one_pow, mul_comm] using hpowAbs
  have hj₀ : 0 ≤ (j : ℝ) := Nat.cast_nonneg j
  have hlinear :
      (j : ℝ) * (1 - ell) ≤
        (j : ℝ) * (theta₀ + ((j : ℝ) - 1) * theta₁) :=
    mul_le_mul_of_nonneg_left hprofile hj₀
  have hbetaPow₀ : 0 ≤ beta ^ j := pow_nonneg hbeta₀ j
  calc
    beta ^ j * (1 - ell ^ j) ≤
        beta ^ j * ((j : ℝ) * (1 - ell)) :=
      mul_le_mul_of_nonneg_left hpow hbetaPow₀
    _ ≤ beta ^ j *
        ((j : ℝ) * (theta₀ + ((j : ℝ) - 1) * theta₁)) :=
      mul_le_mul_of_nonneg_left hlinear hbetaPow₀
    _ = beta ^ j * ((j : ℝ) * theta₀ +
        (j : ℝ) * ((j : ℝ) - 1) * theta₁) := by ring

/-- Summed normalized sequential deficit.  The right side is expressed by
the first two factorial moments of the binomial generating function. -/
lemma sum_choose_normalized_sequential_power_deficit_le
    (a : ℕ) (ell : ℕ → ℝ) {theta₀ theta₁ beta : ℝ}
    (hbeta₀ : 0 ≤ beta)
    (hell : ∀ j ∈ range (a + 1), 0 < j → 0 ≤ ell j ∧ ell j ≤ 1)
    (hprofile : ∀ j ∈ range (a + 1), 0 < j →
      1 - ell j ≤ theta₀ + ((j : ℝ) - 1) * theta₁) :
    (∑ j ∈ range (a + 1),
      (a.choose j : ℝ) * (beta ^ j * (1 - ell j ^ j))) ≤
      theta₀ * ((a : ℝ) * beta * (1 + beta) ^ (a - 1)) +
        theta₁ * ((a : ℝ) * ((a : ℝ) - 1) * beta ^ 2 *
          (1 + beta) ^ (a - 2)) := by
  calc
    (∑ j ∈ range (a + 1),
      (a.choose j : ℝ) * (beta ^ j * (1 - ell j ^ j))) ≤
        ∑ j ∈ range (a + 1),
          (a.choose j : ℝ) *
            (beta ^ j * ((j : ℝ) * theta₀ +
              (j : ℝ) * ((j : ℝ) - 1) * theta₁)) := by
      apply sum_le_sum
      intro j hj
      by_cases hj₀ : j = 0
      · simp [hj₀]
      · have hjpos : 0 < j := Nat.pos_of_ne_zero hj₀
        simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
            (normalized_sequential_power_deficit_le j
              (hell j hj hjpos).1 (hell j hj hjpos).2
              (hprofile j hj hjpos) hbeta₀)
            (Nat.cast_nonneg (a.choose j))
    _ = theta₀ * ((a : ℝ) * beta * (1 + beta) ^ (a - 1)) +
        theta₁ * ((a : ℝ) * ((a : ℝ) - 1) * beta ^ 2 *
          (1 + beta) ^ (a - 2)) := by
      rw [← sum_choose_mul_pow_mul_affine_pred]
      apply sum_congr rfl
      intro j _
      ring

/-- Scaling a raw degree-power deficit by `p = beta/D` is exactly the
corresponding normalized deficit. -/
lemma scaledPowerDeficit_eq_normalized
    (j : ℕ) (D beta lower : ℝ) (hD : D ≠ 0) :
    (beta / D) ^ j * (D ^ j - lower ^ j) =
      beta ^ j * (1 - (lower / D) ^ j) := by
  rw [div_pow, div_pow]
  field_simp [hD]

/-- Summable comparison of arbitrary sequential lower factors with `D^j`.
Only positive `j` require the factors to lie in `[0,D]`; the zeroth deficit
vanishes identically. -/
lemma sum_choose_scaledPowerDeficit_le
    (a : ℕ) (lower : ℕ → ℝ) {D beta theta₀ theta₁ : ℝ}
    (hD : 0 < D) (hbeta₀ : 0 ≤ beta)
    (hlower : ∀ j ∈ range (a + 1), 0 < j →
      0 ≤ lower j ∧ lower j ≤ D)
    (hprofile : ∀ j ∈ range (a + 1), 0 < j →
      1 - lower j / D ≤ theta₀ + ((j : ℝ) - 1) * theta₁) :
    (∑ j ∈ range (a + 1),
      (a.choose j : ℝ) * (beta / D) ^ j *
        (D ^ j - lower j ^ j)) ≤
      theta₀ * ((a : ℝ) * beta * (1 + beta) ^ (a - 1)) +
        theta₁ * ((a : ℝ) * ((a : ℝ) - 1) * beta ^ 2 *
          (1 + beta) ^ (a - 2)) := by
  calc
    (∑ j ∈ range (a + 1),
      (a.choose j : ℝ) * (beta / D) ^ j *
        (D ^ j - lower j ^ j)) =
        ∑ j ∈ range (a + 1),
          (a.choose j : ℝ) *
            (beta ^ j * (1 - (lower j / D) ^ j)) := by
      apply sum_congr rfl
      intro j _
      calc
        (a.choose j : ℝ) * (beta / D) ^ j *
            (D ^ j - lower j ^ j) =
            (a.choose j : ℝ) *
              ((beta / D) ^ j * (D ^ j - lower j ^ j)) := by ring
        _ = (a.choose j : ℝ) *
              (beta ^ j * (1 - (lower j / D) ^ j)) := by
          rw [scaledPowerDeficit_eq_normalized j D beta (lower j) hD.ne']
    _ ≤ theta₀ * ((a : ℝ) * beta * (1 + beta) ^ (a - 1)) +
        theta₁ * ((a : ℝ) * ((a : ℝ) - 1) * beta ^ 2 *
          (1 + beta) ^ (a - 2)) := by
      apply sum_choose_normalized_sequential_power_deficit_le
        a (fun j ↦ lower j / D) hbeta₀
      · intro j hj hjpos
        constructor
        · exact div_nonneg (hlower j hj hjpos).1 hD.le
        · exact (div_le_one hD).2 (hlower j hj hjpos).2
      · exact hprofile

/-- The preceding comparison specialized to the unique-anchor sequential
choice factor
`Dlow - (a-1)C - (j-1)kC`. -/
lemma sum_choose_scaledSequentialLower_deficit_le
    (a k : ℕ) {D degreeLower C beta : ℝ}
    (hD : 0 < D) (hbeta₀ : 0 ≤ beta)
    (hlower : ∀ j ∈ range (a + 1), 0 < j →
      0 ≤ degreeLower - ((a : ℝ) - 1) * C -
          ((j : ℝ) - 1) * (k : ℝ) * C ∧
        degreeLower - ((a : ℝ) - 1) * C -
          ((j : ℝ) - 1) * (k : ℝ) * C ≤ D) :
    (∑ j ∈ range (a + 1),
      (a.choose j : ℝ) * (beta / D) ^ j *
        (D ^ j -
          (degreeLower - ((a : ℝ) - 1) * C -
            ((j : ℝ) - 1) * (k : ℝ) * C) ^ j)) ≤
      ((D - degreeLower + ((a : ℝ) - 1) * C) / D) *
          ((a : ℝ) * beta * (1 + beta) ^ (a - 1)) +
        (((k : ℝ) * C) / D) *
          ((a : ℝ) * ((a : ℝ) - 1) * beta ^ 2 *
            (1 + beta) ^ (a - 2)) := by
  apply sum_choose_scaledPowerDeficit_le a
    (fun j ↦ degreeLower - ((a : ℝ) - 1) * C -
      ((j : ℝ) - 1) * (k : ℝ) * C) hD hbeta₀ hlower
  intro j _ _
  field_simp [hD.ne']
  linarith

/-! ### Honest alternating-moment intervals and sensitivities

Termwise lower and upper bounds for factorial moments do not give a
one-sided bound on their inclusion--exclusion sum with the same endpoint in
every degree: the endpoint reverses with parity.  The next definitions make
the two honest parity-mixed endpoints explicit. -/

/-- The finite alternating sum of a moment profile through order `a`. -/
def alternatingMomentSum (a : ℕ) (moment : ℕ → ℝ) : ℝ :=
  ∑ j ∈ range (a + 1), (-1 : ℝ) ^ j * moment j

/-- The lower parity-mixed endpoint: lower moments in even degrees and upper
moments in odd degrees. -/
def parityMixedMomentLower
    (a : ℕ) (lower upper : ℕ → ℝ) : ℝ :=
  ∑ j ∈ range (a + 1), if Even j then lower j else -upper j

/-- The upper parity-mixed endpoint: upper moments in even degrees and lower
moments in odd degrees. -/
def parityMixedMomentUpper
    (a : ℕ) (lower upper : ℕ → ℝ) : ℝ :=
  ∑ j ∈ range (a + 1), if Even j then upper j else -lower j

/-- Termwise moment intervals imply the honest parity-mixed interval for the
full inclusion--exclusion polynomial. -/
lemma alternatingMomentSum_mem_parityMixedInterval
    (a : ℕ) (lower moment upper : ℕ → ℝ)
    (hbounds : ∀ j ∈ range (a + 1), lower j ≤ moment j ∧ moment j ≤ upper j) :
    alternatingMomentSum a moment ∈ Set.Icc
      (parityMixedMomentLower a lower upper)
      (parityMixedMomentUpper a lower upper) := by
  constructor
  · apply sum_le_sum
    intro j hj
    by_cases heven : Even j
    · simpa [alternatingMomentSum, parityMixedMomentLower,
        neg_one_pow_eq_ite, heven] using (hbounds j hj).1
    · simpa [alternatingMomentSum, parityMixedMomentLower,
        neg_one_pow_eq_ite, heven] using neg_le_neg (hbounds j hj).2
  · apply sum_le_sum
    intro j hj
    by_cases heven : Even j
    · simpa [alternatingMomentSum, parityMixedMomentUpper,
        neg_one_pow_eq_ite, heven] using (hbounds j hj).2
    · simpa [alternatingMomentSum, parityMixedMomentUpper,
        neg_one_pow_eq_ite, heven] using neg_le_neg (hbounds j hj).1

/-- The width of the honest parity-mixed interval is the sum of the
termwise widths.  This identity is useful for assigning a non-uniform
sensitivity weight to each moment order. -/
lemma parityMixedMomentUpper_sub_lower
    (a : ℕ) (lower upper : ℕ → ℝ) :
    parityMixedMomentUpper a lower upper -
        parityMixedMomentLower a lower upper =
      ∑ j ∈ range (a + 1), (upper j - lower j) := by
  rw [parityMixedMomentUpper, parityMixedMomentLower, ← sum_sub_distrib]
  apply sum_congr rfl
  intro j _
  by_cases heven : Even j <;> simp [heven] <;> ring

/-- The ideal full alternating one-step polynomial for a joint uncovered
moment of order `a`.  Its compact form retains the damping that is lost by
bounding all inclusion--exclusion coefficients in absolute value. -/
def meanFieldJointUpdate (a k : ℕ) (beta x : ℝ) : ℝ :=
  (x - beta * x ^ k) ^ a

/-- Exact inclusion--exclusion expansion of the ideal joint-moment update. -/
lemma meanFieldJointUpdate_eq_alternatingPolynomial
    (a k : ℕ) (beta x : ℝ) :
    meanFieldJointUpdate a k beta x =
      ∑ j ∈ range (a + 1),
        (a.choose j : ℝ) * (-beta * x ^ k) ^ j * x ^ (a - j) := by
  rw [meanFieldJointUpdate, show x - beta * x ^ k =
      (-beta * x ^ k) + x by ring, add_pow]
  apply sum_congr rfl
  intro j _
  ring

/-- The scalar mean-field step appearing inside every joint-moment update. -/
def meanFieldStep (k : ℕ) (beta x : ℝ) : ℝ :=
  x - beta * x ^ k

/-- The positive kernel governing absolute error propagation through one
all-order inclusion--exclusion step. -/
def meanFieldPlusJointUpdate (a k : ℕ) (beta x : ℝ) : ℝ :=
  (x + beta * x ^ k) ^ a

/-- Exact binomial expansion of the positive error-propagation kernel. -/
lemma meanFieldPlusJointUpdate_eq_kernel
    (a k : ℕ) (beta x : ℝ) :
    meanFieldPlusJointUpdate a k beta x =
      ∑ j ∈ range (a + 1),
        (a.choose j : ℝ) * (beta * x ^ k) ^ j * x ^ (a - j) := by
  rw [meanFieldPlusJointUpdate, show x + beta * x ^ k =
      (beta * x ^ k) + x by ring, add_pow]
  apply sum_congr rfl
  intro j _
  ring

/-- A power weight of the enlarged joint-set order is exactly the raw
binomial kernel term. -/
lemma meanFieldPlusKernelTerm_eq
    {a k j : ℕ} (hk : 0 < k) (hj : j ≤ a) (beta x : ℝ) :
    (beta * x ^ k) ^ j * x ^ (a - j) =
      beta ^ j * x ^ (a + j * (k - 1)) := by
  have hexp : k * j + (a - j) = a + j * (k - 1) := by
    calc
      k * j + (a - j) = ((k - 1) + 1) * j + (a - j) := by
        rw [Nat.sub_add_cancel (by omega : 1 ≤ k)]
      _ = (k - 1) * j + (j + (a - j)) := by
        simp only [Nat.add_mul, one_mul, Nat.add_assoc]
      _ = (k - 1) * j + a := by rw [Nat.add_sub_of_le hj]
      _ = a + j * (k - 1) := by
        rw [Nat.mul_comm, Nat.add_comm]
  rw [mul_pow, ← pow_mul, mul_assoc, ← pow_add]
  rw [hexp]

/-- Canonical enlarged-order form of the positive propagation kernel. -/
lemma meanFieldPlusJointUpdate_eq_enlargedOrderKernel
    (a : ℕ) {k : ℕ} (hk : 0 < k) (beta x : ℝ) :
    meanFieldPlusJointUpdate a k beta x =
      ∑ j ∈ range (a + 1),
        (a.choose j : ℝ) * beta ^ j *
          x ^ (a + j * (k - 1)) := by
  rw [meanFieldPlusJointUpdate_eq_kernel]
  apply sum_congr rfl
  intro j hj
  have hja : j ≤ a := by
    have := mem_range.mp hj
    omega
  rw [mul_assoc, meanFieldPlusKernelTerm_eq hk hja]
  ring

/-- Changing the positive-kernel coefficient is charged by the derivative
at the upper endpoint.  This is the derivative-shaped injection for an
isolation interval `alpha ≤ beta`. -/
lemma meanFieldPlusJointUpdate_sub_le_coefficientSensitivity
    (a k : ℕ) {alpha beta x : ℝ}
    (halpha₀ : 0 ≤ alpha) (halphaBeta : alpha ≤ beta) (hx₀ : 0 ≤ x) :
    meanFieldPlusJointUpdate a k beta x -
        meanFieldPlusJointUpdate a k alpha x ≤
      (beta - alpha) *
        ((a : ℝ) * x ^ k *
          (x + beta * x ^ k) ^ (a - 1)) := by
  have hbeta₀ : 0 ≤ beta := halpha₀.trans halphaBeta
  have hxpow₀ : 0 ≤ x ^ k := pow_nonneg hx₀ k
  have hlower₀ : 0 ≤ x + alpha * x ^ k :=
    add_nonneg hx₀ (mul_nonneg halpha₀ hxpow₀)
  have hupper₀ : 0 ≤ x + beta * x ^ k :=
    add_nonneg hx₀ (mul_nonneg hbeta₀ hxpow₀)
  have hlowerUpper : x + alpha * x ^ k ≤ x + beta * x ^ k := by
    gcongr
  have hpow : (x + alpha * x ^ k) ^ a ≤
      (x + beta * x ^ k) ^ a :=
    pow_le_pow_left₀ hlower₀ hlowerUpper a
  have habs := abs_pow_sub_pow_le
    (a := x + beta * x ^ k) (b := x + alpha * x ^ k) (n := a)
  rw [abs_of_nonneg (sub_nonneg.mpr hpow),
    abs_of_nonneg (sub_nonneg.mpr hlowerUpper),
    abs_of_nonneg hupper₀, abs_of_nonneg hlower₀,
    max_eq_left hlowerUpper] at habs
  calc
    meanFieldPlusJointUpdate a k beta x -
          meanFieldPlusJointUpdate a k alpha x ≤
        (a : ℝ) *
          ((x + beta * x ^ k) - (x + alpha * x ^ k)) *
            (x + beta * x ^ k) ^ (a - 1) := by
      simpa [meanFieldPlusJointUpdate, mul_assoc, mul_left_comm, mul_comm] using habs
    _ = (beta - alpha) *
        ((a : ℝ) * x ^ k *
          (x + beta * x ^ k) ^ (a - 1)) := by ring

/-- The scalar plus step induced on a power weight by the absolute
moment-error propagation kernel. -/
def meanFieldPlusStep (k : ℕ) (beta x : ℝ) : ℝ :=
  x + beta * x ^ k

/-- Finite union bound in product form.  It is the elementary estimate used
to replace the exact Bernoulli isolation product by an explicit collision
error. -/
lemma one_sub_sum_le_prod_one_sub
    {I : Type*} [DecidableEq I] (s : Finset I) (p : I → ℝ)
    (hp₀ : ∀ i ∈ s, 0 ≤ p i) (hp₁ : ∀ i ∈ s, p i ≤ 1) :
    1 - ∑ i ∈ s, p i ≤ ∏ i ∈ s, (1 - p i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      have hpa₀ : 0 ≤ p a := hp₀ a (mem_insert_self a s)
      have hpa₁ : p a ≤ 1 := hp₁ a (mem_insert_self a s)
      have hs₀ : 0 ≤ ∑ i ∈ s, p i :=
        sum_nonneg fun i hi ↦ hp₀ i (mem_insert_of_mem hi)
      have hih := ih
        (fun i hi ↦ hp₀ i (mem_insert_of_mem hi))
        (fun i hi ↦ hp₁ i (mem_insert_of_mem hi))
      rw [sum_insert ha, prod_insert ha]
      calc
        1 - (p a + ∑ i ∈ s, p i) ≤
            (1 - p a) * (1 - ∑ i ∈ s, p i) := by
          nlinarith
        _ ≤ (1 - p a) * ∏ i ∈ s, (1 - p i) :=
          mul_le_mul_of_nonneg_left hih (sub_nonneg.mpr hpa₁)

/-- A finite product of Bernoulli failure probabilities lies in `[0,1]`. -/
lemma prod_one_sub_mem_Icc
    {I : Type*} [DecidableEq I] (s : Finset I) (p : I → ℝ)
    (hp₀ : ∀ i ∈ s, 0 ≤ p i) (hp₁ : ∀ i ∈ s, p i ≤ 1) :
    (∏ i ∈ s, (1 - p i)) ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · exact prod_nonneg fun i hi ↦ sub_nonneg.mpr (hp₁ i hi)
  · exact prod_le_one (fun i hi ↦ sub_nonneg.mpr (hp₁ i hi))
      (fun i hi ↦ by linarith [hp₀ i hi])

/-- First Bonferroni inequality for the indicator that a finite count is
zero. -/
lemma one_sub_natCast_le_indicator_eq_zero (n : ℕ) :
    1 - (n : ℝ) ≤ if n = 0 then 1 else 0 := by
  cases n with
  | zero => simp
  | succ n =>
      rw [if_neg (Nat.succ_ne_zero n)]
      push_cast
      have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith

/-- Second Bonferroni inequality for the indicator that a finite count is
zero.  The quadratic term is the number of unordered pairs, written over
the reals. -/
lemma indicator_eq_zero_le_one_sub_add_pairCount (n : ℕ) :
    (if n = 0 then (1 : ℝ) else 0) ≤
      1 - (n : ℝ) + (n : ℝ) * ((n : ℝ) - 1) / 2 := by
  by_cases h₀ : n = 0
  · simp [h₀]
  by_cases h₁ : n = 1
  · simp [h₁]
  rw [if_neg h₀]
  have hnNat : 2 ≤ n := by omega
  have hn : (2 : ℝ) ≤ n := by exact_mod_cast hnNat
  have hprod : 0 ≤ ((n : ℝ) - 1) * ((n : ℝ) - 2) :=
    mul_nonneg (by linarith) (by linarith)
  nlinarith

/-- The error after linearizing the map `x ↦ x^a` across a decrement `d`.
This named expression makes the fixed-round mean-field error recursion
readable. -/
def powerLinearizationError (a : ℕ) (x y d : ℝ) : ℝ :=
  x ^ a - y ^ a + (a : ℝ) * d * y ^ (a - 1)

@[simp] lemma powerLinearizationError_zero (x y d : ℝ) :
    powerLinearizationError 0 x y d = 0 := by
  simp [powerLinearizationError]

/-- A second-order bound for the power-map linearization on `[0,1]`.
If `x = y-d`, the remainder is nonnegative and at most `a^2 d^2`.
The deliberately coarse square constant is convenient for the finite
joint-moment induction. -/
lemma powerLinearizationError_mem_Icc
    (a : ℕ) {x y d : ℝ}
    (hx₀ : 0 ≤ x) (hx₁ : x ≤ 1) (hy₁ : y ≤ 1)
    (hd₀ : 0 ≤ d) (hxy : x = y - d) :
    powerLinearizationError a x y d ∈
      Set.Icc 0 (((a : ℝ) ^ 2) * d ^ 2) := by
  induction a with
  | zero => simp
  | succ a ih =>
      by_cases ha : a = 0
      · subst a
        constructor
        · simp [powerLinearizationError, hxy]
        · simp [powerLinearizationError, hxy, sq_nonneg]
      · have ha₁ : 1 ≤ a := Nat.one_le_iff_ne_zero.mpr ha
        have hy₀ : 0 ≤ y := by linarith [hxy]
        have hrec :
            powerLinearizationError (a + 1) x y d =
              x * powerLinearizationError a x y d +
                (a : ℝ) * d ^ 2 * y ^ (a - 1) := by
          unfold powerLinearizationError
          rw [pow_succ, show a + 1 - 1 = a by omega]
          have hpow : y ^ a = y ^ (a - 1) * y := by
            conv_lhs => rw [← Nat.sub_add_cancel ha₁]
            rw [pow_add, pow_one]
          simp_rw [hpow]
          rw [hxy]
          push_cast
          ring_nf
          rw [hpow]
          ring
        rw [hrec]
        constructor
        · exact add_nonneg
            (mul_nonneg hx₀ ih.1)
            (mul_nonneg
              (mul_nonneg (Nat.cast_nonneg a) (sq_nonneg d))
              (pow_nonneg hy₀ _))
        · have hpow₁ : y ^ (a - 1) ≤ 1 :=
            pow_le_one₀ hy₀ hy₁
          have hfirst :
              x * powerLinearizationError a x y d ≤
                1 * (((a : ℝ) ^ 2) * d ^ 2) :=
            mul_le_mul hx₁ ih.2 ih.1 (by norm_num)
          have hsecond :
              (a : ℝ) * d ^ 2 * y ^ (a - 1) ≤
                (a : ℝ) * d ^ 2 * 1 :=
            mul_le_mul_of_nonneg_left hpow₁
              (mul_nonneg (Nat.cast_nonneg a) (sq_nonneg d))
          calc
            x * powerLinearizationError a x y d +
                (a : ℝ) * d ^ 2 * y ^ (a - 1) ≤
              1 * (((a : ℝ) ^ 2) * d ^ 2) +
                (a : ℝ) * d ^ 2 * 1 := add_le_add hfirst hsecond
            _ ≤ (((a + 1 : ℕ) : ℝ) ^ 2) * d ^ 2 := by
              push_cast
              have hd2 : 0 ≤ d ^ 2 := sq_nonneg d
              have haPlus : 0 ≤ (a : ℝ) + 1 := by positivity
              nlinarith [mul_nonneg haPlus hd2]

/-- The scalar deficit in the truncation-stable profile lower bound.  The
four terms on the right charge, respectively, the one-round collision
factor, the low-codegree/degree deficit, and the coarse moment tolerance.
This form deliberately remains valid when either truncated lower factor is
zero. -/
lemma linearProfileDeficit_le
    {a target epsilon collision deficit : ℝ}
    (ha₀ : 0 ≤ a) (htarget₀ : 0 ≤ target) (htarget₁ : target ≤ 1)
    (hepsilon₀ : 0 ≤ epsilon)
    (hcollision₀ : 0 ≤ collision) (hcollision₁ : collision ≤ 1)
    (hdeficit₀ : 0 ≤ deficit) :
    a * target - (1 - collision) * max 0 (a - deficit) *
        max 0 (target - epsilon) ≤
      a * collision + deficit + a * epsilon := by
  by_cases haDeficit : 0 ≤ a - deficit
  · rw [max_eq_right haDeficit]
    by_cases htargetEpsilon : 0 ≤ target - epsilon
    · rw [max_eq_right htargetEpsilon]
      have hac₀ : 0 ≤ 1 - collision := sub_nonneg.mpr hcollision₁
      have haSubLe : a - deficit ≤ a := by linarith
      have htSubLe : target - epsilon ≤ 1 := by linarith
      have hcollisionTerm :
          collision * (a - deficit) * (target - epsilon) ≤
            collision * a := by
        calc
          collision * (a - deficit) * (target - epsilon) ≤
              collision * a * (target - epsilon) := by
            gcongr
          _ ≤ collision * a * 1 := by
            gcongr
          _ = collision * a := by ring
      have hdeficitTarget : deficit * target ≤ deficit := by
        simpa using mul_le_mul_of_nonneg_left htarget₁ hdeficit₀
      have hdeficitEpsilon₀ : 0 ≤ deficit * epsilon :=
        mul_nonneg hdeficit₀ hepsilon₀
      nlinarith
    · rw [max_eq_left (le_of_not_ge htargetEpsilon)]
      have htLeEpsilon : target ≤ epsilon := by linarith
      have hatLe : a * target ≤ a * epsilon :=
        mul_le_mul_of_nonneg_left htLeEpsilon ha₀
      calc
        a * target - (1 - collision) * (a - deficit) * 0 =
            a * target := by ring
        _ ≤ a * epsilon := hatLe
        _ ≤ a * collision + deficit + a * epsilon := by
          have hac₀ : 0 ≤ a * collision := mul_nonneg ha₀ hcollision₀
          linarith
  · rw [max_eq_left (le_of_not_ge haDeficit)]
    have haLeDeficit : a ≤ deficit := by linarith
    have hatLeA : a * target ≤ a := by
      simpa using mul_le_mul_of_nonneg_left htarget₁ ha₀
    have hatLeDeficit : a * target ≤ deficit := hatLeA.trans haLeDeficit
    calc
      a * target - (1 - collision) * 0 * max 0 (target - epsilon) =
          a * target := by ring
      _ ≤ deficit := hatLeDeficit
      _ ≤ a * collision + deficit + a * epsilon := by
        have hac₀ : 0 ≤ a * collision := mul_nonneg ha₀ hcollision₀
        have hae₀ : 0 ≤ a * epsilon := mul_nonneg ha₀ hepsilon₀
        linarith

/-- A coarse but nonnegative error charged by one joint-moment step for a
set of size `a`.  It is arranged so that every term is visibly of order
`beta * previousError`, `beta^2`, or `beta * eta`. -/
def jointMomentStepError (a k : ℕ) (beta eta epsilonA epsilonNext : ℝ) : ℝ :=
  (1 + (((a : ℝ) * beta) ^ 2) / 2) * epsilonA +
    (a : ℝ) * beta * epsilonNext +
    beta ^ 2 *
      (((3 : ℝ) / 2) * (a : ℝ) ^ 2 + (a : ℝ) * (k : ℝ)) +
    beta * eta *
      ((a : ℝ) + (a : ℝ) ^ 2 * ((k : ℝ) + 1))

lemma jointMomentStepError_nonneg
    (a k : ℕ) {beta eta epsilonA epsilonNext : ℝ}
    (hbeta₀ : 0 ≤ beta) (heta₀ : 0 ≤ eta)
    (hepsilonA₀ : 0 ≤ epsilonA) (hepsilonNext₀ : 0 ≤ epsilonNext) :
    0 ≤ jointMomentStepError a k beta eta epsilonA epsilonNext := by
  unfold jointMomentStepError
  positivity

lemma lower_charge_le_jointMomentStepError
    (a k : ℕ) {beta eta epsilonA epsilonNext : ℝ}
    (hbeta₀ : 0 ≤ beta) (heta₀ : 0 ≤ eta)
    (hepsilonA₀ : 0 ≤ epsilonA) :
    epsilonA + (a : ℝ) * beta * epsilonNext +
        (a : ℝ) ^ 2 * beta * eta + (a : ℝ) ^ 2 * beta ^ 2 ≤
      jointMomentStepError a k beta eta epsilonA epsilonNext := by
  unfold jointMomentStepError
  have hpairEpsilon₀ :
      0 ≤ ((((a : ℝ) * beta) ^ 2) / 2) * epsilonA := by positivity
  have hetaExtra₀ :
      0 ≤ beta * eta *
        ((a : ℝ) + (a : ℝ) ^ 2 * ((k : ℝ) + 1)) -
          (a : ℝ) ^ 2 * beta * eta := by
    have hB : (a : ℝ) ^ 2 ≤
        (a : ℝ) + (a : ℝ) ^ 2 * ((k : ℝ) + 1) := by
      have haCast₀ : 0 ≤ (a : ℝ) := Nat.cast_nonneg a
      have hak₀ : 0 ≤ (a : ℝ) ^ 2 * (k : ℝ) :=
        mul_nonneg (sq_nonneg _) (Nat.cast_nonneg k)
      nlinarith
    have := mul_le_mul_of_nonneg_left hB (mul_nonneg hbeta₀ heta₀)
    nlinarith
  have hbetaExtra₀ :
      0 ≤ beta ^ 2 *
          (((3 : ℝ) / 2) * (a : ℝ) ^ 2 +
            (a : ℝ) * (k : ℝ)) -
        (a : ℝ) ^ 2 * beta ^ 2 := by
    have hak₀ : 0 ≤ (a : ℝ) * (k : ℝ) :=
      mul_nonneg (Nat.cast_nonneg a) (Nat.cast_nonneg k)
    nlinarith [sq_nonneg beta, sq_nonneg (a : ℝ)]
  nlinarith

lemma upper_charge_le_jointMomentStepError
    (a k : ℕ) {beta eta epsilonA epsilonNext : ℝ} :
    epsilonA + beta *
        ((a : ℝ) * ((k : ℝ) * beta) +
          eta * ((a : ℝ) + (a : ℝ) ^ 2 * ((k : ℝ) + 1)) +
          (a : ℝ) * epsilonNext) +
        (((a : ℝ) * beta) ^ 2) / 2 * (1 + epsilonA) ≤
      jointMomentStepError a k beta eta epsilonA epsilonNext := by
  unfold jointMomentStepError
  have hsq : 0 ≤ beta ^ 2 * (a : ℝ) ^ 2 :=
    mul_nonneg (sq_nonneg beta) (sq_nonneg (a : ℝ))
  ring_nf
  nlinarith

/-- Scalar stability of one joint-moment step around the Euler mean-field
trajectory.  The hypothesis is exactly the interval produced after
substituting `p = beta / D`, lower degree `(1-eta)D`, and codegree
`eta D` in the real profile recurrence. -/
theorem abs_next_pow_le_jointMomentStepError
    (a k : ℕ) (ha : 0 < a) (hk : 0 < k)
    {beta eta epsilonA epsilonNext y x next : ℝ}
    (hbeta₀ : 0 ≤ beta) (hbeta₁ : beta ≤ 1)
    (heta₀ : 0 ≤ eta)
    (hepsilonA₀ : 0 ≤ epsilonA)
    (hepsilonNext₀ : 0 ≤ epsilonNext)
    (hcollision : (k : ℝ) * beta ≤ 1)
    (hy : y ∈ Set.Icc (0 : ℝ) 1)
    (hx : x ∈ Set.Icc (0 : ℝ) 1)
    (hxy : x = y - beta * y ^ k)
    (hnext : next ∈ Set.Icc
      (y ^ a - epsilonA - beta *
        ((a : ℝ) * (y ^ (a + k - 1) + epsilonNext) +
          (a : ℝ) ^ 2 * eta))
      (y ^ a + epsilonA -
          beta * (1 - (k : ℝ) * beta) *
            max 0
              ((a : ℝ) - eta *
                ((a : ℝ) + (a : ℝ) ^ 2 * ((k : ℝ) + 1))) *
            max 0 (y ^ (a + k - 1) - epsilonNext) +
        (((a : ℝ) * beta) ^ 2) / 2 * (y ^ a + epsilonA))) :
    |next - x ^ a| ≤
      jointMomentStepError a k beta eta epsilonA epsilonNext := by
  let ar : ℝ := a
  let kr : ℝ := k
  let target : ℝ := y ^ (a + k - 1)
  let deficit : ℝ := eta * (ar + ar ^ 2 * (kr + 1))
  let collision : ℝ := kr * beta
  let pairError : ℝ := (ar * beta) ^ 2 / 2
  let remainder : ℝ := powerLinearizationError a x y (beta * y ^ k)
  have har₀ : 0 ≤ ar := Nat.cast_nonneg a
  have hkr₀ : 0 ≤ kr := Nat.cast_nonneg k
  have htarget : target ∈ Set.Icc (0 : ℝ) 1 := by
    exact ⟨pow_nonneg hy.1 _, pow_le_one₀ hy.1 hy.2⟩
  have hcollisionIcc : collision ∈ Set.Icc (0 : ℝ) 1 := by
    exact ⟨mul_nonneg hkr₀ hbeta₀, hcollision⟩
  have hdeficit₀ : 0 ≤ deficit := by
    dsimp only [deficit, ar, kr]
    positivity
  have hprofileDeficit :
      ar * target - (1 - collision) * max 0 (ar - deficit) *
          max 0 (target - epsilonNext) ≤
        ar * collision + deficit + ar * epsilonNext :=
    linearProfileDeficit_le har₀ htarget.1 htarget.2 hepsilonNext₀
      hcollisionIcc.1 hcollisionIcc.2 hdeficit₀
  have hprofileDeficitScaled :
      beta * (ar * target - (1 - collision) * max 0 (ar - deficit) *
          max 0 (target - epsilonNext)) ≤
        beta * (ar * collision + deficit + ar * epsilonNext) :=
    mul_le_mul_of_nonneg_left hprofileDeficit hbeta₀
  have hyPowK : y ^ k ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨pow_nonneg hy.1 _, pow_le_one₀ hy.1 hy.2⟩
  have hd₀ : 0 ≤ beta * y ^ k := mul_nonneg hbeta₀ hyPowK.1
  have hdLe : beta * y ^ k ≤ beta := by
    simpa using mul_le_mul_of_nonneg_left hyPowK.2 hbeta₀
  have hremainderIcc : remainder ∈
      Set.Icc 0 (((a : ℝ) ^ 2) * (beta * y ^ k) ^ 2) := by
    exact powerLinearizationError_mem_Icc a hx.1 hx.2 hy.2 hd₀ hxy
  have hdSqLe : (beta * y ^ k) ^ 2 ≤ beta ^ 2 := by
    nlinarith [sq_nonneg (beta * y ^ k), sq_nonneg beta]
  have hremainderUpper : remainder ≤ (ar ^ 2) * beta ^ 2 := by
    calc
      remainder ≤ ((a : ℝ) ^ 2) * (beta * y ^ k) ^ 2 :=
        hremainderIcc.2
      _ ≤ ((a : ℝ) ^ 2) * beta ^ 2 := by
        gcongr
  have htargetMul : y ^ k * y ^ (a - 1) = target := by
    rw [← pow_add]
    congr 1
    omega
  have hpower :
      x ^ a = y ^ a - ar * beta * target + remainder := by
    dsimp only [remainder, ar]
    unfold powerLinearizationError
    rw [show (a : ℝ) * (beta * y ^ k) * y ^ (a - 1) =
        (a : ℝ) * beta * target by
      rw [mul_assoc, mul_assoc, htargetMul]
      ring]
    ring
  have hcenterPow : y ^ a ≤ 1 := pow_le_one₀ hy.1 hy.2
  have hpairError₀ : 0 ≤ pairError := by
    dsimp only [pairError]
    positivity
  have hpairBound :
      pairError * (y ^ a + epsilonA) ≤
        pairError * (1 + epsilonA) :=
    mul_le_mul_of_nonneg_left (by linarith [hcenterPow]) hpairError₀
  have hLowerCharge :
      epsilonA + ar * beta * epsilonNext + ar ^ 2 * beta * eta +
          ar ^ 2 * beta ^ 2 ≤
        jointMomentStepError a k beta eta epsilonA epsilonNext := by
    simpa [ar] using lower_charge_le_jointMomentStepError a k
      hbeta₀ heta₀ hepsilonA₀
  have hUpperCharge :
      epsilonA +
          beta * (ar * collision + deficit + ar * epsilonNext) +
          pairError * (1 + epsilonA) ≤
        jointMomentStepError a k beta eta epsilonA epsilonNext := by
    simpa [ar, kr, collision, deficit, pairError] using
      upper_charge_le_jointMomentStepError a k
  have hUpperCore :
      epsilonA +
          beta * (ar * target -
            (1 - collision) * max 0 (ar - deficit) *
              max 0 (target - epsilonNext)) +
          pairError * (1 + epsilonA) ≤
        jointMomentStepError a k beta eta epsilonA epsilonNext := by
    calc
      epsilonA +
          beta * (ar * target -
            (1 - collision) * max 0 (ar - deficit) *
              max 0 (target - epsilonNext)) +
          pairError * (1 + epsilonA) ≤
        epsilonA + beta * (ar * collision + deficit + ar * epsilonNext) +
          pairError * (1 + epsilonA) := by
        gcongr
      _ ≤ jointMomentStepError a k beta eta epsilonA epsilonNext :=
        hUpperCharge
  rw [abs_le]
  constructor
  · have hlow : x ^ a -
        jointMomentStepError a k beta eta epsilonA epsilonNext ≤ next := by
      rw [hpower]
      calc
        y ^ a - ar * beta * target + remainder -
              jointMomentStepError a k beta eta epsilonA epsilonNext ≤
            y ^ a - ar * beta * target + ar ^ 2 * beta ^ 2 -
              jointMomentStepError a k beta eta epsilonA epsilonNext := by
          linarith [hremainderUpper]
        _ ≤ y ^ a - epsilonA - beta *
              (ar * (target + epsilonNext) + ar ^ 2 * eta) := by
          calc
            y ^ a - ar * beta * target + ar ^ 2 * beta ^ 2 -
                  jointMomentStepError a k beta eta epsilonA epsilonNext =
              y ^ a - epsilonA -
                  beta * (ar * (target + epsilonNext) + ar ^ 2 * eta) +
                (epsilonA + ar * beta * epsilonNext +
                  ar ^ 2 * beta * eta + ar ^ 2 * beta ^ 2 -
                    jointMomentStepError a k beta eta epsilonA epsilonNext) := by
              ring
            _ ≤ y ^ a - epsilonA -
                beta * (ar * (target + epsilonNext) + ar ^ 2 * eta) := by
              simpa only [add_le_iff_nonpos_right] using
                (sub_nonpos.mpr hLowerCharge)
        _ ≤ next := by
          simpa [ar, target] using hnext.1
    linarith
  · have hupp : next ≤ x ^ a +
        jointMomentStepError a k beta eta epsilonA epsilonNext := by
      rw [hpower]
      calc
        next ≤
            y ^ a + epsilonA -
                beta * (1 - collision) * max 0 (ar - deficit) *
                  max 0 (target - epsilonNext) +
              pairError * (y ^ a + epsilonA) := by
          simpa [ar, kr, target, deficit, collision, pairError] using hnext.2
        _ ≤ y ^ a + epsilonA -
                beta * (1 - collision) * max 0 (ar - deficit) *
                  max 0 (target - epsilonNext) +
              pairError * (1 + epsilonA) := by
          gcongr
        _ ≤ y ^ a - ar * beta * target +
              jointMomentStepError a k beta eta epsilonA epsilonNext := by
          calc
            y ^ a + epsilonA -
                  beta * (1 - collision) * max 0 (ar - deficit) *
                    max 0 (target - epsilonNext) +
                pairError * (1 + epsilonA) =
              y ^ a - ar * beta * target +
                (epsilonA + beta *
                  (ar * target -
                    (1 - collision) * max 0 (ar - deficit) *
                      max 0 (target - epsilonNext)) +
                  pairError * (1 + epsilonA)) := by ring
            _ ≤ y ^ a - ar * beta * target +
                jointMomentStepError a k beta eta epsilonA epsilonNext := by
              gcongr
        _ ≤ y ^ a - ar * beta * target + remainder +
              jointMomentStepError a k beta eta epsilonA epsilonNext := by
          linarith [hremainderIcc.1]
    linarith

/-- Discrete mean-field survival trajectory for a `k`-uniform nibble with
sampling intensity `beta / D`. -/
def meanFieldSurvival (k : ℕ) (beta : ℝ) : ℕ → ℝ
  | 0 => 1
  | r + 1 => meanFieldSurvival k beta r -
      beta * meanFieldSurvival k beta r ^ k

@[simp] lemma meanFieldSurvival_zero (k : ℕ) (beta : ℝ) :
    meanFieldSurvival k beta 0 = 1 := rfl

@[simp] lemma meanFieldSurvival_succ (k : ℕ) (beta : ℝ) (r : ℕ) :
    meanFieldSurvival k beta (r + 1) = meanFieldSurvival k beta r -
      beta * meanFieldSurvival k beta r ^ k := rfl

/-- The mean-field live probabilities telescope exactly. -/
lemma beta_mul_sum_meanFieldSurvival_pow
    (k L : ℕ) (beta : ℝ) :
    beta * (∑ r ∈ range L, meanFieldSurvival k beta r ^ k) =
      1 - meanFieldSurvival k beta L := by
  induction L with
  | zero => simp
  | succ L ih =>
      rw [sum_range_succ, mul_add, ih, meanFieldSurvival_succ]
      ring

/-- The exact accumulated lower comparison profile, with a uniform additive
error in each of the first `L` rounds. -/
lemma beta_mul_sum_meanFieldSurvival_pow_sub_const
    (k L : ℕ) (beta rho : ℝ) :
    beta * (∑ r ∈ range L, (meanFieldSurvival k beta r ^ k - rho)) =
      1 - meanFieldSurvival k beta L - beta * (L : ℝ) * rho := by
  rw [sum_sub_distrib, mul_sub, beta_mul_sum_meanFieldSurvival_pow]
  simp
  ring

/-- The exact accumulated upper comparison profile, with a uniform additive
error in each of the first `L` rounds. -/
lemma beta_mul_sum_meanFieldSurvival_pow_add_const
    (k L : ℕ) (beta rho : ℝ) :
    beta * (∑ r ∈ range L, (meanFieldSurvival k beta r ^ k + rho)) =
      1 - meanFieldSurvival k beta L + beta * (L : ℝ) * rho := by
  rw [sum_add_distrib, mul_add, beta_mul_sum_meanFieldSurvival_pow]
  simp
  ring

/-- A convenient scalar error budget for the final two-sided marginal.
The three losses are, respectively, the one-round collision loss, the
uncovered mean-field tail after `L` rounds, and the accumulated error in the
live-edge comparison.  Allocating one quarter of `zeta` to each leaves a
small amount of slack. -/
lemma meanField_marginal_scalar_budget
    {k D L : ℕ} {beta rho zeta : ℝ}
    (hD : 0 < D) (hbeta₀ : 0 ≤ beta) (hrho₀ : 0 ≤ rho)
    (hzeta₀ : 0 ≤ zeta) (hzeta₁ : zeta ≤ 1)
    (hcollision : (k : ℝ) * beta ≤ zeta / 4)
    (htail₀ : 0 ≤ meanFieldSurvival k beta L)
    (htail : meanFieldSurvival k beta L ≤ zeta / 4)
    (herror : beta * (L : ℝ) * rho ≤ zeta / 4) :
    0 ≤ beta / (D : ℝ) -
        (((k * D : ℕ) : ℝ) * (beta / (D : ℝ)) ^ 2) ∧
      (1 - zeta) / (D : ℝ) ≤
        (beta / (D : ℝ) -
          (((k * D : ℕ) : ℝ) * (beta / (D : ℝ)) ^ 2)) *
          (∑ r ∈ range L, (meanFieldSurvival k beta r ^ k - rho)) ∧
      beta / (D : ℝ) *
          (∑ r ∈ range L, (meanFieldSurvival k beta r ^ k + rho)) ≤
        (1 + zeta) / (D : ℝ) := by
  have hDreal : (0 : ℝ) < D := by exact_mod_cast hD
  have hDne : D ≠ 0 := Nat.ne_of_gt hD
  have hL₀ : (0 : ℝ) ≤ L := Nat.cast_nonneg L
  have herror₀ : 0 ≤ beta * (L : ℝ) * rho :=
    mul_nonneg (mul_nonneg hbeta₀ hL₀) hrho₀
  have hkbeta₀ : 0 ≤ (k : ℝ) * beta :=
    mul_nonneg (Nat.cast_nonneg k) hbeta₀
  have hkbeta₁ : (k : ℝ) * beta ≤ 1 := by
    calc
      (k : ℝ) * beta ≤ zeta / 4 := hcollision
      _ ≤ 1 := by linarith
  have hcoeff₀ : 0 ≤ beta * (1 - (k : ℝ) * beta) :=
    mul_nonneg hbeta₀ (sub_nonneg.mpr hkbeta₁)
  have hqeq :
      beta / (D : ℝ) -
          (((k * D : ℕ) : ℝ) * (beta / (D : ℝ)) ^ 2) =
        beta * (1 - (k : ℝ) * beta) / (D : ℝ) := by
    push_cast
    field_simp
  have hlowerNumerator :
      1 - zeta ≤
        (1 - (k : ℝ) * beta) *
          (1 - meanFieldSurvival k beta L - beta * (L : ℝ) * rho) := by
    nlinarith
  have hupperNumerator :
      1 - meanFieldSurvival k beta L + beta * (L : ℝ) * rho ≤ 1 + zeta := by
    linarith
  constructor
  · rw [hqeq]
    exact div_nonneg hcoeff₀ hDreal.le
  constructor
  · rw [hqeq]
    apply (div_le_iff₀ hDreal).2
    calc
      1 - zeta ≤ (1 - (k : ℝ) * beta) *
          (1 - meanFieldSurvival k beta L - beta * (L : ℝ) * rho) :=
        hlowerNumerator
      _ = (beta * (1 - (k : ℝ) * beta) / (D : ℝ) *
          (∑ r ∈ range L,
            (meanFieldSurvival k beta r ^ k - rho))) * (D : ℝ) := by
        rw [← beta_mul_sum_meanFieldSurvival_pow_sub_const]
        field_simp
        <;> ring
  · apply (le_div_iff₀ hDreal).2
    calc
      (beta / (D : ℝ) *
          (∑ r ∈ range L,
            (meanFieldSurvival k beta r ^ k + rho))) * (D : ℝ) =
          beta * (∑ r ∈ range L,
            (meanFieldSurvival k beta r ^ k + rho)) := by
        field_simp
      _ = 1 - meanFieldSurvival k beta L + beta * (L : ℝ) * rho :=
        beta_mul_sum_meanFieldSurvival_pow_add_const k L beta rho
      _ ≤ 1 + zeta := hupperNumerator

/-- Scaling the elementary one-round collision coefficient by `p = beta/D`
isolates the dimensionless loss `k * beta`. -/
lemma scaled_collision_coefficient
    (k D : ℕ) (beta : ℝ) (hD : D ≠ 0) :
    beta / (D : ℝ) - (((k * D : ℕ) : ℝ) * (beta / (D : ℝ)) ^ 2) =
      beta * (1 - (k : ℝ) * beta) / (D : ℝ) := by
  push_cast
  field_simp

/-- For positive uniformity and a step size in `[0,1]`, the mean-field
trajectory remains a density. -/
lemma meanFieldSurvival_mem_Icc
    {k : ℕ} (hk : 0 < k) {beta : ℝ}
    (hbeta₀ : 0 ≤ beta) (hbeta₁ : beta ≤ 1) (r : ℕ) :
    meanFieldSurvival k beta r ∈ Set.Icc (0 : ℝ) 1 := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
  induction r with
  | zero => simp
  | succ r ih =>
      let y := meanFieldSurvival (j + 1) beta r
      have hy₀ : 0 ≤ y := ih.1
      have hy₁ : y ≤ 1 := ih.2
      have hyPow₀ : 0 ≤ y ^ j := pow_nonneg hy₀ j
      have hyPow₁ : y ^ j ≤ 1 := pow_le_one₀ hy₀ hy₁
      have hbetaPow : beta * y ^ j ≤ 1 := calc
        beta * y ^ j ≤ 1 * 1 :=
          mul_le_mul hbeta₁ hyPow₁ hyPow₀ (by norm_num)
        _ = 1 := by ring
      have hdecrement : beta * y ^ (j + 1) ≤ y := calc
        beta * y ^ (j + 1) = y * (beta * y ^ j) := by
          rw [pow_succ]
          ring
        _ ≤ y * 1 := mul_le_mul_of_nonneg_left hbetaPow hy₀
        _ = y := mul_one y
      constructor
      · simpa [meanFieldSurvival_succ, y] using sub_nonneg.mpr hdecrement
      · calc
          meanFieldSurvival (j + 1) beta (r + 1) ≤ y := by
            rw [meanFieldSurvival_succ]
            exact sub_le_self y (mul_nonneg hbeta₀ (pow_nonneg hy₀ _))
          _ ≤ 1 := hy₁

/-- The mean-field survival densities decrease with the number of rounds. -/
lemma meanFieldSurvival_antitone
    {k : ℕ} (hk : 0 < k) {beta : ℝ}
    (hbeta₀ : 0 ≤ beta) (hbeta₁ : beta ≤ 1) :
    Antitone (meanFieldSurvival k beta) := by
  apply antitone_nat_of_succ_le
  intro r
  rw [meanFieldSurvival_succ]
  exact sub_le_self _ (mul_nonneg hbeta₀
    (pow_nonneg (meanFieldSurvival_mem_Icc hk hbeta₀ hbeta₁ r).1 _))

/-- With a strictly positive step size, the mean-field uncovered density
tends to zero. -/
lemma tendsto_meanFieldSurvival_zero
    {k : ℕ} (hk : 0 < k) {beta : ℝ}
    (hbeta₀ : 0 < beta) (hbeta₁ : beta ≤ 1) :
    Filter.Tendsto (meanFieldSurvival k beta) Filter.atTop (nhds 0) := by
  let y := meanFieldSurvival k beta
  have hbeta₀' : 0 ≤ beta := hbeta₀.le
  have hyIcc (r : ℕ) : y r ∈ Set.Icc (0 : ℝ) 1 :=
    meanFieldSurvival_mem_Icc hk hbeta₀' hbeta₁ r
  have hyAnti : Antitone y :=
    meanFieldSurvival_antitone hk hbeta₀' hbeta₁
  have hyBdd : BddBelow (Set.range y) := by
    refine ⟨0, ?_⟩
    rintro z ⟨r, rfl⟩
    exact hyIcc r |>.1
  let ell : ℝ := ⨅ r, y r
  have htend : Filter.Tendsto y Filter.atTop (nhds ell) :=
    tendsto_atTop_ciInf hyAnti hyBdd
  have hshift : Filter.Tendsto (fun r ↦ y (r + 1))
      Filter.atTop (nhds ell) :=
    htend.comp (Filter.tendsto_add_atTop_nat 1)
  have hrec : Filter.Tendsto (fun r ↦ y r - beta * y r ^ k)
      Filter.atTop (nhds (ell - beta * ell ^ k)) :=
    htend.sub (tendsto_const_nhds.mul (htend.pow k))
  have hshift' : Filter.Tendsto (fun r ↦ y (r + 1))
      Filter.atTop (nhds (ell - beta * ell ^ k)) := by
    simpa [y, meanFieldSurvival_succ] using hrec
  have hfixed : ell = ell - beta * ell ^ k :=
    tendsto_nhds_unique hshift hshift'
  have hpow : ell ^ k = 0 := by
    have hmul : beta * ell ^ k = 0 := by linarith
    exact (mul_eq_zero.mp hmul).resolve_left (ne_of_gt hbeta₀)
  have hell : ell = 0 := by
    by_contra hell
    exact (pow_ne_zero k hell) hpow
  simpa [hell] using htend

/-- Consequently one can stop after finitely many rounds with arbitrarily
small remaining mean-field density. -/
lemma exists_meanFieldSurvival_lt
    {k : ℕ} (hk : 0 < k) {beta epsilon : ℝ}
    (hbeta₀ : 0 < beta) (hbeta₁ : beta ≤ 1)
    (hepsilon : 0 < epsilon) :
    ∃ L : ℕ, meanFieldSurvival k beta L < epsilon := by
  have hevent : ∀ᶠ L in Filter.atTop,
      meanFieldSurvival k beta L < epsilon :=
    (tendsto_order.1 (tendsto_meanFieldSurvival_zero hk hbeta₀ hbeta₁)).2
      epsilon hepsilon
  exact hevent.exists

/-! ### Stability under the isolation-adjusted step size -/

/-- On the unit interval, the `k`th power has Lipschitz constant `k`.
This elementary form avoids importing a calculus estimate into the finite
trajectory argument. -/
lemma pow_sub_pow_le_natCast_mul_sub
    (k : ℕ) {x y : ℝ}
    (hy₀ : 0 ≤ y) (hxy : y ≤ x) (hx₁ : x ≤ 1) :
    x ^ k - y ^ k ≤ (k : ℝ) * (x - y) := by
  have hx₀ : 0 ≤ x := hy₀.trans hxy
  have hpow : y ^ k ≤ x ^ k := pow_le_pow_left₀ hy₀ hxy k
  have hxy₀ : 0 ≤ x - y := sub_nonneg.mpr hxy
  have hmax₀ : 0 ≤ max |x| |y| :=
    (abs_nonneg x).trans (le_max_left |x| |y|)
  have hmax₁ : max |x| |y| ≤ 1 := by
    apply max_le
    · rw [abs_of_nonneg hx₀]
      exact hx₁
    · rw [abs_of_nonneg hy₀]
      exact hxy.trans hx₁
  have hmaxPow : max |x| |y| ^ (k - 1) ≤ 1 :=
    pow_le_one₀ hmax₀ hmax₁
  have habs := abs_pow_sub_pow_le (a := x) (b := y) (n := k)
  rw [abs_of_nonneg (sub_nonneg.mpr hpow),
    abs_of_nonneg hxy₀] at habs
  calc
    x ^ k - y ^ k ≤
        (x - y) * (k : ℝ) * max |x| |y| ^ (k - 1) := habs
    _ ≤ (x - y) * (k : ℝ) * 1 :=
      mul_le_mul_of_nonneg_left hmaxPow
        (mul_nonneg hxy₀ (Nat.cast_nonneg k))
    _ = (k : ℝ) * (x - y) := by ring

/-- The explicit Euler map `x ↦ x - beta*x^k` is monotone on `[0,1]`
provided `beta*k ≤ 1`. -/
lemma sub_mul_pow_mono_on_Icc
    (k : ℕ) {beta x y : ℝ}
    (hbeta₀ : 0 ≤ beta) (hbetaK : beta * (k : ℝ) ≤ 1)
    (hy₀ : 0 ≤ y) (hxy : y ≤ x) (hx₁ : x ≤ 1) :
    y - beta * y ^ k ≤ x - beta * x ^ k := by
  have hpowBound := pow_sub_pow_le_natCast_mul_sub k hy₀ hxy hx₁
  have hmul : beta * (x ^ k - y ^ k) ≤ x - y := calc
    beta * (x ^ k - y ^ k) ≤
        beta * ((k : ℝ) * (x - y)) :=
      mul_le_mul_of_nonneg_left hpowBound hbeta₀
    _ = (beta * (k : ℝ)) * (x - y) := by ring
    _ ≤ 1 * (x - y) :=
      mul_le_mul_of_nonneg_right hbetaK (sub_nonneg.mpr hxy)
    _ = x - y := one_mul _
  linarith

/-- Increasing the Euler step size decreases the survival trajectory.  The
same induction gives the sharp elementary gap bound
`y_alpha(r) - y_beta(r) ≤ r * (beta-alpha)`. -/
theorem meanFieldSurvival_stepSize_order_and_gap
    {k : ℕ} (hk : 0 < k) {alpha beta : ℝ}
    (halpha₀ : 0 ≤ alpha) (halphaBeta : alpha ≤ beta)
    (hbeta₁ : beta ≤ 1) (hbetaK : beta * (k : ℝ) ≤ 1) (r : ℕ) :
    meanFieldSurvival k beta r ≤ meanFieldSurvival k alpha r ∧
      meanFieldSurvival k alpha r - meanFieldSurvival k beta r ≤
        (r : ℝ) * (beta - alpha) := by
  have hbeta₀ : 0 ≤ beta := halpha₀.trans halphaBeta
  have halpha₁ : alpha ≤ 1 := halphaBeta.trans hbeta₁
  induction r with
  | zero => simp
  | succ r ih =>
      let xa := meanFieldSurvival k alpha r
      let xb := meanFieldSurvival k beta r
      have hxaIcc : xa ∈ Set.Icc (0 : ℝ) 1 :=
        meanFieldSurvival_mem_Icc hk halpha₀ halpha₁ r
      have hxbIcc : xb ∈ Set.Icc (0 : ℝ) 1 :=
        meanFieldSurvival_mem_Icc hk hbeta₀ hbeta₁ r
      have halphaK : alpha * (k : ℝ) ≤ 1 := calc
        alpha * (k : ℝ) ≤ beta * (k : ℝ) :=
          mul_le_mul_of_nonneg_right halphaBeta (Nat.cast_nonneg k)
        _ ≤ 1 := hbetaK
      have hmap :
          xb - alpha * xb ^ k ≤ xa - alpha * xa ^ k :=
        sub_mul_pow_mono_on_Icc k halpha₀ halphaK hxbIcc.1 ih.1 hxaIcc.2
      have hsamePoint :
          xb - beta * xb ^ k ≤ xb - alpha * xb ^ k := by
        have hxbPow₀ : 0 ≤ xb ^ k := pow_nonneg hxbIcc.1 k
        exact sub_le_sub_left
          (mul_le_mul_of_nonneg_right halphaBeta hxbPow₀) xb
      have horder :
          meanFieldSurvival k beta (r + 1) ≤
            meanFieldSurvival k alpha (r + 1) := by
        simpa [meanFieldSurvival_succ, xa, xb] using hsamePoint.trans hmap
      have hpowOrder : xb ^ k ≤ xa ^ k :=
        pow_le_pow_left₀ hxbIcc.1 ih.1 k
      have hxbPow₁ : xb ^ k ≤ 1 :=
        pow_le_one₀ hxbIcc.1 hxbIcc.2
      have hgap₀ : 0 ≤ beta - alpha := sub_nonneg.mpr halphaBeta
      have hdrop₀ : 0 ≤ alpha * (xa ^ k - xb ^ k) :=
        mul_nonneg halpha₀ (sub_nonneg.mpr hpowOrder)
      have hstepGap :
          (xa - alpha * xa ^ k) - (xb - beta * xb ^ k) ≤
            (xa - xb) + (beta - alpha) := by
        have hgapMul : (beta - alpha) * xb ^ k ≤ beta - alpha := calc
          (beta - alpha) * xb ^ k ≤ (beta - alpha) * 1 :=
            mul_le_mul_of_nonneg_left hxbPow₁ hgap₀
          _ = beta - alpha := mul_one _
        nlinarith
      constructor
      · exact horder
      · calc
          meanFieldSurvival k alpha (r + 1) -
              meanFieldSurvival k beta (r + 1) ≤
              (xa - xb) + (beta - alpha) := by
            simpa [meanFieldSurvival_succ, xa, xb] using hstepGap
          _ ≤ (r : ℝ) * (beta - alpha) + (beta - alpha) :=
            by simpa [xa, xb] using
              add_le_add_right ih.2 (beta - alpha)
          _ = ((r + 1 : ℕ) : ℝ) * (beta - alpha) := by
            push_cast
            ring

/-- Bernoulli's inequality in the exact form used to bound the loss from
requiring a finite family of coordinates to be absent. -/
lemma one_sub_one_sub_pow_le_natCast_mul
    (n : ℕ) {p : ℝ} (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) :
    1 - (1 - p) ^ n ≤ (n : ℝ) * p := by
  have h := one_add_mul_sub_le_pow (a := (1 - p : ℝ)) (by linarith) n
  push_cast at h
  nlinarith

/-- Replacing `beta` by the worst-case isolated-sampling coefficient loses
at most `k*beta^2`, uniformly in the degree `D`. -/
lemma isolationAdjustedStepSize_gap_mem_Icc
    (k D : ℕ) {beta : ℝ} (hD : D ≠ 0)
    (hbeta₀ : 0 ≤ beta) (hp₁ : beta / (D : ℝ) ≤ 1) :
    beta - beta * (1 - beta / (D : ℝ)) ^ (k * D) ∈
      Set.Icc 0 ((k : ℝ) * beta ^ 2) := by
  have hDpos : 0 < (D : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero hD
  have hp₀ : 0 ≤ beta / (D : ℝ) := div_nonneg hbeta₀ hDpos.le
  have hbase₀ : 0 ≤ 1 - beta / (D : ℝ) := sub_nonneg.mpr hp₁
  have hbase₁ : 1 - beta / (D : ℝ) ≤ 1 := by linarith
  have hpow₀ : 0 ≤ (1 - beta / (D : ℝ)) ^ (k * D) :=
    pow_nonneg hbase₀ _
  have hpow₁ : (1 - beta / (D : ℝ)) ^ (k * D) ≤ 1 :=
    pow_le_one₀ hbase₀ hbase₁
  constructor
  · nlinarith [mul_le_mul_of_nonneg_left hpow₁ hbeta₀]
  · have hBernoulli :=
      one_sub_one_sub_pow_le_natCast_mul (k * D) hp₀ hp₁
    have hmul := mul_le_mul_of_nonneg_left hBernoulli hbeta₀
    push_cast at hmul
    have hDne : (D : ℝ) ≠ 0 := ne_of_gt hDpos
    field_simp [hDne] at hmul ⊢
    nlinarith

/-- The lower simultaneous-acceptance coefficient is exactly a power of
the isolation-adjusted step size after the degree scaling is factored out. -/
lemma isolationFamilyCoefficient_eq
    (j k D : ℕ) (beta : ℝ) :
    (beta / (D : ℝ)) ^ j *
        (1 - beta / (D : ℝ)) ^ (j * k * D) =
      (beta * (1 - beta / (D : ℝ)) ^ (k * D) / (D : ℝ)) ^ j := by
  calc
    (beta / (D : ℝ)) ^ j *
        (1 - beta / (D : ℝ)) ^ (j * k * D) =
        (beta / (D : ℝ)) ^ j *
          ((1 - beta / (D : ℝ)) ^ (k * D)) ^ j := by
      congr 1
      calc
        (1 - beta / (D : ℝ)) ^ (j * k * D) =
            (1 - beta / (D : ℝ)) ^ ((k * D) * j) := by
          congr 1
          ac_rfl
        _ = ((1 - beta / (D : ℝ)) ^ (k * D)) ^ j :=
          pow_mul _ _ _
    _ = ((beta / (D : ℝ)) *
          (1 - beta / (D : ℝ)) ^ (k * D)) ^ j := by
      rw [mul_pow]
    _ = (beta * (1 - beta / (D : ℝ)) ^ (k * D) / (D : ℝ)) ^ j := by
      congr 1
      ring

/-- Direct trajectory comparison for the worst-case isolated-sampling step
size.  Over `r` rounds, the collision adjustment changes the mean-field
survival density by at most `r*k*beta^2`. -/
theorem meanFieldSurvival_isolationAdjusted_order_and_gap
    {k D : ℕ} (hk : 0 < k) (hD : D ≠ 0) {beta : ℝ}
    (hbeta₀ : 0 ≤ beta) (hbeta₁ : beta ≤ 1)
    (hp₁ : beta / (D : ℝ) ≤ 1)
    (hbetaK : beta * (k : ℝ) ≤ 1) (r : ℕ) :
    let alpha := beta * (1 - beta / (D : ℝ)) ^ (k * D)
    meanFieldSurvival k beta r ≤ meanFieldSurvival k alpha r ∧
      meanFieldSurvival k alpha r - meanFieldSurvival k beta r ≤
        (r : ℝ) * ((k : ℝ) * beta ^ 2) := by
  let alpha := beta * (1 - beta / (D : ℝ)) ^ (k * D)
  have hDpos : 0 < (D : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero hD
  have hp₀ : 0 ≤ beta / (D : ℝ) := div_nonneg hbeta₀ hDpos.le
  have hbase₀ : 0 ≤ 1 - beta / (D : ℝ) := sub_nonneg.mpr hp₁
  have halpha₀ : 0 ≤ alpha := by
    exact mul_nonneg hbeta₀ (pow_nonneg hbase₀ _)
  have hgap := isolationAdjustedStepSize_gap_mem_Icc k D hD hbeta₀ hp₁
  have halphaBeta : alpha ≤ beta := by
    dsimp only [alpha]
    linarith [hgap.1]
  have htraj := meanFieldSurvival_stepSize_order_and_gap hk
    halpha₀ halphaBeta hbeta₁ hbetaK r
  constructor
  · exact htraj.1
  · calc
      meanFieldSurvival k alpha r - meanFieldSurvival k beta r ≤
          (r : ℝ) * (beta - alpha) := htraj.2
      _ ≤ (r : ℝ) * ((k : ℝ) * beta ^ 2) := by
        apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg r)
        dsimp only [alpha]
        exact hgap.2

end FiniteHypergraph

end

end Erdos76
