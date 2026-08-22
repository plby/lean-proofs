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

import ErdosProblems.Erdos1165.RenewalTail
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# Quantitative lower bounds for recurrent-renewal tails

Let `u n` be a renewal sequence, `f n` its first-return distribution, and

`G(N) = ∑_{j ≤ N} u(j)`, `F(N) = ∑_{1 ≤ j ≤ N} f(j)`.

The key finite estimate in this file is the rectangular renewal bound

`F(n) * G(m) ≤ G(n + m) - 1`.

Unlike the customary square bound with `m = n`, taking `m` much larger than
`n` makes the Green increment `G(n + m) - G(m)` small.  It follows that the
no-return mass `1 - F(n)` is bounded below by

`(1 - (G(n + m) - G(m))) / G(m)`.

The final results make the usual coefficient input explicit.  If

`u(k) = c / k + e(k)`

and the partial sums of `e` are bounded, the denominator is at most
`1 + c * (1 + log m) + E`; if the remainder changes by at most `delta`
between `m` and `m+n`, the numerator is at least
`1 - c*n/(m+1) - delta`.  This is the quantitative renewal theorem needed
for the logarithmic external-walk local-time tail.  In particular, choosing
`m = n^2` gives a positive multiple of `1 / log n` as soon as the remainder
increment tends to zero.
-/

open scoped BigOperators
open Finset

namespace Erdos1165.QuantitativeRenewal

open RenewalTail

/-! ## A rectangular finite-renewal estimate -/

private def renewalTriangle (N : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.Icc 1 N).biUnion Finset.HasAntidiagonal.antidiagonal

private lemma antidiagonal_pairwiseDisjoint (N : ℕ) :
    Set.PairwiseDisjoint (↑(Finset.Icc 1 N) : Set ℕ)
      Finset.HasAntidiagonal.antidiagonal := by
  intro i hi j hj hij
  change Disjoint (Finset.HasAntidiagonal.antidiagonal i)
    (Finset.HasAntidiagonal.antidiagonal j)
  rw [Finset.disjoint_left]
  intro p hpi hpj
  apply hij
  exact (Finset.HasAntidiagonal.mem_antidiagonal.mp hpi).symm.trans
    (Finset.HasAntidiagonal.mem_antidiagonal.mp hpj)

private lemma rectangle_subset_renewalTriangle (n m : ℕ) :
    Finset.Icc 1 n ×ˢ Finset.range (m + 1) ⊆ renewalTriangle (n + m) := by
  intro p hp
  rw [Finset.mem_product] at hp
  rcases hp with ⟨hk, hj⟩
  have hk' := Finset.mem_Icc.mp hk
  have hj' : p.2 ≤ m := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  rw [renewalTriangle, Finset.mem_biUnion]
  refine ⟨p.1 + p.2, ?_, ?_⟩
  · rw [Finset.mem_Icc]
    omega
  · exact Finset.HasAntidiagonal.mem_antidiagonal.mpr rfl

/-- The rectangular finite-renewal estimate
`F(n) G(m) ≤ G(n+m)-1`.

The earlier square estimate is the specialization `m = n`.  The asymmetric
form is what gives a sharp-order lower bound on the no-return probability:
one may take a comparison horizon `m` substantially larger than `n`. -/
theorem firstReturnMass_mul_truncatedGreen_le_add
    (f u : ℕ → ℝ)
    (hf_nonneg : ∀ k, 0 ≤ f k)
    (hu_nonneg : ∀ k, 0 ≤ u k)
    (hf_zero : f 0 = 0)
    (hu_zero : u 0 = 1)
    (hrenew : ∀ r, 0 < r →
      u r = ∑ k ∈ Finset.Icc 1 r, f k * u (r - k))
    (n m : ℕ) :
    firstReturnMass f n * truncatedGreen u m ≤
      truncatedGreen u (n + m) - 1 := by
  calc
    firstReturnMass f n * truncatedGreen u m =
        ∑ p ∈ Finset.Icc 1 n ×ˢ Finset.range (m + 1), f p.1 * u p.2 := by
      rw [firstReturnMass, truncatedGreen, Finset.sum_mul_sum, Finset.sum_product]
    _ ≤ ∑ p ∈ renewalTriangle (n + m), f p.1 * u p.2 := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
        (rectangle_subset_renewalTriangle n m)
      intro p hp hnot
      exact mul_nonneg (hf_nonneg p.1) (hu_nonneg p.2)
    _ = ∑ r ∈ Finset.Icc 1 (n + m), u r := by
      rw [renewalTriangle,
        Finset.sum_biUnion (antidiagonal_pairwiseDisjoint (n + m))]
      apply Finset.sum_congr rfl
      intro r hr
      calc
        (∑ p ∈ Finset.HasAntidiagonal.antidiagonal r, f p.1 * u p.2) =
            ∑ k ∈ Finset.range (r + 1), f k * u (r - k) :=
          Finset.Nat.sum_antidiagonal_eq_sum_range_succ
            (fun k j ↦ f k * u j) r
        _ = ∑ k ∈ Finset.Icc 1 r, f k * u (r - k) := by
          have hrange : Finset.range (r + 1) =
              insert 0 (Finset.Icc 1 r) := by
            ext k
            simp
            omega
          rw [hrange, Finset.sum_insert]
          · simp [hf_zero]
          · simp
        _ = u r := (hrenew r (Finset.mem_Icc.mp hr).1).symm
    _ = truncatedGreen u (n + m) - 1 := by
      rw [sum_Icc_one_eq_truncatedGreen_sub, hu_zero]

/-! ## No-return probability from a distant Green comparison -/

/-- The mass of seeing no positive renewal through time `n`.  For a genuine
first-return distribution this is exactly the probability of no return by
time `n`. -/
def noReturnMass (f : ℕ → ℝ) (n : ℕ) : ℝ :=
  1 - firstReturnMass f n

/-- A direct rearrangement of the rectangular renewal estimate. -/
theorem greenIncrement_div_le_noReturnMass
    (f u : ℕ → ℝ)
    (hf_nonneg : ∀ k, 0 ≤ f k)
    (hu_nonneg : ∀ k, 0 ≤ u k)
    (hf_zero : f 0 = 0)
    (hu_zero : u 0 = 1)
    (hrenew : ∀ r, 0 < r →
      u r = ∑ k ∈ Finset.Icc 1 r, f k * u (r - k))
    (n m : ℕ) :
    (1 - (truncatedGreen u (n + m) - truncatedGreen u m)) /
        truncatedGreen u m ≤ noReturnMass f n := by
  have hGpos : 0 < truncatedGreen u m :=
    lt_of_lt_of_le zero_lt_one
      (one_le_truncatedGreen hu_nonneg hu_zero m)
  apply (div_le_iff₀ hGpos).2
  have hrect := firstReturnMass_mul_truncatedGreen_le_add
    f u hf_nonneg hu_nonneg hf_zero hu_zero hrenew n m
  unfold noReturnMass
  nlinarith

/-- If the distant Green increment is at most `delta`, the no-return mass is
at least `(1-delta)/G(m)`. -/
theorem one_sub_increment_div_le_noReturnMass
    (f u : ℕ → ℝ)
    (hf_nonneg : ∀ k, 0 ≤ f k)
    (hu_nonneg : ∀ k, 0 ≤ u k)
    (hf_zero : f 0 = 0)
    (hu_zero : u 0 = 1)
    (hrenew : ∀ r, 0 < r →
      u r = ∑ k ∈ Finset.Icc 1 r, f k * u (r - k))
    (n m : ℕ) (delta : ℝ)
    (hincrement : truncatedGreen u (n + m) - truncatedGreen u m ≤ delta) :
    (1 - delta) / truncatedGreen u m ≤ noReturnMass f n := by
  have hGpos : 0 < truncatedGreen u m :=
    lt_of_lt_of_le zero_lt_one
      (one_le_truncatedGreen hu_nonneg hu_zero m)
  calc
    (1 - delta) / truncatedGreen u m ≤
        (1 - (truncatedGreen u (n + m) - truncatedGreen u m)) /
          truncatedGreen u m := by
      exact div_le_div_of_nonneg_right (sub_le_sub_left hincrement 1) hGpos.le
    _ ≤ noReturnMass f n := greenIncrement_div_le_noReturnMass
      f u hf_nonneg hu_nonneg hf_zero hu_zero hrenew n m

/-- A version in which both Green estimates have already been supplied.
This is often the cleanest interface for a local central limit theorem. -/
theorem explicit_div_le_noReturnMass_of_green_bounds
    (f u : ℕ → ℝ)
    (hf_nonneg : ∀ k, 0 ≤ f k)
    (hu_nonneg : ∀ k, 0 ≤ u k)
    (hf_zero : f 0 = 0)
    (hu_zero : u 0 = 1)
    (hrenew : ∀ r, 0 < r →
      u r = ∑ k ∈ Finset.Icc 1 r, f k * u (r - k))
    (n m : ℕ) (delta H : ℝ)
    (hdelta : delta ≤ 1)
    (hincrement : truncatedGreen u (n + m) - truncatedGreen u m ≤ delta)
    (hgreen : truncatedGreen u m ≤ H) :
    (1 - delta) / H ≤ noReturnMass f n := by
  have hGpos : 0 < truncatedGreen u m :=
    lt_of_lt_of_le zero_lt_one
      (one_le_truncatedGreen hu_nonneg hu_zero m)
  have hHpos : 0 < H := hGpos.trans_le hgreen
  calc
    (1 - delta) / H ≤ (1 - delta) / truncatedGreen u m := by
      exact div_le_div_of_nonneg_left (sub_nonneg.mpr hdelta) hGpos hgreen
    _ ≤ noReturnMass f n := one_sub_increment_div_le_noReturnMass
      f u hf_nonneg hu_nonneg hf_zero hu_zero hrenew n m delta hincrement

/-- The same estimate, arranged as the upper bound on the probability of a
return by time `n` used in geometric local-time tails. -/
theorem firstReturnMass_le_one_sub_div_of_green_bounds
    (f u : ℕ → ℝ)
    (hf_nonneg : ∀ k, 0 ≤ f k)
    (hu_nonneg : ∀ k, 0 ≤ u k)
    (hf_zero : f 0 = 0)
    (hu_zero : u 0 = 1)
    (hrenew : ∀ r, 0 < r →
      u r = ∑ k ∈ Finset.Icc 1 r, f k * u (r - k))
    (n m : ℕ) (delta H : ℝ)
    (hdelta : delta ≤ 1)
    (hincrement : truncatedGreen u (n + m) - truncatedGreen u m ≤ delta)
    (hgreen : truncatedGreen u m ≤ H) :
    firstReturnMass f n ≤ 1 - (1 - delta) / H := by
  have h := explicit_div_le_noReturnMass_of_green_bounds
    f u hf_nonneg hu_nonneg hf_zero hu_zero hrenew n m delta H
      hdelta hincrement hgreen
  unfold noReturnMass at h
  linarith

/-! ## Extracting the Green estimates from reciprocal coefficients -/

/-- The accumulated error after subtracting the principal coefficient
`c/k` from a return sequence. -/
noncomputable def reciprocalRemainderSum (u : ℕ → ℝ) (c : ℝ) (N : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc 1 N, (u k - c / (k : ℝ))

lemma truncatedGreen_eq_harmonic_add_remainder
    (u : ℕ → ℝ) (c : ℝ) (N : ℕ) (hu_zero : u 0 = 1) :
    truncatedGreen u N =
      1 + c * (harmonic N : ℝ) + reciprocalRemainderSum u c N := by
  have hpositive := sum_Icc_one_eq_truncatedGreen_sub u N
  rw [hu_zero] at hpositive
  rw [harmonic_eq_sum_Icc, reciprocalRemainderSum]
  push_cast
  calc
    truncatedGreen u N = 1 + ∑ k ∈ Finset.Icc 1 N, u k := by
      linarith
    _ = 1 + c * (∑ k ∈ Finset.Icc 1 N, (k : ℝ)⁻¹) +
          ∑ k ∈ Finset.Icc 1 N, (u k - c / (k : ℝ)) := by
      rw [Finset.mul_sum]
      have hsum :
          (∑ k ∈ Finset.Icc 1 N, u k) =
            (∑ k ∈ Finset.Icc 1 N, c * (k : ℝ)⁻¹) +
              ∑ k ∈ Finset.Icc 1 N, (u k - c / (k : ℝ)) := by
        simp_rw [div_eq_mul_inv]
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro k hk
        ring
      rw [hsum]
      ring

/-- A bounded partial sum of the coefficient remainder gives the sharp
logarithmic coefficient in the Green upper bound. -/
theorem truncatedGreen_le_log_of_remainder
    (u : ℕ → ℝ) (c E : ℝ) (N : ℕ)
    (hu_zero : u 0 = 1) (hc : 0 ≤ c)
    (hrem : reciprocalRemainderSum u c N ≤ E) :
    truncatedGreen u N ≤ 1 + c * (1 + Real.log N) + E := by
  rw [truncatedGreen_eq_harmonic_add_remainder u c N hu_zero]
  have hh : (harmonic N : ℝ) ≤ 1 + Real.log N :=
    harmonic_le_one_add_log N
  nlinarith [mul_le_mul_of_nonneg_left hh hc]

lemma truncatedGreen_add_sub (u : ℕ → ℝ) (m n : ℕ) :
    truncatedGreen u (n + m) - truncatedGreen u m =
      ∑ j ∈ Finset.range n, u (m + 1 + j) := by
  rw [truncatedGreen, truncatedGreen]
  have hadd : n + m + 1 = (m + 1) + n := by omega
  rw [hadd, Finset.sum_range_add]
  ring

lemma sum_range_reciprocal_add_le (m n : ℕ) :
    (∑ j ∈ Finset.range n, (1 : ℝ) / (m + 1 + j)) ≤
      n / (m + 1 : ℝ) := by
  calc
    (∑ j ∈ Finset.range n, (1 : ℝ) / (m + 1 + j)) ≤
        ∑ _j ∈ Finset.range n, (1 : ℝ) / (m + 1) := by
      apply Finset.sum_le_sum
      intro j hj
      have hpos : (0 : ℝ) < m + 1 := by positivity
      apply one_div_le_one_div_of_le hpos
      norm_cast
      omega
    _ = n / (m + 1 : ℝ) := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      ring

/-- The Green increment is controlled by its reciprocal main term and the
increment of the accumulated remainder. -/
theorem truncatedGreen_increment_le_of_remainder
    (u : ℕ → ℝ) (c delta : ℝ) (m n : ℕ)
    (hu_zero : u 0 = 1) (hc : 0 ≤ c)
    (hrem : reciprocalRemainderSum u c (n + m) -
      reciprocalRemainderSum u c m ≤ delta) :
    truncatedGreen u (n + m) - truncatedGreen u m ≤
      c * (n : ℝ) / (m + 1 : ℝ) + delta := by
  rw [truncatedGreen_eq_harmonic_add_remainder u c (n + m) hu_zero,
    truncatedGreen_eq_harmonic_add_remainder u c m hu_zero]
  have hharm : (harmonic (n + m) : ℝ) - harmonic m ≤
      n / (m + 1 : ℝ) := by
    rw [harmonic, harmonic]
    push_cast
    have hadd : n + m = m + n := Nat.add_comm n m
    rw [hadd, Finset.sum_range_add]
    simp only [Nat.cast_add]
    ring_nf
    convert sum_range_reciprocal_add_le m n using 1 <;> ring_nf
  calc
    1 + c * (harmonic (n + m) : ℝ) + reciprocalRemainderSum u c (n + m) -
          (1 + c * (harmonic m : ℝ) + reciprocalRemainderSum u c m) =
        c * ((harmonic (n + m) : ℝ) - harmonic m) +
          (reciprocalRemainderSum u c (n + m) - reciprocalRemainderSum u c m) := by
      ring
    _ ≤ c * (n / (m + 1 : ℝ)) + delta :=
      add_le_add (mul_le_mul_of_nonneg_left hharm hc) hrem
    _ = c * (n : ℝ) / (m + 1 : ℝ) + delta := by ring

/-- Quantitative recurrent-renewal theorem from a reciprocal coefficient
with controlled summable remainder.

The statement deliberately keeps the two finite remainder bounds explicit;
`u(k) = c/k + O(k^{-1-ε})` supplies them with bounded `E` and an increment
`delta → 0`.  Taking `m=n²` then gives the optimal logarithmic order, and
the coefficient of the denominator is the sharp coefficient `c`. -/
theorem reciprocalCoefficient_noReturn_lower
    (f u : ℕ → ℝ)
    (hf_nonneg : ∀ k, 0 ≤ f k)
    (hu_nonneg : ∀ k, 0 ≤ u k)
    (hf_zero : f 0 = 0)
    (hu_zero : u 0 = 1)
    (hrenew : ∀ r, 0 < r →
      u r = ∑ k ∈ Finset.Icc 1 r, f k * u (r - k))
    (c E delta : ℝ) (n m : ℕ)
    (hc : 0 ≤ c)
    (hrem_global : reciprocalRemainderSum u c m ≤ E)
    (hrem_increment : reciprocalRemainderSum u c (n + m) -
      reciprocalRemainderSum u c m ≤ delta)
    (hdelta : c * (n : ℝ) / (m + 1 : ℝ) + delta ≤ 1) :
    (1 - (c * (n : ℝ) / (m + 1 : ℝ) + delta)) /
        (1 + c * (1 + Real.log m) + E) ≤ noReturnMass f n := by
  apply explicit_div_le_noReturnMass_of_green_bounds
    f u hf_nonneg hu_nonneg hf_zero hu_zero hrenew n m
      (c * (n : ℝ) / (m + 1 : ℝ) + delta)
      (1 + c * (1 + Real.log m) + E) hdelta
  · exact truncatedGreen_increment_le_of_remainder
      u c delta m n hu_zero hc hrem_increment
  · exact truncatedGreen_le_log_of_remainder
      u c E m hu_zero hc hrem_global

/-- Return-by-time upper bound corresponding to
`reciprocalCoefficient_noReturn_lower`.  This is the direct input to an
excursion-by-excursion geometric-tail argument. -/
theorem reciprocalCoefficient_firstReturn_upper
    (f u : ℕ → ℝ)
    (hf_nonneg : ∀ k, 0 ≤ f k)
    (hu_nonneg : ∀ k, 0 ≤ u k)
    (hf_zero : f 0 = 0)
    (hu_zero : u 0 = 1)
    (hrenew : ∀ r, 0 < r →
      u r = ∑ k ∈ Finset.Icc 1 r, f k * u (r - k))
    (c E delta : ℝ) (n m : ℕ)
    (hc : 0 ≤ c)
    (hrem_global : reciprocalRemainderSum u c m ≤ E)
    (hrem_increment : reciprocalRemainderSum u c (n + m) -
      reciprocalRemainderSum u c m ≤ delta)
    (hdelta : c * (n : ℝ) / (m + 1 : ℝ) + delta ≤ 1) :
    firstReturnMass f n ≤
      1 - (1 - (c * (n : ℝ) / (m + 1 : ℝ) + delta)) /
        (1 + c * (1 + Real.log m) + E) := by
  have h := reciprocalCoefficient_noReturn_lower
    f u hf_nonneg hu_nonneg hf_zero hu_zero hrenew c E delta n m hc
      hrem_global hrem_increment hdelta
  unfold noReturnMass at h
  linarith

/-- The useful polynomial-horizon specialization.  With `m=n²`, the
Green increment in the numerator is `O(1/n)`, while the denominator is
`2c log n + O(1)`.  Thus this already gives a completely explicit
`constant / log n` no-return lower bound. -/
theorem reciprocalCoefficient_noReturn_lower_square
    (f u : ℕ → ℝ)
    (hf_nonneg : ∀ k, 0 ≤ f k)
    (hu_nonneg : ∀ k, 0 ≤ u k)
    (hf_zero : f 0 = 0)
    (hu_zero : u 0 = 1)
    (hrenew : ∀ r, 0 < r →
      u r = ∑ k ∈ Finset.Icc 1 r, f k * u (r - k))
    (c E delta : ℝ) (n : ℕ)
    (hc : 0 ≤ c)
    (hrem_global : reciprocalRemainderSum u c (n ^ 2) ≤ E)
    (hrem_increment : reciprocalRemainderSum u c (n + n ^ 2) -
      reciprocalRemainderSum u c (n ^ 2) ≤ delta)
    (hdelta : c * (n : ℝ) / (n ^ 2 + 1 : ℕ) + delta ≤ 1) :
    (1 - (c * (n : ℝ) / ((n ^ 2 + 1 : ℕ) : ℝ) + delta)) /
        (1 + c * (1 + Real.log ((n ^ 2 : ℕ) : ℝ)) + E) ≤
      noReturnMass f n := by
  have hdelta' : c * (n : ℝ) / ((n ^ 2 : ℕ) + 1 : ℝ) + delta ≤ 1 := by
    exact_mod_cast hdelta
  simpa only [Nat.cast_add, Nat.cast_one] using reciprocalCoefficient_noReturn_lower
    f u hf_nonneg hu_nonneg hf_zero hu_zero hrenew c E delta n (n ^ 2)
      hc hrem_global hrem_increment hdelta'

end Erdos1165.QuantitativeRenewal
