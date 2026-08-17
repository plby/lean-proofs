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

import ErdosProblems.Erdos444.PrimeBounds
import ErdosProblems.Erdos697.Erdos697Factorization
import ErdosProblems.Erdos697.Erdos697Smooth
import ErdosProblems.Erdos285.RoughCounts
import UnitFractions.AuxiliaryLemmas

/-!
# Reciprocal mass of integers with few large prime factors

This file proves the finite smooth--rough estimate used in the large-values
argument for Erdős Problem 444.  An integer is split into its part supported
on primes at most `y` and its complementary rough part.  The reciprocal mass
of all possible smooth parts is bounded by a finite Euler product.  Rough
parts with fewer than `t` distinct prime factors are bounded by the first
`t` terms of the exponential series, using exact prime-power parts.

The main estimate is deliberately finite and has no asymptotic hypotheses.
-/

open scoped ArithmeticFunction.omega BigOperators

namespace Erdos444

open Erdos285.RoughCounts
open Erdos697.Factorization

noncomputable section

attribute [local instance] Classical.propDecidable

/-- Positive members of `A` at most `X` having fewer than `t` distinct
prime factors greater than `y`. -/
def fewRoughFactorsUpTo (A : Set ℕ) (X y t : ℕ) : Finset ℕ :=
  (Finset.Icc 1 X).filter fun n ↦ n ∈ A ∧ (roughPrimes y n).card < t

@[simp] theorem mem_fewRoughFactorsUpTo
    {A : Set ℕ} {X y t n : ℕ} :
    n ∈ fewRoughFactorsUpTo A X y t ↔
      1 ≤ n ∧ n ≤ X ∧ n ∈ A ∧ (roughPrimes y n).card < t := by
  simp [fewRoughFactorsUpTo, and_assoc]

/-- The rough-prime set really counts the distinct prime factors of the
rough part. -/
theorem card_roughPrimes_eq_omega (y n : ℕ) :
    (roughPrimes y n).card = ω (roughPart y n) := by
  calc
    (roughPrimes y n).card =
        (roughPart y n).factorization.support.card := by
      rw [factorization_roughPart]
      simp [roughPrimes, roughFactorization, Finsupp.support_filter]
    _ = (roughPart y n).primeFactors.card := by
      rw [Nat.support_factorization]
    _ = ω (roughPart y n) := by
      rw [ArithmeticFunction.cardDistinctFactors_apply]
      exact Multiset.card_toFinset
        (m := ((roughPart y n).primeFactorsList : Multiset ℕ))

/-- Prime-power reciprocal mass occurring in a finite set is bounded by the
prime-power Mertens prefix at any common upper bound. -/
theorem sum_ppowersInSet_reciprocal_le_primePowerReciprocalUpTo
    {R : Finset ℕ} {X : ℕ} (hRX : ∀ r ∈ R, r ≤ X) :
    (∑ q ∈ UnitFractions.ppowers_in_set R, (1 : ℝ) / q) ≤
      primePowerReciprocalUpTo X := by
  unfold primePowerReciprocalUpTo
  simp only [one_div]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro q hq
    have hqBounds := UnitFractions.ppowers_in_set_le hRX q hq
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_Icc.mpr hqBounds,
        (UnitFractions.mem_ppowers_in_set.mp hq).1⟩
  · intro q _ _
    positivity

/-- Exact finite rough-part estimate.  This is the exponential-series half
of the smooth--rough decomposition. -/
theorem roughParts_reciprocal_le_truncatedPrimePowerExp
    {B : Finset ℕ} {X y t : ℕ}
    (hBpos : ∀ n ∈ B, 0 < n) (hBX : ∀ n ∈ B, n ≤ X)
    (hBfew : ∀ n ∈ B, (roughPrimes y n).card < t) :
    (∑ r ∈ B.image (roughPart y), (1 : ℝ) / r) ≤
      ∑ j ∈ Finset.range t,
        primePowerReciprocalUpTo X ^ j / (j.factorial : ℝ) := by
  let R : Finset ℕ := B.image (roughPart y)
  have hRpos : ∀ r ∈ R, 0 < r := by
    intro r hr
    obtain ⟨n, hnB, rfl⟩ := Finset.mem_image.mp hr
    exact roughPart_pos (hBpos n hnB)
  have hRX : ∀ r ∈ R, r ≤ X := by
    intro r hr
    obtain ⟨n, hnB, rfl⟩ := Finset.mem_image.mp hr
    exact (Nat.le_of_dvd (hBpos n hnB) (roughPart_dvd (hBpos n hnB))).trans
      (hBX n hnB)
  have hRfew : ∀ r ∈ R, ω r ∈ Finset.range t := by
    intro r hr
    obtain ⟨n, hnB, rfl⟩ := Finset.mem_image.mp hr
    rw [Finset.mem_range, ← card_roughPrimes_eq_omega]
    exact hBfew n hnB
  have hRzero : 0 ∉ R := by
    intro h0
    exact (hRpos 0 h0).ne' rfl
  let W : ℝ := ∑ q ∈ UnitFractions.ppowers_in_set R, (1 : ℝ) / q
  let H : ℝ := primePowerReciprocalUpTo X
  have hWH : W ≤ H :=
    sum_ppowersInSet_reciprocal_le_primePowerReciprocalUpTo hRX
  have hW0 : 0 ≤ W := by
    dsimp [W]
    positivity
  have hrough := UnitFractions.rec_sum_le_prod_sum hRzero hRfew
  calc
    (∑ r ∈ B.image (roughPart y), (1 : ℝ) / r) =
        (UnitFractions.rec_sum R : ℝ) := by
      simp [R, UnitFractions.rec_sum]
    _ ≤ ∑ j ∈ Finset.range t, W ^ j / (j.factorial : ℝ) := by
      simpa [W] using hrough
    _ ≤ ∑ j ∈ Finset.range t, H ^ j / (j.factorial : ℝ) := by
      apply Finset.sum_le_sum
      intro j hj
      exact div_le_div_of_nonneg_right
        (pow_le_pow_left₀ hW0 hWH j) (by positivity)
    _ = ∑ j ∈ Finset.range t,
          primePowerReciprocalUpTo X ^ j / (j.factorial : ℝ) := by
      rfl

/-- Finite few-large-prime reciprocal-mass estimate.

No property of `B` beyond positivity, the common bound `X`, and the
large-prime-factor condition is used.  This generic form lets downstream
arguments apply the estimate to a filtered prefix of an arbitrary set. -/
theorem reciprocalMass_le_smallPrimeEulerProduct_mul_truncatedPrimePowerExp
    {B : Finset ℕ} {X y t : ℕ}
    (hBpos : ∀ n ∈ B, 0 < n) (hBX : ∀ n ∈ B, n ≤ X)
    (hBfew : ∀ n ∈ B, (roughPrimes y n).card < t) :
    (∑ n ∈ B, (1 : ℝ) / n) ≤
      PrimeBounds.smallPrimeEulerProduct y *
        ∑ j ∈ Finset.range t,
          primePowerReciprocalUpTo X ^ j / (j.factorial : ℝ) := by
  let S : Finset ℕ := Erdos697.Smooth.parts y X
  let R : Finset ℕ := B.image (roughPart y)
  let P : Finset (ℕ × ℕ) :=
    B.image fun n ↦ (smallPart y n, roughPart y n)
  have hpairInj : Set.InjOn
      (fun n ↦ (smallPart y n, roughPart y n)) (B : Set ℕ) := by
    intro a ha b hb hab
    have ha0 := (hBpos a ha).ne'
    have hb0 := (hBpos b hb).ne'
    have hprod := congrArg (fun z : ℕ × ℕ ↦ z.1 * z.2) hab
    simpa [smallPart_mul_roughPart ha0, smallPart_mul_roughPart hb0] using hprod
  have hPsub : P ⊆ S.product R := by
    intro z hz
    obtain ⟨n, hnB, rfl⟩ := Finset.mem_image.mp hz
    have hnpos := hBpos n hnB
    have hspos := smallPart_pos (R := y) hnpos
    have hsdvd := smallPart_dvd (R := y) hnpos
    have hsX : smallPart y n ≤ X :=
      (Nat.le_of_dvd hnpos hsdvd).trans (hBX n hnB)
    refine Finset.mem_product.mpr ⟨?_, Finset.mem_image.mpr ⟨n, hnB, rfl⟩⟩
    exact Erdos697.Smooth.mem_parts.mpr
      ⟨hspos, hsX, smallPart_smooth hnpos⟩
  have hsumPairs :
      (∑ n ∈ B, (1 : ℝ) / n) =
        ∑ z ∈ P, ((1 : ℝ) / z.1) * ((1 : ℝ) / z.2) := by
    change (∑ n ∈ B, (1 : ℝ) / n) =
      ∑ z ∈ B.image (fun n ↦ (smallPart y n, roughPart y n)),
        ((1 : ℝ) / z.1) * ((1 : ℝ) / z.2)
    rw [Finset.sum_image]
    · apply Finset.sum_congr rfl
      intro n hn
      have hnpos := hBpos n hn
      rw [one_div_mul_one_div, ← Nat.cast_mul,
        smallPart_mul_roughPart hnpos.ne']
    · intro a ha b hb hab
      exact hpairInj ha hb hab
  have hnonneg : ∀ z ∈ S.product R,
      z ∉ P → 0 ≤ ((1 : ℝ) / z.1) * ((1 : ℝ) / z.2) := by
    intro z hzP hz
    positivity
  have hrough :
      (∑ r ∈ R, (1 : ℝ) / r) ≤
        ∑ j ∈ Finset.range t,
          primePowerReciprocalUpTo X ^ j / (j.factorial : ℝ) := by
    exact roughParts_reciprocal_le_truncatedPrimePowerExp hBpos hBX hBfew
  have hsmooth :
      (∑ s ∈ S, (1 : ℝ) / s) ≤
        PrimeBounds.smallPrimeEulerProduct y := by
    simpa [S, PrimeBounds.smallPrimeEulerProduct, Nat.primesLE] using
      Erdos697.Smooth.sum_parts_reciprocal_le_euler y X
  calc
    (∑ n ∈ B, (1 : ℝ) / n) =
        ∑ z ∈ P, ((1 : ℝ) / z.1) * ((1 : ℝ) / z.2) := hsumPairs
    _ ≤ ∑ z ∈ S.product R,
          ((1 : ℝ) / z.1) * ((1 : ℝ) / z.2) :=
      Finset.sum_le_sum_of_subset_of_nonneg hPsub hnonneg
    _ = (∑ s ∈ S, (1 : ℝ) / s) *
          (∑ r ∈ R, (1 : ℝ) / r) := by
      rw [Finset.product_eq_sprod,
        Finset.sum_product S R
          (fun z ↦ ((1 : ℝ) / z.1) * ((1 : ℝ) / z.2)),
        Finset.sum_mul]
      congr 1
      funext s
      rw [Finset.mul_sum]
    _ ≤ PrimeBounds.smallPrimeEulerProduct y *
          (∑ j ∈ Finset.range t,
            primePowerReciprocalUpTo X ^ j / (j.factorial : ℝ)) := by
      apply mul_le_mul hsmooth hrough
      · exact Finset.sum_nonneg fun _ _ ↦ by positivity
      · exact (Finset.sum_nonneg fun _ _ ↦ by positivity).trans hsmooth

/-- Set-prefix specialization of the generic finite estimate. -/
theorem fewRoughFactorsUpTo_reciprocalMass_le
    (A : Set ℕ) (X y t : ℕ) :
    (∑ n ∈ fewRoughFactorsUpTo A X y t, (1 : ℝ) / n) ≤
      PrimeBounds.smallPrimeEulerProduct y *
        ∑ j ∈ Finset.range t,
          primePowerReciprocalUpTo X ^ j / (j.factorial : ℝ) := by
  apply reciprocalMass_le_smallPrimeEulerProduct_mul_truncatedPrimePowerExp
  · intro n hn
    exact (mem_fewRoughFactorsUpTo.mp hn).1
  · intro n hn
    exact (mem_fewRoughFactorsUpTo.mp hn).2.1
  · intro n hn
    exact (mem_fewRoughFactorsUpTo.mp hn).2.2.2

end

end Erdos444
