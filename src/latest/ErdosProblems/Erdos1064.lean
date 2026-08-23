/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- Original license: Apache 2.0. Note: This file has been modified. -/
/-
This is a Lean formalization of a solution to Erdős Problem 1064.
https://www.erdosproblems.com/forum/thread/1064

Informal authors:
- Florian Luca
- Carl Pomerance

Statement authors:
- Formal Conjectures authors

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos1064.md
- https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/1064.lean
-/
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
import ErdosProblems.Erdos285.RoughCounts
import ErdosProblems.Erdos459
import Util.Density
import Util.Primes
import Util.Prod

/-!
# Erdős Problem 1064

This file proves the density-one inequality
`φ n > φ (n - φ n)`, its strengthening by every natural-valued `o(n)` error,
and the infinitude of the reverse inequality.

The density proof uses finite first-moment estimates for reciprocal prime-factor
mass and the divergence of reciprocal primes in a reduced residue class.
-/

open Nat Filter Topology Set Real
open scoped BigOperators

namespace Erdos1064

noncomputable section

def reciprocalPrimeMass (n : ℕ) : ℝ :=
  ∑ p ∈ n.primeFactors, (p : ℝ)⁻¹

def largeReciprocalPrimeMass (B n : ℕ) : ℝ :=
  ∑ p ∈ n.primeFactors.filter (B < ·), (p : ℝ)⁻¹

lemma totient_ratio_eq {n : ℕ} (hn : n ≠ 0) :
    (Nat.totient n : ℝ) / n =
      ∏ p ∈ n.primeFactors, (1 - (p : ℝ)⁻¹) := by
  have hq := Nat.totient_eq_mul_prod_factors n
  have hr : (Nat.totient n : ℝ) =
      n * ∏ p ∈ n.primeFactors, (1 - (p : ℝ)⁻¹) := by
    have := congrArg (fun x : ℚ ↦ (x : ℝ)) hq
    simpa using this
  rw [hr]
  field_simp

lemma exp_neg_two_mul_le_one_sub {x : ℝ} (hx0 : 0 ≤ x) (hx2 : x ≤ 1 / 2) :
    Real.exp (-2 * x) ≤ 1 - x := by
  have hsub : 0 < 1 - x := by linarith
  have hinv : (1 - x)⁻¹ ≤ 1 + 2 * x := by
    rw [inv_eq_one_div, div_le_iff₀ hsub]
    nlinarith [mul_nonneg hx0 (sub_nonneg.mpr (by linarith : 0 ≤ 1 - 2 * x))]
  have hexp : 1 + 2 * x ≤ Real.exp (2 * x) := by
    simpa [add_comm] using Real.add_one_le_exp (2 * x)
  have hmain : (1 - x)⁻¹ ≤ Real.exp (2 * x) := hinv.trans hexp
  rw [show -2 * x = -(2 * x) by ring, Real.exp_neg]
  have hposinv : 0 < (1 - x)⁻¹ := inv_pos.mpr hsub
  have := (inv_le_inv₀ (Real.exp_pos (2 * x)) hposinv).2 hmain
  simpa [inv_inv] using this

lemma exp_mass_le_totient_ratio {n : ℕ} (hn : n ≠ 0) :
    Real.exp (-2 * reciprocalPrimeMass n) ≤ (Nat.totient n : ℝ) / n := by
  rw [totient_ratio_eq hn, reciprocalPrimeMass, Finset.mul_sum, Real.exp_sum]
  apply Finset.prod_le_prod
  · intro p hp
    positivity
  · intro p hp
    have hpprime := Nat.prime_of_mem_primeFactors hp
    have hp0 : (0 : ℝ) ≤ (p : ℝ)⁻¹ := by positivity
    have hp2 : (p : ℝ)⁻¹ ≤ 1 / 2 := by
      simpa [one_div] using
        (inv_le_inv₀ (by exact_mod_cast hpprime.pos : (0 : ℝ) < p)
          (by norm_num : (0 : ℝ) < 2)).2
          (by exact_mod_cast hpprime.two_le : (2 : ℝ) ≤ p)
    simpa [mul_inv_rev, mul_comm] using exp_neg_two_mul_le_one_sub hp0 hp2

lemma sum_reciprocalPrimeMass_range_le (N : ℕ) :
    ∑ n ∈ Finset.range N, reciprocalPrimeMass n ≤ (N : ℝ) := by
  by_cases hN : N = 0
  · simp [hN]
  have hNpos : 0 < N := Nat.pos_of_ne_zero hN
  have hpoint : ∀ n ∈ Finset.range N,
      reciprocalPrimeMass n ≤
        ∑ p ∈ Finset.Icc 2 (N - 1),
          if n ≠ 0 ∧ p ∣ n then (p : ℝ)⁻¹ else 0 := by
    intro n hn
    rw [reciprocalPrimeMass]
    have hsub : n.primeFactors ⊆ Finset.Icc 2 (N - 1) := by
      intro p hp
      have hpprime := Nat.prime_of_mem_primeFactors hp
      have hpn := Nat.le_of_mem_primeFactors hp
      have hnN := Finset.mem_range.mp hn
      exact Finset.mem_Icc.mpr ⟨hpprime.two_le, by omega⟩
    calc
      (∑ p ∈ n.primeFactors, (p : ℝ)⁻¹) =
          ∑ p ∈ n.primeFactors,
            if n ≠ 0 ∧ p ∣ n then (p : ℝ)⁻¹ else 0 := by
              apply Finset.sum_congr rfl
              intro p hp
              simp [Nat.mem_primeFactors.mp hp]
      _ ≤ ∑ p ∈ Finset.Icc 2 (N - 1),
            if n ≠ 0 ∧ p ∣ n then (p : ℝ)⁻¹ else 0 := by
              apply Finset.sum_le_sum_of_subset_of_nonneg hsub
              intro p hpI hpnot
              split_ifs <;> positivity
  calc
    ∑ n ∈ Finset.range N, reciprocalPrimeMass n ≤
        ∑ n ∈ Finset.range N,
          ∑ p ∈ Finset.Icc 2 (N - 1),
            if n ≠ 0 ∧ p ∣ n then (p : ℝ)⁻¹ else 0 :=
      Finset.sum_le_sum fun n hn ↦ hpoint n hn
    _ = ∑ p ∈ Finset.Icc 2 (N - 1),
          ∑ n ∈ Finset.range N,
            if n ≠ 0 ∧ p ∣ n then (p : ℝ)⁻¹ else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ p ∈ Finset.Icc 2 (N - 1),
          (((N - 1) / p : ℕ) : ℝ) * (p : ℝ)⁻¹ := by
      apply Finset.sum_congr rfl
      intro p hp
      calc
        ∑ n ∈ Finset.range N,
              (if n ≠ 0 ∧ p ∣ n then (p : ℝ)⁻¹ else 0) =
            (((Finset.range N).filter (fun n ↦ n ≠ 0 ∧ p ∣ n)).card : ℝ) *
              (p : ℝ)⁻¹ := by
          rw [← Finset.sum_boole (R := ℝ) (fun n ↦ n ≠ 0 ∧ p ∣ n) (Finset.range N),
            Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro n hn
          split_ifs <;> simp
        _ = (((N - 1) / p : ℕ) : ℝ) * (p : ℝ)⁻¹ := by
          congr 1
          have hrange : Finset.range N = Finset.range (N - 1).succ := by
            congr 1
            omega
          rw [hrange]
          exact_mod_cast Nat.card_multiples' (N - 1) p
    _ ≤ ∑ p ∈ Finset.Icc 2 (N - 1),
          (N : ℝ) * ((p : ℝ) ^ 2)⁻¹ := by
      apply Finset.sum_le_sum
      intro p hp
      have hp2 : 2 ≤ p := (Finset.mem_Icc.mp hp).1
      have hpR : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
      have hfloor : (((N - 1) / p : ℕ) : ℝ) ≤ (N : ℝ) / p := by
        calc
          (((N - 1) / p : ℕ) : ℝ) ≤ ((N - 1 : ℕ) : ℝ) / p :=
            Nat.cast_div_le
          _ ≤ (N : ℝ) / p := by gcongr; omega
      calc
        (((N - 1) / p : ℕ) : ℝ) * (p : ℝ)⁻¹ ≤
            ((N : ℝ) / p) * (p : ℝ)⁻¹ :=
          mul_le_mul_of_nonneg_right hfloor (by positivity)
        _ = (N : ℝ) * ((p : ℝ) ^ 2)⁻¹ := by
          field_simp
    _ = (N : ℝ) *
          ∑ p ∈ Finset.Icc 2 (N - 1), ((p : ℝ) ^ 2)⁻¹ := by
      rw [Finset.mul_sum]
    _ ≤ (N : ℝ) * 1 := by
      gcongr
      simpa using
        Erdos285.RoughCounts.sum_Icc_inv_sq_le_inv 1 (N - 1) (by norm_num)
    _ = (N : ℝ) := by ring

lemma sum_largeReciprocalPrimeMass_range_le (B N : ℕ) (hB : 1 ≤ B) :
    ∑ n ∈ Finset.range N, largeReciprocalPrimeMass B n ≤ (N : ℝ) / B := by
  by_cases hN : N = 0
  · simp [hN]
  have hNpos : 0 < N := Nat.pos_of_ne_zero hN
  have hpoint : ∀ n ∈ Finset.range N,
      largeReciprocalPrimeMass B n ≤
        ∑ p ∈ Finset.Icc (B + 1) (N - 1),
          if n ≠ 0 ∧ p ∣ n then (p : ℝ)⁻¹ else 0 := by
    intro n hn
    rw [largeReciprocalPrimeMass]
    have hsub : n.primeFactors.filter (B < ·) ⊆ Finset.Icc (B + 1) (N - 1) := by
      intro p hp
      have hpdata := Finset.mem_filter.mp hp
      have hpn := Nat.le_of_mem_primeFactors hpdata.1
      have hnN := Finset.mem_range.mp hn
      exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    calc
      (∑ p ∈ n.primeFactors.filter (B < ·), (p : ℝ)⁻¹) =
          ∑ p ∈ n.primeFactors.filter (B < ·),
            if n ≠ 0 ∧ p ∣ n then (p : ℝ)⁻¹ else 0 := by
              apply Finset.sum_congr rfl
              intro p hp
              have hp' := (Finset.mem_filter.mp hp).1
              simp [Nat.mem_primeFactors.mp hp']
      _ ≤ ∑ p ∈ Finset.Icc (B + 1) (N - 1),
            if n ≠ 0 ∧ p ∣ n then (p : ℝ)⁻¹ else 0 := by
              apply Finset.sum_le_sum_of_subset_of_nonneg hsub
              intro p hpI hpnot
              split_ifs <;> positivity
  calc
    ∑ n ∈ Finset.range N, largeReciprocalPrimeMass B n ≤
        ∑ n ∈ Finset.range N,
          ∑ p ∈ Finset.Icc (B + 1) (N - 1),
            if n ≠ 0 ∧ p ∣ n then (p : ℝ)⁻¹ else 0 :=
      Finset.sum_le_sum fun n hn ↦ hpoint n hn
    _ = ∑ p ∈ Finset.Icc (B + 1) (N - 1),
          ∑ n ∈ Finset.range N,
            if n ≠ 0 ∧ p ∣ n then (p : ℝ)⁻¹ else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ p ∈ Finset.Icc (B + 1) (N - 1),
          (((N - 1) / p : ℕ) : ℝ) * (p : ℝ)⁻¹ := by
      apply Finset.sum_congr rfl
      intro p hp
      calc
        ∑ n ∈ Finset.range N,
              (if n ≠ 0 ∧ p ∣ n then (p : ℝ)⁻¹ else 0) =
            (((Finset.range N).filter (fun n ↦ n ≠ 0 ∧ p ∣ n)).card : ℝ) *
              (p : ℝ)⁻¹ := by
          rw [← Finset.sum_boole (R := ℝ) (fun n ↦ n ≠ 0 ∧ p ∣ n) (Finset.range N),
            Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro n hn
          split_ifs <;> simp
        _ = (((N - 1) / p : ℕ) : ℝ) * (p : ℝ)⁻¹ := by
          congr 1
          have hrange : Finset.range N = Finset.range (N - 1).succ := by
            congr 1
            omega
          rw [hrange]
          exact_mod_cast Nat.card_multiples' (N - 1) p
    _ ≤ ∑ p ∈ Finset.Icc (B + 1) (N - 1),
          (N : ℝ) * ((p : ℝ) ^ 2)⁻¹ := by
      apply Finset.sum_le_sum
      intro p hp
      have hpB : B + 1 ≤ p := (Finset.mem_Icc.mp hp).1
      have hpR : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
      have hfloor : (((N - 1) / p : ℕ) : ℝ) ≤ (N : ℝ) / p := by
        calc
          (((N - 1) / p : ℕ) : ℝ) ≤ ((N - 1 : ℕ) : ℝ) / p :=
            Nat.cast_div_le
          _ ≤ (N : ℝ) / p := by gcongr; omega
      calc
        (((N - 1) / p : ℕ) : ℝ) * (p : ℝ)⁻¹ ≤
            ((N : ℝ) / p) * (p : ℝ)⁻¹ :=
          mul_le_mul_of_nonneg_right hfloor (by positivity)
        _ = (N : ℝ) * ((p : ℝ) ^ 2)⁻¹ := by field_simp
    _ = (N : ℝ) *
          ∑ p ∈ Finset.Icc (B + 1) (N - 1), ((p : ℝ) ^ 2)⁻¹ := by
      rw [Finset.mul_sum]
    _ ≤ (N : ℝ) * (B : ℝ)⁻¹ := by
      gcongr
      exact Erdos285.RoughCounts.sum_Icc_inv_sq_le_inv B (N - 1) hB
    _ = (N : ℝ) / B := by rw [div_eq_mul_inv]

lemma card_mul_le_sum_of_le
    {s : Finset ℕ} {P : ℕ → Prop} [DecidablePred P]
    {w : ℕ → ℝ} {t : ℝ}
    (hw : ∀ n ∈ s, 0 ≤ w n) (hP : ∀ n ∈ s, P n → t ≤ w n) :
    (((s.filter P).card : ℝ) * t) ≤ ∑ n ∈ s, w n := by
  calc
    (((s.filter P).card : ℝ) * t) = ∑ n ∈ s.filter P, t := by simp
    _ ≤ ∑ n ∈ s.filter P, w n :=
      Finset.sum_le_sum fun n hn ↦ hP n (Finset.mem_filter.mp hn).1 (Finset.mem_filter.mp hn).2
    _ ≤ ∑ n ∈ s, w n := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset P s)
      intro n hns hnP
      exact hw n hns

lemma small_totient_ratio_count (T : ℝ) (hT : 0 < T) (N : ℕ) :
    (((Finset.range N).filter (fun n ↦
      n ≠ 0 ∧ (Nat.totient n : ℝ) / n < Real.exp (-T))).card : ℝ) /
        N ≤ 2 / T := by
  by_cases hN : N = 0
  · simp [hN]
    positivity
  have hNpos : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
  have hmarkov :
      (((Finset.range N).filter (fun n ↦
        n ≠ 0 ∧ (Nat.totient n : ℝ) / n < Real.exp (-T))).card : ℝ) *
          (T / 2) ≤ ∑ n ∈ Finset.range N, reciprocalPrimeMass n := by
    apply card_mul_le_sum_of_le
    · intro n hn
      exact Finset.sum_nonneg fun p hp ↦ by positivity
    · intro n hn hnsmall
      have hexp : Real.exp (-2 * reciprocalPrimeMass n) < Real.exp (-T) :=
        (exp_mass_le_totient_ratio hnsmall.1).trans_lt hnsmall.2
      rw [Real.exp_lt_exp] at hexp
      linarith
  have hbound :
      (((Finset.range N).filter (fun n ↦
        n ≠ 0 ∧ (Nat.totient n : ℝ) / n < Real.exp (-T))).card : ℝ) *
          (T / 2) ≤ (N : ℝ) :=
    hmarkov.trans (sum_reciprocalPrimeMass_range_le N)
  apply (div_le_iff₀ hNpos).2
  have hc :
      (((Finset.range N).filter (fun n ↦
        n ≠ 0 ∧ (Nat.totient n : ℝ) / n < Real.exp (-T))).card : ℝ) ≤
          2 * (N : ℝ) / T := by
    apply (le_div_iff₀ hT).2
    nlinarith
  calc
    (((Finset.range N).filter (fun n ↦
      n ≠ 0 ∧ (Nat.totient n : ℝ) / n < Real.exp (-T))).card : ℝ) ≤
        2 * (N : ℝ) / T := hc
    _ = 2 / T * (N : ℝ) := by ring

lemma large_tail_count (B N : ℕ) (hB : 1 ≤ B) (δ : ℝ) (hδ : 0 < δ) :
    (((Finset.range N).filter (fun n ↦
      δ / 2 ≤ largeReciprocalPrimeMass B n)).card : ℝ) / N ≤
        2 / ((B : ℝ) * δ) := by
  by_cases hN : N = 0
  · simp [hN]
    positivity
  have hNpos : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
  have hmarkov :
      (((Finset.range N).filter (fun n ↦
        δ / 2 ≤ largeReciprocalPrimeMass B n)).card : ℝ) * (δ / 2) ≤
          ∑ n ∈ Finset.range N, largeReciprocalPrimeMass B n := by
    apply card_mul_le_sum_of_le
    · intro n hn
      exact Finset.sum_nonneg fun p hp ↦ by positivity
    · intro n hn hnlarge
      exact hnlarge
  have hbound := hmarkov.trans (sum_largeReciprocalPrimeMass_range_le B N hB)
  have hBR : (0 : ℝ) < B := by exact_mod_cast (show 0 < B by omega)
  apply (div_le_iff₀ hNpos).2
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ (mul_pos hBR hδ)).2
  field_simp at hbound ⊢
  nlinarith

lemma hasDensity_of_has_natural_density (S : Set ℕ) (d : ℝ)
    (h : Erdos459.has_natural_density S d) : S.HasDensity d := by
  classical
  rw [Set.HasDensity]
  rw [Erdos459.has_natural_density] at h
  exact h.congr' (Filter.Eventually.of_forall fun n ↦ by
    simp only [Set.partialDensity, Set.inter_univ, Set.univ_inter,
      Set.ncard_Iio_nat]
    have hcard : (S ∩ Set.Iio n).ncard =
        ((Finset.range n).filter fun m ↦ m ∈ S).card := by
      rw [Set.ncard_eq_toFinset_card _
        ((Set.finite_Iio n).subset Set.inter_subset_right)]
      congr 1
      ext m
      simp [and_comm]
    rw [hcard])

lemma hasDensity_one_of_compl_ratio_tendsto_zero (S : Set ℕ)
    (h : Tendsto
      (fun N : ℕ ↦ (((Sᶜ ∩ Set.Iio N).ncard : ℕ) : ℝ) / N)
      atTop (nhds 0)) :
    S.HasDensity 1 := by
  rw [Set.HasDensity]
  have ht : Tendsto
      (fun N : ℕ ↦ (1 : ℝ) - (((Sᶜ ∩ Set.Iio N).ncard : ℕ) : ℝ) / N)
      atTop (nhds ((1 : ℝ) - 0)) := tendsto_const_nhds.sub h
  simpa only [sub_zero] using ht.congr' (by
    filter_upwards [eventually_gt_atTop 0] with N hN
    simp only [Set.partialDensity, Set.inter_univ, Set.univ_inter,
      Set.ncard_Iio_nat]
    have hdisj : Disjoint (S ∩ Set.Iio N) (Sᶜ ∩ Set.Iio N) := by
      exact Set.disjoint_left.mpr fun x hxS hxC ↦ hxC.1 hxS.1
    have hunion : (S ∩ Set.Iio N) ∪ (Sᶜ ∩ Set.Iio N) = Set.Iio N := by
      ext x
      by_cases hx : x ∈ S <;> simp [hx]
    have hcard : (S ∩ Set.Iio N).ncard + (Sᶜ ∩ Set.Iio N).ncard = N := by
      rw [← Set.ncard_union_eq hdisj, hunion]
      simp
    have hcardR : ((S ∩ Set.Iio N).ncard : ℝ) +
        ((Sᶜ ∩ Set.Iio N).ncard : ℝ) = (N : ℝ) := by
      exact_mod_cast hcard
    have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
    field_simp
    linarith [hcardR])

def residuePrimes (q K : ℕ) : Finset ℕ :=
  (Finset.range K).filter fun p ↦ p.Prime ∧ (p : ZMod q) = 1

lemma avoidance_product_le_exp (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    (∏ p ∈ P, (1 - (p : ℝ)⁻¹)) ≤
      Real.exp (-∑ p ∈ P, (p : ℝ)⁻¹) := by
  rw [← Finset.sum_neg_distrib, Real.exp_sum]
  apply Finset.prod_le_prod
  · intro p hp
    have hpprime := hP p hp
    have hp2R : (2 : ℝ) ≤ p := by exact_mod_cast hpprime.two_le
    have hpinv : (p : ℝ)⁻¹ ≤ 1 := by
      have hpR : (1 : ℝ) ≤ p := hp2R.trans' (by norm_num)
      exact inv_le_one_of_one_le₀ hpR
    positivity
  · intro p hp
    simpa using Real.one_sub_le_exp_neg ((p : ℝ)⁻¹)

lemma prime_dvd_totient_hasDensity_one (q : ℕ) (hq : q.Prime) :
    {n : ℕ | q ∣ Nat.totient n}.HasDensity 1 := by
  classical
  let : NeZero q := ⟨hq.ne_zero⟩
  have hnonsum := Nat.Primes.residue_reciprocals_not_summable
    q (1 : ZMod q) isUnit_one
  have hdiv0 : Tendsto
      (fun K : ℕ ↦ ∑ p ∈ Finset.range K,
        if p.Prime ∧ (p : ZMod q) = 1 then (1 : ℝ) / p else 0)
      atTop atTop :=
    (not_summable_iff_tendsto_nat_atTop_of_nonneg (fun p ↦ by
      split_ifs <;> positivity)).mp hnonsum
  have hdiv : Tendsto
      (fun K : ℕ ↦ ∑ p ∈ residuePrimes q K, (p : ℝ)⁻¹)
      atTop atTop := by
    convert hdiv0 using 1
    funext K
    simp [residuePrimes, Finset.sum_filter, one_div]
  have hexp : Tendsto
      (fun K : ℕ ↦ Real.exp (-∑ p ∈ residuePrimes q K, (p : ℝ)⁻¹))
      atTop (nhds 0) := Real.tendsto_exp_neg_atTop_nhds_zero.comp hdiv
  apply hasDensity_one_of_compl_ratio_tendsto_zero
  rw [Metric.tendsto_atTop]
  intro ε hε
  have heventExp := hexp.eventually (Iio_mem_nhds hε)
  obtain ⟨K, hK⟩ := Filter.eventually_atTop.mp heventExp
  let P := residuePrimes q K
  let d : ℝ := ∏ p ∈ P, (1 - (p : ℝ)⁻¹)
  let A : Set ℕ := {n | ∀ p ∈ P, ¬ p ∣ n}
  have hP : ∀ p ∈ P, p.Prime := by
    intro p hp
    exact (Finset.mem_filter.mp hp).2.1
  have hdlt : d < ε := by
    exact (avoidance_product_le_exp P hP).trans_lt (hK K le_rfl)
  have hAdensity : A.HasDensity d := by
    apply hasDensity_of_has_natural_density
    simpa [A, d, one_div] using Erdos459.density_no_prime P hP
  rw [Set.HasDensity] at hAdensity
  have hAevent : ∀ᶠ N : ℕ in atTop, A.partialDensity Set.univ N < ε :=
    hAdensity.eventually (Iio_mem_nhds hdlt)
  rw [Filter.eventually_atTop] at hAevent
  obtain ⟨N₀, hN₀⟩ := hAevent
  refine ⟨N₀, fun N hNN₀ ↦ ?_⟩
  have hsubset : ({n : ℕ | q ∣ Nat.totient n}ᶜ ∩ Set.Iio N) ⊆ A ∩ Set.Iio N := by
    rintro n ⟨hnq, hnN⟩
    refine ⟨?_, hnN⟩
    intro p hpP hpn
    have hpdata := (Finset.mem_filter.mp hpP).2
    have hpprime : p.Prime := hpdata.1
    have hpmod : p ≡ 1 [MOD q] :=
      (ZMod.natCast_eq_natCast_iff p 1 q).mp (by simpa using hpdata.2)
    have hqpred : q ∣ p - 1 := hpmod.symm.dvd'
    have hqphiP : q ∣ Nat.totient p := by
      simpa [Nat.totient_prime hpprime] using hqpred
    have hphiPphiN : Nat.totient p ∣ Nat.totient n :=
      Nat.totient_dvd_of_dvd hpn
    exact hnq (hqphiP.trans hphiPphiN)
  have hcard : (({n : ℕ | q ∣ Nat.totient n}ᶜ ∩ Set.Iio N).ncard : ℝ) ≤
      ((A ∩ Set.Iio N).ncard : ℝ) := by
    exact_mod_cast Set.ncard_le_ncard hsubset
      ((Set.finite_Iio N).subset Set.inter_subset_right)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)]
  calc
    (({n : ℕ | q ∣ Nat.totient n}ᶜ ∩ Set.Iio N).ncard : ℝ) / N ≤
        ((A ∩ Set.Iio N).ncard : ℝ) / N :=
      div_le_div_of_nonneg_right hcard (by positivity)
    _ = A.partialDensity Set.univ N := by
      simp [Set.partialDensity]
    _ < ε := hN₀ N hNN₀

lemma compl_ratio_tendsto_zero_of_hasDensity_one (S : Set ℕ)
    (h : S.HasDensity 1) :
    Tendsto (fun N : ℕ ↦ ((Sᶜ ∩ Set.Iio N).ncard : ℝ) / N)
      atTop (nhds 0) := by
  rw [Set.HasDensity] at h
  have ht : Tendsto (fun N : ℕ ↦ (1 : ℝ) - S.partialDensity Set.univ N)
      atTop (nhds ((1 : ℝ) - 1)) := tendsto_const_nhds.sub h
  simpa only [sub_self] using ht.congr' (by
    filter_upwards [eventually_gt_atTop 0] with N hN
    simp only [Set.partialDensity, Set.inter_univ, Set.univ_inter,
      Set.ncard_Iio_nat]
    have hdisj : Disjoint (S ∩ Set.Iio N) (Sᶜ ∩ Set.Iio N) := by
      exact Set.disjoint_left.mpr fun x hxS hxC ↦ hxC.1 hxS.1
    have hunion : (S ∩ Set.Iio N) ∪ (Sᶜ ∩ Set.Iio N) = Set.Iio N := by
      ext x
      by_cases hx : x ∈ S <;> simp [hx]
    have hcard : (S ∩ Set.Iio N).ncard + (Sᶜ ∩ Set.Iio N).ncard = N := by
      rw [← Set.ncard_union_eq hdisj, hunion]
      simp
    have hcardR : ((S ∩ Set.Iio N).ncard : ℝ) +
        ((Sᶜ ∩ Set.Iio N).ncard : ℝ) = (N : ℝ) := by
      exact_mod_cast hcard
    have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
    field_simp
    linarith [hcardR])

def smallPrimesDivideTotient (B : ℕ) : Set ℕ :=
  {n | ∀ q ∈ (Finset.range (B + 1)).filter Nat.Prime, q ∣ Nat.totient n}

lemma smallPrimesDivideTotient_hasDensity_one (B : ℕ) :
    (smallPrimesDivideTotient B).HasDensity 1 := by
  classical
  let Q := (Finset.range (B + 1)).filter Nat.Prime
  let S : ℕ → Set ℕ := fun q ↦ {n | q ∣ Nat.totient n}
  have hqzero : ∀ q ∈ Q,
      Tendsto (fun N : ℕ ↦ ((S q)ᶜ ∩ Set.Iio N).ncard / (N : ℝ))
        atTop (nhds 0) := by
    intro q hq
    have hqprime : q.Prime := (Finset.mem_filter.mp hq).2
    exact compl_ratio_tendsto_zero_of_hasDensity_one (S q)
      (prime_dvd_totient_hasDensity_one q hqprime)
  have hsum : Tendsto
      (fun N : ℕ ↦ ∑ q ∈ Q, ((S q)ᶜ ∩ Set.Iio N).ncard / (N : ℝ))
      atTop (nhds 0) := by
    simpa using tendsto_finsetSum Q hqzero
  apply hasDensity_one_of_compl_ratio_tendsto_zero
  refine squeeze_zero_norm ?_ hsum
  intro N
  have hsubset : ((smallPrimesDivideTotient B)ᶜ ∩ Set.Iio N) ⊆
      ⋃ q ∈ Q, (S q)ᶜ ∩ Set.Iio N := by
    rintro n ⟨hn, hnN⟩
    have hn' : ¬ ∀ q, q ∈ Q → q ∣ Nat.totient n := by
      exact hn
    push Not at hn'
    obtain ⟨q, hqQ, hnq⟩ := hn'
    exact Set.mem_iUnion_of_mem q <| Set.mem_iUnion_of_mem hqQ ⟨hnq, hnN⟩
  have hunionFinite : (⋃ q ∈ Q, (S q)ᶜ ∩ Set.Iio N).Finite := by
    apply (Set.finite_Iio N).subset
    intro n hn
    simp only [Set.mem_iUnion] at hn
    obtain ⟨q, hq⟩ := hn
    obtain ⟨hqQ, hn⟩ := hq
    exact hn.2
  have hcardNat : ((smallPrimesDivideTotient B)ᶜ ∩ Set.Iio N).ncard ≤
      ∑ q ∈ Q, ((S q)ᶜ ∩ Set.Iio N).ncard := by
    exact (Set.ncard_le_ncard hsubset hunionFinite).trans
      (Q.set_ncard_biUnion_le fun q ↦ (S q)ᶜ ∩ Set.Iio N)
  have hcard : (((smallPrimesDivideTotient B)ᶜ ∩ Set.Iio N).ncard : ℝ) ≤
      ∑ q ∈ Q, (((S q)ᶜ ∩ Set.Iio N).ncard : ℝ) := by
    exact_mod_cast hcardNat
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc
    (((smallPrimesDivideTotient B)ᶜ ∩ Set.Iio N).ncard : ℝ) / N ≤
        (∑ q ∈ Q, (((S q)ᶜ ∩ Set.Iio N).ncard : ℝ)) / N :=
      div_le_div_of_nonneg_right hcard (by positivity)
    _ = ∑ q ∈ Q, ((S q)ᶜ ∩ Set.Iio N).ncard / (N : ℝ) := by
      rw [Finset.sum_div]

lemma normalized_gap_lower_bound
    {B n : ℕ} {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) (hn : 2 ≤ n)
    (hsmall : n ∈ smallPrimesDivideTotient B)
    (hratio : δ ≤ (Nat.totient n : ℝ) / n)
    (htail : largeReciprocalPrimeMass B n < δ / 2) :
    δ ^ 2 / 2 <
      ((Nat.totient n : ℝ) - Nat.totient (n - Nat.totient n)) / n := by
  classical
  let m := n - Nat.totient n
  let A := n.primeFactors
  let M := m.primeFactors
  let R := A \ M
  let factor : ℕ → ℝ := fun p ↦ 1 - (p : ℝ)⁻¹
  let a : ℝ := (Nat.totient n : ℝ) / n
  let b : ℝ := (Nat.totient m : ℝ) / m
  let c : ℝ := ∏ p ∈ R, factor p
  let gap : ℝ := a - (1 - a) * b
  have hn0 : n ≠ 0 := by omega
  have hphiLt : Nat.totient n < n := Nat.totient_lt n (by omega)
  have hmpos : 0 < m := by simp [m]; omega
  have hm0 : m ≠ 0 := hmpos.ne'
  have haEq : a = ∏ p ∈ A, factor p := by
    simpa [a, A, factor] using totient_ratio_eq hn0
  have hbEq : b = ∏ p ∈ M, factor p := by
    simpa [b, M, factor] using totient_ratio_eq hm0
  have hfactor0 : ∀ p, p.Prime → 0 ≤ factor p := by
    intro p hp
    have hp1 : (p : ℝ)⁻¹ ≤ 1 := by
      apply inv_le_one_of_one_le₀
      exact_mod_cast hp.one_lt.le
    simp only [factor]
    linarith
  have hfactor1 : ∀ p, p.Prime → factor p ≤ 1 := by
    intro p hp
    simp only [factor]
    exact sub_le_self 1 (by positivity)
  have hRlarge : R ⊆ n.primeFactors.filter (B < ·) := by
    intro p hpR
    have hpA : p ∈ A := (Finset.mem_sdiff.mp hpR).1
    have hpM : p ∉ M := (Finset.mem_sdiff.mp hpR).2
    have hpprime : p.Prime := Nat.prime_of_mem_primeFactors hpA
    have hpn : p ∣ n := Nat.dvd_of_mem_primeFactors hpA
    apply Finset.mem_filter.mpr
    refine ⟨hpA, ?_⟩
    by_contra hpB
    have hp_le_B : p ≤ B := Nat.le_of_not_gt hpB
    have hpQ : p ∈ (Finset.range (B + 1)).filter Nat.Prime := by
      simp [hpprime, hp_le_B]
    have hpPhi : p ∣ Nat.totient n := hsmall p hpQ
    have hpm : p ∣ m := by
      simpa [m] using Nat.dvd_sub hpn hpPhi
    exact hpM (hpprime.mem_primeFactors hpm hm0)
  have hRsum : (∑ p ∈ R, (p : ℝ)⁻¹) < δ / 2 := by
    have hle : (∑ p ∈ R, (p : ℝ)⁻¹) ≤
        largeReciprocalPrimeMass B n := by
      rw [largeReciprocalPrimeMass]
      apply Finset.sum_le_sum_of_subset_of_nonneg hRlarge
      intro p hp hpnot
      positivity
    exact hle.trans_lt htail
  have hcLower : 1 - δ / 2 < c := by
    have hprod := Finset.one_sub_sum_le_prod_one_sub
      (s := R) (f := fun p ↦ (p : ℝ)⁻¹)
      (fun p hp ↦ by positivity)
      (fun p hp ↦ by
        apply inv_le_one_of_one_le₀
        exact_mod_cast (Nat.prime_of_mem_primeFactors (Finset.mem_sdiff.mp hp).1).one_lt.le)
    have : 1 - δ / 2 < 1 - ∑ p ∈ R, (p : ℝ)⁻¹ := by linarith
    exact this.trans_le (by simpa [c, factor] using hprod)
  have hc0 : 0 ≤ c := by
    apply Finset.prod_nonneg
    intro p hp
    exact hfactor0 p (Nat.prime_of_mem_primeFactors (Finset.mem_sdiff.mp hp).1)
  have hc1 : c ≤ 1 := by
    apply Finset.prod_le_one
    · intro p hp
      exact hfactor0 p (Nat.prime_of_mem_primeFactors (Finset.mem_sdiff.mp hp).1)
    · intro p hp
      exact hfactor1 p (Nat.prime_of_mem_primeFactors (Finset.mem_sdiff.mp hp).1)
  have ha0 : 0 ≤ a := by simp [a]; positivity
  have ha1 : a ≤ 1 := by
    simp only [a]
    exact (div_le_one (by exact_mod_cast (show 0 < n by omega))).mpr
      (by exact_mod_cast Nat.totient_le n)
  have hb0 : 0 ≤ b := by simp [b]; positivity
  have hAMR : A ⊆ M ∪ R := by
    intro p hp
    by_cases hpM : p ∈ M
    · exact Finset.mem_union_left R hpM
    · exact Finset.mem_union_right M (Finset.mem_sdiff.mpr ⟨hp, hpM⟩)
  have hprodMR : (∏ p ∈ M ∪ R, factor p) ≤ ∏ p ∈ A, factor p := by
    apply Finset.prod_le_prod_of_subset_of_le_one hAMR
    · intro p hp
      rcases Finset.mem_union.mp hp with hpM | hpR
      · exact hfactor0 p (Nat.prime_of_mem_primeFactors hpM)
      · exact hfactor0 p
          (Nat.prime_of_mem_primeFactors (Finset.mem_sdiff.mp hpR).1)
    · intro p hp hpA
      rcases Finset.mem_union.mp hp with hpM | hpR
      · exact hfactor1 p (Nat.prime_of_mem_primeFactors hpM)
      · exact hfactor1 p
          (Nat.prime_of_mem_primeFactors (Finset.mem_sdiff.mp hpR).1)
  have hdisj : Disjoint M R := Finset.sdiff_disjoint.symm
  have hbc : b * c ≤ a := by
    rw [hbEq, haEq]
    rw [← Finset.prod_union hdisj]
    exact hprodMR
  have hapos : 0 < a := hδ0.trans_le hratio
  have hcpos : 0 < c := by linarith
  have hright : δ / 2 < a + c - 1 := by linarith
  have hquad : δ ^ 2 / 2 < a * (a + c - 1) := by
    calc
      δ ^ 2 / 2 = δ * (δ / 2) := by ring
      _ ≤ a * (δ / 2) := by
        exact mul_le_mul_of_nonneg_right hratio (by positivity)
      _ < a * (a + c - 1) := mul_lt_mul_of_pos_left hright hapos
  have hstep : a * (a + c - 1) ≤ c * gap := by
    have hnonneg := mul_nonneg (sub_nonneg.mpr ha1) (sub_nonneg.mpr hbc)
    simp only [gap]
    nlinarith
  have hcgappos : 0 < c * gap := (hquad.trans_le hstep).trans' (by positivity)
  have hgappos : 0 < gap := pos_of_mul_pos_right hcgappos hc0
  have hcgap_le : c * gap ≤ gap := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hc1) hgappos.le]
  have hgap : δ ^ 2 / 2 < gap := (hquad.trans_le hstep).trans_le hcgap_le
  have hgapEq : gap =
      ((Nat.totient n : ℝ) - Nat.totient m) / n := by
    have hmcast : (m : ℝ) = (n : ℝ) - Nat.totient n := by
      simp [m, Nat.cast_sub hphiLt.le]
    have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn0
    have hmDiff : (n : ℝ) - Nat.totient n ≠ 0 := by
      rw [← hmcast]
      exact_mod_cast hm0
    simp only [gap, a, b]
    rw [hmcast]
    field_simp [hnR, hmDiff]
  rw [hgapEq] at hgap
  simpa [m] using hgap

lemma ncard_inter_Iio_eq_filter_card (S : Set ℕ) (N : ℕ)
    [DecidablePred fun n ↦ n ∈ S] :
    (S ∩ Set.Iio N).ncard =
      ((Finset.range N).filter fun n ↦ n ∈ S).card := by
  classical
  rw [Set.ncard_eq_toFinset_card _
    ((Set.finite_Iio N).subset Set.inter_subset_right)]
  apply congrArg Finset.card
  ext n
  simp [and_comm]

lemma filter_card_four_le
    (s : Finset ℕ) (Q P₀ P₁ P₂ P₃ : ℕ → Prop)
    [DecidablePred Q] [DecidablePred P₀] [DecidablePred P₁]
    [DecidablePred P₂] [DecidablePred P₃]
    (h : ∀ n ∈ s, Q n → P₀ n ∨ P₁ n ∨ P₂ n ∨ P₃ n) :
    (s.filter Q).card ≤ (s.filter P₀).card + (s.filter P₁).card +
      (s.filter P₂).card + (s.filter P₃).card := by
  have hsub : s.filter Q ⊆
      ((s.filter P₀ ∪ s.filter P₁) ∪ s.filter P₂) ∪ s.filter P₃ := by
    intro n hn
    have hn' := Finset.mem_filter.mp hn
    rcases h n hn'.1 hn'.2 with h₀ | h₁ | h₂ | h₃
    · simp [hn'.1, h₀]
    · simp [hn'.1, h₁]
    · simp [hn'.1, h₂]
    · simp [hn'.1, h₃]
  calc
    (s.filter Q).card ≤
        (((s.filter P₀ ∪ s.filter P₁) ∪ s.filter P₂) ∪ s.filter P₃).card :=
      Finset.card_le_card hsub
    _ ≤ ((s.filter P₀ ∪ s.filter P₁) ∪ s.filter P₂).card +
        (s.filter P₃).card := Finset.card_union_le _ _
    _ ≤ (s.filter P₀ ∪ s.filter P₁).card + (s.filter P₂).card +
        (s.filter P₃).card := by gcongr; exact Finset.card_union_le _ _
    _ ≤ ((s.filter P₀).card + (s.filter P₁).card) +
        (s.filter P₂).card + (s.filter P₃).card := by
      gcongr
      exact Finset.card_union_le _ _

lemma general_density_aux (f : ℕ → ℕ)
    (hf : (fun n ↦ (f n : ℝ)) =o[atTop] (fun n ↦ (n : ℝ))) :
    {n : ℕ | Nat.totient (n - Nat.totient n) + f n < Nat.totient n}.HasDensity 1 := by
  classical
  let G : Set ℕ :=
    {n | Nat.totient (n - Nat.totient n) + f n < Nat.totient n}
  suffices G.HasDensity 1 by simpa [G] using this
  apply hasDensity_one_of_compl_ratio_tendsto_zero
  rw [Metric.tendsto_atTop]
  intro ε hε
  let T : ℝ := 8 / ε
  let δ : ℝ := Real.exp (-T)
  have hT : 0 < T := by positivity
  have hδ0 : 0 < δ := Real.exp_pos _
  have hδ1 : δ < 1 := by
    dsimp [δ]
    rw [Real.exp_lt_one_iff]
    linarith
  obtain ⟨B, hBgt⟩ := exists_nat_gt (8 / (ε * δ))
  have hεδ : 0 < ε * δ := mul_pos hε hδ0
  have hBR : 0 < (B : ℝ) := by
    exact (div_pos (by norm_num) hεδ).trans hBgt
  have hBN : 0 < B := by exact_mod_cast hBR
  have hB : 1 ≤ B := hBN
  have htailConst : 2 / ((B : ℝ) * δ) < ε / 4 := by
    apply (div_lt_iff₀ (mul_pos hBR hδ0)).2
    have hcross : 8 < (B : ℝ) * (ε * δ) :=
      (div_lt_iff₀ hεδ).mp hBgt
    nlinarith
  have hratioConst : 2 / T = ε / 4 := by
    dsimp [T]
    field_simp
    norm_num
  have hcoef : 0 < δ ^ 2 / 4 := by positivity
  have hfEventually := hf.def hcoef
  rw [Filter.eventually_atTop] at hfEventually
  obtain ⟨Nf, hNf⟩ := hfEventually
  let C := max 2 Nf
  have hsmallZero := compl_ratio_tendsto_zero_of_hasDensity_one
    (smallPrimesDivideTotient B) (smallPrimesDivideTotient_hasDensity_one B)
  have hε4 : 0 < ε / 4 := by positivity
  have hsmallEventually := hsmallZero.eventually
    (Metric.ball_mem_nhds (0 : ℝ) hε4)
  rw [Filter.eventually_atTop] at hsmallEventually
  obtain ⟨Ns, hNs⟩ := hsmallEventually
  have hcutZero : Tendsto (fun N : ℕ ↦ (C : ℝ) / N) atTop (nhds 0) := by
    exact tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop)
  have hcutEventually := hcutZero.eventually
    (Metric.ball_mem_nhds (0 : ℝ) hε4)
  rw [Filter.eventually_atTop] at hcutEventually
  obtain ⟨Nc, hNc⟩ := hcutEventually
  refine ⟨max (max Ns Nc) 1, fun N hN ↦ ?_⟩
  have hNsN : Ns ≤ N :=
    le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hNcN : Nc ≤ N :=
    le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hNnat : 1 ≤ N := le_trans (le_max_right _ _) hN
  have hsmallN := hNs N hNsN
  have hcutN := hNc N hNcN
  have hsmallBound :
      (((smallPrimesDivideTotient B)ᶜ ∩ Set.Iio N).ncard : ℝ) / N < ε / 4 := by
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)] at hsmallN
    exact hsmallN
  have hcutBound : (C : ℝ) / N < ε / 4 := by
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)] at hcutN
    exact hcutN
  let P₀ : ℕ → Prop := fun n ↦ n < C
  let P₁ : ℕ → Prop := fun n ↦
    n ≠ 0 ∧ (Nat.totient n : ℝ) / n < δ
  let P₂ : ℕ → Prop := fun n ↦ δ / 2 ≤ largeReciprocalPrimeMass B n
  let P₃ : ℕ → Prop := fun n ↦ n ∉ smallPrimesDivideTotient B
  have hbad : ∀ n ∈ Finset.range N, n ∉ G →
      P₀ n ∨ P₁ n ∨ P₂ n ∨ P₃ n := by
    intro n hnN hnG
    by_cases h₀ : P₀ n
    · exact Or.inl h₀
    by_cases h₁ : P₁ n
    · exact Or.inr (Or.inl h₁)
    by_cases h₂ : P₂ n
    · exact Or.inr (Or.inr (Or.inl h₂))
    by_cases h₃ : P₃ n
    · exact Or.inr (Or.inr (Or.inr h₃))
    exfalso
    have hnC : C ≤ n := by simpa [P₀] using h₀
    have hnRatio : ¬(Nat.totient n : ℝ) / n < δ := by
      simpa [P₁, show n ≠ 0 by
        have : 2 ≤ n := le_trans (le_max_left 2 Nf) hnC
        omega] using h₁
    have hnTail : ¬δ / 2 ≤ largeReciprocalPrimeMass B n := by
      simpa [P₂] using h₂
    have hnSmall : n ∈ smallPrimesDivideTotient B := by
      simpa [P₃] using h₃
    have hn2 : 2 ≤ n := le_trans (le_max_left 2 Nf) hnC
    have hnNf : Nf ≤ n := le_trans (le_max_right 2 Nf) hnC
    have hfnorm := hNf n hnNf
    have hnR : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
    have hfn : (f n : ℝ) < (δ ^ 2 / 2) * n := by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), Real.norm_eq_abs,
        abs_of_nonneg (by positivity)] at hfnorm
      have hquarter : (δ ^ 2 / 4) * (n : ℝ) <
          (δ ^ 2 / 2) * n := by nlinarith [sq_pos_of_pos hδ0]
      exact hfnorm.trans_lt hquarter
    have hgap := normalized_gap_lower_bound hδ0 hδ1 hn2 hnSmall
      (le_of_not_gt hnRatio) (lt_of_not_ge hnTail)
    have hgap' : (δ ^ 2 / 2) * (n : ℝ) <
        (Nat.totient n : ℝ) - Nat.totient (n - Nat.totient n) :=
      (lt_div_iff₀ hnR).mp hgap
    have hreal : (Nat.totient (n - Nat.totient n) : ℝ) + f n <
        Nat.totient n := by linarith
    have hnat : Nat.totient (n - Nat.totient n) + f n < Nat.totient n := by
      exact_mod_cast hreal
    exact hnG hnat
  have hcardNat := filter_card_four_le (Finset.range N)
    (fun n ↦ n ∉ G) P₀ P₁ P₂ P₃ hbad
  have hcard : (((Finset.range N).filter fun n ↦ n ∉ G).card : ℝ) ≤
      (((Finset.range N).filter P₀).card : ℝ) +
      ((Finset.range N).filter P₁).card +
      ((Finset.range N).filter P₂).card +
      ((Finset.range N).filter P₃).card := by exact_mod_cast hcardNat
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hP₀Nat : ((Finset.range N).filter P₀).card ≤ C := by
    calc
      ((Finset.range N).filter P₀).card ≤ (Finset.range C).card := by
        apply Finset.card_le_card
        intro n hn
        have hn' := (Finset.mem_filter.mp hn).2
        exact Finset.mem_range.mpr (by simpa [P₀] using hn')
      _ = C := Finset.card_range C
  have hP₀ : (((Finset.range N).filter P₀).card : ℝ) / N ≤ (C : ℝ) / N := by
    exact div_le_div_of_nonneg_right (by exact_mod_cast hP₀Nat) (by positivity)
  have hP₁ : (((Finset.range N).filter P₁).card : ℝ) / N ≤ 2 / T := by
    simpa [P₁, δ] using small_totient_ratio_count T hT N
  have hP₂ : (((Finset.range N).filter P₂).card : ℝ) / N ≤
      2 / ((B : ℝ) * δ) := by
    simpa [P₂] using large_tail_count B N hB δ hδ0
  have hP₃ : (((Finset.range N).filter P₃).card : ℝ) / N ≤
      (((smallPrimesDivideTotient B)ᶜ ∩ Set.Iio N).ncard : ℝ) / N := by
    rw [ncard_inter_Iio_eq_filter_card]
    simp [P₃]
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)]
  rw [ncard_inter_Iio_eq_filter_card]
  calc
    (((Finset.range N).filter fun n ↦ n ∈ Gᶜ).card : ℝ) / N ≤
        ((((Finset.range N).filter P₀).card : ℝ) +
          ((Finset.range N).filter P₁).card +
          ((Finset.range N).filter P₂).card +
          ((Finset.range N).filter P₃).card) / N :=
      div_le_div_of_nonneg_right (by simpa using hcard) (by positivity)
    _ = (((Finset.range N).filter P₀).card : ℝ) / N +
          ((Finset.range N).filter P₁).card / N +
          ((Finset.range N).filter P₂).card / N +
          ((Finset.range N).filter P₃).card / N := by ring
    _ ≤ (C : ℝ) / N + 2 / T + 2 / ((B : ℝ) * δ) +
          (((smallPrimesDivideTotient B)ᶜ ∩ Set.Iio N).ncard : ℝ) / N := by
      exact add_le_add (add_le_add (add_le_add hP₀ hP₁) hP₂) hP₃
    _ < ε / 4 + ε / 4 + ε / 4 + ε / 4 := by
      rw [hratioConst]
      linarith
    _ = ε := by ring

/-- The inequality `φ n > φ (n - φ n)` holds with asymptotic density one. -/
theorem erdos_1064 : {n | φ n > φ (n - φ n)}.HasDensity 1 := by
  apply general_density_aux (f := fun _ ↦ 0)
  simp only [Nat.cast_zero]
  exact
    (Asymptotics.isLittleO_zero (fun n : ℕ ↦ (n : ℝ)) atTop)

/-- There are infinitely many `n` for which the reverse strict inequality holds. -/
theorem erdos_1064.variants.k2 : {n | φ n < φ (n - φ n)}.Infinite := by
  apply Set.infinite_of_injective_forall_mem (f := fun k : ℕ ↦ 30 * 2 ^ k)
  · intro a b hab
    simp only at hab
    have : (2 : ℕ) ^ a = 2 ^ b := by omega
    exact Nat.pow_right_injective (le_refl 2) this
  · intro k
    simp only [Set.mem_ofPred_eq]
    have hφ : Nat.totient (30 * 2 ^ k) = 8 * 2 ^ k := by
      have h : 30 * 2 ^ k = 2 ^ (k + 1) * 15 := by ring
      rw [h, Nat.totient_mul (by norm_num),
        Nat.totient_prime_pow Nat.prime_two (by omega),
        show Nat.totient 15 = 8 from rfl, Nat.add_sub_cancel]
      ring
    have hsub : 30 * 2 ^ k - Nat.totient (30 * 2 ^ k) = 22 * 2 ^ k := by
      rw [hφ]
      omega
    have hφsub : Nat.totient (22 * 2 ^ k) = 10 * 2 ^ k := by
      rw [show 22 * 2 ^ k = 2 ^ (k + 1) * 11 by ring,
        Nat.totient_mul (by norm_num), Nat.totient_prime_pow (by norm_num) (by omega),
        show Nat.totient 11 = 10 from rfl, Nat.add_sub_cancel]
      ring
    rw [hsub, hφ, hφsub]
    have : (0 : ℕ) < 2 ^ k := pow_pos (by norm_num) k
    omega

/-- The strengthened result with an arbitrary natural-valued error `f = o(n)`. -/
theorem erdos_1064.variants.general_function (f : ℕ → ℕ)
    (hf : (fun n ↦ (f n : ℝ)) =o[atTop] (fun n ↦ (n : ℝ))) :
    {n : ℕ | φ (n - φ n) + f n < φ n}.HasDensity 1 := by
  exact general_density_aux f hf


end

end Erdos1064
