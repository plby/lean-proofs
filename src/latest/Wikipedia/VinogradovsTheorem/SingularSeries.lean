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
import Wikipedia.VinogradovsTheorem.External.MathExtras.NumberTheory.Vinogradov.MajorArcExplicit
import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.NumberTheory.SumPrimeReciprocals
import Mathlib.Analysis.SpecialFunctions.Log.Summable

/-!
# The qualitative ternary-Goldbach singular series

This file isolates the arithmetic part of the qualitative circle method used
for Erdős Problem 471.  It proves, without citation axioms, that the absolutely
convergent Ramanujan denominator series has the expected Euler product and is
uniformly positive on odd integers.
-/

namespace VinogradovsTheorem.Analytic

open scoped BigOperators Topology
open Filter

/-- The odd-prime local factor in the ternary Goldbach singular series.  The
prime `2` is normalized to one; its factor two is kept outside the product. -/
noncomputable def localFactor (p n : ℕ) : ℝ :=
  if p ≤ 2 then 1
  else if p ∣ n then 1 - 1 / ((p : ℝ) - 1) ^ 2
  else 1 + 1 / ((p : ℝ) - 1) ^ 3

/-- The Euler-product normalization of the ternary Goldbach singular series. -/
noncomputable def singularSeries (n : ℕ) : ℝ :=
  ∏' p : Nat.Primes, localFactor p.val n

lemma localFactor_pos_of_prime {p n : ℕ} (hp : p.Prime) :
    0 < localFactor p n := by
  unfold localFactor
  by_cases hp2 : p ≤ 2
  · simp [hp2]
  · have hp3 : 3 ≤ p := by omega
    have hp3R : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp3
    have hp1 : (1 : ℝ) < (p : ℝ) - 1 := by linarith
    simp only [hp2, if_false]
    split_ifs with hpn
    · have hsq : (1 : ℝ) < ((p : ℝ) - 1) ^ 2 :=
        one_lt_pow₀ hp1 (by norm_num)
      have hinv : 1 / ((p : ℝ) - 1) ^ 2 < 1 := by
        rw [div_lt_one (by positivity)]
        exact hsq
      linarith
    · positivity

lemma localFactor_two (n : ℕ) : localFactor 2 n = 1 := by
  simp [localFactor]

lemma localFactor_of_dvd {p n : ℕ} (hp3 : 3 ≤ p) (hpn : p ∣ n) :
    localFactor p n = 1 - 1 / ((p : ℝ) - 1) ^ 2 := by
  simp [localFactor, show ¬ p ≤ 2 by omega, hpn]

lemma localFactor_of_not_dvd {p n : ℕ} (hp3 : 3 ≤ p) (hpn : ¬p ∣ n) :
    localFactor p n = 1 + 1 / ((p : ℝ) - 1) ^ 3 := by
  simp [localFactor, show ¬ p ≤ 2 by omega, hpn]

/-- Absolute convergence of the local-factor product. -/
theorem multipliable_localFactor (n : ℕ) :
    Multipliable (fun p : Nat.Primes ↦ localFactor p.val n) := by
  let g : Nat.Primes → ℝ := fun p ↦ localFactor p.val n - 1
  have hfactor : ∀ p : Nat.Primes, localFactor p.val n = 1 + g p := by
    intro p
    simp [g]
  have hbound : ∀ p : Nat.Primes, |g p| ≤ 4 * ((p.val : ℝ) ^ (-2 : ℝ)) := by
    intro p
    have hpR : (0 : ℝ) < p.val := by exact_mod_cast p.prop.pos
    have hrpow : (p.val : ℝ) ^ (-2 : ℝ) = 1 / (p.val : ℝ) ^ 2 := by
      rw [Real.rpow_neg hpR.le, Real.rpow_two, one_div]
    rw [hrpow]
    by_cases hp2 : p.val ≤ 2
    · have hg : g p = 0 := by simp [g, localFactor, hp2]
      simp [hg]
    · have hp3 : 3 ≤ p.val := by omega
      have hp3R : (3 : ℝ) ≤ (p.val : ℝ) := by exact_mod_cast hp3
      have hp1 : (0 : ℝ) < (p.val : ℝ) - 1 := by linarith
      have hp1one : (1 : ℝ) ≤ (p.val : ℝ) - 1 := by linarith
      have hsq : 1 / ((p.val : ℝ) - 1) ^ 2 ≤
          4 * (1 / (p.val : ℝ) ^ 2) := by
        rw [div_le_iff₀ (by positivity)]
        rw [show (4 : ℝ) * (1 / (p.val : ℝ) ^ 2) =
            4 / (p.val : ℝ) ^ 2 by ring]
        rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
        nlinarith [sq_nonneg ((p.val : ℝ) - 1),
          sq_nonneg ((p.val : ℝ) - 2)]
      rw [show g p = localFactor p.val n - 1 by rfl]
      rw [localFactor]
      simp only [hp2, if_false]
      split_ifs with hpn
      · rw [show 1 - 1 / ((p.val : ℝ) - 1) ^ 2 - 1 =
            -(1 / ((p.val : ℝ) - 1) ^ 2) by ring,
          abs_neg, abs_of_pos (by positivity)]
        exact hsq
      · rw [show 1 + 1 / ((p.val : ℝ) - 1) ^ 3 - 1 =
            1 / ((p.val : ℝ) - 1) ^ 3 by ring,
          abs_of_pos (by positivity)]
        calc
          1 / ((p.val : ℝ) - 1) ^ 3 ≤
              1 / ((p.val : ℝ) - 1) ^ 2 := by
            rw [div_le_div_iff₀ (by positivity) (by positivity)]
            nlinarith
          _ ≤ 4 * (1 / (p.val : ℝ) ^ 2) := hsq
  have hsum : Summable (fun p : Nat.Primes ↦
      4 * ((p.val : ℝ) ^ (-2 : ℝ))) :=
    (Nat.Primes.summable_rpow.mpr (by norm_num : (-2 : ℝ) < -1)).mul_left 4
  have hg : Summable g := by
    refine Summable.of_norm_bounded hsum ?_
    intro p
    rw [Real.norm_eq_abs]
    exact hbound p
  have hlog : Summable (fun p : Nat.Primes ↦ Real.log (1 + g p)) :=
    Real.summable_log_one_add_of_summable hg
  have hpos : ∀ p : Nat.Primes, 0 < localFactor p.val n :=
    fun p ↦ localFactor_pos_of_prime p.prop
  apply Real.multipliable_of_summable_log hpos
  exact hlog.congr fun p ↦ by rw [hfactor p]

private theorem prod_range_one_sub_inv_sq_shift_eq (m : ℕ) :
    (∏ k ∈ Finset.range m, (1 - 1 / (((k : ℝ) + 2) ^ 2))) =
      ((m : ℝ) + 2) / (2 * ((m : ℝ) + 1)) := by
  induction m with
  | zero => norm_num
  | succ m ih =>
      rw [Finset.prod_range_succ, ih]
      have hm1 : ((m : ℝ) + 1) ≠ 0 := by positivity
      have hm2 : ((m : ℝ) + 2) ≠ 0 := by positivity
      field_simp [hm1, hm2]
      norm_num [Nat.cast_add, Nat.cast_one]
      ring

private theorem prod_Ico_two_one_sub_inv_sq_ge_half (M : ℕ) :
    (1 / 2 : ℝ) ≤ ∏ k ∈ Finset.Ico 2 (M + 1),
      (1 - 1 / ((k : ℝ) ^ 2)) := by
  by_cases hM : 2 ≤ M
  · rw [Finset.prod_Ico_eq_prod_range]
    have hsub : M + 1 - 2 = M - 1 := by omega
    rw [hsub]
    have hcongr :
        (∏ k ∈ Finset.range (M - 1),
            (1 - 1 / (↑(2 + k) ^ 2 : ℝ))) =
          ∏ k ∈ Finset.range (M - 1),
            (1 - 1 / (((k : ℝ) + 2) ^ 2)) := by
      refine Finset.prod_congr rfl ?_
      intro k _
      norm_num [Nat.cast_add]
      ring
    rw [hcongr, prod_range_one_sub_inv_sq_shift_eq]
    have hden : (0 : ℝ) < 2 * (M : ℝ) := by positivity
    have hcast1 : ((M - 1 : ℕ) : ℝ) + 2 = (M : ℝ) + 1 := by
      exact_mod_cast (by omega : M - 1 + 2 = M + 1)
    have hcast2 : ((M - 1 : ℕ) : ℝ) + 1 = (M : ℝ) := by
      exact_mod_cast (by omega : M - 1 + 1 = M)
    rw [hcast1, hcast2]
    rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < 2) hden]
    nlinarith
  · have hico : Finset.Ico 2 (M + 1) = ∅ :=
      Finset.Ico_eq_empty_of_le (by omega)
    rw [hico]
    norm_num

private theorem finite_prod_one_sub_inv_sq_ge_half (s : Finset ℕ)
    (hs : ∀ k ∈ s, 2 ≤ k) :
    (1 / 2 : ℝ) ≤ ∏ k ∈ s, (1 - 1 / ((k : ℝ) ^ 2)) := by
  classical
  let M := ∑ k ∈ s, k
  have hsubset : s ⊆ Finset.Ico 2 (M + 1) := by
    intro k hk
    have hkM : k ≤ M := Finset.single_le_sum (fun x _ ↦ Nat.zero_le x) hk
    simp [Finset.mem_Ico, hs k hk, Nat.lt_succ_of_le hkM]
  have hnonneg : ∀ k ∈ Finset.Ico 2 (M + 1),
      0 ≤ (1 - 1 / ((k : ℝ) ^ 2) : ℝ) := by
    intro k hk
    have hk2 : 2 ≤ k := (Finset.mem_Ico.mp hk).1
    have hkR : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk2
    have hsq : (1 : ℝ) ≤ (k : ℝ) ^ 2 := by nlinarith
    have hinv : 1 / ((k : ℝ) ^ 2) ≤ 1 := by
      rw [div_le_one (by positivity)]
      exact hsq
    linarith
  have hle : ∀ k ∈ Finset.Ico 2 (M + 1), k ∉ s →
      (1 - 1 / ((k : ℝ) ^ 2)) ≤ 1 := by
    intro k _ _
    have : 0 ≤ 1 / ((k : ℝ) ^ 2) := by positivity
    linarith
  exact (prod_Ico_two_one_sub_inv_sq_ge_half M).trans
    (Finset.prod_le_prod_of_subset_of_le_one hsubset hnonneg hle)

private theorem finite_prime_deficit_product_ge_half (S : Finset Nat.Primes)
    (hS3 : ∀ p ∈ S, 3 ≤ p.val) :
    (1 / 2 : ℝ) ≤ ∏ p ∈ S,
      (1 - 1 / (((p.val : ℝ) - 1) ^ 2)) := by
  classical
  let imageS : Finset ℕ := S.image (fun p : Nat.Primes ↦ p.val - 1)
  have himage : ∀ k ∈ imageS, 2 ≤ k := by
    intro k hk
    rcases Finset.mem_image.mp hk with ⟨p, hp, rfl⟩
    have hp3 := hS3 p hp
    omega
  have hhalf := finite_prod_one_sub_inv_sq_ge_half imageS himage
  have hinj : Set.InjOn (fun p : Nat.Primes ↦ p.val - 1) ↑S := by
    intro a ha b hb h
    apply Subtype.ext
    have ha3 := hS3 a ha
    have hb3 := hS3 b hb
    change a.val - 1 = b.val - 1 at h
    omega
  rw [Finset.prod_image (s := S) (g := fun p : Nat.Primes ↦ p.val - 1)
    (f := fun k : ℕ ↦ (1 - 1 / ((k : ℝ) ^ 2) : ℝ)) hinj] at hhalf
  convert hhalf using 1
  refine Finset.prod_congr rfl ?_
  intro p hp
  rw [Nat.cast_sub (by have := hS3 p hp; omega)]
  norm_num

/-- The normalized odd-prime Euler product is uniformly bounded below by
`1/2` for every odd target. -/
theorem singularSeries_lower_half_of_odd (n : ℕ) (hodd : Odd n) :
    (1 / 2 : ℝ) ≤ singularSeries n := by
  classical
  have hn0 : n ≠ 0 := by
    intro h
    exact hodd.not_two_dvd_nat (by simp [h])
  let base : Finset ℕ := n.primeFactors.filter (fun p ↦ p ≠ 2)
  let emb : {p // p ∈ base} ↪ Nat.Primes :=
    { toFun := fun p ↦
        ⟨p.1, (Nat.mem_primeFactors.mp (Finset.mem_filter.mp p.2).1).1⟩
      inj' := by
        intro a b h
        apply Subtype.ext
        exact congrArg (fun x : Nat.Primes ↦ x.val) h }
  let S : Finset Nat.Primes := base.attach.map emb
  have hSmem : ∀ p : Nat.Primes, p ∈ S ↔ p.val ∈ base := by
    intro p
    constructor
    · intro hp
      rcases Finset.mem_map.mp hp with ⟨x, _, hx⟩
      have hv : p.val = x.val := congrArg (fun y : Nat.Primes ↦ y.val) hx.symm
      simpa [hv, base] using x.2
    · intro hp
      let x : {p // p ∈ base} := ⟨p.val, hp⟩
      exact Finset.mem_map.mpr ⟨x, by simp [x], by apply Subtype.ext; rfl⟩
  have hS3 : ∀ p ∈ S, 3 ≤ p.val := by
    intro p hp
    have hb := (hSmem p).1 hp
    have hp2 : p.val ≠ 2 := (Finset.mem_filter.mp hb).2
    have hpge := p.prop.two_le
    omega
  have hprod : (1 / 2 : ℝ) ≤ ∏ p ∈ S, localFactor p.val n := by
    refine (finite_prime_deficit_product_ge_half S hS3).trans_eq ?_
    refine (Finset.prod_congr rfl ?_).symm
    intro p hp
    have hb := (hSmem p).1 hp
    have hdvd : p.val ∣ n :=
      (Nat.mem_primeFactors.mp (Finset.mem_filter.mp hb).1).2.1
    exact localFactor_of_dvd (hS3 p hp) hdvd
  have hmulti := multipliable_localFactor n
  have hnonneg : ∀ p : Nat.Primes, 0 ≤ localFactor p.val n :=
    fun p ↦ (localFactor_pos_of_prime p.prop).le
  have hone : ∀ p : Nat.Primes, p ∉ S → 1 ≤ localFactor p.val n := by
    intro p hpS
    by_cases hp2 : p.val = 2
    · rw [hp2, localFactor_two]
    · have hp3 : 3 ≤ p.val := by
        have := p.prop.two_le
        omega
      have hndvd : ¬p.val ∣ n := by
        intro hdvd
        have hpf : p.val ∈ n.primeFactors := p.prop.mem_primeFactors hdvd hn0
        have hb : p.val ∈ base := by simp [base, hpf, hp2]
        exact hpS ((hSmem p).2 hb)
      rw [localFactor_of_not_dvd hp3 hndvd]
      have hp3R : (3 : ℝ) ≤ (p.val : ℝ) := by exact_mod_cast hp3
      have hp1 : (0 : ℝ) < (p.val : ℝ) - 1 := by linarith
      exact le_add_of_nonneg_right (by positivity)
  have hprod_le : (∏ p ∈ S, localFactor p.val n) ≤
      ∏' p : Nat.Primes, localFactor p.val n := by
    refine ge_of_tendsto hmulti.hasProd <|
      .filter_mono
        (show (SummationFilter.unconditional Nat.Primes).filter ≤ Filter.atTop
          from le_rfl) ?_
    refine Filter.eventually_atTop.2 ⟨S, ?_⟩
    intro t hSt
    exact Finset.prod_le_prod_of_subset_of_one_le hSt
      (fun p _ ↦ hnonneg p) (fun p _ hp ↦ hone p hp)
  unfold singularSeries
  exact hprod.trans hprod_le

/-! ## Ramanujan denominator series -/

/-- The complex Ramanujan summand obtained after summing the reduced major-arc
centers with denominator `q`. -/
noncomputable def singularTerm (q n : ℕ) : ℂ :=
  (((((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 3) /
      (Nat.totient q : ℝ) ^ 3 : ℝ) : ℂ) * Vinogradov.ramanujanSum q n

lemma singularTerm_one (n : ℕ) : singularTerm 1 n = 1 := by
  unfold singularTerm Vinogradov.ramanujanSum
  simp

lemma singularTerm_zero (n : ℕ) : singularTerm 0 n = 0 := by
  unfold singularTerm
  simp

lemma singularTerm_mul_of_coprime
    {q₁ q₂ : ℕ} (hq₁ : 0 < q₁) (hq₂ : 0 < q₂)
    (hcop : q₁.Coprime q₂) (n : ℕ) :
    singularTerm (q₁ * q₂) n = singularTerm q₁ n * singularTerm q₂ n := by
  unfold singularTerm
  have hmu : ArithmeticFunction.moebius (q₁ * q₂) =
      ArithmeticFunction.moebius q₁ * ArithmeticFunction.moebius q₂ := by
    exact ArithmeticFunction.IsMultiplicative.map_mul_of_coprime
      ArithmeticFunction.isMultiplicative_moebius
      (Nat.coprime_iff_gcd_eq_one.mp hcop)
  have hphi : Nat.totient (q₁ * q₂) = Nat.totient q₁ * Nat.totient q₂ :=
    Nat.totient_mul hcop
  have hram : Vinogradov.ramanujanSum (q₁ * q₂) n =
      Vinogradov.ramanujanSum q₁ n * Vinogradov.ramanujanSum q₂ n := by
    exact ArithmeticFunction.IsMultiplicative.map_mul_of_coprime
      (Vinogradov.ramanujanSum_fixed_isMultiplicative n)
      (Nat.coprime_iff_gcd_eq_one.mp hcop)
  have hphi₁ : ((Nat.totient q₁ : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr hq₁).ne'
  have hphi₂ : ((Nat.totient q₂ : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr hq₂).ne'
  rw [hram, hmu, hphi]
  push_cast
  field_simp [hphi₁, hphi₂]

lemma singularTerm_prime_dvd {p n : ℕ} (hp : p.Prime) (hpn : p ∣ n) :
    singularTerm p n = ((-1 / ((p : ℝ) - 1) ^ 2 : ℝ) : ℂ) := by
  unfold singularTerm
  rw [Vinogradov.ramanujanSum_prime_for_moebius hp, if_pos hpn,
    ArithmeticFunction.moebius_apply_prime hp, Nat.totient_prime hp]
  have hp1 : 1 ≤ p := hp.one_lt.le
  have hpden : ((p : ℝ) - 1) ≠ 0 := by
    have hpgt : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
    linarith
  norm_num [Nat.cast_sub hp1]
  field_simp [hpden]

lemma singularTerm_prime_not_dvd {p n : ℕ} (hp : p.Prime) (hpn : ¬p ∣ n) :
    singularTerm p n = ((1 / ((p : ℝ) - 1) ^ 3 : ℝ) : ℂ) := by
  unfold singularTerm
  rw [Vinogradov.ramanujanSum_prime_for_moebius hp, if_neg hpn,
    ArithmeticFunction.moebius_apply_prime hp, Nat.totient_prime hp]
  have hp1 : 1 ≤ p := hp.one_lt.le
  have hpden : ((p : ℝ) - 1) ≠ 0 := by
    have hpgt : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
    linarith
  norm_num [Nat.cast_sub hp1]
  field_simp [hpden]

lemma singularTerm_prime {p n : ℕ} (hp : p.Prime) :
    singularTerm p n =
      if p ∣ n then ((-1 / ((p : ℝ) - 1) ^ 2 : ℝ) : ℂ)
      else ((1 / ((p : ℝ) - 1) ^ 3 : ℝ) : ℂ) := by
  by_cases hpn : p ∣ n
  · rw [if_pos hpn, singularTerm_prime_dvd hp hpn]
  · rw [if_neg hpn, singularTerm_prime_not_dvd hp hpn]

lemma singularTerm_prime_pow_eq_zero_of_two_le
    {p k n : ℕ} (hp : p.Prime) (hk : 2 ≤ k) :
    singularTerm (p ^ k) n = 0 := by
  have hk0 : k ≠ 0 := by omega
  have hk1 : k ≠ 1 := by omega
  unfold singularTerm
  rw [ArithmeticFunction.moebius_apply_prime_pow hp hk0, if_neg hk1]
  simp

lemma tsum_singularTerm_prime_pow_eq_localFactor
    {p n : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) :
    (∑' k : ℕ, singularTerm (p ^ k) n) = (localFactor p n : ℂ) := by
  have hsupport : ∀ k : ℕ, k ∉ ({0, 1} : Finset ℕ) →
      singularTerm (p ^ k) n = 0 := by
    intro k hk
    exact singularTerm_prime_pow_eq_zero_of_two_le hp (by
      by_contra hklt
      interval_cases k <;> simp at hk)
  rw [tsum_eq_sum hsupport]
  simp only [Finset.mem_singleton, Finset.sum_insert, Finset.sum_singleton,
    zero_ne_one, not_false_eq_true, Nat.pow_zero, Nat.pow_one]
  by_cases hpn : p ∣ n
  · rw [singularTerm_one, singularTerm_prime_dvd hp hpn,
      localFactor_of_dvd hp3 hpn]
    norm_num [sub_eq_add_neg, div_eq_mul_inv]
  · rw [singularTerm_one, singularTerm_prime_not_dvd hp hpn,
      localFactor_of_not_dvd hp3 hpn]
    norm_num

lemma tsum_singularTerm_two_pow (n : ℕ) :
    (∑' k : ℕ, singularTerm (2 ^ k) n) =
      if 2 ∣ n then (0 : ℂ) else (2 : ℂ) := by
  have hsupport : ∀ k : ℕ, k ∉ ({0, 1} : Finset ℕ) →
      singularTerm (2 ^ k) n = 0 := by
    intro k hk
    exact singularTerm_prime_pow_eq_zero_of_two_le Nat.prime_two (by
      by_contra hklt
      interval_cases k <;> simp at hk)
  rw [tsum_eq_sum hsupport]
  simp only [Finset.mem_singleton, Finset.sum_insert, Finset.sum_singleton,
    zero_ne_one, not_false_eq_true, Nat.pow_zero, Nat.pow_one]
  by_cases hpn : 2 ∣ n
  · rw [if_pos hpn, singularTerm_one,
      singularTerm_prime_dvd Nat.prime_two hpn]
    norm_num
  · rw [if_neg hpn, singularTerm_one,
      singularTerm_prime_not_dvd Nat.prime_two hpn]
    norm_num

lemma tprod_singularTerm_prime_pow_eq_two_singularSeries
    {n : ℕ} (hodd : Odd n) :
    (∏' p : Nat.Primes, ∑' k : ℕ, singularTerm (p.val ^ k) n) =
      (2 : ℂ) * (singularSeries n : ℂ) := by
  let twoPrime : Nat.Primes := ⟨2, Nat.prime_two⟩
  let f : Nat.Primes → ℂ := fun p ↦ ∑' k : ℕ, singularTerm (p.val ^ k) n
  let lfC : Nat.Primes → ℂ := fun p ↦ (localFactor p.val n : ℂ)
  have hlfC : Multipliable lfC := by
    simpa [lfC, Function.comp_def] using
      (multipliable_localFactor n).map Complex.ofRealHom Complex.continuous_ofReal
  have hupdate : Function.update f twoPrime 1 = lfC := by
    funext p
    by_cases hp2 : p = twoPrime
    · subst p
      change Function.update f twoPrime 1 twoPrime = lfC twoPrime
      rw [Function.update_self]
      simp [lfC, twoPrime, localFactor_two]
    · have hp3 : 3 ≤ p.val := by
        have h2le : 2 ≤ p.val := p.prop.two_le
        have hpval_ne : p.val ≠ 2 := fun h ↦ hp2 (Subtype.ext h)
        omega
      rw [Function.update_of_ne hp2]
      exact tsum_singularTerm_prime_pow_eq_localFactor p.prop hp3
  have hf_two : f twoPrime = 2 := by
    change (∑' k : ℕ, singularTerm (2 ^ k) n) = 2
    rw [tsum_singularTerm_two_pow, if_neg hodd.not_two_dvd_nat]
  have htprod_split := Multipliable.tprod_eq_mul_tprod_ite' (f := f) twoPrime (by
    simpa [hupdate] using hlfC)
  have hite : ∀ p : Nat.Primes, (if p = twoPrime then 1 else f p) = lfC p := by
    intro p
    by_cases hp2 : p = twoPrime
    · subst p
      rw [if_pos rfl]
      simp [lfC, twoPrime, localFactor_two]
    · have hp3 : 3 ≤ p.val := by
        have h2le : 2 ≤ p.val := p.prop.two_le
        have hpval_ne : p.val ≠ 2 := fun h ↦ hp2 (Subtype.ext h)
        omega
      simp [hp2, f, lfC, tsum_singularTerm_prime_pow_eq_localFactor p.prop hp3]
  have htprod_ite :
      (∏' p : Nat.Primes, if p = twoPrime then 1 else f p) =
        (singularSeries n : ℂ) := by
    calc
      (∏' p : Nat.Primes, if p = twoPrime then 1 else f p) =
          ∏' p : Nat.Primes, lfC p := tprod_congr hite
      _ = (singularSeries n : ℂ) := by
        have hmap := (multipliable_localFactor n).map_tprod
          Complex.ofRealHom Complex.continuous_ofReal
        simpa [singularSeries, lfC, Function.comp_def] using hmap.symm
  change (∏' p : Nat.Primes, f p) = (2 : ℂ) * (singularSeries n : ℂ)
  rw [htprod_split, hf_two, htprod_ite]

private lemma norm_singularTerm_prime_le {p n : ℕ} (hp : p.Prime) :
    ‖singularTerm p n‖ ≤ 4 * ((p : ℝ) ^ (-2 : ℝ)) := by
  have hp_pos : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hp1_pos : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  have hp_ge_one : (1 : ℝ) ≤ (p : ℝ) - 1 := by linarith
  have hsq : 1 / ((p : ℝ) - 1) ^ 2 ≤ 4 * (1 / (p : ℝ) ^ 2) := by
    rw [div_le_iff₀ (by positivity)]
    rw [show (4 : ℝ) * (1 / (p : ℝ) ^ 2) = 4 / (p : ℝ) ^ 2 by ring]
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    nlinarith [sq_nonneg ((p : ℝ) - 1), sq_nonneg ((p : ℝ) - 2)]
  have hcube : 1 / ((p : ℝ) - 1) ^ 3 ≤ 1 / ((p : ℝ) - 1) ^ 2 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [hp_ge_one, sq_nonneg ((p : ℝ) - 1)]
  have hrpow : (p : ℝ) ^ (-2 : ℝ) = 1 / (p : ℝ) ^ 2 := by
    rw [Real.rpow_neg hp_pos.le, Real.rpow_two, one_div]
  rw [hrpow, singularTerm_prime hp]
  split_ifs with hpn
  · rw [Complex.norm_real, Real.norm_eq_abs]
    have habs : |(-1 / ((p : ℝ) - 1) ^ 2 : ℝ)| =
        1 / ((p : ℝ) - 1) ^ 2 := by
      rw [show (-1 / ((p : ℝ) - 1) ^ 2 : ℝ) =
          -(1 / ((p : ℝ) - 1) ^ 2) by ring,
        abs_neg, abs_of_pos (by positivity)]
    rw [habs]
    exact hsq
  · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    exact hcube.trans hsq

private lemma summable_norm_norm_singularTerm_prime_pow {p n : ℕ}
    (hp : p.Prime) :
    Summable fun k : ℕ ↦ ‖(‖singularTerm (p ^ k) n‖ : ℝ)‖ := by
  refine summable_of_hasFiniteSupport (((Set.finite_singleton (0 : ℕ)).insert 1).subset ?_)
  intro k hk
  simp only [Function.mem_support] at hk ⊢
  contrapose! hk
  rw [Real.norm_of_nonneg (norm_nonneg _)]
  exact norm_eq_zero.mpr (singularTerm_prime_pow_eq_zero_of_two_le hp (by
    by_contra hklt
    interval_cases k <;> simp at hk))

private lemma tsum_norm_singularTerm_prime_pow_le {p n : ℕ} (hp : p.Prime) :
    (∑' k : ℕ, ‖singularTerm (p ^ k) n‖) ≤
      1 + 4 * ((p : ℝ) ^ (-2 : ℝ)) := by
  have hsupport : ∀ k : ℕ, k ∉ ({0, 1} : Finset ℕ) →
      ‖singularTerm (p ^ k) n‖ = 0 := by
    intro k hk
    rw [norm_eq_zero]
    exact singularTerm_prime_pow_eq_zero_of_two_le hp (by
      by_contra hklt
      interval_cases k <;> simp at hk)
  rw [tsum_eq_sum hsupport]
  simp only [Finset.mem_singleton, Finset.sum_insert, Finset.sum_singleton,
    zero_ne_one, not_false_eq_true, Nat.pow_zero, Nat.pow_one]
  have hprime := norm_singularTerm_prime_le (p := p) (n := n) hp
  have hone : ‖singularTerm 1 n‖ = (1 : ℝ) := by simp [singularTerm_one]
  rw [hone]
  linarith

private lemma mem_factoredNumbers_primesBelow_of_mem_range_filter_ne_zero {N q : ℕ}
    (hq : q ∈ (Finset.range N).filter (fun q ↦ q ≠ 0)) :
    q ∈ Nat.factoredNumbers (Nat.primesBelow N) := by
  simp only [Finset.mem_filter, Finset.mem_range, ne_eq] at hq
  rw [Nat.mem_factoredNumbers_iff_primeFactors_subset]
  constructor
  · exact hq.2
  · intro p hp
    rw [Nat.mem_primesBelow]
    have hpdvd : p ∣ q := Nat.dvd_of_mem_primeFactors hp
    have hpprime : p.Prime := (Nat.mem_primeFactors.mp hp).1
    have hp_le_q : p ≤ q := Nat.le_of_dvd (Nat.pos_of_ne_zero hq.2) hpdvd
    exact ⟨lt_of_le_of_lt hp_le_q hq.1, hpprime⟩

/-- The Ramanujan denominator series is absolutely summable. -/
theorem summable_norm_singularTerm (n : ℕ) :
    Summable fun q : ℕ ↦ ‖singularTerm q n‖ := by
  classical
  let f : ℕ → ℝ := fun q ↦ ‖singularTerm q n‖
  have hf_nonneg : ∀ q, 0 ≤ f q := fun q ↦ norm_nonneg _
  have hf₁ : f 1 = 1 := by simp [f, singularTerm_one]
  have hf₀ : f 0 = 0 := by simp [f, singularTerm_zero]
  have hmul : ∀ {q₁ q₂ : ℕ}, q₁.Coprime q₂ → f (q₁ * q₂) = f q₁ * f q₂ := by
    intro q₁ q₂ hcop
    by_cases hq₁ : q₁ = 0
    · subst q₁
      simp [f, singularTerm_zero]
    by_cases hq₂ : q₂ = 0
    · subst q₂
      simp [f, singularTerm_zero]
    change ‖singularTerm (q₁ * q₂) n‖ = ‖singularTerm q₁ n‖ * ‖singularTerm q₂ n‖
    rw [singularTerm_mul_of_coprime (q₁ := q₁) (q₂ := q₂)
      (Nat.pos_of_ne_zero hq₁) (Nat.pos_of_ne_zero hq₂) hcop n, norm_mul]
  have hlocal : ∀ {p : ℕ}, p.Prime → Summable fun k : ℕ ↦ ‖f (p ^ k)‖ := by
    intro p hp
    simpa [f] using summable_norm_norm_singularTerm_prime_pow (p := p) (n := n) hp
  have hprimeSummable :
      Summable fun p : Nat.Primes ↦ 4 * ((p.val : ℝ) ^ (-2 : ℝ)) := by
    exact (Nat.Primes.summable_rpow.mpr (by norm_num : (-2 : ℝ) < -1)).mul_left 4
  let B : Nat.Primes → ℝ := fun p ↦ 1 + 4 * ((p.val : ℝ) ^ (-2 : ℝ))
  have hB : Multipliable B := by
    simpa [B] using Real.multipliable_one_add_of_summable hprimeSummable
  obtain ⟨C, _hCpos, sB, hBbound⟩ := hB.eventually_bounded_finsetProd
  have hsum_range_le : ∀ N : ℕ, ∑ q ∈ Finset.range N, f q ≤ C := by
    intro N
    let S : Finset ℕ := Nat.primesBelow N
    have hfact := EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_tsum
      (R := ℝ) (f := f) hf₁ hmul hlocal S
    have hfact_sum : Summable fun m : Nat.factoredNumbers S ↦ f m.val := by
      simpa [f, Real.norm_of_nonneg] using hfact.1
    let T : Finset ℕ := (Finset.range N).filter (fun q ↦ q ≠ 0)
    let e : {q // q ∈ T} → Nat.factoredNumbers S := fun q ↦
      ⟨q.val, by
        change q.val ∈ Nat.factoredNumbers (Nat.primesBelow N)
        exact mem_factoredNumbers_primesBelow_of_mem_range_filter_ne_zero
          (N := N) (q := q.val) q.property⟩
    have heinj : Function.Injective e := by
      intro a b hab
      apply Subtype.ext
      exact congrArg (fun x : Nat.factoredNumbers S ↦ x.val) hab
    have hA_sum : Summable fun q : {q // q ∈ T} ↦ f q.val := Summable.of_finite
    have hsub_le : (∑' q : {q // q ∈ T}, f q.val) ≤
        ∑' m : Nat.factoredNumbers S, f m.val := by
      refine Summable.tsum_le_tsum_of_inj e heinj ?_ ?_ hA_sum hfact_sum
      · intro c _hc
        exact hf_nonneg c.val
      · intro q
        rfl
    have hrange_eq_sub : (∑ q ∈ Finset.range N, f q) = ∑ q ∈ T, f q := by
      symm
      apply Finset.sum_subset
      · intro q hq
        exact Finset.mem_range.mpr (by simpa [T] using (Finset.mem_filter.mp hq).1)
      · intro q hqrange hqnotfilter
        simp only [T, Finset.mem_filter, hqrange, true_and, not_not] at hqnotfilter
        rw [hqnotfilter, hf₀]
    have hsub_eq : (∑' q : {q // q ∈ T}, f q.val) = ∑ q ∈ T, f q := by
      rw [tsum_fintype]
      exact Finset.sum_attach _ _
    have hfact_tsum_eq : (∑' m : Nat.factoredNumbers S, f m.val) =
        ∏ p ∈ S with p.Prime, ∑' k : ℕ, f (p ^ k) := hfact.2.tsum_eq
    have hfilter : S.filter (fun p ↦ p.Prime) = S := by
      apply Finset.filter_true_of_mem
      intro p hpS
      exact (Nat.mem_primesBelow.mp (by simpa [S] using hpS)).2
    have hprod_le : (∏ p ∈ S with p.Prime, ∑' k : ℕ, f (p ^ k)) ≤
        ∏ p ∈ S, (1 + 4 * ((p : ℝ) ^ (-2 : ℝ))) := by
      rw [hfilter]
      refine Finset.prod_le_prod ?_ ?_
      · intro p _hpS
        exact tsum_nonneg (fun k ↦ hf_nonneg (p ^ k))
      · intro p hpS
        exact tsum_norm_singularTerm_prime_pow_le (p := p) (n := n)
          ((Nat.mem_primesBelow.mp (by simpa [S] using hpS)).2)
    let emb : {p // p ∈ S} ↪ Nat.Primes :=
      { toFun := fun p ↦ ⟨p.val, (Nat.mem_primesBelow.mp p.property).2⟩
        inj' := by
          intro a b hab
          apply Subtype.ext
          exact congrArg (fun x : Nat.Primes ↦ x.val) hab }
    let Ssub : Finset Nat.Primes := S.attach.map emb
    have hprod_eq_sub :
        (∏ p ∈ S, (1 + 4 * ((p : ℝ) ^ (-2 : ℝ)))) = ∏ p ∈ Ssub, B p := by
      calc
        ∏ p ∈ S, (1 + 4 * ((p : ℝ) ^ (-2 : ℝ))) =
            ∏ x ∈ S.attach, (1 + 4 * ((x.val : ℝ) ^ (-2 : ℝ))) :=
              (Finset.prod_attach S (fun p ↦ 1 + 4 * ((p : ℝ) ^ (-2 : ℝ)))).symm
        _ = ∏ x ∈ S.attach, B (emb x) := by rfl
        _ = ∏ p ∈ Ssub, B p := by
          exact (Finset.prod_map (s := S.attach) (f := fun p ↦ B p) emb).symm
    have hB_nonneg : ∀ p : Nat.Primes, 0 ≤ B p := by
      intro p
      have hrp : 0 ≤ (p.val : ℝ) ^ (-2 : ℝ) := Real.rpow_nonneg (Nat.cast_nonneg _) _
      dsimp [B]
      nlinarith
    have hB_one_le : ∀ p : Nat.Primes, 1 ≤ B p := by
      intro p
      have hrp : 0 ≤ (p.val : ℝ) ^ (-2 : ℝ) := Real.rpow_nonneg (Nat.cast_nonneg _) _
      dsimp [B]
      nlinarith
    have hsub_prod_le_C : (∏ p ∈ Ssub, B p) ≤ C := by
      calc
        ∏ p ∈ Ssub, B p ≤ ∏ p ∈ Ssub ∪ sB, B p := by
          exact Finset.prod_le_prod_of_subset_of_one_le
            Finset.subset_union_left (fun p _ ↦ hB_nonneg p) (fun p _ _ ↦ hB_one_le p)
        _ ≤ C := hBbound (Ssub ∪ sB) Finset.subset_union_right
    calc
      ∑ q ∈ Finset.range N, f q = ∑ q ∈ T, f q := hrange_eq_sub
      _ = ∑' q : {q // q ∈ T}, f q.val := hsub_eq.symm
      _ ≤ ∑' m : Nat.factoredNumbers S, f m.val := hsub_le
      _ = ∏ p ∈ S with p.Prime, ∑' k : ℕ, f (p ^ k) := hfact_tsum_eq
      _ ≤ ∏ p ∈ S, (1 + 4 * ((p : ℝ) ^ (-2 : ℝ))) := hprod_le
      _ = ∏ p ∈ Ssub, B p := hprod_eq_sub
      _ ≤ C := hsub_prod_le_C
  simpa [f] using summable_of_sum_range_le hf_nonneg hsum_range_le

/-- A Ramanujan sum is bounded by the number of reduced residue classes.
This elementary estimate is deliberately stated here because, at frequency
zero, it turns the already-proved denominator series into a majorant uniform
in the target integer. -/
theorem norm_ramanujanSum_le_totient (q n : ℕ) :
    ‖Vinogradov.ramanujanSum q n‖ ≤ (Nat.totient q : ℝ) := by
  unfold Vinogradov.ramanujanSum
  calc
    ‖∑ a ∈ (Finset.range q).filter (fun a ↦ Nat.Coprime a q),
        Vinogradov.addChar ((n : ℝ) / (q : ℝ)) a‖
        ≤ ∑ a ∈ (Finset.range q).filter (fun a ↦ Nat.Coprime a q),
            ‖Vinogradov.addChar ((n : ℝ) / (q : ℝ)) a‖ :=
          norm_sum_le _ _
    _ = ((Finset.range q).filter (fun a ↦ Nat.Coprime a q)).card := by
          simp [Vinogradov.norm_addChar]
    _ = (Nat.totient q : ℝ) := by
          have hfilter :
              (Finset.range q).filter (fun a ↦ Nat.Coprime a q) =
                (Finset.range q).filter (fun a ↦ Nat.Coprime q a) := by
            ext a
            simp [Nat.coprime_comm]
          rw [hfilter]
          rw [Nat.totient_eq_card_coprime]

/-- At frequency zero the Ramanujan sum is exactly `φ(q)`. -/
theorem ramanujanSum_zero_frequency (q : ℕ) :
    Vinogradov.ramanujanSum q 0 = (Nat.totient q : ℂ) := by
  unfold Vinogradov.ramanujanSum
  simp only [Nat.cast_zero, zero_div, Vinogradov.addChar_zero_left,
    Finset.sum_const, nsmul_eq_mul, mul_one]
  have hfilter :
      (Finset.range q).filter (fun a ↦ Nat.Coprime a q) =
        (Finset.range q).filter (fun a ↦ Nat.Coprime q a) := by
    ext a
    simp [Nat.coprime_comm]
  rw [hfilter]
  rw [Nat.totient_eq_card_coprime]

/-- The zero-frequency denominator term is a pointwise majorant for every
target frequency. -/
theorem norm_singularTerm_le_zero_frequency (q n : ℕ) :
    ‖singularTerm q n‖ ≤ ‖singularTerm q 0‖ := by
  let C : ℂ := (((((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 3) /
      (Nat.totient q : ℝ) ^ 3 : ℝ) : ℂ)
  change ‖C * Vinogradov.ramanujanSum q n‖ ≤
    ‖C * Vinogradov.ramanujanSum q 0‖
  rw [norm_mul, norm_mul, ramanujanSum_zero_frequency]
  have hram := norm_ramanujanSum_le_totient q n
  simpa using mul_le_mul_of_nonneg_left hram (norm_nonneg C)

/-- One summable sequence majorizes all target-dependent singular-series
terms.  This is the uniform denominator-tail input used in the qualitative
major-arc argument. -/
theorem summable_uniform_singularMajorant :
    Summable fun q : ℕ ↦ ‖singularTerm q 0‖ :=
  summable_norm_singularTerm 0

lemma tsum_singularTerm_eq_tprod_prime_pow (n : ℕ) :
    (∑' q : ℕ, singularTerm q n) =
      ∏' p : Nat.Primes, ∑' k : ℕ, singularTerm (p.val ^ k) n := by
  let f : ℕ → ℂ := fun q ↦ singularTerm q n
  have hf₁ : f 1 = 1 := by simp [f, singularTerm_one]
  have hf₀ : f 0 = 0 := by simp [f, singularTerm_zero]
  have hmul : ∀ {q₁ q₂ : ℕ}, q₁.Coprime q₂ → f (q₁ * q₂) = f q₁ * f q₂ := by
    intro q₁ q₂ hcop
    by_cases hq₁ : q₁ = 0
    · subst q₁
      simp [f, singularTerm_zero]
    by_cases hq₂ : q₂ = 0
    · subst q₂
      simp [f, singularTerm_zero]
    exact singularTerm_mul_of_coprime (q₁ := q₁) (q₂ := q₂)
      (Nat.pos_of_ne_zero hq₁) (Nat.pos_of_ne_zero hq₂) hcop n
  have heuler := EulerProduct.eulerProduct_tprod (R := ℂ) (f := f)
    hf₁ hmul (summable_norm_singularTerm n) hf₀
  simpa [f] using heuler.symm

/-- The full denominator series equals twice the normalized singular series. -/
theorem tsum_singularTerm_eq_two_singularSeries {n : ℕ} (hodd : Odd n) :
    ∑' q : ℕ, singularTerm q n = 2 * (singularSeries n : ℂ) := by
  rw [tsum_singularTerm_eq_tprod_prime_pow n,
    tprod_singularTerm_prime_pow_eq_two_singularSeries hodd]

end VinogradovsTheorem.Analytic
