/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ErdosProblems.Erdos697.Erdos697CRTModel

/-!
# Finite CRT transfer for Erdős Problem 144

This file contains the deterministic part of the finite prime-block model.
It turns selected CRT zero coordinates into divisors, proves that different
sets of distinct primes give different products, and converts a logarithmic
distance strictly smaller than `log 2` into the strict factor-two inequality.

The probabilistic and density estimates are deliberately kept out of this
file.
-/

open scoped BigOperators

namespace Erdos144.CRTClose

noncomputable section

/-- The literal divisor-pair predicate occurring in Erdős Problem 144. -/
def HasCloseDivisors (n : ℕ) : Prop :=
  ∃ d₁ d₂ : ℕ, d₁ ∣ n ∧ d₂ ∣ n ∧ d₁ < d₂ ∧ d₂ < 2 * d₁

/-- Product of the primes whose indices belong to `A`. -/
def primeProduct {ι : Type*} [DecidableEq ι] (p : ι → ℕ)
    (A : Finset ι) : ℕ :=
  ∏ i ∈ A, p i

variable {ι : Type*} [DecidableEq ι]
variable {p : ι → ℕ} {A B S : Finset ι} {n : ℕ}

@[simp] theorem primeProduct_empty : primeProduct p ∅ = 1 := by
  simp [primeProduct]

theorem primeProduct_pos (hprime : ∀ i ∈ A, (p i).Prime) :
    0 < primeProduct p A := by
  exact Finset.prod_pos fun i hi ↦ (hprime i hi).pos

/-- Distinct indexed primes are pairwise coprime. -/
theorem coprime_of_distinct_indices
    (hprime : ∀ i, (p i).Prime) (hinj : Function.Injective p)
    {i j : ι} (hij : i ≠ j) :
    Nat.Coprime (p i) (p j) := by
  exact (hprime i).coprime_iff_not_dvd.mpr fun hdvd ↦
    hij (hinj ((Nat.prime_dvd_prime_iff_eq (hprime i) (hprime j)).mp hdvd))

/-- Global pairwise-coprimality form needed by `ZMod.prodEquivPi`. -/
theorem primeFamily_pairwise_coprime
    (hprime : ∀ i, (p i).Prime) (hinj : Function.Injective p) :
    Pairwise (Function.onFun Nat.Coprime p) := by
  intro i j hij
  exact coprime_of_distinct_indices hprime hinj hij

/-- A product of pairwise distinct primes divides `n` if every factor does. -/
theorem primeProduct_dvd
    (hprime : ∀ i, (p i).Prime) (hinj : Function.Injective p)
    (hdvd : ∀ i ∈ A, p i ∣ n) :
    primeProduct p A ∣ n := by
  induction A using Finset.induction_on with
  | empty => simp [primeProduct]
  | @insert a T ha ih =>
      rw [primeProduct, Finset.prod_insert ha]
      have hcop : Nat.Coprime (p a) (∏ i ∈ T, p i) := by
        apply Nat.Coprime.prod_right
        intro i hi
        exact coprime_of_distinct_indices hprime hinj
          (fun hai ↦ ha (hai ▸ hi))
      apply hcop.mul_dvd_of_dvd_of_dvd
      · exact hdvd a (Finset.mem_insert_self a T)
      · apply ih
        intro i hi
        exact hdvd i (Finset.mem_insert_of_mem hi)

/-- The subset form used when `S` is the selected CRT zero set. -/
theorem primeProduct_dvd_of_subset
    (hprime : ∀ i, (p i).Prime) (hinj : Function.Injective p)
    (hAS : A ⊆ S) (hdvd : ∀ i ∈ S, p i ∣ n) :
    primeProduct p A ∣ n := by
  exact primeProduct_dvd hprime hinj fun i hi ↦ hdvd i (hAS hi)

/-- Unique factorization: different finite sets of distinct indexed primes
have different products. -/
theorem primeProduct_injective
    (hprime : ∀ i, (p i).Prime) (hinj : Function.Injective p) :
    Function.Injective (primeProduct p) := by
  intro U V huv
  have hprodU : (U.image p).prod id = primeProduct p U := by
    simpa [primeProduct] using
      (Finset.prod_image (f := id) (g := p) (s := U)
        (fun i _ j _ hij ↦ hinj hij))
  have hprodV : (V.image p).prod id = primeProduct p V := by
    simpa [primeProduct] using
      (Finset.prod_image (f := id) (g := p) (s := V)
        (fun i _ j _ hij ↦ hinj hij))
  have hU : (primeProduct p U).primeFactors = U.image p := by
    rw [← hprodU]
    exact Nat.primeFactors_prod fun q hq ↦ by
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hq
      exact hprime i
  have hV : (primeProduct p V).primeFactors = V.image p := by
    rw [← hprodV]
    exact Nat.primeFactors_prod fun q hq ↦ by
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hq
      exact hprime i
  apply (Finset.image_inj hinj).mp
  rw [← hU, ← hV, huv]

theorem primeProduct_ne_of_ne
    (hprime : ∀ i, (p i).Prime) (hinj : Function.Injective p)
    (hAB : A ≠ B) :
    primeProduct p A ≠ primeProduct p B :=
  fun h ↦ hAB (primeProduct_injective hprime hinj h)

/-- The logarithm of an indexed prime product is the corresponding sum of
prime logarithms. -/
theorem log_primeProduct
    (hprime : ∀ i ∈ A, (p i).Prime) :
    Real.log (primeProduct p A : ℝ) =
      ∑ i ∈ A, Real.log (p i : ℝ) := by
  rw [primeProduct, Nat.cast_prod, Real.log_prod]
  intro i hi
  exact_mod_cast (hprime i hi).ne_zero

/-- If every selected prime logarithm lies within `δ` of its block center
and two selections have the same sum of block centers, their product
logarithms differ by at most the total number of selected primes times
`δ`. -/
theorem abs_log_primeProduct_sub_le_of_approx
    (hprime : ∀ i, (p i).Prime) (w : ι → ℝ) {δ : ℝ}
    (happrox : ∀ i ∈ A ∪ B, |Real.log (p i : ℝ) - w i| ≤ δ)
    (hsum : (∑ i ∈ A, w i) = ∑ i ∈ B, w i) :
    |Real.log (primeProduct p A : ℝ) -
        Real.log (primeProduct p B : ℝ)| ≤
      ((A.card + B.card : ℕ) : ℝ) * δ := by
  have herrA :
      |∑ i ∈ A, (Real.log (p i : ℝ) - w i)| ≤ (A.card : ℝ) * δ := by
    calc
      |∑ i ∈ A, (Real.log (p i : ℝ) - w i)| ≤
          ∑ i ∈ A, |Real.log (p i : ℝ) - w i| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i ∈ A, δ := by
        exact Finset.sum_le_sum fun i hi ↦
          happrox i (Finset.mem_union_left B hi)
      _ = (A.card : ℝ) * δ := by simp
  have herrB :
      |∑ i ∈ B, (Real.log (p i : ℝ) - w i)| ≤ (B.card : ℝ) * δ := by
    calc
      |∑ i ∈ B, (Real.log (p i : ℝ) - w i)| ≤
          ∑ i ∈ B, |Real.log (p i : ℝ) - w i| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i ∈ B, δ := by
        exact Finset.sum_le_sum fun i hi ↦
          happrox i (Finset.mem_union_right A hi)
      _ = (B.card : ℝ) * δ := by simp
  rw [log_primeProduct (fun i _ ↦ hprime i),
    log_primeProduct (fun i _ ↦ hprime i)]
  have hrearrange :
      (∑ i ∈ A, Real.log (p i : ℝ)) -
          ∑ i ∈ B, Real.log (p i : ℝ) =
        (∑ i ∈ A, (Real.log (p i : ℝ) - w i)) -
          ∑ i ∈ B, (Real.log (p i : ℝ) - w i) := by
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, hsum]
    ring
  rw [hrearrange]
  calc
    |(∑ i ∈ A, (Real.log (p i : ℝ) - w i)) -
        ∑ i ∈ B, (Real.log (p i : ℝ) - w i)| ≤
      |∑ i ∈ A, (Real.log (p i : ℝ) - w i)| +
        |∑ i ∈ B, (Real.log (p i : ℝ) - w i)| := abs_sub _ _
    _ ≤ (A.card : ℝ) * δ + (B.card : ℝ) * δ :=
      add_le_add herrA herrB
    _ = ((A.card + B.card : ℕ) : ℝ) * δ := by
      push_cast
      ring

/-! ## CRT zero coordinates -/

variable [Fintype ι] [(i : ι) → NeZero (p i)]

/-- Under the CRT equivalence, coordinate `i` is zero exactly when its
modulus divides the sampled natural number. -/
theorem mem_crtZeroSet_iff_dvd
    (hprime : ∀ i, (p i).Prime) (hinj : Function.Injective p)
    (i : ι) (n : ℕ) :
    i ∈ Erdos697.CRTModel.zeroSet p
        (ZMod.prodEquivPi p
          (primeFamily_pairwise_coprime hprime hinj)
          (n : ZMod (∏ i, p i))) ↔
      p i ∣ n := by
  rw [Erdos697.CRTModel.mem_zeroSet]
  simp only [ZMod.prodEquivPi_apply, map_natCast]
  exact ZMod.natCast_eq_zero_iff n (p i)

/-- Every prime indexed by a subset of the CRT zero set contributes to a
genuine divisor of the sampled integer. -/
theorem primeProduct_dvd_of_subset_crtZeroSet
    (hprime : ∀ i, (p i).Prime) (hinj : Function.Injective p)
    {A : Finset ι} {n : ℕ}
    (hA : A ⊆ Erdos697.CRTModel.zeroSet p
      (ZMod.prodEquivPi p
        (primeFamily_pairwise_coprime hprime hinj)
        (n : ZMod (∏ i, p i)))) :
    primeProduct p A ∣ n := by
  apply primeProduct_dvd hprime hinj
  intro i hi
  exact (mem_crtZeroSet_iff_dvd hprime hinj i n).mp (hA hi)

/-! ## Logarithmic distance and the factor-two conclusion -/

/-- Positive unequal natural numbers whose logarithms differ by less than
`log 2` can be ordered to give the strict factor-two inequalities. -/
theorem hasCloseDivisors_of_abs_log_sub_lt_log_two
    {d e n : ℕ} (hd : d ∣ n) (he : e ∣ n)
    (hdpos : 0 < d) (hepos : 0 < e) (hne : d ≠ e)
    (hlog : |Real.log (d : ℝ) - Real.log (e : ℝ)| < Real.log 2) :
    HasCloseDivisors n := by
  have hratio_de : (d : ℝ) < 2 * e := by
    have hde : Real.log (d : ℝ) - Real.log (e : ℝ) < Real.log 2 :=
      lt_of_le_of_lt (le_abs_self _) hlog
    have hdR : (0 : ℝ) < d := by exact_mod_cast hdpos
    have heR : (0 : ℝ) < e := by exact_mod_cast hepos
    rw [sub_lt_iff_lt_add, ← Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) heR.ne'] at hde
    exact (Real.strictMonoOn_log.lt_iff_lt hdR
      (mul_pos (by norm_num) heR)).mp hde
  have hratio_ed : (e : ℝ) < 2 * d := by
    have hed : Real.log (e : ℝ) - Real.log (d : ℝ) < Real.log 2 := by
      have hneg : -(Real.log (d : ℝ) - Real.log (e : ℝ)) < Real.log 2 :=
        lt_of_le_of_lt (neg_le_abs _) hlog
      linarith
    have hdR : (0 : ℝ) < d := by exact_mod_cast hdpos
    have heR : (0 : ℝ) < e := by exact_mod_cast hepos
    rw [sub_lt_iff_lt_add, ← Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hdR.ne'] at hed
    exact (Real.strictMonoOn_log.lt_iff_lt heR
      (mul_pos (by norm_num) hdR)).mp hed
  rcases lt_or_gt_of_ne hne with hde | hed
  · exact ⟨d, e, hd, he, hde, by exact_mod_cast hratio_ed⟩
  · exact ⟨e, d, he, hd, hed, by exact_mod_cast hratio_de⟩

/-- Prime-product specialization of the logarithmic bridge. -/
theorem hasCloseDivisors_of_primeProducts
    (hprime : ∀ i, (p i).Prime) (hinj : Function.Injective p)
    (hA : ∀ i ∈ A, p i ∣ n) (hB : ∀ i ∈ B, p i ∣ n)
    (hAB : A ≠ B)
    (hlog : |Real.log (primeProduct p A : ℝ) -
        Real.log (primeProduct p B : ℝ)| < Real.log 2) :
    HasCloseDivisors n := by
  apply hasCloseDivisors_of_abs_log_sub_lt_log_two
    (primeProduct_dvd hprime hinj hA)
    (primeProduct_dvd hprime hinj hB)
    (primeProduct_pos fun i hi ↦ hprime i)
    (primeProduct_pos fun i hi ↦ hprime i)
    (primeProduct_ne_of_ne hprime hinj hAB)
    hlog

/-- Direct CRT specialization: two different subsets of the zero set whose
prime products are logarithmically close give the desired divisor pair. -/
theorem hasCloseDivisors_of_crtPrimeProducts
    (hprime : ∀ i, (p i).Prime) (hinj : Function.Injective p)
    {A B : Finset ι} {n : ℕ}
    (hA : A ⊆ Erdos697.CRTModel.zeroSet p
      (ZMod.prodEquivPi p (primeFamily_pairwise_coprime hprime hinj)
        (n : ZMod (∏ i, p i))))
    (hB : B ⊆ Erdos697.CRTModel.zeroSet p
      (ZMod.prodEquivPi p (primeFamily_pairwise_coprime hprime hinj)
        (n : ZMod (∏ i, p i))))
    (hAB : A ≠ B)
    (hlog : |Real.log (primeProduct p A : ℝ) -
        Real.log (primeProduct p B : ℝ)| < Real.log 2) :
    HasCloseDivisors n := by
  apply hasCloseDivisors_of_abs_log_sub_lt_log_two
    (primeProduct_dvd_of_subset_crtZeroSet hprime hinj hA)
    (primeProduct_dvd_of_subset_crtZeroSet hprime hinj hB)
    (primeProduct_pos fun i hi ↦ hprime i)
    (primeProduct_pos fun i hi ↦ hprime i)
    (primeProduct_ne_of_ne hprime hinj hAB)
    hlog

/-- Block-center form of the direct CRT specialization.  This is the final
deterministic interface needed from a finite equal-sums event. -/
theorem hasCloseDivisors_of_crtPrimeProducts_of_approx
    (hprime : ∀ i, (p i).Prime) (hinj : Function.Injective p)
    {A B : Finset ι} {n : ℕ} (w : ι → ℝ) {δ : ℝ}
    (hA : A ⊆ Erdos697.CRTModel.zeroSet p
      (ZMod.prodEquivPi p (primeFamily_pairwise_coprime hprime hinj)
        (n : ZMod (∏ i, p i))))
    (hB : B ⊆ Erdos697.CRTModel.zeroSet p
      (ZMod.prodEquivPi p (primeFamily_pairwise_coprime hprime hinj)
        (n : ZMod (∏ i, p i))))
    (hAB : A ≠ B)
    (happrox : ∀ i ∈ A ∪ B, |Real.log (p i : ℝ) - w i| ≤ δ)
    (hsum : (∑ i ∈ A, w i) = ∑ i ∈ B, w i)
    (hsmall : ((A.card + B.card : ℕ) : ℝ) * δ < Real.log 2) :
    HasCloseDivisors n := by
  apply hasCloseDivisors_of_crtPrimeProducts hprime hinj hA hB hAB
  exact (abs_log_primeProduct_sub_le_of_approx hprime w happrox hsum).trans_lt hsmall

end

end Erdos144.CRTClose
