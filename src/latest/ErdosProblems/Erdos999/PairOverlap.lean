/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ErdosProblems.Erdos999.CongruenceReduction
import ErdosProblems.Erdos999.CoprimeInterval
import ErdosProblems.Erdos999.SignedInterval
import ErdosProblems.Erdos999.TotientProducts

/-!
# The Pollington--Vaughan pair-overlap estimate

This file combines the congruence-fibre calculation with the weighted
coprime-interval sieve.  The elementary geometry and CRT calculations are
kept in their respective helper files; here we isolate the Euler-product
majorant and assemble the resulting absolute bound.
-/

open scoped BigOperators

namespace Erdos999

noncomputable section

/-- Primes in the common part of two moduli which do not occur in either
coprime quotient. -/
def freshCommonPrimes (g u : ℕ) : Finset ℕ :=
  g.primeFactors.filter fun p ↦ ¬ p ∣ u

/-- The two Euler-factor products occurring in the common-part density. -/
def pairLocalDensityProduct (g u : ℕ) : ℝ :=
  (∏ p ∈ g.primeFactors.filter (fun p ↦ p ∣ u),
      (1 - (p : ℝ)⁻¹)) *
    ∏ p ∈ freshCommonPrimes g u, (1 - (p : ℝ)⁻¹) ^ 2

lemma freshCommonPrimes_prime {g u p : ℕ}
    (hp : p ∈ freshCommonPrimes g u) : p.Prime := by
  exact Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1

lemma primeFactors_disjoint_freshCommonPrimes (g u : ℕ) :
    Disjoint u.primeFactors (freshCommonPrimes g u) := by
  rw [Finset.disjoint_left]
  intro p hpu hpf
  exact (Finset.mem_filter.mp hpf).2 (Nat.dvd_of_mem_primeFactors hpu)

/-- The radical condition required by the weighted interval sieve follows
from the half-unit lower bounds on both anisotropic radii. -/
lemma prod_primeFactors_mul_le_ceil_sq
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b) {L M : ℝ}
    (hL : (1 : ℝ) / 2 ≤ L) (hM : (1 : ℝ) / 2 ≤ M) :
    (∏ p ∈ (a * b).primeFactors, p) ≤
      (Nat.ceil ((b : ℝ) * L + (a : ℝ) * M)) ^ 2 := by
  let X : ℝ := (b : ℝ) * L + (a : ℝ) * M
  let K : ℕ := Nat.ceil X
  have haR : 0 < (a : ℝ) := by positivity
  have hbR : 0 < (b : ℝ) := by positivity
  have hXlower : ((a : ℝ) + b) / 2 ≤ X := by
    dsimp [X]
    nlinarith
  have hX : 0 ≤ X := le_trans (by positivity) hXlower
  have hK : X ≤ (K : ℕ) := by
    exact Nat.le_ceil X
  have habX : ((a * b : ℕ) : ℝ) ≤ X ^ 2 := by
    push_cast
    nlinarith [sq_nonneg ((a : ℝ) - b)]
  have habKReal : ((a * b : ℕ) : ℝ) ≤ ((K ^ 2 : ℕ) : ℝ) := by
    calc
      ((a * b : ℕ) : ℝ) ≤ X ^ 2 := habX
      _ ≤ (K : ℝ) ^ 2 := (sq_le_sq₀ hX (by positivity)).2 hK
      _ = ((K ^ 2 : ℕ) : ℝ) := by norm_num
  have habK : a * b ≤ K ^ 2 := by exact_mod_cast habKReal
  have hradDvd : (∏ p ∈ (a * b).primeFactors, p) ∣ a * b :=
    Nat.prod_primeFactors_dvd (a * b)
  have hradPos : 0 < ∏ p ∈ (a * b).primeFactors, p := by
    exact Finset.prod_pos fun p hp ↦ Nat.pos_of_mem_primeFactors hp
  simpa [X, K] using (Nat.le_trans (Nat.le_of_dvd (mul_pos ha hb) hradDvd) habK)

private def pairEqualPrimeFactor (g c p : ℕ) : ℕ :=
  p ^ (g.factorization p - 1) * (if p ∣ c then p - 1 else p - 2)

private def pairCongruenceLocalProduct (g u c : ℕ) : ℕ :=
  if u.Coprime c then
    (∏ p ∈ g.primeFactors.filter (fun p ↦ p ∣ u),
        p ^ (g.factorization p - 1) * (p - 1)) *
      ∏ p ∈ freshCommonPrimes g u, pairEqualPrimeFactor g c p
  else 0

private lemma equalPrimeFactor_cast_le
    {g c p : ℕ} (hg : 0 < g) (hp : p.Prime) (hpg : p ∣ g) :
    (pairEqualPrimeFactor g c p : ℝ) ≤
      (p : ℝ) ^ g.factorization p * (1 - (p : ℝ)⁻¹) ^ 2 *
        (if p ∣ c then (1 - (p : ℝ)⁻¹)⁻¹ else 1) := by
  have hv : 0 < g.factorization p := hp.factorization_pos_of_dvd hg.ne' hpg
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hp1R : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_le
  have hfac :
      (p : ℝ) ^ (g.factorization p - 1) * p =
        (p : ℝ) ^ g.factorization p := by
    rw [← pow_succ]
    congr 2
    omega
  by_cases hpc : p ∣ c
  · rw [if_pos hpc]
    simp only [pairEqualPrimeFactor, hpc, if_pos, Nat.cast_mul, Nat.cast_pow,
      Nat.cast_sub hp.one_le]
    have he : 1 - (p : ℝ)⁻¹ ≠ 0 := by
      rw [sub_ne_zero]
      simpa [inv_eq_one] using hp.ne_one
    have heq :
        (p : ℝ) ^ g.factorization p * (1 - (p : ℝ)⁻¹) ^ 2 *
            (1 - (p : ℝ)⁻¹)⁻¹ =
          (p : ℝ) ^ (g.factorization p - 1) * (p - 1) := by
      rw [sq]
      field_simp [hpR.ne', he]
      nlinarith [hfac]
    simpa only [Nat.cast_one] using le_of_eq heq.symm
  · rw [if_neg hpc]
    simp only [pairEqualPrimeFactor, hpc, if_false, Nat.cast_mul, Nat.cast_pow,
      mul_one]
    rw [Nat.cast_sub hp.two_le]
    rw [show (1 - (p : ℝ)⁻¹) = (p - 1) / p by field_simp]
    have hpow : 0 ≤ (p : ℝ) ^ (g.factorization p - 1) := by positivity
    rw [show (p : ℝ) ^ g.factorization p =
      (p : ℝ) ^ (g.factorization p - 1) * p by simpa using hfac.symm]
    calc
      (p : ℝ) ^ (g.factorization p - 1) * (p - 2) ≤
          (p : ℝ) ^ (g.factorization p - 1) * ((p - 1) ^ 2 / p) := by
        apply mul_le_mul_of_nonneg_left _ hpow
        rw [le_div_iff₀ hpR]
        nlinarith
      _ = ((p : ℝ) ^ (g.factorization p - 1) * p) *
          ((p - 1) / p) ^ 2 := by field_simp

private lemma unequalPrimeFactor_cast_eq
    {g p : ℕ} (hg : 0 < g) (hp : p.Prime) (hpg : p ∣ g) :
    ((p ^ (g.factorization p - 1) * (p - 1) : ℕ) : ℝ) =
      (p : ℝ) ^ g.factorization p * (1 - (p : ℝ)⁻¹) := by
  have hv : 0 < g.factorization p := hp.factorization_pos_of_dvd hg.ne' hpg
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_sub hp.one_le]
  rw [show (1 - (p : ℝ)⁻¹) = (p - 1) / p by field_simp]
  rw [show (p : ℝ) ^ g.factorization p =
    (p : ℝ) ^ (g.factorization p - 1) * p by
      rw [← pow_succ]
      congr 2
      omega]
  field_simp
  norm_num

private lemma prod_indicator_eq_primeWeight
    (S : Finset ℕ) (c : ℕ) :
    (∏ p ∈ S,
      if p ∣ c then (1 - (p : ℝ)⁻¹)⁻¹ else 1) =
      coprimeIntervalPrimeWeight S c := by
  classical
  rw [coprimeIntervalPrimeWeight, Finset.prod_filter]

private lemma prod_primePowers_split (g u : ℕ) :
    (∏ p ∈ g.primeFactors.filter (fun p ↦ p ∣ u),
        (p : ℝ) ^ g.factorization p) *
      (∏ p ∈ freshCommonPrimes g u,
        (p : ℝ) ^ g.factorization p) =
      ∏ p ∈ g.primeFactors, (p : ℝ) ^ g.factorization p := by
  classical
  exact Finset.prod_filter_mul_prod_filter_not g.primeFactors
    (fun p ↦ p ∣ u) (fun p ↦ (p : ℝ) ^ g.factorization p)

private lemma prod_primePowers_eq (g : ℕ) (hg : 0 < g) :
    (∏ p ∈ g.primeFactors, (p : ℝ) ^ g.factorization p) = g := by
  exact_mod_cast Nat.prod_factorization_pow_eq_self hg.ne'

/-- The local CRT product is bounded by the common modulus times its two
Euler densities and the residual Pollington--Vaughan divisibility weight. -/
lemma pairCongruenceLocalProduct_cast_le
    {g u c : ℕ} (hg : 0 < g) :
    (pairCongruenceLocalProduct g u c : ℝ) ≤
      if u.Coprime c then
        g * pairLocalDensityProduct g u * coprimeIntervalPrimeWeight
          (freshCommonPrimes g u) c
      else 0 := by
  classical
  by_cases huc : u.Coprime c
  · rw [if_pos huc, pairCongruenceLocalProduct, if_pos huc]
    push_cast
    let P := g.primeFactors.filter fun p ↦ p ∣ u
    let S := freshCommonPrimes g u
    change
      (∏ p ∈ P,
          (p : ℝ) ^ (g.factorization p - 1) * ((p - 1 : ℕ) : ℝ)) *
        (∏ p ∈ S, (pairEqualPrimeFactor g c p : ℝ)) ≤
      (g : ℝ) * pairLocalDensityProduct g u *
        coprimeIntervalPrimeWeight (freshCommonPrimes g u) c
    have hunequal :
        (∏ p ∈ P,
          (p : ℝ) ^ (g.factorization p - 1) * ((p - 1 : ℕ) : ℝ)) =
          (∏ p ∈ P,
            (p : ℝ) ^ g.factorization p * (1 - (p : ℝ)⁻¹)) := by
      apply Finset.prod_congr rfl
      intro p hpP
      simpa only [Nat.cast_mul, Nat.cast_pow] using
        unequalPrimeFactor_cast_eq hg
          (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hpP).1)
          (Nat.dvd_of_mem_primeFactors (Finset.mem_filter.mp hpP).1)
    have hequal :
        (∏ p ∈ S, (pairEqualPrimeFactor g c p : ℝ)) ≤
          ∏ p ∈ S,
            ((p : ℝ) ^ g.factorization p * (1 - (p : ℝ)⁻¹) ^ 2 *
              (if p ∣ c then (1 - (p : ℝ)⁻¹)⁻¹ else 1)) := by
      apply Finset.prod_le_prod
      · intro p hpS
        positivity
      · intro p hpS
        exact equalPrimeFactor_cast_le hg (freshCommonPrimes_prime hpS)
          (Nat.dvd_of_mem_primeFactors (Finset.mem_filter.mp hpS).1)
    have hprodPnonneg : 0 ≤
        ∏ p ∈ P, (p : ℝ) ^ g.factorization p * (1 - (p : ℝ)⁻¹) := by
      apply Finset.prod_nonneg
      intro p hpP
      have hpPrime : p.Prime :=
        Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hpP).1
      exact mul_nonneg (by positivity)
        (sub_nonneg.mpr (inv_le_one_of_one_le₀ (by exact_mod_cast hpPrime.one_le)))
    have hpowers :
        (∏ p ∈ P, (p : ℝ) ^ g.factorization p) *
            (∏ p ∈ S, (p : ℝ) ^ g.factorization p) = g := by
      rw [show P = g.primeFactors.filter (fun p ↦ p ∣ u) by rfl,
        show S = freshCommonPrimes g u by rfl,
        prod_primePowers_split, prod_primePowers_eq g hg]
    rw [hunequal]
    calc
      (∏ p ∈ P,
          (p : ℝ) ^ g.factorization p * (1 - (p : ℝ)⁻¹)) *
          (∏ p ∈ S, (pairEqualPrimeFactor g c p : ℝ)) ≤
        (∏ p ∈ P,
          (p : ℝ) ^ g.factorization p * (1 - (p : ℝ)⁻¹)) *
          (∏ p ∈ S,
            ((p : ℝ) ^ g.factorization p * (1 - (p : ℝ)⁻¹) ^ 2 *
              (if p ∣ c then (1 - (p : ℝ)⁻¹)⁻¹ else 1))) := by
        exact mul_le_mul_of_nonneg_left hequal hprodPnonneg
      _ = g * pairLocalDensityProduct g u *
          coprimeIntervalPrimeWeight (freshCommonPrimes g u) c := by
        simp only [Finset.prod_mul_distrib]
        rw [prod_indicator_eq_primeWeight]
        simp only [pairLocalDensityProduct]
        rw [show g.primeFactors.filter (fun p ↦ p ∣ u) = P by rfl,
          show freshCommonPrimes g u = S by rfl]
        calc
          _ = (((∏ x ∈ P, (x : ℝ) ^ g.factorization x) *
                ∏ x ∈ S, (x : ℝ) ^ g.factorization x) *
              ((∏ x ∈ P, (1 - (x : ℝ)⁻¹)) *
                ∏ x ∈ S, (1 - (x : ℝ)⁻¹) ^ 2)) *
              coprimeIntervalPrimeWeight S c := by ring
          _ = (g : ℝ) *
              ((∏ x ∈ P, (1 - (x : ℝ)⁻¹)) *
                ∏ x ∈ S, (1 - (x : ℝ)⁻¹) ^ 2) *
              coprimeIntervalPrimeWeight S c := by rw [hpowers]
          _ = _ := by ring
  · simp [pairCongruenceLocalProduct, huc]

lemma pairLocalDensityProduct_nonneg (g u : ℕ) :
    0 ≤ pairLocalDensityProduct g u := by
  apply mul_nonneg <;> apply Finset.prod_nonneg <;> intro p hp
  · have hpPrime : p.Prime :=
      Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1
    exact sub_nonneg.mpr
      (inv_le_one_of_one_le₀ (by exact_mod_cast hpPrime.one_le))
  · positivity

/-- Real majorant for the exact congruence-fibre local product. -/
lemma congruenceFiberLocalProduct_cast_le_weight
    {g a b : ℕ} (hg : 0 < g) (c : ℤ) :
    (congruenceFiberLocalProduct g a b c : ℝ) ≤
      if (a * b).Coprime c.natAbs then
        g * pairLocalDensityProduct g (a * b) *
          coprimeIntervalPrimeWeight (freshCommonPrimes g (a * b)) c.natAbs
      else 0 := by
  rw [congruenceFiberLocalProduct_eq_split]
  simpa only [pairCongruenceLocalProduct,
    equalPrimeFactor, pairEqualPrimeFactor, freshCommonPrimes] using
    (pairCongruenceLocalProduct_cast_le (g := g) (u := a * b)
      (c := c.natAbs) hg)

/-- Sum of congruence fibres over a symmetric interval.  The hypothesis
`1 < a*b` removes the central value, while the radical hypothesis is exactly
the one required by `weightedCoprimeInterval_sum_le`. -/
theorem sum_congruenceFiberCount_le_weighted
    {g a b K : ℕ} (hg : 0 < g) (ha : 0 < a) (hb : 0 < b)
    (hab : a.Coprime b) (hu : 1 < a * b)
    (hrad : (∏ p ∈ (a * b).primeFactors, p) ≤ K ^ 2) :
    (∑ c ∈ signedIntegerRange K,
      (congruenceFiberCount g a b c : ℝ)) ≤
      2 * (g * pairLocalDensityProduct g (a * b)) *
        (weightedCoprimeIntervalConstant * K *
          ((a * b).totient : ℝ) / (a * b)) := by
  classical
  let S := freshCommonPrimes g (a * b)
  let A : ℝ := g * pairLocalDensityProduct g (a * b)
  let F : ℕ → ℝ := fun n ↦
    if (a * b).Coprime n then A * coprimeIntervalPrimeWeight S n else 0
  have hA : 0 ≤ A := mul_nonneg (by positivity)
    (pairLocalDensityProduct_nonneg g (a * b))
  have hpoint (c : ℤ) :
      (congruenceFiberCount g a b c : ℝ) ≤ F c.natAbs := by
    calc
      (congruenceFiberCount g a b c : ℝ) ≤
          congruenceFiberLocalProduct g a b c := by
        exact_mod_cast congruenceFiberCount_le_localProduct hg ha hb hab c
      _ ≤ F c.natAbs := by
        simpa only [F, A, S] using
          congruenceFiberLocalProduct_cast_le_weight (g := g) (a := a)
            (b := b) hg c
  have hweighted := weightedCoprimeInterval_sum_le (a * b) K S
    (mul_pos ha hb) (fun p hp ↦ freshCommonPrimes_prime hp)
    (primeFactors_disjoint_freshCommonPrimes g (a * b)) hrad
  calc
    (∑ c ∈ signedIntegerRange K,
        (congruenceFiberCount g a b c : ℝ)) ≤
        ∑ c ∈ signedIntegerRange K, F c.natAbs := by
      exact Finset.sum_le_sum fun c _ ↦ hpoint c
    _ = F 0 + 2 • (∑ n ∈ Finset.Ioc 0 K, F n) := by
      simpa only [signedIntegerRange] using sum_Icc_int_natAbs F K
    _ = 2 * (∑ n ∈ Finset.Ioc 0 K, F n) := by
      have hne : a * b ≠ 1 := by omega
      simp [F, hne, two_smul]
      ring
    _ = 2 * (A * (∑ n ∈ Finset.Ioc 0 K,
        if (a * b).Coprime n then coprimeIntervalPrimeWeight S n else 0)) := by
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n hn
      by_cases hcop : (a * b).Coprime n <;> simp [F, hcop]
    _ ≤ 2 * (A * (weightedCoprimeIntervalConstant * K *
          ((a * b).totient : ℝ) / (a * b))) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply mul_le_mul_of_nonneg_left _ hA
      simpa only [Nat.cast_mul] using hweighted
    _ = 2 * (g * pairLocalDensityProduct g (a * b)) *
        (weightedCoprimeIntervalConstant * K *
          ((a * b).totient : ℝ) / (a * b)) := by
      dsimp only [A]
      ring

/-- Factored-denominator overlap bound before eliminating the cutoff and
Euler products. -/
theorem overlapPairCount_mul_le_weighted
    {g a b : ℕ} (hg : 0 < g) (ha : 0 < a) (hb : 0 < b)
    (hab : a.Coprime b) (hneq : g * a ≠ g * b)
    {L M : ℝ} (hL : (1 : ℝ) / 2 ≤ L) (hM : (1 : ℝ) / 2 ≤ M) :
    (overlapPairCount (g * a) (g * b) L M : ℝ) ≤
      2 * (g * pairLocalDensityProduct g (a * b)) *
        (weightedCoprimeIntervalConstant *
          Nat.ceil ((b : ℝ) * L + (a : ℝ) * M) *
          ((a * b).totient : ℝ) / (a * b)) := by
  let X : ℝ := (b : ℝ) * L + (a : ℝ) * M
  let K : ℕ := Nat.ceil X
  have hu : 1 < a * b := by
    have habne : a * b ≠ 1 := by
      intro hone
      have haone : a = 1 := Nat.dvd_one.mp (by
        rw [← hone]
        exact dvd_mul_right a b)
      have hbone : b = 1 := Nat.dvd_one.mp (by
        rw [← hone]
        exact dvd_mul_left b a)
      exact hneq (by simp [haone, hbone])
    have hu0 : 0 < a * b := mul_pos ha hb
    omega
  have hscale :
      (g * a * b : ℝ) *
          (L / (g * a : ℕ) + M / (g * b : ℕ)) = X := by
    dsimp only [X]
    push_cast
    field_simp
  have hcut :
      (g * a * b : ℝ) *
          (L / (g * a : ℕ) + M / (g * b : ℕ)) ≤ K := by
    rw [hscale]
    exact Nat.le_ceil X
  have hgeomNat :
      overlapPairCount (g * a) (g * b) L M ≤
        ∑ c ∈ signedIntegerRange K, congruenceFiberCount g a b c :=
    (overlapPairCount_le_nearbyReducedPairCount (g * a) (g * b) L M).trans
      (nearbyReducedPairCount_mul_le_sum_congruenceFiberCount hg ha hb hcut)
  have hgeom :
      (overlapPairCount (g * a) (g * b) L M : ℝ) ≤
        ∑ c ∈ signedIntegerRange K,
          (congruenceFiberCount g a b c : ℝ) := by
    exact_mod_cast hgeomNat
  calc
    (overlapPairCount (g * a) (g * b) L M : ℝ) ≤
        ∑ c ∈ signedIntegerRange K,
          (congruenceFiberCount g a b c : ℝ) := hgeom
    _ ≤ 2 * (g * pairLocalDensityProduct g (a * b)) *
        (weightedCoprimeIntervalConstant * K *
          ((a * b).totient : ℝ) / (a * b)) :=
      sum_congruenceFiberCount_le_weighted hg ha hb hab hu
        (by simpa only [X, K] using
          prod_primeFactors_mul_le_ceil_sq ha hb hL hM)
    _ = 2 * (g * pairLocalDensityProduct g (a * b)) *
        (weightedCoprimeIntervalConstant *
          Nat.ceil ((b : ℝ) * L + (a : ℝ) * M) *
          ((a * b).totient : ℝ) / (a * b)) := by rfl

/-- An explicit absolute constant for the Pollington--Vaughan pair count. -/
def pairOverlapConstant : ℝ := 8 * weightedCoprimeIntervalConstant

lemma pairOverlapConstant_nonneg : 0 ≤ pairOverlapConstant := by
  simp only [pairOverlapConstant, weightedCoprimeIntervalConstant]
  positivity

/-- Pollington--Vaughan overlap estimate in factored-denominator form. -/
theorem overlapPairCount_mul_le
    {g a b : ℕ} (hg : 0 < g) (ha : 0 < a) (hb : 0 < b)
    (hab : a.Coprime b) (hneq : g * a ≠ g * b)
    {L M : ℝ} (hL : (1 : ℝ) / 2 ≤ L) (hM : (1 : ℝ) / 2 ≤ M) :
    (overlapPairCount (g * a) (g * b) L M : ℝ) ≤
      pairOverlapConstant * ((g * a).totient : ℝ) *
        ((g * b).totient : ℝ) *
        max (L / (g * a : ℕ)) (M / (g * b : ℕ)) := by
  let X : ℝ := (b : ℝ) * L + (a : ℝ) * M
  let K : ℕ := Nat.ceil X
  let D : ℝ := pairLocalDensityProduct g (a * b)
  let C : ℝ := weightedCoprimeIntervalConstant
  have hraw := overlapPairCount_mul_le_weighted hg ha hb hab hneq hL hM
  have hXone : (1 : ℝ) ≤ X := by
    dsimp only [X]
    have haR : (1 : ℝ) ≤ a := by exact_mod_cast ha
    have hbR : (1 : ℝ) ≤ b := by exact_mod_cast hb
    nlinarith
  have hK : (K : ℝ) ≤ 2 * X := by
    have hceil : (K : ℝ) < X + 1 := Nat.ceil_lt_add_one (by linarith)
    linarith
  have hbridge :
      D * (((a * b).totient : ℝ) / (a * b)) =
        (((g * a).totient : ℝ) / (g * a)) *
          (((g * b).totient : ℝ) / (g * b)) := by
    dsimp only [D, pairLocalDensityProduct, freshCommonPrimes]
    exact totient_product_bridge_real g a b hg ha hb hab
  have hC : 0 ≤ C := by
    dsimp only [C, weightedCoprimeIntervalConstant]
    positivity
  have hratA : 0 ≤ (((g * a).totient : ℝ) / (g * a)) := by positivity
  have hratB : 0 ≤ (((g * b).totient : ℝ) / (g * b)) := by positivity
  have hraw' :
      (overlapPairCount (g * a) (g * b) L M : ℝ) ≤
        2 * C * g * K *
          ((((g * a).totient : ℝ) / (g * a)) *
            (((g * b).totient : ℝ) / (g * b))) := by
    calc
      (overlapPairCount (g * a) (g * b) L M : ℝ) ≤
          2 * ((g : ℝ) * D) *
            (C * K * ((a * b).totient : ℝ) / (a * b)) := by
        simpa only [C, D, K, X] using hraw
      _ = 2 * C * g * K *
          (D * (((a * b).totient : ℝ) / (a * b))) := by ring
      _ = 2 * C * g * K *
          ((((g * a).totient : ℝ) / (g * a)) *
            (((g * b).totient : ℝ) / (g * b))) := by rw [hbridge]
  have hscale :
      2 * C * (g : ℝ) * (2 * X) *
          ((((g * a).totient : ℝ) / (g * a)) *
            (((g * b).totient : ℝ) / (g * b))) =
        4 * C * ((g * a).totient : ℝ) * ((g * b).totient : ℝ) *
          (L / (g * a : ℕ) + M / (g * b : ℕ)) := by
    dsimp only [X]
    push_cast
    field_simp <;> ring
  have hsum :
      L / (g * a : ℕ) + M / (g * b : ℕ) ≤
        2 * max (L / (g * a : ℕ)) (M / (g * b : ℕ)) := by
    calc
      L / (g * a : ℕ) + M / (g * b : ℕ) ≤
          max (L / (g * a : ℕ)) (M / (g * b : ℕ)) +
            max (L / (g * a : ℕ)) (M / (g * b : ℕ)) :=
        add_le_add (le_max_left _ _) (le_max_right _ _)
      _ = 2 * max (L / (g * a : ℕ)) (M / (g * b : ℕ)) := by ring
  calc
    (overlapPairCount (g * a) (g * b) L M : ℝ) ≤
        2 * C * g * K *
          ((((g * a).totient : ℝ) / (g * a)) *
            (((g * b).totient : ℝ) / (g * b))) := hraw'
    _ ≤ 2 * C * g * (2 * X) *
          ((((g * a).totient : ℝ) / (g * a)) *
            (((g * b).totient : ℝ) / (g * b))) := by
      gcongr
    _ = 4 * C * ((g * a).totient : ℝ) * ((g * b).totient : ℝ) *
          (L / (g * a : ℕ) + M / (g * b : ℕ)) := hscale
    _ ≤ 4 * C * ((g * a).totient : ℝ) * ((g * b).totient : ℝ) *
          (2 * max (L / (g * a : ℕ)) (M / (g * b : ℕ))) := by
      exact mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = pairOverlapConstant * ((g * a).totient : ℝ) *
        ((g * b).totient : ℝ) *
        max (L / (g * a : ℕ)) (M / (g * b : ℕ)) := by
      simp only [pairOverlapConstant, C]
      ring

/-- Pollington--Vaughan overlap estimate for arbitrary distinct positive
denominators.  This is the public pair-count API used by the large-value
second-moment argument. -/
theorem overlapPairCount_le
    {q r : ℕ} (hq : 0 < q) (hr : 0 < r) (hneq : q ≠ r)
    {L M : ℝ} (hL : (1 : ℝ) / 2 ≤ L) (hM : (1 : ℝ) / 2 ≤ M) :
    (overlapPairCount q r L M : ℝ) ≤
      pairOverlapConstant * (q.totient : ℝ) * (r.totient : ℝ) *
        max (L / q) (M / r) := by
  let g := q.gcd r
  let a := q / g
  let b := r / g
  have hg : 0 < g := Nat.gcd_pos_of_pos_left r hq
  have hgleq : g ≤ q := Nat.le_of_dvd hq (Nat.gcd_dvd_left q r)
  have hgler : g ≤ r := Nat.le_of_dvd hr (Nat.gcd_dvd_right q r)
  have ha : 0 < a := Nat.div_pos hgleq hg
  have hb : 0 < b := Nat.div_pos hgler hg
  have hab : a.Coprime b := Nat.coprime_div_gcd_div_gcd hg
  have hqfac : g * a = q := Nat.mul_div_cancel' (Nat.gcd_dvd_left q r)
  have hrfac : g * b = r := Nat.mul_div_cancel' (Nat.gcd_dvd_right q r)
  have hneq' : g * a ≠ g * b := by simpa only [hqfac, hrfac] using hneq
  simpa only [hqfac, hrfac] using
    overlapPairCount_mul_le hg ha hb hab hneq' hL hM

/-- Version allowing a vanished radius, as occurs when the natural-valued
approximating function is zero at one of the denominators. -/
theorem overlapPairCount_le_of_zero_or_half
    {q r : ℕ} (hq : 0 < q) (hr : 0 < r) (hneq : q ≠ r)
    {L M : ℝ} (hL : L = 0 ∨ (1 : ℝ) / 2 ≤ L)
    (hM : M = 0 ∨ (1 : ℝ) / 2 ≤ M) :
    (overlapPairCount q r L M : ℝ) ≤
      pairOverlapConstant * (q.totient : ℝ) * (r.totient : ℝ) *
        max (L / q) (M / r) := by
  rcases hL with rfl | hL
  · rw [overlapPairCount_eq_zero_of_left_nonpos q r (le_refl 0)]
    norm_num only [Nat.cast_zero]
    have hM0 : 0 ≤ M := hM.elim (fun h ↦ h.ge) (le_trans (by norm_num) ·)
    exact mul_nonneg
      (mul_nonneg (mul_nonneg pairOverlapConstant_nonneg (by positivity))
        (by positivity))
      (le_trans (div_nonneg hM0 (by positivity)) (le_max_right _ _))
  rcases hM with rfl | hM
  · rw [overlapPairCount_eq_zero_of_right_nonpos q r (le_refl 0)]
    norm_num only [Nat.cast_zero]
    exact mul_nonneg
      (mul_nonneg (mul_nonneg pairOverlapConstant_nonneg (by positivity))
        (by positivity))
      (le_trans (div_nonneg (le_trans (by norm_num) hL) (by positivity))
        (le_max_left _ _))
  exact overlapPairCount_le hq hr hneq hL hM

end

end Erdos999
