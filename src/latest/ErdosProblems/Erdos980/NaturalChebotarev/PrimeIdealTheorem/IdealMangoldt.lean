/-
Copyright (c) 2026 The Formal Conjectures Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors
-/

module

public import CebotarevDensity.NumberFieldEulerProduct
public import Mathlib.RingTheory.UniqueFactorizationDomain.Finite

/-!
# The von Mangoldt function on ideals

This file defines the von Mangoldt weight directly on the nonzero integral ideals of a number
field.  The definition uses the normalized factorization of an ideal in the Dedekind domain
`𝓞 K`.  It is consequently independent of any enumeration of prime ideals:

* the weight of `𝔭 ^ m`, for a nonzero prime ideal `𝔭` and `m > 0`, is `log (N 𝔭)`;
* the weight of every ideal having zero or at least two distinct prime factors is zero.

The final identities express `log (N 𝔞)` both as the sum of the logarithms of the normalized
prime factors (with multiplicity), and as the sum of the ideal von Mangoldt weights over the
prime-power divisors selected by the factorization of `𝔞`.
-/

@[expose] public section

noncomputable section

open NumberField UniqueFactorizationMonoid
open scoped BigOperators

namespace Erdos980.NaturalChebotarev.PrimeIdealTheorem

variable (K : Type*) [Field K] [NumberField K]

/-- The finite set of distinct prime factors of a nonzero ideal. -/
noncomputable def idealPrimeSupport (I : Chebotarev.NonzeroIdeal K) :
    Finset (Ideal (𝓞 K)) :=
  (normalizedFactors I.1).toFinset

/-- The von Mangoldt weight of a nonzero ideal.  When there is exactly one distinct normalized
prime factor, sum its logarithmic norm; otherwise return zero.  Writing the singleton branch as
a finite sum avoids making an arbitrary choice of the unique factor. -/
noncomputable def idealMangoldt (I : Chebotarev.NonzeroIdeal K) : ℝ :=
  if (idealPrimeSupport K I).card = 1 then
    ∑ P ∈ idealPrimeSupport K I, Real.log (Ideal.absNorm P : ℝ)
  else 0

/-- The same weight on all ideals, extended by zero at the bottom ideal. -/
noncomputable def idealMangoldtIdeal (I : Ideal (𝓞 K)) : ℝ :=
  if hI : I ≠ ⊥ then idealMangoldt K ⟨I, hI⟩ else 0

@[simp] theorem idealPrimeSupport_top :
    idealPrimeSupport K (⟨⊤, by simp⟩ : Chebotarev.NonzeroIdeal K) = ∅ := by
  simp [idealPrimeSupport, ← Ideal.one_eq_top, normalizedFactors_one]

@[simp] theorem idealMangoldt_top :
    idealMangoldt K (⟨⊤, by simp⟩ : Chebotarev.NonzeroIdeal K) = 0 := by
  simp [idealMangoldt]

@[simp] theorem idealMangoldtIdeal_bot : idealMangoldtIdeal K ⊥ = 0 := by
  simp [idealMangoldtIdeal]

theorem idealPrimeSupport_prime_pow {P : Ideal (𝓞 K)}
    (hP : P.IsPrime) (hP0 : P ≠ ⊥) {m : ℕ} (hm : 0 < m) :
    idealPrimeSupport K (⟨P ^ m, pow_ne_zero m hP0⟩ : Chebotarev.NonzeroIdeal K) = {P} := by
  have hPirred : Irreducible P := Ideal.prime_of_isPrime hP0 hP |>.irreducible
  simp [idealPrimeSupport, normalizedFactors_of_irreducible_pow hPirred,
    normalize_eq, hm.ne']

/-- The defining prime-power value of the ideal von Mangoldt function. -/
theorem idealMangoldt_prime_pow {P : Ideal (𝓞 K)}
    (hP : P.IsPrime) (hP0 : P ≠ ⊥) {m : ℕ} (hm : 0 < m) :
    idealMangoldt K (⟨P ^ m, pow_ne_zero m hP0⟩ : Chebotarev.NonzeroIdeal K) =
      Real.log (Ideal.absNorm P : ℝ) := by
  rw [idealMangoldt, idealPrimeSupport_prime_pow K hP hP0 hm]
  simp

/-- The defining prime-power value for the extension to all ideals. -/
theorem idealMangoldtIdeal_prime_pow {P : Ideal (𝓞 K)}
    (hP : P.IsPrime) (hP0 : P ≠ ⊥) {m : ℕ} (hm : 0 < m) :
    idealMangoldtIdeal K (P ^ m) = Real.log (Ideal.absNorm P : ℝ) := by
  rw [idealMangoldtIdeal]
  split
  · exact idealMangoldt_prime_pow K hP hP0 hm
  · rename_i h
    exact (h (pow_ne_zero m hP0)).elim

/-- Every normalized ideal factor is a nonzero prime ideal. -/
theorem normalizedFactor_isPrime_ne_bot {I : Chebotarev.NonzeroIdeal K}
    {P : Ideal (𝓞 K)} (hP : P ∈ normalizedFactors I.1) :
    P.IsPrime ∧ P ≠ ⊥ := by
  have hp : Prime P := prime_of_normalized_factor P hP
  exact ⟨Ideal.isPrime_of_prime hp, hp.ne_zero⟩

/-- A normalized prime factor of a number-ring ideal has norm at least two. -/
theorem two_le_absNorm_of_mem_normalizedFactors {I : Chebotarev.NonzeroIdeal K}
    {P : Ideal (𝓞 K)} (hP : P ∈ normalizedFactors I.1) :
    2 ≤ Ideal.absNorm P := by
  have hp := normalizedFactor_isPrime_ne_bot K hP
  have hne0 : Ideal.absNorm P ≠ 0 := fun h ↦ hp.2 (Ideal.absNorm_eq_zero_iff.mp h)
  have hne1 : Ideal.absNorm P ≠ 1 := fun h ↦ hp.1.ne_top (Ideal.absNorm_eq_one_iff.mp h)
  omega

/-- Ideal von Mangoldt weights are nonnegative. -/
theorem idealMangoldt_nonneg (I : Chebotarev.NonzeroIdeal K) :
    0 ≤ idealMangoldt K I := by
  rw [idealMangoldt]
  split_ifs
  · exact Finset.sum_nonneg fun P hP ↦ Real.log_nonneg <| by
      exact_mod_cast one_le_two.trans
        (two_le_absNorm_of_mem_normalizedFactors K (Multiset.mem_toFinset.mp hP))
  · exact le_rfl

theorem idealMangoldtIdeal_nonneg (I : Ideal (𝓞 K)) :
    0 ≤ idealMangoldtIdeal K I := by
  rw [idealMangoldtIdeal]
  split_ifs with hI
  · exact idealMangoldt_nonneg K ⟨I, hI⟩
  · exact le_rfl

/-- If the support is not a singleton, the ideal Mangoldt weight vanishes. -/
theorem idealMangoldt_eq_zero_of_support_card_ne_one {I : Chebotarev.NonzeroIdeal K}
    (hI : (idealPrimeSupport K I).card ≠ 1) :
    idealMangoldt K I = 0 := by
  simp [idealMangoldt, hI]

/-- A nonzero ideal whose normalized factor support is a singleton is a positive power of the
unique nonzero prime ideal in that support. -/
theorem exists_prime_pow_of_idealPrimeSupport_card_eq_one
    (I : Chebotarev.NonzeroIdeal K) (hI : (idealPrimeSupport K I).card = 1) :
    ∃ (P : Ideal (𝓞 K)) (m : ℕ),
      P.IsPrime ∧ P ≠ ⊥ ∧ 0 < m ∧ I.1 = P ^ m := by
  obtain ⟨P, hsupp⟩ := Finset.card_eq_one.mp hI
  have hP_supp : P ∈ idealPrimeSupport K I := by simp [hsupp]
  have hP_fac : P ∈ normalizedFactors I.1 := by
    exact Multiset.mem_toFinset.mp hP_supp
  have hp := normalizedFactor_isPrime_ne_bot K hP_fac
  let m := (normalizedFactors I.1).card
  have hm : 0 < m := Multiset.card_pos_iff_exists_mem.mpr ⟨P, hP_fac⟩
  have hall : ∀ Q ∈ normalizedFactors I.1, Q = P := by
    intro Q hQ
    have hQ_supp : Q ∈ idealPrimeSupport K I := Multiset.mem_toFinset.mpr hQ
    rw [hsupp] at hQ_supp
    simpa using hQ_supp
  have hfac : normalizedFactors I.1 = Multiset.replicate m P :=
    Multiset.eq_replicate_card.mpr hall
  refine ⟨P, m, hp.1, hp.2, hm, ?_⟩
  calc
    I.1 = (normalizedFactors I.1).prod :=
      (Ideal.prod_normalizedFactors_eq_self I.2).symm
    _ = (Multiset.replicate m P).prod := by rw [hfac]
    _ = P ^ m := Multiset.prod_replicate m P

/-- Exact prime-power characterization of singleton ideal-factor support. -/
theorem idealPrimeSupport_card_eq_one_iff_exists_prime_pow
    (I : Chebotarev.NonzeroIdeal K) :
    (idealPrimeSupport K I).card = 1 ↔
      ∃ (P : Ideal (𝓞 K)) (m : ℕ),
        P.IsPrime ∧ P ≠ ⊥ ∧ 0 < m ∧ I.1 = P ^ m := by
  constructor
  · exact exists_prime_pow_of_idealPrimeSupport_card_eq_one K I
  · rintro ⟨P, m, hP, hP0, hm, hIP⟩
    have hsub : I = (⟨P ^ m, pow_ne_zero m hP0⟩ : Chebotarev.NonzeroIdeal K) :=
      Subtype.ext hIP
    rw [hsub, idealPrimeSupport_prime_pow K hP hP0 hm]
    simp

/-- Singleton support gives a strictly positive Mangoldt weight. -/
theorem idealMangoldt_pos_of_support_card_eq_one {I : Chebotarev.NonzeroIdeal K}
    (hI : (idealPrimeSupport K I).card = 1) :
    0 < idealMangoldt K I := by
  obtain ⟨P, hsupp⟩ := Finset.card_eq_one.mp hI
  have hP_supp : P ∈ idealPrimeSupport K I := by simp [hsupp]
  have hP_fac : P ∈ normalizedFactors I.1 := Multiset.mem_toFinset.mp hP_supp
  rw [idealMangoldt, if_pos hI, hsupp]
  simp only [Finset.sum_singleton]
  apply Real.log_pos
  exact_mod_cast lt_of_lt_of_le Nat.one_lt_two
    (two_le_absNorm_of_mem_normalizedFactors K hP_fac)

/-- The ideal Mangoldt weight vanishes exactly away from positive prime powers. -/
theorem idealMangoldt_eq_zero_iff_not_exists_prime_pow (I : Chebotarev.NonzeroIdeal K) :
    idealMangoldt K I = 0 ↔
      ¬∃ (P : Ideal (𝓞 K)) (m : ℕ),
        P.IsPrime ∧ P ≠ ⊥ ∧ 0 < m ∧ I.1 = P ^ m := by
  rw [← idealPrimeSupport_card_eq_one_iff_exists_prime_pow K I]
  constructor
  · intro hΛ hcard
    exact (idealMangoldt_pos_of_support_card_eq_one K hcard).ne' hΛ
  · exact idealMangoldt_eq_zero_of_support_card_ne_one K

/-- Absolute norm is the product of the norms of the normalized ideal factors. -/
theorem absNorm_eq_prod_normalizedFactors (I : Chebotarev.NonzeroIdeal K) :
    Ideal.absNorm I.1 =
      ((normalizedFactors I.1).map (fun P ↦ Ideal.absNorm P)).prod := by
  calc
    Ideal.absNorm I.1 = Ideal.absNorm (normalizedFactors I.1).prod := by
      rw [Ideal.prod_normalizedFactors_eq_self I.2]
    _ = ((normalizedFactors I.1).map (fun P ↦ Ideal.absNorm P)).prod :=
      map_multiset_prod Ideal.absNorm (normalizedFactors I.1)

/-- The logarithm of the norm of an ideal is the sum of the logarithmic norms of its normalized
prime factors, counted with multiplicity. -/
theorem log_absNorm_eq_sum_normalizedFactors (I : Chebotarev.NonzeroIdeal K) :
    Real.log (Ideal.absNorm I.1 : ℝ) =
      ((normalizedFactors I.1).map
        (fun P ↦ Real.log (Ideal.absNorm P : ℝ))).sum := by
  rw [absNorm_eq_prod_normalizedFactors K I, Nat.cast_multiset_prod,
    Real.log_multiset_prod]
  · simp only [Multiset.map_map, Function.comp_apply]
  · intro x hx
    obtain ⟨n, hn, rfl⟩ := Multiset.mem_map.mp hx
    obtain ⟨P, hP, rfl⟩ := Multiset.mem_map.mp hn
    exact_mod_cast Nat.ne_of_gt
      (Nat.zero_lt_two.trans_le (two_le_absNorm_of_mem_normalizedFactors K hP))

/-- Grouping the preceding factor sum by distinct prime factors exposes their multiplicities. -/
theorem log_absNorm_eq_sum_support_count (I : Chebotarev.NonzeroIdeal K) :
    Real.log (Ideal.absNorm I.1 : ℝ) =
      ∑ P ∈ idealPrimeSupport K I,
        (normalizedFactors I.1).count P * Real.log (Ideal.absNorm P : ℝ) := by
  rw [log_absNorm_eq_sum_normalizedFactors K I, idealPrimeSupport]
  simpa only [nsmul_eq_mul] using
    (Finset.sum_multiset_map_count (normalizedFactors I.1)
      (fun P ↦ Real.log (Ideal.absNorm P : ℝ)))

/-- The sum of the ideal Mangoldt weights of the positive powers of one normalized prime factor
up to its multiplicity. -/
theorem sum_idealMangoldtIdeal_prime_powers {I : Chebotarev.NonzeroIdeal K}
    {P : Ideal (𝓞 K)} (hP : P ∈ idealPrimeSupport K I) :
    (∑ m ∈ Finset.Icc 1 ((normalizedFactors I.1).count P),
        idealMangoldtIdeal K (P ^ m)) =
      (normalizedFactors I.1).count P * Real.log (Ideal.absNorm P : ℝ) := by
  have hP' : P ∈ normalizedFactors I.1 := Multiset.mem_toFinset.mp hP
  have hp := normalizedFactor_isPrime_ne_bot K hP'
  calc
    (∑ m ∈ Finset.Icc 1 ((normalizedFactors I.1).count P),
        idealMangoldtIdeal K (P ^ m)) =
        ∑ _m ∈ Finset.Icc 1 ((normalizedFactors I.1).count P),
          Real.log (Ideal.absNorm P : ℝ) := by
      apply Finset.sum_congr rfl
      intro m hm
      exact idealMangoldtIdeal_prime_pow K hp.1 hp.2 (Finset.mem_Icc.mp hm).1
    _ = (normalizedFactors I.1).count P * Real.log (Ideal.absNorm P : ℝ) := by
      simp [Finset.sum_const, nsmul_eq_mul]

/-- Divisor-convolution form of the logarithmic norm identity.  For each distinct prime factor
`P` of `I`, the inner sum runs through exactly the prime-power divisors
`P, P^2, ..., P^(v_P(I))`.  Since the ideal Mangoldt function vanishes away from prime powers,
this is the effective finite divisor sum `∑_{J ∣ I} Λ_K(J)`. -/
theorem log_absNorm_eq_sum_idealMangoldt_primePowerDivisors
    (I : Chebotarev.NonzeroIdeal K) :
    Real.log (Ideal.absNorm I.1 : ℝ) =
      ∑ P ∈ idealPrimeSupport K I,
        ∑ m ∈ Finset.Icc 1 ((normalizedFactors I.1).count P),
          idealMangoldtIdeal K (P ^ m) := by
  rw [log_absNorm_eq_sum_support_count K I]
  exact Finset.sum_congr rfl fun P hP ↦
    (sum_idealMangoldtIdeal_prime_powers K hP).symm

end Erdos980.NaturalChebotarev.PrimeIdealTheorem
