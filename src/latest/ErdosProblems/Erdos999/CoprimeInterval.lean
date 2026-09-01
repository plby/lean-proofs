/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib

/-!
# Coprime integers in a short interval

This file proves an elementary, completely explicit upper-bound sieve for the
number of integers in an interval which are coprime to a prescribed modulus.
The error term is the number of squarefree divisors of the modulus.  A second
lemma absorbs that error as soon as the radical of the modulus is at most the
square of the interval length.
-/

namespace Erdos999

open scoped BigOperators
open ArithmeticFunction

private lemma card_filter_dvd_Ioc (A B d : ℕ) (hd : 0 < d) :
    ((Finset.Ioc A B).filter fun x => d ∣ x).card = B / d - A / d := by
  classical
  rw [show ((Finset.Ioc A B).filter fun x => d ∣ x) =
      (Finset.Ioc (A / d) (B / d)).image (fun k => d * k) by
    ext x
    simp only [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_image]
    constructor
    · rintro ⟨⟨hAx, hxB⟩, hdx⟩
      refine ⟨x / d, ⟨?_, Nat.div_le_div_right hxB⟩, ?_⟩
      · by_contra h
        have hxAdiv : x / d ≤ A / d := Nat.le_of_not_gt h
        have hxA : x ≤ A := calc
          x = (x / d) * d := (Nat.div_mul_cancel hdx).symm
          _ ≤ (A / d) * d := Nat.mul_le_mul_right d hxAdiv
          _ ≤ A := Nat.div_mul_le_self A d
        omega
      · simpa [Nat.mul_comm] using Nat.div_mul_cancel hdx
    · rintro ⟨k, ⟨hAk, hkB⟩, rfl⟩
      refine ⟨⟨?_, ?_⟩, dvd_mul_right d k⟩
      · simpa [Nat.mul_comm] using (Nat.div_lt_iff_lt_mul hd).mp hAk
      · simpa [Nat.mul_comm] using (Nat.le_div_iff_mul_le hd).mp hkB]
  rw [Finset.card_image_of_injective _ (mul_right_injective₀ hd.ne')]
  simp

private lemma abs_card_filter_dvd_Ioc_sub (A B d : ℕ) (hd : 0 < d) :
    |(((Finset.Ioc A B).filter fun x => d ∣ x).card : ℝ) -
        ((B - A : ℕ) : ℝ) / d| ≤ 1 := by
  rw [card_filter_dvd_Ioc A B d hd]
  by_cases hAB : A ≤ B
  · rw [Nat.cast_sub hAB]
    have hABdiv : A / d ≤ B / d := Nat.div_le_div_right hAB
    rw [Nat.cast_sub hABdiv]
    have hA : ((A / d : ℕ) : ℝ) ≤ (A : ℝ) / d := Nat.cast_div_le
    have hB : ((B / d : ℕ) : ℝ) ≤ (B : ℝ) / d := Nat.cast_div_le
    have hA' : (A : ℝ) / d < ((A / d : ℕ) : ℝ) + 1 := by
      rw [div_lt_iff₀ (by exact_mod_cast hd)]
      exact_mod_cast (by simpa [Nat.mul_comm, Nat.add_mul] using Nat.lt_mul_div_succ A hd)
    have hB' : (B : ℝ) / d < ((B / d : ℕ) : ℝ) + 1 := by
      rw [div_lt_iff₀ (by exact_mod_cast hd)]
      exact_mod_cast (by simpa [Nat.mul_comm, Nat.add_mul] using Nat.lt_mul_div_succ B hd)
    have hsub : ((B : ℝ) - A) / d = (B : ℝ) / d - (A : ℝ) / d := by ring
    rw [hsub]
    rw [abs_le]
    constructor <;> linarith
  · have hBA : B ≤ A := Nat.le_of_not_ge hAB
    simp [Nat.sub_eq_zero_of_le hBA, Nat.div_le_div_right hBA]

/-- The squarefree kernel of a natural number. -/
private def natRadical (N : ℕ) : ℕ := ∏ p ∈ N.primeFactors, p

private lemma natRadical_pos (N : ℕ) : 0 < natRadical N := by
  apply Finset.prod_pos
  intro p hp
  exact (Nat.prime_of_mem_primeFactors hp).pos

private lemma prod_primes_squarefree (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) :
    Squarefree (∏ p ∈ s, p) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert p s hps ih =>
      rw [Finset.prod_insert hps, Nat.squarefree_mul_iff]
      have hp : p.Prime := hs p (Finset.mem_insert_self p s)
      have hs' : ∀ q ∈ s, q.Prime := fun q hq => hs q (Finset.mem_insert_of_mem hq)
      refine ⟨hp.coprime_iff_not_dvd.mpr ?_, hp.squarefree, ih hs'⟩
      intro hpdiv
      rw [Prime.dvd_finsetProd_iff hp.prime] at hpdiv
      obtain ⟨q, hqs, hpq⟩ := hpdiv
      have hpqeq : p = q := (Nat.prime_dvd_prime_iff_eq hp (hs' q hqs)).mp hpq
      exact hps (hpqeq.symm ▸ hqs)

private lemma natRadical_squarefree (N : ℕ) : Squarefree (natRadical N) := by
  exact prod_primes_squarefree N.primeFactors fun p hp => Nat.prime_of_mem_primeFactors hp

private lemma natRadical_primeFactors (N : ℕ) :
    (natRadical N).primeFactors = N.primeFactors := by
  exact Nat.primeFactors_prod_primeFactors N

private lemma coprime_natRadical_iff {N x : ℕ} (hN : N ≠ 0) :
    (natRadical N).Coprime x ↔ N.Coprime x := by
  constructor
  · intro hrad
    by_contra h
    rw [Nat.Prime.not_coprime_iff_dvd] at h
    obtain ⟨p, hp, hpN, hpx⟩ := h
    have hpMem : p ∈ N.primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpN, hN⟩
    have hpRad : p ∣ natRadical N := Finset.dvd_prod_of_mem id hpMem
    exact (Nat.not_coprime_of_dvd_of_dvd hp.one_lt hpRad hpx) hrad
  · intro hNcop
    exact Nat.Coprime.coprime_dvd_left (Nat.prod_primeFactors_dvd N) hNcop

private lemma card_divisors_of_squarefree {n : ℕ} (hn : Squarefree n) :
    n.divisors.card = 2 ^ n.primeFactors.card := by
  rw [← Nat.divisors_filter_squarefree_of_squarefree hn]
  rw [Finset.card_eq_sum_ones]
  rw [Nat.sum_divisors_filter_squarefree hn.ne_zero]
  simp [Nat.factors_eq]

private lemma sum_moebius_divisors_eq_coprime_indicator
    (R x : ℕ) (hR : R ≠ 0) :
    (∑ d ∈ R.divisors,
        if d ∣ x then ((ArithmeticFunction.moebius d : ℤ) : ℝ) else 0) =
      if R.Coprime x then 1 else 0 := by
  classical
  have hgcddiv : (Nat.gcd x R).divisors = R.divisors.filter fun d => d ∣ x := by
    ext d
    constructor
    · intro hd
      rw [Nat.mem_divisors] at hd
      rcases (Nat.dvd_gcd_iff.mp hd.1) with ⟨hdx, hdR⟩
      exact Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨hdR, hR⟩, hdx⟩
    · intro hd
      rw [Finset.mem_filter, Nat.mem_divisors] at hd
      rcases hd with ⟨⟨hdR, _⟩, hdx⟩
      rw [Nat.mem_divisors]
      exact ⟨Nat.dvd_gcd hdx hdR, Nat.gcd_ne_zero_right hR⟩
  rw [← Finset.sum_filter, ← hgcddiv]
  rw [← Int.cast_sum, ← ArithmeticFunction.coe_mul_zeta_apply,
    ArithmeticFunction.moebius_mul_coe_zeta]
  change ((if Nat.gcd x R = 1 then 1 else 0 : ℤ) : ℝ) = _
  simp [Nat.Coprime, Nat.gcd_comm]

private lemma coprime_interval_card_eq_moebius_sum
    (A B R : ℕ) (hR : R ≠ 0) :
    ((((Finset.Ioc A B).filter fun x => R.Coprime x).card : ℕ) : ℝ) =
      ∑ d ∈ R.divisors, ((ArithmeticFunction.moebius d : ℤ) : ℝ) *
        (((Finset.Ioc A B).filter fun x => d ∣ x).card : ℝ) := by
  classical
  rw [← Finset.sum_boole]
  simp_rw [← sum_moebius_divisors_eq_coprime_indicator R _ hR]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d hd
  simp_rw [← mul_boole _ ((ArithmeticFunction.moebius d : ℤ) : ℝ)]
  rw [← Finset.mul_sum, ← Finset.sum_filter]
  simp

private lemma moebius_reciprocal_sum {N : ℕ} (hN : N ≠ 0) :
    N.divisors.sum (fun x => (ArithmeticFunction.moebius x : ℝ) / x) =
      (N.divisors.filter Nat.Prime).prod (fun p => 1 - (p : ℝ)⁻¹) := by
  let f' : ArithmeticFunction ℝ :=
    ⟨fun x => (ArithmeticFunction.moebius x : ℝ) / x, by simp⟩
  have hf' : f'.IsMultiplicative := by
    refine ⟨?_, ?_⟩
    · simp [f']
    · intro m n hmn
      simp [f', ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hmn,
        mul_div_mul_comm, Nat.cast_mul, Int.cast_mul]
  let f : ArithmeticFunction ℝ := f' * ArithmeticFunction.zeta
  have hf : f.IsMultiplicative := hf'.mul ArithmeticFunction.isMultiplicative_zeta.natCast
  change ∑ x ∈ N.divisors, f' x = _
  rw [← ArithmeticFunction.coe_mul_zeta_apply]
  change f N = _
  rw [← Nat.primeFactors_eq_to_filter_divisors_prime]
  induction N using Nat.recOnPosPrimePosCoprime with
  | prime_pow p k hp hk =>
      rw [ArithmeticFunction.coe_mul_zeta_apply, Nat.sum_divisors_prime_pow hp,
        Finset.sum_range_succ', Nat.primeFactors_prime_pow hk.ne' hp, Finset.prod_singleton]
      simp [f', ArithmeticFunction.moebius_apply_prime_pow, hp, hk, ite_div]
      ring
  | zero => cases hN rfl
  | one => simp [hf.map_one]
  | coprime a b ha hb hab aih bih =>
      have ha0 : a ≠ 0 := Nat.ne_of_gt (lt_trans Nat.zero_lt_one ha)
      have hb0 : b ≠ 0 := Nat.ne_of_gt (lt_trans Nat.zero_lt_one hb)
      rw [hf.map_mul_of_coprime hab, Nat.primeFactors_mul ha0 hb0, Finset.prod_union]
      · rw [aih ha0, bih hb0]
      · exact hab.disjoint_primeFactors

private lemma primeDensity_eq_totient_div (N : ℕ) (hN : N ≠ 0) :
    (∏ p ∈ N.primeFactors, (1 - (p : ℝ)⁻¹)) = (N.totient : ℝ) / N := by
  have htot := Nat.totient_mul_prod_primeFactors N
  have hprod : (∏ p ∈ N.primeFactors, (p : ℝ)) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro p hp
    exact_mod_cast (Nat.prime_of_mem_primeFactors hp).ne_zero
  have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast hN
  have hf : ∀ p ∈ N.primeFactors,
      1 - (p : ℝ)⁻¹ = ((p - 1 : ℕ) : ℝ) / p := by
    intro p hp
    have hp1 : 1 ≤ p := (Nat.prime_of_mem_primeFactors hp).one_le
    rw [Nat.cast_sub hp1, Nat.cast_one]
    have hp0 : (p : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.prime_of_mem_primeFactors hp).ne_zero
    field_simp
  rw [Finset.prod_congr rfl hf, Finset.prod_div_distrib]
  apply (div_eq_div_iff hprod hNR).2
  have hreal := congrArg (fun n : ℕ => (n : ℝ)) htot.symm
  push_cast at hreal
  simpa [mul_comm] using hreal

/--
The elementary upper-bound sieve with its explicit inclusion--exclusion
error.  The interval `(A,B]` contains at most its expected coprime density,
plus one rounding unit for each squarefree divisor of `N`.
-/
theorem coprimeInterval_card_le_density_add_error
    (A B N : ℕ) (hN : 0 < N) :
    ((((Finset.Ioc A B).filter fun x => N.Coprime x).card : ℕ) : ℝ) ≤
      ((B - A : ℕ) : ℝ) * (N.totient : ℝ) / N +
        (2 ^ N.primeFactors.card : ℕ) := by
  classical
  let R := natRadical N
  have hRpos : 0 < R := natRadical_pos N
  have hR : R ≠ 0 := hRpos.ne'
  have hRsq : Squarefree R := natRadical_squarefree N
  have hcop : ∀ x, R.Coprime x ↔ N.Coprime x := fun x => coprime_natRadical_iff hN.ne'
  have hcard := coprime_interval_card_eq_moebius_sum A B R hR
  simp_rw [hcop] at hcard
  rw [hcard]
  let L : ℝ := (B - A : ℕ)
  let M : ℝ :=
    ∑ d ∈ R.divisors, ((ArithmeticFunction.moebius d : ℤ) : ℝ) / d
  let E : ℝ :=
    ∑ d ∈ R.divisors, ((ArithmeticFunction.moebius d : ℤ) : ℝ) *
      ((((Finset.Ioc A B).filter fun x => d ∣ x).card : ℝ) - L / d)
  have hsplit :
      (∑ d ∈ R.divisors, ((ArithmeticFunction.moebius d : ℤ) : ℝ) *
          (((Finset.Ioc A B).filter fun x => d ∣ x).card : ℝ)) = L * M + E := by
    simp only [M, E, Finset.mul_sum]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro d hd
    ring
  rw [hsplit]
  have hE : E ≤ (R.divisors.card : ℝ) := by
    calc
      E ≤ |E| := le_abs_self E
      _ ≤ ∑ d ∈ R.divisors,
          |((ArithmeticFunction.moebius d : ℤ) : ℝ) *
            ((((Finset.Ioc A B).filter fun x => d ∣ x).card : ℝ) - L / d)| := by
        exact Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _d ∈ R.divisors, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro d hd
        have hdpos : 0 < d := Nat.pos_of_mem_divisors hd
        have herr := abs_card_filter_dvd_Ioc_sub A B d hdpos
        have hmuZ : |ArithmeticFunction.moebius d| ≤ (1 : ℤ) :=
          ArithmeticFunction.abs_moebius_le_one
        have hmu : |((ArithmeticFunction.moebius d : ℤ) : ℝ)| ≤ 1 := by
          exact_mod_cast hmuZ
        rw [abs_mul]
        change |((ArithmeticFunction.moebius d : ℤ) : ℝ)| *
            |(((Finset.Ioc A B).filter fun x => d ∣ x).card : ℝ) -
              ((B - A : ℕ) : ℝ) / d| ≤ 1
        nlinarith [abs_nonneg ((ArithmeticFunction.moebius d : ℤ) : ℝ),
          abs_nonneg ((((Finset.Ioc A B).filter fun x => d ∣ x).card : ℝ) -
            ((B - A : ℕ) : ℝ) / d)]
      _ = (R.divisors.card : ℝ) := by simp
  have hM : M = (N.totient : ℝ) / N := by
    have hm := moebius_reciprocal_sum hR
    rw [← Nat.primeFactors_eq_to_filter_divisors_prime] at hm
    dsimp [M]
    rw [hm]
    rw [show R.primeFactors = N.primeFactors by
      exact natRadical_primeFactors N]
    exact primeDensity_eq_totient_div N hN.ne'
  have hcardR : R.divisors.card = 2 ^ N.primeFactors.card := by
    rw [card_divisors_of_squarefree hRsq, natRadical_primeFactors]
  rw [hcardR] at hE
  rw [hM]
  change L * ((N.totient : ℝ) / N) + E ≤
    ((B - A : ℕ) : ℝ) * (N.totient : ℝ) / N +
      (2 ^ N.primeFactors.card : ℕ)
  dsimp [L]
  rw [mul_div_assoc]
  simpa [add_comm] using add_le_add_left hE
    (((B - A : ℕ) : ℝ) * ((N.totient : ℝ) / N))

private noncomputable def primeFactorRatio (p : ℕ) : ℝ :=
  2 * (p : ℝ) / ((p - 1 : ℕ) : ℝ)

private noncomputable def primeDensityFactor (p : ℕ) : ℝ :=
  1 - (p : ℝ)⁻¹

private lemma primeFactorRatio_le_four {p : ℕ} (hp : p.Prime) :
    primeFactorRatio p ≤ 4 := by
  have hp2 : 2 ≤ p := hp.two_le
  have hden : (0 : ℝ) < (p - 1 : ℕ) := by
    exact_mod_cast Nat.sub_pos_of_lt hp.one_lt
  rw [primeFactorRatio, div_le_iff₀ hden]
  rw [Nat.cast_sub hp.one_le, Nat.cast_one]
  have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hp2
  nlinarith

private lemma primeFactorRatio_le_sqrt {p : ℕ} (hp : p.Prime) (h7 : 7 ≤ p) :
    primeFactorRatio p ≤ Real.sqrt p := by
  have hden : (0 : ℝ) < (p - 1 : ℕ) := by
    exact_mod_cast Nat.sub_pos_of_lt hp.one_lt
  rw [primeFactorRatio, div_le_iff₀ hden]
  rw [Nat.cast_sub hp.one_le, Nat.cast_one]
  have hpR : (7 : ℝ) ≤ p := by exact_mod_cast h7
  have hsqrt : 0 ≤ Real.sqrt (p : ℝ) := Real.sqrt_nonneg _
  have hsqrt_sq : Real.sqrt (p : ℝ) ^ 2 = p := Real.sq_sqrt (by positivity)
  nlinarith

private lemma primeFactorRatio_product_le (N : ℕ) :
    (∏ p ∈ N.primeFactors, primeFactorRatio p) ≤
      (4 : ℝ) ^ 7 * Real.sqrt (natRadical N) := by
  classical
  let P := N.primeFactors
  let S := P.filter (fun p => p < 7)
  let T := P.filter (fun p => ¬p < 7)
  have hsCard : S.card ≤ 7 := by
    apply Finset.card_le_card (t := Finset.range 7)
    intro p hp
    exact Finset.mem_range.mpr (Finset.mem_filter.mp hp).2
  have hs : (∏ p ∈ S, primeFactorRatio p) ≤ (4 : ℝ) ^ 7 := by
    calc
      (∏ p ∈ S, primeFactorRatio p) ≤ ∏ _p ∈ S, (4 : ℝ) := by
        apply Finset.prod_le_prod
        · intro p hp
          exact div_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _))
            (Nat.cast_nonneg _)
        · intro p hp
          exact primeFactorRatio_le_four
            (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1)
      _ = (4 : ℝ) ^ S.card := by simp
      _ ≤ (4 : ℝ) ^ 7 := pow_le_pow_right₀ (by norm_num) hsCard
  have hTP : T ⊆ P := Finset.filter_subset _ _
  have hprodTP : (∏ p ∈ T, p) ≤ natRadical N := by
    change (∏ p ∈ T, p) ≤ ∏ p ∈ P, p
    exact Finset.prod_le_prod_of_subset_of_one_le' hTP fun p hpP hpT =>
      (Nat.prime_of_mem_primeFactors hpP).one_le
  have ht : (∏ p ∈ T, primeFactorRatio p) ≤ Real.sqrt (natRadical N) := by
    calc
      (∏ p ∈ T, primeFactorRatio p) ≤ ∏ p ∈ T, Real.sqrt p := by
        apply Finset.prod_le_prod
        · intro p hp
          exact div_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _))
            (Nat.cast_nonneg _)
        · intro p hp
          exact primeFactorRatio_le_sqrt
            (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1)
            (by
              have hpnot := (Finset.mem_filter.mp hp).2
              omega)
      _ = Real.sqrt (∏ p ∈ T, (p : ℝ)) :=
        (Real.sqrt_prod T (fun p hp => by positivity)).symm
      _ ≤ Real.sqrt (natRadical N) := Real.sqrt_le_sqrt (by
        have hh : ((∏ p ∈ T, p : ℕ) : ℝ) ≤ (natRadical N : ℝ) := by
          exact_mod_cast hprodTP
        simpa only [Nat.cast_prod] using hh)
  change (∏ p ∈ P, primeFactorRatio p) ≤
    (4 : ℝ) ^ 7 * Real.sqrt (natRadical N)
  rw [← Finset.prod_filter_mul_prod_filter_not P (fun p => p < 7) primeFactorRatio]
  change (∏ p ∈ S, primeFactorRatio p) * (∏ p ∈ T, primeFactorRatio p) ≤ _
  have ht0 : (0 : ℝ) ≤ ∏ p ∈ T, primeFactorRatio p :=
    Finset.prod_nonneg fun p hp =>
      div_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) (Nat.cast_nonneg _)
  exact mul_le_mul hs ht ht0 (by positivity)

private lemma pow_primeFactors_card_factorization (N : ℕ) :
    ((2 ^ N.primeFactors.card : ℕ) : ℝ) =
      (∏ p ∈ N.primeFactors, primeFactorRatio p) *
        ∏ p ∈ N.primeFactors, primeDensityFactor p := by
  push_cast
  rw [← Finset.prod_const, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro p hp
  have hpPrime := Nat.prime_of_mem_primeFactors hp
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hpPrime.ne_zero
  have hpminus : (p : ℝ) - 1 ≠ 0 := by
    exact sub_ne_zero.mpr (by exact_mod_cast hpPrime.ne_one)
  rw [primeFactorRatio, primeDensityFactor, Nat.cast_sub hpPrime.one_le, Nat.cast_one]
  field_simp [hp0, hpminus]

private lemma pow_primeFactors_card_le_density
    (N L : ℕ)
    (hrad : (∏ p ∈ N.primeFactors, p) ≤ L ^ 2) :
    ((2 ^ N.primeFactors.card : ℕ) : ℝ) ≤
      (4 : ℝ) ^ 7 * L * (∏ p ∈ N.primeFactors, primeDensityFactor p) := by
  have hrad' : natRadical N ≤ L ^ 2 := hrad
  have hsqrt : Real.sqrt (natRadical N) ≤ (L : ℝ) := by
    calc
      Real.sqrt (natRadical N) ≤ Real.sqrt ((L : ℝ) ^ 2) :=
        Real.sqrt_le_sqrt (by exact_mod_cast hrad')
      _ = (L : ℝ) := Real.sqrt_sq (Nat.cast_nonneg L)
  have hdensity : 0 ≤ ∏ p ∈ N.primeFactors, primeDensityFactor p := by
    apply Finset.prod_nonneg
    intro p hp
    rw [primeDensityFactor]
    have hpR : (1 : ℝ) ≤ p := by
      exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_le
    exact sub_nonneg.mpr ((inv_le_one₀ (by positivity : (0 : ℝ) < p)).2 hpR)
  rw [pow_primeFactors_card_factorization]
  calc
    (∏ p ∈ N.primeFactors, primeFactorRatio p) *
        (∏ p ∈ N.primeFactors, primeDensityFactor p) ≤
      ((4 : ℝ) ^ 7 * Real.sqrt (natRadical N)) *
        (∏ p ∈ N.primeFactors, primeDensityFactor p) :=
      mul_le_mul_of_nonneg_right (primeFactorRatio_product_le N) hdensity
    _ ≤ ((4 : ℝ) ^ 7 * L) *
        (∏ p ∈ N.primeFactors, primeDensityFactor p) := by
      gcongr
    _ = _ := by ring

/--
Uniform short-interval sieve.  If the product of the distinct prime divisors
of `N` is at most the square of the interval length, then the number of
integers in `(A,B]` coprime to `N` is at most `16385` times the expected
number.  The deliberately non-optimized constant is absolute.
-/
theorem coprimeInterval_card_le
    (A B N : ℕ) (hN : 0 < N)
    (hrad : (∏ p ∈ N.primeFactors, p) ≤ (B - A) ^ 2) :
    ((((Finset.Ioc A B).filter fun x => N.Coprime x).card : ℕ) : ℝ) ≤
      16385 * ((B - A : ℕ) : ℝ) * (N.totient : ℝ) / N := by
  have hbase := coprimeInterval_card_le_density_add_error A B N hN
  have herr := pow_primeFactors_card_le_density N (B - A) hrad
  have hdensity :
      (∏ p ∈ N.primeFactors, primeDensityFactor p) = (N.totient : ℝ) / N := by
    simpa [primeDensityFactor] using primeDensity_eq_totient_div N hN.ne'
  rw [hdensity] at herr
  calc
    ((((Finset.Ioc A B).filter fun x => N.Coprime x).card : ℕ) : ℝ) ≤
        ((B - A : ℕ) : ℝ) * (N.totient : ℝ) / N +
          (2 ^ N.primeFactors.card : ℕ) := hbase
    _ ≤ ((B - A : ℕ) : ℝ) * (N.totient : ℝ) / N +
        (4 : ℝ) ^ 7 * (B - A : ℕ) * ((N.totient : ℝ) / N) := by
      gcongr
    _ = 16385 * ((B - A : ℕ) : ℝ) * (N.totient : ℝ) / N := by
      norm_num
      ring

open scoped BigOperators

private lemma prod_primes_le_two_mul_sub_one_sq (s : Finset ℕ)
    (hs : ∀ p ∈ s, p.Prime) :
    (∏ p ∈ s, p) ≤ 2 * (∏ p ∈ s, (p - 1)) ^ 2 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert p s hps ih =>
      rw [Finset.prod_insert hps, Finset.prod_insert hps]
      have hp := hs p (Finset.mem_insert_self p s)
      have hs' : ∀ q ∈ s, q.Prime := fun q hq => hs q (Finset.mem_insert_of_mem hq)
      by_cases hp2 : p = 2
      · subst p
        norm_num
        have hrest : (∏ q ∈ s, q) ≤ (∏ q ∈ s, (q - 1)) ^ 2 := by
          rw [← Finset.prod_pow]
          apply Finset.prod_le_prod
          · intro q hq
            omega
          · intro q hq
            have hqPrime := hs' q hq
            have hq2 : q ≠ 2 := by
              intro h
              subst q
              exact hps hq
            have hq3 : 3 ≤ q := by
              have := hqPrime.two_le
              omega
            calc
              q ≤ 2 * (q - 1) := by omega
              _ ≤ (q - 1) * (q - 1) := Nat.mul_le_mul_right _ (by omega)
              _ = (q - 1) ^ 2 := by ring
        nlinarith
      · have hp3 : 3 ≤ p := by
          have := hp.two_le
          omega
        have hpineq : p ≤ (p - 1) ^ 2 := by
          calc
            p ≤ 2 * (p - 1) := by omega
            _ ≤ (p - 1) * (p - 1) := Nat.mul_le_mul_right _ (by omega)
            _ = (p - 1) ^ 2 := by ring
        have hprod0 : 0 < ∏ q ∈ s, q := by
          apply Finset.prod_pos
          intro q hq
          exact (hs' q hq).pos
        have hsub0 : 0 ≤ ∏ q ∈ s, (q - 1) := by positivity
        have hmul := Nat.mul_le_mul (ih hs') hpineq
        nlinarith [sq_nonneg (∏ q ∈ s, (q - 1))]

private lemma totient_prod_primes (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) :
    (∏ p ∈ s, p).totient = ∏ p ∈ s, (p - 1) := by
  have hsq : Squarefree (∏ p ∈ s, p) := by
    classical
    induction s using Finset.induction_on with
    | empty => simp
    | @insert p s hps ih =>
        rw [Finset.prod_insert hps, Nat.squarefree_mul_iff]
        have hp : p.Prime := hs p (Finset.mem_insert_self p s)
        have hs' : ∀ q ∈ s, q.Prime := fun q hq => hs q (Finset.mem_insert_of_mem hq)
        refine ⟨hp.coprime_iff_not_dvd.mpr ?_, hp.squarefree, ih hs'⟩
        intro hpdiv
        rw [Prime.dvd_finsetProd_iff hp.prime] at hpdiv
        obtain ⟨q, hqs, hpq⟩ := hpdiv
        have hpqeq : p = q := (Nat.prime_dvd_prime_iff_eq hp (hs' q hqs)).mp hpq
        exact hps (hpqeq.symm ▸ hqs)
  rw [Nat.totient_eq_div_primeFactors_mul,
    Nat.prod_primeFactors_of_squarefree hsq]
  rw [Nat.div_self (Nat.pos_of_ne_zero hsq.ne_zero), one_mul]
  rw [Nat.primeFactors_prod hs]

private lemma inv_totient_prod_primes_le (s : Finset ℕ)
    (hs : ∀ p ∈ s, p.Prime) :
    1 / (((∏ p ∈ s, p).totient : ℕ) : ℝ) ≤
      2 / Real.sqrt (∏ p ∈ s, p) := by
  have hprod := prod_primes_le_two_mul_sub_one_sq s hs
  rw [totient_prod_primes s hs]
  let d : ℝ := ((∏ p ∈ s, p : ℕ) : ℝ)
  let t : ℝ := ((∏ p ∈ s, (p - 1) : ℕ) : ℝ)
  have hdpos : 0 < d := by
    have h : 0 < ∏ p ∈ s, p := by
      apply Finset.prod_pos
      intro p hp
      exact (hs p hp).pos
    dsimp [d]
    exact_mod_cast h
  have htpos : 0 < t := by
    have h : 0 < ∏ p ∈ s, (p - 1) := by
      apply Finset.prod_pos
      intro p hp
      exact Nat.sub_pos_of_lt (hs p hp).one_lt
    dsimp [t]
    exact_mod_cast h
  have hcast : d ≤ 2 * t ^ 2 := by
    dsimp [d, t]
    exact_mod_cast hprod
  have hsqrtpos : 0 < Real.sqrt d := Real.sqrt_pos.2 hdpos
  have hsqrtsq : Real.sqrt d ^ 2 = d := Real.sq_sqrt hdpos.le
  rw [← Nat.cast_prod]
  change 1 / t ≤ 2 / Real.sqrt d
  rw [div_le_div_iff₀ htpos hsqrtpos]
  have hroot : Real.sqrt d ≤ 2 * t := by
    rw [Real.sqrt_le_iff]
    constructor
    · positivity
    · nlinarith [sq_nonneg t]
  nlinarith

private lemma prime_euler_weight_product_le_nine (S : Finset ℕ)
    (hS : ∀ p ∈ S, p.Prime) :
    (∏ p ∈ S, (1 + 1 / ((p : ℝ) * (p - 1)))) ≤ 9 := by
  classical
  by_cases hSE : S = ∅
  · simp [hSE]
  let D := ∏ p ∈ S, p
  have hDpos : 0 < D := by
    dsimp [D]
    apply Finset.prod_pos
    intro p hp
    exact (hS p hp).pos
  have hsub : S ⊆ Finset.Ioc 1 D := by
    intro p hp
    rw [Finset.mem_Ioc]
    constructor
    · exact (hS p hp).one_lt
    · exact Nat.le_of_dvd hDpos (Finset.dvd_prod_of_mem id hp)
  have hsumSq : (∑ p ∈ S, (((p : ℝ) ^ 2)⁻¹)) ≤ 1 := by
    calc
      (∑ p ∈ S, (((p : ℝ) ^ 2)⁻¹)) ≤
          ∑ n ∈ Finset.Ioc 1 D, (((n : ℝ) ^ 2)⁻¹) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun n hn hnS => by positivity)
      _ ≤ (1 : ℝ)⁻¹ - (D : ℝ)⁻¹ :=
        by simpa using (sum_Ioc_inv_sq_le_sub (α := ℝ) one_ne_zero hDpos)
      _ ≤ 1 := by
        have : (0 : ℝ) ≤ (D : ℝ)⁻¹ := inv_nonneg.mpr (by positivity)
        norm_num
  have hsum : (∑ p ∈ S, 1 / ((p : ℝ) * (p - 1))) ≤ 2 := by
    calc
      (∑ p ∈ S, 1 / ((p : ℝ) * (p - 1))) ≤
          ∑ p ∈ S, 2 * (((p : ℝ) ^ 2)⁻¹) := by
        apply Finset.sum_le_sum
        intro p hp
        have hpPrime := hS p hp
        have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hpPrime.two_le
        have hp0 : (0 : ℝ) < p := by positivity
        have hpm1 : (0 : ℝ) < p - 1 := by linarith
        change 1 / ((p : ℝ) * (p - 1)) ≤ 2 / (p : ℝ) ^ 2
        rw [div_le_div_iff₀ (mul_pos hp0 hpm1) (sq_pos_of_pos hp0)]
        nlinarith
      _ = 2 * (∑ p ∈ S, (((p : ℝ) ^ 2)⁻¹)) := by
        rw [Finset.mul_sum]
      _ ≤ 2 := by nlinarith
  calc
    (∏ p ∈ S, (1 + 1 / ((p : ℝ) * (p - 1)))) ≤
        Real.exp (∑ p ∈ S, 1 / ((p : ℝ) * (p - 1))) :=
      Real.prod_one_add_le_exp_sum S (fun p => by
        by_cases hp : p ≤ 1
        · interval_cases p <;> norm_num
        · have hp2 : 2 ≤ p := by omega
          have hpR : (1 : ℝ) ≤ p := by exact_mod_cast (show 1 ≤ p by omega)
          exact one_div_nonneg.mpr
            (mul_nonneg (Nat.cast_nonneg _) (sub_nonneg.mpr hpR)))
    _ ≤ Real.exp 2 := Real.exp_le_exp.mpr hsum
    _ = Real.exp 1 ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
    _ ≤ 9 := by
      have he : Real.exp 1 ≤ 3 := (Real.exp_one_lt_d9.trans (by norm_num)).le
      nlinarith [Real.exp_pos 1]

private noncomputable def cubicRatio (p : ℕ) : ℝ :=
  2 * ((p : ℝ) / ((p - 1 : ℕ) : ℝ)) ^ 3

private lemma cubicRatio_nonneg (p : ℕ) : 0 ≤ cubicRatio p := by
  unfold cubicRatio
  positivity

private lemma cubicRatio_le_sixteen {p : ℕ} (hp : p.Prime) :
    cubicRatio p ≤ 16 := by
  have hden : (0 : ℝ) < (p - 1 : ℕ) := by
    exact_mod_cast Nat.sub_pos_of_lt hp.one_lt
  have hp2 : (p : ℝ) ≤ 2 * (p - 1 : ℕ) := by
    rw [Nat.cast_sub hp.one_le, Nat.cast_one]
    have : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
    linarith
  have hratio : (p : ℝ) / (p - 1 : ℕ) ≤ 2 := by
    rw [div_le_iff₀ hden]
    exact hp2
  have hratio0 : (0 : ℝ) ≤ (p : ℝ) / (p - 1 : ℕ) := by positivity
  have hcube := pow_le_pow_left₀ hratio0 hratio 3
  unfold cubicRatio
  norm_num at hcube ⊢
  linarith

private lemma cubicRatio_le_sqrt {p : ℕ} (hp : p.Prime) (h16 : 16 ≤ p) :
    cubicRatio p ≤ Real.sqrt p := by
  have hden : (0 : ℝ) < (p - 1 : ℕ) := by
    exact_mod_cast Nat.sub_pos_of_lt hp.one_lt
  have hratio0 : (0 : ℝ) ≤ (p : ℝ) / (p - 1 : ℕ) := by positivity
  have hratio : (p : ℝ) / (p - 1 : ℕ) ≤ 16 / 15 := by
    rw [div_le_iff₀ hden]
    rw [Nat.cast_sub hp.one_le, Nat.cast_one]
    have hpR : (16 : ℝ) ≤ p := by exact_mod_cast h16
    nlinarith
  have hcube := pow_le_pow_left₀ hratio0 hratio 3
  have hcubic : cubicRatio p ≤ 4 := by
    unfold cubicRatio
    norm_num at hcube ⊢
    linarith
  refine hcubic.trans ?_
  rw [Real.le_sqrt (by norm_num : (0 : ℝ) ≤ 4) (by positivity : (0 : ℝ) ≤ p)]
  exact_mod_cast h16

private lemma cubicRatio_product_le (N : ℕ) :
    (∏ p ∈ N.primeFactors, cubicRatio p) ≤
      (16 : ℝ) ^ 16 * Real.sqrt (∏ p ∈ N.primeFactors, p) := by
  classical
  let P := N.primeFactors
  let S := P.filter (fun p => p < 16)
  let T := P.filter (fun p => ¬p < 16)
  have hsCard : S.card ≤ 16 := by
    apply Finset.card_le_card (t := Finset.range 16)
    intro p hp
    exact Finset.mem_range.mpr (Finset.mem_filter.mp hp).2
  have hs : (∏ p ∈ S, cubicRatio p) ≤ (16 : ℝ) ^ 16 := by
    calc
      (∏ p ∈ S, cubicRatio p) ≤ ∏ _p ∈ S, (16 : ℝ) := by
        apply Finset.prod_le_prod
        · intro p hp
          exact cubicRatio_nonneg p
        · intro p hp
          exact cubicRatio_le_sixteen
            (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1)
      _ = (16 : ℝ) ^ S.card := by simp
      _ ≤ (16 : ℝ) ^ 16 := pow_le_pow_right₀ (by norm_num) hsCard
  have hTP : T ⊆ P := Finset.filter_subset _ _
  have hprodTP : (∏ p ∈ T, p) ≤ ∏ p ∈ P, p := by
    exact Finset.prod_le_prod_of_subset_of_one_le' hTP fun p hpP hpT =>
      (Nat.prime_of_mem_primeFactors hpP).one_le
  have ht : (∏ p ∈ T, cubicRatio p) ≤ Real.sqrt (∏ p ∈ P, p) := by
    calc
      (∏ p ∈ T, cubicRatio p) ≤ ∏ p ∈ T, Real.sqrt p := by
        apply Finset.prod_le_prod
        · intro p hp
          exact cubicRatio_nonneg p
        · intro p hp
          exact cubicRatio_le_sqrt
            (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1)
            (by
              have hpnot := (Finset.mem_filter.mp hp).2
              omega)
      _ = Real.sqrt (∏ p ∈ T, (p : ℝ)) :=
        (Real.sqrt_prod T (fun p hp => by positivity)).symm
      _ ≤ Real.sqrt (∏ p ∈ P, p) := Real.sqrt_le_sqrt (by
        simpa only [Nat.cast_prod] using (show
          ((∏ p ∈ T, p : ℕ) : ℝ) ≤ ((∏ p ∈ P, p : ℕ) : ℝ) by exact_mod_cast hprodTP))
  change (∏ p ∈ P, cubicRatio p) ≤
    (16 : ℝ) ^ 16 * Real.sqrt (∏ p ∈ P, p)
  rw [← Finset.prod_filter_mul_prod_filter_not P (fun p => p < 16) cubicRatio]
  change (∏ p ∈ S, cubicRatio p) * (∏ p ∈ T, cubicRatio p) ≤ _
  exact mul_le_mul hs ht (Finset.prod_nonneg fun p hp => cubicRatio_nonneg p) (by positivity)

private lemma pow_card_eq_cubicRatio_mul_density_cube (N : ℕ) :
    ((2 ^ N.primeFactors.card : ℕ) : ℝ) =
      (∏ p ∈ N.primeFactors, cubicRatio p) *
        (∏ p ∈ N.primeFactors, (1 - (p : ℝ)⁻¹)) ^ 3 := by
  push_cast
  rw [← Finset.prod_const, ← Finset.prod_pow]
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro p hp
  have hpPrime := Nat.prime_of_mem_primeFactors hp
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hpPrime.ne_zero
  have hpm1 : ((p : ℝ) - 1) ≠ 0 :=
    sub_ne_zero.mpr (by exact_mod_cast hpPrime.ne_one)
  unfold cubicRatio
  rw [Nat.cast_sub hpPrime.one_le, Nat.cast_one]
  field_simp [hp0, hpm1]

private lemma pow_primeFactors_card_le_density_cube (N K : ℕ)
    (hrad : (∏ p ∈ N.primeFactors, p) ≤ K ^ 2) :
    ((2 ^ N.primeFactors.card : ℕ) : ℝ) ≤
      (16 : ℝ) ^ 16 * K *
        (∏ p ∈ N.primeFactors, (1 - (p : ℝ)⁻¹)) ^ 3 := by
  have hsqrt : Real.sqrt (∏ p ∈ N.primeFactors, p) ≤ (K : ℝ) := by
    calc
      Real.sqrt (∏ p ∈ N.primeFactors, p) ≤ Real.sqrt ((K : ℝ) ^ 2) :=
        Real.sqrt_le_sqrt (by
          simpa only [Nat.cast_prod, Nat.cast_pow] using (show
            ((∏ p ∈ N.primeFactors, p : ℕ) : ℝ) ≤ ((K ^ 2 : ℕ) : ℝ) by
              exact_mod_cast hrad))
      _ = (K : ℝ) := Real.sqrt_sq (Nat.cast_nonneg K)
  have hdensity : 0 ≤ ∏ p ∈ N.primeFactors, (1 - (p : ℝ)⁻¹) := by
    apply Finset.prod_nonneg
    intro p hp
    have hpR : (1 : ℝ) ≤ p := by
      exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_le
    exact sub_nonneg.mpr ((inv_le_one₀ (by positivity : (0 : ℝ) < p)).2 hpR)
  rw [pow_card_eq_cubicRatio_mul_density_cube]
  calc
    (∏ p ∈ N.primeFactors, cubicRatio p) *
          (∏ p ∈ N.primeFactors, (1 - (p : ℝ)⁻¹)) ^ 3 ≤
        ((16 : ℝ) ^ 16 * Real.sqrt (∏ p ∈ N.primeFactors, p)) *
          (∏ p ∈ N.primeFactors, (1 - (p : ℝ)⁻¹)) ^ 3 := by
      gcongr
      exact cubicRatio_product_le N
    _ ≤ ((16 : ℝ) ^ 16 * K) *
          (∏ p ∈ N.primeFactors, (1 - (p : ℝ)⁻¹)) ^ 3 := by
      gcongr
    _ = _ := by ring

private lemma card_dvd_coprime_Ioc_zero (K Q d : ℕ) (hd : 0 < d)
    (hdQ : d.Coprime Q) :
    ((Finset.Ioc 0 K).filter fun c => d ∣ c ∧ Q.Coprime c).card =
      ((Finset.Ioc 0 (K / d)).filter fun b => Q.Coprime b).card := by
  classical
  rw [show ((Finset.Ioc 0 K).filter fun c => d ∣ c ∧ Q.Coprime c) =
      (((Finset.Ioc 0 (K / d)).filter fun b => Q.Coprime b).image fun b => d * b) by
    ext c
    simp only [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_image]
    constructor
    · rintro ⟨⟨hc0, hcK⟩, hdc, hQc⟩
      refine ⟨c / d, ⟨⟨?_, Nat.div_le_div_right hcK⟩, ?_⟩, ?_⟩
      · exact Nat.div_pos (Nat.le_of_dvd hc0 hdc) hd
      · have hcEq : d * (c / d) = c := by
          simpa [Nat.mul_comm] using (Nat.div_mul_cancel hdc)
        have hprod : (d * (c / d)).Coprime Q := hcEq.symm ▸ hQc.symm
        exact hprod.coprime_mul_left.symm
      · simpa [Nat.mul_comm] using Nat.div_mul_cancel hdc
    · rintro ⟨b, ⟨⟨hb0, hbK⟩, hQb⟩, rfl⟩
      refine ⟨⟨Nat.mul_pos hd hb0, ?_⟩, dvd_mul_right d b, ?_⟩
      · simpa [Nat.mul_comm] using (Nat.le_div_iff_mul_le hd).mp hbK
      · exact hdQ.symm.mul_right hQb]
  rw [Finset.card_image_of_injective _ (mul_right_injective₀ hd.ne')]

private lemma prod_subset_coprime (Q : ℕ) (S T : Finset ℕ) (hQ : Q ≠ 0)
    (hS : ∀ p ∈ S, p.Prime) (hTS : T ⊆ S)
    (hdisj : Disjoint Q.primeFactors S) :
    (∏ p ∈ T, p).Coprime Q := by
  classical
  induction T using Finset.induction_on with
  | empty => simp
  | @insert p T hpT ih =>
      rw [Finset.prod_insert hpT]
      have hpS : p ∈ S := hTS (Finset.mem_insert_self p T)
      have hpPrime := hS p hpS
      have hpNot : p ∉ Q.primeFactors := by
        intro hpQ
        exact Finset.disjoint_left.mp hdisj hpQ hpS
      have hpNotDvd : ¬p ∣ Q := by
        intro hpDvd
        exact hpNot (Nat.mem_primeFactors.mpr ⟨hpPrime, hpDvd, hQ⟩)
      have hpCop : p.Coprime Q := hpPrime.coprime_iff_not_dvd.mpr hpNotDvd
      have hTSub : T ⊆ S := fun q hq => hTS (Finset.mem_insert_of_mem hq)
      exact hpCop.mul_left (ih hTSub)

private lemma prod_primes_injective_on_powerset (S : Finset ℕ)
    (hS : ∀ p ∈ S, p.Prime) :
    Set.InjOn (fun T : Finset ℕ => ∏ p ∈ T, p) S.powerset := by
  intro T hT U hU hEq
  have hTp : ∀ p ∈ T, p.Prime := fun p hp => hS p (Finset.mem_powerset.mp hT hp)
  have hUp : ∀ p ∈ U, p.Prime := fun p hp => hS p (Finset.mem_powerset.mp hU hp)
  calc
    T = (∏ p ∈ T, p).primeFactors := (Nat.primeFactors_prod hTp).symm
    _ = (∏ p ∈ U, p).primeFactors := congrArg Nat.primeFactors hEq
    _ = U := Nat.primeFactors_prod hUp

/-- The local Pollington--Vaughan weight contributed by a finite set of primes. -/
noncomputable def coprimeIntervalPrimeWeight (S : Finset ℕ) (c : ℕ) : ℝ :=
  ∏ p ∈ S.filter (fun p => p ∣ c), (1 - (p : ℝ)⁻¹)⁻¹

private lemma prime_weight_factor_eq {p : ℕ} (hp : p.Prime) :
    (1 - (p : ℝ)⁻¹)⁻¹ = 1 + 1 / ((p : ℝ) - 1) := by
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hpm1 : (p : ℝ) - 1 ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hp.ne_one)
  field_simp [hp0, hpm1]
  ring

private lemma prod_primes_dvd_iff (T : Finset ℕ) (c : ℕ)
    (hT : ∀ p ∈ T, p.Prime) :
    (∏ p ∈ T, p) ∣ c ↔ ∀ p ∈ T, p ∣ c := by
  constructor
  · intro hd p hp
    exact (Finset.dvd_prod_of_mem id hp).trans hd
  · intro hall
    induction T using Finset.induction_on with
    | empty => simp
    | @insert p T hpT ih =>
        rw [Finset.prod_insert hpT]
        have hpPrime := hT p (Finset.mem_insert_self p T)
        have hTprime : ∀ q ∈ T, q.Prime :=
          fun q hq => hT q (Finset.mem_insert_of_mem hq)
        have hpCop : p.Coprime (∏ q ∈ T, q) := hpPrime.coprime_iff_not_dvd.mpr (by
          intro hpDvd
          rw [Prime.dvd_finsetProd_iff hpPrime.prime] at hpDvd
          obtain ⟨q, hqT, hpq⟩ := hpDvd
          have hpqEq : p = q :=
            (Nat.prime_dvd_prime_iff_eq hpPrime (hTprime q hqT)).mp hpq
          exact hpT (hpqEq.symm ▸ hqT))
        exact hpCop.mul_dvd_of_dvd_of_dvd
          (hall p (Finset.mem_insert_self p T))
          (ih hTprime (fun q hq => hall q (Finset.mem_insert_of_mem hq)))

private lemma subset_weight_term_eq (T : Finset ℕ) (c : ℕ)
    (hT : ∀ p ∈ T, p.Prime) :
    (∏ p ∈ T, if p ∣ c then 1 / ((p : ℝ) - 1) else 0) =
      if (∏ p ∈ T, p) ∣ c then
        1 / ((((∏ p ∈ T, p).totient : ℕ) : ℝ)) else 0 := by
  by_cases hall : ∀ p ∈ T, p ∣ c
  · have hd : (∏ p ∈ T, p) ∣ c := (prod_primes_dvd_iff T c hT).2 hall
    rw [if_pos hd]
    calc
      (∏ p ∈ T, if p ∣ c then 1 / ((p : ℝ) - 1) else 0) =
          ∏ p ∈ T, 1 / ((p : ℝ) - 1) := by
        apply Finset.prod_congr rfl
        intro p hp
        rw [if_pos (hall p hp)]
      _ = 1 / ((((∏ p ∈ T, p).totient : ℕ) : ℝ)) := by
        rw [totient_prod_primes T hT, Nat.cast_prod, one_div,
          ← Finset.prod_inv_distrib]
        apply Finset.prod_congr rfl
        intro p hp
        rw [Nat.cast_sub (hT p hp).one_le, Nat.cast_one]
        simp [one_div]
  · push Not at hall
    obtain ⟨p, hpT, hpnot⟩ := hall
    have hdnot : ¬(∏ p ∈ T, p) ∣ c := by
      intro hd
      exact hpnot ((Finset.dvd_prod_of_mem id hpT).trans hd)
    rw [if_neg hdnot]
    exact Finset.prod_eq_zero hpT (if_neg hpnot)

private lemma coprimeIntervalPrimeWeight_eq_subsetSum (S : Finset ℕ) (c : ℕ)
    (hS : ∀ p ∈ S, p.Prime) :
    coprimeIntervalPrimeWeight S c =
      ∑ T ∈ S.powerset, if (∏ p ∈ T, p) ∣ c then
        1 / ((((∏ p ∈ T, p).totient : ℕ) : ℝ)) else 0 := by
  classical
  rw [coprimeIntervalPrimeWeight, Finset.prod_filter]
  calc
    (∏ p ∈ S, if p ∣ c then (1 - (p : ℝ)⁻¹)⁻¹ else 1) =
        ∏ p ∈ S, (1 + if p ∣ c then 1 / ((p : ℝ) - 1) else 0) := by
      apply Finset.prod_congr rfl
      intro p hp
      by_cases hpc : p ∣ c
      · simp [hpc, prime_weight_factor_eq (hS p hp)]
      · simp [hpc]
    _ = ∑ T ∈ S.powerset,
        ∏ p ∈ T, (if p ∣ c then 1 / ((p : ℝ) - 1) else 0) :=
      Finset.prod_one_add S
    _ = _ := by
      apply Finset.sum_congr rfl
      intro T hT
      exact subset_weight_term_eq T c
        (fun p hp => hS p (Finset.mem_powerset.mp hT hp))

private lemma weighted_coprime_sum_eq_subset_count (Q K : ℕ) (S : Finset ℕ)
    (hS : ∀ p ∈ S, p.Prime) :
    (∑ c ∈ Finset.Ioc 0 K,
        if Q.Coprime c then coprimeIntervalPrimeWeight S c else 0) =
      ∑ T ∈ S.powerset,
        (1 / ((((∏ p ∈ T, p).totient : ℕ) : ℝ))) *
          (((Finset.Ioc 0 K).filter fun c =>
            (∏ p ∈ T, p) ∣ c ∧ Q.Coprime c).card : ℝ) := by
  classical
  simp_rw [coprimeIntervalPrimeWeight_eq_subsetSum S _ hS]
  calc
    (∑ c ∈ Finset.Ioc 0 K,
        if Q.Coprime c then
          ∑ T ∈ S.powerset,
            if (∏ p ∈ T, p) ∣ c then
              1 / ((((∏ p ∈ T, p).totient : ℕ) : ℝ)) else 0
        else 0) =
        ∑ c ∈ Finset.Ioc 0 K, ∑ T ∈ S.powerset,
          if Q.Coprime c then
            (if (∏ p ∈ T, p) ∣ c then
              1 / ((((∏ p ∈ T, p).totient : ℕ) : ℝ)) else 0)
          else 0 := by
      apply Finset.sum_congr rfl
      intro c hc
      by_cases hQc : Q.Coprime c <;> simp [hQc]
    _ = ∑ T ∈ S.powerset, ∑ c ∈ Finset.Ioc 0 K,
          if Q.Coprime c then
            (if (∏ p ∈ T, p) ∣ c then
              1 / ((((∏ p ∈ T, p).totient : ℕ) : ℝ)) else 0)
          else 0 := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro T hT
      rw [← Finset.sum_boole]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro c hc
      by_cases hQc : Q.Coprime c <;>
        by_cases hdc : (∏ p ∈ T, p) ∣ c <;> simp [hQc, hdc]

private lemma subset_main_sum_le_nine (S : Finset ℕ)
    (hS : ∀ p ∈ S, p.Prime) :
    (∑ T ∈ S.powerset,
      (1 / ((((∏ p ∈ T, p).totient : ℕ) : ℝ))) *
        (1 / ((∏ p ∈ T, p : ℕ) : ℝ))) ≤ 9 := by
  calc
    (∑ T ∈ S.powerset,
      (1 / ((((∏ p ∈ T, p).totient : ℕ) : ℝ))) *
        (1 / ((∏ p ∈ T, p : ℕ) : ℝ))) =
        ∑ T ∈ S.powerset,
          ∏ p ∈ T, (1 / ((p : ℝ) * (p - 1))) := by
      apply Finset.sum_congr rfl
      intro T hT
      have hTp : ∀ p ∈ T, p.Prime :=
        fun p hp => hS p (Finset.mem_powerset.mp hT hp)
      rw [totient_prod_primes T hTp, Nat.cast_prod, Nat.cast_prod,
        one_div, one_div, ← Finset.prod_inv_distrib,
        ← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro p hp
      rw [Nat.cast_sub (hTp p hp).one_le, Nat.cast_one]
      field_simp
    _ = ∏ p ∈ S, (1 + 1 / ((p : ℝ) * (p - 1))) :=
      (Finset.prod_one_add S).symm
    _ ≤ 9 := prime_euler_weight_product_le_nine S hS

private lemma subset_small_error_sum_le (S : Finset ℕ)
    (hS : ∀ p ∈ S, p.Prime) (M : ℕ) :
    (∑ T ∈ S.powerset.filter (fun T => (∏ p ∈ T, p) ≤ M),
      1 / ((((∏ p ∈ T, p).totient : ℕ) : ℝ))) ≤ M := by
  classical
  let U := S.powerset.filter (fun T => (∏ p ∈ T, p) ≤ M)
  have hinj : Set.InjOn (fun T : Finset ℕ => ∏ p ∈ T, p) U :=
    (prod_primes_injective_on_powerset S hS).mono (Finset.filter_subset _ _)
  have himage : U.image (fun T => ∏ p ∈ T, p) ⊆ Finset.Icc 1 M := by
    intro d hd
    obtain ⟨T, hTU, rfl⟩ := Finset.mem_image.mp hd
    rw [Finset.mem_Icc]
    constructor
    · have : 0 < ∏ p ∈ T, p := by
        apply Finset.prod_pos
        intro p hp
        exact (hS p (Finset.mem_powerset.mp (Finset.mem_filter.mp hTU).1 hp)).pos
      omega
    · exact (Finset.mem_filter.mp hTU).2
  have hcard : U.card ≤ M := by
    calc
      U.card = (U.image (fun T => ∏ p ∈ T, p)).card :=
        (Finset.card_image_of_injOn hinj).symm
      _ ≤ (Finset.Icc 1 M).card := Finset.card_le_card himage
      _ ≤ M := by simp
  change (∑ T ∈ U, 1 / ((((∏ p ∈ T, p).totient : ℕ) : ℝ))) ≤ M
  calc
    (∑ T ∈ U, 1 / ((((∏ p ∈ T, p).totient : ℕ) : ℝ))) ≤
        ∑ _T ∈ U, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro T hTU
      have hdpos : 0 < ∏ p ∈ T, p := by
        apply Finset.prod_pos
        intro p hp
        exact (hS p (Finset.mem_powerset.mp (Finset.mem_filter.mp hTU).1 hp)).pos
      have htot : (1 : ℝ) ≤ (∏ p ∈ T, p).totient := by
        exact_mod_cast (Nat.totient_pos.mpr hdpos)
      exact (div_le_one (by positivity)).2 htot
    _ = (U.card : ℝ) := by simp
    _ ≤ M := by exact_mod_cast hcard

private lemma rpow_neg_three_halves_eq (n : ℕ) :
    (n : ℝ) ^ (-(3 / 2 : ℝ)) = 1 / ((n : ℝ) * Real.sqrt n) := by
  by_cases hn : n = 0
  · simp [hn]
  · have hn0 : (0 : ℝ) ≤ n := by positivity
    have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
    rw [show -(3 / 2 : ℝ) = -(1 + 1 / 2) by norm_num,
      Real.rpow_neg hn0, Real.rpow_add hnpos, Real.rpow_one, ← Real.sqrt_eq_rpow]
    rw [one_div]

private lemma integral_rpow_neg_three_halves_le (a b : ℕ) (ha : 1 ≤ a) (hab : a ≤ b) :
    (∫ x in (a : ℝ)..(b : ℝ), x ^ (-(3 / 2 : ℝ))) ≤ 2 / Real.sqrt a := by
  rw [integral_rpow]
  · have ha0 : (0 : ℝ) < a := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one ha)
    have hpowb : 0 ≤ (b : ℝ) ^ (-(1 / 2 : ℝ)) :=
      Real.rpow_nonneg (by positivity) _
    rw [show -(3 / 2 : ℝ) + 1 = -(1 / 2 : ℝ) by norm_num]
    have haPow : (a : ℝ) ^ (-(1 / 2 : ℝ)) = 1 / Real.sqrt a := by
      rw [show -(1 / 2 : ℝ) = -(2 : ℝ)⁻¹ by norm_num,
        Real.rpow_neg (le_of_lt ha0), Real.sqrt_eq_rpow]
      simp [one_div]
    rw [haPow]
    have heq :
        ((b : ℝ) ^ (-(1 / 2 : ℝ)) - 1 / Real.sqrt a) / (-(1 / 2 : ℝ)) =
          2 / Real.sqrt a - 2 * (b : ℝ) ^ (-(1 / 2 : ℝ)) := by ring
    rw [heq]
    linarith
  · right
    constructor
    · norm_num
    · rw [Set.uIcc_of_le (by exact_mod_cast hab)]
      have ha0 : (0 : ℝ) < a := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one ha)
      exact fun hmem => (not_lt_of_ge hmem.1) ha0

private lemma antitone_rpow_neg_three_halves (a b : ℕ) (ha : 1 ≤ a) :
    AntitoneOn (fun x : ℝ => x ^ (-(3 / 2 : ℝ))) (Set.Icc (a : ℝ) b) := by
  exact (Real.antitoneOn_rpow_Ioi_of_exponent_nonpos (by norm_num)).mono (by
    intro x hx
    have ha0 : (0 : ℝ) < a := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one ha)
    exact ha0.trans_le hx.1)

private lemma sum_Ioc_rpow_neg_three_halves_le (M K : ℕ) :
    (∑ n ∈ Finset.Ioc M K, (n : ℝ) ^ (-(3 / 2 : ℝ))) ≤
      3 / Real.sqrt (M + 1) := by
  have hshift (a b : ℕ) :
      (∑ n ∈ Finset.Ioc a b, (n : ℝ) ^ (-(3 / 2 : ℝ))) =
        ∑ i ∈ Finset.Ico a b, ((i + 1 : ℕ) : ℝ) ^ (-(3 / 2 : ℝ)) := by
    classical
    symm
    refine Finset.sum_bij (fun i _ => i + 1) ?_ ?_ ?_ ?_
    · intro i hi
      simp only [Finset.mem_Ico, Finset.mem_Ioc] at hi ⊢
      omega
    · intro i₁ hi₁ i₂ hi₂ heq
      omega
    · intro n hn
      refine ⟨n - 1, ?_, ?_⟩
      · simp only [Finset.mem_Ioc, Finset.mem_Ico] at hn ⊢
        omega
      · simp only [Finset.mem_Ioc] at hn
        omega
    · intro i hi
      rfl
  by_cases hMK : M ≤ K
  · by_cases hM : M = 0
    · subst M
      by_cases hK : K = 0
      · subst K
        simp
      · obtain ⟨L, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hK
        have htail := AntitoneOn.sum_le_integral_Ico (f := fun x : ℝ =>
          x ^ (-(3 / 2 : ℝ))) (a := 1) (b := L + 1) (by omega)
          (antitone_rpow_neg_three_halves 1 (L + 1) (by omega))
        have hint := integral_rpow_neg_three_halves_le 1 (L + 1) (by omega) (by omega)
        rw [show Finset.Ioc 0 (L + 1) = insert 1 (Finset.Ioc 1 (L + 1)) by
          ext n
          simp
          omega, Finset.sum_insert (by simp)]
        rw [hshift]
        norm_num at htail hint ⊢
        linarith
    · have hMpos : 1 ≤ M := Nat.one_le_iff_ne_zero.mpr hM
      have htail := AntitoneOn.sum_le_integral_Ico (f := fun x : ℝ =>
        x ^ (-(3 / 2 : ℝ))) (a := M) (b := K) hMK
        (antitone_rpow_neg_three_halves M K hMpos)
      have hint := integral_rpow_neg_three_halves_le M K hMpos hMK
      have hsqrtM0 : 0 ≤ Real.sqrt M := Real.sqrt_nonneg _
      have hsqrtM1 : 0 ≤ Real.sqrt (M + 1) := Real.sqrt_nonneg _
      have hsqrtMpos : 0 < Real.sqrt M := Real.sqrt_pos.2 (by exact_mod_cast hMpos)
      have hsqrtM1pos : 0 < Real.sqrt (M + 1) := Real.sqrt_pos.2 (by positivity)
      have hsqrtMsq : Real.sqrt (M : ℝ) ^ 2 = M := Real.sq_sqrt (by positivity)
      have hsqrtM1sq : Real.sqrt ((M + 1 : ℕ) : ℝ) ^ 2 = ((M + 1 : ℕ) : ℝ) :=
        Real.sq_sqrt (by positivity)
      have hcompare : 2 / Real.sqrt M ≤ 3 / Real.sqrt (M + 1) := by
        rw [div_le_div_iff₀ hsqrtMpos hsqrtM1pos]
        have hroot : Real.sqrt ((M + 1 : ℕ) : ℝ) ≤
            (3 / 2 : ℝ) * Real.sqrt (M : ℝ) := by
          rw [Real.sqrt_le_iff]
          constructor
          · positivity
          · calc
              ((M + 1 : ℕ) : ℝ) = (M : ℝ) + 1 := by norm_num
              _ ≤ (9 / 4 : ℝ) * M := by
                nlinarith [show (1 : ℝ) ≤ M by exact_mod_cast hMpos]
              _ = ((3 / 2 : ℝ) * Real.sqrt (M : ℝ)) ^ 2 := by
                rw [mul_pow, hsqrtMsq]
                ring
        norm_num only [Nat.cast_add, Nat.cast_one] at hroot
        linarith
      rw [hshift]
      exact htail.trans (hint.trans hcompare)
  · have hKM : K ≤ M := Nat.le_of_not_ge hMK
    have : (0 : ℝ) ≤ 3 / Real.sqrt (M + 1) := by positivity
    simpa [Finset.Ioc_eq_empty (not_lt_of_ge hKM)] using this

private lemma subset_tail_sum_le (S : Finset ℕ)
    (hS : ∀ p ∈ S, p.Prime) (M K : ℕ) :
    (∑ T ∈ S.powerset.filter (fun T =>
        M < (∏ p ∈ T, p) ∧ (∏ p ∈ T, p) ≤ K),
      (1 / ((((∏ p ∈ T, p).totient : ℕ) : ℝ))) *
        (1 / ((∏ p ∈ T, p : ℕ) : ℝ))) ≤
      6 / Real.sqrt (M + 1) := by
  classical
  let V := S.powerset.filter (fun T =>
    M < (∏ p ∈ T, p) ∧ (∏ p ∈ T, p) ≤ K)
  have hinj : Set.InjOn (fun T : Finset ℕ => ∏ p ∈ T, p) V :=
    (prod_primes_injective_on_powerset S hS).mono (Finset.filter_subset _ _)
  have himage : V.image (fun T => ∏ p ∈ T, p) ⊆ Finset.Ioc M K := by
    intro d hd
    obtain ⟨T, hTV, rfl⟩ := Finset.mem_image.mp hd
    simpa only [Finset.mem_Ioc] using (Finset.mem_filter.mp hTV).2
  change (∑ T ∈ V,
      (1 / ((((∏ p ∈ T, p).totient : ℕ) : ℝ))) *
        (1 / ((∏ p ∈ T, p : ℕ) : ℝ))) ≤ _
  calc
    (∑ T ∈ V,
      (1 / ((((∏ p ∈ T, p).totient : ℕ) : ℝ))) *
        (1 / ((∏ p ∈ T, p : ℕ) : ℝ))) ≤
        ∑ T ∈ V, 2 * (((∏ p ∈ T, p : ℕ) : ℝ) ^ (-(3 / 2 : ℝ))) := by
      apply Finset.sum_le_sum
      intro T hTV
      have hTp : ∀ p ∈ T, p.Prime := fun p hp =>
        hS p (Finset.mem_powerset.mp (Finset.mem_filter.mp hTV).1 hp)
      have hcoeff := inv_totient_prod_primes_le T hTp
      have hcoeff' :
          1 / ((((∏ p ∈ T, p).totient : ℕ) : ℝ)) ≤
            2 / Real.sqrt (((∏ p ∈ T, p : ℕ) : ℝ)) := by
        simpa only [Nat.cast_prod] using hcoeff
      rw [rpow_neg_three_halves_eq]
      have hinv : 0 ≤ 1 / ((∏ p ∈ T, p : ℕ) : ℝ) := by positivity
      calc
        (1 / ((((∏ p ∈ T, p).totient : ℕ) : ℝ))) *
            (1 / ((∏ p ∈ T, p : ℕ) : ℝ)) ≤
            (2 / Real.sqrt (((∏ p ∈ T, p : ℕ) : ℝ))) *
              (1 / ((∏ p ∈ T, p : ℕ) : ℝ)) :=
          mul_le_mul_of_nonneg_right hcoeff' hinv
        _ = 2 * (1 / (((∏ p ∈ T, p : ℕ) : ℝ) *
              Real.sqrt (((∏ p ∈ T, p : ℕ) : ℝ)))) := by ring
    _ = ∑ d ∈ V.image (fun T => ∏ p ∈ T, p),
          2 * ((d : ℝ) ^ (-(3 / 2 : ℝ))) := by
      rw [Finset.sum_image hinj]
    _ ≤ ∑ d ∈ Finset.Ioc M K,
          2 * ((d : ℝ) ^ (-(3 / 2 : ℝ))) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg himage
      intro d hd hdimage
      exact mul_nonneg (by norm_num) (Real.rpow_nonneg (by positivity) _)
    _ = 2 * (∑ d ∈ Finset.Ioc M K,
          ((d : ℝ) ^ (-(3 / 2 : ℝ)))) := by rw [Finset.mul_sum]
    _ ≤ 2 * (3 / Real.sqrt (M + 1)) := by
      gcongr
      exact sum_Ioc_rpow_neg_three_halves_le M K
    _ = 6 / Real.sqrt (M + 1) := by ring


private lemma subset_coprime_count_le_error (Q K : ℕ) (S T : Finset ℕ)
    (hQ : 0 < Q) (hS : ∀ p ∈ S, p.Prime) (hT : T ∈ S.powerset)
    (hdisj : Disjoint Q.primeFactors S) :
    ((((Finset.Ioc 0 K).filter fun c =>
      (∏ p ∈ T, p) ∣ c ∧ Q.Coprime c).card : ℕ) : ℝ) ≤
      (K : ℝ) * (1 / ((∏ p ∈ T, p : ℕ) : ℝ)) *
        ((Q.totient : ℝ) / Q) + (2 ^ Q.primeFactors.card : ℕ) := by
  let d := ∏ p ∈ T, p
  have hTp : ∀ p ∈ T, p.Prime :=
    fun p hp => hS p (Finset.mem_powerset.mp hT hp)
  have hd : 0 < d := by
    dsimp [d]
    apply Finset.prod_pos
    intro p hp
    exact (hTp p hp).pos
  have hdQ : d.Coprime Q :=
    prod_subset_coprime Q S T hQ.ne' hS (Finset.mem_powerset.mp hT) hdisj
  have hcard := card_dvd_coprime_Ioc_zero K Q d hd hdQ
  have hbase := coprimeInterval_card_le_density_add_error 0 (K / d) Q hQ
  simp only [Nat.sub_zero] at hbase
  rw [hcard]
  have hdiv : (((K / d : ℕ) : ℝ)) ≤ (K : ℝ) / d := Nat.cast_div_le
  calc
    ((((Finset.Ioc 0 (K / d)).filter fun x => Q.Coprime x).card : ℕ) : ℝ) ≤
        ((K / d : ℕ) : ℝ) * ((Q.totient : ℝ) / Q) +
          (2 ^ Q.primeFactors.card : ℕ) := by
      simpa [mul_div_assoc] using hbase
    _ ≤ ((K : ℝ) / d) * ((Q.totient : ℝ) / Q) +
        (2 ^ Q.primeFactors.card : ℕ) := by gcongr
    _ = (K : ℝ) * (1 / (d : ℝ)) * ((Q.totient : ℝ) / Q) +
        (2 ^ Q.primeFactors.card : ℕ) := by ring

private lemma subset_coprime_count_le_trivial (Q K : ℕ) (S T : Finset ℕ)
    (hQ : 0 < Q) (hS : ∀ p ∈ S, p.Prime) (hT : T ∈ S.powerset)
    (hdisj : Disjoint Q.primeFactors S) :
    ((((Finset.Ioc 0 K).filter fun c =>
      (∏ p ∈ T, p) ∣ c ∧ Q.Coprime c).card : ℕ) : ℝ) ≤
      (K : ℝ) * (1 / ((∏ p ∈ T, p : ℕ) : ℝ)) := by
  let d := ∏ p ∈ T, p
  have hTp : ∀ p ∈ T, p.Prime :=
    fun p hp => hS p (Finset.mem_powerset.mp hT hp)
  have hd : 0 < d := by
    dsimp [d]
    apply Finset.prod_pos
    intro p hp
    exact (hTp p hp).pos
  have hdQ : d.Coprime Q :=
    prod_subset_coprime Q S T hQ.ne' hS (Finset.mem_powerset.mp hT) hdisj
  rw [card_dvd_coprime_Ioc_zero K Q d hd hdQ]
  calc
    ((((Finset.Ioc 0 (K / d)).filter fun b => Q.Coprime b).card : ℕ) : ℝ) ≤
        ((Finset.Ioc 0 (K / d)).card : ℝ) := by
      exact_mod_cast Finset.card_filter_le _ _
    _ = ((K / d : ℕ) : ℝ) := by simp
    _ ≤ (K : ℝ) / d := Nat.cast_div_le
    _ = (K : ℝ) * (1 / (d : ℝ)) := by ring

private lemma subset_coprime_count_eq_zero (Q K : ℕ) (S T : Finset ℕ)
    (hQ : 0 < Q) (hS : ∀ p ∈ S, p.Prime) (hT : T ∈ S.powerset)
    (hdisj : Disjoint Q.primeFactors S) (hTK : K < ∏ p ∈ T, p) :
    ((Finset.Ioc 0 K).filter fun c =>
      (∏ p ∈ T, p) ∣ c ∧ Q.Coprime c).card = 0 := by
  let d := ∏ p ∈ T, p
  have hTp : ∀ p ∈ T, p.Prime :=
    fun p hp => hS p (Finset.mem_powerset.mp hT hp)
  have hd : 0 < d := by
    dsimp [d]
    apply Finset.prod_pos
    intro p hp
    exact (hTp p hp).pos
  have hdQ : d.Coprime Q :=
    prod_subset_coprime Q S T hQ.ne' hS (Finset.mem_powerset.mp hT) hdisj
  rw [card_dvd_coprime_Ioc_zero K Q d hd hdQ]
  have hKd : K / d = 0 := Nat.div_eq_of_lt hTK
  simp [hKd]

private lemma weighted_subset_count_decomp (Q K M : ℕ) (S : Finset ℕ)
    (hQ : 0 < Q) (hS : ∀ p ∈ S, p.Prime)
    (hdisj : Disjoint Q.primeFactors S) :
    (∑ T ∈ S.powerset,
      (1 / ((((∏ p ∈ T, p).totient : ℕ) : ℝ))) *
        (((Finset.Ioc 0 K).filter fun c =>
          (∏ p ∈ T, p) ∣ c ∧ Q.Coprime c).card : ℝ)) ≤
      (K : ℝ) * ((Q.totient : ℝ) / Q) *
        (∑ T ∈ S.powerset,
          (1 / ((((∏ p ∈ T, p).totient : ℕ) : ℝ))) *
            (1 / ((∏ p ∈ T, p : ℕ) : ℝ))) +
      (2 ^ Q.primeFactors.card : ℕ) *
        (∑ T ∈ S.powerset.filter (fun T => (∏ p ∈ T, p) ≤ M),
          1 / ((((∏ p ∈ T, p).totient : ℕ) : ℝ))) +
      (K : ℝ) *
        (∑ T ∈ S.powerset.filter (fun T =>
            M < (∏ p ∈ T, p) ∧ (∏ p ∈ T, p) ≤ K),
          (1 / ((((∏ p ∈ T, p).totient : ℕ) : ℝ))) *
            (1 / ((∏ p ∈ T, p : ℕ) : ℝ))) := by
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  rw [Finset.sum_filter, Finset.sum_filter]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro T hT
  let d := ∏ p ∈ T, p
  let a : ℝ := 1 / ((d.totient : ℕ) : ℝ)
  have hTp : ∀ p ∈ T, p.Prime :=
    fun p hp => hS p (Finset.mem_powerset.mp hT hp)
  have hd : 0 < d := by
    dsimp [d]
    apply Finset.prod_pos
    intro p hp
    exact (hTp p hp).pos
  have ha : 0 ≤ a := by dsimp [a]; positivity
  by_cases hsmallT : d ≤ M
  · have hc := subset_coprime_count_le_error Q K S T hQ hS hT hdisj
    have hnotLarge : ¬ M < d := not_lt_of_ge hsmallT
    change a * _ ≤ _
    calc
      a * ((({c ∈ Finset.Ioc 0 K | d ∣ c ∧ Q.Coprime c}.card : ℕ) : ℝ)) ≤
          a * ((K : ℝ) * (1 / (d : ℝ)) * ((Q.totient : ℝ) / Q) +
            (2 ^ Q.primeFactors.card : ℕ)) :=
        mul_le_mul_of_nonneg_left hc ha
      _ = (K : ℝ) * ((Q.totient : ℝ) / Q) *
          (a * (1 / (d : ℝ))) +
          (2 ^ Q.primeFactors.card : ℕ) * a + 0 := by ring
      _ = _ := by
        simp [a, d, hsmallT, hnotLarge, Nat.cast_prod, one_div]
  · have hlargeM : M < d := Nat.lt_of_not_ge hsmallT
    by_cases hdK : d ≤ K
    · have hc := subset_coprime_count_le_trivial Q K S T hQ hS hT hdisj
      change a * _ ≤ _
      calc
        a * ((({c ∈ Finset.Ioc 0 K | d ∣ c ∧ Q.Coprime c}.card : ℕ) : ℝ)) ≤
            a * ((K : ℝ) * (1 / (d : ℝ))) :=
          mul_le_mul_of_nonneg_left hc ha
        _ = (K : ℝ) * (a * (1 / (d : ℝ))) := by ring
        _ ≤ (K : ℝ) * ((Q.totient : ℝ) / Q) *
            (a * (1 / (d : ℝ))) + 0 +
            (K : ℝ) * (a * (1 / (d : ℝ))) := by
          have hmainNonneg : 0 ≤ (K : ℝ) * ((Q.totient : ℝ) / Q) *
              (a * (1 / (d : ℝ))) := by positivity
          linarith
        _ = _ := by
          simp [a, d, hsmallT, hlargeM, hdK, Nat.cast_prod, one_div]
    · have hKd : K < d := Nat.lt_of_not_ge hdK
      have hz := subset_coprime_count_eq_zero Q K S T hQ hS hT hdisj hKd
      change a * _ ≤ _
      rw [hz]
      simp only [CharP.cast_eq_zero, mul_zero, one_div, Nat.cast_prod,
        Nat.cast_pow, Nat.cast_ofNat]
      positivity

private lemma error_mul_threshold_le (Q K : ℕ) (hQ : 0 < Q) :
    let e : ℕ := 2 ^ Q.primeFactors.card
    let M : ℕ := K * Q.totient / (e * Q)
    (e : ℝ) * M ≤ (K : ℝ) * ((Q.totient : ℝ) / Q) := by
  dsimp only
  let e : ℕ := 2 ^ Q.primeFactors.card
  have hnat : e * Q * (K * Q.totient / (e * Q)) ≤ K * Q.totient := by
    simpa [mul_assoc] using Nat.mul_div_le (K * Q.totient) (e * Q)
  have hreal : (e : ℝ) * Q * ((K * Q.totient / (e * Q) : ℕ) : ℝ) ≤
      (K : ℝ) * Q.totient := by
    exact_mod_cast hnat
  rw [show (K : ℝ) * ((Q.totient : ℝ) / Q) =
    ((K : ℝ) * Q.totient) / Q by ring]
  rw [le_div_iff₀ (by exact_mod_cast hQ)]
  simpa [e, mul_comm, mul_left_comm, mul_assoc] using hreal

private lemma threshold_inv_sqrt_le (Q K : ℕ) (hQ : 0 < Q)
    (hrad : (∏ p ∈ Q.primeFactors, p) ≤ K ^ 2) :
    let e : ℕ := 2 ^ Q.primeFactors.card
    let M : ℕ := K * Q.totient / (e * Q)
    1 / Real.sqrt (M + 1) ≤
      (16 : ℝ) ^ 8 * ((Q.totient : ℝ) / Q) := by
  dsimp only
  let e : ℕ := 2 ^ Q.primeFactors.card
  let M : ℕ := K * Q.totient / (e * Q)
  let δ : ℝ := (Q.totient : ℝ) / Q
  let C : ℝ := (16 : ℝ) ^ 8
  have hradpos : 0 < ∏ p ∈ Q.primeFactors, p := by
    apply Finset.prod_pos
    intro p hp
    exact (Nat.prime_of_mem_primeFactors hp).pos
  have hK : 0 < K := by
    by_contra h
    have hK0 : K = 0 := Nat.eq_zero_of_not_pos h
    simp [hK0] at hrad
    omega
  have htot : 0 < Q.totient := Nat.totient_pos.mpr hQ
  have he : 0 < e := by simp [e]
  have hden : 0 < e * Q := Nat.mul_pos he hQ
  have hecube := pow_primeFactors_card_le_density_cube Q K hrad
  have hdensity :
      (∏ p ∈ Q.primeFactors, (1 - (p : ℝ)⁻¹)) = δ := by
    simpa [δ] using primeDensity_eq_totient_div Q hQ.ne'
  rw [hdensity] at hecube
  change (e : ℝ) ≤ (16 : ℝ) ^ 16 * K * δ ^ 3 at hecube
  have hquotNat : K * Q.totient < e * Q * (M + 1) := by
    have hlt := (Nat.div_lt_iff_lt_mul hden).mp
      (Nat.lt_succ_self (K * Q.totient / (e * Q)))
    change K * Q.totient < e * Q * (K * Q.totient / (e * Q) + 1)
    simpa [mul_comm, mul_left_comm, mul_assoc] using hlt
  have hquot : (K : ℝ) * Q.totient < (e : ℝ) * Q * (M + 1) := by
    exact_mod_cast hquotNat
  have hecube' : (e : ℝ) * (Q : ℝ) ^ 3 ≤
      C ^ 2 * (K : ℝ) * (Q.totient : ℝ) ^ 3 := by
    have hQreal : (0 : ℝ) < Q := by exact_mod_cast hQ
    have hm := mul_le_mul_of_nonneg_right hecube (le_of_lt (pow_pos hQreal 3))
    dsimp [δ, C] at hm ⊢
    calc
      (e : ℝ) * (Q : ℝ) ^ 3 ≤
          ((16 : ℝ) ^ 16 * (K : ℝ) *
            (((Q.totient : ℝ) / Q) ^ 3)) * (Q : ℝ) ^ 3 := hm
      _ = ((16 : ℝ) ^ 8) ^ 2 * (K : ℝ) * (Q.totient : ℝ) ^ 3 := by
        field_simp
  have hbig : (Q : ℝ) ^ 2 <
      C ^ 2 * (Q.totient : ℝ) ^ 2 * (M + 1) := by
    have hKtot : 0 < (K : ℝ) * Q.totient := by positivity
    have hchain : ((K : ℝ) * Q.totient) * (Q : ℝ) ^ 2 <
        ((K : ℝ) * Q.totient) *
          (C ^ 2 * (Q.totient : ℝ) ^ 2 * (M + 1)) := by
      calc
      ((K : ℝ) * Q.totient) * (Q : ℝ) ^ 2 <
          ((e : ℝ) * Q * (M + 1)) * (Q : ℝ) ^ 2 :=
        mul_lt_mul_of_pos_right hquot (sq_pos_of_pos (by exact_mod_cast hQ))
      _ = ((e : ℝ) * (Q : ℝ) ^ 3) * (M + 1) := by ring
      _ ≤ (C ^ 2 * (K : ℝ) * (Q.totient : ℝ) ^ 3) * (M + 1) := by
        gcongr
      _ = ((K : ℝ) * Q.totient) *
          (C ^ 2 * (Q.totient : ℝ) ^ 2 * (M + 1)) := by ring
    exact lt_of_mul_lt_mul_left hchain hKtot.le
  have hspos : 0 < Real.sqrt ((M + 1 : ℕ) : ℝ) := Real.sqrt_pos.2 (by positivity)
  norm_num only [Nat.cast_add, Nat.cast_one] at hspos
  have hQreal : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hsSq : Real.sqrt ((M + 1 : ℕ) : ℝ) ^ 2 = ((M + 1 : ℕ) : ℝ) :=
    Real.sq_sqrt (by positivity)
  norm_num only [Nat.cast_add, Nat.cast_one] at hsSq
  have hroot : (Q : ℝ) ≤
      C * (Q.totient : ℝ) * Real.sqrt (M + 1) := by
    have hright : 0 ≤ C * (Q.totient : ℝ) * Real.sqrt (M + 1) := by positivity
    have hsquare : (Q : ℝ) ^ 2 <
        (C * (Q.totient : ℝ) * Real.sqrt (M + 1)) ^ 2 := by
      calc
        (Q : ℝ) ^ 2 < C ^ 2 * (Q.totient : ℝ) ^ 2 * (M + 1) := hbig
        _ = (C * (Q.totient : ℝ) * Real.sqrt (M + 1)) ^ 2 := by
          rw [mul_pow, mul_pow, hsSq]
    nlinarith [sq_nonneg
      (C * (Q.totient : ℝ) * Real.sqrt ((M + 1 : ℕ) : ℝ) + Q)]
  change 1 / Real.sqrt (M + 1) ≤ C * δ
  dsimp [δ, C]
  rw [show (16 : ℝ) ^ 8 * ((Q.totient : ℝ) / Q) =
    ((16 : ℝ) ^ 8 * Q.totient) / Q by ring]
  rw [div_le_div_iff₀ hspos hQreal]
  simpa [mul_assoc] using hroot

/-- An explicit absolute constant for the weighted coprime-interval sieve. -/
def weightedCoprimeIntervalConstant : ℝ := 10 + 6 * (16 : ℝ) ^ 8

/--
Weighted coprime-interval sieve in the form needed by the
Pollington--Vaughan overlap estimate.  The local weight is
`∏ p ∈ S.filter (p ∣ c), (1 - 1 / p)⁻¹`.  The auxiliary primes in `S` must
be disjoint from the prime divisors of the sieving modulus `Q`.
-/
theorem weightedCoprimeInterval_sum_le (Q K : ℕ) (S : Finset ℕ)
    (hQ : 0 < Q) (hS : ∀ p ∈ S, p.Prime)
    (hdisj : Disjoint Q.primeFactors S)
    (hrad : (∏ p ∈ Q.primeFactors, p) ≤ K ^ 2) :
    (∑ c ∈ Finset.Ioc 0 K,
      if Q.Coprime c then coprimeIntervalPrimeWeight S c else 0) ≤
      weightedCoprimeIntervalConstant * K * (Q.totient : ℝ) / Q := by
  let e : ℕ := 2 ^ Q.primeFactors.card
  let M : ℕ := K * Q.totient / (e * Q)
  have hdecomp := weighted_subset_count_decomp Q K M S hQ hS hdisj
  have hmain := subset_main_sum_le_nine S hS
  have hsmall := subset_small_error_sum_le S hS M
  have htail := subset_tail_sum_le S hS M K
  have hsmallAbsorb := error_mul_threshold_le Q K hQ
  have htailAbsorb := threshold_inv_sqrt_le Q K hQ hrad
  dsimp only at hsmallAbsorb htailAbsorb
  rw [weighted_coprime_sum_eq_subset_count Q K S hS]
  calc
    (∑ T ∈ S.powerset,
      (1 / ((((∏ p ∈ T, p).totient : ℕ) : ℝ))) *
        (((Finset.Ioc 0 K).filter fun c =>
          (∏ p ∈ T, p) ∣ c ∧ Q.Coprime c).card : ℝ)) ≤
      (K : ℝ) * ((Q.totient : ℝ) / Q) *
        (∑ T ∈ S.powerset,
          (1 / ((((∏ p ∈ T, p).totient : ℕ) : ℝ))) *
            (1 / ((∏ p ∈ T, p : ℕ) : ℝ))) +
      (e : ℝ) *
        (∑ T ∈ S.powerset.filter (fun T => (∏ p ∈ T, p) ≤ M),
          1 / ((((∏ p ∈ T, p).totient : ℕ) : ℝ))) +
      (K : ℝ) *
        (∑ T ∈ S.powerset.filter (fun T =>
            M < (∏ p ∈ T, p) ∧ (∏ p ∈ T, p) ≤ K),
          (1 / ((((∏ p ∈ T, p).totient : ℕ) : ℝ))) *
            (1 / ((∏ p ∈ T, p : ℕ) : ℝ))) := by
      simpa [e] using hdecomp
    _ ≤ (K : ℝ) * ((Q.totient : ℝ) / Q) * 9 +
        (e : ℝ) * M + (K : ℝ) * (6 / Real.sqrt (M + 1)) := by
      gcongr
    _ ≤ (K : ℝ) * ((Q.totient : ℝ) / Q) * 9 +
        (K : ℝ) * ((Q.totient : ℝ) / Q) +
        (K : ℝ) * (6 * ((16 : ℝ) ^ 8 * ((Q.totient : ℝ) / Q))) := by
      gcongr
      have htail' : 6 / Real.sqrt (M + 1) ≤
          6 * ((16 : ℝ) ^ 8 * ((Q.totient : ℝ) / Q)) := by
        calc
          6 / Real.sqrt (M + 1) = 6 * (1 / Real.sqrt (M + 1)) := by ring
          _ ≤ 6 * ((16 : ℝ) ^ 8 * ((Q.totient : ℝ) / Q)) :=
            mul_le_mul_of_nonneg_left (by simpa [e, M] using htailAbsorb) (by norm_num)
      exact htail'
    _ = weightedCoprimeIntervalConstant * K * (Q.totient : ℝ) / Q := by
      rw [weightedCoprimeIntervalConstant]
      ring

#print axioms coprimeInterval_card_le
#print axioms weightedCoprimeInterval_sum_le

end Erdos999
