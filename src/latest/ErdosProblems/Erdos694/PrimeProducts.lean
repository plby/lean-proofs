import ErdosProblems.Erdos694.Core

/-!
# Replacing a Linnik prime by a product of primes

The collision identity only needs a positive integer `N` whose totient is
divisible by `A Y` and coprime to `N`. A product of distinct odd primes in
one dyadic interval has the latter property.
-/

namespace Erdos694.LowerConstruction

open scoped BigOperators

lemma totient_P_mul_U_mul_Q (Y U : ℕ) (hU : 0 < U) :
    Nat.totient (P Y * U * Q Y U) =
      A Y * U * ∏ q ∈ largeFactors Y U, (q - 1) := by
  have hkey := Nat.totient_mul_prod_primeFactors (P Y * U * Q Y U)
  rw [primeFactors_b Y U hU (Q_dvd_U Y U hU.ne'),
    Finset.prod_union (smallPrimes_disjoint_largeFactors Y U),
    Finset.prod_union (smallPrimes_disjoint_largeFactors Y U),
    prod_smallPrimes_eq_P, prod_largeFactors_eq_Q,
    prod_smallPrimes_sub_one_eq_A] at hkey
  apply Nat.eq_of_mul_eq_mul_right (Nat.mul_pos (P_pos Y) (Q_pos Y U))
  rw [hkey]
  ring

lemma totient_Q (Y U : ℕ) (hU : U ≠ 0) :
    Nat.totient (Q Y U) = ∏ q ∈ largeFactors Y U, (q - 1) := by
  have hkey := Nat.totient_mul_prod_primeFactors (Q Y U)
  rw [primeFactors_Q Y U hU, prod_largeFactors_eq_Q] at hkey
  apply Nat.eq_of_mul_eq_mul_right (Q_pos Y U)
  rw [hkey, mul_comm]

lemma composite_collision (Y N : ℕ) (hN : 0 < N)
    (hcop : N.Coprime (Nat.totient N)) (hA : A Y ∣ Nat.totient N) :
    let U := Nat.totient N / A Y
    Nat.totient (N * Q Y U) = Nat.totient (P Y * U * Q Y U) := by
  dsimp only
  let U := Nat.totient N / A Y
  have hAU : A Y * U = Nat.totient N := Nat.mul_div_cancel' hA
  have hU : 0 < U := Nat.div_pos (Nat.le_of_dvd (Nat.totient_pos.mpr hN) hA)
    (A_pos Y)
  have hUd : U ∣ Nat.totient N := by
    rw [← hAU]
    exact dvd_mul_left _ _
  have hQcop : N.Coprime (Q Y U) :=
    hcop.of_dvd_right ((Q_dvd_U Y U hU.ne').trans hUd)
  change Nat.totient (N * Q Y U) = Nat.totient (P Y * U * Q Y U)
  rw [Nat.totient_mul hQcop, totient_Q Y U hU.ne',
    totient_P_mul_U_mul_Q Y U hU, hAU]

lemma composite_collision_ratio (Y N : ℕ) (hN : 0 < N)
    (hA : A Y ∣ Nat.totient N) :
    let U := Nat.totient N / A Y
    ((P Y * U * Q Y U : ℕ) : ℝ) / (N * Q Y U : ℕ) =
      primeEulerProdNat Y * ((Nat.totient N : ℝ) / N) := by
  dsimp only
  let U := Nat.totient N / A Y
  have hAU : A Y * U = Nat.totient N := Nat.mul_div_cancel' hA
  have hAU' : (A Y : ℝ) * U = Nat.totient N := by exact_mod_cast hAU
  have hAR : (A Y : ℝ) ≠ 0 := by exact_mod_cast (A_pos Y).ne'
  have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hQR : (Q Y U : ℝ) ≠ 0 := by exact_mod_cast (Q_pos Y U).ne'
  change ((P Y * U * Q Y U : ℕ) : ℝ) / (N * Q Y U : ℕ) = _
  rw [← P_div_A_eq_primeEulerProdNat]
  push_cast
  rw [← hAU']
  field_simp

lemma composite_collision_size (Y N : ℕ) (hN : 0 < N)
    (hA : A Y ∣ Nat.totient N) :
    let U := Nat.totient N / A Y
    Nat.totient (N * Q Y U) ≤ N ^ 2 := by
  dsimp only
  let U := Nat.totient N / A Y
  have hU : 0 < U := Nat.div_pos (Nat.le_of_dvd (Nat.totient_pos.mpr hN) hA)
    (A_pos Y)
  have hQ : Q Y U ≤ U := Nat.le_of_dvd hU (Q_dvd_U Y U hU.ne')
  calc
    Nat.totient (N * Q Y U) ≤ N * Q Y U := Nat.totient_le _
    _ ≤ N * N := Nat.mul_le_mul_left N
      (hQ.trans ((Nat.div_le_self _ _).trans (Nat.totient_le N)))
    _ = N ^ 2 := by ring

lemma totient_prod_primes (S : Finset ℕ) (hS : ∀ p ∈ S, Nat.Prime p) :
    Nat.totient (∏ p ∈ S, p) = ∏ p ∈ S, (p - 1) := by
  have hpos : 0 < ∏ p ∈ S, p := Finset.prod_pos fun p hp => (hS p hp).pos
  have h := Nat.totient_mul_prod_primeFactors (∏ p ∈ S, p)
  rw [Nat.primeFactors_prod hS] at h
  apply Nat.eq_of_mul_eq_mul_right hpos
  rw [h, mul_comm]

lemma dyadic_prime_coprime_sub_one {T p q : ℕ} (hT : 2 ≤ T)
    (hp : p.Prime) (hq : q.Prime) (hTp : T < p) (hqT : q ≤ 2 * T) :
    p.Coprime (q - 1) := by
  apply hp.coprime_iff_not_dvd.mpr
  intro hdiv
  have hp2 : p ≠ 2 := by omega
  have hcop : Nat.Coprime 2 p := Nat.prime_two.coprime_iff_not_dvd.mpr
    (by intro hd; have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp hd; omega)
  have hq2 : q ≠ 2 := by
    intro heq
    subst q
    norm_num at hdiv
    omega
  have heven : 2 ∣ q - 1 := even_iff_two_dvd.mp (hq.even_sub_one hq2)
  have hboth : 2 * p ∣ q - 1 := hcop.mul_dvd_of_dvd_of_dvd heven hdiv
  have hle := Nat.le_of_dvd (by have := hq.two_le; omega : 0 < q - 1) hboth
  omega

lemma dyadic_product_coprime_totient (T : ℕ) (S : Finset ℕ) (hT : 2 ≤ T)
    (hS : ∀ p ∈ S, p.Prime ∧ T < p ∧ p ≤ 2 * T) :
    (∏ p ∈ S, p).Coprime (Nat.totient (∏ p ∈ S, p)) := by
  rw [totient_prod_primes S fun p hp => (hS p hp).1]
  apply Nat.Coprime.prod_left
  intro p hp
  apply Nat.Coprime.prod_right
  intro q hq
  exact dyadic_prime_coprime_sub_one hT (hS p hp).1 (hS q hq).1
    (hS p hp).2.1 (hS q hq).2.2

lemma A_primeFactorsList_length_le (Y : ℕ) :
    (A Y).primeFactorsList.length ≤ 2 * Y := by
  apply (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp
  calc
    2 ^ (A Y).primeFactorsList.length ≤ (A Y).primeFactorsList.prod :=
      List.pow_card_le_prod _ _ fun p hp => (Nat.prime_of_mem_primeFactorsList hp).two_le
    _ = A Y := Nat.prod_primeFactorsList (A_pos Y).ne'
    _ ≤ 4 ^ Y := A_le_four_pow Y
    _ = 2 ^ (2 * Y) := by rw [pow_mul]; norm_num

lemma A_primeFactorsList_mem_le {Y p : ℕ} (hp : p ∈ (A Y).primeFactorsList) :
    p ≤ Y := by
  have hpp := Nat.prime_of_mem_primeFactorsList hp
  have hd := Nat.dvd_of_mem_primeFactorsList hp
  unfold A at hd
  obtain ⟨q, hq, hpq⟩ := (hpp.prime.dvd_finsetProd_iff fun q => q - 1).mp hd
  have hqY := (Finset.mem_Icc.mp (Finset.mem_filter.mp hq).1).2
  have hqprime := (Finset.mem_filter.mp hq).2
  exact (Nat.le_of_dvd (by have := hqprime.two_le; omega) hpq).trans (by omega)

lemma select_dyadic_primes (T : ℕ) (L : List ℕ)
    (hsupply : ∀ q ∈ L, L.length ≤ ((Finset.Ioc T (2 * T)).filter
      (fun p => p.Prime ∧ p % q = 1 % q)).card) :
    ∃ S : Finset ℕ, S.card = L.length ∧
      (∀ p ∈ S, p.Prime ∧ T < p ∧ p ≤ 2 * T) ∧
      L.prod ∣ ∏ p ∈ S, (p - 1) := by
  classical
  induction L with
  | nil => exact ⟨∅, by simp, by simp, by simp⟩
  | cons q L ih =>
    obtain ⟨S, hcard, hS, hdiv⟩ := ih (fun r hr =>
      (Nat.le_succ L.length).trans (hsupply r (List.mem_cons_of_mem q hr)))
    have hlt : S.card < ((Finset.Ioc T (2 * T)).filter
        (fun p => p.Prime ∧ p % q = 1 % q)).card := by
      have h := hsupply q List.mem_cons_self
      simpa only [hcard, List.length_cons] using Nat.lt_of_lt_of_le
        (Nat.lt_succ_self L.length) h
    obtain ⟨p, hp, hpS⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
    obtain ⟨hpI, hpp, hmod⟩ := Finset.mem_filter.mp hp
    obtain ⟨hTp, hpT⟩ := Finset.mem_Ioc.mp hpI
    have hqd : q ∣ p - 1 :=
      (Nat.modEq_iff_dvd' hpp.one_le).mp (show 1 ≡ p [MOD q] from hmod.symm)
    refine ⟨insert p S, by simp [hpS, hcard], ?_, ?_⟩
    · intro r hr
      rcases Finset.mem_insert.mp hr with rfl | hr
      · exact ⟨hpp, hTp, hpT⟩
      · exact hS r hr
    · rw [List.prod_cons, Finset.prod_insert hpS]
      exact Nat.mul_dvd_mul hqd hdiv

lemma exists_dyadic_totient_multiple (Y T : ℕ) (hT : 2 ≤ T)
    (hsupply : ∀ q : ℕ, q.Prime → q ≤ Y →
      2 * Y ≤ ((Finset.Ioc T (2 * T)).filter
        (fun p => p.Prime ∧ p % q = 1 % q)).card) :
    ∃ S : Finset ℕ, S.card ≤ 2 * Y ∧
      (∀ p ∈ S, p.Prime ∧ T < p ∧ p ≤ 2 * T) ∧
      A Y ∣ Nat.totient (∏ p ∈ S, p) ∧
      (∏ p ∈ S, p).Coprime (Nat.totient (∏ p ∈ S, p)) := by
  obtain ⟨S, hcard, hS, hdiv⟩ := select_dyadic_primes T (A Y).primeFactorsList
    (fun q hq => (A_primeFactorsList_length_le Y).trans
      (hsupply q (Nat.prime_of_mem_primeFactorsList hq) (A_primeFactorsList_mem_le hq)))
  refine ⟨S, hcard ▸ A_primeFactorsList_length_le Y, hS, ?_,
    dyadic_product_coprime_totient T S hT hS⟩
  rw [totient_prod_primes S fun p hp => (hS p hp).1]
  rwa [Nat.prod_primeFactorsList (A_pos Y).ne'] at hdiv

lemma dyadic_totient_ratio_lower (T : ℕ) (S : Finset ℕ) (hT : 1 ≤ T)
    (hS : ∀ p ∈ S, p.Prime ∧ T < p) :
    1 - (S.card : ℝ) / T ≤
      (Nat.totient (∏ p ∈ S, p) : ℝ) / (∏ p ∈ S, p : ℕ) := by
  have hTpos : (0 : ℝ) < T := by exact_mod_cast hT
  rw [totient_prod_primes S fun p hp => (hS p hp).1]
  push_cast
  rw [← Finset.prod_div_distrib]
  have hbase : (0 : ℝ) ≤ 1 - 1 / (T : ℝ) := by
    have hTone : (1 : ℝ) ≤ T := by exact_mod_cast hT
    exact sub_nonneg.mpr ((div_le_one hTpos).mpr hTone)
  calc
    1 - (S.card : ℝ) / T ≤ (1 - 1 / (T : ℝ)) ^ S.card := by
      have h := one_add_mul_le_pow (show (-2 : ℝ) ≤ -(1 / (T : ℝ)) by linarith) S.card
      simpa only [mul_neg, mul_one_div, ← sub_eq_add_neg] using h
    _ = ∏ _p ∈ S, (1 - 1 / (T : ℝ)) := by rw [Finset.prod_const]
    _ ≤ ∏ p ∈ S, ((p : ℝ) - 1) / p := by
      apply Finset.prod_le_prod (fun _ _ => hbase)
      intro p hp
      have hpR : (0 : ℝ) < p := by exact_mod_cast (hS p hp).1.pos
      have hTp : (T : ℝ) ≤ p := by exact_mod_cast (hS p hp).2.le
      have hle := one_div_le_one_div_of_le hTpos hTp
      rw [sub_div, div_self hpR.ne']
      linarith
    _ = ∏ p ∈ S, ((p - 1 : ℕ) : ℝ) / p := by
      apply Finset.prod_congr rfl
      intro p hp
      rw [Nat.cast_sub (hS p hp).1.one_le, Nat.cast_one]

end Erdos694.LowerConstruction
