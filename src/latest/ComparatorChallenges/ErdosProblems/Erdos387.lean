import Mathlib

open scoped BigOperators

namespace Erdos387

def UniversalNearDivisor (c : ℝ) : Prop :=
  0 < c ∧ ∀ n k : ℕ, 1 ≤ k → k < n →
    ∃ d : ℕ, (d : ℝ) ∈ Set.Ioc (c * n) n ∧ d ∣ n.choose k

/-- A counterexample at the real endpoint `c * n`. -/
def IsCounterexample (c : ℝ) (n k : ℕ) : Prop :=
  1 ≤ k ∧ k < n ∧
    ∀ d : ℕ, (d : ℝ) ∈ Set.Ioc (c * n) n → ¬d ∣ n.choose k

/-- A counterexample at the fixed-parameter endpoint `n / B`. -/
def IsFixedBCounterexample (B n k : ℕ) : Prop :=
  1 ≤ k ∧ k < n ∧
    ∀ d : ℕ, (d : ℝ) ∈ Set.Ioc ((n : ℝ) / B) n → ¬d ∣ n.choose k

noncomputable def BNPZEndpoint (k : ℕ) : ℝ :=
  241 * (Real.log (Real.log (k : ℝ)) / Real.log (k : ℝ))

structure CoverFactorization (n k : ℕ) where
  g : ℕ → ℕ
  divides_term : ∀ i < k, g i ∣ n - i
  product_eq_factorial : ∏ i ∈ Finset.range k, g i = k.factorial

structure CoverDivisorTuple (D : CoverFactorization n k) where
  factor : Fin k → ℕ
  divides : ∀ i, factor i ∣ (n - (i : ℕ)) / D.g i

namespace CoverDivisorTuple

def value {D : CoverFactorization n k} (E : CoverDivisorTuple D) : ℕ :=
  ∏ i, E.factor i

def HasLargeComponent {D : CoverFactorization n k}
    (E : CoverDivisorTuple D) (large : ℕ) : Prop :=
  ∃ i : Fin k, large < E.factor i

/-- Some component lies in the half-open medium range `(medium, large]`. -/
def HasMediumComponent {D : CoverFactorization n k}
    (E : CoverDivisorTuple D) (medium large : ℕ) : Prop :=
  ∃ i : Fin k, medium < E.factor i ∧ E.factor i ≤ large

/-- One component factors into two integers both exceeding `y`. -/
def HasConvenientComponent {D : CoverFactorization n k}
    (E : CoverDivisorTuple D) (y : ℕ) : Prop :=
  ∃ i : Fin k, ∃ r s : ℕ,
    E.factor i = r * s ∧ y < r ∧ y < s

/-- Every component is a `y³`-small factor times either one or a single prime
above `y`. -/
def IsAlmostPrimeTuple {D : CoverFactorization n k}
    (E : CoverDivisorTuple D) (y : ℕ) : Prop :=
  ∀ i : Fin k, ∃ f q : ℕ,
    E.factor i = f * q ∧ f ≤ y ^ 3 ∧
      (q = 1 ∨ q.Prime ∧ y < q)

end CoverDivisorTuple

namespace CoverBPZ

structure AbsorberCover (m k : ℕ) where
  N₀ : ℤ
  Mk : ℕ
  Mk_pos : 0 < Mk
  B : Fin k → ℕ
  B_ge_m : ∀ j, m ≤ B j
  prod_B_eq_factorial : ∏ j, B j = k.factorial

namespace AbsorberCover

variable {m k : ℕ}

def N (cov : AbsorberCover m k) (n : ℕ) : ℤ := cov.N₀ + (cov.Mk : ℤ) * n

def L (cov : AbsorberCover m k) (n : ℕ) (j : Fin k) : ℤ :=
  (cov.N n - (k : ℤ) + (j.val + 1 : ℤ)) / (cov.B j : ℤ)

end AbsorberCover

structure AbsorberCoverValid (m k : ℕ) extends AbsorberCover m k where
  L_div : ∀ n j, ((toAbsorberCover.B j : ℤ)) ∣
    (toAbsorberCover.N n - (k : ℤ) + (j.val + 1 : ℤ))
  N_pos : ∀ n, 0 < toAbsorberCover.N n
  binom_eq : ∀ n,
    (((toAbsorberCover.N n).toNat).choose k : ℤ) = ∏ j, toAbsorberCover.L n j
  pairwise_coprime : ∀ n, ∀ i j : Fin k, i ≠ j →
    Int.gcd (toAbsorberCover.L n i) (toAbsorberCover.L n j) = 1
  k_lt_N_toNat : ∀ n, k < (toAbsorberCover.N n).toNat
  Mk_smooth : ∀ p : ℕ, p.Prime → p ∣ toAbsorberCover.Mk → p ≤ k
  B_dvd_Mk : ∀ j, toAbsorberCover.B j ∣ toAbsorberCover.Mk

theorem B_pos {m k : ℕ} (cov : AbsorberCover m k) (j : Fin k) :
    0 < cov.B j := by
  have hprod : ∏ i, cov.B i = k.factorial := cov.prod_B_eq_factorial
  have hfact_pos : 0 < k.factorial := Nat.factorial_pos k
  have hprod_pos : 0 < ∏ i, cov.B i := by rw [hprod]; exact hfact_pos
  rcases Nat.eq_zero_or_pos (cov.B j) with hBj_zero | hBj_pos
  · exfalso
    have hzero : ∏ i, cov.B i = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ j) hBj_zero
    omega
  · exact hBj_pos

noncomputable def Nk_formula (k : ℕ) : ℕ :=
  ∏ p ∈ (Finset.range (k + 1)).filter Nat.Prime, p ^ (Nat.log p k + 1)

structure BPZSection6Input (B K : ℕ) where
  k : ℕ
  hkK : K ≤ k
  hk3 : 3 ≤ k
  α : ℤ
  g : Fin k → ℕ
  g_pos : ∀ i : Fin k, 0 < g i
  g_ge_B : ∀ i : Fin k, B ≤ g i
  g_prod_factorial : (∏ i : Fin k, g i) = k.factorial
  progression :
    ∀ n : ℤ, (k : ℤ) < n →
      (Nk_formula k : ℤ) ∣ n - α →
        (∀ i : Fin k, (g i : ℤ) ∣ n - (i.val : ℤ)) ∧
        (∀ p : ℕ, p.Prime → p ≤ k →
          ¬ (p : ℤ) ∣ ((n.toNat).choose k : ℤ)) ∧
        (∀ i : Fin k, ∀ p : ℕ, p.Prime → p ≤ k →
          ¬ p ∣ (n.toNat - i.val) / g i)

namespace AbsorberCoverValid

noncomputable def affineRescale {m k : ℕ} (C : AbsorberCoverValid m k)
    (t₀ Q : ℕ) (hQpos : 0 < Q)
    (hQsmooth : ∀ p : ℕ, p.Prime → p ∣ Q → p ≤ k) :
    AbsorberCoverValid m k := by
  let C' : AbsorberCover m k :=
    { N₀ := C.toAbsorberCover.N t₀
      Mk := C.toAbsorberCover.Mk * Q
      Mk_pos := Nat.mul_pos C.toAbsorberCover.Mk_pos hQpos
      B := C.toAbsorberCover.B
      B_ge_m := C.toAbsorberCover.B_ge_m
      prod_B_eq_factorial := C.toAbsorberCover.prod_B_eq_factorial }
  have hN (u : ℕ) :
      C'.N u = C.toAbsorberCover.N (t₀ + Q * u) := by
    simp [C', AbsorberCover.N]
    ring
  refine
    { toAbsorberCover := C'
      L_div := ?_
      N_pos := ?_
      binom_eq := ?_
      pairwise_coprime := ?_
      k_lt_N_toNat := ?_
      Mk_smooth := ?_
      B_dvd_Mk := ?_ }
  · intro u j
    rw [hN]
    exact C.L_div (t₀ + Q * u) j
  · intro u
    rw [hN]
    exact C.N_pos (t₀ + Q * u)
  · intro u
    simpa [AbsorberCover.L, hN] using C.binom_eq (t₀ + Q * u)
  · intro u i j hij
    simpa [AbsorberCover.L, hN] using
      C.pairwise_coprime (t₀ + Q * u) i j hij
  · intro u
    rw [hN]
    exact C.k_lt_N_toNat (t₀ + Q * u)
  · intro p hp hpd
    rcases hp.dvd_mul.mp hpd with hpM | hpQ
    · exact C.Mk_smooth p hp hpM
    · exact hQsmooth p hp hpQ
  · intro j
    exact (C.B_dvd_Mk j).trans (Nat.dvd_mul_right _ Q)

def nNat {m k : ℕ} (C : AbsorberCoverValid m k) (t : ℕ) : ℕ :=
  (C.toAbsorberCover.N t).toNat

/-- The positive natural residual factor indexed by `j`. -/
def residual {m k : ℕ} (C : AbsorberCoverValid m k)
    (t : ℕ) (j : Fin k) : ℕ :=
  (C.toAbsorberCover.L t j).toNat

theorem nNat_cast {m k : ℕ} (C : AbsorberCoverValid m k) (t : ℕ) :
    (C.nNat t : ℤ) = C.toAbsorberCover.N t := by
  unfold nNat
  exact Int.toNat_of_nonneg (C.N_pos t).le

theorem k_lt_nNat {m k : ℕ} (C : AbsorberCoverValid m k) (t : ℕ) :
    k < C.nNat t := C.k_lt_N_toNat t

theorem residual_int_pos {m k : ℕ} (C : AbsorberCoverValid m k)
    (t : ℕ) (j : Fin k) :
    0 < C.toAbsorberCover.L t j := by
  have hBnat : 0 < C.toAbsorberCover.B j :=
    Erdos387.CoverBPZ.B_pos C.toAbsorberCover j
  have hB : (0 : ℤ) < C.toAbsorberCover.B j := by
    exact_mod_cast hBnat
  have hNcast := C.nNat_cast t
  have hkn := C.k_lt_nNat t
  have hnum : (0 : ℤ) <
      C.toAbsorberCover.N t - (k : ℤ) + (j.val + 1 : ℤ) := by
    rw [← hNcast]
    have hknz : (k : ℤ) < (C.nNat t : ℤ) := by exact_mod_cast hkn
    have hjz : (0 : ℤ) < (j.val + 1 : ℕ) := by exact_mod_cast Nat.succ_pos j.val
    omega
  have hmul := Int.ediv_mul_cancel (C.L_div t j)
  change C.toAbsorberCover.L t j *
      (C.toAbsorberCover.B j : ℤ) =
        C.toAbsorberCover.N t - (k : ℤ) + (j.val + 1 : ℤ) at hmul
  nlinarith

theorem residual_cast {m k : ℕ} (C : AbsorberCoverValid m k)
    (t : ℕ) (j : Fin k) :
    (C.residual t j : ℤ) = C.toAbsorberCover.L t j := by
  unfold residual
  exact Int.toNat_of_nonneg (C.residual_int_pos t j).le

def freezeExponent {m k : ℕ} (C : AbsorberCoverValid m k) (t₀ : ℕ) : ℕ :=
  ∏ j : Fin k, C.residual t₀ j

/-- Smooth modulus used to freeze all primes at most `k`. -/
def freezeModulus {m k : ℕ} (C : AbsorberCoverValid m k) (t₀ : ℕ) : ℕ :=
  k.factorial ^ C.freezeExponent t₀

theorem freezeModulus_pos {m k : ℕ} (C : AbsorberCoverValid m k)
    (t₀ : ℕ) : 0 < C.freezeModulus t₀ := by
  unfold freezeModulus
  positivity

theorem freezeModulus_smooth {m k : ℕ} (C : AbsorberCoverValid m k)
    (t₀ : ℕ) (p : ℕ) (hp : p.Prime) (hpd : p ∣ C.freezeModulus t₀) :
    p ≤ k := by
  apply hp.dvd_factorial.mp
  exact hp.dvd_of_dvd_pow (by simpa [freezeModulus] using hpd)

noncomputable def frozen {m k : ℕ} (C : AbsorberCoverValid m k)
    (t₀ : ℕ) : AbsorberCoverValid m k :=
  C.affineRescale t₀ (C.freezeModulus t₀) (C.freezeModulus_pos t₀)
    (C.freezeModulus_smooth t₀)

noncomputable def smallPrimePart (k n : ℕ) : ℕ :=
  ∏ p ∈ n.primeFactors.filter (fun p => p ≤ k), p ^ n.factorization p

/-- Complementary product supported on primes greater than `k`. -/
noncomputable def largePrimePart (k n : ℕ) : ℕ :=
  ∏ p ∈ n.primeFactors.filter (fun p => ¬p ≤ k), p ^ n.factorization p

theorem residual_mul_B {m k : ℕ} (C : AbsorberCoverValid m k)
    (t : ℕ) (j : Fin k) :
    C.residual t j * C.toAbsorberCover.B j =
      C.nNat t - k + (j.val + 1) := by
  have hkn : k ≤ C.nNat t := (C.k_lt_nNat t).le
  have hmulInt := Int.ediv_mul_cancel (C.L_div t j)
  change C.toAbsorberCover.L t j *
      (C.toAbsorberCover.B j : ℤ) =
        C.toAbsorberCover.N t - (k : ℤ) + (j.val + 1 : ℤ) at hmulInt
  have hmulCast :
      ((C.residual t j * C.toAbsorberCover.B j : ℕ) : ℤ) =
        ((C.nNat t - k + (j.val + 1) : ℕ) : ℤ) := by
    rw [Nat.cast_mul, C.residual_cast, Nat.cast_add,
      Nat.cast_sub hkn, C.nNat_cast]
    push_cast
    exact hmulInt
  exact Int.ofNat_inj.mp hmulCast

noncomputable def toCoverFactorization {m k : ℕ}
    (C : AbsorberCoverValid m k) (t : ℕ) :
    Erdos387.CoverFactorization (C.nNat t) k := by
  let g : ℕ → ℕ := fun i =>
    if hi : i < k then C.toAbsorberCover.B (Fin.rev ⟨i, hi⟩) else 1
  refine
    { g := g
      divides_term := ?_
      product_eq_factorial := ?_ }
  · intro i hi
    have hmul := C.residual_mul_B t (Fin.rev ⟨i, hi⟩)
    have hterm :
        C.nNat t - k + ((Fin.rev ⟨i, hi⟩).val + 1) =
          C.nNat t - i := by
      have hkn := C.k_lt_nNat t
      simp only [Fin.val_rev]
      omega
    rw [hterm] at hmul
    refine ⟨C.residual t (Fin.rev ⟨i, hi⟩), ?_⟩
    simpa [g, hi, mul_comm] using hmul.symm
  · calc
      ∏ i ∈ Finset.range k, g i = ∏ i : Fin k, g i := by
        exact (Fin.prod_univ_eq_prod_range g k).symm
      _ = ∏ i : Fin k, C.toAbsorberCover.B (Fin.rev i) := by
        apply Finset.prod_congr rfl
        intro i hi
        simp [g]
      _ = ∏ i : Fin k, C.toAbsorberCover.B i := by
        exact Fintype.prod_equiv (Fin.revPerm : Equiv.Perm (Fin k))
          (fun i : Fin k => C.toAbsorberCover.B (Fin.rev i))
          C.toAbsorberCover.B (fun _ => rfl)
      _ = k.factorial := C.toAbsorberCover.prod_B_eq_factorial

end AbsorberCoverValid

namespace BPZSection6Input

def gNat {B K : ℕ} (S : CoverBPZ.BPZSection6Input B K) (i : ℕ) : ℕ :=
  if hi : i < S.k then S.g ⟨i, hi⟩ else 1

theorem gNat_eq {B K : ℕ} (S : CoverBPZ.BPZSection6Input B K)
    {i : ℕ} (hi : i < S.k) : S.gNat i = S.g ⟨i, hi⟩ := by
  simp [gNat, hi]

/-- Every natural member of the certified progression yields exactly the
factorization data used by `choose_eq_prod_coverQuotients`. -/
noncomputable def toCoverFactorization {B K n : ℕ}
    (S : CoverBPZ.BPZSection6Input B K) (hn : S.k < n)
    (hprog : (CoverBPZ.Nk_formula S.k : ℤ) ∣ (n : ℤ) - S.α) :
    CoverFactorization n S.k where
  g := S.gNat
  divides_term := by
    intro i hi
    have hdata := S.progression (n : ℤ) (by exact_mod_cast hn) hprog
    have hdivZ := hdata.1 ⟨i, hi⟩
    have hin : i ≤ n := (Nat.le_of_lt hi).trans hn.le
    have hcastSub : ((n - i : ℕ) : ℤ) = (n : ℤ) - (i : ℤ) := by
      exact Nat.cast_sub hin
    have hdivZ' : (S.g ⟨i, hi⟩ : ℤ) ∣ ((n - i : ℕ) : ℤ) := by
      rwa [hcastSub]
    rw [S.gNat_eq hi]
    exact_mod_cast hdivZ'
  product_eq_factorial := by
    rw [← Fin.prod_univ_eq_prod_range S.gNat S.k]
    simpa [gNat] using S.g_prod_factorial

end BPZSection6Input
end CoverBPZ

def sievePrimes (k z : ℕ) : Finset ℕ :=
  (Finset.range z).filter fun p => p.Prime ∧ k < p

theorem mem_sievePrimes {k z p : ℕ} :
    p ∈ sievePrimes k z ↔ p.Prime ∧ k < p ∧ p < z := by
  simp only [sievePrimes, Finset.mem_filter, Finset.mem_range]
  aesop

/-- Squarefree product of the sieving primes. -/
def sievePrimeProduct (k z : ℕ) : ℕ :=
  ∏ p ∈ sievePrimes k z, p

theorem prime_mem_sievePrimes_of_dvd_product {k z p : ℕ}
    (hp : p.Prime) (hdiv : p ∣ sievePrimeProduct k z) :
    p ∈ sievePrimes k z := by
  unfold sievePrimeProduct at hdiv
  obtain ⟨q, hq, hpq⟩ := (hp.prime.dvd_finsetProd_iff id).mp hdiv
  have hqPrime := (mem_sievePrimes.mp hq).1
  have hpEq : p = q := ((hqPrime.dvd_iff_eq hp.ne_one).mp hpq).symm
  simpa [hpEq] using hq

/-- Every prime divisor of the public progression modulus is at most `k`. -/
theorem prime_le_of_dvd_Nk_formula {k p : ℕ} (hp : p.Prime)
    (hdiv : p ∣ CoverBPZ.Nk_formula k) : p ≤ k := by
  unfold CoverBPZ.Nk_formula at hdiv
  obtain ⟨q, hq, hpqPow⟩ :=
    (hp.prime.dvd_finsetProd_iff
      (fun q => q ^ (Nat.log q k + 1))).mp hdiv
  have hqData := Finset.mem_filter.mp hq
  have hpq : p ∣ q := hp.dvd_of_dvd_pow hpqPow
  have hpEq : p = q :=
    (((hqData.2.dvd_iff_eq hp.ne_one).mp hpq).symm)
  rw [hpEq]
  exact Nat.lt_succ_iff.mp (Finset.mem_range.mp hqData.1)

/-- The progression modulus is coprime to every divisor of the product of
sieving primes, since the former has prime factors at most `k` and the latter
has prime factors greater than `k`. -/
theorem coprime_Nk_formula_of_dvd_sievePrimeProduct
    {k z d : ℕ} (hd : d ∣ sievePrimeProduct k z) :
    Nat.Coprime (CoverBPZ.Nk_formula k) d := by
  by_contra hcop
  obtain ⟨p, hp, hpM, hpd⟩ := Nat.Prime.not_coprime_iff_dvd.mp hcop
  have hple : p ≤ k := prime_le_of_dvd_Nk_formula hp hpM
  have hpProd : p ∣ sievePrimeProduct k z := hpd.trans hd
  have hmem := prime_mem_sievePrimes_of_dvd_product hp hpProd
  exact (Nat.not_lt_of_ge hple) (mem_sievePrimes.mp hmem).2.1

noncomputable def progressionResidue {B K : ℕ}
    (S : CoverBPZ.BPZSection6Input B K) : ℕ :=
  (S.α % (CoverBPZ.Nk_formula S.k : ℤ)).toNat

noncomputable def progressionLocalResidue {B K z d : ℕ}
    (S : CoverBPZ.BPZSection6Input B K)
    (hd : d ∣ sievePrimeProduct S.k z) (a : ℕ) : ℕ :=
  Nat.chineseRemainder (coprime_Nk_formula_of_dvd_sievePrimeProduct hd)
    (progressionResidue S) a

namespace CoverBPZ

def refinementPrimeProduct (k : ℕ) : ℕ :=
  sievePrimeProduct k (2 * k)

noncomputable def refinementResidue {B K : ℕ}
    (S : BPZSection6Input B K) : ℕ :=
  progressionLocalResidue S (dvd_refl (refinementPrimeProduct S.k)) S.k

noncomputable def refinementModulus {B K : ℕ} (S : BPZSection6Input B K) : ℕ :=
  Nk_formula S.k * refinementPrimeProduct S.k

end CoverBPZ

def IsZRough (z m : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → p < z → ¬p ∣ m

noncomputable def RefinedBaseCandidates {B K : ℕ}
    (S : CoverBPZ.BPZSection6Input B K) (X : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Ioc (X / 2) X).filter fun n =>
    S.k < n ∧ (CoverBPZ.refinementModulus S : ℤ) ∣
      (n : ℤ) - CoverBPZ.refinementResidue S

noncomputable def RefinedSiftedCandidates {B K : ℕ}
    (S : CoverBPZ.BPZSection6Input B K) (X z : ℕ) : Finset ℕ := by
  classical
  exact (RefinedBaseCandidates S X).filter fun n =>
    IsZRough z (n.choose S.k)

def AbsorberParameterCandidates (T : ℕ) : Finset ℕ :=
  Finset.Ioc (T / 2) T

noncomputable def SiftedAbsorberParameterCandidates {m k : ℕ}
    (C : CoverBPZ.AbsorberCoverValid m k) (T z : ℕ) : Finset ℕ := by
  classical
  exact (AbsorberParameterCandidates T).filter fun t =>
    Nat.Coprime (sievePrimeProduct k z) ((C.nNat t).choose k)

noncomputable def frozenFixedPartChoices {m k : ℕ}
    (C : CoverBPZ.AbsorberCoverValid m k) (t₀ : ℕ) :
    Finset (Fin k → ℕ) :=
  Fintype.piFinset fun i : Fin k =>
    (CoverBPZ.AbsorberCoverValid.smallPrimePart k
      (C.residual t₀ (Fin.rev i))).divisors

def IsAbsorberLargeError {m k : ℕ}
    (C : CoverBPZ.AbsorberCoverValid m k) (t large : ℕ) : Prop :=
  ∃ d : ℕ, ∃ E : CoverDivisorTuple (C.toCoverFactorization t),
    C.nNat t < m * d ∧ d ≤ C.nNat t ∧ E.value = d ∧
      E.HasLargeComponent large

/-- Absorber bad tuple with a component in `(medium,large]`. -/
def IsAbsorberMediumError {m k : ℕ}
    (C : CoverBPZ.AbsorberCoverValid m k)
    (t medium large : ℕ) : Prop :=
  ∃ d : ℕ, ∃ E : CoverDivisorTuple (C.toCoverFactorization t),
    C.nNat t < m * d ∧ d ≤ C.nNat t ∧ E.value = d ∧
      E.HasMediumComponent medium large

/-- Absorber bad tuple with a convenient component factorization. -/
def IsAbsorberConvenientError {m k : ℕ}
    (C : CoverBPZ.AbsorberCoverValid m k) (t y medium : ℕ) : Prop :=
  ∃ d : ℕ, ∃ E : CoverDivisorTuple (C.toCoverFactorization t),
    C.nNat t < m * d ∧ d ≤ C.nNat t ∧ E.value = d ∧
      E.HasConvenientComponent y ∧
      ∀ i : Fin k, E.factor i ≤ medium

/-- Remaining absorber error class: every component is medium and is a
small factor times at most one prime above `y`. -/
def IsAbsorberAlmostPrimeError {m k : ℕ}
    (C : CoverBPZ.AbsorberCoverValid m k) (t y medium : ℕ) : Prop :=
  ∃ d : ℕ, ∃ E : CoverDivisorTuple (C.toCoverFactorization t),
    C.nNat t < m * d ∧ d ≤ C.nNat t ∧ E.value = d ∧
      (∀ i : Fin k, E.factor i ≤ medium) ∧ E.IsAlmostPrimeTuple y

noncomputable def AbsorberLargeErrors {m k : ℕ}
    (C : CoverBPZ.AbsorberCoverValid m k)
    (T z large : ℕ) : Finset ℕ := by
  classical
  exact (SiftedAbsorberParameterCandidates C T z).filter fun t =>
    IsAbsorberLargeError C t large

noncomputable def AbsorberMediumErrors {m k : ℕ}
    (C : CoverBPZ.AbsorberCoverValid m k)
    (T z medium large : ℕ) : Finset ℕ := by
  classical
  exact (SiftedAbsorberParameterCandidates C T z).filter fun t =>
    IsAbsorberMediumError C t medium large

noncomputable def AbsorberConvenientErrors {m k : ℕ}
    (C : CoverBPZ.AbsorberCoverValid m k)
    (T z y medium : ℕ) : Finset ℕ := by
  classical
  exact (SiftedAbsorberParameterCandidates C T z).filter fun t =>
    IsAbsorberConvenientError C t y medium

noncomputable def AbsorberAlmostPrimeErrors {m k : ℕ}
    (C : CoverBPZ.AbsorberCoverValid m k)
    (T z y medium : ℕ) : Finset ℕ := by
  classical
  exact (SiftedAbsorberParameterCandidates C T z).filter fun t =>
    IsAbsorberAlmostPrimeError C t y medium

def IsFrozenRoughProductError {m k : ℕ}
    (C : CoverBPZ.AbsorberCoverValid m k) (t₀ t z : ℕ) : Prop :=
  ∃ a b : Fin k → ℕ,
    a ∈ frozenFixedPartChoices C t₀ ∧
    (∀ i : Fin k,
      b i ∣ CoverBPZ.AbsorberCoverValid.largePrimePart k
        ((C.frozen t₀).residual t (Fin.rev i))) ∧
    (∀ i : Fin k, IsZRough z (b i)) ∧
    (C.frozen t₀).nNat t <
      m * ((∏ i, a i) * ∏ i, b i) ∧
    (∏ i, a i) * ∏ i, b i ≤ (C.frozen t₀).nNat t

/-- The literal subset of sifted parameters carrying a rough-product error. -/
noncomputable def FrozenRoughProductErrors {m k : ℕ}
    (C : CoverBPZ.AbsorberCoverValid m k) (t₀ T z : ℕ) : Finset ℕ := by
  classical
  exact (SiftedAbsorberParameterCandidates (C.frozen t₀) T z).filter fun t =>
    IsFrozenRoughProductError C t₀ t z

namespace CoverBPZ

def IsLargeError {B K : ℕ} (S : BPZSection6Input B K)
    (n large : ℕ) : Prop :=
  ∃ hn : S.k < n,
    ∃ hprog : (Nk_formula S.k : ℤ) ∣ (n : ℤ) - S.α,
      ∃ d : ℕ, ∃ E : CoverDivisorTuple (S.toCoverFactorization hn hprog),
        n < B * d ∧ d ≤ n ∧ E.value = d ∧ E.HasLargeComponent large

/-- A bad tuple with a component in `(medium, large]`. -/
def IsMediumError {B K : ℕ} (S : BPZSection6Input B K)
    (n medium large : ℕ) : Prop :=
  ∃ hn : S.k < n,
    ∃ hprog : (Nk_formula S.k : ℤ) ∣ (n : ℤ) - S.α,
      ∃ d : ℕ, ∃ E : CoverDivisorTuple (S.toCoverFactorization hn hprog),
        n < B * d ∧ d ≤ n ∧ E.value = d ∧
          E.HasMediumComponent medium large

/-- A bad tuple having a convenient component factorization above `y`. -/
def IsConvenientError {B K : ℕ} (S : BPZSection6Input B K)
    (n y medium : ℕ) : Prop :=
  ∃ hn : S.k < n,
    ∃ hprog : (Nk_formula S.k : ℤ) ∣ (n : ℤ) - S.α,
      ∃ d : ℕ, ∃ E : CoverDivisorTuple (S.toCoverFactorization hn hprog),
        n < B * d ∧ d ≤ n ∧ E.value = d ∧ E.HasConvenientComponent y
          ∧ ∀ i : Fin S.k, E.factor i ≤ medium

/-- The remaining error class: all components are at most `medium`, and
each is a `y³`-small factor times at most one large prime. -/
def IsAlmostPrimeError {B K : ℕ} (S : BPZSection6Input B K)
    (n y medium : ℕ) : Prop :=
  ∃ hn : S.k < n,
    ∃ hprog : (Nk_formula S.k : ℤ) ∣ (n : ℤ) - S.α,
      ∃ d : ℕ, ∃ E : CoverDivisorTuple (S.toCoverFactorization hn hprog),
        n < B * d ∧ d ≤ n ∧ E.value = d ∧
          (∀ i : Fin S.k, E.factor i ≤ medium) ∧ E.IsAlmostPrimeTuple y

noncomputable def RefinedLargeErrors {B K : ℕ}
    (S : BPZSection6Input B K) (X z large : ℕ) : Finset ℕ := by
  classical
  exact (RefinedSiftedCandidates S X z).filter fun n =>
    IsLargeError S n large

noncomputable def RefinedMediumErrors {B K : ℕ}
    (S : BPZSection6Input B K) (X z medium large : ℕ) : Finset ℕ := by
  classical
  exact (RefinedSiftedCandidates S X z).filter fun n =>
    IsMediumError S n medium large

noncomputable def RefinedConvenientErrors {B K : ℕ}
    (S : BPZSection6Input B K) (X z y medium : ℕ) : Finset ℕ := by
  classical
  exact (RefinedSiftedCandidates S X z).filter fun n =>
    IsConvenientError S n y medium

noncomputable def RefinedAlmostPrimeErrors {B K : ℕ}
    (S : BPZSection6Input B K) (X z y medium : ℕ) : Finset ℕ := by
  classical
  exact (RefinedSiftedCandidates S X z).filter fun n =>
    IsAlmostPrimeError S n y medium

def HasComparablePrimeError {B K : ℕ} (S : BPZSection6Input B K)
    (n secondMin gap medium : ℕ) : Prop :=
  ∃ r q : ℕ,
    r.Prime ∧ q.Prime ∧ secondMin < r ∧ r < q ∧ q ≤ medium ∧
      q < gap * r ∧ r ∣ n.choose S.k ∧ q ∣ n.choose S.k

/-- The certificate estimated in Proposition 6.6: after extracting uniformly
small factors, one prime is separated from every other prime factor by the
prescribed multiplicative gap, and a second prime exceeds `secondMin`. -/
def HasSeparatedAlmostPrimeError {B K : ℕ} (S : BPZSection6Input B K)
    (n y medium secondMin gap : ℕ) : Prop :=
  ∃ hn : S.k < n,
    ∃ hprog : (Nk_formula S.k : ℤ) ∣ (n : ℤ) - S.α,
      ∃ d : ℕ, ∃ E : CoverDivisorTuple (S.toCoverFactorization hn hprog),
        ∃ f q : Fin S.k → ℕ, ∃ i₀ j₀ : Fin S.k,
          n < B * d ∧ d ≤ n ∧ E.value = d ∧
          (∀ i, E.factor i = f i * q i) ∧
          (∀ i, f i ≤ y ^ 3) ∧
          (∀ i, q i = 1 ∨ (q i).Prime ∧ y < q i) ∧
          (∀ i, E.factor i ≤ medium) ∧
          (∀ i, q i ≤ q i₀) ∧
          i₀ ≠ j₀ ∧ secondMin < q j₀ ∧
          ∀ j, j ≠ i₀ → gap * q j ≤ q i₀

noncomputable def RefinedComparablePrimeErrors {B K : ℕ}
    (S : BPZSection6Input B K) (X z secondMin gap medium : ℕ) :
    Finset ℕ := by
  classical
  exact (RefinedSiftedCandidates S X z).filter fun n =>
    HasComparablePrimeError S n secondMin gap medium

noncomputable def RefinedSeparatedAlmostPrimeErrors {B K : ℕ}
    (S : BPZSection6Input B K)
    (X z y medium secondMin gap : ℕ) : Finset ℕ := by
  classical
  exact (RefinedSiftedCandidates S X z).filter fun n =>
    HasSeparatedAlmostPrimeError S n y medium secondMin gap

end CoverBPZ

theorem erdos_387_of_counterexamples
    (h : ∀ c : ℝ, 0 < c → ∃ n k : ℕ, IsCounterexample c n k) :
    False ↔ ∃ c : ℝ, UniversalNearDivisor c := by
  sorry

theorem erdos_387_of_fixedB
    (h : ∀ B : ℕ, 2 ≤ B → ∃ n k : ℕ, IsFixedBCounterexample B n k) :
    False ↔ ∃ c : ℝ, 0 < c ∧ ∀ n k : ℕ, 1 ≤ k → k < n →
      ∃ d : ℕ, (d : ℝ) ∈ Set.Ioc (c * n) n ∧ d ∣ n.choose k := by
  sorry

theorem erdos_387_of_eventually_fixedB
    (h : ∃ B₀ : ℕ, ∀ B : ℕ, B₀ ≤ B →
      ∃ n k : ℕ, IsFixedBCounterexample B n k) :
    False ↔ ∃ c : ℝ, 0 < c ∧ ∀ n k : ℕ, 1 ≤ k → k < n →
      ∃ d : ℕ, (d : ℝ) ∈ Set.Ioc (c * n) n ∧ d ∣ n.choose k := by
  sorry

theorem erdos_387_of_eventually_BNPZ
    (h : ∀ᶠ k : ℕ in Filter.atTop,
      ∃ n : ℕ, 1 ≤ k ∧ k < n ∧
        ∀ d : ℕ,
          (d : ℝ) ∈ Set.Ioc (BNPZEndpoint k * n) n → ¬d ∣ n.choose k) :
    False ↔ ∃ c : ℝ, 0 < c ∧ ∀ n k : ℕ, 1 ≤ k → k < n →
      ∃ d : ℕ, (d : ℝ) ∈ Set.Ioc (c * n) n ∧ d ∣ n.choose k := by
  sorry

theorem erdos_387_of_cover_certificates
    (h : ∀ B : ℕ, 2 ≤ B →
      ∃ n k : ℕ, ∃ D : CoverFactorization n k,
        1 ≤ k ∧ k < n ∧
        ∀ e : ℕ → ℕ,
          (∀ i < k, e i ∣ (n - i) / D.g i) →
          ¬((∏ i ∈ Finset.range k, e i : ℕ) : ℝ) ∈ Set.Ioc ((n : ℝ) / B) n) :
    False ↔ ∃ c : ℝ, 0 < c ∧ ∀ n k : ℕ, 1 ≤ k → k < n →
      ∃ d : ℕ, (d : ℝ) ∈ Set.Ioc (c * n) n ∧ d ∣ n.choose k := by
  sorry

theorem erdos_387_of_absorber_error_bounds
    (h : ∀ m : ℕ, 3 ≤ m →
      ∃ k : ℕ, ∃ C : CoverBPZ.AbsorberCoverValid m k,
        ∃ T z y medium large : ℕ,
          3 ≤ k ∧ 2 ≤ y ∧
          (AbsorberLargeErrors C T z large).card +
              (AbsorberMediumErrors C T z medium large).card +
              (AbsorberConvenientErrors C T z y medium).card +
              (AbsorberAlmostPrimeErrors C T z y medium).card <
            (SiftedAbsorberParameterCandidates C T z).card) :
    False ↔ ∃ c : ℝ, 0 < c ∧ ∀ n k : ℕ, 1 ≤ k → k < n →
      ∃ d : ℕ, (d : ℝ) ∈ Set.Ioc (c * n) n ∧ d ∣ n.choose k := by
  sorry

theorem erdos_387_of_frozen_roughProduct_bounds
    (h : ∀ m : ℕ, 3 ≤ m →
      ∃ k : ℕ, ∃ C : CoverBPZ.AbsorberCoverValid m k,
        ∃ t₀ T z : ℕ,
          3 ≤ k ∧
          (FrozenRoughProductErrors C t₀ T z).card <
            (SiftedAbsorberParameterCandidates (C.frozen t₀) T z).card) :
    False ↔ ∃ c : ℝ, 0 < c ∧ ∀ n k : ℕ, 1 ≤ k → k < n →
      ∃ d : ℕ, (d : ℝ) ∈ Set.Ioc (c * n) n ∧ d ∣ n.choose k := by
  sorry

theorem erdos_387_of_refined_error_bounds
    (h : ∀ B K : ℕ, 3 ≤ B →
      ∀ S : CoverBPZ.BPZSection6Input B K,
        ∃ X z y medium large : ℕ,
          2 ≤ y ∧
          (CoverBPZ.RefinedLargeErrors S X z large).card +
              (CoverBPZ.RefinedMediumErrors S X z medium large).card +
              (CoverBPZ.RefinedConvenientErrors S X z y medium).card +
              (CoverBPZ.RefinedAlmostPrimeErrors S X z y medium).card <
            (RefinedSiftedCandidates S X z).card) :
    False ↔ ∃ c : ℝ, 0 < c ∧ ∀ n k : ℕ, 1 ≤ k → k < n →
      ∃ d : ℕ, (d : ℝ) ∈ Set.Ioc (c * n) n ∧ d ∣ n.choose k := by
  sorry

theorem erdos_387_of_refined_five_error_bounds
    (h : ∀ B K : ℕ, 3 ≤ B →
      ∀ S : CoverBPZ.BPZSection6Input B K,
        ∃ X z y medium large secondMin gap : ℕ,
          2 ≤ y ∧ 1 ≤ secondMin ∧
          B * y ^ (3 * S.k) * medium * secondMin ^ (S.k - 1) ≤ X / 2 ∧
          B * y ^ (3 * S.k) * (gap * secondMin) ^ S.k ≤ X / 2 ∧
          (CoverBPZ.RefinedLargeErrors S X z large).card +
              (CoverBPZ.RefinedMediumErrors S X z medium large).card +
              (CoverBPZ.RefinedConvenientErrors S X z y medium).card +
              (CoverBPZ.RefinedComparablePrimeErrors S X z secondMin gap
                medium).card +
              (CoverBPZ.RefinedSeparatedAlmostPrimeErrors S X z y medium
                secondMin gap).card <
            (RefinedSiftedCandidates S X z).card) :
    False ↔ ∃ c : ℝ, 0 < c ∧ ∀ n k : ℕ, 1 ≤ k → k < n →
      ∃ d : ℕ, (d : ℝ) ∈ Set.Ioc (c * n) n ∧ d ∣ n.choose k := by
  sorry

end Erdos387
