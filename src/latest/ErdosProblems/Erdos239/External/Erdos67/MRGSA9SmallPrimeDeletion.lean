import ErdosProblems.Erdos239.External.Erdos67.MRGSA9A13SourceShift
import ErdosProblems.Erdos239.External.Erdos67.MRGSTwoBlockDeletion

/-!
# Removing the finitely many small Euler factors in A.9

The horizontal product comparison is applied only at primes at least `23`.
This file records that deleting all smaller primes does not alter any of
those local factors, and packages the corresponding nonpretentiousness loss.
-/

open scoped BigOperators

namespace Erdos67.MRHalaszBands

noncomputable section

/-- The fixed finite collection removed before the source A.13 shift. -/
def gsA9SmallPrime (p : ℕ) : Prop := p.Prime ∧ p < 23

instance : DecidablePred gsA9SmallPrime := fun _ ↦ Classical.propDecidable _

/-- The finite set of primes removed from the shifted comparison. -/
def gsA9SmallPrimeFinset : Finset ℕ :=
  (Finset.range 23).filter Nat.Prime

/-- A fixed absolute majorant for their Euler factors on `Re s ≥ 1/2`. -/
def gsA9SmallPrimeEulerBound : ℝ :=
  ∏ p ∈ gsA9SmallPrimeFinset,
    (1 - (p : ℝ) ^ (-(1 / 2 : ℝ)))⁻¹

/-- The complementary prime set on which the shifted Euler comparison is
performed. -/
def gsA9LargePrimesUpTo (y : ℕ) : Finset ℕ :=
  (primesUpTo y).filter (fun p ↦ 23 ≤ p)

theorem not_hasPrimeFactor_gsA9SmallPrime_prime_pow
    {p e : ℕ} (hp : p.Prime) (hpLarge : 23 ≤ p) :
    ¬ HasPrimeFactor gsA9SmallPrime (p ^ e) := by
  rw [hasPrimeFactor_iff]
  rintro ⟨q, hq, hqSmall⟩
  by_cases he : e = 0
  · subst e
    simp at hq
  · rw [Nat.primeFactors_prime_pow he hp] at hq
    have hqp : q = p := by simpa using hq
    subst q
    exact (not_lt_of_ge hpLarge) hqSmall.2

/-- Deleting the fixed small primes leaves every power of a prime at least
`23` unchanged. -/
theorem gsDeleteSmallPrimes_prime_pow
    (f : ℕ → ℂ) {p e : ℕ} (hp : p.Prime) (hpLarge : 23 ≤ p) :
    gsDeletePrimeBand f gsA9SmallPrime (p ^ e) = f (p ^ e) := by
  rw [gsDeletePrimeBand_apply f gsA9SmallPrime (pow_pos hp.pos e),
    if_neg (not_hasPrimeFactor_gsA9SmallPrime_prime_pow hp hpLarge)]

theorem gsDeleteSmallPrimes_prime_pow_eq_zero
    (f : ℕ → ℂ) {p e : ℕ} (hp : p.Prime) (hpSmall : p < 23)
    (he : e ≠ 0) :
    gsDeletePrimeBand f gsA9SmallPrime (p ^ e) = 0 := by
  have hhas : HasPrimeFactor gsA9SmallPrime (p ^ e) := by
    rw [hasPrimeFactor_iff, Nat.primeFactors_prime_pow he hp]
    exact ⟨p, by simp, hp, hpSmall⟩
  rw [gsDeletePrimeBand_apply f gsA9SmallPrime (pow_pos hp.pos e), if_pos hhas]

/-- Consequently all large-prime local Euler factors agree exactly. -/
theorem gsA9LocalEulerFactor_deleteSmallPrimes_eq
    (f : ℕ → ℂ) (s : ℂ) {p : ℕ}
    (hp : p.Prime) (hpLarge : 23 ≤ p) :
    gsA9LocalEulerFactor (gsDeletePrimeBand f gsA9SmallPrime) s p =
      gsA9LocalEulerFactor f s p := by
  unfold gsA9LocalEulerFactor
  apply tsum_congr
  intro e
  rw [gsDeleteSmallPrimes_prime_pow f hp hpLarge]

/-- At a deleted prime the corresponding local factor is exactly one. -/
theorem gsA9LocalEulerFactor_deleteSmallPrimes_eq_one
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (s : ℂ) {p : ℕ} (hp : p.Prime) (hpSmall : p < 23) :
    gsA9LocalEulerFactor (gsDeletePrimeBand f gsA9SmallPrime) s p = 1 := by
  unfold gsA9LocalEulerFactor
  rw [tsum_eq_single 0]
  · have hno : ¬ HasPrimeFactor gsA9SmallPrime 1 := by
      rw [hasPrimeFactor_iff]
      simp
    simp only [pow_zero]
    rw [gsDeletePrimeBand_apply f gsA9SmallPrime (by simp), if_neg hno,
      hmul.1, one_mul]
  · intro e he
    rw [gsDeleteSmallPrimes_prime_pow_eq_zero f hp hpSmall he, zero_mul]

/-- Equality of every finite large-prime Euler product after deletion. -/
theorem prod_gsA9LocalEulerFactor_deleteSmallPrimes_eq
    (f : ℕ → ℂ) (s : ℂ) (S : Finset ℕ)
    (hprime : ∀ p ∈ S, p.Prime) (hlarge : ∀ p ∈ S, 23 ≤ p) :
    (∏ p ∈ S, gsA9LocalEulerFactor (gsDeletePrimeBand f gsA9SmallPrime) s p) =
      ∏ p ∈ S, gsA9LocalEulerFactor f s p := by
  apply Finset.prod_congr rfl
  intro p hp
  exact gsA9LocalEulerFactor_deleteSmallPrimes_eq f s (hprime p hp) (hlarge p hp)

/-- The omitted small factors of the deleted function are all one, so its
full low-prime product is exactly its product over primes at least `23`. -/
theorem prod_deleteSmallPrimes_primesUpTo_eq_large
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (s : ℂ) (y : ℕ) :
    (∏ p ∈ primesUpTo y,
        gsA9LocalEulerFactor (gsDeletePrimeBand f gsA9SmallPrime) s p) =
      ∏ p ∈ gsA9LargePrimesUpTo y,
        gsA9LocalEulerFactor (gsDeletePrimeBand f gsA9SmallPrime) s p := by
  let a : ℕ → ℂ := fun p ↦
    gsA9LocalEulerFactor (gsDeletePrimeBand f gsA9SmallPrime) s p
  have hsmall : ∏ p ∈ (primesUpTo y).filter (fun p ↦ p < 23), a p = 1 := by
    apply Finset.prod_eq_one
    intro p hp
    have hp' := Finset.mem_filter.mp hp
    exact gsA9LocalEulerFactor_deleteSmallPrimes_eq_one hmul s
      (mem_primesUpTo.mp hp'.1).1 hp'.2
  have hsplit := Finset.prod_filter_mul_prod_filter_not
    (primesUpTo y) (fun p ↦ p < 23) a
  have hlarge : (primesUpTo y).filter (fun p ↦ ¬ p < 23) =
      gsA9LargePrimesUpTo y := by
    ext p
    simp [gsA9LargePrimesUpTo]
  rw [hsmall, one_mul, hlarge] at hsplit
  exact hsplit.symm

/-- The same deletion identity after imposing any additional predicate on
the low primes.  Factors supported below `23` are one, independently of the
predicate, so only the corresponding large-prime filter remains. -/
theorem prod_filter_deleteSmallPrimes_eq_large_filter
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (s : ℂ) (y : ℕ) (P : ℕ → Prop) [DecidablePred P] :
    (∏ p ∈ (primesUpTo y).filter P,
        gsA9LocalEulerFactor (gsDeletePrimeBand f gsA9SmallPrime) s p) =
      ∏ p ∈ (gsA9LargePrimesUpTo y).filter P,
        gsA9LocalEulerFactor (gsDeletePrimeBand f gsA9SmallPrime) s p := by
  symm
  apply Finset.prod_subset
  · intro p hp
    have hp' := Finset.mem_filter.mp hp
    have hpLarge := Finset.mem_filter.mp hp'.1
    exact Finset.mem_filter.mpr ⟨hpLarge.1, hp'.2⟩
  · intro p hp hnot
    have hp' := Finset.mem_filter.mp hp
    have hpPrime := (mem_primesUpTo.mp hp'.1).1
    have hpSmall : p < 23 := by
      by_contra h
      have hpLarge : p ∈ (gsA9LargePrimesUpTo y).filter P := by
        exact Finset.mem_filter.mpr ⟨
          Finset.mem_filter.mpr ⟨hp'.1, Nat.le_of_not_gt h⟩, hp'.2⟩
      exact hnot hpLarge
    exact gsA9LocalEulerFactor_deleteSmallPrimes_eq_one
      hmul s hpPrime hpSmall

/-- Recombining the large low-prime product with the ordinary high factor
recovers the full L-series of the small-prime-deleted coefficient. -/
theorem prod_large_deleteSmallPrimes_mul_high_eq_LSeries
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    (y : ℕ) {s : ℂ} (hs : 1 < s.re) :
    (∏ p ∈ gsA9LargePrimesUpTo y,
        gsA9LocalEulerFactor (gsDeletePrimeBand f gsA9SmallPrime) s p) *
      LSeries (gsA9High (gsDeletePrimeBand f gsA9SmallPrime) y) s =
        LSeries (gsDeletePrimeBand f gsA9SmallPrime) s := by
  have hmulDel := gsDeletePrimeBand_isMultiplicativeOnPositiveNat
    hmul gsA9SmallPrime
  have hboundDel : ∀ n, 0 < n →
      ‖gsDeletePrimeBand f gsA9SmallPrime n‖ ≤ 1 := by
    intro n hn
    exact norm_gsDeletePrimeBand_le_one hbound gsA9SmallPrime hn
  rw [← prod_deleteSmallPrimes_primesUpTo_eq_large hmul s y,
    ← LSeries_gsA9Low_eq_finiteEulerProduct hmulDel hboundDel y hs]
  exact LSeries_gsA9Low_mul_gsA9High hmulDel hboundDel y hs

/-- Above a cutoff at least `23`, the high-prime coefficient is unaffected
by deleting the fixed small primes. -/
theorem gsA9High_deleteSmallPrimes_eq
    (f : ℕ → ℂ) {y : ℕ} (hy : 23 ≤ y) :
    gsA9High (gsDeletePrimeBand f gsA9SmallPrime) y = gsA9High f y := by
  funext n
  unfold gsA9High primeBandCoefficient
  by_cases hs : PrimeSupported (fun p ↦ ¬ p ≤ y) n
  · rw [if_pos hs, if_pos hs]
    have hn : 0 < n := Nat.pos_of_ne_zero hs.1
    have hno : ¬ HasPrimeFactor gsA9SmallPrime n := by
      rw [hasPrimeFactor_iff]
      rintro ⟨p, hpn, hpSmall⟩
      have hpHigh := hs.2 p hpn
      exact hpHigh (hpSmall.2.le.trans hy)
    rw [gsDeletePrimeBand_apply f gsA9SmallPrime hn, if_neg hno]
  · rw [if_neg hs, if_neg hs]

/-- Each one-bounded small-prime Euler factor is controlled by the fixed
positive geometric factor at exponent `1/2`. -/
theorem norm_gsA9LocalEulerFactor_le_smallPrimeGeometric
    {f : ℕ → ℂ} (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    {p : ℕ} (hp : p.Prime) {sigma t : ℝ} (hsigma : 1 / 2 ≤ sigma) :
    ‖gsA9LocalEulerFactor f ((sigma : ℂ) + Complex.I * (t : ℂ)) p‖ ≤
      (1 - (p : ℝ) ^ (-(1 / 2 : ℝ)))⁻¹ := by
  let x : ℂ := (p : ℂ) ^ (-((sigma : ℂ) + Complex.I * (t : ℂ)))
  have hpOne : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_le
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hxnorm : ‖x‖ = (p : ℝ) ^ (-sigma) := by
    exact Erdos67.HalaszCpowDeficit.norm_nat_cpow_neg_sigma_add_I_mul
      hp.pos sigma t
  have hrpow : (p : ℝ) ^ (-sigma) ≤ (p : ℝ) ^ (-(1 / 2 : ℝ)) := by
    exact Real.rpow_le_rpow_of_exponent_le hpOne (by linarith)
  have hhalf : (p : ℝ) ^ (-(1 / 2 : ℝ)) < 1 := by
    exact Real.rpow_lt_one_of_one_lt_of_neg
      (by exact_mod_cast hp.one_lt) (by norm_num)
  have hx : ‖x‖ < 1 := hxnorm.trans_le hrpow |>.trans_lt hhalf
  have hlocal := norm_localEulerSeries_le_inv_one_sub
    (fun e ↦ f (p ^ e)) (fun e ↦ hbound _ (pow_pos hp.pos e)) hx
  unfold gsA9LocalEulerFactor
  change ‖∑' e : ℕ, f (p ^ e) * x ^ e‖ ≤ _
  refine hlocal.trans ?_
  apply (inv_le_inv₀ (sub_pos.mpr hx) (sub_pos.mpr hhalf)).2
  rw [hxnorm]
  linarith

/-- The product of all fixed small-prime factors has a universal bound. -/
theorem norm_prod_gsA9LocalEulerFactor_smallPrimes_le
    {f : ℕ → ℂ} (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    {sigma t : ℝ} (hsigma : 1 / 2 ≤ sigma) :
    ‖∏ p ∈ gsA9SmallPrimeFinset,
        gsA9LocalEulerFactor f ((sigma : ℂ) + Complex.I * (t : ℂ)) p‖ ≤
      gsA9SmallPrimeEulerBound := by
  rw [norm_prod]
  unfold gsA9SmallPrimeEulerBound
  apply Finset.prod_le_prod
  · intro p hp
    exact norm_nonneg _
  · intro p hp
    exact norm_gsA9LocalEulerFactor_le_smallPrimeGeometric hbound
      (Finset.mem_filter.mp hp).2 hsigma

/-- The existing deletion-distance theorem specialized to the fixed small
prime set. -/
theorem archimedeanNonpretentious_half_deleteSmallPrimes
    {f : ℕ → ℂ} {A X : ℕ}
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    (hnonpret : MRArchimedeanNonpretentious f A X) :
    ∀ t : ℝ, |t| ≤ X →
      (A : ℝ) / 2 ≤
        pretentiousDistSq (gsDeletePrimeBand f gsA9SmallPrime)
          (archimedeanTwist t) X :=
  archimedeanNonpretentious_half_deletePrimeBand
    hbound gsA9SmallPrime hnonpret

end

end Erdos67.MRHalaszBands
