import ErdosProblems.Erdos67b.MRMeanSquareProof
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.NumberTheory.SmoothNumbers

/-!
# Prime-band and finite mean-square helpers for the cheap Halasz argument

The cheap proof of Halasz's theorem splits every integer into factors whose
prime factors lie in disjoint bands.  This file records that splitting at the
level of `Nat.factorization`; in particular it does not appeal to a
factorisation choice or to unique choice.

It also packages the finite logarithmic-polynomial mean-square estimate in
the weighted form used for a truncated Dirichlet series.
-/

open scoped BigOperators ComplexConjugate LSeries.notation
open Finset
open MeasureTheory

namespace Erdos67b.MRHalaszBands

noncomputable section

/-- The factor of `n` obtained by retaining precisely the prime powers whose
prime satisfies `P`.  At `n = 0` this has the harmless value `1`, since
`Nat.factorization 0 = 0`. -/
def primeBandPart (P : ℕ → Prop) [DecidablePred P] (n : ℕ) : ℕ :=
  (n.factorization.filter P).prod fun p e ↦ p ^ e

theorem primeBandPart_factorization (P : ℕ → Prop) [DecidablePred P]
    (n : ℕ) :
    (primeBandPart P n).factorization = n.factorization.filter P := by
  unfold primeBandPart
  apply Nat.prod_pow_factorization_eq_self
  intro p hp
  rw [Finsupp.support_filter, Finset.mem_filter] at hp
  exact Nat.prime_of_mem_primeFactors (by simpa using hp.1)

theorem primeBandPart_ne_zero (P : ℕ → Prop) [DecidablePred P]
    (n : ℕ) :
    primeBandPart P n ≠ 0 := by
  unfold primeBandPart Finsupp.prod
  apply Finset.prod_ne_zero_iff.mpr
  intro p hp
  rw [Finsupp.support_filter, Finset.mem_filter] at hp
  exact pow_ne_zero _ (Nat.prime_of_mem_primeFactors (by simpa using hp.1)).ne_zero

/-- Complementary prime bands multiply back to the original nonzero
integer. -/
theorem primeBandPart_mul_compl (P : ℕ → Prop) [DecidablePred P]
    {n : ℕ} (hn : n ≠ 0) :
    primeBandPart P n * primeBandPart (fun p ↦ ¬ P p) n = n := by
  unfold primeBandPart
  rw [Finsupp.prod_filter_mul_prod_filter_not]
  exact Nat.prod_factorization_pow_eq_self hn

theorem primeBandPart_factorization_apply_pos
    (P : ℕ → Prop) [DecidablePred P] (n p : ℕ) (hp : P p) :
    (primeBandPart P n).factorization p = n.factorization p := by
  rw [primeBandPart_factorization, Finsupp.filter_apply_pos _ _ hp]

theorem primeBandPart_factorization_apply_neg
    (P : ℕ → Prop) [DecidablePred P] (n p : ℕ) (hp : ¬ P p) :
    (primeBandPart P n).factorization p = 0 := by
  rw [primeBandPart_factorization, Finsupp.filter_apply_neg _ _ hp]

/-- Every prime factor of a band part lies in that band. -/
theorem primeFactors_primeBandPart_subset
    (P : ℕ → Prop) [DecidablePred P] (n : ℕ) :
    (primeBandPart P n).primeFactors ⊆ n.primeFactors.filter P := by
  intro p hp
  have hpSupport : p ∈ (primeBandPart P n).factorization.support := by
    simpa only [Nat.support_factorization] using hp
  rw [primeBandPart_factorization, Finsupp.support_filter] at hpSupport
  exact hpSupport

/-- Prime factors in the selected band are retained with their full
multiplicity. -/
theorem prime_mem_primeFactors_primeBandPart_iff
    (P : ℕ → Prop) [DecidablePred P] (n p : ℕ) :
    p ∈ (primeBandPart P n).primeFactors ↔ p ∈ n.primeFactors ∧ P p := by
  rw [← Nat.support_factorization, primeBandPart_factorization,
    Finsupp.support_filter, Finset.mem_filter, Nat.support_factorization]

/-- A positive integer is supported on a prescribed band of primes. -/
def PrimeSupported (P : ℕ → Prop) (n : ℕ) : Prop :=
  n ≠ 0 ∧ ∀ p ∈ n.primeFactors, P p

theorem primeSupported_primeBandPart
    (P : ℕ → Prop) [DecidablePred P] (n : ℕ) :
    PrimeSupported P (primeBandPart P n) := by
  refine ⟨primeBandPart_ne_zero P n, ?_⟩
  intro p hp
  have hp' := primeFactors_primeBandPart_subset P n hp
  exact (Finset.mem_filter.mp hp').2

/-- The prime-band factorization is the unique factorization `d * e = n`
with `d` supported on `P` and `e` supported on the complementary band. -/
theorem eq_primeBandParts_of_mul_eq
    (P : ℕ → Prop) [DecidablePred P]
    {d e n : ℕ} (hde : d * e = n)
    (hd : PrimeSupported P d)
    (he : PrimeSupported (fun p ↦ ¬ P p) e) :
    d = primeBandPart P n ∧
      e = primeBandPart (fun p ↦ ¬ P p) n := by
  have hfac : n.factorization = d.factorization + e.factorization := by
    rw [← hde, Nat.factorization_mul hd.1 he.1]
  have hdEq : d = primeBandPart P n := by
    apply Nat.eq_of_factorization_eq hd.1 (primeBandPart_ne_zero P n)
    intro p
    rw [primeBandPart_factorization, Finsupp.filter_apply]
    by_cases hp : P p
    · rw [if_pos hp, hfac, Finsupp.add_apply]
      have hep : e.factorization p = 0 := by
        by_contra hne
        have hmem : p ∈ e.primeFactors := by
          simpa [← Nat.support_factorization, Finsupp.mem_support_iff] using hne
        exact he.2 p hmem hp
      omega
    · rw [if_neg hp]
      by_contra hne
      have hmem : p ∈ d.primeFactors := by
        simpa [← Nat.support_factorization, Finsupp.mem_support_iff] using hne
      exact hp (hd.2 p hmem)
  have heEq : e = primeBandPart (fun p ↦ ¬ P p) n := by
    apply Nat.eq_of_factorization_eq he.1
      (primeBandPart_ne_zero (fun p ↦ ¬ P p) n)
    intro p
    rw [primeBandPart_factorization, Finsupp.filter_apply]
    by_cases hp : P p
    · rw [if_neg (not_not_intro hp)]
      by_contra hne
      have hmem : p ∈ e.primeFactors := by
        simpa [← Nat.support_factorization, Finsupp.mem_support_iff] using hne
      exact he.2 p hmem hp
    · rw [if_pos hp, hfac, Finsupp.add_apply]
      have hdp : d.factorization p = 0 := by
        by_contra hne
        have hmem : p ∈ d.primeFactors := by
          simpa [← Nat.support_factorization, Finsupp.mem_support_iff] using hne
        exact hp (hd.2 p hmem)
      omega
  exact ⟨hdEq, heEq⟩

/-- Restriction of an arithmetic coefficient to integers supported on one
prime band. -/
noncomputable def primeBandCoefficient (a : ℕ → ℂ) (P : ℕ → Prop)
    [DecidablePred P] (n : ℕ) : ℂ := by
  classical
  exact if PrimeSupported P n then a n else 0

theorem primeBandCoefficient_eq_of_supported
    (a : ℕ → ℂ) (P : ℕ → Prop) [DecidablePred P]
    {n : ℕ} (hn : PrimeSupported P n) :
    primeBandCoefficient a P n = a n := by
  simp [primeBandCoefficient, hn]

/-- Exact coefficient factorization across two complementary prime bands.
This is the algebraic core of the small/medium/large convolution split. -/
theorem primeBandCoefficient_convolution_compl
    (h : ℕ →*₀ ℂ) (P : ℕ → Prop) [DecidablePred P] :
    LSeries.convolution (primeBandCoefficient h P)
        (primeBandCoefficient h (fun p ↦ ¬ P p)) = h := by
  funext n
  by_cases hn : n = 0
  · subst n
    simp [LSeries.convolution_map_zero]
  · rw [LSeries.convolution_def]
    change (∑ p ∈ n.divisorsAntidiagonal,
      primeBandCoefficient h P p.1 *
        primeBandCoefficient h (fun p ↦ ¬ P p) p.2) = h n
    let d := primeBandPart P n
    let e := primeBandPart (fun p ↦ ¬ P p) n
    have hde : d * e = n := by
      exact primeBandPart_mul_compl P hn
    have hd : PrimeSupported P d := primeSupported_primeBandPart P n
    have he : PrimeSupported (fun p ↦ ¬ P p) e :=
      primeSupported_primeBandPart (fun p ↦ ¬ P p) n
    have hmem : (d, e) ∈ n.divisorsAntidiagonal :=
      Nat.mem_divisorsAntidiagonal.mpr ⟨hde, hn⟩
    rw [Finset.sum_eq_single (d, e)]
    · simp only [primeBandCoefficient_eq_of_supported h P hd,
        primeBandCoefficient_eq_of_supported h (fun p ↦ ¬ P p) he]
      rw [← map_mul, hde]
    · intro q hq hqne
      by_cases hqP : PrimeSupported P q.1
      · by_cases hqC : PrimeSupported (fun p ↦ ¬ P p) q.2
        · have hqmul := (Nat.mem_divisorsAntidiagonal.mp hq).1
          have hu := eq_primeBandParts_of_mul_eq P hqmul hqP hqC
          exact (hqne (Prod.ext hu.1 hu.2)).elim
        · simp [primeBandCoefficient, hqC]
      · simp [primeBandCoefficient, hqP]
    · intro hnot
      exact (hnot hmem).elim

/-- The weighted coefficient on the first `N` positive integers. -/
def weightedPrefixCoefficient (a : ℕ → ℂ) (sigma : ℝ) {N : ℕ}
    (n : Fin N) : ℂ :=
  a (n.1 + 1) * Complex.ofReal (((n.1 + 1 : ℕ) : ℝ) ^ (-sigma))

/-- A finite weighted Dirichlet polynomial, indexed so that its frequencies
are exactly `log 1, ..., log N`. -/
def weightedPrefixPolynomial (a : ℕ → ℂ) (N : ℕ)
    (sigma t : ℝ) : ℂ :=
  finiteFrequencyPolynomial (fun n : Fin N ↦ Real.log (n.1 + 1))
    (weightedPrefixCoefficient a sigma) t

/-- Exact finite mean-square estimate for a weighted prefix.  This is the
finite `L²` input used after truncating a prime-band Euler factor. -/
theorem norm_weightedPrefixPolynomial_intervalIntegral_le
    {N : ℕ} (hN : 0 < N) (a : ℕ → ℂ) (sigma : ℝ)
    {T : ℝ} (hT : 0 ≤ T) :
    ‖∫ t in -T..T,
        conj (weightedPrefixPolynomial a N sigma t) *
          weightedPrefixPolynomial a N sigma t‖ ≤
      (2 * T + 2 * Real.pi * (N : ℝ)) *
        ∑ n : Fin N, ‖weightedPrefixCoefficient a sigma n‖ ^ 2 := by
  exact norm_finiteLogPolynomial_intervalIntegral_le hN
    (weightedPrefixCoefficient a sigma) hT

/-- The integrated `L^∞ × L² × L²` estimate used after the
three-prime-band factorization.  It is stated for an arbitrary measure so it
applies directly to the restricted Lebesgue measure on a Perron segment. -/
theorem norm_integral_triple_le_Linfty_mul_L2_mul_L2
    {alpha : Type*} [MeasurableSpace alpha] {mu : Measure alpha}
    {f g k : alpha → ℂ} {M : ℝ}
    (hM : 0 ≤ M) (hf : ∀ᵐ x ∂mu, ‖f x‖ ≤ M)
    (hg : MemLp g (2 : ENNReal) mu)
    (hk : MemLp k (2 : ENNReal) mu) :
    ‖∫ x, f x * g x * k x ∂mu‖ ≤
      M *
        ((∫ x, ‖g x‖ ^ (2 : ℝ) ∂mu) ^ ((1 : ℝ) / 2)) *
        ((∫ x, ‖k x‖ ^ (2 : ℝ) ∂mu) ^ ((1 : ℝ) / 2)) := by
  have hprod : Integrable (fun x ↦ ‖g x‖ * ‖k x‖) mu := by
    change Integrable ((fun x ↦ ‖g x‖) * (fun x ↦ ‖k x‖)) mu
    exact hg.norm.integrable_mul hk.norm
  have hmajor : Integrable (fun x ↦ M * (‖g x‖ * ‖k x‖)) mu :=
    hprod.const_mul M
  have hpoint : ∀ᵐ x ∂mu,
      ‖f x * g x * k x‖ ≤ M * (‖g x‖ * ‖k x‖) := by
    filter_upwards [hf] with x hx
    rw [norm_mul, norm_mul]
    calc
      ‖f x‖ * ‖g x‖ * ‖k x‖ = ‖f x‖ * (‖g x‖ * ‖k x‖) := by ring
      _ ≤ M * (‖g x‖ * ‖k x‖) :=
        mul_le_mul_of_nonneg_right hx
          (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  have hholder := integral_mul_norm_le_Lp_mul_Lq
    (μ := mu) (p := (2 : ℝ)) (q := (2 : ℝ))
    Real.HolderConjugate.two_two (by simpa using hg) (by simpa using hk)
  calc
    ‖∫ x, f x * g x * k x ∂mu‖ ≤
        ∫ x, M * (‖g x‖ * ‖k x‖) ∂mu :=
      norm_integral_le_of_norm_le hmajor hpoint
    _ = M * ∫ x, ‖g x‖ * ‖k x‖ ∂mu := by
      rw [integral_const_mul]
    _ ≤ M *
          (((∫ x, ‖g x‖ ^ (2 : ℝ) ∂mu) ^ ((1 : ℝ) / 2)) *
            ((∫ x, ‖k x‖ ^ (2 : ℝ) ∂mu) ^ ((1 : ℝ) / 2))) :=
      mul_le_mul_of_nonneg_left hholder hM
    _ = _ := by ring

/-- Perron-segment specialization of the preceding Hölder estimate.  The
`L²` hypotheses are exactly on the restricted measure represented by the
oriented interval integral. -/
theorem norm_intervalIntegral_triple_le_Linfty_mul_L2_mul_L2
    {f g k : ℝ → ℂ} {M T : ℝ}
    (hM : 0 ≤ M) (hT : 0 ≤ T)
    (hf : ∀ t, |t| ≤ T → ‖f t‖ ≤ M)
    (hg : MemLp g (2 : ENNReal)
      (volume.restrict (Set.Ioc (-T) T)))
    (hk : MemLp k (2 : ENNReal)
      (volume.restrict (Set.Ioc (-T) T))) :
    ‖∫ t in -T..T, f t * g t * k t‖ ≤
      M *
        ((∫ t in -T..T, ‖g t‖ ^ (2 : ℝ)) ^ ((1 : ℝ) / 2)) *
        ((∫ t in -T..T, ‖k t‖ ^ (2 : ℝ)) ^ ((1 : ℝ) / 2)) := by
  have hle : -T ≤ T := by linarith
  have hfAE : ∀ᵐ t ∂(volume.restrict (Set.Ioc (-T) T)), ‖f t‖ ≤ M :=
    ae_restrict_of_forall_mem measurableSet_Ioc fun t ht ↦ by
      apply hf t
      exact abs_le.mpr ⟨ht.1.le, ht.2⟩
  have hbase := norm_integral_triple_le_Linfty_mul_L2_mul_L2
    (mu := volume.restrict (Set.Ioc (-T) T)) hM hfAE hg hk
  simpa only [← intervalIntegral.integral_of_le hle] using hbase

/-- A one-bounded coefficient has square mass bounded by the corresponding
scalar power weights. -/
theorem weightedPrefixCoefficient_norm_sq_le
    {a : ℕ → ℂ} (ha : ∀ n, 0 < n → ‖a n‖ ≤ 1)
    (sigma : ℝ) {N : ℕ} (n : Fin N) :
    ‖weightedPrefixCoefficient a sigma n‖ ^ 2 ≤
      (((n.1 + 1 : ℕ) : ℝ) ^ (-sigma)) ^ 2 := by
  unfold weightedPrefixCoefficient
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (by positivity) _)]
  simp only [Nat.cast_add, Nat.cast_one]
  have ha' := ha (n.1 + 1) (Nat.zero_lt_succ _)
  have hw : 0 ≤ ((n.1 + 1 : ℝ) ^ (-sigma)) :=
    Real.rpow_nonneg (by positivity) _
  apply (sq_le_sq₀ (mul_nonneg (norm_nonneg _) hw) hw).2
  simpa only [one_mul] using mul_le_mul_of_nonneg_right ha' hw

/-- Triangle-inequality bound for a one-bounded sum supported on smooth
numbers, followed by Mathlib's explicit smooth-number cardinality bound. -/
theorem norm_sum_smoothNumbersUpTo_le
    {a : ℕ → ℂ} (ha : ∀ n, 0 < n → ‖a n‖ ≤ 1)
    (N k : ℕ) :
    ‖∑ n ∈ Nat.smoothNumbersUpTo N k, a n‖ ≤
      (2 ^ (Nat.primesBelow k).card * N.sqrt : ℕ) := by
  calc
    ‖∑ n ∈ Nat.smoothNumbersUpTo N k, a n‖ ≤
        ∑ n ∈ Nat.smoothNumbersUpTo N k, ‖a n‖ := norm_sum_le _ _
    _ ≤ ∑ _n ∈ Nat.smoothNumbersUpTo N k, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro n hn
      exact ha n (Nat.ne_zero_of_mem_smoothNumbers
        (Nat.mem_smoothNumbersUpTo.mp hn).2).bot_lt
    _ = (Nat.smoothNumbersUpTo N k).card := by simp
    _ ≤ (2 ^ (Nat.primesBelow k).card * N.sqrt : ℕ) := by
      exact_mod_cast Nat.smoothNumbersUpTo_card_le N k

end

end Erdos67b.MRHalaszBands
