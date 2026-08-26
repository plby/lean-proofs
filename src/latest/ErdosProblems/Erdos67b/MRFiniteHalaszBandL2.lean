import ErdosProblems.Erdos67b.MRFiniteHalaszBands
import ErdosProblems.Erdos67b.MRFiniteRamareLargeValues
import ErdosProblems.Erdos67b.MRTDensity

/-!
# Finite local square means for Halasz prime-band factors

The two non-selected factors in the finite Halasz decomposition have no
constant coefficient.  On a dyadic factor interval `(L,U]`, their harmonic
coefficients have square mass `L⁻²` times the Selberg-sieve square mass.
The finite Dirichlet-polynomial mean-value theorem then gives a completely
finite vertical `L²` estimate.  No complete L-series or tail occurs here.
-/

open scoped BigOperators ComplexConjugate Interval
open Complex Finset MeasureTheory

namespace Erdos67b.MRHalaszBands

noncomputable section

open Erdos67b.MRIntervalSieve Erdos67b.SelbergSupport

/-- A prime-band coefficient with the harmonic weight appearing on the
line `Re(s)=1`. -/
def harmonicPrimeBandCoefficient
    (f : ℕ → ℂ) (Q : ℕ → Prop) [DecidablePred Q] (n : ℕ) : ℂ :=
  primeBandCoefficient f Q n * (((n : ℝ)⁻¹ : ℝ) : ℂ)

/-- The finite vertical polynomial of one prime band on a factor interval. -/
def harmonicPrimeBandPolynomial
    (f : ℕ → ℂ) (Q : ℕ → Prop) [DecidablePred Q]
    (L U : ℕ) (t : ℝ) : ℂ :=
  logarithmicDirichletPolynomial (Finset.Ioc L U)
    (harmonicPrimeBandCoefficient f Q) t

/-- The same band coefficient on a real line `Re(s)=sigma`. -/
def smoothedPrimeBandCoefficient
    (f : ℕ → ℂ) (Q : ℕ → Prop) [DecidablePred Q]
    (sigma : ℝ) (n : ℕ) : ℂ :=
  primeBandCoefficient f Q n * Complex.ofReal ((n : ℝ) ^ (-sigma))

def smoothedPrimeBandPolynomial
    (f : ℕ → ℂ) (Q : ℕ → Prop) [DecidablePred Q]
    (sigma : ℝ) (L U : ℕ) (t : ℝ) : ℂ :=
  logarithmicDirichletPolynomial (Finset.Ioc L U)
    (smoothedPrimeBandCoefficient f Q sigma) t

/-- Harmonic weighting converts a local band square mass into an `L⁻²`
multiple. -/
theorem sum_normSq_harmonicPrimeBandCoefficient_le
    {f : ℕ → ℂ} (Q : ℕ → Prop) [DecidablePred Q]
    {L U : ℕ} (hL : 0 < L) :
    (∑ n ∈ Finset.Ioc L U,
        Complex.normSq (harmonicPrimeBandCoefficient f Q n)) ≤
      ((L : ℝ)⁻¹) ^ 2 *
        ∑ n ∈ Finset.Ioc L U,
          Complex.normSq (primeBandCoefficient f Q n) := by
  calc
    (∑ n ∈ Finset.Ioc L U,
        Complex.normSq (harmonicPrimeBandCoefficient f Q n)) ≤
      ∑ n ∈ Finset.Ioc L U,
        ((L : ℝ)⁻¹) ^ 2 *
          Complex.normSq (primeBandCoefficient f Q n) := by
      apply Finset.sum_le_sum
      intro n hn
      have hnL : L < n := (Finset.mem_Ioc.mp hn).1
      have hLR : (0 : ℝ) < L := by exact_mod_cast hL
      have hnR : (0 : ℝ) < n := by
        exact_mod_cast hL.trans hnL
      have hinv : ((n : ℝ)⁻¹) ≤ (L : ℝ)⁻¹ := by
        apply inv_anti₀ hLR
        exact_mod_cast hnL.le
      have hsquare : ((n : ℝ)⁻¹) ^ 2 ≤ ((L : ℝ)⁻¹) ^ 2 :=
        pow_le_pow_left₀ (inv_nonneg.mpr hnR.le) hinv 2
      unfold harmonicPrimeBandCoefficient
      rw [Complex.normSq_mul, Complex.normSq_ofReal]
      have hband : 0 ≤ Complex.normSq (primeBandCoefficient f Q n) :=
        Complex.normSq_nonneg _
      nlinarith
    _ = ((L : ℝ)⁻¹) ^ 2 *
        ∑ n ∈ Finset.Ioc L U,
          Complex.normSq (primeBandCoefficient f Q n) := by
      rw [Finset.mul_sum]

/-- A band supported away from every prime in `I` has square mass at most
the concrete missing-block set.  This adapter permits the exponential
Mertens/beta-sieve density bounds, rather than only the elementary linear
reciprocal-mass sieve. -/
theorem sum_normSq_primeBandCoefficient_le_card_missingPrimeBlockSet
    (I : ℕ × ℕ) (Q : ℕ → Prop) [DecidablePred Q]
    (hdisj : ∀ p ∈ primesInBlock I, ¬ Q p)
    (f : ℕ → ℂ) (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    {L U : ℕ} (hL : 0 < L) :
    (∑ n ∈ Finset.Ioc L U,
        Complex.normSq (primeBandCoefficient f Q n)) ≤
      ((missingPrimeBlockSet I U).card : ℝ) := by
  classical
  have hpoint : ∀ n ∈ Finset.Ioc L U,
      Complex.normSq (primeBandCoefficient f Q n) ≤
        if n ∈ missingPrimeBlockSet I U then 1 else 0 := by
    intro n hn
    have hnpos : 0 < n := hL.trans (Finset.mem_Ioc.mp hn).1
    by_cases hsupp : PrimeSupported Q n
    · have hmissing : n ∈ missingPrimeBlockSet I U := by
        rw [mem_missingPrimeBlockSet]
        refine ⟨hnpos, (Finset.mem_Ioc.mp hn).2, ?_⟩
        rintro ⟨p, hpI, hpn⟩
        have hpprime := (mem_primesInBlock.mp hpI).1
        have hpFactors : p ∈ n.primeFactors :=
          Nat.mem_primeFactors.mpr ⟨hpprime, hpn, hnpos.ne'⟩
        exact hdisj p hpI (hsupp.2 p hpFactors)
      rw [if_pos hmissing,
        primeBandCoefficient_eq_of_supported f Q hsupp,
        Complex.normSq_eq_norm_sq]
      simpa using (sq_le_sq₀ (norm_nonneg _) zero_le_one).2 (hbound n hnpos)
    · rw [show primeBandCoefficient f Q n = 0 by
          simp [primeBandCoefficient, hsupp], Complex.normSq_zero]
      split_ifs <;> norm_num
  calc
    (∑ n ∈ Finset.Ioc L U,
        Complex.normSq (primeBandCoefficient f Q n)) ≤
      ∑ n ∈ Finset.Ioc L U,
        if n ∈ missingPrimeBlockSet I U then (1 : ℝ) else 0 := by
          exact Finset.sum_le_sum hpoint
    _ = (((Finset.Ioc L U).filter
          (fun n ↦ n ∈ missingPrimeBlockSet I U)).card : ℝ) := by
      simp
    _ ≤ ((missingPrimeBlockSet I U).card : ℝ) := by
      exact_mod_cast Finset.card_le_card (by
        intro n hn
        exact (Finset.mem_filter.mp hn).2)

/-- Moving the real part of the line to the right of one can only decrease
the coefficient square mass. -/
theorem sum_normSq_smoothedPrimeBandCoefficient_le_harmonic
    {f : ℕ → ℂ} (Q : ℕ → Prop) [DecidablePred Q]
    {sigma : ℝ} (hsigma : 1 ≤ sigma)
    {L U : ℕ} (hL : 0 < L) :
    (∑ n ∈ Finset.Ioc L U,
        Complex.normSq (smoothedPrimeBandCoefficient f Q sigma n)) ≤
      ∑ n ∈ Finset.Ioc L U,
        Complex.normSq (harmonicPrimeBandCoefficient f Q n) := by
  apply Finset.sum_le_sum
  intro n hn
  have hnpos : 0 < n := hL.trans (Finset.mem_Ioc.mp hn).1
  have hnone : (1 : ℝ) ≤ n := by exact_mod_cast hnpos
  have hrpow : (n : ℝ) ^ (-sigma) ≤ (n : ℝ)⁻¹ := by
    rw [← Real.rpow_neg_one]
    apply Real.rpow_le_rpow_of_exponent_le hnone
    linarith
  have hrpowNonneg : 0 ≤ (n : ℝ) ^ (-sigma) :=
    Real.rpow_nonneg (Nat.cast_nonneg n) _
  have hinvNonneg : 0 ≤ (n : ℝ)⁻¹ :=
    inv_nonneg.mpr (Nat.cast_nonneg n)
  have hsquare : ((n : ℝ) ^ (-sigma)) ^ 2 ≤ ((n : ℝ)⁻¹) ^ 2 :=
    pow_le_pow_left₀ hrpowNonneg hrpow 2
  unfold smoothedPrimeBandCoefficient harmonicPrimeBandCoefficient
  rw [Complex.normSq_mul, Complex.normSq_mul,
    Complex.normSq_ofReal, Complex.normSq_ofReal]
  have hband : 0 ≤ Complex.normSq (primeBandCoefficient f Q n) :=
    Complex.normSq_nonneg _
  nlinarith

/-- Local finite `L²` estimate for a prime band, with the reciprocal-mass
sieve saving and all finite endpoint terms explicit. -/
theorem intervalIntegral_normSq_harmonicPrimeBandPolynomial_le
    (P : Finset ℕ) (hprime : ∀ p ∈ P, p.Prime)
    (hmass : 0 < reciprocalMass P)
    (Q : ℕ → Prop) [DecidablePred Q]
    (hdisj : ∀ p ∈ P, ¬ Q p)
    (f : ℕ → ℂ) (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    {L U : ℕ} (hL : 0 < L) (hLU : L ≤ U)
    {T : ℝ} (hT : 0 ≤ T) :
    (∫ t in -T..T,
        Complex.normSq (harmonicPrimeBandPolynomial f Q L U t)) ≤
      (2 * T + 2 * Real.pi * (U : ℝ)) *
        (((L : ℝ)⁻¹) ^ 2 *
          (((U - L : ℕ) : ℝ) / (1 + reciprocalMass P) +
            2 * P.card + P.card ^ 2)) := by
  have hU : 0 < U := hL.trans_le hLU
  have hpos : ∀ n ∈ Finset.Ioc L U, 0 < n := by
    intro n hn
    exact hL.trans (Finset.mem_Ioc.mp hn).1
  have hupper : ∀ n ∈ Finset.Ioc L U, n ≤ U := by
    intro n hn
    exact (Finset.mem_Ioc.mp hn).2
  have hmean := norm_logarithmicDirichletPolynomial_intervalIntegral_le
    hU hpos hupper (harmonicPrimeBandCoefficient f Q) hT
  have hharmonic := sum_normSq_harmonicPrimeBandCoefficient_le
    (f := f) (L := L) (U := U) Q hL
  have hsieve := sum_normSq_primeBandCoefficient_le
    P hprime hmass Q hdisj f hbound hLU
  have hmassBound :
      (∑ n ∈ Finset.Ioc L U,
          Complex.normSq (harmonicPrimeBandCoefficient f Q n)) ≤
        ((L : ℝ)⁻¹) ^ 2 *
          (((U - L : ℕ) : ℝ) / (1 + reciprocalMass P) +
            2 * P.card + P.card ^ 2) :=
    hharmonic.trans (mul_le_mul_of_nonneg_left hsieve (sq_nonneg _))
  unfold harmonicPrimeBandPolynomial
  rw [intervalIntegral_normSq_eq_norm_intervalIntegral_conj_mul _ hT]
  exact hmean.trans (mul_le_mul_of_nonneg_left hmassBound (by positivity))

/-- The local finite `L²` bound on every Halasz line to the right of one. -/
theorem intervalIntegral_normSq_smoothedPrimeBandPolynomial_le
    (P : Finset ℕ) (hprime : ∀ p ∈ P, p.Prime)
    (hmass : 0 < reciprocalMass P)
    (Q : ℕ → Prop) [DecidablePred Q]
    (hdisj : ∀ p ∈ P, ¬ Q p)
    (f : ℕ → ℂ) (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    {sigma : ℝ} (hsigma : 1 ≤ sigma)
    {L U : ℕ} (hL : 0 < L) (hLU : L ≤ U)
    {T : ℝ} (hT : 0 ≤ T) :
    (∫ t in -T..T,
        Complex.normSq
          (smoothedPrimeBandPolynomial f Q sigma L U t)) ≤
      (2 * T + 2 * Real.pi * (U : ℝ)) *
        (((L : ℝ)⁻¹) ^ 2 *
          (((U - L : ℕ) : ℝ) / (1 + reciprocalMass P) +
            2 * P.card + P.card ^ 2)) := by
  have hU : 0 < U := hL.trans_le hLU
  have hpos : ∀ n ∈ Finset.Ioc L U, 0 < n := by
    intro n hn
    exact hL.trans (Finset.mem_Ioc.mp hn).1
  have hupper : ∀ n ∈ Finset.Ioc L U, n ≤ U := by
    intro n hn
    exact (Finset.mem_Ioc.mp hn).2
  have hmean := norm_logarithmicDirichletPolynomial_intervalIntegral_le
    hU hpos hupper (smoothedPrimeBandCoefficient f Q sigma) hT
  have hsmooth := sum_normSq_smoothedPrimeBandCoefficient_le_harmonic
    (f := f) Q hsigma (L := L) (U := U) hL
  have hharmonic := sum_normSq_harmonicPrimeBandCoefficient_le
    (f := f) (L := L) (U := U) Q hL
  have hsieve := sum_normSq_primeBandCoefficient_le
    P hprime hmass Q hdisj f hbound hLU
  have hmassBound :
      (∑ n ∈ Finset.Ioc L U,
          Complex.normSq (smoothedPrimeBandCoefficient f Q sigma n)) ≤
        ((L : ℝ)⁻¹) ^ 2 *
          (((U - L : ℕ) : ℝ) / (1 + reciprocalMass P) +
            2 * P.card + P.card ^ 2) :=
    hsmooth.trans <| hharmonic.trans <|
      mul_le_mul_of_nonneg_left hsieve (sq_nonneg _)
  unfold smoothedPrimeBandPolynomial
  rw [intervalIntegral_normSq_eq_norm_intervalIntegral_conj_mul _ hT]
  exact hmean.trans (mul_le_mul_of_nonneg_left hmassBound (by positivity))

/-- Strong-sieve version of the local finite line estimate.  The concrete
cardinality on the right can be discharged by
`exists_card_missingPrimeBlockSet_mertens_beta_bound`, giving the required
exponential-in-reciprocal-mass (Mertens ratio) saving. -/
theorem intervalIntegral_normSq_smoothedPrimeBandPolynomial_le_missingBlock
    (I : ℕ × ℕ) (Q : ℕ → Prop) [DecidablePred Q]
    (hdisj : ∀ p ∈ primesInBlock I, ¬ Q p)
    (f : ℕ → ℂ) (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    {sigma : ℝ} (hsigma : 1 ≤ sigma)
    {L U : ℕ} (hL : 0 < L) (hLU : L ≤ U)
    {T : ℝ} (hT : 0 ≤ T) :
    (∫ t in -T..T,
        Complex.normSq
          (smoothedPrimeBandPolynomial f Q sigma L U t)) ≤
      (2 * T + 2 * Real.pi * (U : ℝ)) *
        (((L : ℝ)⁻¹) ^ 2 *
          ((missingPrimeBlockSet I U).card : ℝ)) := by
  have hU : 0 < U := hL.trans_le hLU
  have hpos : ∀ n ∈ Finset.Ioc L U, 0 < n := by
    intro n hn
    exact hL.trans (Finset.mem_Ioc.mp hn).1
  have hupper : ∀ n ∈ Finset.Ioc L U, n ≤ U := by
    intro n hn
    exact (Finset.mem_Ioc.mp hn).2
  have hmean := norm_logarithmicDirichletPolynomial_intervalIntegral_le
    hU hpos hupper (smoothedPrimeBandCoefficient f Q sigma) hT
  have hsmooth := sum_normSq_smoothedPrimeBandCoefficient_le_harmonic
    (f := f) Q hsigma (L := L) (U := U) hL
  have hharmonic := sum_normSq_harmonicPrimeBandCoefficient_le
    (f := f) (L := L) (U := U) Q hL
  have hmissing :=
    sum_normSq_primeBandCoefficient_le_card_missingPrimeBlockSet
      I Q hdisj f hbound (L := L) (U := U) hL
  have hmassBound :
      (∑ n ∈ Finset.Ioc L U,
          Complex.normSq (smoothedPrimeBandCoefficient f Q sigma n)) ≤
        ((L : ℝ)⁻¹) ^ 2 *
          ((missingPrimeBlockSet I U).card : ℝ) :=
    hsmooth.trans <| hharmonic.trans <|
      mul_le_mul_of_nonneg_left hmissing (sq_nonneg _)
  unfold smoothedPrimeBandPolynomial
  rw [intervalIntegral_normSq_eq_norm_intervalIntegral_conj_mul _ hT]
  exact hmean.trans (mul_le_mul_of_nonneg_left hmassBound (by positivity))

/-- A positive prefix-truncated L-series is exactly its finite logarithmic
polynomial on the line `sigma + i t`. -/
theorem LSeries_positivePrefixTruncate_eq_logarithmic
    (a : ℕ → ℂ) (N : ℕ) (sigma t : ℝ) :
    LSeries (positivePrefixTruncate a N)
        ((sigma : ℂ) + Complex.I * (t : ℂ)) =
      logarithmicDirichletPolynomial (Finset.Ioc 1 N)
        (fun n ↦ a n * Complex.ofReal ((n : ℝ) ^ (-sigma))) (-t) := by
  classical
  unfold LSeries logarithmicDirichletPolynomial
  rw [tsum_eq_sum (s := Finset.Ioc 1 N)]
  · apply Finset.sum_congr rfl
    intro n hn
    have hn1 : 1 < n := (Finset.mem_Ioc.mp hn).1
    have hnN : n ≤ N := (Finset.mem_Ioc.mp hn).2
    have hnpos : 0 < n := by omega
    rw [LSeries.term_of_ne_zero hnpos.ne',
      positivePrefixTruncate_eq_of_lt_le a hn1 hnN,
      div_eq_mul_inv, ← Complex.cpow_neg,
      ← ofReal_rpow_mul_logarithmicPhase_neg_eq_cpow_neg
        hnpos sigma t]
    ring
  · intro n hn
    by_cases hn0 : n = 0
    · subst n
      simp
    · rw [LSeries.term_of_ne_zero hn0]
      by_cases hn1 : n ≤ 1
      · rw [positivePrefixTruncate_eq_zero_of_le_one a hn1, zero_div]
      · have hNone : N < n := by
          by_contra hnot
          exact hn (Finset.mem_Ioc.mpr
            ⟨Nat.lt_of_not_ge hn1, Nat.le_of_not_gt hnot⟩)
        rw [positivePrefixTruncate_eq_zero_of_lt a hNone, zero_div]

end

end Erdos67b.MRHalaszBands
