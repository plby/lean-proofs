import ErdosProblems.Erdos239.External.Erdos67.MRCofactorPerron
import ErdosProblems.Erdos239.External.Erdos67.MRHalaszPerron
import ErdosProblems.Erdos239.External.Erdos67.MRLemma14
import ErdosProblems.Erdos239.External.Erdos67.MRCommonCoefficient

/-!
# Mellin--Perron projection for the denominator-corrected Ramaré coefficient

The common-denominator Ramaré expression is the short sum of a single
Dirichlet-convolution coefficient.  This file identifies its complete
`LSeries` with the product of the selected-prime polynomial and the
denominator-weighted cofactor series.  It then applies the explicit Perron
theorem to the coefficient after the Mellin shift `n ^ (-1-it)`.  Thus the
finite polynomial on `(X,2X]` which occurs in `MRLemma14` is obtained from
the rectangular product on the shifted vertical line, with the exact
countable Perron error and endpoint correction exposed.
-/

open scoped BigOperators ComplexConjugate LSeries.notation
open Finset Complex

namespace Erdos67

noncomputable section

/-- The coefficient supported on the selected prime block. -/
def mrPrimeBlockCoefficient (P : Finset ℕ) (f : ℕ → ℂ) (n : ℕ) : ℂ :=
  if n ∈ P then f n else 0

/-- The complete common-denominator Ramaré coefficient.  Its value at zero
is set to zero, matching Mathlib's convention for Dirichlet convolution. -/
def mrRamareConvolutionCoefficient
    (P : Finset ℕ) (f : ℕ → ℂ) (n : ℕ) : ℂ :=
  if n = 0 then 0 else mrCommonRamareCoefficient P f n

/-- The displayed divisor sum is precisely the Dirichlet convolution of the
prime-block coefficient with the denominator-weighted cofactor. -/
theorem mrRamareConvolutionCoefficient_eq_convolution
    (P : Finset ℕ) (f : ℕ → ℂ) :
    mrRamareConvolutionCoefficient P f =
      LSeries.convolution (mrPrimeBlockCoefficient P f)
        (fun k ↦ f k / (mrCommonDenominator P k : ℂ)) := by
  classical
  funext n
  by_cases hn : n = 0
  · subst n
    simp [mrRamareConvolutionCoefficient, LSeries.convolution_map_zero]
  · rw [mrRamareConvolutionCoefficient, if_neg hn,
      LSeries.convolution_def]
    unfold mrCommonRamareCoefficient
    change (∑ p ∈ P, if p ∣ n then
        f p * f (n / p) / (mrCommonDenominator P (n / p) : ℂ)
      else 0) =
      ∑ q ∈ n.divisorsAntidiagonal,
        mrPrimeBlockCoefficient P f q.1 *
          (f q.2 / (mrCommonDenominator P q.2 : ℂ))
    have hanti := Nat.sum_divisorsAntidiagonal
      (fun p k : ℕ ↦ mrPrimeBlockCoefficient P f p *
        (f k / (mrCommonDenominator P k : ℂ))) (n := n)
    rw [hanti]
    simp only [mrPrimeBlockCoefficient, ite_mul, zero_mul]
    rw [← Finset.sum_filter, ← Finset.sum_filter]
    apply Finset.sum_congr
    · ext p
      simp [hn, and_comm]
    · intro p hp
      ring

/-- A finite prime support has an absolutely convergent `LSeries` on every
vertical line. -/
theorem mrPrimeBlockCoefficient_LSeriesSummable
    (P : Finset ℕ) (f : ℕ → ℂ) (s : ℂ) :
    LSeriesSummable (mrPrimeBlockCoefficient P f) s := by
  apply summable_of_hasFiniteSupport
  refine (P.finite_toSet.subset ?_)
  intro n hnSupport
  by_contra hnP
  by_cases hn0 : n = 0
  · subst n
    exact hnSupport (by simp [LSeries.term])
  · have hnP' : n ∉ P := by simpa using hnP
    have hcoeff : mrPrimeBlockCoefficient P f n = 0 := by
      simp [mrPrimeBlockCoefficient, hnP']
    exact hnSupport (by
      rw [LSeries.term_of_ne_zero hn0, hcoeff, zero_div])

/-- The finite prime `LSeries` is the prime Perron factor in logarithmic
phase notation. -/
theorem LSeries_mrPrimeBlockCoefficient_eq_ramarePrimePerronFactorAt
    (P : Finset ℕ) (f : ℕ → ℂ) (sigma t : ℝ)
    (hPpos : ∀ p ∈ P, 0 < p) :
    LSeries (mrPrimeBlockCoefficient P f)
        ((sigma : ℂ) + Complex.I * (t : ℂ)) =
      logarithmicDirichletPolynomial P
        (weightedPrimeCoefficient f sigma) (-t) := by
  rw [LSeries, tsum_eq_sum (s := P)]
  · unfold logarithmicDirichletPolynomial weightedPrimeCoefficient
    apply Finset.sum_congr rfl
    intro p hp
    have hp0 := hPpos p hp
    rw [LSeries.term_of_ne_zero hp0.ne', mrPrimeBlockCoefficient,
      if_pos hp, div_eq_mul_inv, ← Complex.cpow_neg]
    rw [← ofReal_rpow_mul_logarithmicPhase_neg_eq_cpow_neg hp0 sigma t]
    ring
  · intro n hn
    simp [LSeries.term, mrPrimeBlockCoefficient, hn]

/-- Complete product identity for the common-denominator Ramaré
coefficient. -/
theorem LSeries_mrRamareConvolutionCoefficient_eq_product
    (P : Finset ℕ) {f : ℕ → ℂ}
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    {s : ℂ} (hs : 1 < s.re) :
    LSeries (mrRamareConvolutionCoefficient P f) s =
      LSeries (mrPrimeBlockCoefficient P f) s *
        mrCofactorLSeries P f s := by
  rw [mrRamareConvolutionCoefficient_eq_convolution,
    LSeries_convolution'
      (mrPrimeBlockCoefficient_LSeriesSummable P f s)
      (mrCofactorLSeriesSummable P hbound hs)]
  rfl

theorem mrRamareConvolutionCoefficient_LSeriesSummable
    (P : Finset ℕ) {f : ℕ → ℂ}
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (mrRamareConvolutionCoefficient P f) s := by
  rw [mrRamareConvolutionCoefficient_eq_convolution]
  exact (mrPrimeBlockCoefficient_LSeriesSummable P f s).convolution
    (mrCofactorLSeriesSummable P hbound hs)

/-- On the Halász vertical line, the complete product is exactly the finite
prime Perron factor times the complete denominator-weighted cofactor
series. -/
theorem LSeries_mrRamareConvolutionCoefficient_eq_ramare_product
    (I : ℕ × ℕ) {f : ℕ → ℂ}
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    {sigma t : ℝ} (hsigma : 1 < sigma) :
    LSeries (mrRamareConvolutionCoefficient (primesInBlock I) f)
        ((sigma : ℂ) + Complex.I * (t : ℂ)) =
      ramarePrimePerronFactorAt sigma I f t *
        mrCofactorLSeries (primesInBlock I) f
          ((sigma : ℂ) + Complex.I * (t : ℂ)) := by
  rw [LSeries_mrRamareConvolutionCoefficient_eq_product
    (primesInBlock I) hbound (by simpa using hsigma)]
  rw [LSeries_mrPrimeBlockCoefficient_eq_ramarePrimePerronFactorAt]
  · rfl
  · intro p hp
    exact (mem_primesInBlock.mp hp).1.pos

/-- The common-denominator finite Ramaré expression is the short sum of
the complete convolution coefficient. -/
theorem mrCommonDenominatorRamareShortSum_zero_eq_sum_convolution
    {P S : Finset ℕ} (hP : ∀ p ∈ P, p.Prime)
    (hSpos : ∀ m ∈ S, 0 < m) (f : ℕ → ℂ) (n : ℕ) :
    mrCommonDenominatorRamareShortSum P S f n 0 =
      ∑ m ∈ S, mrRamareConvolutionCoefficient P f m := by
  classical
  rw [mrCommonDenominatorRamareShortSum_eq_coefficient_sum hP]
  apply Finset.sum_congr rfl
  intro m hm
  simp [additivePhase, mrRamareConvolutionCoefficient,
    mrCommonRamareCoefficient, (hSpos m hm).ne']

/-! ## Mellin translation -/

/-- Multiplication by the Mellin monomial `n^(-rho-it)`, with the zero
coefficient fixed to zero. -/
def mrMellinShiftedCoefficient
    (a : ℕ → ℂ) (rho t : ℝ) (n : ℕ) : ℂ :=
  if n = 0 then 0 else
    a n / (n : ℂ) ^ ((rho : ℂ) + Complex.I * (t : ℂ))

/-- A Mellin shift of coefficients is a vertical translation of the
corresponding `LSeries`, term by term. -/
theorem LSeries_term_mrMellinShiftedCoefficient
    (a : ℕ → ℂ) (rho t delta u : ℝ) (n : ℕ) :
    LSeries.term (mrMellinShiftedCoefficient a rho t)
        ((delta : ℂ) + Complex.I * (u : ℂ)) n =
      LSeries.term a
        (((rho + delta : ℝ) : ℂ) +
          Complex.I * ((t + u : ℝ) : ℂ)) n := by
  by_cases hn : n = 0
  · subst n
    simp [LSeries.term]
  · rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn]
    unfold mrMellinShiftedCoefficient
    rw [if_neg hn, div_div]
    have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn
    rw [← Complex.cpow_add _ _ hnC]
    congr 2
    push_cast
    ring

theorem LSeries_mrMellinShiftedCoefficient
    (a : ℕ → ℂ) (rho t delta u : ℝ) :
    LSeries (mrMellinShiftedCoefficient a rho t)
        ((delta : ℂ) + Complex.I * (u : ℂ)) =
      LSeries a
        (((rho + delta : ℝ) : ℂ) +
          Complex.I * ((t + u : ℝ) : ℂ)) := by
  unfold LSeries
  apply tsum_congr
  exact LSeries_term_mrMellinShiftedCoefficient a rho t delta u

/-- The norm of a Mellin-shifted coefficient is independent of the
vertical parameter. -/
theorem norm_mrMellinShiftedCoefficient_eq
    (a : ℕ → ℂ) (rho t : ℝ) {n : ℕ} (hn : 0 < n) :
    ‖mrMellinShiftedCoefficient a rho t n‖ =
      ‖a n‖ / (n : ℝ) ^ rho := by
  unfold mrMellinShiftedCoefficient
  rw [if_neg hn.ne', norm_div]
  congr 1
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  simpa using Complex.norm_cpow_eq_rpow_re_of_pos hnR
    ((rho : ℂ) + Complex.I * (t : ℂ))

theorem norm_mrMellinShiftedCoefficient_vertical_eq
    (a : ℕ → ℂ) (rho t u : ℝ) (n : ℕ) :
    ‖mrMellinShiftedCoefficient a rho t n‖ =
      ‖mrMellinShiftedCoefficient a rho u n‖ := by
  by_cases hn : n = 0
  · subst n
    simp [mrMellinShiftedCoefficient]
  · rw [norm_mrMellinShiftedCoefficient_eq a rho t
      (Nat.pos_of_ne_zero hn),
      norm_mrMellinShiftedCoefficient_eq a rho u
        (Nat.pos_of_ne_zero hn)]

/-- At real part one, the Mellin coefficient is exactly the coefficient
convention used by `MRLemma14`. -/
theorem mrMellinShiftedCoefficient_one_eq
    (a : ℕ → ℂ) (t : ℝ) {n : ℕ} (hn : 0 < n) :
    mrMellinShiftedCoefficient a 1 t n =
      a n / (n : ℂ) * logarithmicPhase n (-t) := by
  unfold mrMellinShiftedCoefficient
  rw [if_neg hn.ne', div_eq_mul_inv, ← Complex.cpow_neg]
  have hweight :
      Complex.ofReal ((n : ℝ) ^ (-(1 : ℝ))) = (n : ℂ)⁻¹ := by
    rw [Real.rpow_neg_one, Complex.ofReal_inv,
      Complex.ofReal_natCast]
  rw [← ofReal_rpow_mul_logarithmicPhase_neg_eq_cpow_neg hn 1 t,
    hweight]
  ring

theorem mrMellinShiftedCoefficient_LSeriesSummable
    {a : ℕ → ℂ} {rho t delta u : ℝ}
    (hsum : LSeriesSummable a
      (((rho + delta : ℝ) : ℂ) +
        Complex.I * ((t + u : ℝ) : ℂ))) :
    LSeriesSummable (mrMellinShiftedCoefficient a rho t)
      ((delta : ℂ) + Complex.I * (u : ℂ)) := by
  apply hsum.congr
  intro n
  exact (LSeries_term_mrMellinShiftedCoefficient
    a rho t delta u n).symm

/-- At the Lemma-14 line `rho = 1`, every one-bounded coefficient has the
shifted absolute convergence needed by Perron for every `delta > 0`. -/
theorem mrMellinShiftedCoefficient_one_LSeriesSummable
    {a : ℕ → ℂ} (ha : ∀ n ≠ 0, ‖a n‖ ≤ 1)
    {delta t u : ℝ} (hdelta : 0 < delta) :
    LSeriesSummable (mrMellinShiftedCoefficient a 1 t)
      ((delta : ℂ) + Complex.I * (u : ℂ)) := by
  apply mrMellinShiftedCoefficient_LSeriesSummable
  apply LSeriesSummable_of_bounded_of_one_lt_re (m := 1) ha
  simp
  linarith

/-- The dyadic Mellin polynomial needed in Lemma 14. -/
def mrDyadicMellinPolynomial
    (a : ℕ → ℂ) (X : ℕ) (rho t : ℝ) : ℂ :=
  ∑ n ∈ Finset.Ioc X (2 * X), mrMellinShiftedCoefficient a rho t n

/-- Identification of the Mellin polynomial with the exact finite vertical
polynomial in `MRLemma14`. -/
theorem mrDyadicMellinPolynomial_one_eq_dyadicVerticalDirichletPolynomial
    (a : ℕ → ℂ) (X : ℕ) (t : ℝ) :
    mrDyadicMellinPolynomial a X 1 t =
      dyadicVerticalDirichletPolynomial (Finset.Ioc X (2 * X)) a X t := by
  have hsupport :
      dyadicRestrictedSupport (Finset.Ioc X (2 * X)) X =
        Finset.Ioc X (2 * X) := by
    simp [dyadicRestrictedSupport]
  unfold mrDyadicMellinPolynomial dyadicVerticalDirichletPolynomial
    logarithmicDirichletPolynomial
  rw [hsupport]
  apply Finset.sum_congr rfl
  intro n hn
  exact mrMellinShiftedCoefficient_one_eq a t
    (by have := (Finset.mem_Ioc.mp hn).1; omega)

/-- The two-endpoint Perron projection of the dyadic Mellin polynomial. -/
def mrDyadicPerronProjection
    (a : ℕ → ℂ) (X : ℕ) (rho t delta U : ℝ) : ℂ :=
  BoundedGaps.Maynard.dirichletPerronIntegral
      (mrMellinShiftedCoefficient a rho t) ((2 * X : ℕ) : ℝ) delta U -
    BoundedGaps.Maynard.dirichletPerronIntegral
      (mrMellinShiftedCoefficient a rho t) (X : ℝ) delta U

/-- The exact Perron error attached to the two endpoints and their
half-weight corrections. -/
def mrDyadicPerronProjectionError
    (a : ℕ → ℂ) (X : ℕ) (rho t delta U : ℝ) : ℝ :=
  let b := mrMellinShiftedCoefficient a rho t
  MRHalaszPerron.perronTruncationError b (2 * X) delta U +
    MRHalaszPerron.perronTruncationError b X delta U +
    (1 / 2 : ℝ) * (‖b (2 * X)‖ + ‖b X‖)

/-- Explicit two-endpoint Perron projection.  This is a norm estimate for
the difference, not a supremum replacement; consequently the integral on
the right still contains the translated rectangular product and can be
inserted into a vertical `L²` estimate. -/
theorem norm_mrDyadicMellinPolynomial_sub_perronProjection_le
    {a : ℕ → ℂ} {X : ℕ} {rho t delta U : ℝ}
    (hsum : LSeriesSummable (mrMellinShiftedCoefficient a rho t)
      (delta : ℂ))
    (hX : 0 < X) (hdelta : 0 < delta) (hdeltaUpper : delta ≤ 2)
    (hU : 0 < U) :
    ‖mrDyadicMellinPolynomial a X rho t -
        mrDyadicPerronProjection a X rho t delta U‖ ≤
      mrDyadicPerronProjectionError a X rho t delta U := by
  let b := mrMellinShiftedCoefficient a rho t
  let S2 := BoundedGaps.Maynard.dirichletPerronStarredSum b (2 * X)
  let S1 := BoundedGaps.Maynard.dirichletPerronStarredSum b X
  let J2 := BoundedGaps.Maynard.dirichletPerronIntegral b
    ((2 * X : ℕ) : ℝ) delta U
  let J1 := BoundedGaps.Maynard.dirichletPerronIntegral b (X : ℝ) delta U
  have h2X : 0 < 2 * X := by omega
  have hupper :=
    BoundedGaps.Maynard.norm_dirichletPerronStarredSum_sub_integral_le
      hsum h2X hdelta hdeltaUpper hU
  have hlower :=
    BoundedGaps.Maynard.norm_dirichletPerronStarredSum_sub_integral_le
      hsum hX hdelta hdeltaUpper hU
  have hidentity :
      mrDyadicMellinPolynomial a X rho t -
          mrDyadicPerronProjection a X rho t delta U =
        (S2 - J2) - (S1 - J1) +
          (1 / 2 : ℂ) * (b (2 * X) - b X) := by
    unfold mrDyadicMellinPolynomial mrDyadicPerronProjection
    rw [MRHalaszPerron.sum_Ioc_eq_starred_sub_starred_add_endpoints b hX]
    dsimp only [b, S2, S1, J2, J1]
    ring
  rw [hidentity]
  calc
    ‖(S2 - J2) - (S1 - J1) +
        (1 / 2 : ℂ) * (b (2 * X) - b X)‖ ≤
        ‖S2 - J2‖ + ‖S1 - J1‖ +
          (1 / 2 : ℝ) * (‖b (2 * X)‖ + ‖b X‖) := by
      calc
        _ ≤ ‖(S2 - J2) - (S1 - J1)‖ +
            ‖(1 / 2 : ℂ) * (b (2 * X) - b X)‖ := norm_add_le _ _
        _ ≤ (‖S2 - J2‖ + ‖S1 - J1‖) +
            (1 / 2 : ℝ) * (‖b (2 * X)‖ + ‖b X‖) := by
          gcongr
          · exact norm_sub_le _ _
          · rw [norm_mul]
            have hhalf : ‖(1 / 2 : ℂ)‖ = (1 / 2 : ℝ) := by norm_num
            rw [hhalf]
            exact mul_le_mul_of_nonneg_left (norm_sub_le _ _) (by norm_num)
        _ = _ := by ring
    _ ≤ mrDyadicPerronProjectionError a X rho t delta U := by
      unfold mrDyadicPerronProjectionError MRHalaszPerron.perronTruncationError
      dsimp only [b, S2, S1, J2, J1]
      exact add_le_add (add_le_add hupper hlower) le_rfl

/-- The explicit Perron error is uniform in the outer vertical height. -/
theorem mrDyadicPerronProjectionError_vertical_eq
    (a : ℕ → ℂ) (X : ℕ) (rho t u delta U : ℝ) :
    mrDyadicPerronProjectionError a X rho t delta U =
      mrDyadicPerronProjectionError a X rho u delta U := by
  have hnear (x : ℕ) :
      BoundedGaps.Maynard.dirichletPerronNearMass
          (mrMellinShiftedCoefficient a rho t) x U =
        BoundedGaps.Maynard.dirichletPerronNearMass
          (mrMellinShiftedCoefficient a rho u) x U := by
    unfold BoundedGaps.Maynard.dirichletPerronNearMass
    apply tsum_congr
    intro n
    rw [norm_mrMellinShiftedCoefficient_vertical_eq a rho t u n]
  have hmass :
      BoundedGaps.Maynard.dirichletPerronCoefficientMass
          (mrMellinShiftedCoefficient a rho t) delta =
        BoundedGaps.Maynard.dirichletPerronCoefficientMass
          (mrMellinShiftedCoefficient a rho u) delta := by
    unfold BoundedGaps.Maynard.dirichletPerronCoefficientMass
    apply tsum_congr
    intro n
    simp only [LSeries.norm_term_eq, Complex.ofReal_re]
    rw [norm_mrMellinShiftedCoefficient_vertical_eq a rho t u n]
  dsimp only [mrDyadicPerronProjectionError]
  unfold MRHalaszPerron.perronTruncationError
  rw [hnear (2 * X), hnear X, hmass,
    norm_mrMellinShiftedCoefficient_vertical_eq a rho t u (2 * X),
    norm_mrMellinShiftedCoefficient_vertical_eq a rho t u X]

/-! ## One-bounded common Ramaré coefficient -/

/-- For a one-bounded input, the zero-normalized complete common
coefficient remains in the closed unit disc. -/
theorem norm_mrRamareConvolutionCoefficient_le_one
    {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime)
    {f : ℕ → ℂ} (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    (n : ℕ) :
    ‖mrRamareConvolutionCoefficient P f n‖ ≤ 1 := by
  by_cases hn : n = 0
  · subst n
    simp [mrRamareConvolutionCoefficient]
  · rw [mrRamareConvolutionCoefficient, if_neg hn]
    exact norm_mrCommonRamareCoefficient_le_one hP hbound
      (Nat.pos_of_ne_zero hn)

/-- The `LSeries` inside the Perron projector is exactly the translated
prime/cofactor rectangle. -/
theorem LSeries_mrMellinShiftedRamareCoefficient_eq_product
    (I : ℕ × ℕ) {f : ℕ → ℂ}
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    {rho delta t u : ℝ} (hsigma : 1 < rho + delta) :
    LSeries
        (mrMellinShiftedCoefficient
          (mrRamareConvolutionCoefficient (primesInBlock I) f) rho t)
        ((delta : ℂ) + Complex.I * (u : ℂ)) =
      ramarePrimePerronFactorAt (rho + delta) I f (t + u) *
        mrCofactorLSeries (primesInBlock I) f
          (((rho + delta : ℝ) : ℂ) +
            Complex.I * ((t + u : ℝ) : ℂ)) := by
  rw [LSeries_mrMellinShiftedCoefficient]
  exact LSeries_mrRamareConvolutionCoefficient_eq_ramare_product
    I hbound hsigma

/-- The two Perron integrals with their `LSeries` integrands already
replaced by the translated prime/cofactor product. -/
def mrRamareDyadicPerronProductProjection
    (I : ℕ × ℕ) (f : ℕ → ℂ) (X : ℕ)
    (rho t delta U : ℝ) : ℂ :=
  let F : ℝ → ℂ := fun u ↦
    ramarePrimePerronFactorAt (rho + delta) I f (t + u) *
      mrCofactorLSeries (primesInBlock I) f
        (((rho + delta : ℝ) : ℂ) +
          Complex.I * ((t + u : ℝ) : ℂ))
  (((2 * Real.pi : ℝ) : ℂ)⁻¹) *
      (∫ u in -U..U,
        F u * (((2 * X : ℕ) : ℝ) : ℂ) ^
            ((delta : ℂ) + u * Complex.I) /
          ((delta : ℂ) + u * Complex.I)) -
    (((2 * Real.pi : ℝ) : ℂ)⁻¹) *
      (∫ u in -U..U,
        F u * ((X : ℝ) : ℂ) ^
            ((delta : ℂ) + u * Complex.I) /
          ((delta : ℂ) + u * Complex.I))

/-- The abstract Perron projector for the common Ramaré coefficient is
exactly the explicit translated prime/cofactor product projector. -/
theorem mrDyadicPerronProjection_ramare_eq_productProjection
    (I : ℕ × ℕ) {f : ℕ → ℂ}
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    (X : ℕ) {rho t delta U : ℝ} (hsigma : 1 < rho + delta) :
    mrDyadicPerronProjection
        (mrRamareConvolutionCoefficient (primesInBlock I) f)
        X rho t delta U =
      mrRamareDyadicPerronProductProjection I f X rho t delta U := by
  unfold mrDyadicPerronProjection mrRamareDyadicPerronProductProjection
    BoundedGaps.Maynard.dirichletPerronIntegral
  dsimp only
  apply congrArg₂ (fun x y : ℂ ↦ x - y)
  · apply congrArg (((((2 * Real.pi : ℝ) : ℂ)⁻¹) * ·))
    apply intervalIntegral.integral_congr
    intro u hu
    dsimp only
    rw [mul_comm (u : ℂ) Complex.I]
    rw [LSeries_mrMellinShiftedRamareCoefficient_eq_product
      I hbound hsigma]
  · apply congrArg (((((2 * Real.pi : ℝ) : ℂ)⁻¹) * ·))
    apply intervalIntegral.integral_congr
    intro u hu
    dsimp only
    rw [mul_comm (u : ℂ) Complex.I]
    rw [LSeries_mrMellinShiftedRamareCoefficient_eq_product
      I hbound hsigma]

/-- Final projector handoff: the dyadically restricted Mellin polynomial is
within the explicit, height-independent Perron error of an integral of the
translated prime/cofactor product. -/
theorem norm_mrDyadicMellinRamarePolynomial_sub_productProjection_le
    (I : ℕ × ℕ) {f : ℕ → ℂ}
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    {X : ℕ} {rho t delta U : ℝ}
    (hsum : LSeriesSummable
      (mrMellinShiftedCoefficient
        (mrRamareConvolutionCoefficient (primesInBlock I) f) rho t)
      (delta : ℂ))
    (hX : 0 < X) (hsigma : 1 < rho + delta)
    (hdelta : 0 < delta) (hdeltaUpper : delta ≤ 2) (hU : 0 < U) :
    ‖mrDyadicMellinPolynomial
          (mrRamareConvolutionCoefficient (primesInBlock I) f) X rho t -
        mrRamareDyadicPerronProductProjection I f X rho t delta U‖ ≤
      mrDyadicPerronProjectionError
        (mrRamareConvolutionCoefficient (primesInBlock I) f)
          X rho 0 delta U := by
  rw [← mrDyadicPerronProjection_ramare_eq_productProjection
    I hbound X hsigma]
  have hproj := norm_mrDyadicMellinPolynomial_sub_perronProjection_le
    hsum hX hdelta hdeltaUpper hU
  rw [mrDyadicPerronProjectionError_vertical_eq
    (mrRamareConvolutionCoefficient (primesInBlock I) f)
      X rho t 0 delta U] at hproj
  exact hproj

/-- Fully unconditional one-bounded form at the Lemma-14 line.  No
summability hypothesis remains: `delta > 0` supplies absolute convergence,
and the error is explicit and uniform in `t`. -/
theorem norm_mrDyadicMellinRamarePolynomial_one_sub_productProjection_le
    (I : ℕ × ℕ) {f : ℕ → ℂ}
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    {X : ℕ} {t delta U : ℝ}
    (hX : 0 < X) (hdelta : 0 < delta)
    (hdeltaUpper : delta ≤ 2) (hU : 0 < U) :
    ‖mrDyadicMellinPolynomial
          (mrRamareConvolutionCoefficient (primesInBlock I) f) X 1 t -
        mrRamareDyadicPerronProductProjection I f X 1 t delta U‖ ≤
      mrDyadicPerronProjectionError
        (mrRamareConvolutionCoefficient (primesInBlock I) f)
          X 1 0 delta U := by
  let a : ℕ → ℂ :=
    mrRamareConvolutionCoefficient (primesInBlock I) f
  have ha : ∀ n ≠ 0, ‖a n‖ ≤ 1 := by
    intro n hn
    dsimp only [a]
    exact norm_mrRamareConvolutionCoefficient_le_one
      (fun p hp ↦ (mem_primesInBlock.mp hp).1) hbound n
  have hsum : LSeriesSummable (mrMellinShiftedCoefficient a 1 t)
      (delta : ℂ) := by
    simpa using
      (mrMellinShiftedCoefficient_one_LSeriesSummable
        (a := a) ha (t := t) (u := 0) hdelta)
  have hproj := norm_mrDyadicMellinPolynomial_sub_perronProjection_le
    hsum hX hdelta hdeltaUpper hU
  have hsigma : 1 < (1 : ℝ) + delta := by linarith
  change ‖mrDyadicMellinPolynomial a X 1 t -
      mrRamareDyadicPerronProductProjection I f X 1 t delta U‖ ≤
    mrDyadicPerronProjectionError a X 1 0 delta U
  rw [← mrDyadicPerronProjection_ramare_eq_productProjection
    I hbound X hsigma]
  change ‖mrDyadicMellinPolynomial a X 1 t -
      mrDyadicPerronProjection a X 1 t delta U‖ ≤ _
  rw [← mrDyadicPerronProjectionError_vertical_eq
    a X 1 t 0 delta U]
  exact hproj

end

end Erdos67
