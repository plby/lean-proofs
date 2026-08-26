import ErdosProblems.Erdos67b.MRShiftedMaskSum
import ErdosProblems.Erdos67b.MRGSA10FixedHighTailoredVertical

/-!
# Common Mangoldt windows for the actual typical cofactor

The low factor is the exact denominator-weighted typical coefficient.
Positive-line convergence justifies its four-factor tailored L-series,
and the proved fixed-high window energies control its vertical integral.
This does not yet include the Perron kernel or the coefficient projection.
-/

open scoped BigOperators Classical LSeries.notation

namespace Erdos67b

open MRHalaszBands MRHalaszEuler EulerResidue EulerQuantitative

noncomputable section

def mrTypicalCofactorTailoredCoefficient {ι : Type*}
    (A : Finset ℕ) (J : Finset ι) (B : ι → Finset ℕ)
    (f : ℕ → ℂ) (hmul : IsMultiplicativeOnPositiveNat f)
    (y X : ℕ) (alpha beta : ℝ) : ArithmeticFunction ℂ :=
  gsA10TailoredCoefficient (mrTypicalCofactorLowArithmetic A J B f y)
    (gsA9HighArithmetic f y) (gsA9HighGeneralizedMangoldt hmul y) y X alpha beta

theorem mrLSeries_typicalCofactorTailored_eq_fourFactors {ι : Type*}
    (A : Finset ℕ) (J : Finset ι) (B : ι → Finset ℕ)
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    {y X : ℕ} (hX : 1 < X) {alpha beta t : ℝ}
    (hlogy : 6 ≤ Real.log (y : ℝ))
    (ha : alpha ≤ (Real.log (y : ℝ))⁻¹)
    (hb : beta ≤ (Real.log (y : ℝ))⁻¹) :
    let s := (((taoExponent X - alpha - 2 * beta : ℝ) : ℂ) + Complex.I * (t : ℂ))
    let W := gsA10LambdaWindow (gsA9HighGeneralizedMangoldt hmul y) y X
    LSeries (mrTypicalCofactorTailoredCoefficient A J B f hmul y X alpha beta) s =
      (LSeries (mrTypicalCofactorLowArithmetic A J B f y) s *
        LSeries (gsA9HighArithmetic f y) (halaszPoint X t)) *
      (LSeries W (((taoExponent X - 2 * beta : ℝ) : ℂ) + Complex.I * (t : ℂ)) *
        LSeries W (halaszPoint X t)) := by
  dsimp only
  let s : ℂ := (((taoExponent X - alpha - 2 * beta : ℝ) : ℂ) + Complex.I * (t : ℂ))
  have hc := one_lt_taoExponent hX
  have hinv : (Real.log (y : ℝ))⁻¹ ≤ 1 / 6 := by
    simpa only [one_div] using inv_anti₀ (by norm_num : (0 : ℝ) < 6) hlogy
  have hpos : 0 < s.re := by
    dsimp only [s]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
      Complex.I_im, Complex.ofReal_im, zero_mul, one_mul, sub_zero, add_zero]
    linarith
  have hshift : s + ((alpha + 2 * beta : ℝ) : ℂ) = halaszPoint X t := by
    dsimp only [s, halaszPoint]
    push_cast
    ring
  have hshift' : s + (alpha : ℂ) =
      (((taoExponent X - 2 * beta : ℝ) : ℂ) + Complex.I * (t : ℂ)) := by
    dsimp only [s]
    push_cast
    ring
  have hlow := mrTypicalCofactorLowArithmetic_LSeriesSummable_of_pos_re A J B hbound y hpos
  have hhigh : LSeriesSummable (gsA9HighArithmetic f y) (s + ((alpha + 2 * beta : ℝ) : ℂ)) := by
    rw [hshift]
    exact gsA9HighArithmetic_LSeriesSummable hbound y (by rw [halaszPoint_re]; exact hc)
  have hfour := LSeries_gsA10TailoredCoefficient
    (mrTypicalCofactorLowArithmetic A J B f y) (gsA9HighArithmetic f y)
    (gsA9HighGeneralizedMangoldt hmul y) y X alpha beta s hlow hhigh
  rw [hshift, hshift'] at hfour
  exact hfour

theorem mrContinuous_LSeries_typicalCofactorLow_vertical {ι : Type*}
    (A : Finset ℕ) (J : Finset ι) (B : ι → Finset ℕ)
    {f : ℕ → ℂ} (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    (y : ℕ) {sigma : ℝ} (hsigma : 0 < sigma) :
    Continuous (fun t : ℝ ↦ LSeries (mrTypicalCofactorLowArithmetic A J B f y)
      ((sigma : ℂ) + Complex.I * (t : ℂ))) := by
  have hsum := mrTypicalCofactorLowArithmetic_LSeriesSummable_of_pos_re A J B hbound y
    (s := ((sigma / 2 : ℝ) : ℂ)) (by simpa using half_pos hsigma)
  have habs : LSeries.abscissaOfAbsConv (mrTypicalCofactorLowArithmetic A J B f y) <
      (sigma : EReal) := by
    calc
      _ ≤ ((sigma / 2 : ℝ) : EReal) := by simpa using hsum.abscissaOfAbsConv_le
      _ < (sigma : EReal) := by exact_mod_cast (by linarith : sigma / 2 < sigma)
  have hline : Continuous (fun t : ℝ ↦ (sigma : ℂ) + Complex.I * (t : ℂ)) := by fun_prop
  exact (LSeries_differentiableOn (mrTypicalCofactorLowArithmetic A J B f y)).continuousOn.comp_continuous
    hline (fun _ ↦ by simpa using habs)

def mrTypicalCofactorFixedHighEnvelope (A : Finset ℕ) (N X : ℕ) : ℝ :=
  Real.exp (6 * gsA9WideSourceShiftConstant +
    Real.log (riemannZeta (taoExponent X : ℂ)).re +
    3 * primeQuadraticConstant + mrMaskProductSeries -
    Real.exp (-1) / 16 * ((N : ℝ) / 2) +
    Real.exp (-1) / 16 * mrSelectedPrimeReciprocalMass A X)

theorem mrExists_norm_intervalIntegral_typicalCofactorTailored_le :
    ∃ Cβ : ℝ, 1 ≤ Cβ ∧
      ∀ (A : Finset ℕ) (_hA : ∀ p ∈ A, p.Prime)
        (J : Finset ℕ) (B : ℕ → Finset ℕ) {N X y Q S : ℕ}
        (_hX : 1 < X) (_hy : 23 ≤ y)
        (_hJ : ∀ j ∈ J, 1 ≤ j) (_hB : ∀ j ∈ J, B j ⊆ primesUpTo X)
        (_hdisj : Set.PairwiseDisjoint (↑J : Set ℕ) B)
        (_hsmall : ∀ j ∈ J, ∀ p ∈ B j, Real.log (p : ℝ) ≤ Real.log (X : ℝ) / 16)
        (_hmass : ∀ j ∈ J, 2 * Real.log (j : ℝ) ≤ ∑ p ∈ B j, 1 / (p : ℝ))
        (_hAy : ∀ p ∈ A, p ≤ y) (_hBy : ∀ j ∈ J, ∀ p ∈ B j, p ≤ y)
        {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
        (_hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1) (_hnonpret : MRArchimedeanNonpretentious f N X)
        (_hQ : 3 ≤ Q) (_hQy : Q ≤ y) (_hS : 101 ≤ S)
        (_hlogCβ : Real.log Cβ ≤ 2 * (S - 100 : ℕ) / 99)
        {alpha beta T : ℝ} (_hlogy : 6 ≤ Real.log (y : ℝ))
        (_ha0 : 0 ≤ alpha) (_ha : alpha ≤ (Real.log (y : ℝ))⁻¹)
        (_hb0 : 0 ≤ beta) (_hb : beta ≤ (Real.log (y : ℝ))⁻¹)
        (_hT : 0 < T) (_hTX : T ≤ X),
        ‖∫ t in -T..T,
          LSeries (mrTypicalCofactorTailoredCoefficient A J B
            (gsDeletePrimeBand f gsA9SmallPrime)
            (gsDeletePrimeBand_isMultiplicativeOnPositiveNat hmul gsA9SmallPrime)
            y X alpha beta)
            (((taoExponent X - alpha - 2 * beta : ℝ) : ℂ) + Complex.I * (t : ℂ))‖ ≤
          mrTypicalCofactorFixedHighEnvelope A N X *
              (gsA10PrimeLambdaLeftEnergyBound Cβ Q S X y (2 * beta) T) ^ ((1 : ℝ) / 2) *
              (gsA10PrimeLambdaRightEnergyBound Cβ Q S y X T) ^ ((1 : ℝ) / 2) +
            2 * T * mrTypicalCofactorFixedHighEnvelope A N X *
              gsA10LambdaVerticalSplitError y X (taoExponent X - 2 * beta) (taoExponent X) := by
  obtain ⟨Cβ, hCβ, hvertical⟩ := exists_norm_intervalIntegral_mul_gsA10LambdaWindow_fixedHigh_pair_le
  refine ⟨Cβ, hCβ, ?_⟩
  intro A hA J B N X y Q S hX hy hJ hB hdisj hsmall hmass hAy hBy f hmul hbound hnonpret
    hQ hQy hS hlogCβ alpha beta T hlogy ha0 ha hb0 hb hT hTX
  let g := gsDeletePrimeBand f gsA9SmallPrime
  let hgmul := gsDeletePrimeBand_isMultiplicativeOnPositiveNat hmul gsA9SmallPrime
  have hgbound : ∀ n, 0 < n → ‖g n‖ ≤ 1 :=
    fun n hn ↦ norm_gsDeletePrimeBand_le_one hbound gsA9SmallPrime hn
  let sigma := taoExponent X - alpha - 2 * beta
  let F : ℝ → ℂ := fun t ↦
    LSeries (mrTypicalCofactorLowArithmetic A J B g y) ((sigma : ℂ) + Complex.I * (t : ℂ)) *
      LSeries (gsA9HighArithmetic g y) (halaszPoint X t)
  have hc := one_lt_taoExponent hX
  have hinv : (Real.log (y : ℝ))⁻¹ ≤ 1 / 6 := by
    simpa only [one_div] using inv_anti₀ (by norm_num : (0 : ℝ) < 6) hlogy
  have hsigma : 0 < sigma := by dsimp only [sigma]; linarith
  have hFcont : Continuous F :=
    (mrContinuous_LSeries_typicalCofactorLow_vertical A J B hgbound y hsigma).mul
      (continuous_LSeries_gsA9HighArithmetic_vertical hgbound y hc)
  have hFbound : ∀ t, |t| ≤ T → ‖F t‖ ≤ mrTypicalCofactorFixedHighEnvelope A N X := by
    intro t ht
    dsimp only [F]
    rw [LSeries_gsA9HighArithmetic, gsA9High_deleteSmallPrimes_eq f hy]
    exact mrNorm_sourceTypicalCofactorLow_mul_high_fixedHalasz_le A hA J B hX hy hJ hB
      hdisj hsmall hmass hAy hBy hmul hbound hnonpret hlogy ha0 ha hb0 hb (ht.trans hTX)
  have hraw := hvertical hgmul hgbound y X Q S beta T
    (mrTypicalCofactorFixedHighEnvelope A N X) F (by omega) hQ hQy hS hlogCβ hb0 hT
    (Real.exp_pos _).le hFcont hFbound
  have hid : (fun t : ℝ ↦ LSeries (mrTypicalCofactorTailoredCoefficient A J B g hgmul y X alpha beta)
      ((sigma : ℂ) + Complex.I * (t : ℂ))) =
      fun t ↦ F t *
        LSeries (gsA10LambdaWindow (gsA9HighGeneralizedMangoldt hgmul y) y X)
          (((taoExponent X - 2 * beta : ℝ) : ℂ) + Complex.I * (t : ℂ)) *
        LSeries (gsA10LambdaWindow (gsA9HighGeneralizedMangoldt hgmul y) y X)
          (halaszPoint X t) := by
    funext t
    have hfour := mrLSeries_typicalCofactorTailored_eq_fourFactors A J B hgmul hgbound hX hlogy ha hb (t := t)
    simpa only [F, sigma, mul_assoc] using hfour
  change ‖∫ t in -T..T, LSeries (mrTypicalCofactorTailoredCoefficient A J B g hgmul y X alpha beta)
    ((sigma : ℂ) + Complex.I * (t : ℂ))‖ ≤ _
  rw [hid]
  exact hraw

end

end Erdos67b
