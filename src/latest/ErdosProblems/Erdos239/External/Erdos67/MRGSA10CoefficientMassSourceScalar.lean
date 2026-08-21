import ErdosProblems.Erdos239.External.Erdos67.MRGSA10LambdaWindowMassOrdinary
import ErdosProblems.Erdos239.External.Erdos67.MRGSA9SourceRadiusWide
import ErdosProblems.Erdos239.External.Erdos67.MRGSA9SmallPrimeDeletion
import ErdosProblems.Erdos239.External.Erdos67.MRGSA9ZetaMajorant
import ErdosProblems.Erdos239.External.Erdos67.MRGSRiemannZetaUpper

/-!
# Source-line scalar bounds for the A.10 coefficient mass

The absolute Perron mass of the alternating low factor is majorized by the
positive low Euler series, while the common high factor is majorized by the
positive high Euler series.  The large-prime part of the low series is then
shifted to the fixed Tao line and recombined with the high series.  This
retains only one zeta pole, rather than paying separate `log y` and
`log X / log y` bounds.
-/

open scoped BigOperators LSeries.notation ComplexOrder

namespace Erdos67.MRHalaszBands

noncomputable section

open BoundedGaps.Maynard

private theorem one_multiplicative_sourceMass :
    IsMultiplicativeOnPositiveNat (fun _ : ℕ ↦ (1 : ℂ)) := by
  constructor <;> simp

private theorem one_bounded_sourceMass :
    ∀ n : ℕ, 0 < n → ‖(1 : ℂ)‖ ≤ 1 := by simp

/-- A coefficientwise positive majorant controls the complete absolute
Perron mass on a real line. -/
theorem dirichletPerronCoefficientMass_le_norm_LSeries_of_major
    {a b : ℕ → ℂ} {sigma : ℝ}
    (hsumA : LSeriesSummable a (sigma : ℂ))
    (hsumB : LSeriesSummable b (sigma : ℂ))
    (haNonneg : ∀ n, 0 ≤ a n)
    (hmajor : ∀ n, ‖b n‖ ≤ ‖a n‖) :
    dirichletPerronCoefficientMass b sigma ≤
      ‖LSeries a (sigma : ℂ)‖ := by
  have hterm (n : ℕ) :
      ‖LSeries.term a (sigma : ℂ) n‖ =
        (LSeries.term a (sigma : ℂ) n).re := by
    have hn := LSeries.term_nonneg (haNonneg n) sigma
    rw [Complex.nonneg_iff] at hn
    have heq : LSeries.term a (sigma : ℂ) n =
        ((LSeries.term a (sigma : ℂ) n).re : ℂ) := by
      apply Complex.ext
      · rfl
      · simpa using hn.2.symm
    calc
      ‖LSeries.term a (sigma : ℂ) n‖ =
          ‖((LSeries.term a (sigma : ℂ) n).re : ℂ)‖ := congrArg norm heq
      _ = (LSeries.term a (sigma : ℂ) n).re := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hn.1]
  have hmass :
      (∑' n : ℕ, ‖LSeries.term a (sigma : ℂ) n‖) =
        (LSeries a (sigma : ℂ)).re := by
    unfold LSeries
    rw [Complex.re_tsum hsumA]
    exact tsum_congr hterm
  have hpoint (n : ℕ) :
      ‖LSeries.term b (sigma : ℂ) n‖ ≤
        ‖LSeries.term a (sigma : ℂ) n‖ := by
    rw [LSeries.norm_term_eq, LSeries.norm_term_eq]
    split_ifs
    · exact le_rfl
    · exact div_le_div_of_nonneg_right (hmajor n) (by positivity)
  unfold dirichletPerronCoefficientMass
  calc
    (∑' n : ℕ, ‖LSeries.term b (sigma : ℂ) n‖) ≤
        ∑' n : ℕ, ‖LSeries.term a (sigma : ℂ) n‖ :=
      Summable.tsum_le_tsum hpoint hsumB.norm hsumA.norm
    _ = (LSeries a (sigma : ℂ)).re := hmass
    _ ≤ ‖LSeries a (sigma : ℂ)‖ := Complex.re_le_norm _

/-- The complete absolute mass of the alternating low coefficient is
majorized by the positive low Euler series on every positive line. -/
theorem dirichletPerronCoefficientMass_twoBlockAlternatingLow_le_positive
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    (P₁ P₂ : ℕ → Prop) [DecidablePred P₁] [DecidablePred P₂]
    {y : ℕ}
    (hQ₂ : ∀ p, (¬ P₁ p ∧ P₂ p) → p ≤ y)
    (hQ₃ : ∀ p, (¬ P₁ p ∧ ¬ P₂ p) → p ≤ y)
    {sigma : ℝ} (hsigma : 0 < sigma) :
    dirichletPerronCoefficientMass
        (gsA10TwoBlockAlternatingLow f P₁ P₂ y) sigma ≤
      ‖LSeries (gsA9Low (fun _ : ℕ ↦ (1 : ℂ)) y) (sigma : ℂ)‖ := by
  let a : ℕ → ℂ := gsA9Low (fun _ : ℕ ↦ (1 : ℂ)) y
  let b : ℕ → ℂ := gsA10TwoBlockAlternatingLow f P₁ P₂ y
  have hsumA : LSeriesSummable a (sigma : ℂ) :=
    primeBandCoefficient_LSeriesSummable_of_pos_re
      one_multiplicative_sourceMass one_bounded_sourceMass
      (fun p ↦ p ≤ y) y (fun _ hp ↦ hp) (by simpa using hsigma)
  have hsumB : LSeriesSummable b (sigma : ℂ) :=
    gsA10TwoBlockAlternatingLow_LSeriesSummable_of_pos_re
      hmul hbound P₁ P₂ y (by simpa using hsigma)
  have haNonneg : ∀ n, 0 ≤ a n := by
    intro n
    unfold a gsA9Low primeBandCoefficient
    split_ifs <;> simp
  have hmajor : ∀ n, ‖b n‖ ≤ ‖a n‖ := by
    intro n
    by_cases hn : n = 0
    · subst n
      simp [a, b, gsA10TwoBlockAlternatingLow, gsA9LowArithmetic,
        gsA9LowDeletionArithmetic, toArithmeticFunction, gsA9Low,
        primeBandCoefficient]
    · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
      by_cases hsupp : PrimeSupported (fun p ↦ p ≤ y) n
      · have hlow := norm_gsA10TwoBlockAlternatingLow_le_one
          hmul hbound P₁ P₂ y hQ₂ hQ₃ n hnpos
        simpa [a, b, gsA9Low, primeBandCoefficient, hsupp] using hlow
      · rw [show b n = 0 by
            exact gsA10TwoBlockAlternatingLow_eq_zero_of_not_lowSupported
              f P₁ P₂ y hn hsupp]
        simp
  simpa only [a, b] using
    dirichletPerronCoefficientMass_le_norm_LSeries_of_major
      hsumA hsumB haNonneg hmajor

/-- The complete absolute mass of the common high coefficient is
majorized by the corresponding positive high Euler series. -/
theorem dirichletPerronCoefficientMass_gsA9HighArithmetic_le_positive
    {f : ℕ → ℂ}
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    (y : ℕ) {sigma : ℝ} (hsigma : 1 < sigma) :
    dirichletPerronCoefficientMass (gsA9HighArithmetic f y) sigma ≤
      ‖LSeries (gsA9High (fun _ : ℕ ↦ (1 : ℂ)) y) (sigma : ℂ)‖ := by
  let a : ℕ → ℂ := gsA9High (fun _ : ℕ ↦ (1 : ℂ)) y
  let b : ℕ → ℂ := gsA9HighArithmetic f y
  have hsumA : LSeriesSummable a (sigma : ℂ) :=
    primeBandCoefficient_LSeriesSummable one_bounded_sourceMass
      (fun p ↦ ¬ p ≤ y) (by simpa using hsigma)
  have hsumB : LSeriesSummable b (sigma : ℂ) :=
    gsA9HighArithmetic_LSeriesSummable hbound y (by simpa using hsigma)
  have haNonneg : ∀ n, 0 ≤ a n := by
    intro n
    unfold a gsA9High primeBandCoefficient
    split_ifs <;> simp
  have hmajor : ∀ n, ‖b n‖ ≤ ‖a n‖ := by
    intro n
    by_cases hn : n = 0
    · subst n
      simp [a, b, gsA9HighArithmetic,
        gsA9High, primeBandCoefficient]
    · change ‖gsA9HighArithmetic f y n‖ ≤ ‖a n‖
      rw [gsA9HighArithmetic_apply_of_ne_zero f y hn]
      unfold a gsA9High primeBandCoefficient
      by_cases hsupp : PrimeSupported (fun p ↦ ¬ p ≤ y) n
      · rw [if_pos hsupp, if_pos hsupp, norm_one]
        exact hbound n (Nat.pos_of_ne_zero hn)
      · rw [if_neg hsupp, if_neg hsupp]
  simpa only [a, b] using
    dirichletPerronCoefficientMass_le_norm_LSeries_of_major
      hsumA hsumB haNonneg hmajor

/-- The fixed universal cost of moving the positive low Euler product from
the widened source line to the fixed high line. -/
def gsA10SourceCoefficientMassConstant : ℝ :=
  gsA9SmallPrimeEulerBound *
    Real.exp (6 * gsA9WideSourceShiftConstant)

theorem gsA10SourceCoefficientMassConstant_nonneg :
    0 ≤ gsA10SourceCoefficientMassConstant := by
  unfold gsA10SourceCoefficientMassConstant gsA9SmallPrimeEulerBound
  apply mul_nonneg
  · apply Finset.prod_nonneg
    intro p hp
    exact inv_nonneg.mpr (sub_nonneg.mpr (by
      have hpPrime := (Finset.mem_filter.mp hp).2
      exact Real.rpow_le_one_of_one_le_of_nonpos
        (by exact_mod_cast hpPrime.one_le)
        (by norm_num : (-(1 / 2 : ℝ)) ≤ 0)))
  · positivity

/-- Source-uniform absolute coefficient-mass recombination.  The two
positive majorants are joined before invoking the zeta bound, so only one
pole factor remains. -/
theorem mul_dirichletPerronCoefficientMass_twoBlockLow_high_le_source
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    (P₁ P₂ : ℕ → Prop) [DecidablePred P₁] [DecidablePred P₂]
    {y : ℕ} (hy : 23 ≤ y)
    (hQ₂ : ∀ p, (¬ P₁ p ∧ P₂ p) → p ≤ y)
    (hQ₃ : ∀ p, (¬ P₁ p ∧ ¬ P₂ p) → p ≤ y)
    {sigmaLow sigmaHigh : ℝ}
    (hhalf : 1 / 2 ≤ sigmaLow)
    (hhigh : 1 < sigmaHigh)
    (hle : sigmaLow ≤ sigmaHigh)
    (hwide : 1 - 3 / Real.log (y : ℝ) ≤ sigmaLow)
    (hgap : sigmaHigh - sigmaLow ≤ 3 / Real.log (y : ℝ)) :
    dirichletPerronCoefficientMass
        (gsA10TwoBlockAlternatingLow f P₁ P₂ y) sigmaLow *
      dirichletPerronCoefficientMass (gsA9HighArithmetic f y) sigmaHigh ≤
        gsA10SourceCoefficientMassConstant *
          (1 + (sigmaHigh - 1)⁻¹) := by
  let one : ℕ → ℂ := fun _ ↦ 1
  let oneDel : ℕ → ℂ := gsDeletePrimeBand one gsA9SmallPrime
  let S : Finset ℕ := gsA9LargePrimesUpTo y
  let Low : ℕ → ℂ := gsA9Low one y
  let High : ℕ → ℂ := gsA9High one y
  have hy2 : 2 ≤ y := by omega
  have hsigmaLowPos : 0 < sigmaLow :=
    (by norm_num : (0 : ℝ) < 1 / 2).trans_le hhalf
  have hlowMass :=
    dirichletPerronCoefficientMass_twoBlockAlternatingLow_le_positive
      hmul hbound P₁ P₂ hQ₂ hQ₃ hsigmaLowPos
  have hhighMass :=
    dirichletPerronCoefficientMass_gsA9HighArithmetic_le_positive
      hbound y hhigh
  have hEulerLow :
      LSeries Low (sigmaLow : ℂ) =
        ∏ p ∈ primesUpTo y,
          gsA9LocalEulerFactor one (sigmaLow : ℂ) p := by
    simpa only [Low, one] using
      LSeries_gsA9Low_eq_finiteEulerProduct_of_pos_re
        one_multiplicative_sourceMass one_bounded_sourceMass y
          (by simpa using hsigmaLowPos)
  have hsmallSet :
      (primesUpTo y).filter (fun p ↦ p < 23) = gsA9SmallPrimeFinset := by
    ext p
    simp only [Finset.mem_filter, mem_primesUpTo, gsA9SmallPrimeFinset,
      Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨⟨hp, _⟩, hp23⟩
      exact ⟨hp23, hp⟩
    · rintro ⟨hp23, hp⟩
      exact ⟨⟨hp, hp23.le.trans hy⟩, hp23⟩
  have hlargeSet :
      (primesUpTo y).filter (fun p ↦ ¬ p < 23) = S := by
    ext p
    simp [S, gsA9LargePrimesUpTo]
  have hsplit :
      (∏ p ∈ gsA9SmallPrimeFinset,
          gsA9LocalEulerFactor one (sigmaLow : ℂ) p) *
        (∏ p ∈ S, gsA9LocalEulerFactor one (sigmaLow : ℂ) p) =
      ∏ p ∈ primesUpTo y,
        gsA9LocalEulerFactor one (sigmaLow : ℂ) p := by
    simpa only [hsmallSet, hlargeSet] using
      Finset.prod_filter_mul_prod_filter_not (primesUpTo y)
        (fun p ↦ p < 23)
        (fun p ↦ gsA9LocalEulerFactor one (sigmaLow : ℂ) p)
  have hsmall :
      ‖∏ p ∈ gsA9SmallPrimeFinset,
          gsA9LocalEulerFactor one (sigmaLow : ℂ) p‖ ≤
        gsA9SmallPrimeEulerBound := by
    simpa only [one, mul_zero, Complex.ofReal_zero, add_zero] using
      norm_prod_gsA9LocalEulerFactor_smallPrimes_le
        one_bounded_sourceMass (t := 0) hhalf
  have hSsub : S ⊆ primesUpTo y := by
    intro p hp
    exact (Finset.mem_filter.mp hp).1
  have hSprime : ∀ p ∈ S, p.Prime := by
    intro p hp
    exact (mem_primesUpTo.mp (hSsub hp)).1
  have hSlarge : ∀ p ∈ S, 23 ≤ p := by
    intro p hp
    exact (Finset.mem_filter.mp hp).2
  have hthird : ∀ p ∈ S,
      ‖(p : ℂ) ^ (-(sigmaLow : ℂ))‖ ≤ (1 / 3 : ℝ) := by
    intro p hp
    have h := norm_prime_cpow_le_one_third_of_twenty_three_le
      (hSprime p hp) (hSlarge p hp) (t := 0) hhalf
    simpa only [mul_zero, Complex.ofReal_zero, add_zero] using h
  let c : ℕ → ℝ := fun p ↦ (p : ℝ) ^ (sigmaHigh - sigmaLow)
  have hc : ∀ p ∈ S, 1 ≤ c p := by
    intro p hp
    exact Real.one_le_rpow (by exact_mod_cast (hSprime p hp).one_le)
      (sub_nonneg.mpr hle)
  have hfactor : ∀ p ∈ S,
      (p : ℂ) ^ (-(sigmaLow : ℂ)) =
        (c p : ℂ) * (p : ℂ) ^ (-(sigmaHigh : ℂ)) := by
    intro p hp
    have h := nat_cpow_neg_low_eq_rpow_gap_mul_neg_high
      (hSprime p hp) (t := 0) hle
    simpa only [mul_zero, Complex.ofReal_zero, add_zero, c] using h
  have hD :
      (∑ p ∈ S,
        (‖(p : ℂ) ^ (-(sigmaLow : ℂ))‖ -
          ‖(p : ℂ) ^ (-(sigmaHigh : ℂ))‖)) ≤
        gsA9WideSourceShiftConstant := by
    have h := sum_prime_radial_norm_sub_subset_wideSourceGap_le_constant
      hy2 S hSsub hle hwide hgap (t := 0)
    simpa only [mul_zero, Complex.ofReal_zero, add_zero] using h
  have hshift := norm_prod_gsA9LocalEulerFactor_shift_le_exp_sum_norm_sub
    one_multiplicative_sourceMass one_bounded_sourceMass S hSprime c hc
      hfactor hthird
  have hshift' :
      ‖∏ p ∈ S, gsA9LocalEulerFactor one (sigmaLow : ℂ) p‖ ≤
        ‖∏ p ∈ S, gsA9LocalEulerFactor one (sigmaHigh : ℂ) p‖ *
          Real.exp (6 * gsA9WideSourceShiftConstant) := by
    exact hshift.trans (mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hD (by norm_num)))
      (norm_nonneg _))
  have hlowPositive :
      ‖LSeries Low (sigmaLow : ℂ)‖ ≤
        gsA10SourceCoefficientMassConstant *
          ‖∏ p ∈ S,
            gsA9LocalEulerFactor one (sigmaHigh : ℂ) p‖ := by
    rw [hEulerLow, ← hsplit, norm_mul]
    unfold gsA10SourceCoefficientMassConstant
    calc
      _ ≤ gsA9SmallPrimeEulerBound *
          (‖∏ p ∈ S, gsA9LocalEulerFactor one (sigmaHigh : ℂ) p‖ *
            Real.exp (6 * gsA9WideSourceShiftConstant)) :=
        mul_le_mul hsmall hshift' (norm_nonneg _)
          (by
            unfold gsA9SmallPrimeEulerBound
            apply Finset.prod_nonneg
            intro p hp
            exact inv_nonneg.mpr (sub_nonneg.mpr (by
              have hpPrime := (Finset.mem_filter.mp hp).2
              exact Real.rpow_le_one_of_one_le_of_nonpos
                (by exact_mod_cast hpPrime.one_le)
                (by norm_num : (-(1 / 2 : ℝ)) ≤ 0))))
      _ = gsA9SmallPrimeEulerBound *
          Real.exp (6 * gsA9WideSourceShiftConstant) *
            ‖∏ p ∈ S,
              gsA9LocalEulerFactor one (sigmaHigh : ℂ) p‖ := by ring
  have honeDelBound : ∀ n, 0 < n → ‖oneDel n‖ ≤ 1 := by
    intro n hn
    exact norm_gsDeletePrimeBand_le_one one_bounded_sourceMass
      gsA9SmallPrime hn
  have hprodOne := prod_gsA9LocalEulerFactor_deleteSmallPrimes_eq
    one (sigmaHigh : ℂ) S hSprime hSlarge
  have hhighOne : gsA9High oneDel y = gsA9High one y := by
    exact gsA9High_deleteSmallPrimes_eq one hy
  have hrecombine :
      (∏ p ∈ S, gsA9LocalEulerFactor one (sigmaHigh : ℂ) p) *
        LSeries High (sigmaHigh : ℂ) =
      LSeries oneDel (sigmaHigh : ℂ) := by
    have h := prod_large_deleteSmallPrimes_mul_high_eq_LSeries
      one_multiplicative_sourceMass one_bounded_sourceMass y
        (s := (sigmaHigh : ℂ)) (by simpa using hhigh)
    simpa only [one, oneDel, S, High, hprodOne, hhighOne] using h
  have hzeta : ‖LSeries oneDel (sigmaHigh : ℂ)‖ ≤
      ‖riemannZeta (sigmaHigh : ℂ)‖ := by
    simpa only [oneDel, Complex.ofReal_zero, mul_zero, add_zero] using
      Erdos67.norm_LSeries_le_norm_riemannZeta_real_of_bounded
        honeDelBound hhigh (t := 0)
  have hzetaPole : ‖riemannZeta (sigmaHigh : ℂ)‖ ≤
      1 + (sigmaHigh - 1)⁻¹ := by
    have h := Erdos67.norm_riemannZeta_real_le_one_add_inv
      (show 0 < sigmaHigh - 1 by linarith)
    simpa [show 1 + (sigmaHigh - 1) = sigmaHigh by ring] using h
  have hlow0 : 0 ≤ dirichletPerronCoefficientMass
      (gsA10TwoBlockAlternatingLow f P₁ P₂ y) sigmaLow := by
    unfold dirichletPerronCoefficientMass
    positivity
  have hhigh0 : 0 ≤ dirichletPerronCoefficientMass
      (gsA9HighArithmetic f y) sigmaHigh := by
    unfold dirichletPerronCoefficientMass
    positivity
  calc
    dirichletPerronCoefficientMass
          (gsA10TwoBlockAlternatingLow f P₁ P₂ y) sigmaLow *
        dirichletPerronCoefficientMass (gsA9HighArithmetic f y) sigmaHigh ≤
      ‖LSeries Low (sigmaLow : ℂ)‖ *
        ‖LSeries High (sigmaHigh : ℂ)‖ :=
      mul_le_mul hlowMass hhighMass hhigh0 (norm_nonneg _)
    _ ≤ (gsA10SourceCoefficientMassConstant *
          ‖∏ p ∈ S,
            gsA9LocalEulerFactor one (sigmaHigh : ℂ) p‖) *
        ‖LSeries High (sigmaHigh : ℂ)‖ :=
      mul_le_mul_of_nonneg_right hlowPositive (norm_nonneg _)
    _ = gsA10SourceCoefficientMassConstant *
        ‖LSeries oneDel (sigmaHigh : ℂ)‖ := by
      rw [mul_assoc, ← norm_mul, hrecombine]
    _ ≤ gsA10SourceCoefficientMassConstant *
        ‖riemannZeta (sigmaHigh : ℂ)‖ :=
      mul_le_mul_of_nonneg_left hzeta gsA10SourceCoefficientMassConstant_nonneg
    _ ≤ gsA10SourceCoefficientMassConstant *
        (1 + (sigmaHigh - 1)⁻¹) :=
      mul_le_mul_of_nonneg_left hzetaPole gsA10SourceCoefficientMassConstant_nonneg

/-- The exact moving-Perron specialization: the low factor is at
`taoExponent X - alpha - 2 beta`, while the high factor stays on the fixed
Tao line. -/
theorem mul_dirichletPerronCoefficientMass_twoBlockLow_high_le_fixedTao
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    (P₁ P₂ : ℕ → Prop) [DecidablePred P₁] [DecidablePred P₂]
    {y X : ℕ} (hy : 23 ≤ y) (hX : 1 < X)
    (hQ₂ : ∀ p, (¬ P₁ p ∧ P₂ p) → p ≤ y)
    (hQ₃ : ∀ p, (¬ P₁ p ∧ ¬ P₂ p) → p ≤ y)
    {alpha beta : ℝ} (hlogy : 6 ≤ Real.log (y : ℝ))
    (halpha0 : 0 ≤ alpha)
    (halpha : alpha ≤ (Real.log (y : ℝ))⁻¹)
    (hbeta0 : 0 ≤ beta)
    (hbeta : beta ≤ (Real.log (y : ℝ))⁻¹) :
    let c := Erdos67.EulerResidue.taoExponent X
    dirichletPerronCoefficientMass
        (gsA10TwoBlockAlternatingLow f P₁ P₂ y)
        (c - alpha - 2 * beta) *
      dirichletPerronCoefficientMass (gsA9HighArithmetic f y) c ≤
        gsA10SourceCoefficientMassConstant *
          (1 + Real.log (X : ℝ)) := by
  dsimp only
  let c : ℝ := Erdos67.EulerResidue.taoExponent X
  let sigmaLow : ℝ := c - alpha - 2 * beta
  have hlogX : 0 < Real.log (X : ℝ) :=
    Real.log_pos (by exact_mod_cast hX)
  have hcOne : 1 ≤ c := by
    dsimp only [c, Erdos67.EulerResidue.taoExponent]
    exact le_add_of_nonneg_right (inv_pos.mpr hlogX).le
  have hcHigh : 1 < c := by
    dsimp only [c]
    exact Erdos67.EulerResidue.one_lt_taoExponent hX
  have hetaSixth : (Real.log (y : ℝ))⁻¹ ≤ 1 / 6 := by
    simpa only [one_div] using
      inv_anti₀ (by norm_num : (0 : ℝ) < 6) hlogy
  have hab : alpha + 2 * beta ≤
      3 * (Real.log (y : ℝ))⁻¹ := by linarith
  have hsigmaHalf : 1 / 2 ≤ sigmaLow := by
    dsimp only [sigmaLow]
    linarith
  have hsigmaWide : 1 - 3 / Real.log (y : ℝ) ≤ sigmaLow := by
    dsimp only [sigmaLow]
    rw [show 3 / Real.log (y : ℝ) =
      3 * (Real.log (y : ℝ))⁻¹ by field_simp]
    linarith
  have hle : sigmaLow ≤ c := by
    dsimp only [sigmaLow]
    linarith
  have hgap : c - sigmaLow ≤ 3 / Real.log (y : ℝ) := by
    dsimp only [sigmaLow]
    rw [show 3 / Real.log (y : ℝ) =
      3 * (Real.log (y : ℝ))⁻¹ by field_simp]
    linarith
  have hmass := mul_dirichletPerronCoefficientMass_twoBlockLow_high_le_source
    hmul hbound P₁ P₂ hy hQ₂ hQ₃ hsigmaHalf hcHigh hle hsigmaWide hgap
  have hcSub : c - 1 = (Real.log (X : ℝ))⁻¹ := by
    dsimp only [c, Erdos67.EulerResidue.taoExponent]
    ring
  have hcInv : (c - 1)⁻¹ = Real.log (X : ℝ) := by
    rw [hcSub, inv_inv]
  simpa only [sigmaLow, hcInv] using hmass

/-- Complete four-factor absolute mass for the ordinary-multiplicative
two-block tailored coefficient on the moving Perron line. -/
theorem dirichletPerronCoefficientMass_twoBlockTailored_fixedTao_le
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    (P₁ P₂ : ℕ → Prop) [DecidablePred P₁] [DecidablePred P₂]
    {y X : ℕ} (hy : 23 ≤ y) (hX : 1 < X)
    (hQ₂ : ∀ p, (¬ P₁ p ∧ P₂ p) → p ≤ y)
    (hQ₃ : ∀ p, (¬ P₁ p ∧ ¬ P₂ p) → p ≤ y)
    {alpha beta : ℝ} (hlogy : 6 ≤ Real.log (y : ℝ))
    (halpha0 : 0 ≤ alpha)
    (halpha : alpha ≤ (Real.log (y : ℝ))⁻¹)
    (hbeta0 : 0 ≤ beta)
    (hbeta : beta ≤ (Real.log (y : ℝ))⁻¹) :
    dirichletPerronCoefficientMass
        (gsA10TwoBlockTailoredCoefficient
          f hmul P₁ P₂ y X alpha beta)
        (Erdos67.EulerResidue.taoExponent X - alpha - 2 * beta) ≤
      (gsA10SourceCoefficientMassConstant *
        (1 + Real.log (X : ℝ))) *
      ((gsA10OrdinaryLambdaWindowMassBase y X) ^ 2 *
        (X : ℝ) ^
          (1 - min (Erdos67.EulerResidue.taoExponent X - 2 * beta) 1)) := by
  let c : ℝ := Erdos67.EulerResidue.taoExponent X
  let sigmaLow : ℝ := c - alpha - 2 * beta
  let low : ArithmeticFunction ℂ :=
    gsA10TwoBlockAlternatingLow f P₁ P₂ y
  let high : ArithmeticFunction ℂ := gsA9HighArithmetic f y
  have hX2 : 2 ≤ X := by omega
  have hlogX : 0 < Real.log (X : ℝ) :=
    Real.log_pos (by exact_mod_cast hX)
  have hcOne : 1 ≤ c := by
    dsimp only [c, Erdos67.EulerResidue.taoExponent]
    exact le_add_of_nonneg_right (inv_pos.mpr hlogX).le
  have hetaSixth : (Real.log (y : ℝ))⁻¹ ≤ 1 / 6 := by
    simpa only [one_div] using
      inv_anti₀ (by norm_num : (0 : ℝ) < 6) hlogy
  have hsigmaHalf : 1 / 2 ≤ sigmaLow := by
    dsimp only [sigmaLow]
    linarith
  have hsigmaPos : 0 < sigmaLow :=
    (by norm_num : (0 : ℝ) < 1 / 2).trans_le hsigmaHalf
  have hlowSum : LSeriesSummable low (sigmaLow : ℂ) := by
    exact gsA10TwoBlockAlternatingLow_LSeriesSummable_of_pos_re
      hmul hbound P₁ P₂ y (by simpa only [Complex.ofReal_re] using hsigmaPos)
  have hhighSum : LSeriesSummable high (c : ℂ) := by
    exact gsA9HighArithmetic_LSeriesSummable hbound y
      (by simpa only [Complex.ofReal_re] using
        (Erdos67.EulerResidue.one_lt_taoExponent hX))
  have hfour :=
    dirichletPerronCoefficientMass_gsA10Tailored_ordinary_fixedHigh_le
      hmul hbound low high hX2 hlogy hbeta0 hbeta hlowSum hhighSum
  have hfront :=
    mul_dirichletPerronCoefficientMass_twoBlockLow_high_le_fixedTao
      hmul hbound P₁ P₂ hy hX hQ₂ hQ₃ hlogy
        halpha0 halpha hbeta0 hbeta
  have hwindow0 : 0 ≤
      (gsA10OrdinaryLambdaWindowMassBase y X) ^ 2 *
        (X : ℝ) ^ (1 - min (c - 2 * beta) 1) := by positivity
  have hfour' :
      dirichletPerronCoefficientMass
          (gsA10TwoBlockTailoredCoefficient
            f hmul P₁ P₂ y X alpha beta) sigmaLow ≤
        (dirichletPerronCoefficientMass low sigmaLow *
          dirichletPerronCoefficientMass high c) *
        ((gsA10OrdinaryLambdaWindowMassBase y X) ^ 2 *
          (X : ℝ) ^ (1 - min (c - 2 * beta) 1)) := by
    simpa only [low, high, c, sigmaLow, gsA10TwoBlockTailoredCoefficient]
      using hfour
  exact hfour'.trans (mul_le_mul_of_nonneg_right
    (by simpa only [low, high, c, sigmaLow] using hfront) hwindow0)

end

end Erdos67.MRHalaszBands

#print axioms Erdos67.MRHalaszBands.dirichletPerronCoefficientMass_le_norm_LSeries_of_major
#print axioms Erdos67.MRHalaszBands.dirichletPerronCoefficientMass_twoBlockAlternatingLow_le_positive
#print axioms Erdos67.MRHalaszBands.dirichletPerronCoefficientMass_gsA9HighArithmetic_le_positive
#print axioms Erdos67.MRHalaszBands.mul_dirichletPerronCoefficientMass_twoBlockLow_high_le_fixedTao
#print axioms Erdos67.MRHalaszBands.dirichletPerronCoefficientMass_twoBlockTailored_fixedTao_le
