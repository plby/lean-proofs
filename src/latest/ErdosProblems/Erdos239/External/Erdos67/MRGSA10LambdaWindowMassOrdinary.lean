import ErdosProblems.Erdos239.External.Erdos67.MRGSA10CoefficientMassConvolution
import ErdosProblems.Erdos239.External.Erdos67.MRGSA10SecondSecondaryHigherPrimePower
import ErdosProblems.Erdos239.External.Erdos67.MRGSA10SecondSecondaryPrimeChebyshev

/-!
# Absolute A.10 Mangoldt-window mass for ordinary multiplicative functions

For an ordinary multiplicative coefficient the generalized Mangoldt
function need not be bounded by the classical von Mangoldt function at
higher prime powers.  We split it into its exact prime part and the
geometrically bounded higher-prime-power part.  This supplies the absolute
coefficient mass needed by the truncated Perron error without assuming
complete multiplicativity.
-/

open scoped BigOperators
open BoundedGaps.Maynard

namespace Erdos67.MRHalaszBands

noncomputable section

/-- The source-uniform coefficient controlling an ordinary generalized-
Mangoldt window on the real line one. -/
def gsA10OrdinaryLambdaWindowMassBase (y X : ℕ) : ℝ :=
  2 * (Real.log 4 + 4) * (Nat.log 2 X : ℝ) +
    gsA10HigherPrimePowerGeometricMass y X

theorem gsA10OrdinaryLambdaWindowMassBase_nonneg (y X : ℕ) :
    0 ≤ gsA10OrdinaryLambdaWindowMassBase y X := by
  unfold gsA10OrdinaryLambdaWindowMassBase
  apply add_nonneg
  · positivity
  · unfold gsA10HigherPrimePowerGeometricMass
    apply Finset.sum_nonneg
    intro p hp
    apply mul_nonneg
    · exact Real.log_nonneg (by
        have hpPrime := (mem_primesUpTo.mp (Finset.mem_filter.mp hp).1).1
        exact_mod_cast hpPrime.one_le)
    · apply Finset.sum_nonneg
      intro k hk
      exact div_nonneg (sub_nonneg.mpr (one_le_pow₀ (by norm_num)))
        (pow_nonneg (Nat.cast_nonneg _) _)

/-- At real part one, the finite actual-high Mangoldt window is bounded by
the classical prime contribution plus the explicit higher-prime-power
geometric mass. -/
theorem dirichletPerronCoefficientMass_gsA10LambdaWindow_ordinary_le_one
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    {y X : ℕ} (hX : 2 ≤ X) :
    dirichletPerronCoefficientMass
        (gsA10LambdaWindow (gsA9HighGeneralizedMangoldt hmul y) y X) 1 ≤
      gsA10OrdinaryLambdaWindowMassBase y X := by
  let lambda : ArithmeticFunction ℂ := gsA9HighGeneralizedMangoldt hmul y
  let prime : ArithmeticFunction ℂ := gsPrimePart lambda
  let hpp : ArithmeticFunction ℂ := gsHigherPrimePowerPart lambda
  let W : ArithmeticFunction ℂ := gsA10LambdaWindow lambda y X
  let major : ℕ → ℝ := fun n ↦ if n = 0 then 0 else
    ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-(1 : ℝ)) +
      ‖hpp n‖ / (n : ℝ)
  have hlambda : lambda = prime + hpp := by
    exact gsA9HighGeneralizedMangoldt_eq_primePart_add_higherPrimePowerPart
      hmul y
  have hsupport : ∀ n ∉ Finset.range (X / y),
      ‖LSeries.term W (1 : ℂ) n‖ = 0 := by
    intro n hn
    have hnUpper : X / y ≤ n := by
      simpa only [Finset.mem_range, not_lt] using hn
    by_cases hn0 : n = 0
    · subst n
      simp
    rw [LSeries.norm_term_eq, if_neg hn0,
      gsA10LambdaWindow_eq_zero_of_ge lambda y X hnUpper,
      norm_zero, zero_div]
  have hpoint : ∀ n ∈ Finset.range (X / y),
      ‖LSeries.term W (1 : ℂ) n‖ ≤ major n := by
    intro n hn
    by_cases hn0 : n = 0
    · subst n
      simp [major]
    have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
    rw [LSeries.norm_term_eq, if_neg hn0]
    rw [show ((1 : ℂ).re) = (1 : ℝ) by norm_num, Real.rpow_one]
    dsimp only [W]
    rw [gsA10LambdaWindow_apply]
    split_ifs with hwin
    · have hsum : lambda n = prime n + hpp n := by
        simpa only [ArithmeticFunction.add_apply] using
          DFunLike.congr_fun hlambda n
      rw [hsum]
      have hprime := norm_gsPrimePart_highGeneralizedMangoldt_le_vonMangoldt
        hmul hbound y n
      have hprime' : ‖prime n‖ ≤ ArithmeticFunction.vonMangoldt n := by
        simpa only [prime, lambda] using hprime
      dsimp only [major]
      rw [if_neg hn0]
      have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
      rw [Real.rpow_neg_one]
      calc
        ‖prime n + hpp n‖ / (n : ℝ) ≤
            (‖prime n‖ + ‖hpp n‖) / (n : ℝ) := by
          exact div_le_div_of_nonneg_right (norm_add_le _ _) hnR.le
        _ ≤ (ArithmeticFunction.vonMangoldt n + ‖hpp n‖) / (n : ℝ) := by
          exact div_le_div_of_nonneg_right
            (add_le_add hprime' le_rfl) hnR.le
        _ = ArithmeticFunction.vonMangoldt n * (n : ℝ)⁻¹ +
            ‖hpp n‖ / (n : ℝ) := by
          rw [add_div, div_eq_mul_inv]
    · dsimp only [major]
      rw [if_neg hn0, norm_zero, zero_div]
      exact add_nonneg
        (mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (by positivity))
        (div_nonneg (norm_nonneg _) (Nat.cast_nonneg _))
  have hrangeMajor : (∑ n ∈ Finset.range (X / y), major n) ≤
      ∑ n ∈ Finset.Icc 1 X,
        (ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-(1 : ℝ)) +
          ‖hpp n‖ / (n : ℝ)) := by
    rw [← Finset.sum_filter_of_ne (p := fun n : ℕ ↦ n ≠ 0) (by
      intro n hn hmajor
      by_contra hn0
      subst n
      simp [major] at hmajor)]
    have hfilterEq :
        (∑ n ∈ (Finset.range (X / y)).filter (fun n : ℕ ↦ n ≠ 0),
          major n) =
        ∑ n ∈ (Finset.range (X / y)).filter (fun n : ℕ ↦ n ≠ 0),
          (ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-(1 : ℝ)) +
            ‖hpp n‖ / (n : ℝ)) := by
      apply Finset.sum_congr rfl
      intro n hn
      have hn0 := (Finset.mem_filter.mp hn).2
      simp only [major, if_neg hn0]
    rw [hfilterEq]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro n hn
      have hnData := Finset.mem_filter.mp hn
      have hnlt : n < X / y := Finset.mem_range.mp hnData.1
      exact Finset.mem_Icc.mpr ⟨Nat.one_le_iff_ne_zero.mpr hnData.2,
        hnlt.le.trans (Nat.div_le_self X y)⟩
    · intro n hn hnot
      exact add_nonneg
        (mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (by positivity))
        (div_nonneg (norm_nonneg _) (Nat.cast_nonneg _))
  have hprimeMass :
      (∑ n ∈ Finset.Icc 1 X,
        ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-(1 : ℝ))) ≤
      2 * (Real.log 4 + 4) * (Nat.log 2 X : ℝ) := by
    have h := sum_vonMangoldt_mul_rpow_neg_le_one hX
      (show (0 : ℝ) ≤ 1 by norm_num) (le_refl 1)
    simpa only [sub_self, Real.rpow_zero, mul_one] using h
  have hhppMass :
      (∑ n ∈ Finset.Icc 1 X, ‖hpp n‖ / (n : ℝ)) ≤
        gsA10HigherPrimePowerGeometricMass y X := by
    have h := sum_norm_shift_higherPrimePowerPart_div_le_mass
      hmul hbound (y := y) (X := X) (alpha := 0) (le_refl 0)
    calc
      (∑ n ∈ Finset.Icc 1 X, ‖hpp n‖ / (n : ℝ)) =
          ∑ n ∈ Finset.Icc 1 X,
            ‖gsRealShift 0 hpp n‖ / (n : ℝ) := by
        apply Finset.sum_congr rfl
        intro n hn
        have hn0 : n ≠ 0 := Nat.ne_of_gt (Finset.mem_Icc.mp hn).1
        rw [gsRealShift_apply_of_ne_zero 0 hpp hn0]
        simp
      _ ≤ gsA10HigherPrimePowerGeometricMass y X := by
        simpa only [hpp, lambda] using h
  unfold dirichletPerronCoefficientMass
  change (∑' n : ℕ, ‖LSeries.term W (1 : ℂ) n‖) ≤
    gsA10OrdinaryLambdaWindowMassBase y X
  rw [tsum_eq_sum hsupport]
  calc
    (∑ n ∈ Finset.range (X / y), ‖LSeries.term W (1 : ℂ) n‖) ≤
        ∑ n ∈ Finset.range (X / y), major n :=
      Finset.sum_le_sum hpoint
    _ ≤ ∑ n ∈ Finset.Icc 1 X,
        (ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-(1 : ℝ)) +
          ‖hpp n‖ / (n : ℝ)) := hrangeMajor
    _ = (∑ n ∈ Finset.Icc 1 X,
          ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-(1 : ℝ))) +
        ∑ n ∈ Finset.Icc 1 X, ‖hpp n‖ / (n : ℝ) := by
      rw [Finset.sum_add_distrib]
    _ ≤ 2 * (Real.log 4 + 4) * (Nat.log 2 X : ℝ) +
        gsA10HigherPrimePowerGeometricMass y X :=
      add_le_add hprimeMass hhppMass
    _ = gsA10OrdinaryLambdaWindowMassBase y X := rfl

/-- Moving a finite Mangoldt window left of the line one costs only the
largest support scale to the corresponding exponent. -/
theorem dirichletPerronCoefficientMass_gsA10LambdaWindow_le_rpow_mul_one
    (lambda : ArithmeticFunction ℂ) {y X : ℕ}
    {sigma : ℝ} (hsigma : 0 ≤ sigma) :
    dirichletPerronCoefficientMass (gsA10LambdaWindow lambda y X) sigma ≤
      (X : ℝ) ^ (1 - min sigma 1) *
        dirichletPerronCoefficientMass
          (gsA10LambdaWindow lambda y X) 1 := by
  let W : ArithmeticFunction ℂ := gsA10LambdaWindow lambda y X
  let rho : ℝ := min sigma 1
  have hrho0 : 0 ≤ rho := le_min hsigma (by norm_num)
  have hrhoOne : rho ≤ 1 := min_le_right _ _
  have hrhoSigma : rho ≤ sigma := min_le_left _ _
  have hanti : dirichletPerronCoefficientMass W sigma ≤
      dirichletPerronCoefficientMass W rho := by
    exact dirichletPerronCoefficientMass_gsA10LambdaWindow_anti
      lambda y X hrhoSigma
  have hsupport (tau : ℝ) : ∀ n ∉ Finset.range (X / y),
      ‖LSeries.term W (tau : ℂ) n‖ = 0 := by
    intro n hn
    have hnUpper : X / y ≤ n := by
      simpa only [Finset.mem_range, not_lt] using hn
    by_cases hn0 : n = 0
    · subst n
      simp
    rw [LSeries.norm_term_eq, if_neg hn0,
      gsA10LambdaWindow_eq_zero_of_ge lambda y X hnUpper,
      norm_zero, zero_div]
  have hpoint : ∀ n ∈ Finset.range (X / y),
      ‖LSeries.term W (rho : ℂ) n‖ ≤
        (X : ℝ) ^ (1 - rho) * ‖LSeries.term W (1 : ℂ) n‖ := by
    intro n hn
    by_cases hn0 : n = 0
    · subst n
      simp
    have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
    have hnle : n ≤ X :=
      (Finset.mem_range.mp hn).le.trans (Nat.div_le_self X y)
    have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
    have hnX : (n : ℝ) ≤ X := by exact_mod_cast hnle
    have hexp0 : 0 ≤ 1 - rho := by linarith
    have hpow : (n : ℝ) ^ (1 - rho) ≤ (X : ℝ) ^ (1 - rho) :=
      Real.rpow_le_rpow hnR.le hnX hexp0
    rw [LSeries.norm_term_eq, LSeries.norm_term_eq,
      if_neg hn0, if_neg hn0]
    change ‖W n‖ / (n : ℝ) ^ rho ≤
      (X : ℝ) ^ (1 - rho) * (‖W n‖ / (n : ℝ) ^ (1 : ℝ))
    have hidentity : ‖W n‖ / (n : ℝ) ^ rho =
        (n : ℝ) ^ (1 - rho) * (‖W n‖ / (n : ℝ) ^ (1 : ℝ)) := by
      rw [Real.rpow_one, div_eq_mul_inv, div_eq_mul_inv]
      rw [← Real.rpow_neg hnR.le rho, ← Real.rpow_neg_one]
      calc
        ‖W n‖ * (n : ℝ) ^ (-rho) =
            ‖W n‖ * (n : ℝ) ^ ((1 - rho) + (-1)) := by
          congr 2
          ring
        _ = ‖W n‖ *
            ((n : ℝ) ^ (1 - rho) * (n : ℝ) ^ (-(1 : ℝ))) := by
          rw [Real.rpow_add hnR]
        _ = (n : ℝ) ^ (1 - rho) *
            (‖W n‖ * (n : ℝ) ^ (-(1 : ℝ))) := by ring
    rw [hidentity]
    exact mul_le_mul_of_nonneg_right hpow
      (div_nonneg (norm_nonneg _) (Real.rpow_nonneg hnR.le _))
  have hrhoBound : dirichletPerronCoefficientMass W rho ≤
      (X : ℝ) ^ (1 - rho) * dirichletPerronCoefficientMass W 1 := by
    unfold dirichletPerronCoefficientMass
    rw [tsum_eq_sum (hsupport rho), tsum_eq_sum (hsupport 1),
      Finset.mul_sum]
    exact Finset.sum_le_sum hpoint
  exact hanti.trans (by simpa only [W, rho] using hrhoBound)

/-- Ordinary-multiplicative source-line bound for one finite generalized-
Mangoldt window. -/
theorem dirichletPerronCoefficientMass_gsA10LambdaWindow_ordinary_le
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    {y X : ℕ} (hX : 2 ≤ X) {sigma : ℝ} (hsigma : 0 ≤ sigma) :
    dirichletPerronCoefficientMass
        (gsA10LambdaWindow (gsA9HighGeneralizedMangoldt hmul y) y X)
        sigma ≤
      (X : ℝ) ^ (1 - min sigma 1) *
        gsA10OrdinaryLambdaWindowMassBase y X := by
  have hmove :=
    dirichletPerronCoefficientMass_gsA10LambdaWindow_le_rpow_mul_one
      (gsA9HighGeneralizedMangoldt hmul y) (y := y) (X := X)
      hsigma
  have hone :=
    dirichletPerronCoefficientMass_gsA10LambdaWindow_ordinary_le_one
      hmul hbound (y := y) (X := X) hX
  exact hmove.trans (mul_le_mul_of_nonneg_left hone (by positivity))

/-- Joint ordinary-multiplicative bound for the two finite Mangoldt windows
on the actual A.10 source lines. -/
theorem mul_dirichletPerronCoefficientMass_gsA10LambdaWindow_ordinary_sourceLines_le
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    {y X : ℕ} (hX : 2 ≤ X)
    (hlogy : 4 ≤ Real.log (y : ℝ))
    {beta : ℝ} (hbeta0 : 0 ≤ beta)
    (hbeta : beta ≤ (Real.log (y : ℝ))⁻¹) :
    let c := Erdos67.EulerResidue.taoExponent X
    let W := gsA10LambdaWindow (gsA9HighGeneralizedMangoldt hmul y) y X
    dirichletPerronCoefficientMass W (c - beta) *
        dirichletPerronCoefficientMass W (c + beta) ≤
      (gsA10OrdinaryLambdaWindowMassBase y X) ^ 2 *
        (X : ℝ) ^ (1 - min (c - beta) 1) := by
  dsimp only
  let c : ℝ := Erdos67.EulerResidue.taoExponent X
  let W : ArithmeticFunction ℂ :=
    gsA10LambdaWindow (gsA9HighGeneralizedMangoldt hmul y) y X
  let B : ℝ := gsA10OrdinaryLambdaWindowMassBase y X
  have hlogX : 0 < Real.log (X : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < X by omega))
  have hcOne : 1 ≤ c := by
    dsimp only [c, Erdos67.EulerResidue.taoExponent]
    exact le_add_of_nonneg_right (inv_pos.mpr hlogX).le
  have hetaQuarter : (Real.log (y : ℝ))⁻¹ ≤ 1 / 4 := by
    simpa only [one_div] using
      inv_anti₀ (by norm_num : (0 : ℝ) < 4) hlogy
  have hlow0 : 0 ≤ c - beta := by linarith
  have hhighOne : 1 ≤ c + beta := by linarith
  have hlow :=
    dirichletPerronCoefficientMass_gsA10LambdaWindow_ordinary_le
      hmul hbound (y := y) (X := X) hX hlow0
  have hhigh :=
    dirichletPerronCoefficientMass_gsA10LambdaWindow_ordinary_le
      hmul hbound (y := y) (X := X) hX
        (show 0 ≤ c + beta by linarith)
  have hminHigh : min (c + beta) 1 = 1 := min_eq_right hhighOne
  have hhigh' : dirichletPerronCoefficientMass W (c + beta) ≤ B := by
    simpa only [W, B, hminHigh, sub_self, Real.rpow_zero, one_mul] using hhigh
  have hlow' : dirichletPerronCoefficientMass W (c - beta) ≤
      (X : ℝ) ^ (1 - min (c - beta) 1) * B := by
    simpa only [W, B] using hlow
  have hmassHigh0 : 0 ≤ dirichletPerronCoefficientMass W (c + beta) := by
    unfold dirichletPerronCoefficientMass
    positivity
  have hright0 : 0 ≤ (X : ℝ) ^ (1 - min (c - beta) 1) * B :=
    mul_nonneg (by positivity) (gsA10OrdinaryLambdaWindowMassBase_nonneg y X)
  calc
    dirichletPerronCoefficientMass W (c - beta) *
        dirichletPerronCoefficientMass W (c + beta) ≤
      ((X : ℝ) ^ (1 - min (c - beta) 1) * B) * B :=
      mul_le_mul hlow' hhigh' hmassHigh0 hright0
    _ = B ^ 2 * (X : ℝ) ^ (1 - min (c - beta) 1) := by ring

/-- The tailored four-factor mass with the ordinary two-window contribution
already replaced by its source-line scalar. -/
theorem dirichletPerronCoefficientMass_gsA10Tailored_ordinary_sourceLines_le
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    (low high : ArithmeticFunction ℂ)
    {y X : ℕ} (hX : 2 ≤ X)
    (hlogy : 4 ≤ Real.log (y : ℝ))
    {alpha beta : ℝ} (hbeta0 : 0 ≤ beta)
    (hbeta : beta ≤ (Real.log (y : ℝ))⁻¹)
    (hlow : LSeriesSummable low
      ((Erdos67.EulerResidue.taoExponent X - alpha - beta : ℝ) : ℂ))
    (hhigh : LSeriesSummable high
      ((Erdos67.EulerResidue.taoExponent X + beta : ℝ) : ℂ)) :
    dirichletPerronCoefficientMass
        (gsA10TailoredCoefficient low high
          (gsA9HighGeneralizedMangoldt hmul y) y X alpha beta)
        (Erdos67.EulerResidue.taoExponent X - alpha - beta) ≤
      (dirichletPerronCoefficientMass low
          (Erdos67.EulerResidue.taoExponent X - alpha - beta) *
        dirichletPerronCoefficientMass high
          (Erdos67.EulerResidue.taoExponent X + beta)) *
      ((gsA10OrdinaryLambdaWindowMassBase y X) ^ 2 *
        (X : ℝ) ^
          (1 - min (Erdos67.EulerResidue.taoExponent X - beta) 1)) := by
  let c : ℝ := Erdos67.EulerResidue.taoExponent X
  let lambda : ArithmeticFunction ℂ := gsA9HighGeneralizedMangoldt hmul y
  let W : ArithmeticFunction ℂ := gsA10LambdaWindow lambda y X
  have hfour :=
    dirichletPerronCoefficientMass_gsA10TailoredCoefficient_sourceLines_le
      low high lambda y X c alpha beta hlow hhigh
  have hwindow :=
    mul_dirichletPerronCoefficientMass_gsA10LambdaWindow_ordinary_sourceLines_le
      hmul hbound hX hlogy hbeta0 hbeta
  have hfront0 : 0 ≤ dirichletPerronCoefficientMass low
      (c - alpha - beta) * dirichletPerronCoefficientMass high (c + beta) := by
    apply mul_nonneg <;> unfold dirichletPerronCoefficientMass <;> positivity
  exact hfour.trans (mul_le_mul_of_nonneg_left
    (by simpa only [c, lambda, W] using hwindow) hfront0)

/-- Joint ordinary window mass on the beta-dependent Perron line used to
keep the high factor at the fixed Halasz point. -/
theorem mul_dirichletPerronCoefficientMass_gsA10LambdaWindow_ordinary_fixedHigh_le
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    {y X : ℕ} (hX : 2 ≤ X)
    (hlogy : 6 ≤ Real.log (y : ℝ))
    {beta : ℝ} (_hbeta0 : 0 ≤ beta)
    (hbeta : beta ≤ (Real.log (y : ℝ))⁻¹) :
    let c := Erdos67.EulerResidue.taoExponent X
    let W := gsA10LambdaWindow (gsA9HighGeneralizedMangoldt hmul y) y X
    dirichletPerronCoefficientMass W (c - 2 * beta) *
        dirichletPerronCoefficientMass W c ≤
      (gsA10OrdinaryLambdaWindowMassBase y X) ^ 2 *
        (X : ℝ) ^ (1 - min (c - 2 * beta) 1) := by
  dsimp only
  let c : ℝ := Erdos67.EulerResidue.taoExponent X
  let W : ArithmeticFunction ℂ :=
    gsA10LambdaWindow (gsA9HighGeneralizedMangoldt hmul y) y X
  let B : ℝ := gsA10OrdinaryLambdaWindowMassBase y X
  have hlogX : 0 < Real.log (X : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < X by omega))
  have hcOne : 1 ≤ c := by
    dsimp only [c, Erdos67.EulerResidue.taoExponent]
    exact le_add_of_nonneg_right (inv_pos.mpr hlogX).le
  have hetaSixth : (Real.log (y : ℝ))⁻¹ ≤ 1 / 6 := by
    simpa only [one_div] using
      inv_anti₀ (by norm_num : (0 : ℝ) < 6) hlogy
  have hlow0 : 0 ≤ c - 2 * beta := by linarith
  have hlow :=
    dirichletPerronCoefficientMass_gsA10LambdaWindow_ordinary_le
      hmul hbound (y := y) (X := X) hX hlow0
  have hhigh :=
    dirichletPerronCoefficientMass_gsA10LambdaWindow_ordinary_le
      hmul hbound (y := y) (X := X) hX (show 0 ≤ c by linarith)
  have hminHigh : min c 1 = 1 := min_eq_right hcOne
  have hhigh' : dirichletPerronCoefficientMass W c ≤ B := by
    simpa only [W, B, hminHigh, sub_self, Real.rpow_zero, one_mul] using hhigh
  have hlow' : dirichletPerronCoefficientMass W (c - 2 * beta) ≤
      (X : ℝ) ^ (1 - min (c - 2 * beta) 1) * B := by
    simpa only [W, B] using hlow
  have hmassHigh0 : 0 ≤ dirichletPerronCoefficientMass W c := by
    unfold dirichletPerronCoefficientMass
    positivity
  have hright0 : 0 ≤ (X : ℝ) ^ (1 - min (c - 2 * beta) 1) * B :=
    mul_nonneg (by positivity) (gsA10OrdinaryLambdaWindowMassBase_nonneg y X)
  calc
    dirichletPerronCoefficientMass W (c - 2 * beta) *
        dirichletPerronCoefficientMass W c ≤
      ((X : ℝ) ^ (1 - min (c - 2 * beta) 1) * B) * B :=
      mul_le_mul hlow' hhigh' hmassHigh0 hright0
    _ = B ^ 2 * (X : ℝ) ^ (1 - min (c - 2 * beta) 1) := by ring

/-- Four-factor Perron mass on the fixed-Halasz beta-dependent line. -/
theorem dirichletPerronCoefficientMass_gsA10Tailored_ordinary_fixedHigh_le
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    (low high : ArithmeticFunction ℂ)
    {y X : ℕ} (hX : 2 ≤ X)
    (hlogy : 6 ≤ Real.log (y : ℝ))
    {alpha beta : ℝ} (hbeta0 : 0 ≤ beta)
    (hbeta : beta ≤ (Real.log (y : ℝ))⁻¹)
    (hlow : LSeriesSummable low
      ((Erdos67.EulerResidue.taoExponent X - alpha - 2 * beta : ℝ) : ℂ))
    (hhigh : LSeriesSummable high
      (Erdos67.EulerResidue.taoExponent X : ℂ)) :
    dirichletPerronCoefficientMass
        (gsA10TailoredCoefficient low high
          (gsA9HighGeneralizedMangoldt hmul y) y X alpha beta)
        (Erdos67.EulerResidue.taoExponent X - alpha - 2 * beta) ≤
      (dirichletPerronCoefficientMass low
          (Erdos67.EulerResidue.taoExponent X - alpha - 2 * beta) *
        dirichletPerronCoefficientMass high
          (Erdos67.EulerResidue.taoExponent X)) *
      ((gsA10OrdinaryLambdaWindowMassBase y X) ^ 2 *
        (X : ℝ) ^
          (1 - min (Erdos67.EulerResidue.taoExponent X - 2 * beta) 1)) := by
  let c : ℝ := Erdos67.EulerResidue.taoExponent X
  let lambda : ArithmeticFunction ℂ := gsA9HighGeneralizedMangoldt hmul y
  let W : ArithmeticFunction ℂ := gsA10LambdaWindow lambda y X
  have hfour :=
    dirichletPerronCoefficientMass_gsA10TailoredCoefficient_le
      low high lambda y X alpha beta (c - alpha - 2 * beta)
      hlow (by
        have hline : (c - alpha - 2 * beta) + alpha + 2 * beta = c := by ring
        simpa only [hline] using hhigh)
  have hlineHigh : (c - alpha - 2 * beta) + alpha + 2 * beta = c := by ring
  have hlineLow : (c - alpha - 2 * beta) + alpha = c - 2 * beta := by ring
  have hlineAfter : c - 2 * beta + 2 * beta = c := by ring
  have hfour' : dirichletPerronCoefficientMass
        (gsA10TailoredCoefficient low high lambda y X alpha beta)
        (c - alpha - 2 * beta) ≤
      (dirichletPerronCoefficientMass low (c - alpha - 2 * beta) *
        dirichletPerronCoefficientMass high c) *
      (dirichletPerronCoefficientMass W (c - 2 * beta) *
        dirichletPerronCoefficientMass W c) := by
    simpa only [W, hlineHigh, hlineLow, hlineAfter] using hfour
  have hwindow :=
    mul_dirichletPerronCoefficientMass_gsA10LambdaWindow_ordinary_fixedHigh_le
      hmul hbound hX hlogy hbeta0 hbeta
  have hfront0 : 0 ≤ dirichletPerronCoefficientMass low
      (c - alpha - 2 * beta) * dirichletPerronCoefficientMass high c := by
    apply mul_nonneg <;> unfold dirichletPerronCoefficientMass <;> positivity
  exact hfour'.trans (mul_le_mul_of_nonneg_left
    (by simpa only [c, lambda, W] using hwindow) hfront0)

end

end Erdos67.MRHalaszBands
