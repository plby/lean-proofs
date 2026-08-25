import ErdosProblems.Erdos67.MRGSA10SourcePrimeVerticalContour
import ErdosProblems.Erdos67.MRGSA10SourceMaximumModulus
import ErdosProblems.Erdos67.MRGSA10SymmetricVerticalScalar
import ErdosProblems.Erdos67.MRGSA10PrimeLambdaBetaDiagonalScalar

/-!
# Full source-line vertical contour after maximum modulus

This module keeps the genuine lines `c₀-beta` and `c₀+beta`.  It combines
the ordinary symmetric prime energies with the explicit higher-prime-power
split.  The common factor `((X / y) : ℝ)^beta` is retained in both terms.
-/

open scoped LSeries.notation
open Complex MeasureTheory Set

namespace Erdos67.MRHalaszBands

noncomputable section

/-- Ordinary vertical Cauchy--Schwarz, in the scalar form needed after the
maximum-modulus estimate has absorbed the Perron denominator. -/
theorem intervalIntegral_norm_mul_le_rpow_half_normSq
    (A B : ℝ → ℂ) (hA : Continuous A) (hB : Continuous B)
    {T : ℝ} (hT : 0 ≤ T) :
    (∫ t in -T..T, ‖A t * B t‖) ≤
      (∫ t in -T..T, Complex.normSq (A t)) ^ ((1 : ℝ) / 2) *
        (∫ t in -T..T, Complex.normSq (B t)) ^ ((1 : ℝ) / 2) := by
  let S : Set ℝ := Set.Ioc (-T) T
  let u : ℝ → ℝ := fun t ↦ ‖A t‖
  let v : ℝ → ℝ := fun t ↦ ‖B t‖
  have hu : Continuous u := hA.norm
  have hv : Continuous v := hB.norm
  have huLp : MemLp u 2 (volume.restrict S) := by
    apply (memLp_two_iff_integrable_sq hu.aestronglyMeasurable).2
    exact (hu.pow 2).integrableOn_Ioc
  have hvLp : MemLp v 2 (volume.restrict S) := by
    apply (memLp_two_iff_integrable_sq hv.aestronglyMeasurable).2
    exact (hv.pow 2).integrableOn_Ioc
  have huLp' : MemLp u (ENNReal.ofReal (2 : ℝ)) (volume.restrict S) := by
    simpa using huLp
  have hvLp' : MemLp v (ENNReal.ofReal (2 : ℝ)) (volume.restrict S) := by
    simpa using hvLp
  have hholder := integral_mul_le_Lp_mul_Lq_of_nonneg
    (μ := volume.restrict S) (f := u) (g := v)
    Real.HolderConjugate.two_two
    (Filter.Eventually.of_forall fun t ↦ norm_nonneg (A t))
    (Filter.Eventually.of_forall fun t ↦ norm_nonneg (B t))
    huLp' hvLp'
  have horder : -T ≤ T := by linarith
  have hholder' :
      (∫ t in -T..T, u t * v t) ≤
        ((∫ t in -T..T, u t ^ (2 : ℝ)) ^ ((1 : ℝ) / 2)) *
          ((∫ t in -T..T, v t ^ (2 : ℝ)) ^ ((1 : ℝ) / 2)) := by
    simpa only [S, ← intervalIntegral.integral_of_le horder] using hholder
  simpa only [u, v, norm_mul, Real.rpow_two,
    Complex.normSq_eq_norm_sq] using hholder'

/-- A uniform bound for the source Perron envelope, followed only after that
by the exact prime/HPP split of the two Lambda windows. -/
theorem intervalIntegral_sourcePerronEnvelope_mul_lambdaPairNorm_le_uniform
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    (y : ℕ) {X : ℕ} (hX : 2 ≤ X)
    {beta T M : ℝ} (hbeta0 : 0 ≤ beta) (hT : 0 ≤ T) (hM : 0 ≤ M)
    (henv : ∀ t, |t| ≤ T → gsA10SourcePerronEnvelope f X beta t ≤ M) :
    (∫ t in -T..T,
      gsA10SourcePerronEnvelope f X beta t *
        gsA10SourceLambdaPairNorm f hmul y X beta t) ≤
      M *
        ((∫ t in -T..T,
            Complex.normSq
              (gsA10PrimeLambdaPolynomial hmul y X
                (Erdos67.EulerResidue.taoExponent X - beta) t)) ^
              ((1 : ℝ) / 2) *
          (∫ t in -T..T,
            Complex.normSq
              (gsA10PrimeLambdaPolynomial hmul y X
                (Erdos67.EulerResidue.taoExponent X + beta) t)) ^
              ((1 : ℝ) / 2) +
          2 * T *
            gsA10LambdaVerticalSplitError y X
              (Erdos67.EulerResidue.taoExponent X - beta)
              (Erdos67.EulerResidue.taoExponent X + beta)) := by
  let c₀ : ℝ := Erdos67.EulerResidue.taoExponent X
  let W := gsA10LambdaWindow (gsA9HighGeneralizedMangoldt hmul y) y X
  let H : ℝ → ℝ := gsA10SourcePerronEnvelope f X beta
  let Aminus : ℝ → ℂ := fun t ↦
    LSeries W (((c₀ - beta : ℝ) : ℂ) + Complex.I * (t : ℂ))
  let Aplus : ℝ → ℂ := fun t ↦
    LSeries W (((c₀ + beta : ℝ) : ℂ) + Complex.I * (t : ℂ))
  let Pminus : ℝ → ℂ := fun t ↦
    gsA10PrimeLambdaPolynomial hmul y X (c₀ - beta) (-t)
  let Pplus : ℝ → ℂ := fun t ↦
    gsA10PrimeLambdaPolynomial hmul y X (c₀ + beta) (-t)
  let E : ℝ := gsA10LambdaVerticalSplitError y X
    (c₀ - beta) (c₀ + beta)
  have hH : Continuous H :=
    continuous_gsA10SourcePerronEnvelope hbound (by omega) hbeta0
  have hAminus : Continuous Aminus :=
    continuous_LSeries_gsA10LambdaWindow hmul y X (c₀ - beta)
  have hAplus : Continuous Aplus :=
    continuous_LSeries_gsA10LambdaWindow hmul y X (c₀ + beta)
  have hPminus : Continuous Pminus :=
    (continuous_gsA10PrimeLambdaPolynomial hmul y X (c₀ - beta)).comp
      continuous_neg
  have hPplus : Continuous Pplus :=
    (continuous_gsA10PrimeLambdaPolynomial hmul y X (c₀ + beta)).comp
      continuous_neg
  have hE0 : 0 ≤ E := by
    have hsplit :=
      norm_LSeries_gsA10LambdaWindow_product_sub_primeProduct_le
        hmul hbound (y := y) hX (c₀ - beta) (c₀ + beta) 0
    exact (norm_nonneg _).trans hsplit
  have hpoint (t : ℝ) (ht : t ∈ Set.Icc (-T) T) :
      H t * ‖Aminus t * Aplus t‖ ≤
        M * (‖Pminus t * Pplus t‖ + E) := by
    have htAbs : |t| ≤ T := abs_le.mpr ht
    have hHt := henv t htAbs
    have hH0 : 0 ≤ H t := by
      dsimp only [H]
      unfold gsA10SourcePerronEnvelope gsA10SourceWindowCoreBudget
      positivity
    have hsplit : ‖Aminus t * Aplus t - Pminus t * Pplus t‖ ≤ E := by
      simpa only [Aminus, Aplus, Pminus, Pplus, E, W, c₀] using
        (norm_LSeries_gsA10LambdaWindow_product_sub_primeProduct_le
          hmul hbound hX (c₀ - beta) (c₀ + beta) t)
    have hpair : ‖Aminus t * Aplus t‖ ≤
        ‖Pminus t * Pplus t‖ + E := by
      calc
        ‖Aminus t * Aplus t‖ =
            ‖(Aminus t * Aplus t - Pminus t * Pplus t) +
              Pminus t * Pplus t‖ := by ring_nf
        _ ≤ ‖Aminus t * Aplus t - Pminus t * Pplus t‖ +
            ‖Pminus t * Pplus t‖ := norm_add_le _ _
        _ ≤ ‖Pminus t * Pplus t‖ + E := by linarith
    exact mul_le_mul hHt hpair (norm_nonneg _) hM
  have hleftCont : Continuous (fun t ↦ H t * ‖Aminus t * Aplus t‖) :=
    hH.mul (hAminus.mul hAplus).norm
  have hrightCont : Continuous (fun t ↦
      M * (‖Pminus t * Pplus t‖ + E)) :=
    continuous_const.mul ((hPminus.mul hPplus).norm.add continuous_const)
  have hmono :
      (∫ t in -T..T, H t * ‖Aminus t * Aplus t‖) ≤
        ∫ t in -T..T, M * (‖Pminus t * Pplus t‖ + E) := by
    apply intervalIntegral.integral_mono_on (by linarith)
      (hleftCont.intervalIntegrable _ _) (hrightCont.intervalIntegrable _ _)
    intro t ht
    exact hpoint t ht
  have hcauchy := intervalIntegral_norm_mul_le_rpow_half_normSq
    Pminus Pplus hPminus hPplus hT
  have hflipMinus :
      (∫ t in -T..T, Complex.normSq (Pminus t)) =
        ∫ t in -T..T,
          Complex.normSq
            (gsA10PrimeLambdaPolynomial hmul y X (c₀ - beta) t) := by
    simpa only [Pminus, neg_neg] using
      (intervalIntegral.integral_comp_neg (a := -T) (b := T)
        (fun t ↦ Complex.normSq
          (gsA10PrimeLambdaPolynomial hmul y X (c₀ - beta) (-t)))).symm
  have hflipPlus :
      (∫ t in -T..T, Complex.normSq (Pplus t)) =
        ∫ t in -T..T,
          Complex.normSq
            (gsA10PrimeLambdaPolynomial hmul y X (c₀ + beta) t) := by
    simpa only [Pplus, neg_neg] using
      (intervalIntegral.integral_comp_neg (a := -T) (b := T)
        (fun t ↦ Complex.normSq
          (gsA10PrimeLambdaPolynomial hmul y X (c₀ + beta) (-t)))).symm
  have hprime :
      (∫ t in -T..T, ‖Pminus t * Pplus t‖) ≤
        (∫ t in -T..T,
          Complex.normSq
            (gsA10PrimeLambdaPolynomial hmul y X (c₀ - beta) t)) ^
              ((1 : ℝ) / 2) *
        (∫ t in -T..T,
          Complex.normSq
            (gsA10PrimeLambdaPolynomial hmul y X (c₀ + beta) t)) ^
              ((1 : ℝ) / 2) := by
    simpa only [hflipMinus, hflipPlus] using hcauchy
  unfold gsA10SourceLambdaPairNorm
  dsimp only [c₀, W, H, Aminus, Aplus]
  calc
    (∫ t in -T..T,
        gsA10SourcePerronEnvelope f X beta t *
          ‖LSeries W (((c₀ - beta : ℝ) : ℂ) + Complex.I * (t : ℂ)) *
            LSeries W (((c₀ + beta : ℝ) : ℂ) + Complex.I * (t : ℂ))‖) ≤
        ∫ t in -T..T, M * (‖Pminus t * Pplus t‖ + E) := hmono
    _ = M * (∫ t in -T..T, ‖Pminus t * Pplus t‖ + E) := by
      rw [intervalIntegral.integral_const_mul]
    _ = M * ((∫ t in -T..T, ‖Pminus t * Pplus t‖) +
        ∫ _t in -T..T, E) := by
      congr 1
      exact intervalIntegral.integral_add
        ((hPminus.mul hPplus).norm.intervalIntegrable (-T) T)
        (continuous_const.intervalIntegrable (-T) T)
    _ = M * ((∫ t in -T..T, ‖Pminus t * Pplus t‖) + 2 * T * E) := by
      rw [intervalIntegral.integral_const]
      simp only [smul_eq_mul]
      ring
    _ ≤ M *
        ((∫ t in -T..T,
            Complex.normSq
              (gsA10PrimeLambdaPolynomial hmul y X (c₀ - beta) t)) ^
                ((1 : ℝ) / 2) *
          (∫ t in -T..T,
            Complex.normSq
              (gsA10PrimeLambdaPolynomial hmul y X (c₀ + beta) t)) ^
                ((1 : ℝ) / 2) + 2 * T * E) := by
      exact mul_le_mul_of_nonneg_left (add_le_add hprime (le_refl _)) hM
    _ = _ := rfl

/-- Fully source-shaped vertical estimate.  The prime and higher-prime-power
parts share the same exact `(X/y)^beta` factor. -/
theorem intervalIntegral_sourcePerronEnvelope_mul_lambdaPairNorm_le_affineRow
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    {A X y : ℕ} (hX : 2 ≤ X) (hy : 0 < y) (hyX : y ≤ X)
    (hN : 2 ≤ X / y) (hlogX : 1 ≤ Real.log (X : ℝ))
    (hnonpret : MRArchimedeanNonpretentious f A X)
    {beta T Arow Brow : ℝ}
    (hbeta0 : 0 ≤ beta) (hbeta : beta ≤ 1 / 4)
    (hT0 : 0 < T) (hTX : T ≤ X) (hArow : 0 ≤ Arow) (hBrow : 0 ≤ Brow)
    (hrow : ∀ n ∈ gsA10PrimeWindow y X,
      (∑ m ∈ gsA10PrimeWindow y X,
          (Real.log (m : ℝ) / m) *
            finiteHalaszGaussianPairKernel (T⁻¹ ^ 2)
              (Real.log m - Real.log n)) ≤ Arow / T + Brow) :
    (∫ t in -T..T,
      gsA10SourcePerronEnvelope f X beta t *
        gsA10SourceLambdaPairNorm f hmul y X beta t) ≤
      (Real.exp
          (28 * Real.exp 4 *
              Erdos67.EulerQuantitative.primeQuadraticConstant +
            36 * gsA9SourceShiftConstant) *
        gsA10SourceMaximumModulusSqrtScalar A X *
        Real.sqrt
          ‖riemannZeta
            (((Erdos67.EulerResidue.taoExponent X + beta : ℝ) : ℂ))‖) *
      (((X / y : ℕ) : ℝ) ^ beta *
        ((Real.exp 1 * Real.sqrt Real.pi * (Arow + Brow * T)) *
            gsA10PrimeLambdaSymmetricBetaDiagonalBudget X beta +
          2 * T *
            (2 * gsA10PrimeLambdaHarmonicBudget X *
                gsA10HigherPrimePowerGeometricMass y X +
              (gsA10HigherPrimePowerGeometricMass y X) ^ 2))) := by
  let M : ℝ :=
    Real.exp
        (28 * Real.exp 4 *
            Erdos67.EulerQuantitative.primeQuadraticConstant +
          36 * gsA9SourceShiftConstant) *
      gsA10SourceMaximumModulusSqrtScalar A X *
      Real.sqrt
        ‖riemannZeta
          (((Erdos67.EulerResidue.taoExponent X + beta : ℝ) : ℂ))‖
  let Q : ℝ := Real.exp 1 * Real.sqrt Real.pi * (Arow + Brow * T)
  let R : ℝ := ((X / y : ℕ) : ℝ) ^ beta
  let D : ℝ := gsA10PrimeLambdaSymmetricBetaDiagonalBudget X beta
  let E : ℝ := gsA10LambdaVerticalSplitError y X
    (Erdos67.EulerResidue.taoExponent X - beta)
    (Erdos67.EulerResidue.taoExponent X + beta)
  let G : ℝ :=
    2 * gsA10PrimeLambdaHarmonicBudget X *
        gsA10HigherPrimePowerGeometricMass y X +
      (gsA10HigherPrimePowerGeometricMass y X) ^ 2
  have hM0 : 0 ≤ M := by
    dsimp only [M, gsA10SourceMaximumModulusSqrtScalar]
    have hsqrt : 0 ≤ Real.sqrt (1 + Real.log (X : ℝ)) :=
      Real.sqrt_nonneg _
    positivity
  have henv : ∀ t, |t| ≤ T →
      gsA10SourcePerronEnvelope f X beta t ≤ M := by
    intro t ht
    simpa only [M] using
      (gsA10SourcePerronEnvelope_le_maximumModulus
        hmul hbound (show 1 < X by omega) hlogX hnonpret hbeta0 hbeta
          hT0.le hTX ht)
  have hbase :=
    intervalIntegral_sourcePerronEnvelope_mul_lambdaPairNorm_le_uniform
      hmul hbound y hX hbeta0 hT0.le hM0 henv
  have hprime :=
    rpow_half_mul_intervalIntegral_normSq_gsA10PrimeLambda_tao_le_affineRow_symmetric
      hmul hbound y X beta T Arow Brow hX hN hbeta0
        (hbeta.trans (by norm_num : (1 / 4 : ℝ) ≤ 1 / 2))
        hT0 hArow hBrow hrow
  have hhpp := gsA10LambdaVerticalSplitError_symmetric_le
    hy hyX hX hbeta0
  change _ ≤ M * (_ + 2 * T * E) at hbase
  change _ ≤ Q * (R * D) at hprime
  change E ≤ R * G at hhpp
  change _ ≤ M * (R * (Q * D + 2 * T * G))
  calc
    _ ≤ M * (_ + 2 * T * E) := hbase
    _ ≤ M * (Q * (R * D) + 2 * T * (R * G)) := by
      gcongr
    _ = M * (R * (Q * D + 2 * T * G)) := by ring

/-- The scalar on the right of the preceding source vertical estimate. -/
def gsA10SourceAffineVerticalBudget
    (A X y : ℕ) (beta T Arow Brow : ℝ) : ℝ :=
  (Real.exp
      (28 * Real.exp 4 *
          Erdos67.EulerQuantitative.primeQuadraticConstant +
        36 * gsA9SourceShiftConstant) *
    gsA10SourceMaximumModulusSqrtScalar A X *
    Real.sqrt
      ‖riemannZeta
        (((Erdos67.EulerResidue.taoExponent X + beta : ℝ) : ℂ))‖) *
  (((X / y : ℕ) : ℝ) ^ beta *
    ((Real.exp 1 * Real.sqrt Real.pi * (Arow + Brow * T)) *
        gsA10PrimeLambdaSymmetricBetaDiagonalBudget X beta +
      2 * T *
        (2 * gsA10PrimeLambdaHarmonicBudget X *
            gsA10HigherPrimePowerGeometricMass y X +
          (gsA10HigherPrimePowerGeometricMass y X) ^ 2)))

/-- The same vertical budget after combining the symmetric diagonal and the
high-line zeta factor.  The prime term has pole order `3/2`; the explicit
higher-prime-power term has only the square-root pole. -/
def gsA10SourceAffineVerticalBetaPoleBudget
    (A X y : ℕ) (beta T Arow Brow : ℝ) : ℝ :=
  (Real.exp
      (28 * Real.exp 4 *
          Erdos67.EulerQuantitative.primeQuadraticConstant +
        36 * gsA9SourceShiftConstant) *
    gsA10SourceMaximumModulusSqrtScalar A X) *
  (((X / y : ℕ) : ℝ) ^ beta *
    ((Real.exp 1 * Real.sqrt Real.pi * (Arow + Brow * T)) *
        ((2 * gsA10PrimeLambdaSymmetricBetaScalarConstant) *
          ((Real.log (X : ℝ))⁻¹ + beta) ^ (-3 / 2 : ℝ)) +
      4 * T *
        (2 * gsA10PrimeLambdaHarmonicBudget X *
            gsA10HigherPrimePowerGeometricMass y X +
          (gsA10HigherPrimePowerGeometricMass y X) ^ 2) *
        Real.sqrt (((Real.log (X : ℝ))⁻¹ + beta)⁻¹)))

theorem gsA10SourceAffineVerticalBudget_le_betaPoleBudget
    {A X y : ℕ} (hX : 2 ≤ X)
    {beta T Arow Brow : ℝ} (hbeta0 : 0 ≤ beta)
    (hbeta : beta ≤ 1 / 4) (hT : 0 ≤ T)
    (hArow : 0 ≤ Arow) (hBrow : 0 ≤ Brow) :
    gsA10SourceAffineVerticalBudget A X y beta T Arow Brow ≤
      gsA10SourceAffineVerticalBetaPoleBudget A X y beta T Arow Brow := by
  let K : ℝ :=
    Real.exp
        (28 * Real.exp 4 *
            Erdos67.EulerQuantitative.primeQuadraticConstant +
          36 * gsA9SourceShiftConstant) *
      gsA10SourceMaximumModulusSqrtScalar A X
  let Z : ℝ := Real.sqrt
    ‖riemannZeta
      (((Erdos67.EulerResidue.taoExponent X + beta : ℝ) : ℂ))‖
  let R : ℝ := ((X / y : ℕ) : ℝ) ^ beta
  let Q : ℝ := Real.exp 1 * Real.sqrt Real.pi * (Arow + Brow * T)
  let B : ℝ := gsA10PrimeLambdaSymmetricBetaDiagonalBudget X beta
  let G : ℝ :=
    2 * gsA10PrimeLambdaHarmonicBudget X *
        gsA10HigherPrimePowerGeometricMass y X +
      (gsA10HigherPrimePowerGeometricMass y X) ^ 2
  let D : ℝ :=
    (2 * gsA10PrimeLambdaSymmetricBetaScalarConstant) *
      ((Real.log (X : ℝ))⁻¹ + beta) ^ (-3 / 2 : ℝ)
  let S : ℝ := Real.sqrt (((Real.log (X : ℝ))⁻¹ + beta)⁻¹)
  have hK0 : 0 ≤ K := by
    dsimp only [K, gsA10SourceMaximumModulusSqrtScalar]
    have hsqrt : 0 ≤ Real.sqrt (1 + Real.log (X : ℝ)) :=
      Real.sqrt_nonneg _
    positivity
  have hR0 : 0 ≤ R := by dsimp only [R]; positivity
  have hQ0 : 0 ≤ Q := by dsimp only [Q]; positivity
  have hG0 : 0 ≤ G := by
    dsimp only [G]
    have hH0 : 0 ≤ gsA10PrimeLambdaHarmonicBudget X := by
      unfold gsA10PrimeLambdaHarmonicBudget
      positivity
    have hP0 : 0 ≤ gsA10HigherPrimePowerGeometricMass y X := by
      unfold gsA10HigherPrimePowerGeometricMass
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
    positivity
  have hdiag : B * Z ≤ D := by
    simpa only [B, Z, D] using
      (gsA10PrimeLambdaSymmetricBetaDiagonalBudget_mul_sqrt_zeta_le
        hX hbeta0 (hbeta.trans (by norm_num : (1 / 4 : ℝ) ≤ 1 / 2)))
  have hzeta : Z ≤ 2 * S := by
    simpa only [Z, S] using
      (sqrt_norm_riemannZeta_tao_add_beta_le hX hbeta0
        (hbeta.trans (by norm_num : (1 / 4 : ℝ) ≤ 1 / 2)))
  have hprime : Q * (B * Z) ≤ Q * D :=
    mul_le_mul_of_nonneg_left hdiag hQ0
  have hhpp : 2 * T * G * Z ≤ 2 * T * G * (2 * S) :=
    mul_le_mul_of_nonneg_left hzeta
      (mul_nonneg (mul_nonneg (by norm_num) hT) hG0)
  unfold gsA10SourceAffineVerticalBudget
    gsA10SourceAffineVerticalBetaPoleBudget
  change K * Z * (R * (Q * B + 2 * T * G)) ≤
    K * (R * (Q * D + 4 * T * G * S))
  calc
    K * Z * (R * (Q * B + 2 * T * G)) =
        K * R * (Q * (B * Z) + 2 * T * G * Z) := by ring
    _ ≤ K * R * (Q * D + 2 * T * G * (2 * S)) := by
      exact mul_le_mul_of_nonneg_left (add_le_add hprime hhpp)
        (mul_nonneg hK0 hR0)
    _ = K * (R * (Q * D + 4 * T * G * S)) := by ring

/-- Actual restored source A.10 Perron contour.  The beta-dependent vertical
budget is the only quantity remaining after the exact A.13--A.14 and
prime/HPP compositions. -/
theorem norm_gsA10SourceTailoredPerronIntegral_le_affineVerticalBudget
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    (P₁ P₂ : ℕ → Prop) [DecidablePred P₁] [DecidablePred P₂]
    (hsmallOutside : ∀ p ∈ gsA9SmallPrimeFinset, P₁ p)
    {A X y : ℕ} (hy23 : 23 ≤ y) (hyX : y ≤ X) (hX : 2 ≤ X)
    (hN : 2 ≤ X / y) (hlogy : 4 ≤ Real.log (y : ℝ))
    (hlogX : 1 ≤ Real.log (X : ℝ))
    (hnonpret : MRArchimedeanNonpretentious f A X)
    {alpha beta T Arow Brow : ℝ}
    (halpha0 : 0 ≤ alpha)
    (halpha : alpha ≤ (Real.log (y : ℝ))⁻¹)
    (hbeta0 : 0 ≤ beta)
    (hbetaY : beta ≤ (Real.log (y : ℝ))⁻¹)
    (hbeta : beta ≤ 1 / 4)
    (hT0 : 0 < T) (hTX : T ≤ X)
    (hArow : 0 ≤ Arow) (hBrow : 0 ≤ Brow)
    (hrow : ∀ n ∈ gsA10PrimeWindow y X,
      (∑ m ∈ gsA10PrimeWindow y X,
          (Real.log (m : ℝ) / m) *
            finiteHalaszGaussianPairKernel (T⁻¹ ^ 2)
              (Real.log m - Real.log n)) ≤ Arow / T + Brow) :
    ‖gsA10TailoredPerronIntegral
        (gsA10TwoBlockAlternatingLow f P₁ P₂ y)
        (gsA9HighArithmetic f y)
        (gsA9HighGeneralizedMangoldt hmul y)
        y X (Erdos67.EulerResidue.taoExponent X) alpha beta T‖ ≤
      (2 * Real.pi)⁻¹ *
        (3 * gsA9SmallPrimeEulerBound *
          (X : ℝ) ^
            (Erdos67.EulerResidue.taoExponent X - alpha - beta)) *
        gsA10SourceAffineVerticalBudget A X y beta T Arow Brow := by
  let C : ℝ := 3 * gsA9SmallPrimeEulerBound *
    (X : ℝ) ^
      (Erdos67.EulerResidue.taoExponent X - alpha - beta)
  let G : ℝ → ℝ := fun t ↦
    gsA10SourcePerronEnvelope f X beta t *
      gsA10SourceLambdaPairNorm f hmul y X beta t
  let V : ℝ := gsA10SourceAffineVerticalBudget A X y beta T Arow Brow
  have hbase :=
    norm_gsA10SourceTailoredPerronIntegral_le_weightedLambdaIntegral_continuous
      hmul hbound P₁ P₂ hsmallOutside hy23 (show 1 < X by omega)
        hlogy halpha0 halpha hbeta0 hbetaY hT0.le
  have hvertical : (∫ t in -T..T, G t) ≤ V := by
    dsimp only [G, V, gsA10SourceAffineVerticalBudget]
    exact intervalIntegral_sourcePerronEnvelope_mul_lambdaPairNorm_le_affineRow
      hmul hbound hX (by omega) hyX hN hlogX hnonpret hbeta0 hbeta hT0
        hTX hArow hBrow hrow
  have hC0 : 0 ≤ C := by
    dsimp only [C]
    have hsmall0 : 0 ≤ gsA9SmallPrimeEulerBound := by
      have hsmall := norm_gsA9SmallPrimeEulerProduct_le hbound
        (sigma := (1 / 2 : ℝ)) (t := 0) le_rfl
      exact (norm_nonneg _).trans hsmall
    positivity
  have hpi0 : 0 ≤ (2 * Real.pi)⁻¹ :=
    inv_nonneg.mpr (by positivity)
  calc
    ‖gsA10TailoredPerronIntegral
        (gsA10TwoBlockAlternatingLow f P₁ P₂ y)
        (gsA9HighArithmetic f y)
        (gsA9HighGeneralizedMangoldt hmul y)
        y X (Erdos67.EulerResidue.taoExponent X) alpha beta T‖ ≤
        (2 * Real.pi)⁻¹ * ∫ t in -T..T, C * G t := by
      simpa only [C, G, mul_assoc] using hbase
    _ = (2 * Real.pi)⁻¹ * (C * ∫ t in -T..T, G t) := by
      rw [intervalIntegral.integral_const_mul]
    _ ≤ (2 * Real.pi)⁻¹ * (C * V) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hvertical hC0) hpi0
    _ = _ := by
      dsimp only [C, V]
      ring

end

end Erdos67.MRHalaszBands

#print axioms
  Erdos67.MRHalaszBands.intervalIntegral_sourcePerronEnvelope_mul_lambdaPairNorm_le_affineRow
#print axioms
  Erdos67.MRHalaszBands.gsA10SourceAffineVerticalBudget_le_betaPoleBudget
#print axioms
  Erdos67.MRHalaszBands.norm_gsA10SourceTailoredPerronIntegral_le_affineVerticalBudget
