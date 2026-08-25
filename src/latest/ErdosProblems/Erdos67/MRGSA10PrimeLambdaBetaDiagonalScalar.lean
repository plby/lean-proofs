import ErdosProblems.Erdos67.MRGSA10PrimeLambdaBetaDiagonal
import ErdosProblems.Erdos67.DyadicGeometric
import ErdosProblems.Erdos67.MRGSRiemannZetaUpper

/-!
# Scalar form of the symmetric beta-sensitive prime-Lambda diagonal

The source-symmetric diagonal budget is the minimum of a logarithmic bound
and a reciprocal-beta bound.  This file packages the elementary interpolation
between those two estimates in the form needed by the A.10 contour:

`B(X, beta) <= C / ((log X)⁻¹ + beta)`.

All constants are explicit and independent of `X` and `beta`.  The endpoint
`beta = 0` is handled through the logarithmic branch of the definition rather
than by a limiting argument.
-/

namespace Erdos67.MRHalaszBands

noncomputable section

/-- Constant converting the binary shell count in the harmonic diagonal to
the natural logarithm. -/
def gsA10PrimeLambdaHarmonicLogConstant : ℝ :=
  2 * (Real.log 4 + 4) * (Real.log 2)⁻¹

/-- Constant in the reciprocal-beta branch after using `beta <= 1/2`. -/
def gsA10PrimeLambdaSymmetricBetaTailConstant : ℝ :=
  4 * gsA10PrimeLogHarmonicFactorFourConstant *
    ((1 / 2 : ℝ) + (2 * Real.log 2)⁻¹)

/-- Universal scalar constant for the symmetric prime-Lambda diagonal. -/
def gsA10PrimeLambdaSymmetricBetaScalarConstant : ℝ :=
  gsA10PrimeLambdaHarmonicLogConstant +
    gsA10PrimeLambdaSymmetricBetaTailConstant

theorem gsA10PrimeLambdaHarmonicLogConstant_nonneg :
    0 ≤ gsA10PrimeLambdaHarmonicLogConstant := by
  unfold gsA10PrimeLambdaHarmonicLogConstant
  positivity

theorem gsA10PrimeLambdaSymmetricBetaTailConstant_nonneg :
    0 ≤ gsA10PrimeLambdaSymmetricBetaTailConstant := by
  unfold gsA10PrimeLambdaSymmetricBetaTailConstant
  exact mul_nonneg
    (mul_nonneg (by norm_num)
      gsA10PrimeLogHarmonicFactorFourConstant_nonneg)
    (by positivity)

theorem gsA10PrimeLambdaSymmetricBetaScalarConstant_nonneg :
    0 ≤ gsA10PrimeLambdaSymmetricBetaScalarConstant := by
  unfold gsA10PrimeLambdaSymmetricBetaScalarConstant
  exact add_nonneg gsA10PrimeLambdaHarmonicLogConstant_nonneg
    gsA10PrimeLambdaSymmetricBetaTailConstant_nonneg

/-- The elementary harmonic budget is at most an explicit constant times
`log X`. -/
theorem gsA10PrimeLambdaHarmonicBudget_le_log
    {X : ℕ} (hX : 2 ≤ X) :
    gsA10PrimeLambdaHarmonicBudget X ≤
      gsA10PrimeLambdaHarmonicLogConstant * Real.log (X : ℝ) := by
  have hlogCount :=
    Erdos67.DyadicGeometric.natLog_two_le_realLog_div
      (show 0 < X by omega)
  have hfactor : 0 ≤ 2 * (Real.log 4 + 4) := by positivity
  unfold gsA10PrimeLambdaHarmonicBudget
  calc
    2 * (Real.log 4 + 4) * (Nat.log 2 X : ℝ) ≤
        2 * (Real.log 4 + 4) *
          (Real.log (X : ℝ) / Real.log 2) :=
      mul_le_mul_of_nonneg_left hlogCount hfactor
    _ = gsA10PrimeLambdaHarmonicLogConstant * Real.log (X : ℝ) := by
      unfold gsA10PrimeLambdaHarmonicLogConstant
      rw [div_eq_mul_inv]
      ring

/-- In the positive-beta branch, multiplying the reciprocal-beta estimate by
`beta` removes its singularity with an explicit uniform constant. -/
theorem gsA10PrimeLambdaSymmetricBetaSharp_mul_le
    {beta : ℝ} (hbeta : 0 < beta) (hbetaHalf : beta ≤ 1 / 2) :
    (4 * gsA10PrimeLogHarmonicFactorFourConstant *
        (1 + (2 * Real.log 2 * beta)⁻¹)) * beta ≤
      gsA10PrimeLambdaSymmetricBetaTailConstant := by
  have hlogTwo : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  have hbetaNe : beta ≠ 0 := ne_of_gt hbeta
  have hcancel : (2 * Real.log 2 * beta)⁻¹ * beta =
      (2 * Real.log 2)⁻¹ := by
    field_simp [hlogTwo, hbetaNe]
  have hbase :
      beta + (2 * Real.log 2)⁻¹ ≤
        (1 / 2 : ℝ) + (2 * Real.log 2)⁻¹ := by
    linarith
  unfold gsA10PrimeLambdaSymmetricBetaTailConstant
  calc
    (4 * gsA10PrimeLogHarmonicFactorFourConstant *
        (1 + (2 * Real.log 2 * beta)⁻¹)) * beta =
        4 * gsA10PrimeLogHarmonicFactorFourConstant *
          (beta + (2 * Real.log 2)⁻¹) := by
      rw [mul_assoc, add_mul, one_mul, hcancel]
    _ ≤ 4 * gsA10PrimeLogHarmonicFactorFourConstant *
        ((1 / 2 : ℝ) + (2 * Real.log 2)⁻¹) :=
      mul_le_mul_of_nonneg_left hbase
        (mul_nonneg (by norm_num)
          gsA10PrimeLogHarmonicFactorFourConstant_nonneg)

/-- The source-symmetric beta diagonal has the single reciprocal envelope
`C / ((log X)⁻¹ + beta)`.  This is uniform at `beta = 0`. -/
theorem gsA10PrimeLambdaSymmetricBetaDiagonalBudget_le_inv_log_add_beta
    {X : ℕ} (hX : 2 ≤ X) {beta : ℝ}
    (hbeta : 0 ≤ beta) (hbetaHalf : beta ≤ 1 / 2) :
    gsA10PrimeLambdaSymmetricBetaDiagonalBudget X beta ≤
      gsA10PrimeLambdaSymmetricBetaScalarConstant /
        ((Real.log (X : ℝ))⁻¹ + beta) := by
  let L : ℝ := Real.log (X : ℝ)
  let B : ℝ := gsA10PrimeLambdaSymmetricBetaDiagonalBudget X beta
  have hL : 0 < L := by
    dsimp only [L]
    exact Real.log_pos (by exact_mod_cast (show 1 < X by omega))
  have hd : 0 < L⁻¹ + beta := add_pos_of_pos_of_nonneg (inv_pos.mpr hL) hbeta
  have hB0 : 0 ≤ B := by
    exact gsA10PrimeLambdaSymmetricBetaDiagonalBudget_nonneg hbeta
  have hBH : B ≤ gsA10PrimeLambdaHarmonicBudget X := by
    dsimp only [B]
    unfold gsA10PrimeLambdaSymmetricBetaDiagonalBudget
    split_ifs with hzero
    · exact le_rfl
    · exact min_le_left _ _
  have hHlog : gsA10PrimeLambdaHarmonicBudget X ≤
      gsA10PrimeLambdaHarmonicLogConstant * L := by
    simpa only [L] using gsA10PrimeLambdaHarmonicBudget_le_log hX
  have hlogPart : B * L⁻¹ ≤ gsA10PrimeLambdaHarmonicLogConstant := by
    calc
      B * L⁻¹ ≤
          (gsA10PrimeLambdaHarmonicLogConstant * L) * L⁻¹ :=
        mul_le_mul_of_nonneg_right (hBH.trans hHlog) (inv_nonneg.mpr hL.le)
      _ = gsA10PrimeLambdaHarmonicLogConstant := by
        rw [mul_assoc, mul_inv_cancel₀ hL.ne']
        ring
  have hbetaPart : B * beta ≤
      gsA10PrimeLambdaSymmetricBetaTailConstant := by
    by_cases hzero : beta = 0
    · subst beta
      simpa only [mul_zero] using
        gsA10PrimeLambdaSymmetricBetaTailConstant_nonneg
    · have hbetapos : 0 < beta := lt_of_le_of_ne hbeta (Ne.symm hzero)
      have hBsharp : B ≤
          4 * gsA10PrimeLogHarmonicFactorFourConstant *
            (1 + (2 * Real.log 2 * beta)⁻¹) := by
        dsimp only [B]
        rw [gsA10PrimeLambdaSymmetricBetaDiagonalBudget, if_neg hzero]
        exact min_le_right _ _
      exact (mul_le_mul_of_nonneg_right hBsharp hbeta).trans
        (gsA10PrimeLambdaSymmetricBetaSharp_mul_le hbetapos hbetaHalf)
  apply (le_div_iff₀ hd).2
  calc
    B * (L⁻¹ + beta) = B * L⁻¹ + B * beta := by ring
    _ ≤ gsA10PrimeLambdaHarmonicLogConstant +
        gsA10PrimeLambdaSymmetricBetaTailConstant :=
      add_le_add hlogPart hbetaPart
    _ = gsA10PrimeLambdaSymmetricBetaScalarConstant := by
      rfl

/-- On the source high line, the real zeta factor has precisely the same
pole scale `((log X)⁻¹ + beta)⁻¹`.  A constant `2` is enough uniformly for
`X >= 2` and `0 <= beta <= 1/2`. -/
theorem sqrt_norm_riemannZeta_tao_add_beta_le
    {X : ℕ} (hX : 2 ≤ X) {beta : ℝ}
    (hbeta : 0 ≤ beta) (hbetaHalf : beta ≤ 1 / 2) :
    Real.sqrt
        ‖riemannZeta
          ((Erdos67.EulerResidue.taoExponent X + beta : ℝ) : ℂ)‖ ≤
      2 * Real.sqrt (((Real.log (X : ℝ))⁻¹ + beta)⁻¹) := by
  let L : ℝ := Real.log (X : ℝ)
  let d : ℝ := L⁻¹ + beta
  have hL : 0 < L := by
    dsimp only [L]
    exact Real.log_pos (by exact_mod_cast (show 1 < X by omega))
  have hd : 0 < d := add_pos_of_pos_of_nonneg (inv_pos.mpr hL) hbeta
  have hlogMono : Real.log 2 ≤ L := by
    dsimp only [L]
    exact Real.strictMonoOn_log.monotoneOn
      (by norm_num [Set.mem_Ioi])
      (by simpa only [Set.mem_Ioi] using
        (show (0 : ℝ) < (X : ℝ) by exact_mod_cast (show 0 < X by omega)))
      (by exact_mod_cast hX)
  have hlogTwoHalf : (1 / 2 : ℝ) ≤ Real.log 2 := by
    exact (by norm_num : (1 / 2 : ℝ) < 0.6931471803).le.trans
      Real.log_two_gt_d9.le
  have hinvLog : L⁻¹ ≤ 2 := by
    have hlogHalf : (1 / 2 : ℝ) ≤ L := hlogTwoHalf.trans hlogMono
    have h := (inv_le_inv₀ hL (by norm_num : (0 : ℝ) < 1 / 2)).2 hlogHalf
    norm_num at h ⊢
    exact h
  have hdThree : d ≤ 3 := by
    dsimp only [d]
    linarith
  have hone : 1 ≤ 3 * d⁻¹ := by
    calc
      (1 : ℝ) = d * d⁻¹ := by rw [mul_inv_cancel₀ hd.ne']
      _ ≤ 3 * d⁻¹ :=
        mul_le_mul_of_nonneg_right hdThree (inv_nonneg.mpr hd.le)
  have hzeta0 := Erdos67.norm_riemannZeta_real_le_one_add_inv hd
  have hpoint :
      ((Erdos67.EulerResidue.taoExponent X + beta : ℝ) : ℂ) =
        (((1 + d : ℝ) : ℂ)) := by
    dsimp only [d, L]
    unfold Erdos67.EulerResidue.taoExponent
    push_cast
    ring
  have hzeta :
      ‖riemannZeta
          ((Erdos67.EulerResidue.taoExponent X + beta : ℝ) : ℂ)‖ ≤
        4 * d⁻¹ := by
    rw [hpoint]
    exact hzeta0.trans (by linarith)
  have hsqrt := Real.sqrt_le_sqrt hzeta
  calc
    Real.sqrt
        ‖riemannZeta
          ((Erdos67.EulerResidue.taoExponent X + beta : ℝ) : ℂ)‖ ≤
        Real.sqrt (4 * d⁻¹) := hsqrt
    _ = 2 * Real.sqrt d⁻¹ := by
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
      norm_num
    _ = 2 * Real.sqrt (((Real.log (X : ℝ))⁻¹ + beta)⁻¹) := by
      rfl

private theorem inv_mul_sqrt_inv_eq_rpow_neg_three_halves
    {d : ℝ} (hd : 0 < d) :
    d⁻¹ * Real.sqrt d⁻¹ = d ^ (-3 / 2 : ℝ) := by
  rw [← Real.rpow_neg_one d, Real.sqrt_eq_rpow]
  rw [← Real.rpow_mul hd.le]
  rw [← Real.rpow_add hd]
  congr 1
  ring

/-- Contour-ready product of the symmetric diagonal budget and the high-line
zeta square root.  Its total pole order is `3/2`. -/
theorem gsA10PrimeLambdaSymmetricBetaDiagonalBudget_mul_sqrt_zeta_le
    {X : ℕ} (hX : 2 ≤ X) {beta : ℝ}
    (hbeta : 0 ≤ beta) (hbetaHalf : beta ≤ 1 / 2) :
    gsA10PrimeLambdaSymmetricBetaDiagonalBudget X beta *
        Real.sqrt
          ‖riemannZeta
            ((Erdos67.EulerResidue.taoExponent X + beta : ℝ) : ℂ)‖ ≤
      (2 * gsA10PrimeLambdaSymmetricBetaScalarConstant) *
        ((Real.log (X : ℝ))⁻¹ + beta) ^ (-3 / 2 : ℝ) := by
  let d : ℝ := (Real.log (X : ℝ))⁻¹ + beta
  have hlogX : 0 < Real.log (X : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < X by omega))
  have hd : 0 < d := by
    dsimp only [d]
    exact add_pos_of_pos_of_nonneg (inv_pos.mpr hlogX) hbeta
  have hbudget0 :=
    gsA10PrimeLambdaSymmetricBetaDiagonalBudget_le_inv_log_add_beta
      hX hbeta hbetaHalf
  have hbudget :
      gsA10PrimeLambdaSymmetricBetaDiagonalBudget X beta ≤
        gsA10PrimeLambdaSymmetricBetaScalarConstant / d := by
    simpa only [d] using hbudget0
  have hzeta0 := sqrt_norm_riemannZeta_tao_add_beta_le
    hX hbeta hbetaHalf
  have hzeta : Real.sqrt
      ‖riemannZeta
        ((Erdos67.EulerResidue.taoExponent X + beta : ℝ) : ℂ)‖ ≤
      2 * Real.sqrt d⁻¹ := by
    simpa only [d] using hzeta0
  have hB0 :=
    gsA10PrimeLambdaSymmetricBetaDiagonalBudget_nonneg (X := X) hbeta
  have hZ0 : 0 ≤ Real.sqrt
      ‖riemannZeta
        ((Erdos67.EulerResidue.taoExponent X + beta : ℝ) : ℂ)‖ :=
    Real.sqrt_nonneg _
  calc
    gsA10PrimeLambdaSymmetricBetaDiagonalBudget X beta *
        Real.sqrt
          ‖riemannZeta
            ((Erdos67.EulerResidue.taoExponent X + beta : ℝ) : ℂ)‖ ≤
        (gsA10PrimeLambdaSymmetricBetaScalarConstant / d) *
          (2 * Real.sqrt d⁻¹) := by
      exact mul_le_mul hbudget hzeta hZ0
        (div_nonneg gsA10PrimeLambdaSymmetricBetaScalarConstant_nonneg hd.le)
    _ = (2 * gsA10PrimeLambdaSymmetricBetaScalarConstant) *
        d ^ (-3 / 2 : ℝ) := by
      rw [div_eq_mul_inv]
      rw [← inv_mul_sqrt_inv_eq_rpow_neg_three_halves hd]
      ring
    _ = (2 * gsA10PrimeLambdaSymmetricBetaScalarConstant) *
        ((Real.log (X : ℝ))⁻¹ + beta) ^ (-3 / 2 : ℝ) := by
      rfl

end

end Erdos67.MRHalaszBands
