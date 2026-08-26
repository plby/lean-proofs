import ErdosProblems.Erdos67b.MRGSA10FixedHighTailoredVerticalScalar
import ErdosProblems.Erdos67b.MRGSA10MovingPerronIntegral

/-!
# The exact moving Perron-kernel power

The fixed-high A.10 contour may keep the exact moving real power
`X^(taoExponent X - alpha - 2 beta)`.  The only loss in the Perron
denominator is the factor two coming from the lower bound `Re s ≥ 1/2`.
-/

open Complex

namespace Erdos67b.MRHalaszBands

noncomputable section

/-- The exact vertical Perron-kernel estimate on a line with real part at
least one half. -/
theorem norm_natCast_cpow_div_vertical_le_two_mul_rpow
    {X : ℕ} (hX : 0 < X) {sigma t : ℝ}
    (hsigma : 1 / 2 ≤ sigma) :
    ‖(X : ℂ) ^ ((sigma : ℂ) + I * (t : ℂ)) /
        ((sigma : ℂ) + I * (t : ℂ))‖ ≤
      2 * (X : ℝ) ^ sigma := by
  let s : ℂ := (sigma : ℂ) + I * (t : ℂ)
  have hsigmaPos : 0 < sigma :=
    (by norm_num : (0 : ℝ) < 1 / 2).trans_le hsigma
  have hsRe : s.re = sigma := by simp [s]
  have hsNorm : sigma ≤ ‖s‖ := by
    have hre := Complex.abs_re_le_norm s
    simpa only [hsRe, abs_of_pos hsigmaPos] using hre
  have hsNormPos : 0 < ‖s‖ := hsigmaPos.trans_le hsNorm
  have hXR : (0 : ℝ) < X := by exact_mod_cast hX
  have hpowNorm : ‖(X : ℂ) ^ s‖ = (X : ℝ) ^ sigma := by
    have hcast : (X : ℂ) = ((X : ℝ) : ℂ) := by norm_num
    rw [hcast]
    simpa only [hsRe] using
      Complex.norm_cpow_eq_rpow_re_of_pos hXR s
  change ‖(X : ℂ) ^ s / s‖ ≤ 2 * (X : ℝ) ^ sigma
  rw [norm_div, hpowNorm]
  calc
    (X : ℝ) ^ sigma / ‖s‖ ≤
        (X : ℝ) ^ sigma / (1 / 2 : ℝ) :=
      div_le_div_of_nonneg_left (Real.rpow_nonneg hXR.le _)
        (by norm_num) (hsigma.trans hsNorm)
    _ = 2 * (X : ℝ) ^ sigma := by ring

/-- The exact pointwise kernel scale retained on the moving source line. -/
def gsA10MovingPerronKernelScale
    (X : ℕ) (alpha beta : ℝ) : ℝ :=
  2 * (X : ℝ) ^
    (Erdos67b.EulerResidue.taoExponent X - alpha - 2 * beta)

theorem gsA10MovingPerronKernelScale_nonneg
    (X : ℕ) (alpha beta : ℝ) :
    0 ≤ gsA10MovingPerronKernelScale X alpha beta := by
  unfold gsA10MovingPerronKernelScale
  positivity

/-- On the A.10 source rectangle the moving line has real part at least
one half, so the exact `X^(c₀-alpha-2 beta)` power is preserved. -/
theorem norm_gsA10MovingPerronKernel_le_exact_rpow
    {y X : ℕ} (hX : 2 ≤ X)
    (hlogy : 6 ≤ Real.log (y : ℝ))
    {alpha beta t : ℝ}
    (_halpha0 : 0 ≤ alpha)
    (halpha : alpha ≤ (Real.log (y : ℝ))⁻¹)
    (_hbeta0 : 0 ≤ beta)
    (hbeta : beta ≤ (Real.log (y : ℝ))⁻¹) :
    ‖(X : ℂ) ^
          (((Erdos67b.EulerResidue.taoExponent X - alpha - 2 * beta : ℝ) : ℂ) +
            I * (t : ℂ)) /
        (((Erdos67b.EulerResidue.taoExponent X - alpha - 2 * beta : ℝ) : ℂ) +
          I * (t : ℂ))‖ ≤
      2 * (X : ℝ) ^
        (Erdos67b.EulerResidue.taoExponent X - alpha - 2 * beta) := by
  have hlogX : 0 < Real.log (X : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < X by omega))
  have hetaSixth : (Real.log (y : ℝ))⁻¹ ≤ 1 / 6 := by
    simpa only [one_div] using
      inv_anti₀ (by norm_num : (0 : ℝ) < 6) hlogy
  have hcOne : 1 ≤ Erdos67b.EulerResidue.taoExponent X := by
    unfold Erdos67b.EulerResidue.taoExponent
    exact le_add_of_nonneg_right (inv_pos.mpr hlogX).le
  have hab : alpha + 2 * beta ≤
      3 * (Real.log (y : ℝ))⁻¹ := by
    linarith
  have hsigmaHalf :
      1 / 2 ≤ Erdos67b.EulerResidue.taoExponent X - alpha - 2 * beta := by
    linarith
  exact norm_natCast_cpow_div_vertical_le_two_mul_rpow
    (show 0 < X by omega) hsigmaHalf

/-- Pointwise replacement form for the fixed-high argument: its constant
kernel scale can be replaced by the exact moving scale at each
`(alpha,beta)`. -/
theorem norm_gsA10MovingPerronKernel_le_scale
    {y X : ℕ} (hX : 2 ≤ X)
    (hlogy : 6 ≤ Real.log (y : ℝ))
    {alpha beta t : ℝ}
    (halpha0 : 0 ≤ alpha)
    (halpha : alpha ≤ (Real.log (y : ℝ))⁻¹)
    (hbeta0 : 0 ≤ beta)
    (hbeta : beta ≤ (Real.log (y : ℝ))⁻¹) :
    ‖(X : ℂ) ^
          (((Erdos67b.EulerResidue.taoExponent X - alpha - 2 * beta : ℝ) : ℂ) +
            I * (t : ℂ)) /
        (((Erdos67b.EulerResidue.taoExponent X - alpha - 2 * beta : ℝ) : ℂ) +
          I * (t : ℂ))‖ ≤
      gsA10MovingPerronKernelScale X alpha beta := by
  exact norm_gsA10MovingPerronKernel_le_exact_rpow
    hX hlogy halpha0 halpha hbeta0 hbeta

end

end Erdos67b.MRHalaszBands

#print axioms
  Erdos67b.MRHalaszBands.norm_natCast_cpow_div_vertical_le_two_mul_rpow
#print axioms
  Erdos67b.MRHalaszBands.norm_gsA10MovingPerronKernel_le_exact_rpow
#print axioms
  Erdos67b.MRHalaszBands.norm_gsA10MovingPerronKernel_le_scale
