import ErdosProblems.Erdos239.External.Erdos67.MRGSA10TailoredPerronContour
import ErdosProblems.Erdos239.External.Erdos67.MRGSA9SmallPrimeRestore
import ErdosProblems.Erdos239.External.Erdos67.MRGSA10LambdaVerticalContour

/-!
# The source-shaped A.13--A.14 Perron envelope

This file keeps the beta-shifted full deleted L-series and the genuine
Perron denominator visible.  In particular, it does not replace the
A.13--A.14 factor by the fixed-height Halasz scalar.
-/

open scoped BigOperators LSeries.notation
open Complex Set MeasureTheory

namespace Erdos67.MRHalaszBands

noncomputable section

/-- The exact A.13--A.14 numerator divided by the norm of the shifted
high-line point.  This is the source-shaped factor which remains inside
the beta and vertical integrations. -/
def gsA10SourcePerronEnvelope
    (f : ℕ → ℂ) (X : ℕ) (beta t : ℝ) : ℝ :=
  let c₀ := Erdos67.EulerResidue.taoExponent X
  gsA10SourceWindowCoreBudget f 0 X beta t /
    ‖(((c₀ + beta : ℝ) : ℂ) + Complex.I * (t : ℂ))‖

/-- Norm of the two finite Mangoldt windows on the original source lines.
It is intentionally not estimated here. -/
def gsA10SourceLambdaPairNorm
    (f : ℕ → ℂ) (hmul : IsMultiplicativeOnPositiveNat f)
    (y X : ℕ) (beta t : ℝ) : ℝ :=
  let c₀ := Erdos67.EulerResidue.taoExponent X
  let W := gsA10LambdaWindow (gsA9HighGeneralizedMangoldt hmul y) y X
  ‖LSeries W (((c₀ - beta : ℝ) : ℂ) + Complex.I * (t : ℂ)) *
    LSeries W (((c₀ + beta : ℝ) : ℂ) + Complex.I * (t : ℂ))‖

private theorem continuous_LSeries_sourceDeleted_vertical
    {f : ℕ → ℂ} (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    {sigma : ℝ} (hsigma : 1 < sigma) :
    Continuous (fun t : ℝ ↦
      LSeries (gsA10SourceDeleted f)
        ((sigma : ℂ) + Complex.I * (t : ℂ))) := by
  let g : ℕ → ℂ := gsA10SourceDeleted f
  have hboundG : ∀ n, n ≠ 0 → ‖g n‖ ≤ 1 := by
    intro n hn
    exact norm_gsDeletePrimeBand_le_one hbound gsA9SmallPrime
      (Nat.pos_of_ne_zero hn)
  have hmid : 1 < (sigma + 1) / 2 := by linarith
  have hsum : LSeriesSummable g (((sigma + 1) / 2 : ℝ) : ℂ) :=
    LSeriesSummable_of_bounded_of_one_lt_re hboundG (by simpa using hmid)
  have habs : LSeries.abscissaOfAbsConv g < (sigma : EReal) := by
    calc
      LSeries.abscissaOfAbsConv g ≤ (((sigma + 1) / 2 : ℝ) : EReal) := by
        simpa using hsum.abscissaOfAbsConv_le
      _ < (sigma : ℝ) := by
        exact_mod_cast (by linarith : (sigma + 1) / 2 < sigma)
  have hline : Continuous (fun t : ℝ ↦
      (sigma : ℂ) + Complex.I * (t : ℂ)) := by fun_prop
  exact (LSeries_differentiableOn g).continuousOn.comp_continuous
    hline (fun t ↦ by simpa using habs)

theorem continuous_gsA10SourcePerronEnvelope
    {f : ℕ → ℂ} (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    {X : ℕ} (hX : 1 < X) {beta : ℝ} (hbeta0 : 0 ≤ beta) :
    Continuous (gsA10SourcePerronEnvelope f X beta) := by
  let c₀ : ℝ := Erdos67.EulerResidue.taoExponent X
  let sigmaHigh : ℝ := c₀ + beta
  have hlogX : 0 < Real.log (X : ℝ) :=
    Real.log_pos (by exact_mod_cast hX)
  have hcStrict : 1 < c₀ := by
    dsimp only [c₀, Erdos67.EulerResidue.taoExponent]
    linarith [inv_pos.mpr hlogX]
  have hsigmaHigh : 1 < sigmaHigh := by
    dsimp only [sigmaHigh]
    linarith
  have hL : Continuous (fun t : ℝ ↦
      LSeries (gsA10SourceDeleted f)
        ((sigmaHigh : ℂ) + Complex.I * (t : ℂ))) :=
    continuous_LSeries_sourceDeleted_vertical hbound hsigmaHigh
  have hcore : Continuous (fun t : ℝ ↦
      gsA10SourceWindowCoreBudget f 0 X beta t) := by
    unfold gsA10SourceWindowCoreBudget
    dsimp only
    have hsqrtL : Continuous (fun t : ℝ ↦
        Real.sqrt ‖LSeries (gsA10SourceDeleted f)
          ((sigmaHigh : ℂ) + Complex.I * (t : ℂ))‖) := hL.norm.sqrt
    have hC : Continuous (fun _ : ℝ ↦
        Real.exp
          (28 * Real.exp 4 *
              Erdos67.EulerQuantitative.primeQuadraticConstant +
            36 * gsA9SourceShiftConstant)) := continuous_const
    have hconst : Continuous (fun _ : ℝ ↦
        Real.sqrt ‖riemannZeta ((sigmaHigh : ℝ) : ℂ)‖) := continuous_const
    have hprod : Continuous (fun t : ℝ ↦
        (Real.exp
            (28 * Real.exp 4 *
                Erdos67.EulerQuantitative.primeQuadraticConstant +
              36 * gsA9SourceShiftConstant) *
          Real.sqrt ‖LSeries (gsA10SourceDeleted f)
            ((sigmaHigh : ℂ) + Complex.I * (t : ℂ))‖) *
          Real.sqrt ‖riemannZeta ((sigmaHigh : ℝ) : ℂ)‖) :=
      (hC.mul hsqrtL).mul hconst
    simpa only [c₀, sigmaHigh] using hprod
  have hden : Continuous (fun t : ℝ ↦
      ‖(((sigmaHigh : ℝ) : ℂ) + Complex.I * (t : ℂ))‖) := by
    fun_prop
  have hdenNe : ∀ t : ℝ,
      ‖(((sigmaHigh : ℝ) : ℂ) + Complex.I * (t : ℂ))‖ ≠ 0 := by
    intro t hzero
    have hz : ((sigmaHigh : ℝ) : ℂ) + Complex.I * (t : ℂ) = 0 :=
      norm_eq_zero.mp hzero
    have hre := congrArg Complex.re hz
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.I_re, Complex.I_im, Complex.ofReal_im, zero_mul, one_mul,
      sub_zero, Complex.zero_re] at hre
    linarith
  unfold gsA10SourcePerronEnvelope
  dsimp only [c₀, sigmaHigh]
  exact hcore.div hden hdenNe

theorem continuous_gsA10SourceLambdaPairNorm
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (y X : ℕ) (beta : ℝ) :
    Continuous (gsA10SourceLambdaPairNorm f hmul y X beta) := by
  let c₀ : ℝ := Erdos67.EulerResidue.taoExponent X
  have hlow := continuous_LSeries_gsA10LambdaWindow
    hmul y X (c₀ - beta)
  have hhigh := continuous_LSeries_gsA10LambdaWindow
    hmul y X (c₀ + beta)
  unfold gsA10SourceLambdaPairNorm
  dsimp only [c₀]
  exact (hlow.mul hhigh).norm

/-- The high source point has norm at most three times the corresponding
low Perron point.  The constant is deliberately elementary and uniform on
the whole source rectangle. -/
theorem norm_sourceHigh_le_three_mul_norm_sourceLow
    {c alpha beta t : ℝ}
    (hhalf : 1 / 2 ≤ c - alpha - beta)
    (hshift0 : 0 ≤ alpha + 2 * beta)
    (hshift : alpha + 2 * beta ≤ 1) :
    ‖(((c + beta : ℝ) : ℂ) + Complex.I * (t : ℂ))‖ ≤
      3 * ‖(((c - alpha - beta : ℝ) : ℂ) +
        Complex.I * (t : ℂ))‖ := by
  let sLow : ℂ := ((c - alpha - beta : ℝ) : ℂ) +
    Complex.I * (t : ℂ)
  let sHigh : ℂ := ((c + beta : ℝ) : ℂ) +
    Complex.I * (t : ℂ)
  let delta : ℝ := alpha + 2 * beta
  have hpoint : sHigh = sLow + (delta : ℂ) := by
    apply Complex.ext <;>
      simp only [sHigh, sLow, delta, Complex.add_re, Complex.add_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re,
        Complex.mul_im, Complex.I_re, Complex.I_im, zero_mul, one_mul,
        mul_zero, add_zero, zero_add, sub_zero] <;> ring
  have hlow : 1 / 2 ≤ ‖sLow‖ := by
    have hre := Complex.abs_re_le_norm sLow
    have hreEq : sLow.re = c - alpha - beta := by simp [sLow]
    rw [hreEq, abs_of_nonneg (by linarith : 0 ≤ c - alpha - beta)] at hre
    exact hhalf.trans hre
  have hdelta : ‖(delta : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
    · simpa only [delta] using hshift
    · simpa only [delta] using hshift0
  calc
    ‖sHigh‖ = ‖sLow + (delta : ℂ)‖ := by rw [hpoint]
    _ ≤ ‖sLow‖ + ‖(delta : ℂ)‖ := norm_add_le _ _
    _ ≤ ‖sLow‖ + 1 := add_le_add_right hdelta _
    _ ≤ 3 * ‖sLow‖ := by linarith

/-- Reciprocal form of `norm_sourceHigh_le_three_mul_norm_sourceLow`.
This is the denominator comparison used after A.13--A.14. -/
theorem inv_norm_sourceLow_le_three_div_norm_sourceHigh
    {c alpha beta t : ℝ}
    (hhalf : 1 / 2 ≤ c - alpha - beta)
    (hshift0 : 0 ≤ alpha + 2 * beta)
    (hshift : alpha + 2 * beta ≤ 1) :
    (‖(((c - alpha - beta : ℝ) : ℂ) +
        Complex.I * (t : ℂ))‖)⁻¹ ≤
      3 / ‖(((c + beta : ℝ) : ℂ) +
        Complex.I * (t : ℂ))‖ := by
  let sLow : ℂ := ((c - alpha - beta : ℝ) : ℂ) +
    Complex.I * (t : ℂ)
  let sHigh : ℂ := ((c + beta : ℝ) : ℂ) +
    Complex.I * (t : ℂ)
  have hlowRe : 0 < sLow.re := by simp [sLow]; linarith
  have hhighRe : 0 < sHigh.re := by
    simp only [sHigh, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.I_re, Complex.I_im, Complex.ofReal_im, zero_mul, one_mul,
      sub_zero, add_zero]
    linarith
  have hlowNorm : 0 < ‖sLow‖ := by
    exact (abs_pos.mpr (ne_of_gt hlowRe)).trans_le
      (Complex.abs_re_le_norm sLow)
  have hhighNorm : 0 < ‖sHigh‖ := by
    exact (abs_pos.mpr (ne_of_gt hhighRe)).trans_le
      (Complex.abs_re_le_norm sHigh)
  have hcomp : ‖sHigh‖ ≤ 3 * ‖sLow‖ := by
    simpa only [sLow, sHigh] using
      (norm_sourceHigh_le_three_mul_norm_sourceLow
        hhalf hshift0 hshift)
  rw [inv_eq_one_div]
  exact (div_le_div_iff₀ hlowNorm hhighNorm).2 (by simpa using hcomp)

/-- Deleted source coefficient: exact A.13--A.14 with the Perron
denominator retained and compared to the shifted high-line denominator. -/
theorem norm_deleted_sourceLowHigh_div_sourceLow_le_envelope
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    (P₁ P₂ : ℕ → Prop) [DecidablePred P₁] [DecidablePred P₂]
    {y X : ℕ} (hy : 23 ≤ y) (hX : 1 < X)
    {alpha beta t : ℝ} (hlogy : 4 ≤ Real.log (y : ℝ))
    (halpha0 : 0 ≤ alpha)
    (halpha : alpha ≤ (Real.log (y : ℝ))⁻¹)
    (hbeta0 : 0 ≤ beta)
    (hbeta : beta ≤ (Real.log (y : ℝ))⁻¹) :
    let g := gsA10SourceDeleted f
    let c₀ := Erdos67.EulerResidue.taoExponent X
    let sLow : ℂ := ((c₀ - alpha - beta : ℝ) : ℂ) +
      Complex.I * (t : ℂ)
    let sHigh : ℂ := ((c₀ + beta : ℝ) : ℂ) +
      Complex.I * (t : ℂ)
    ‖(LSeries (gsA10TwoBlockAlternatingLow g P₁ P₂ y) sLow *
        LSeries (gsA9HighArithmetic g y) sHigh) / sLow‖ ≤
      3 * gsA10SourcePerronEnvelope f X beta t := by
  dsimp only
  let g : ℕ → ℂ := gsA10SourceDeleted f
  let c₀ : ℝ := Erdos67.EulerResidue.taoExponent X
  let sigmaLow : ℝ := c₀ - alpha - beta
  let sLow : ℂ := (sigmaLow : ℂ) + Complex.I * (t : ℂ)
  let sHigh : ℂ := ((c₀ + beta : ℝ) : ℂ) + Complex.I * (t : ℂ)
  let core : ℝ := gsA10SourceWindowCoreBudget f y X beta t
  have hetaQuarter : (Real.log (y : ℝ))⁻¹ ≤ 1 / 4 := by
    simpa only [one_div] using
      inv_anti₀ (by norm_num : (0 : ℝ) < 4) hlogy
  have hlogX : 0 < Real.log (X : ℝ) :=
    Real.log_pos (by exact_mod_cast hX)
  have hcOne : 1 ≤ c₀ := by
    dsimp only [c₀, Erdos67.EulerResidue.taoExponent]
    exact le_add_of_nonneg_right (inv_pos.mpr hlogX).le
  have hhalf : 1 / 2 ≤ sigmaLow := by
    dsimp only [sigmaLow]
    have hab : alpha + beta ≤ 2 * (Real.log (y : ℝ))⁻¹ := by linarith
    linarith
  have hshift0 : 0 ≤ alpha + 2 * beta := by linarith
  have hshift : alpha + 2 * beta ≤ 1 := by linarith
  have hlowNorm : 0 < ‖sLow‖ := by
    have hre : 0 < sLow.re := by simp [sLow, sigmaLow]; linarith
    exact (abs_pos.mpr (ne_of_gt hre)).trans_le
      (Complex.abs_re_le_norm sLow)
  have hcore0 : 0 ≤ core := by
    dsimp only [core, gsA10SourceWindowCoreBudget]
    positivity
  have hsource :
      ‖LSeries (gsA10TwoBlockAlternatingLow g P₁ P₂ y) sLow *
          LSeries (gsA9HighArithmetic g y) sHigh‖ ≤ core := by
    simpa only [g, c₀, sigmaLow, sLow, sHigh, core,
      gsA10SourceWindowCoreBudget] using
      (norm_LSeries_gsA10TwoBlockAlternatingLow_mul_high_le_sourceWindow
        hmul hbound P₁ P₂ hy hX hlogy halpha0 halpha hbeta0 hbeta
        (t := t))
  have hinv := inv_norm_sourceLow_le_three_div_norm_sourceHigh
    (c := c₀) (alpha := alpha) (beta := beta) (t := t)
    (by simpa only [sigmaLow] using hhalf) hshift0 hshift
  rw [norm_div]
  calc
    ‖LSeries (gsA10TwoBlockAlternatingLow g P₁ P₂ y) sLow *
          LSeries (gsA9HighArithmetic g y) sHigh‖ / ‖sLow‖ ≤
        core / ‖sLow‖ := div_le_div_of_nonneg_right hsource hlowNorm.le
    _ = core * (‖sLow‖)⁻¹ := by rw [div_eq_mul_inv]
    _ ≤ core * (3 / ‖sHigh‖) :=
      mul_le_mul_of_nonneg_left (by simpa only [sLow, sHigh] using hinv) hcore0
    _ = 3 * gsA10SourcePerronEnvelope f X beta t := by
      unfold gsA10SourcePerronEnvelope
      dsimp only [c₀]
      rw [show gsA10SourceWindowCoreBudget f 0 X beta t =
          gsA10SourceWindowCoreBudget f y X beta t by rfl]
      dsimp only [core, sHigh]
      ring

/-- The preceding denominator estimate with the exact Perron power
retained. -/
theorem norm_deleted_sourceLowHigh_mul_perronKernel_le_envelope
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    (P₁ P₂ : ℕ → Prop) [DecidablePred P₁] [DecidablePred P₂]
    {y X : ℕ} (hy : 23 ≤ y) (hX : 1 < X)
    {alpha beta t : ℝ} (hlogy : 4 ≤ Real.log (y : ℝ))
    (halpha0 : 0 ≤ alpha)
    (halpha : alpha ≤ (Real.log (y : ℝ))⁻¹)
    (hbeta0 : 0 ≤ beta)
    (hbeta : beta ≤ (Real.log (y : ℝ))⁻¹) :
    let g := gsA10SourceDeleted f
    let c₀ := Erdos67.EulerResidue.taoExponent X
    let sigmaLow := c₀ - alpha - beta
    let sLow : ℂ := (sigmaLow : ℂ) + Complex.I * (t : ℂ)
    let sHigh : ℂ := ((c₀ + beta : ℝ) : ℂ) + Complex.I * (t : ℂ)
    ‖(LSeries (gsA10TwoBlockAlternatingLow g P₁ P₂ y) sLow *
        LSeries (gsA9HighArithmetic g y) sHigh) *
        (X : ℂ) ^ sLow / sLow‖ ≤
      3 * (X : ℝ) ^ sigmaLow *
        gsA10SourcePerronEnvelope f X beta t := by
  dsimp only
  let g : ℕ → ℂ := gsA10SourceDeleted f
  let c₀ : ℝ := Erdos67.EulerResidue.taoExponent X
  let sigmaLow : ℝ := c₀ - alpha - beta
  let sLow : ℂ := (sigmaLow : ℂ) + Complex.I * (t : ℂ)
  let sHigh : ℂ := ((c₀ + beta : ℝ) : ℂ) + Complex.I * (t : ℂ)
  have hbase := norm_deleted_sourceLowHigh_div_sourceLow_le_envelope
    hmul hbound P₁ P₂ hy hX hlogy halpha0 halpha hbeta0 hbeta (t := t)
  have hXpos : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
  have hpow : ‖(X : ℂ) ^ sLow‖ = (X : ℝ) ^ sigmaLow := by
    have hcast : (X : ℂ) = ((X : ℝ) : ℂ) := by norm_num
    rw [hcast]
    simpa only [sLow, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.I_re, Complex.I_im, Complex.ofReal_im, zero_mul, one_mul,
      sub_zero, add_zero] using
      Complex.norm_cpow_eq_rpow_re_of_pos hXpos sLow
  have henv0 : 0 ≤ gsA10SourcePerronEnvelope f X beta t := by
    unfold gsA10SourcePerronEnvelope gsA10SourceWindowCoreBudget
    positivity
  have hrearrange :
      (LSeries (gsA10TwoBlockAlternatingLow g P₁ P₂ y) sLow *
          LSeries (gsA9HighArithmetic g y) sHigh) *
          (X : ℂ) ^ sLow / sLow =
        ((LSeries (gsA10TwoBlockAlternatingLow g P₁ P₂ y) sLow *
          LSeries (gsA9HighArithmetic g y) sHigh) / sLow) *
          (X : ℂ) ^ sLow := by
    field_simp
  rw [hrearrange, norm_mul, hpow]
  calc
    ‖(LSeries (gsA10TwoBlockAlternatingLow g P₁ P₂ y) sLow *
          LSeries (gsA9HighArithmetic g y) sHigh) / sLow‖ *
        (X : ℝ) ^ sigmaLow ≤
      (3 * gsA10SourcePerronEnvelope f X beta t) *
        (X : ℝ) ^ sigmaLow := by
          exact mul_le_mul_of_nonneg_right
            (by simpa only [g, c₀, sigmaLow, sLow, sHigh] using hbase)
            (Real.rpow_nonneg (by positivity) _)
    _ = 3 * (X : ℝ) ^ sigmaLow *
        gsA10SourcePerronEnvelope f X beta t := by ring

/-- Restored source coefficient.  The finitely many primes below `23`
cost exactly one copy of `gsA9SmallPrimeEulerBound`; the beta-dependent
full deleted L-series and the shifted Perron denominator remain visible. -/
theorem norm_sourceLowHigh_mul_perronKernel_le_restoredEnvelope
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    (P₁ P₂ : ℕ → Prop) [DecidablePred P₁] [DecidablePred P₂]
    (hsmallOutside : ∀ p ∈ gsA9SmallPrimeFinset, P₁ p)
    {y X : ℕ} (hy : 23 ≤ y) (hX : 1 < X)
    {alpha beta t : ℝ} (hlogy : 4 ≤ Real.log (y : ℝ))
    (halpha0 : 0 ≤ alpha)
    (halpha : alpha ≤ (Real.log (y : ℝ))⁻¹)
    (hbeta0 : 0 ≤ beta)
    (hbeta : beta ≤ (Real.log (y : ℝ))⁻¹) :
    let c₀ := Erdos67.EulerResidue.taoExponent X
    let sigmaLow := c₀ - alpha - beta
    let sLow : ℂ := (sigmaLow : ℂ) + Complex.I * (t : ℂ)
    let sHigh : ℂ := ((c₀ + beta : ℝ) : ℂ) + Complex.I * (t : ℂ)
    ‖(LSeries (gsA10TwoBlockAlternatingLow f P₁ P₂ y) sLow *
        LSeries (gsA9HighArithmetic f y) sHigh) *
        (X : ℂ) ^ sLow / sLow‖ ≤
      3 * gsA9SmallPrimeEulerBound * (X : ℝ) ^ sigmaLow *
        gsA10SourcePerronEnvelope f X beta t := by
  dsimp only
  let g : ℕ → ℂ := gsA10SourceDeleted f
  let c₀ : ℝ := Erdos67.EulerResidue.taoExponent X
  let sigmaLow : ℝ := c₀ - alpha - beta
  let sLow : ℂ := (sigmaLow : ℂ) + Complex.I * (t : ℂ)
  let sHigh : ℂ := ((c₀ + beta : ℝ) : ℂ) + Complex.I * (t : ℂ)
  have hetaQuarter : (Real.log (y : ℝ))⁻¹ ≤ 1 / 4 := by
    simpa only [one_div] using
      inv_anti₀ (by norm_num : (0 : ℝ) < 4) hlogy
  have hlogX : 0 < Real.log (X : ℝ) :=
    Real.log_pos (by exact_mod_cast hX)
  have hcOne : 1 ≤ c₀ := by
    dsimp only [c₀, Erdos67.EulerResidue.taoExponent]
    exact le_add_of_nonneg_right (inv_pos.mpr hlogX).le
  have hhalf : 1 / 2 ≤ sigmaLow := by
    dsimp only [sigmaLow]
    have hab : alpha + beta ≤ 2 * (Real.log (y : ℝ))⁻¹ := by linarith
    linarith
  have hsLow : 0 < sLow.re := by simp [sLow, sigmaLow]; linarith
  have hrestore := LSeries_twoBlockAlternatingLow_eq_smallPrime_mul_delete
    hmul hbound P₁ P₂ hy hsmallOutside hsLow
  have hrestore' :
      LSeries (gsA10TwoBlockAlternatingLow f P₁ P₂ y) sLow =
        gsA9SmallPrimeEulerProduct f sLow *
          LSeries (gsA10TwoBlockAlternatingLow g P₁ P₂ y) sLow := by
    simpa only [g, gsA10SourceDeleted] using hrestore
  have hhighCoeff : gsA9High g y = gsA9High f y := by
    exact gsA9High_deleteSmallPrimes_eq f hy
  have hhighSeries :
      LSeries (gsA9HighArithmetic f y) sHigh =
        LSeries (gsA9HighArithmetic g y) sHigh := by
    rw [LSeries_gsA9HighArithmetic, LSeries_gsA9HighArithmetic,
      hhighCoeff]
  have hbase := norm_deleted_sourceLowHigh_mul_perronKernel_le_envelope
    hmul hbound P₁ P₂ hy hX hlogy halpha0 halpha hbeta0 hbeta (t := t)
  have hsmall : ‖gsA9SmallPrimeEulerProduct f sLow‖ ≤
      gsA9SmallPrimeEulerBound := by
    simpa only [sLow] using
      (norm_gsA9SmallPrimeEulerProduct_le hbound (t := t) hhalf)
  have hsmall0 : 0 ≤ gsA9SmallPrimeEulerBound :=
    (norm_nonneg _).trans hsmall
  have hfactor :
      (LSeries (gsA10TwoBlockAlternatingLow f P₁ P₂ y) sLow *
          LSeries (gsA9HighArithmetic f y) sHigh) *
          (X : ℂ) ^ sLow / sLow =
        gsA9SmallPrimeEulerProduct f sLow *
          ((LSeries (gsA10TwoBlockAlternatingLow g P₁ P₂ y) sLow *
              LSeries (gsA9HighArithmetic g y) sHigh) *
            (X : ℂ) ^ sLow / sLow) := by
    rw [hrestore', hhighSeries]
    ring
  rw [hfactor, norm_mul]
  calc
    ‖gsA9SmallPrimeEulerProduct f sLow‖ *
          ‖(LSeries (gsA10TwoBlockAlternatingLow g P₁ P₂ y) sLow *
              LSeries (gsA9HighArithmetic g y) sHigh) *
            (X : ℂ) ^ sLow / sLow‖ ≤
        gsA9SmallPrimeEulerBound *
          (3 * (X : ℝ) ^ sigmaLow *
            gsA10SourcePerronEnvelope f X beta t) := by
      apply mul_le_mul hsmall
        (by simpa only [g, c₀, sigmaLow, sLow, sHigh] using hbase)
      · exact norm_nonneg _
      · exact hsmall0
    _ = 3 * gsA9SmallPrimeEulerBound * (X : ℝ) ^ sigmaLow *
        gsA10SourcePerronEnvelope f X beta t := by ring

/-- Source A.10 contour inequality before estimating the two finite
Mangoldt windows.  The beta- and t-dependent A.13--A.14 envelope, including
the shifted denominator, stays inside the sole remaining vertical
integral. -/
theorem norm_gsA10SourceTailoredPerronIntegral_le_weightedLambdaIntegral
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    (P₁ P₂ : ℕ → Prop) [DecidablePred P₁] [DecidablePred P₂]
    (hsmallOutside : ∀ p ∈ gsA9SmallPrimeFinset, P₁ p)
    {y X : ℕ} (hy : 23 ≤ y) (hX : 1 < X)
    {alpha beta T : ℝ} (hlogy : 4 ≤ Real.log (y : ℝ))
    (halpha0 : 0 ≤ alpha)
    (halpha : alpha ≤ (Real.log (y : ℝ))⁻¹)
    (hbeta0 : 0 ≤ beta)
    (hbeta : beta ≤ (Real.log (y : ℝ))⁻¹)
    (hT : 0 ≤ T)
    (hweighted : IntervalIntegrable
      (fun t : ℝ ↦
        (3 * gsA9SmallPrimeEulerBound *
            (X : ℝ) ^
              (Erdos67.EulerResidue.taoExponent X - alpha - beta) *
            gsA10SourcePerronEnvelope f X beta t) *
          gsA10SourceLambdaPairNorm f hmul y X beta t)
      volume (-T) T) :
    ‖gsA10TailoredPerronIntegral
        (gsA10TwoBlockAlternatingLow f P₁ P₂ y)
        (gsA9HighArithmetic f y)
        (gsA9HighGeneralizedMangoldt hmul y)
        y X (Erdos67.EulerResidue.taoExponent X) alpha beta T‖ ≤
      (2 * Real.pi)⁻¹ *
        ∫ t in -T..T,
          (3 * gsA9SmallPrimeEulerBound *
              (X : ℝ) ^
                (Erdos67.EulerResidue.taoExponent X - alpha - beta) *
              gsA10SourcePerronEnvelope f X beta t) *
            gsA10SourceLambdaPairNorm f hmul y X beta t := by
  let c₀ : ℝ := Erdos67.EulerResidue.taoExponent X
  let sigmaLow : ℝ := c₀ - alpha - beta
  let W : ArithmeticFunction ℂ :=
    gsA10LambdaWindow (gsA9HighGeneralizedMangoldt hmul y) y X
  have hetaQuarter : (Real.log (y : ℝ))⁻¹ ≤ 1 / 4 := by
    simpa only [one_div] using
      inv_anti₀ (by norm_num : (0 : ℝ) < 4) hlogy
  have hlogX : 0 < Real.log (X : ℝ) :=
    Real.log_pos (by exact_mod_cast hX)
  have hcOne : 1 ≤ c₀ := by
    dsimp only [c₀, Erdos67.EulerResidue.taoExponent]
    exact le_add_of_nonneg_right (inv_pos.mpr hlogX).le
  have hlow : 0 < c₀ - alpha - beta := by
    have hab : alpha + beta ≤ 2 * (Real.log (y : ℝ))⁻¹ := by linarith
    linarith
  have hhigh : 1 < c₀ + beta := by
    have hcStrict : 1 < c₀ := by
      dsimp only [c₀, Erdos67.EulerResidue.taoExponent]
      linarith [inv_pos.mpr hlogX]
    linarith
  have hfour := gsA10TwoBlockTailoredPerronIntegral_eq_fourFactors
    hmul hbound P₁ P₂ y X c₀ alpha beta T hT hlow hhigh
  rw [show Erdos67.EulerResidue.taoExponent X = c₀ by rfl, hfour,
    norm_mul]
  have hscalar :
      ‖(((2 * Real.pi : ℝ) : ℂ)⁻¹)‖ = (2 * Real.pi)⁻¹ := by
    have hpi : 0 ≤ 2 * Real.pi := by positivity
    rw [norm_inv, Complex.norm_real, Real.norm_of_nonneg hpi]
  rw [hscalar]
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (by positivity))
  apply intervalIntegral.norm_integral_le_of_norm_le (by linarith : -T ≤ T)
  · filter_upwards with t ht
    have ht' : t ∈ Set.Icc (-T) T := ⟨ht.1.le, ht.2⟩
    let sLow : ℂ := (sigmaLow : ℂ) + Complex.I * (t : ℂ)
    let sHigh : ℂ := ((c₀ + beta : ℝ) : ℂ) + Complex.I * (t : ℂ)
    let sWindowLow : ℂ := ((c₀ - beta : ℝ) : ℂ) +
      Complex.I * (t : ℂ)
    have hbase := norm_sourceLowHigh_mul_perronKernel_le_restoredEnvelope
      hmul hbound P₁ P₂ hsmallOutside hy hX hlogy
      halpha0 halpha hbeta0 hbeta (t := t)
    have hsLowEq :
        (((c₀ - alpha - beta : ℝ) : ℂ) + (t : ℂ) * Complex.I) =
          sLow := by
      dsimp only [sLow, sigmaLow]
      ring
    have hsHighEq :
        (((c₀ - alpha - beta : ℝ) : ℂ) + (t : ℂ) * Complex.I) +
            ((alpha + 2 * beta : ℝ) : ℂ) = sHigh := by
      apply Complex.ext <;>
        simp only [sHigh, Complex.add_re, Complex.add_im,
          Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re,
          Complex.mul_im, Complex.I_re, Complex.I_im, zero_mul, one_mul,
          mul_zero, add_zero, zero_add, sub_zero] <;> ring
    have hsWindowLowEq :
        (((c₀ - alpha - beta : ℝ) : ℂ) + (t : ℂ) * Complex.I) +
            (alpha : ℂ) = sWindowLow := by
      apply Complex.ext <;>
        simp only [sWindowLow, Complex.add_re, Complex.add_im,
          Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re,
          Complex.mul_im, Complex.I_re, Complex.I_im, zero_mul, one_mul,
          mul_zero, add_zero, zero_add, sub_zero] <;> ring
    have hsHighEq' : sLow + ((alpha + 2 * beta : ℝ) : ℂ) = sHigh := by
      rw [← hsLowEq]
      exact hsHighEq
    have hsWindowLowEq' : sLow + (alpha : ℂ) = sWindowLow := by
      rw [← hsLowEq]
      exact hsWindowLowEq
    rw [hsLowEq, hsHighEq', hsWindowLowEq']
    have hrearrange :
        ((LSeries (gsA10TwoBlockAlternatingLow f P₁ P₂ y) sLow *
            LSeries (gsA9HighArithmetic f y) sHigh) *
          (LSeries W sWindowLow * LSeries W sHigh)) *
            (X : ℂ) ^ sLow / sLow =
          ((LSeries (gsA10TwoBlockAlternatingLow f P₁ P₂ y) sLow *
              LSeries (gsA9HighArithmetic f y) sHigh) *
            (X : ℂ) ^ sLow / sLow) *
              (LSeries W sWindowLow * LSeries W sHigh) := by ring
    rw [hrearrange, norm_mul]
    exact mul_le_mul_of_nonneg_right
      (by simpa only [c₀, sigmaLow, sLow, sHigh] using hbase)
      (norm_nonneg _)
  · simpa only [c₀, sigmaLow, W, gsA10SourceLambdaPairNorm] using hweighted

/-- Continuity-discharged form of the source weighted contour inequality. -/
theorem norm_gsA10SourceTailoredPerronIntegral_le_weightedLambdaIntegral_continuous
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    (P₁ P₂ : ℕ → Prop) [DecidablePred P₁] [DecidablePred P₂]
    (hsmallOutside : ∀ p ∈ gsA9SmallPrimeFinset, P₁ p)
    {y X : ℕ} (hy : 23 ≤ y) (hX : 1 < X)
    {alpha beta T : ℝ} (hlogy : 4 ≤ Real.log (y : ℝ))
    (halpha0 : 0 ≤ alpha)
    (halpha : alpha ≤ (Real.log (y : ℝ))⁻¹)
    (hbeta0 : 0 ≤ beta)
    (hbeta : beta ≤ (Real.log (y : ℝ))⁻¹)
    (hT : 0 ≤ T) :
    ‖gsA10TailoredPerronIntegral
        (gsA10TwoBlockAlternatingLow f P₁ P₂ y)
        (gsA9HighArithmetic f y)
        (gsA9HighGeneralizedMangoldt hmul y)
        y X (Erdos67.EulerResidue.taoExponent X) alpha beta T‖ ≤
      (2 * Real.pi)⁻¹ *
        ∫ t in -T..T,
          (3 * gsA9SmallPrimeEulerBound *
              (X : ℝ) ^
                (Erdos67.EulerResidue.taoExponent X - alpha - beta) *
              gsA10SourcePerronEnvelope f X beta t) *
            gsA10SourceLambdaPairNorm f hmul y X beta t := by
  have henv := continuous_gsA10SourcePerronEnvelope hbound hX hbeta0
  have hpair := continuous_gsA10SourceLambdaPairNorm hmul y X beta
  have hconst : Continuous (fun _ : ℝ ↦
      3 * gsA9SmallPrimeEulerBound *
        (X : ℝ) ^
          (Erdos67.EulerResidue.taoExponent X - alpha - beta)) :=
    continuous_const
  have hweighted : IntervalIntegrable
      (fun t : ℝ ↦
        (3 * gsA9SmallPrimeEulerBound *
            (X : ℝ) ^
              (Erdos67.EulerResidue.taoExponent X - alpha - beta) *
            gsA10SourcePerronEnvelope f X beta t) *
          gsA10SourceLambdaPairNorm f hmul y X beta t)
      volume (-T) T := by
    exact ((hconst.mul henv).mul hpair).intervalIntegrable _ _
  exact norm_gsA10SourceTailoredPerronIntegral_le_weightedLambdaIntegral
    hmul hbound P₁ P₂ hsmallOutside hy hX hlogy
    halpha0 halpha hbeta0 hbeta hT hweighted

end

end Erdos67.MRHalaszBands

#print axioms
  Erdos67.MRHalaszBands.norm_gsA10SourceTailoredPerronIntegral_le_weightedLambdaIntegral_continuous
