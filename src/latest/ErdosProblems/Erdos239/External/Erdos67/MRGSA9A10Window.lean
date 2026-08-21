import ErdosProblems.Erdos239.External.Erdos67.MRGSA9A13A14Source

/-!
# The exact A.10 alpha--beta window for A.13--A.14

This specializes the shifted source estimate to
`sigmaLow = c₀ - alpha - beta` and `sigmaHigh = c₀ + beta`, where
`c₀ = 1 + 1 / log X` and `alpha,beta ∈ [0,1/log y]`.
-/

open scoped LSeries.notation

namespace Erdos67.MRHalaszBands

noncomputable section

/-- Complete source A.13--A.14 estimate on the actual A.10 averaging
rectangle.  The elementary line-location, radius, and gap checks are all
internal. -/
theorem norm_twoBlock_alternatingLow_deleteSmallPrimes_mul_high_le_A10Window
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    (Q₂ Q₃ : ℕ → Prop) [DecidablePred Q₂] [DecidablePred Q₃]
    {y : ℕ} (hy : 23 ≤ y)
    (hdisj : ∀ p ∈ primesUpTo y, Q₂ p → Q₃ p → False)
    {X : ℕ} (hX : 1 < X)
    {alpha beta t : ℝ}
    (hlogy : 4 ≤ Real.log (y : ℝ))
    (halpha0 : 0 ≤ alpha)
    (halpha : alpha ≤ (Real.log (y : ℝ))⁻¹)
    (hbeta0 : 0 ≤ beta)
    (hbeta : beta ≤ (Real.log (y : ℝ))⁻¹) :
    let g := gsDeletePrimeBand f gsA9SmallPrime
    let c₀ := Erdos67.EulerResidue.taoExponent X
    let sigmaLow := c₀ - alpha - beta
    let sigmaHigh := c₀ + beta
    let sLow : ℂ := (sigmaLow : ℂ) + Complex.I * (t : ℂ)
    let sHigh : ℂ := (sigmaHigh : ℂ) + Complex.I * (t : ℂ)
    let Alt := LSeries (gsA9Low g y) sLow -
        LSeries (gsA9LowDeletion g Q₂ y) sLow -
        LSeries (gsA9LowDeletion g Q₃ y) sLow +
        LSeries (gsA9LowDeletion g (fun p ↦ Q₂ p ∨ Q₃ p) y) sLow
    ‖Alt * LSeries (gsA9High g y) sHigh‖ ≤
      Real.exp
          (28 * Real.exp 4 *
              Erdos67.EulerQuantitative.primeQuadraticConstant +
            36 * gsA9SourceShiftConstant) *
        Real.sqrt ‖LSeries g sHigh‖ *
        Real.sqrt ‖riemannZeta (sigmaHigh : ℂ)‖ := by
  dsimp only
  let c₀ : ℝ := Erdos67.EulerResidue.taoExponent X
  let eta : ℝ := (Real.log (y : ℝ))⁻¹
  let sigmaLow : ℝ := c₀ - alpha - beta
  let sigmaHigh : ℝ := c₀ + beta
  have hlogyPos : 0 < Real.log (y : ℝ) := lt_of_lt_of_le (by norm_num) hlogy
  have heta0 : 0 ≤ eta := (inv_pos.mpr hlogyPos).le
  have hetaQuarter : eta ≤ 1 / 4 := by
    dsimp only [eta]
    simpa only [one_div] using inv_anti₀ (by norm_num : (0 : ℝ) < 4) hlogy
  have hc₀one : 1 ≤ c₀ := by
    dsimp only [c₀, Erdos67.EulerResidue.taoExponent]
    have hlogX : 0 < Real.log (X : ℝ) :=
      Real.log_pos (by exact_mod_cast hX)
    exact le_add_of_nonneg_right (inv_pos.mpr hlogX).le
  have hhalf : 1 / 2 ≤ sigmaLow := by
    dsimp only [sigmaLow]
    have hab : alpha + beta ≤ 2 * eta := by
      dsimp only [eta]
      linarith
    linarith
  have hle : sigmaLow ≤ sigmaHigh := by
    dsimp only [sigmaLow, sigmaHigh]
    linarith
  have hsigmaLow : 1 - 2 / Real.log (y : ℝ) ≤ sigmaLow := by
    dsimp only [sigmaLow]
    have hab : alpha + beta ≤ 2 / Real.log (y : ℝ) := by
      have ha := halpha
      have hb := hbeta
      calc
        alpha + beta ≤ (Real.log (y : ℝ))⁻¹ +
            (Real.log (y : ℝ))⁻¹ := add_le_add ha hb
        _ = 2 / Real.log (y : ℝ) := by field_simp; norm_num
    linarith
  have hgap : sigmaHigh - sigmaLow ≤ 3 / Real.log (y : ℝ) := by
    dsimp only [sigmaLow, sigmaHigh]
    have ha := halpha
    have hb := hbeta
    rw [show (Real.log (y : ℝ))⁻¹ = 1 / Real.log (y : ℝ) by
      simp only [one_div]] at ha hb
    have hthree : 3 / Real.log (y : ℝ) =
        3 * (Real.log (y : ℝ))⁻¹ := by field_simp
    rw [hthree]
    rw [one_div] at ha hb
    linarith
  have hsigmaHigh : 1 < sigmaHigh := by
    dsimp only [sigmaHigh, c₀, Erdos67.EulerResidue.taoExponent]
    have hlogX : 0 < Real.log (X : ℝ) :=
      Real.log_pos (by exact_mod_cast hX)
    have hinv : 0 < (Real.log (X : ℝ))⁻¹ := inv_pos.mpr hlogX
    linarith
  exact norm_twoBlock_alternatingLow_deleteSmallPrimes_mul_high_le_source_scalar
    hmul hbound Q₂ Q₃ hy hdisj hhalf hle hsigmaLow hgap hsigmaHigh

end

end Erdos67.MRHalaszBands
