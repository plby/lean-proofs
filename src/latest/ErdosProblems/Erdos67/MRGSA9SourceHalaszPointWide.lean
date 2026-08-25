import ErdosProblems.Erdos67.MRGSA9SourceRadiusWide
import ErdosProblems.Erdos67.MRGSA9SourceHalaszPoint

/-!
# A.9 at the widened low line and fixed Halasz high line

This is the source A.13--A.14 estimate needed by the beta-dependent A.10
Perron line.  The high factor remains exactly at `taoExponent X + it`; only
the finite low Euler factor moves as far left as `1 - 3 / log y`.
-/

open scoped BigOperators LSeries.notation

namespace Erdos67.MRHalaszBands

noncomputable section

/-- The absolute Euler-product constant on the widened source line. -/
def gsA9WideSourceEulerConstant : ℝ :=
  Real.exp
    (28 * Real.exp 6 *
        Erdos67.EulerQuantitative.primeQuadraticConstant +
      36 * gsA9WideSourceShiftConstant)

/-- The finite three-block A.13 estimate with widened source-line
hypotheses discharged. -/
theorem norm_threeEulerBlockAlternating_sq_le_wideSource_shifted_full_products
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    {y : ℕ} (hy : 2 ≤ y)
    (S₀ S₂ S₃ : Finset ℕ)
    (hS₀ : S₀ ⊆ primesUpTo y) (hS₂ : S₂ ⊆ primesUpTo y)
    (hS₃ : S₃ ⊆ primesUpTo y)
    (hlarge₀ : ∀ p ∈ S₀, 23 ≤ p)
    (hlarge₂ : ∀ p ∈ S₂, 23 ≤ p)
    (hlarge₃ : ∀ p ∈ S₃, 23 ≤ p)
    {sigmaLow sigmaHigh t : ℝ}
    (hhalf : 1 / 2 ≤ sigmaLow)
    (hle : sigmaLow ≤ sigmaHigh)
    (hsigma : 1 - 3 / Real.log (y : ℝ) ≤ sigmaLow)
    (hgap : sigmaHigh - sigmaLow ≤ 3 / Real.log (y : ℝ)) :
    let sLow : ℂ := (sigmaLow : ℂ) + Complex.I * (t : ℂ)
    let sHigh : ℂ := (sigmaHigh : ℂ) + Complex.I * (t : ℂ)
    let one : ℕ → ℂ := fun _ ↦ 1
    let P₀ := ∏ p ∈ S₀, gsA9LocalEulerFactor f sLow p
    let P₂ := ∏ p ∈ S₂, gsA9LocalEulerFactor f sLow p
    let P₃ := ∏ p ∈ S₃, gsA9LocalEulerFactor f sLow p
    let Q₀ := ∏ p ∈ S₀, gsA9LocalEulerFactor f sHigh p
    let Q₂ := ∏ p ∈ S₂, gsA9LocalEulerFactor f sHigh p
    let Q₃ := ∏ p ∈ S₃, gsA9LocalEulerFactor f sHigh p
    let Q₀p := ∏ p ∈ S₀, gsA9LocalEulerFactor one (sigmaHigh : ℂ) p
    let Q₂p := ∏ p ∈ S₂, gsA9LocalEulerFactor one (sigmaHigh : ℂ) p
    let Q₃p := ∏ p ∈ S₃, gsA9LocalEulerFactor one (sigmaHigh : ℂ) p
    let V₀ := ∑ p ∈ S₀, ‖(p : ℂ) ^ (-sLow)‖ ^ 2
    let V₂ := ∑ p ∈ S₂, ‖(p : ℂ) ^ (-sLow)‖ ^ 2
    let V₃ := ∑ p ∈ S₃, ‖(p : ℂ) ^ (-sLow)‖ ^ 2
    ‖P₀ * (P₂ - 1) * (P₃ - 1)‖ ^ 2 ≤
      Real.exp (7 * V₀ + 24 * (V₂ + V₃) +
        36 * gsA9WideSourceShiftConstant) *
        ‖Q₀ * Q₂ * Q₃‖ * ‖Q₀p * Q₂p * Q₃p‖ := by
  apply norm_threeEulerBlockAlternating_sq_le_shifted_full_products
    hmul hbound S₀ S₂ S₃
  · intro p hp
    exact (mem_primesUpTo.mp (hS₀ hp)).1
  · intro p hp
    exact (mem_primesUpTo.mp (hS₂ hp)).1
  · intro p hp
    exact (mem_primesUpTo.mp (hS₃ hp)).1
  · exact hle
  · intro p hp
    exact norm_prime_cpow_le_one_third_of_twenty_three_le
      (mem_primesUpTo.mp (hS₀ hp)).1 (hlarge₀ p hp) hhalf
  · intro p hp
    exact norm_prime_cpow_le_one_third_of_twenty_three_le
      (mem_primesUpTo.mp (hS₂ hp)).1 (hlarge₂ p hp) hhalf
  · intro p hp
    exact norm_prime_cpow_le_one_third_of_twenty_three_le
      (mem_primesUpTo.mp (hS₃ hp)).1 (hlarge₃ p hp) hhalf
  · exact sum_prime_radial_norm_sub_subset_wideSourceGap_le_constant
      hy S₀ hS₀ hle hsigma hgap
  · exact sum_prime_radial_norm_sub_subset_wideSourceGap_le_constant
      hy S₂ hS₂ hle hsigma hgap
  · exact sum_prime_radial_norm_sub_subset_wideSourceGap_le_constant
      hy S₃ hS₃ hle hsigma hgap

/-- Widened A.13--A.14 after fixed small-prime deletion, in squared scalar
form. -/
theorem norm_twoBlock_alternatingLow_deleteSmallPrimes_mul_high_sq_le_wideSource
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    (Q₂ Q₃ : ℕ → Prop) [DecidablePred Q₂] [DecidablePred Q₃]
    {y : ℕ} (hy : 23 ≤ y)
    (hdisj : ∀ p ∈ primesUpTo y, Q₂ p → Q₃ p → False)
    {sigmaLow sigmaHigh t : ℝ}
    (hhalf : 1 / 2 ≤ sigmaLow)
    (hle : sigmaLow ≤ sigmaHigh)
    (hsigmaLow : 1 - 3 / Real.log (y : ℝ) ≤ sigmaLow)
    (hgap : sigmaHigh - sigmaLow ≤ 3 / Real.log (y : ℝ))
    (hsigmaHigh : 1 < sigmaHigh) :
    let g := gsDeletePrimeBand f gsA9SmallPrime
    let sLow : ℂ := (sigmaLow : ℂ) + Complex.I * (t : ℂ)
    let sHigh : ℂ := (sigmaHigh : ℂ) + Complex.I * (t : ℂ)
    let Alt := LSeries (gsA9Low g y) sLow -
        LSeries (gsA9LowDeletion g Q₂ y) sLow -
        LSeries (gsA9LowDeletion g Q₃ y) sLow +
        LSeries (gsA9LowDeletion g (fun p ↦ Q₂ p ∨ Q₃ p) y) sLow
    ‖Alt * LSeries (gsA9High g y) sHigh‖ ^ 2 ≤
      gsA9WideSourceEulerConstant *
        ‖LSeries g sHigh‖ * ‖riemannZeta (sigmaHigh : ℂ)‖ := by
  dsimp only
  let g : ℕ → ℂ := gsDeletePrimeBand f gsA9SmallPrime
  let sLow : ℂ := (sigmaLow : ℂ) + Complex.I * (t : ℂ)
  let sHigh : ℂ := (sigmaHigh : ℂ) + Complex.I * (t : ℂ)
  let S₀ : Finset ℕ :=
    (gsA9LargePrimesUpTo y).filter (fun p ↦ ¬ Q₂ p ∧ ¬ Q₃ p)
  let S₂ : Finset ℕ := (gsA9LargePrimesUpTo y).filter Q₂
  let S₃ : Finset ℕ := (gsA9LargePrimesUpTo y).filter Q₃
  let one : ℕ → ℂ := fun _ ↦ 1
  let P₀ : ℂ := ∏ p ∈ S₀, gsA9LocalEulerFactor g sLow p
  let P₂ : ℂ := ∏ p ∈ S₂, gsA9LocalEulerFactor g sLow p
  let P₃ : ℂ := ∏ p ∈ S₃, gsA9LocalEulerFactor g sLow p
  let Q₀ : ℂ := ∏ p ∈ S₀, gsA9LocalEulerFactor g sHigh p
  let Q₂p : ℂ := ∏ p ∈ S₂, gsA9LocalEulerFactor g sHigh p
  let Q₃p : ℂ := ∏ p ∈ S₃, gsA9LocalEulerFactor g sHigh p
  let Q₀pos : ℂ := ∏ p ∈ S₀, gsA9LocalEulerFactor one (sigmaHigh : ℂ) p
  let Q₂pos : ℂ := ∏ p ∈ S₂, gsA9LocalEulerFactor one (sigmaHigh : ℂ) p
  let Q₃pos : ℂ := ∏ p ∈ S₃, gsA9LocalEulerFactor one (sigmaHigh : ℂ) p
  let V₀ : ℝ := ∑ p ∈ S₀, ‖(p : ℂ) ^ (-sLow)‖ ^ 2
  let V₂ : ℝ := ∑ p ∈ S₂, ‖(p : ℂ) ^ (-sLow)‖ ^ 2
  let V₃ : ℝ := ∑ p ∈ S₃, ‖(p : ℂ) ^ (-sLow)‖ ^ 2
  let Alt : ℂ := LSeries (gsA9Low g y) sLow -
    LSeries (gsA9LowDeletion g Q₂ y) sLow -
    LSeries (gsA9LowDeletion g Q₃ y) sLow +
    LSeries (gsA9LowDeletion g (fun p ↦ Q₂ p ∨ Q₃ p) y) sLow
  have hmulG : IsMultiplicativeOnPositiveNat g :=
    gsDeletePrimeBand_isMultiplicativeOnPositiveNat hmul gsA9SmallPrime
  have hboundG : ∀ n, 0 < n → ‖g n‖ ≤ 1 := by
    intro n hn
    exact norm_gsDeletePrimeBand_le_one hbound gsA9SmallPrime hn
  have hsLow : 0 < sLow.re := by
    simpa only [sLow, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.I_re, Complex.I_im, Complex.ofReal_im, zero_mul, one_mul,
      sub_zero, add_zero] using
      (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 2) hhalf)
  have hS₀sub : S₀ ⊆ primesUpTo y := by
    intro p hp
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).1
  have hS₂sub : S₂ ⊆ primesUpTo y := by
    intro p hp
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).1
  have hS₃sub : S₃ ⊆ primesUpTo y := by
    intro p hp
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).1
  have hS₀large : ∀ p ∈ S₀, 23 ≤ p := by
    intro p hp
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2
  have hS₂large : ∀ p ∈ S₂, 23 ≤ p := by
    intro p hp
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2
  have hS₃large : ∀ p ∈ S₃, 23 ≤ p := by
    intro p hp
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2
  have hA13 :=
    norm_threeEulerBlockAlternating_sq_le_wideSource_shifted_full_products
      hmulG hboundG (show 2 ≤ y by omega) S₀ S₂ S₃
      hS₀sub hS₂sub hS₃sub hS₀large hS₂large hS₃large
      (t := t) hhalf hle hsigmaLow hgap
  have hAltEq := twoBlock_alternatingLow_deleteSmallPrimes_eq_largeEulerFactors
    hmul hbound Q₂ Q₃ y hdisj hsLow
  have hAltEq' : Alt = P₀ * (P₂ - 1) * (P₃ - 1) := by
    simpa only [g, sLow, S₀, S₂, S₃, P₀, P₂, P₃, Alt] using hAltEq
  have hA13' : ‖Alt‖ ^ 2 ≤
      Real.exp (7 * V₀ + 24 * (V₂ + V₃) +
        36 * gsA9WideSourceShiftConstant) *
        ‖Q₀ * Q₂p * Q₃p‖ * ‖Q₀pos * Q₂pos * Q₃pos‖ := by
    rw [hAltEq']
    simpa only [g, sLow, sHigh, one, S₀, S₂, S₃,
      P₀, P₂, P₃, Q₀, Q₂p, Q₃p, Q₀pos, Q₂pos,
      Q₃pos, V₀, V₂, V₃] using hA13
  have hpartActual : Q₀ * Q₂p * Q₃p =
      ∏ p ∈ gsA9LargePrimesUpTo y,
        gsA9LocalEulerFactor g sHigh p := by
    exact prod_neither_mul_prod_left_mul_prod_right_eq
      (gsA9LargePrimesUpTo y) Q₂ Q₃
      (by
        intro p hp h2 h3
        exact hdisj p (Finset.mem_filter.mp hp).1 h2 h3)
      (gsA9LocalEulerFactor g sHigh)
  have hpartPositive : Q₀pos * Q₂pos * Q₃pos =
      ∏ p ∈ gsA9LargePrimesUpTo y,
        gsA9LocalEulerFactor one (sigmaHigh : ℂ) p := by
    exact prod_neither_mul_prod_left_mul_prod_right_eq
      (gsA9LargePrimesUpTo y) Q₂ Q₃
      (by
        intro p hp h2 h3
        exact hdisj p (Finset.mem_filter.mp hp).1 h2 h3)
      (gsA9LocalEulerFactor one (sigmaHigh : ℂ))
  have hA13full : ‖Alt‖ ^ 2 ≤
      Real.exp (7 * V₀ + 24 * (V₂ + V₃) +
        36 * gsA9WideSourceShiftConstant) *
        ‖∏ p ∈ gsA9LargePrimesUpTo y,
          gsA9LocalEulerFactor g sHigh p‖ *
        ‖∏ p ∈ gsA9LargePrimesUpTo y,
          gsA9LocalEulerFactor one (sigmaHigh : ℂ) p‖ := by
    simpa only [hpartActual, hpartPositive] using hA13'
  have hraw := norm_alt_mul_high_sq_le_deleted_full_mul_zeta
    hmul hbound hy hsigmaHigh (Real.exp_pos _).le Alt hA13full
  have hV₀ : 2 * V₀ ≤ Real.exp 6 *
      Erdos67.EulerQuantitative.primeQuadraticConstant := by
    dsimp only [V₀, sLow]
    exact two_mul_sum_norm_prime_cpow_sq_wideSourceLow_le
      S₀ hS₀sub hsigmaLow
  have hV₂ : 2 * V₂ ≤ Real.exp 6 *
      Erdos67.EulerQuantitative.primeQuadraticConstant := by
    dsimp only [V₂, sLow]
    exact two_mul_sum_norm_prime_cpow_sq_wideSourceLow_le
      S₂ hS₂sub hsigmaLow
  have hV₃ : 2 * V₃ ≤ Real.exp 6 *
      Erdos67.EulerQuantitative.primeQuadraticConstant := by
    dsimp only [V₃, sLow]
    exact two_mul_sum_norm_prime_cpow_sq_wideSourceLow_le
      S₃ hS₃sub hsigmaLow
  have hC : 0 ≤ Real.exp 6 *
      Erdos67.EulerQuantitative.primeQuadraticConstant :=
    mul_nonneg (Real.exp_pos _).le
      Erdos67.EulerQuantitative.primeQuadraticConstant_nonneg
  have hquad : 7 * V₀ + 24 * (V₂ + V₃) ≤
      28 * Real.exp 6 *
        Erdos67.EulerQuantitative.primeQuadraticConstant := by
    nlinarith
  have hexp :
      Real.exp (7 * V₀ + 24 * (V₂ + V₃) +
          36 * gsA9WideSourceShiftConstant) ≤
        gsA9WideSourceEulerConstant := by
    unfold gsA9WideSourceEulerConstant
    exact Real.exp_le_exp.mpr (by linarith)
  have hraw' : ‖Alt * LSeries (gsA9High g y) sHigh‖ ^ 2 ≤
      Real.exp (7 * V₀ + 24 * (V₂ + V₃) +
          36 * gsA9WideSourceShiftConstant) *
        ‖LSeries g sHigh‖ * ‖riemannZeta (sigmaHigh : ℂ)‖ := by
    simpa only [g, sHigh, Alt] using hraw
  exact hraw'.trans (by gcongr)

/-- The widened source estimate with the high factor fixed at the ordinary
Halasz point. -/
theorem norm_twoBlock_alternatingLow_deleteSmallPrimes_mul_high_le_wideHalaszPoint
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    (Q₂ Q₃ : ℕ → Prop) [DecidablePred Q₂] [DecidablePred Q₃]
    {y : ℕ} (hy : 23 ≤ y)
    (hdisj : ∀ p ∈ primesUpTo y, Q₂ p → Q₃ p → False)
    {A X : ℕ} (hX : 1 < X)
    (hnonpret : MRArchimedeanNonpretentious f A X)
    {sigmaLow t : ℝ}
    (hhalf : 1 / 2 ≤ sigmaLow)
    (hle : sigmaLow ≤ Erdos67.EulerResidue.taoExponent X)
    (hsigmaLow : 1 - 3 / Real.log (y : ℝ) ≤ sigmaLow)
    (hgap : Erdos67.EulerResidue.taoExponent X - sigmaLow ≤
      3 / Real.log (y : ℝ))
    (ht : |t| ≤ X) :
    let g := gsDeletePrimeBand f gsA9SmallPrime
    let sLow : ℂ := (sigmaLow : ℂ) + Complex.I * (t : ℂ)
    let sHigh : ℂ := Erdos67.MRHalaszEuler.halaszPoint X t
    let Alt := LSeries (gsA9Low g y) sLow -
        LSeries (gsA9LowDeletion g Q₂ y) sLow -
        LSeries (gsA9LowDeletion g Q₃ y) sLow +
        LSeries (gsA9LowDeletion g (fun p ↦ Q₂ p ∨ Q₃ p) y) sLow
    ‖Alt * LSeries (gsA9High g y) sHigh‖ ≤
      gsA9WideSourceEulerConstant * (1 + Real.log (X : ℝ)) *
        Real.exp
          ((-Real.exp (-1) * ((A / 2 : ℕ) : ℝ) +
            3 * Erdos67.EulerQuantitative.primeQuadraticConstant) / 2) := by
  dsimp only
  let g : ℕ → ℂ := gsDeletePrimeBand f gsA9SmallPrime
  let sLow : ℂ := (sigmaLow : ℂ) + Complex.I * (t : ℂ)
  let sHigh : ℂ := Erdos67.MRHalaszEuler.halaszPoint X t
  let Alt : ℂ := LSeries (gsA9Low g y) sLow -
    LSeries (gsA9LowDeletion g Q₂ y) sLow -
    LSeries (gsA9LowDeletion g Q₃ y) sLow +
    LSeries (gsA9LowDeletion g (fun p ↦ Q₂ p ∨ Q₃ p) y) sLow
  let C : ℝ := gsA9WideSourceEulerConstant
  let q : ℝ := -Real.exp (-1) * ((A / 2 : ℕ) : ℝ) +
    3 * Erdos67.EulerQuantitative.primeQuadraticConstant
  let B : ℝ := 1 + Real.log (X : ℝ)
  let D : ℝ := Real.exp (q / 2)
  have hsigmaHigh : 1 < Erdos67.EulerResidue.taoExponent X :=
    Erdos67.EulerResidue.one_lt_taoExponent hX
  have hsq :=
    norm_twoBlock_alternatingLow_deleteSmallPrimes_mul_high_sq_le_wideSource
      hmul hbound Q₂ Q₃ hy hdisj hhalf hle hsigmaLow hgap hsigmaHigh
      (t := t)
  have hmulG : IsMultiplicativeOnPositiveNat g :=
    gsDeletePrimeBand_isMultiplicativeOnPositiveNat hmul gsA9SmallPrime
  have hboundG : ∀ n, 0 < n → ‖g n‖ ≤ 1 := by
    intro n hn
    exact norm_gsDeletePrimeBand_le_one hbound gsA9SmallPrime hn
  have hnonpretG : MRArchimedeanNonpretentious g (A / 2) X :=
    mrArchimedeanNonpretentious_deleteSmallPrimes_natHalf hbound hnonpret
  have hL : ‖LSeries g sHigh‖ ≤ B * Real.exp q := by
    simpa only [g, sHigh, B, q] using
      norm_LSeries_halaszPoint_le_one_add_log_mul_exp
        hmulG hboundG hX hnonpretG ht
  have hlogX : 0 < Real.log (X : ℝ) :=
    Real.log_pos (by exact_mod_cast hX)
  have hzeta : ‖riemannZeta (Erdos67.EulerResidue.taoExponent X : ℂ)‖ ≤ B := by
    have h := Erdos67.norm_riemannZeta_real_le_one_add_inv
      (sigma := (Real.log (X : ℝ))⁻¹) (inv_pos.mpr hlogX)
    simpa only [B, Erdos67.EulerResidue.taoExponent, inv_inv] using h
  have hC0 : 0 ≤ C := by
    dsimp only [C, gsA9WideSourceEulerConstant]
    exact (Real.exp_pos _).le
  have hB0 : 0 ≤ B := by dsimp only [B]; linarith
  have hsq' : ‖Alt * LSeries (gsA9High g y) sHigh‖ ^ 2 ≤
      C * (B * Real.exp q) * B := by
    have hbase : ‖Alt * LSeries (gsA9High g y) sHigh‖ ^ 2 ≤
        C * ‖LSeries g sHigh‖ *
          ‖riemannZeta (Erdos67.EulerResidue.taoExponent X : ℂ)‖ := by
      simpa only [g, sLow, sHigh, Alt, C,
        Erdos67.MRHalaszEuler.halaszPoint] using hsq
    exact hbase.trans (by gcongr)
  have hC1 : 1 ≤ C := by
    unfold C gsA9WideSourceEulerConstant
    apply Real.one_le_exp
    have hshift0 : 0 ≤ gsA9WideSourceShiftConstant := by
      unfold gsA9WideSourceShiftConstant
      have hlogTwo : 0 < Real.log 2 := Real.log_pos one_lt_two
      have hdiv : 0 ≤ primeLogMertensConstant / Real.log 2 :=
        div_nonneg primeLogMertensConstant_nonneg hlogTwo.le
      exact mul_nonneg (mul_nonneg (by norm_num) (Real.exp_pos _).le)
        (by linarith)
    exact add_nonneg
      (mul_nonneg
        (mul_nonneg (by norm_num) (Real.exp_pos _).le)
        Erdos67.EulerQuantitative.primeQuadraticConstant_nonneg)
      (mul_nonneg (by norm_num) hshift0)
  have hD0 : 0 ≤ D := (Real.exp_pos _).le
  have hDsq : D ^ 2 = Real.exp q := by
    dsimp only [D]
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have htarget : ‖Alt * LSeries (gsA9High g y) sHigh‖ ^ 2 ≤
      (C * B * D) ^ 2 := by
    calc
      _ ≤ C * (B * Real.exp q) * B := hsq'
      _ = C * B ^ 2 * D ^ 2 := by rw [hDsq]; ring
      _ ≤ (C * B * D) ^ 2 := by
        have hnonneg : 0 ≤ (B * D) ^ 2 := sq_nonneg _
        nlinarith
  exact (sq_le_sq₀ (norm_nonneg _)
      (mul_nonneg (mul_nonneg hC0 hB0) hD0)).mp
    htarget

end

end Erdos67.MRHalaszBands

#print axioms
  Erdos67.MRHalaszBands.norm_twoBlock_alternatingLow_deleteSmallPrimes_mul_high_sq_le_wideSource
#print axioms
  Erdos67.MRHalaszBands.norm_twoBlock_alternatingLow_deleteSmallPrimes_mul_high_le_wideHalaszPoint
