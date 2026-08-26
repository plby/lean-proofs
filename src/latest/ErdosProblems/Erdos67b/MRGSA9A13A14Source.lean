import ErdosProblems.Erdos67b.MRGSA9SourceRadius
import ErdosProblems.Erdos67b.MRGSA9A14SourceRecombine
import ErdosProblems.Erdos67b.MRGSA9FiniteEulerPositiveLine

/-!
# Source-shaped A.13--A.14 after fixed small-prime deletion

This module packages the exact four-term low Euler factor over the large
primes, applies the source-window horizontal shift, and recombines the high
factor into the full deleted L-series and zeta.
-/

open scoped BigOperators LSeries.notation

namespace Erdos67b.MRHalaszBands

noncomputable section

/-- Exact alternating-Euler identity after deleting the primes below `23`.
All small-prime local factors of the deleted coefficient are one. -/
theorem twoBlock_alternatingLow_deleteSmallPrimes_eq_largeEulerFactors
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    (Q₂ Q₃ : ℕ → Prop) [DecidablePred Q₂] [DecidablePred Q₃]
    (y : ℕ)
    (hdisj : ∀ p ∈ primesUpTo y, Q₂ p → Q₃ p → False)
    {s : ℂ} (hs : 0 < s.re) :
    let g := gsDeletePrimeBand f gsA9SmallPrime
    LSeries (gsA9Low g y) s -
          LSeries (gsA9LowDeletion g Q₂ y) s -
          LSeries (gsA9LowDeletion g Q₃ y) s +
          LSeries (gsA9LowDeletion g (fun p ↦ Q₂ p ∨ Q₃ p) y) s =
      (∏ p ∈ gsA9LargePrimesUpTo y with ¬ Q₂ p ∧ ¬ Q₃ p,
          gsA9LocalEulerFactor g s p) *
        ((∏ p ∈ gsA9LargePrimesUpTo y with Q₂ p,
            gsA9LocalEulerFactor g s p) - 1) *
        ((∏ p ∈ gsA9LargePrimesUpTo y with Q₃ p,
            gsA9LocalEulerFactor g s p) - 1) := by
  dsimp only
  let g : ℕ → ℂ := gsDeletePrimeBand f gsA9SmallPrime
  have hmulG : IsMultiplicativeOnPositiveNat g :=
    gsDeletePrimeBand_isMultiplicativeOnPositiveNat hmul gsA9SmallPrime
  have hboundG : ∀ n, 0 < n → ‖g n‖ ≤ 1 := by
    intro n hn
    exact norm_gsDeletePrimeBand_le_one hbound gsA9SmallPrime hn
  rw [LSeries_gsA9Low_eq_finiteEulerProduct_of_pos_re
      hmulG hboundG y hs,
    LSeries_gsA9LowDeletion_eq_finiteEulerProduct_of_pos_re
      hmulG hboundG Q₂ y hs,
    LSeries_gsA9LowDeletion_eq_finiteEulerProduct_of_pos_re
      hmulG hboundG Q₃ y hs,
    LSeries_gsA9LowDeletion_eq_finiteEulerProduct_of_pos_re
      hmulG hboundG (fun p ↦ Q₂ p ∨ Q₃ p) y hs,
    alternating_filtered_products_eq (primesUpTo y) Q₂ Q₃
      hdisj (gsA9LocalEulerFactor g s)]
  rw [prod_filter_deleteSmallPrimes_eq_large_filter hmul s y
      (fun p ↦ ¬ Q₂ p ∧ ¬ Q₃ p),
    prod_filter_deleteSmallPrimes_eq_large_filter hmul s y Q₂,
    prod_filter_deleteSmallPrimes_eq_large_filter hmul s y Q₃]

/-- Complete squared source A.13--A.14 estimate.  The low alternating factor
is evaluated on the source left line and the high factor on the right line.
All radius and horizontal-displacement hypotheses are discharged internally;
the remaining quadratic masses are explicit and absolutely summable. -/
theorem norm_twoBlock_alternatingLow_deleteSmallPrimes_mul_high_sq_le_source
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    (Q₂ Q₃ : ℕ → Prop) [DecidablePred Q₂] [DecidablePred Q₃]
    {y : ℕ} (hy : 23 ≤ y)
    (hdisj : ∀ p ∈ primesUpTo y, Q₂ p → Q₃ p → False)
    {sigmaLow sigmaHigh t : ℝ}
    (hhalf : 1 / 2 ≤ sigmaLow)
    (hle : sigmaLow ≤ sigmaHigh)
    (hsigmaLow : 1 - 2 / Real.log (y : ℝ) ≤ sigmaLow)
    (hgap : sigmaHigh - sigmaLow ≤ 3 / Real.log (y : ℝ))
    (hsigmaHigh : 1 < sigmaHigh) :
    let g := gsDeletePrimeBand f gsA9SmallPrime
    let sLow : ℂ := (sigmaLow : ℂ) + Complex.I * (t : ℂ)
    let sHigh : ℂ := (sigmaHigh : ℂ) + Complex.I * (t : ℂ)
    let S₀ := (gsA9LargePrimesUpTo y).filter (fun p ↦ ¬ Q₂ p ∧ ¬ Q₃ p)
    let S₂ := (gsA9LargePrimesUpTo y).filter Q₂
    let S₃ := (gsA9LargePrimesUpTo y).filter Q₃
    let V₀ := ∑ p ∈ S₀, ‖(p : ℂ) ^ (-sLow)‖ ^ 2
    let V₂ := ∑ p ∈ S₂, ‖(p : ℂ) ^ (-sLow)‖ ^ 2
    let V₃ := ∑ p ∈ S₃, ‖(p : ℂ) ^ (-sLow)‖ ^ 2
    let Alt := LSeries (gsA9Low g y) sLow -
        LSeries (gsA9LowDeletion g Q₂ y) sLow -
        LSeries (gsA9LowDeletion g Q₃ y) sLow +
        LSeries (gsA9LowDeletion g (fun p ↦ Q₂ p ∨ Q₃ p) y) sLow
    ‖Alt * LSeries (gsA9High g y) sHigh‖ ^ 2 ≤
      Real.exp (7 * V₀ + 24 * (V₂ + V₃) +
        36 * gsA9SourceShiftConstant) *
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
  let Q₀pos : ℂ := ∏ p ∈ S₀,
    gsA9LocalEulerFactor one (sigmaHigh : ℂ) p
  let Q₂pos : ℂ := ∏ p ∈ S₂,
    gsA9LocalEulerFactor one (sigmaHigh : ℂ) p
  let Q₃pos : ℂ := ∏ p ∈ S₃,
    gsA9LocalEulerFactor one (sigmaHigh : ℂ) p
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
      sub_zero, add_zero] using (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 2) hhalf)
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
  have hA13 := norm_threeEulerBlockAlternating_sq_le_source_shifted_full_products
    hmulG hboundG (show 2 ≤ y by omega) S₀ S₂ S₃
      hS₀sub hS₂sub hS₃sub hS₀large hS₂large hS₃large
      (t := t) hhalf hle hsigmaLow hgap
  have hAltEq := twoBlock_alternatingLow_deleteSmallPrimes_eq_largeEulerFactors
    hmul hbound Q₂ Q₃ y hdisj hsLow
  have hAltEq' : Alt = P₀ * (P₂ - 1) * (P₃ - 1) := by
    simpa only [g, sLow, S₀, S₂, S₃, P₀, P₂, P₃, Alt]
      using hAltEq
  have hA13' : ‖Alt‖ ^ 2 ≤
      Real.exp (7 * V₀ + 24 * (V₂ + V₃) +
        36 * gsA9SourceShiftConstant) *
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
        exact hdisj p
          (Finset.mem_filter.mp hp).1 h2 h3)
      (gsA9LocalEulerFactor g sHigh)
  have hpartPositive : Q₀pos * Q₂pos * Q₃pos =
      ∏ p ∈ gsA9LargePrimesUpTo y,
        gsA9LocalEulerFactor one (sigmaHigh : ℂ) p := by
    exact prod_neither_mul_prod_left_mul_prod_right_eq
      (gsA9LargePrimesUpTo y) Q₂ Q₃
      (by
        intro p hp h2 h3
        exact hdisj p
          (Finset.mem_filter.mp hp).1 h2 h3)
      (gsA9LocalEulerFactor one (sigmaHigh : ℂ))
  have hA13full : ‖Alt‖ ^ 2 ≤
      Real.exp (7 * V₀ + 24 * (V₂ + V₃) +
        36 * gsA9SourceShiftConstant) *
        ‖∏ p ∈ gsA9LargePrimesUpTo y,
          gsA9LocalEulerFactor g sHigh p‖ *
        ‖∏ p ∈ gsA9LargePrimesUpTo y,
          gsA9LocalEulerFactor one (sigmaHigh : ℂ) p‖ := by
    simpa only [hpartActual, hpartPositive] using hA13'
  have hrecombine := norm_alt_mul_high_sq_le_deleted_full_mul_zeta
    hmul hbound hy hsigmaHigh (Real.exp_pos _).le Alt hA13full
  simpa only [g, sHigh, Alt, V₀, V₂, V₃] using hrecombine

/-- Scalar form of the source A.13--A.14 estimate.  All three quadratic
prime masses are absorbed into one universal constant. -/
theorem norm_twoBlock_alternatingLow_deleteSmallPrimes_mul_high_sq_le_source_scalar
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    (Q₂ Q₃ : ℕ → Prop) [DecidablePred Q₂] [DecidablePred Q₃]
    {y : ℕ} (hy : 23 ≤ y)
    (hdisj : ∀ p ∈ primesUpTo y, Q₂ p → Q₃ p → False)
    {sigmaLow sigmaHigh t : ℝ}
    (hhalf : 1 / 2 ≤ sigmaLow)
    (hle : sigmaLow ≤ sigmaHigh)
    (hsigmaLow : 1 - 2 / Real.log (y : ℝ) ≤ sigmaLow)
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
      Real.exp
          (28 * Real.exp 4 *
              Erdos67b.EulerQuantitative.primeQuadraticConstant +
            36 * gsA9SourceShiftConstant) *
        ‖LSeries g sHigh‖ * ‖riemannZeta (sigmaHigh : ℂ)‖ := by
  dsimp only
  let g : ℕ → ℂ := gsDeletePrimeBand f gsA9SmallPrime
  let sLow : ℂ := (sigmaLow : ℂ) + Complex.I * (t : ℂ)
  let sHigh : ℂ := (sigmaHigh : ℂ) + Complex.I * (t : ℂ)
  let S₀ : Finset ℕ :=
    (gsA9LargePrimesUpTo y).filter (fun p ↦ ¬ Q₂ p ∧ ¬ Q₃ p)
  let S₂ : Finset ℕ := (gsA9LargePrimesUpTo y).filter Q₂
  let S₃ : Finset ℕ := (gsA9LargePrimesUpTo y).filter Q₃
  let V₀ : ℝ := ∑ p ∈ S₀, ‖(p : ℂ) ^ (-sLow)‖ ^ 2
  let V₂ : ℝ := ∑ p ∈ S₂, ‖(p : ℂ) ^ (-sLow)‖ ^ 2
  let V₃ : ℝ := ∑ p ∈ S₃, ‖(p : ℂ) ^ (-sLow)‖ ^ 2
  let Alt : ℂ := LSeries (gsA9Low g y) sLow -
    LSeries (gsA9LowDeletion g Q₂ y) sLow -
    LSeries (gsA9LowDeletion g Q₃ y) sLow +
    LSeries (gsA9LowDeletion g (fun p ↦ Q₂ p ∨ Q₃ p) y) sLow
  have hmain :=
    norm_twoBlock_alternatingLow_deleteSmallPrimes_mul_high_sq_le_source
      hmul hbound Q₂ Q₃ hy hdisj (t := t)
        hhalf hle hsigmaLow hgap hsigmaHigh
  have hS₀sub : S₀ ⊆ primesUpTo y := by
    intro p hp
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).1
  have hS₂sub : S₂ ⊆ primesUpTo y := by
    intro p hp
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).1
  have hS₃sub : S₃ ⊆ primesUpTo y := by
    intro p hp
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).1
  have hV₀ : 2 * V₀ ≤ Real.exp 4 *
      Erdos67b.EulerQuantitative.primeQuadraticConstant := by
    dsimp only [V₀, sLow]
    exact two_mul_sum_norm_prime_cpow_sq_sourceLow_le S₀ hS₀sub hsigmaLow
  have hV₂ : 2 * V₂ ≤ Real.exp 4 *
      Erdos67b.EulerQuantitative.primeQuadraticConstant := by
    dsimp only [V₂, sLow]
    exact two_mul_sum_norm_prime_cpow_sq_sourceLow_le S₂ hS₂sub hsigmaLow
  have hV₃ : 2 * V₃ ≤ Real.exp 4 *
      Erdos67b.EulerQuantitative.primeQuadraticConstant := by
    dsimp only [V₃, sLow]
    exact two_mul_sum_norm_prime_cpow_sq_sourceLow_le S₃ hS₃sub hsigmaLow
  have hquad : 7 * V₀ + 24 * (V₂ + V₃) ≤
      28 * Real.exp 4 * Erdos67b.EulerQuantitative.primeQuadraticConstant := by
    have hC : 0 ≤ Real.exp 4 *
        Erdos67b.EulerQuantitative.primeQuadraticConstant :=
      mul_nonneg (Real.exp_pos _).le
        Erdos67b.EulerQuantitative.primeQuadraticConstant_nonneg
    nlinarith
  have hexp :
      Real.exp (7 * V₀ + 24 * (V₂ + V₃) +
          36 * gsA9SourceShiftConstant) ≤
        Real.exp
          (28 * Real.exp 4 *
              Erdos67b.EulerQuantitative.primeQuadraticConstant +
            36 * gsA9SourceShiftConstant) := by
    apply Real.exp_le_exp.mpr
    linarith
  have hmain' : ‖Alt * LSeries (gsA9High g y) sHigh‖ ^ 2 ≤
      Real.exp (7 * V₀ + 24 * (V₂ + V₃) +
          36 * gsA9SourceShiftConstant) *
        ‖LSeries g sHigh‖ * ‖riemannZeta (sigmaHigh : ℂ)‖ := by
    simpa only [g, sLow, sHigh, S₀, S₂, S₃, V₀, V₂, V₃, Alt]
      using hmain
  calc
    ‖Alt * LSeries (gsA9High g y) sHigh‖ ^ 2 ≤
        Real.exp (7 * V₀ + 24 * (V₂ + V₃) +
            36 * gsA9SourceShiftConstant) *
          ‖LSeries g sHigh‖ * ‖riemannZeta (sigmaHigh : ℂ)‖ := hmain'
    _ ≤ Real.exp
          (28 * Real.exp 4 *
              Erdos67b.EulerQuantitative.primeQuadraticConstant +
            36 * gsA9SourceShiftConstant) *
        ‖LSeries g sHigh‖ * ‖riemannZeta (sigmaHigh : ℂ)‖ := by
      gcongr

/-- Unsquared source A.13--A.14 bound on the genuinely shifted high line.
The high full L-series is deliberately left visible for the subsequent
maximum-modulus argument. -/
theorem norm_twoBlock_alternatingLow_deleteSmallPrimes_mul_high_le_source_scalar
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    (Q₂ Q₃ : ℕ → Prop) [DecidablePred Q₂] [DecidablePred Q₃]
    {y : ℕ} (hy : 23 ≤ y)
    (hdisj : ∀ p ∈ primesUpTo y, Q₂ p → Q₃ p → False)
    {sigmaLow sigmaHigh t : ℝ}
    (hhalf : 1 / 2 ≤ sigmaLow)
    (hle : sigmaLow ≤ sigmaHigh)
    (hsigmaLow : 1 - 2 / Real.log (y : ℝ) ≤ sigmaLow)
    (hgap : sigmaHigh - sigmaLow ≤ 3 / Real.log (y : ℝ))
    (hsigmaHigh : 1 < sigmaHigh) :
    let g := gsDeletePrimeBand f gsA9SmallPrime
    let sLow : ℂ := (sigmaLow : ℂ) + Complex.I * (t : ℂ)
    let sHigh : ℂ := (sigmaHigh : ℂ) + Complex.I * (t : ℂ)
    let Alt := LSeries (gsA9Low g y) sLow -
        LSeries (gsA9LowDeletion g Q₂ y) sLow -
        LSeries (gsA9LowDeletion g Q₃ y) sLow +
        LSeries (gsA9LowDeletion g (fun p ↦ Q₂ p ∨ Q₃ p) y) sLow
    ‖Alt * LSeries (gsA9High g y) sHigh‖ ≤
      Real.exp
          (28 * Real.exp 4 *
              Erdos67b.EulerQuantitative.primeQuadraticConstant +
            36 * gsA9SourceShiftConstant) *
        Real.sqrt ‖LSeries g sHigh‖ *
        Real.sqrt ‖riemannZeta (sigmaHigh : ℂ)‖ := by
  dsimp only
  let g : ℕ → ℂ := gsDeletePrimeBand f gsA9SmallPrime
  let sLow : ℂ := (sigmaLow : ℂ) + Complex.I * (t : ℂ)
  let sHigh : ℂ := (sigmaHigh : ℂ) + Complex.I * (t : ℂ)
  let Alt : ℂ := LSeries (gsA9Low g y) sLow -
    LSeries (gsA9LowDeletion g Q₂ y) sLow -
    LSeries (gsA9LowDeletion g Q₃ y) sLow +
    LSeries (gsA9LowDeletion g (fun p ↦ Q₂ p ∨ Q₃ p) y) sLow
  let K : ℝ :=
    28 * Real.exp 4 * Erdos67b.EulerQuantitative.primeQuadraticConstant +
      36 * gsA9SourceShiftConstant
  let C : ℝ := Real.exp K
  let P : ℝ := Real.sqrt ‖LSeries g sHigh‖ *
    Real.sqrt ‖riemannZeta (sigmaHigh : ℂ)‖
  have hsq :=
    norm_twoBlock_alternatingLow_deleteSmallPrimes_mul_high_sq_le_source_scalar
      hmul hbound Q₂ Q₃ hy hdisj (t := t)
        hhalf hle hsigmaLow hgap hsigmaHigh
  have hsq' : ‖Alt * LSeries (gsA9High g y) sHigh‖ ^ 2 ≤
      C * ‖LSeries g sHigh‖ * ‖riemannZeta (sigmaHigh : ℂ)‖ := by
    simpa only [g, sLow, sHigh, Alt, K, C] using hsq
  have hK0 : 0 ≤ K := by
    have hlogTwo : 0 < Real.log 2 := Real.log_pos one_lt_two
    have hshift0 : 0 ≤ gsA9SourceShiftConstant := by
      unfold gsA9SourceShiftConstant
      exact mul_nonneg (mul_nonneg (by norm_num) (Real.exp_pos _).le)
        (by
          have hdiv : 0 ≤ primeLogMertensConstant / Real.log 2 :=
            div_nonneg primeLogMertensConstant_nonneg hlogTwo.le
          linarith)
    dsimp only [K]
    exact add_nonneg
      (mul_nonneg
        (mul_nonneg (by norm_num) (Real.exp_pos _).le)
        Erdos67b.EulerQuantitative.primeQuadraticConstant_nonneg)
      (mul_nonneg (by norm_num) hshift0)
  have hC1 : 1 ≤ C := by
    dsimp only [C]
    exact Real.one_le_exp hK0
  have hP0 : 0 ≤ P := by positivity
  have hPsq : P ^ 2 =
      ‖LSeries g sHigh‖ * ‖riemannZeta (sigmaHigh : ℂ)‖ := by
    dsimp only [P]
    rw [mul_pow, Real.sq_sqrt (norm_nonneg _), Real.sq_sqrt (norm_nonneg _)]
  have hsqTarget : ‖Alt * LSeries (gsA9High g y) sHigh‖ ^ 2 ≤
      (C * P) ^ 2 := by
    calc
      _ ≤ C * ‖LSeries g sHigh‖ *
          ‖riemannZeta (sigmaHigh : ℂ)‖ := hsq'
      _ = C * P ^ 2 := by rw [hPsq]; ring
      _ ≤ (C * P) ^ 2 := by
        have hP2 : 0 ≤ P ^ 2 := sq_nonneg _
        nlinarith
  have hfinal : ‖Alt * LSeries (gsA9High g y) sHigh‖ ≤ C * P :=
    (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.exp_pos _).le hP0)).mp
      hsqTarget
  change ‖Alt * LSeries (gsA9High g y) sHigh‖ ≤
    C * Real.sqrt ‖LSeries g sHigh‖ *
      Real.sqrt ‖riemannZeta (sigmaHigh : ℂ)‖
  calc
    _ ≤ C * P := hfinal
    _ = C * Real.sqrt ‖LSeries g sHigh‖ *
        Real.sqrt ‖riemannZeta (sigmaHigh : ℂ)‖ := by
      dsimp only [P]
      ring

end

end Erdos67b.MRHalaszBands
