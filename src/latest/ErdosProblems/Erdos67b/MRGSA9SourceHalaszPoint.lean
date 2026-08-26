import ErdosProblems.Erdos67b.MRGSA9A13A14Source
import ErdosProblems.Erdos67b.MRGSA9LeftLine

/-!
# Source A.13--A.14 at the Halász point

The fixed-small-prime deletion loses only half of the original
nonpretentiousness threshold.  This file applies the ordinary Halász-point
Euler bound and absorbs the real zeta pole, leaving the contour-ready
logarithmic prefactor and exponential saving.
-/

open scoped LSeries.notation

namespace Erdos67b.MRHalaszBands

noncomputable section

/-- The small-prime-deleted coefficient is nonpretentious at the integer
threshold `A / 2`. -/
theorem mrArchimedeanNonpretentious_deleteSmallPrimes_natHalf
    {f : ℕ → ℂ} (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    {A X : ℕ} (hnonpret : MRArchimedeanNonpretentious f A X) :
    MRArchimedeanNonpretentious
      (gsDeletePrimeBand f gsA9SmallPrime) (A / 2) X := by
  intro t ht
  calc
    ((A / 2 : ℕ) : ℝ) ≤ (A : ℝ) / 2 := by
      simpa only [Nat.cast_ofNat] using (Nat.cast_div_le :
        ((A / 2 : ℕ) : ℝ) ≤ (A : ℝ) / (2 : ℝ))
    _ ≤ pretentiousDistSq (gsDeletePrimeBand f gsA9SmallPrime)
        (archimedeanTwist t) X :=
      archimedeanNonpretentious_half_deleteSmallPrimes hbound hnonpret t ht

/-- Squared A.9 integrand bound at the high Halász point.  The source left
line may lie below one, but is tied to it by the exact A.10 window. -/
theorem norm_twoBlock_alternatingLow_deleteSmallPrimes_mul_high_sq_le_halaszPoint
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    (Q₂ Q₃ : ℕ → Prop) [DecidablePred Q₂] [DecidablePred Q₃]
    {y : ℕ} (hy : 23 ≤ y)
    (hdisj : ∀ p ∈ primesUpTo y, Q₂ p → Q₃ p → False)
    {A X : ℕ} (hX : 1 < X)
    (hnonpret : MRArchimedeanNonpretentious f A X)
    {sigmaLow t : ℝ}
    (hhalf : 1 / 2 ≤ sigmaLow)
    (hle : sigmaLow ≤ Erdos67b.EulerResidue.taoExponent X)
    (hsigmaLow : 1 - 2 / Real.log (y : ℝ) ≤ sigmaLow)
    (hgap : Erdos67b.EulerResidue.taoExponent X - sigmaLow ≤
      3 / Real.log (y : ℝ))
    (ht : |t| ≤ X) :
    let g := gsDeletePrimeBand f gsA9SmallPrime
    let sLow : ℂ := (sigmaLow : ℂ) + Complex.I * (t : ℂ)
    let sHigh : ℂ := Erdos67b.MRHalaszEuler.halaszPoint X t
    let Alt := LSeries (gsA9Low g y) sLow -
        LSeries (gsA9LowDeletion g Q₂ y) sLow -
        LSeries (gsA9LowDeletion g Q₃ y) sLow +
        LSeries (gsA9LowDeletion g (fun p ↦ Q₂ p ∨ Q₃ p) y) sLow
    ‖Alt * LSeries (gsA9High g y) sHigh‖ ^ 2 ≤
      Real.exp
          (28 * Real.exp 4 *
              Erdos67b.EulerQuantitative.primeQuadraticConstant +
            36 * gsA9SourceShiftConstant) *
        (1 + Real.log (X : ℝ)) ^ 2 *
        Real.exp
          (-Real.exp (-1) * ((A / 2 : ℕ) : ℝ) +
            3 * Erdos67b.EulerQuantitative.primeQuadraticConstant) := by
  dsimp only
  let g : ℕ → ℂ := gsDeletePrimeBand f gsA9SmallPrime
  let sigmaHigh : ℝ := Erdos67b.EulerResidue.taoExponent X
  let sLow : ℂ := (sigmaLow : ℂ) + Complex.I * (t : ℂ)
  let sHigh : ℂ := Erdos67b.MRHalaszEuler.halaszPoint X t
  let Alt : ℂ := LSeries (gsA9Low g y) sLow -
    LSeries (gsA9LowDeletion g Q₂ y) sLow -
    LSeries (gsA9LowDeletion g Q₃ y) sLow +
    LSeries (gsA9LowDeletion g (fun p ↦ Q₂ p ∨ Q₃ p) y) sLow
  let C : ℝ := Real.exp
    (28 * Real.exp 4 * Erdos67b.EulerQuantitative.primeQuadraticConstant +
      36 * gsA9SourceShiftConstant)
  let E : ℝ := Real.exp
    (-Real.exp (-1) * ((A / 2 : ℕ) : ℝ) +
      3 * Erdos67b.EulerQuantitative.primeQuadraticConstant)
  have hsigmaHigh : 1 < sigmaHigh := by
    dsimp only [sigmaHigh]
    exact Erdos67b.EulerResidue.one_lt_taoExponent hX
  have hsource :=
    norm_twoBlock_alternatingLow_deleteSmallPrimes_mul_high_sq_le_source_scalar
      hmul hbound Q₂ Q₃ hy hdisj hhalf hle hsigmaLow hgap hsigmaHigh
      (t := t)
  have hsource' : ‖Alt * LSeries (gsA9High g y) sHigh‖ ^ 2 ≤
      C * ‖LSeries g sHigh‖ * ‖riemannZeta (sigmaHigh : ℂ)‖ := by
    simpa only [g, sigmaHigh, sLow, sHigh, Alt, C,
      Erdos67b.MRHalaszEuler.halaszPoint] using hsource
  have hmulG : IsMultiplicativeOnPositiveNat g :=
    gsDeletePrimeBand_isMultiplicativeOnPositiveNat hmul gsA9SmallPrime
  have hboundG : ∀ n, 0 < n → ‖g n‖ ≤ 1 := by
    intro n hn
    exact norm_gsDeletePrimeBand_le_one hbound gsA9SmallPrime hn
  have hnonpretG : MRArchimedeanNonpretentious g (A / 2) X :=
    mrArchimedeanNonpretentious_deleteSmallPrimes_natHalf hbound hnonpret
  have hL : ‖LSeries g sHigh‖ ≤ (1 + Real.log (X : ℝ)) * E := by
    simpa only [g, sHigh, E] using
      norm_LSeries_halaszPoint_le_one_add_log_mul_exp
        hmulG hboundG hX hnonpretG ht
  have hlogX : 0 < Real.log (X : ℝ) :=
    Real.log_pos (by exact_mod_cast hX)
  have hzeta : ‖riemannZeta (sigmaHigh : ℂ)‖ ≤
      1 + Real.log (X : ℝ) := by
    have h := Erdos67b.norm_riemannZeta_real_le_one_add_inv
      (sigma := (Real.log (X : ℝ))⁻¹) (inv_pos.mpr hlogX)
    simpa only [sigmaHigh, Erdos67b.EulerResidue.taoExponent, inv_inv] using h
  calc
    ‖Alt * LSeries (gsA9High g y) sHigh‖ ^ 2 ≤
        C * ‖LSeries g sHigh‖ * ‖riemannZeta (sigmaHigh : ℂ)‖ := hsource'
    _ ≤ C * ((1 + Real.log (X : ℝ)) * E) *
        (1 + Real.log (X : ℝ)) := by
      gcongr
    _ = C * (1 + Real.log (X : ℝ)) ^ 2 * E := by ring

/-- Unsquared contour-ready form.  We keep the full fixed exponential
constant instead of its square root; this harmless weakening makes the
consumer algebra particularly simple. -/
theorem norm_twoBlock_alternatingLow_deleteSmallPrimes_mul_high_le_halaszPoint
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    (Q₂ Q₃ : ℕ → Prop) [DecidablePred Q₂] [DecidablePred Q₃]
    {y : ℕ} (hy : 23 ≤ y)
    (hdisj : ∀ p ∈ primesUpTo y, Q₂ p → Q₃ p → False)
    {A X : ℕ} (hX : 1 < X)
    (hnonpret : MRArchimedeanNonpretentious f A X)
    {sigmaLow t : ℝ}
    (hhalf : 1 / 2 ≤ sigmaLow)
    (hle : sigmaLow ≤ Erdos67b.EulerResidue.taoExponent X)
    (hsigmaLow : 1 - 2 / Real.log (y : ℝ) ≤ sigmaLow)
    (hgap : Erdos67b.EulerResidue.taoExponent X - sigmaLow ≤
      3 / Real.log (y : ℝ))
    (ht : |t| ≤ X) :
    let g := gsDeletePrimeBand f gsA9SmallPrime
    let sLow : ℂ := (sigmaLow : ℂ) + Complex.I * (t : ℂ)
    let sHigh : ℂ := Erdos67b.MRHalaszEuler.halaszPoint X t
    let Alt := LSeries (gsA9Low g y) sLow -
        LSeries (gsA9LowDeletion g Q₂ y) sLow -
        LSeries (gsA9LowDeletion g Q₃ y) sLow +
        LSeries (gsA9LowDeletion g (fun p ↦ Q₂ p ∨ Q₃ p) y) sLow
    ‖Alt * LSeries (gsA9High g y) sHigh‖ ≤
      Real.exp
          (28 * Real.exp 4 *
              Erdos67b.EulerQuantitative.primeQuadraticConstant +
            36 * gsA9SourceShiftConstant) *
        (1 + Real.log (X : ℝ)) *
        Real.exp
          ((-Real.exp (-1) * ((A / 2 : ℕ) : ℝ) +
            3 * Erdos67b.EulerQuantitative.primeQuadraticConstant) / 2) := by
  dsimp only
  let g : ℕ → ℂ := gsDeletePrimeBand f gsA9SmallPrime
  let sLow : ℂ := (sigmaLow : ℂ) + Complex.I * (t : ℂ)
  let sHigh : ℂ := Erdos67b.MRHalaszEuler.halaszPoint X t
  let Alt : ℂ := LSeries (gsA9Low g y) sLow -
    LSeries (gsA9LowDeletion g Q₂ y) sLow -
    LSeries (gsA9LowDeletion g Q₃ y) sLow +
    LSeries (gsA9LowDeletion g (fun p ↦ Q₂ p ∨ Q₃ p) y) sLow
  let K : ℝ :=
    28 * Real.exp 4 * Erdos67b.EulerQuantitative.primeQuadraticConstant +
      36 * gsA9SourceShiftConstant
  let C : ℝ := Real.exp K
  let q : ℝ :=
    -Real.exp (-1) * ((A / 2 : ℕ) : ℝ) +
      3 * Erdos67b.EulerQuantitative.primeQuadraticConstant
  let B : ℝ := 1 + Real.log (X : ℝ)
  let D : ℝ := Real.exp (q / 2)
  have hsq :=
    norm_twoBlock_alternatingLow_deleteSmallPrimes_mul_high_sq_le_halaszPoint
      hmul hbound Q₂ Q₃ hy hdisj hX hnonpret hhalf hle hsigmaLow hgap ht
  have hsq' : ‖Alt * LSeries (gsA9High g y) sHigh‖ ^ 2 ≤
      C * B ^ 2 * Real.exp q := by
    simpa only [g, sLow, sHigh, Alt, K, C, q, B] using hsq
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
  have hB0 : 0 ≤ B := by
    have hlogX : 0 < Real.log (X : ℝ) :=
      Real.log_pos (by exact_mod_cast hX)
    dsimp only [B]
    linarith
  have hD0 : 0 ≤ D := (Real.exp_pos _).le
  have hDsq : D ^ 2 = Real.exp q := by
    dsimp only [D]
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hsqTarget : ‖Alt * LSeries (gsA9High g y) sHigh‖ ^ 2 ≤
      (C * B * D) ^ 2 := by
    calc
      _ ≤ C * B ^ 2 * Real.exp q := hsq'
      _ = C * (B * D) ^ 2 := by rw [← hDsq]; ring
      _ ≤ (C * B * D) ^ 2 := by
        have hP : 0 ≤ (B * D) ^ 2 := sq_nonneg _
        nlinarith
  exact (sq_le_sq₀ (norm_nonneg _) (by positivity : 0 ≤ C * B * D)).mp
    hsqTarget

end

end Erdos67b.MRHalaszBands
