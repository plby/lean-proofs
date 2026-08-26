import ErdosProblems.Erdos67b.MRGSA9SmallPrimeDeletion

/-!
# Three-block source-line A.13

This combines the finite squared A.13 estimate with the source-shaped
horizontal shift for the outside block and the two deletion blocks.
-/

open scoped BigOperators

namespace Erdos67b.MRHalaszBands

noncomputable section

/-- Shifted finite A.13 after the small primes have been separated.  The
common bound `D` for each block is harmless: the source displacement theorem
supplies an absolute choice of `D`. -/
theorem norm_threeEulerBlockAlternating_sq_le_shifted_full_products
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    (S₀ S₂ S₃ : Finset ℕ)
    (hprime₀ : ∀ p ∈ S₀, p.Prime)
    (hprime₂ : ∀ p ∈ S₂, p.Prime)
    (hprime₃ : ∀ p ∈ S₃, p.Prime)
    {sigmaLow sigmaHigh t D : ℝ} (hle : sigmaLow ≤ sigmaHigh)
    (hsmall₀ : ∀ p ∈ S₀,
      ‖(p : ℂ) ^ (-((sigmaLow : ℂ) + Complex.I * (t : ℂ)))‖ ≤ (1 / 3 : ℝ))
    (hsmall₂ : ∀ p ∈ S₂,
      ‖(p : ℂ) ^ (-((sigmaLow : ℂ) + Complex.I * (t : ℂ)))‖ ≤ (1 / 3 : ℝ))
    (hsmall₃ : ∀ p ∈ S₃,
      ‖(p : ℂ) ^ (-((sigmaLow : ℂ) + Complex.I * (t : ℂ)))‖ ≤ (1 / 3 : ℝ))
    (hD₀ : (∑ p ∈ S₀,
      (‖(p : ℂ) ^ (-((sigmaLow : ℂ) + Complex.I * (t : ℂ)))‖ -
        ‖(p : ℂ) ^ (-((sigmaHigh : ℂ) + Complex.I * (t : ℂ)))‖)) ≤ D)
    (hD₂ : (∑ p ∈ S₂,
      (‖(p : ℂ) ^ (-((sigmaLow : ℂ) + Complex.I * (t : ℂ)))‖ -
        ‖(p : ℂ) ^ (-((sigmaHigh : ℂ) + Complex.I * (t : ℂ)))‖)) ≤ D)
    (hD₃ : (∑ p ∈ S₃,
      (‖(p : ℂ) ^ (-((sigmaLow : ℂ) + Complex.I * (t : ℂ)))‖ -
        ‖(p : ℂ) ^ (-((sigmaHigh : ℂ) + Complex.I * (t : ℂ)))‖)) ≤ D) :
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
      Real.exp (7 * V₀ + 24 * (V₂ + V₃) + 36 * D) *
        ‖Q₀ * Q₂ * Q₃‖ * ‖Q₀p * Q₂p * Q₃p‖ := by
  dsimp only
  let sLow : ℂ := (sigmaLow : ℂ) + Complex.I * (t : ℂ)
  let sHigh : ℂ := (sigmaHigh : ℂ) + Complex.I * (t : ℂ)
  let one : ℕ → ℂ := fun _ ↦ 1
  let P₀ : ℂ := ∏ p ∈ S₀, gsA9LocalEulerFactor f sLow p
  let P₂ : ℂ := ∏ p ∈ S₂, gsA9LocalEulerFactor f sLow p
  let P₃ : ℂ := ∏ p ∈ S₃, gsA9LocalEulerFactor f sLow p
  let P₀p : ℂ := ∏ p ∈ S₀, gsA9LocalEulerFactor one (sigmaLow : ℂ) p
  let P₂p : ℂ := ∏ p ∈ S₂, gsA9LocalEulerFactor one (sigmaLow : ℂ) p
  let P₃p : ℂ := ∏ p ∈ S₃, gsA9LocalEulerFactor one (sigmaLow : ℂ) p
  let Q₀ : ℂ := ∏ p ∈ S₀, gsA9LocalEulerFactor f sHigh p
  let Q₂ : ℂ := ∏ p ∈ S₂, gsA9LocalEulerFactor f sHigh p
  let Q₃ : ℂ := ∏ p ∈ S₃, gsA9LocalEulerFactor f sHigh p
  let Q₀p : ℂ := ∏ p ∈ S₀, gsA9LocalEulerFactor one (sigmaHigh : ℂ) p
  let Q₂p : ℂ := ∏ p ∈ S₂, gsA9LocalEulerFactor one (sigmaHigh : ℂ) p
  let Q₃p : ℂ := ∏ p ∈ S₃, gsA9LocalEulerFactor one (sigmaHigh : ℂ) p
  let V₀ : ℝ := ∑ p ∈ S₀, ‖(p : ℂ) ^ (-sLow)‖ ^ 2
  let V₂ : ℝ := ∑ p ∈ S₂, ‖(p : ℂ) ^ (-sLow)‖ ^ 2
  let V₃ : ℝ := ∑ p ∈ S₃, ‖(p : ℂ) ^ (-sLow)‖ ^ 2
  change ‖P₀ * (P₂ - 1) * (P₃ - 1)‖ ^ 2 ≤
    Real.exp (7 * V₀ + 24 * (V₂ + V₃) + 36 * D) *
      ‖Q₀ * Q₂ * Q₃‖ * ‖Q₀p * Q₂p * Q₃p‖
  have hlow := norm_threeEulerBlockAlternating_sq_le_full_products_of_norm_le_third
    hmul hbound S₀ S₂ S₃ hprime₀ hprime₂ hprime₃ hsmall₀ hsmall₂ hsmall₃
  have hlow' : ‖P₀ * (P₂ - 1) * (P₃ - 1)‖ ^ 2 ≤
      Real.exp (7 * V₀ + 24 * (V₂ + V₃)) *
        ‖P₀ * P₂ * P₃‖ * ‖P₀p * P₂p * P₃p‖ := by
    simpa only [sLow, one, P₀, P₂, P₃, P₀p, P₂p, P₃p, V₀, V₂, V₃]
      using hlow
  have hshift₀ := mul_norm_prod_gsA9LocalEulerFactor_source_shift_le
    hmul hbound S₀ hprime₀ hle hsmall₀ hD₀
  have hshift₂ := mul_norm_prod_gsA9LocalEulerFactor_source_shift_le
    hmul hbound S₂ hprime₂ hle hsmall₂ hD₂
  have hshift₃ := mul_norm_prod_gsA9LocalEulerFactor_source_shift_le
    hmul hbound S₃ hprime₃ hle hsmall₃ hD₃
  have hshift₀' : ‖P₀‖ * ‖P₀p‖ ≤ ‖Q₀‖ * ‖Q₀p‖ * Real.exp (12 * D) := by
    simpa only [sLow, sHigh, one, P₀, P₀p, Q₀, Q₀p] using hshift₀
  have hshift₂' : ‖P₂‖ * ‖P₂p‖ ≤ ‖Q₂‖ * ‖Q₂p‖ * Real.exp (12 * D) := by
    simpa only [sLow, sHigh, one, P₂, P₂p, Q₂, Q₂p] using hshift₂
  have hshift₃' : ‖P₃‖ * ‖P₃p‖ ≤ ‖Q₃‖ * ‖Q₃p‖ * Real.exp (12 * D) := by
    simpa only [sLow, sHigh, one, P₃, P₃p, Q₃, Q₃p] using hshift₃
  have hexpThree : Real.exp (12 * D) * Real.exp (12 * D) * Real.exp (12 * D) =
      Real.exp (36 * D) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  have hproducts : ‖P₀ * P₂ * P₃‖ * ‖P₀p * P₂p * P₃p‖ ≤
      (‖Q₀ * Q₂ * Q₃‖ * ‖Q₀p * Q₂p * Q₃p‖) *
        Real.exp (36 * D) := by
    simp only [norm_mul]
    calc
      (‖P₀‖ * ‖P₂‖ * ‖P₃‖) * (‖P₀p‖ * ‖P₂p‖ * ‖P₃p‖) =
          (‖P₀‖ * ‖P₀p‖) * (‖P₂‖ * ‖P₂p‖) * (‖P₃‖ * ‖P₃p‖) := by ring
      _ ≤ (‖Q₀‖ * ‖Q₀p‖ * Real.exp (12 * D)) *
          (‖Q₂‖ * ‖Q₂p‖ * Real.exp (12 * D)) *
          (‖Q₃‖ * ‖Q₃p‖ * Real.exp (12 * D)) := by
        gcongr
      _ = ((‖Q₀‖ * ‖Q₂‖ * ‖Q₃‖) *
          (‖Q₀p‖ * ‖Q₂p‖ * ‖Q₃p‖)) * Real.exp (36 * D) := by
        rw [← hexpThree]
        ring
  calc
    ‖P₀ * (P₂ - 1) * (P₃ - 1)‖ ^ 2 ≤
        Real.exp (7 * V₀ + 24 * (V₂ + V₃)) *
          (‖P₀ * P₂ * P₃‖ * ‖P₀p * P₂p * P₃p‖) := by
      simpa only [mul_assoc] using hlow'
    _ ≤ Real.exp (7 * V₀ + 24 * (V₂ + V₃)) *
        ((‖Q₀ * Q₂ * Q₃‖ * ‖Q₀p * Q₂p * Q₃p‖) *
          Real.exp (36 * D)) := by
      gcongr
    _ = Real.exp (7 * V₀ + 24 * (V₂ + V₃) + 36 * D) *
        ‖Q₀ * Q₂ * Q₃‖ * ‖Q₀p * Q₂p * Q₃p‖ := by
      have he : Real.exp (7 * V₀ + 24 * (V₂ + V₃)) * Real.exp (36 * D) =
          Real.exp (7 * V₀ + 24 * (V₂ + V₃) + 36 * D) := by
        rw [← Real.exp_add]
      rw [show Real.exp (7 * V₀ + 24 * (V₂ + V₃)) *
            ((‖Q₀ * Q₂ * Q₃‖ * ‖Q₀p * Q₂p * Q₃p‖) * Real.exp (36 * D)) =
          (Real.exp (7 * V₀ + 24 * (V₂ + V₃)) * Real.exp (36 * D)) *
            ‖Q₀ * Q₂ * Q₃‖ * ‖Q₀p * Q₂p * Q₃p‖ by ring, he]

end

end Erdos67b.MRHalaszBands
