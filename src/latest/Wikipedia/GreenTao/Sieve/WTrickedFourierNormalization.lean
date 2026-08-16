import Wikipedia.GreenTao.Sieve.CutoffZetaSingularKernel
import Wikipedia.GreenTao.Sieve.WTrickedEulerCorrection

/-!
# Exact W-tricked Fourier normalization

The normalized Selberg majorant contributes, for every selected form,

`(φ(W) / W) / (cχ log R)` and `(log R)²`.

The elementary pole in the zeta quotient contributes `(log R)⁻¹`, while
the omitted primes dividing the primorial contribute the inverse
reduced-residue density.  This file records the exact cancellation:

`Selberg scale × (log R)² × zeta pole × small-prime correction`

is

`cχ⁻¹ × cutoff-normalizer kernel × normalized small-prime residual`.

The identity is pointwise in all Fourier variables.  Specializing
`cχ` to the derivative-square normalizer and replacing the two correction
factors by one leaves an integrand whose full integral is exactly one.
-/

namespace Wikipedia.SzemeredisTheorem

open MeasureTheory
open scoped BigOperators

/-- The real Selberg scale for a primorial, after coercion to `ℂ`, is the
reduced-residue density divided by `cχ log R`. -/
theorem normalizedSelbergScale_primorial_cast
    (cχ : ℝ) (R w : ℕ) :
    (normalizedSelbergScale cχ R (primorial w) : ℂ) =
      primorialReducedResidueDensity w /
        ((cχ : ℂ) * (Real.log (R : ℝ) : ℂ)) := by
  rw [normalizedSelbergScale, primorialReducedResidueDensity]
  push_cast
  rfl

/-- Scalar cancellation before inserting the Fourier transforms.  The
power is kept arbitrary so that the lemma can also be reused for selected
subfamilies. -/
theorem normalizedSelbergScale_log_zeta_density_cancellation
    (cχ : ℝ) (hcχ : cχ ≠ 0)
    {R : ℕ} (hR : 1 < R) (w m : ℕ) :
    (normalizedSelbergScale cχ R (primorial w) : ℂ) ^ m *
          (((Real.log (R : ℝ) ^ 2 : ℝ) : ℂ) ^ m *
            ((((Real.log (R : ℝ))⁻¹ : ℝ) : ℂ) ^ m)) =
      ((cχ : ℂ)⁻¹) ^ m *
        primorialReducedResidueDensity w ^ m := by
  have hlogR :
      Real.log (R : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast hR)).ne'
  have hlogC :
      (Real.log (R : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast hlogR
  have hcχC : (cχ : ℂ) ≠ 0 := by
    exact_mod_cast hcχ
  have hlogSquare :
      (((Real.log (R : ℝ)) ^ 2 : ℝ) : ℂ) =
        (Real.log (R : ℝ) : ℂ) ^ 2 := by
    norm_cast
  have hlogInv :
      (((Real.log (R : ℝ))⁻¹ : ℝ) : ℂ) =
        (Real.log (R : ℝ) : ℂ)⁻¹ := by
    norm_cast
  rw [normalizedSelbergScale_primorial_cast]
  rw [hlogSquare, hlogInv]
  calc
    (primorialReducedResidueDensity w /
          ((cχ : ℂ) * (Real.log (R : ℝ) : ℂ))) ^ m *
          (((Real.log (R : ℝ) : ℂ) ^ 2) ^ m *
            ((Real.log (R : ℝ) : ℂ)⁻¹ ^ m)) =
        ((primorialReducedResidueDensity w /
              ((cχ : ℂ) *
                (Real.log (R : ℝ) : ℂ))) *
            ((Real.log (R : ℝ) : ℂ) ^ 2 *
              (Real.log (R : ℝ) : ℂ)⁻¹)) ^ m := by
      rw [mul_pow, mul_pow]
    _ =
        (((cχ : ℂ)⁻¹) *
          primorialReducedResidueDensity w) ^ m := by
      congr 1
      field_simp [hcχC, hlogC]
    _ =
        ((cχ : ℂ)⁻¹) ^ m *
          primorialReducedResidueDensity w ^ m := by
      rw [mul_pow]

/-- **Exact pointwise normalization identity.**  This is the algebraic
core of the main term calculation, before the completed-zeta and
large-prime correction factors (which may simply be multiplied onto both
sides). -/
theorem normalizedSelberg_fourier_zeta_smallPrime_eq
    {κ : Type*} [Fintype κ]
    (χ : SmoothSieveCutoff)
    {R : ℕ} (hR : 1 < R) (w : ℕ)
    (t u : κ → ℝ) :
    (normalizedSelbergScale χ.normalizer R (primorial w) : ℂ) ^
            Fintype.card κ *
          (((Real.log (R : ℝ) ^ 2 : ℝ) : ℂ) ^
            Fintype.card κ *
            (χ.fourierProductTransform t *
              χ.fourierProductTransform u *
              cutoffZetaSingularFactor R t u)) *
          smallPrimeZetaCorrection R w t u =
      ((χ.normalizer : ℂ)⁻¹) ^ Fintype.card κ *
          χ.cutoffNormalizerSeparatedProduct (t, u) *
          normalizedSmallPrimeZetaCorrection R w t u := by
  rw [χ.fourierProducts_mul_cutoffZetaSingularFactor_eq
    hR t u]
  rw [normalizedSmallPrimeZetaCorrection]
  have hscalar :=
    normalizedSelbergScale_log_zeta_density_cancellation
      χ.normalizer χ.normalizer_pos.ne'
      hR w (Fintype.card κ)
  calc
    (normalizedSelbergScale χ.normalizer R (primorial w) : ℂ) ^
            Fintype.card κ *
          (((Real.log (R : ℝ) ^ 2 : ℝ) : ℂ) ^
            Fintype.card κ *
            (((((Real.log (R : ℝ))⁻¹ : ℝ) : ℂ) ^
                Fintype.card κ) *
              χ.cutoffNormalizerSeparatedProduct (t, u))) *
          smallPrimeZetaCorrection R w t u =
        ((normalizedSelbergScale χ.normalizer R
              (primorial w) : ℂ) ^ Fintype.card κ *
            (((Real.log (R : ℝ) ^ 2 : ℝ) : ℂ) ^
              Fintype.card κ *
              ((((Real.log (R : ℝ))⁻¹ : ℝ) : ℂ) ^
                Fintype.card κ)) *
          χ.cutoffNormalizerSeparatedProduct (t, u) *
          smallPrimeZetaCorrection R w t u) := by
      ring
    _ =
        ((χ.normalizer : ℂ)⁻¹) ^ Fintype.card κ *
          primorialReducedResidueDensity w ^
            Fintype.card κ *
          χ.cutoffNormalizerSeparatedProduct (t, u) *
          smallPrimeZetaCorrection R w t u := by
      rw [hscalar]
    _ =
        ((χ.normalizer : ℂ)⁻¹) ^ Fintype.card κ *
          χ.cutoffNormalizerSeparatedProduct (t, u) *
          (primorialReducedResidueDensity w ^
            Fintype.card κ *
            smallPrimeZetaCorrection R w t u) := by
      ring

/-- The normalized archimedean baseline is absolutely integrable. -/
theorem
    SmoothSieveCutoff.integrable_invNormalizerPow_mul_cutoffNormalizerSeparatedProduct
    {κ : Type*} [Fintype κ]
    (χ : SmoothSieveCutoff) :
    Integrable
      (fun tu : (κ → ℝ) × (κ → ℝ) =>
        ((χ.normalizer : ℂ)⁻¹) ^ Fintype.card κ *
          χ.cutoffNormalizerSeparatedProduct tu)
      (volume.prod volume) :=
  χ.integrable_cutoffNormalizerSeparatedProduct.const_mul
    (((χ.normalizer : ℂ)⁻¹) ^ Fintype.card κ)

/-- The full integral of the normalized archimedean baseline is exactly
one. -/
theorem
    SmoothSieveCutoff.integral_invNormalizerPow_mul_cutoffNormalizerSeparatedProduct_eq_one
    {κ : Type*} [Fintype κ]
    (χ : SmoothSieveCutoff) :
    (∫ tu : (κ → ℝ) × (κ → ℝ),
        ((χ.normalizer : ℂ)⁻¹) ^ Fintype.card κ *
          χ.cutoffNormalizerSeparatedProduct tu
          ∂(volume.prod volume)) = 1 := by
  rw [integral_const_mul,
    χ.integral_cutoffNormalizerSeparatedProduct_eq_pow]
  have hnormalizer :
      (χ.normalizer : ℂ) ≠ 0 := by
    exact_mod_cast χ.normalizer_pos.ne'
  rw [← mul_pow, inv_mul_cancel₀ hnormalizer, one_pow]

end Wikipedia.SzemeredisTheorem
