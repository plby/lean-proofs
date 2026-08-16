import Wikipedia.GreenTao.Sieve.CutoffNormalizerProduct
import Wikipedia.GreenTao.Sieve.ZetaEulerProductIdentification

/-!
# The cutoff zeta pole as the normalizer kernel

For the Fourier shift

`z_R(t) = (1 - 2πit) / log R`,

the elementary pole contribution in one completed zeta quotient is

`z_R(t) z_R(u) / (z_R(t) + z_R(u))`.

This file identifies it exactly with `1 / log R` times the archimedean
kernel evaluated in `CutoffNormalizerIntegral`.  The identity is then
multiplied over a finite selected family and combined with both products of
cutoff Fourier transforms.  No limit is taken here: these are exact
algebraic normalization formulas.
-/

namespace Wikipedia.SzemeredisTheorem

open MeasureTheory
open scoped BigOperators

namespace SmoothSieveCutoff

/-- The two differentiated frequency weights add to the denominator of
the cutoff-normalizer kernel. -/
theorem cutoffDerivativeFrequencyWeight_add
    (t u : ℝ) :
    cutoffDerivativeFrequencyWeight t +
        cutoffDerivativeFrequencyWeight u =
      cutoffNormalizerDenominator t u := by
  simp only [cutoffDerivativeFrequencyWeight,
    cutoffNormalizerDenominator]
  push_cast
  ring

/-- The normalizer denominator is nonzero; its real part is `2`. -/
theorem cutoffNormalizerDenominator_ne_zero
    (t u : ℝ) :
    cutoffNormalizerDenominator t u ≠ 0 := by
  intro hzero
  have hre := congrArg Complex.re hzero
  simp [cutoffNormalizerDenominator] at hre

end SmoothSieveCutoff

/-- Exact one-pair conversion from the cutoff zeta pole to the
archimedean normalizer kernel. -/
theorem cutoffZetaShift_mul_div_add_eq_invLog_mul_kernel
    {R : ℕ} (hR : 1 < R) (t u : ℝ) :
    (cutoffZetaShift R t *
          cutoffZetaShift R u) /
        (cutoffZetaShift R t +
          cutoffZetaShift R u) =
      (((Real.log (R : ℝ))⁻¹ : ℝ) : ℂ) *
        SmoothSieveCutoff.cutoffNormalizerKernel t u := by
  let c : ℂ :=
    (((Real.log (R : ℝ))⁻¹ : ℝ) : ℂ)
  let a : ℂ :=
    SmoothSieveCutoff.cutoffDerivativeFrequencyWeight t
  let b : ℂ :=
    SmoothSieveCutoff.cutoffDerivativeFrequencyWeight u
  have hlog :
      Real.log (R : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast hR)).ne'
  have hc : c ≠ 0 := by
    dsimp [c]
    exact_mod_cast inv_ne_zero hlog
  have hab : a + b ≠ 0 := by
    rw [SmoothSieveCutoff.cutoffDerivativeFrequencyWeight_add]
    exact
      SmoothSieveCutoff.cutoffNormalizerDenominator_ne_zero t u
  have ht :
      cutoffZetaShift R t = c * a := by
    rfl
  have hu :
      cutoffZetaShift R u = c * b := by
    rfl
  have hkernel :
      SmoothSieveCutoff.cutoffNormalizerKernel t u =
        a * b / (a + b) := by
    rw [SmoothSieveCutoff.cutoffNormalizerKernel,
      ← SmoothSieveCutoff.cutoffDerivativeFrequencyWeight_add]
  rw [ht, hu, hkernel]
  change
    (c * a * (c * b)) / (c * a + c * b) =
      c * (a * b / (a + b))
  field_simp [hc, hab]

/-- The full elementary zeta pole is the product normalizer kernel times
one inverse logarithm for every selected form. -/
theorem cutoffZetaSingularFactor_eq_invLog_pow_mul_prod_kernel
    {κ : Type*} [Fintype κ]
    {R : ℕ} (hR : 1 < R)
    (t u : κ → ℝ) :
    cutoffZetaSingularFactor R t u =
      ((((Real.log (R : ℝ))⁻¹ : ℝ) : ℂ) ^
          Fintype.card κ) *
        ∏ i,
          SmoothSieveCutoff.cutoffNormalizerKernel
            (t i) (u i) := by
  classical
  rw [cutoffZetaSingularFactor]
  calc
    (∏ i,
        (cutoffZetaShift R (t i) *
            cutoffZetaShift R (u i)) /
          (cutoffZetaShift R (t i) +
            cutoffZetaShift R (u i))) =
        ∏ i,
          ((((Real.log (R : ℝ))⁻¹ : ℝ) : ℂ) *
            SmoothSieveCutoff.cutoffNormalizerKernel
              (t i) (u i)) := by
      apply Finset.prod_congr rfl
      intro i _
      exact
        cutoffZetaShift_mul_div_add_eq_invLog_mul_kernel
          hR (t i) (u i)
    _ =
        ((((Real.log (R : ℝ))⁻¹ : ℝ) : ℂ) ^
            Fintype.card κ) *
          ∏ i,
            SmoothSieveCutoff.cutoffNormalizerKernel
              (t i) (u i) := by
      rw [Finset.prod_mul_distrib, Finset.prod_const,
        Finset.card_univ]

/-- Exact regrouping of the two Fourier-transform products with the cutoff
zeta singular factor.  The right side is precisely the integrand evaluated
by `integral_cutoffNormalizerSeparatedProduct_eq_pow`, apart from the
displayed inverse-logarithm power. -/
theorem
    SmoothSieveCutoff.fourierProducts_mul_cutoffZetaSingularFactor_eq
    {κ : Type*} [Fintype κ]
    (χ : SmoothSieveCutoff)
    {R : ℕ} (hR : 1 < R)
    (t u : κ → ℝ) :
    χ.fourierProductTransform t *
          χ.fourierProductTransform u *
          cutoffZetaSingularFactor R t u =
      ((((Real.log (R : ℝ))⁻¹ : ℝ) : ℂ) ^
          Fintype.card κ) *
        χ.cutoffNormalizerSeparatedProduct (t, u) := by
  classical
  rw [cutoffZetaSingularFactor_eq_invLog_pow_mul_prod_kernel
    hR t u]
  unfold SmoothSieveCutoff.fourierProductTransform
    SmoothSieveCutoff.cutoffNormalizerSeparatedProduct
    SmoothSieveCutoff.cutoffNormalizerPairFactor
  calc
    (∏ i, χ.cutoffFourierTransform (t i)) *
          (∏ i, χ.cutoffFourierTransform (u i)) *
          (((((Real.log (R : ℝ))⁻¹ : ℝ) : ℂ) ^
              Fintype.card κ) *
            ∏ i,
              SmoothSieveCutoff.cutoffNormalizerKernel
                (t i) (u i)) =
        ((((Real.log (R : ℝ))⁻¹ : ℝ) : ℂ) ^
            Fintype.card κ) *
          (((∏ i, χ.cutoffFourierTransform (t i)) *
              ∏ i, χ.cutoffFourierTransform (u i)) *
            ∏ i,
              SmoothSieveCutoff.cutoffNormalizerKernel
                (t i) (u i)) := by
      ring
    _ =
        ((((Real.log (R : ℝ))⁻¹ : ℝ) : ℂ) ^
            Fintype.card κ) *
          ∏ i,
            χ.cutoffFourierTransform (t i) *
              χ.cutoffFourierTransform (u i) *
              SmoothSieveCutoff.cutoffNormalizerKernel
                (t i) (u i) := by
      congr 1
      rw [← Finset.prod_mul_distrib,
        ← Finset.prod_mul_distrib]

end Wikipedia.SzemeredisTheorem
