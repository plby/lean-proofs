import Wikipedia.GreenTao.Sieve.CutoffNormalizerIntegral
import Mathlib.MeasureTheory.Integral.Pi

/-!
# Finite products of the cutoff-normalizer integral

The one-pair archimedean calculation in
`CutoffNormalizerIntegral` is the factor which remains for each selected
linear form after the arithmetic Euler product has been replaced by its
zeta model.  This file tensors that calculation over an arbitrary finite
family.

Both useful coordinate arrangements are recorded:

* a function `κ → ℝ × ℝ`, which makes the integrand a literal product of
  one-pair factors; and
* the sieve convention `(κ → ℝ) × (κ → ℝ)`, with the two copies of the
  Fourier variables separated.

The passage between them uses Mathlib's measure-preserving equivalence
between functions into a product and pairs of functions.  Thus the final
identity has exactly the product measure used by the multivariate divisor
expansion.
-/

namespace Wikipedia.SzemeredisTheorem

open MeasureTheory
open scoped BigOperators

namespace SmoothSieveCutoff

/-- The unabbreviated archimedean factor for one pair of Fourier
variables. -/
noncomputable def cutoffNormalizerPairFactor
    (χ : SmoothSieveCutoff) (z : ℝ × ℝ) : ℂ :=
  χ.cutoffFourierTransform z.1 *
    χ.cutoffFourierTransform z.2 *
    cutoffNormalizerKernel z.1 z.2

/-- The product of the one-pair archimedean factors over a finite selected
family, written with paired coordinates. -/
noncomputable def cutoffNormalizerPairedProduct
    {κ : Type*} [Fintype κ]
    (χ : SmoothSieveCutoff) (z : κ → ℝ × ℝ) : ℂ :=
  ∏ i, χ.cutoffNormalizerPairFactor (z i)

/-- The same finite product in the separated `(t,u)` coordinate convention
used by the multivariate Fourier divisor expansion. -/
noncomputable def cutoffNormalizerSeparatedProduct
    {κ : Type*} [Fintype κ]
    (χ : SmoothSieveCutoff)
    (tu : (κ → ℝ) × (κ → ℝ)) : ℂ :=
  ∏ i,
    χ.cutoffNormalizerPairFactor
      (tu.1 i, tu.2 i)

/-- The integral of the one-pair factor on `ℝ × ℝ` is the cutoff
normalizer. -/
theorem integral_cutoffNormalizerPairFactor_eq_normalizer
    (χ : SmoothSieveCutoff) :
    (∫ z : ℝ × ℝ,
        χ.cutoffNormalizerPairFactor z) =
      (χ.normalizer : ℂ) := by
  have hintegrable :
      Integrable
        (Function.uncurry
          (fun t : ℝ => fun u : ℝ =>
            χ.cutoffFourierTransform t *
              χ.cutoffFourierTransform u *
              cutoffNormalizerKernel t u))
        (volume.prod volume) := by
    exact
      χ.cutoffFourierKernelIntegrand_integrable.congr
        (Filter.Eventually.of_forall fun z => by
          rcases z with ⟨t, u⟩
          rfl)
  calc
    (∫ z : ℝ × ℝ,
        χ.cutoffNormalizerPairFactor z) =
        ∫ t : ℝ, ∫ u : ℝ,
          χ.cutoffFourierTransform t *
            χ.cutoffFourierTransform u *
            cutoffNormalizerKernel t u := by
      exact
        (integral_integral
          hintegrable).symm
    _ = (χ.normalizer : ℂ) :=
      χ.integral_cutoffFourierTransform_pairKernel_eq_normalizer

/-- Absolute integrability of the paired finite product. -/
theorem integrable_cutoffNormalizerPairedProduct
    {κ : Type*} [Fintype κ]
    (χ : SmoothSieveCutoff) :
    Integrable
      (χ.cutoffNormalizerPairedProduct :
        (κ → ℝ × ℝ) → ℂ) := by
  rw [MeasureTheory.volume_pi]
  exact Integrable.fintype_prod fun _ =>
    χ.cutoffFourierKernelIntegrand_integrable

/-- Tensorized one-pair identity in paired coordinates. -/
theorem integral_cutoffNormalizerPairedProduct_eq_pow
    {κ : Type*} [Fintype κ]
    (χ : SmoothSieveCutoff) :
    (∫ z : κ → ℝ × ℝ,
        χ.cutoffNormalizerPairedProduct z) =
      (χ.normalizer : ℂ) ^ Fintype.card κ := by
  unfold cutoffNormalizerPairedProduct
  rw [integral_fintype_prod_volume_eq_pow,
    χ.integral_cutoffNormalizerPairFactor_eq_normalizer]

/-- The paired and separated product integrands agree under the canonical
function/product equivalence. -/
theorem cutoffNormalizerSeparatedProduct_arrowProdEquiv
    {κ : Type*} [Fintype κ]
    (χ : SmoothSieveCutoff) (z : κ → ℝ × ℝ) :
    χ.cutoffNormalizerSeparatedProduct
        (MeasurableEquiv.arrowProdEquivProdArrow
          ℝ ℝ κ z) =
      χ.cutoffNormalizerPairedProduct z := by
  rfl

/-- Absolute integrability in the separated coordinate convention. -/
theorem integrable_cutoffNormalizerSeparatedProduct
    {κ : Type*} [Fintype κ]
    (χ : SmoothSieveCutoff) :
    Integrable
      (χ.cutoffNormalizerSeparatedProduct :
        ((κ → ℝ) × (κ → ℝ)) → ℂ)
      (volume.prod volume) := by
  let e :=
    MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ κ
  have hpreserving :
      MeasurePreserving e
        (volume : Measure (κ → ℝ × ℝ))
        ((volume : Measure (κ → ℝ)).prod
          (volume : Measure (κ → ℝ))) :=
    volume_measurePreserving_arrowProdEquivProdArrow
      ℝ ℝ κ
  have hcomp :
      Integrable
        ((χ.cutoffNormalizerSeparatedProduct :
            ((κ → ℝ) × (κ → ℝ)) → ℂ) ∘ e) := by
    change
      Integrable
        (fun z : κ → ℝ × ℝ =>
          χ.cutoffNormalizerSeparatedProduct
            (MeasurableEquiv.arrowProdEquivProdArrow
              ℝ ℝ κ z))
    exact
      χ.integrable_cutoffNormalizerPairedProduct.congr
        (Filter.Eventually.of_forall fun z =>
          (χ.cutoffNormalizerSeparatedProduct_arrowProdEquiv
            z).symm)
  exact
    (hpreserving.integrable_comp_emb
      e.measurableEmbedding).mp hcomp

/-- **Finite-product archimedean identity.**  In the separated Fourier
coordinate convention, the full integral is the `card κ`-th power of the
cutoff normalizer. -/
theorem integral_cutoffNormalizerSeparatedProduct_eq_pow
    {κ : Type*} [Fintype κ]
    (χ : SmoothSieveCutoff) :
    (∫ tu :
        (κ → ℝ) × (κ → ℝ),
        χ.cutoffNormalizerSeparatedProduct tu
          ∂(volume.prod volume)) =
      (χ.normalizer : ℂ) ^ Fintype.card κ := by
  let e :=
    MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ κ
  have hpreserving :
      MeasurePreserving e
        (volume : Measure (κ → ℝ × ℝ))
        ((volume : Measure (κ → ℝ)).prod
          (volume : Measure (κ → ℝ))) :=
    volume_measurePreserving_arrowProdEquivProdArrow
      ℝ ℝ κ
  calc
    (∫ tu :
        (κ → ℝ) × (κ → ℝ),
        χ.cutoffNormalizerSeparatedProduct tu
          ∂(volume.prod volume)) =
        ∫ z : κ → ℝ × ℝ,
          χ.cutoffNormalizerSeparatedProduct (e z) := by
      exact
        (hpreserving.integral_comp'
          χ.cutoffNormalizerSeparatedProduct).symm
    _ =
        ∫ z : κ → ℝ × ℝ,
          χ.cutoffNormalizerPairedProduct z := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun z =>
        χ.cutoffNormalizerSeparatedProduct_arrowProdEquiv z
    _ =
        (χ.normalizer : ℂ) ^ Fintype.card κ :=
      χ.integral_cutoffNormalizerPairedProduct_eq_pow

end SmoothSieveCutoff

end Wikipedia.SzemeredisTheorem
