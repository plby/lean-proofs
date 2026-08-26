import ErdosProblems.Erdos1038.PlatformReferenceMomentLimits
import ErdosProblems.Erdos1038.ResidualWidthMomentRecurrence

/-!
# Fixed-degree coefficients on the canonical platform mesh

The canonical inverse-moment Riemann sums converge at every order.  The
triangular moment recurrence therefore gives convergence of each fixed
Lagrange coefficient, including the reference-scale prefactor appearing
in the scaled inverse-width series.
-/

set_option warningAsError false

open Filter Set
open scoped BigOperators Topology

namespace Erdos1038

noncomputable section

variable {iota : Type*} [Fintype iota] [LinearOrder iota]

/-- Continuum value of one fixed scaled Lagrange coefficient. -/
def platformReferenceScaledLagrangeCoefficientLimit
    (C : ResidualConfiguration iota)
    (k a : ℝ) (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a) (degree : ℕ) : ℝ :=
  Real.exp (-((degree : ℝ) *
      platformReferenceLogMomentLimit C k a hk ha ha2 hthreshold)) *
    (degree : ℝ)⁻¹ *
      momentKernelCoefficient (degree : ℝ)
        (platformReferenceInverseMomentLimit C k a
          hk ha ha2 hthreshold) (degree - 1)

/-- Continuum velocity of the inverse moment of order `ell`. -/
def platformReferenceInverseMomentVelocityLimit
    (C : ResidualConfiguration iota)
    (k a : ℝ) (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a) (ell : ℕ) : ℝ :=
  -(ell : ℝ) *
    platformReferenceMaterialInverseMomentLimit C k a
      hk ha ha2 hthreshold ell

/-- Continuum value of one fixed material derivative coefficient. -/
def platformReferenceScaledLagrangeCoefficientDirectionalLimit
    (C : ResidualConfiguration iota)
    (k a : ℝ) (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a) (degree : ℕ) : ℝ :=
  let scale := Real.exp (-((degree : ℝ) *
    platformReferenceLogMomentLimit C k a hk ha ha2 hthreshold))
  let scaleDirectional := -(scale * ((degree : ℝ) *
    platformReferenceMaterialInverseMomentLimit C k a
      hk ha ha2 hthreshold 0))
  scaleDirectional * ((degree : ℝ)⁻¹ *
      momentKernelCoefficient (degree : ℝ)
        (platformReferenceInverseMomentLimit C k a
          hk ha ha2 hthreshold) (degree - 1)) +
    scale * ((degree : ℝ)⁻¹ *
      momentKernelCoefficientDirectional (degree : ℝ)
        (platformReferenceInverseMomentLimit C k a
          hk ha ha2 hthreshold)
        (platformReferenceInverseMomentVelocityLimit C k a
          hk ha ha2 hthreshold) (degree - 1))

/-- The reference-scale factor in a fixed Lagrange degree converges from
the actual canonical logarithmic-moment Riemann sum. -/
theorem tendsto_inverseMonomial_scaledPlatformResidualRefinementReference
    (C : ResidualConfiguration iota)
    (k a : ℝ) (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a) (degree : ℕ) :
    Tendsto
      (fun n ↦ inverseMonomial
        (fun p ↦ (degree : ℝ) *
          platformResidualRefinementAlpha C k n p)
        (platformResidualRefinementReference C k a
          hk ha ha2 hthreshold n))
      atTop
      (nhds (Real.exp (-((degree : ℝ) *
        platformReferenceLogMomentLimit C k a
          hk ha ha2 hthreshold)))) := by
  have hlog := tendsto_platformResidualRefinement_logMoment
    C k a hk ha ha2 hthreshold
  have hscaled := hlog.const_mul (degree : ℝ)
  have hexp := (Real.continuous_exp.tendsto _).comp hscaled.neg
  simpa only [inverseMonomial, Finset.mul_sum, mul_assoc] using! hexp

theorem tendsto_inverseMomentDirectional_platformResidualRefinement
    (C : ResidualConfiguration iota)
    (k a : ℝ) (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a) (ell : ℕ) :
    Tendsto
      (fun n ↦ inverseMomentDirectional
        (platformResidualRefinementAlpha C k n)
        (platformResidualRefinementReference C k a
          hk ha ha2 hthreshold n)
        (platformResidualRefinementTarget C n) ell)
      atTop
      (nhds (platformReferenceInverseMomentVelocityLimit C k a
        hk ha ha2 hthreshold ell)) := by
  have hmaterial :=
    tendsto_platformResidualRefinement_materialInverseMoment
      C k a hk ha ha2 hthreshold ell
  simpa only [inverseMomentDirectional,
    platformReferenceInverseMomentVelocityLimit, mul_assoc] using!
      hmaterial.const_mul (-(ell : ℝ))

theorem tendsto_inverseMonomialDirectional_scaledPlatformRefinement
    (C : ResidualConfiguration iota)
    (k a : ℝ) (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a) (degree : ℕ) :
    Tendsto
      (fun n ↦ inverseMonomialDirectional
        (fun p ↦ (degree : ℝ) *
          platformResidualRefinementAlpha C k n p)
        (platformResidualRefinementReference C k a
          hk ha ha2 hthreshold n)
        (platformResidualRefinementTarget C n))
      atTop
      (nhds (-(Real.exp (-((degree : ℝ) *
          platformReferenceLogMomentLimit C k a hk ha ha2 hthreshold)) *
        ((degree : ℝ) *
          platformReferenceMaterialInverseMomentLimit C k a
            hk ha ha2 hthreshold 0)))) := by
  have hscale :=
    tendsto_inverseMonomial_scaledPlatformResidualRefinementReference
      C k a hk ha ha2 hthreshold degree
  have hmaterial :=
    tendsto_platformResidualRefinement_materialInverseMoment
      C k a hk ha ha2 hthreshold 0
  have hproduct := hscale.mul (hmaterial.const_mul (degree : ℝ))
  apply hproduct.neg.congr'
  exact Filter.Eventually.of_forall fun n ↦ by
    unfold inverseMonomialDirectional
    simp only [div_eq_mul_inv, zero_add, pow_one]
    simp_rw [mul_assoc]
    rw [← Finset.mul_sum]
    ring

/-- Every fixed positive-degree scaled coefficient converges on the actual
canonical platform refinement. -/
theorem tendsto_scaledLagrangeCoefficient_platformResidualRefinement
    (C : ResidualConfiguration iota)
    (k a : ℝ) (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a)
    {degree : ℕ} (hdegree : 0 < degree) :
    Tendsto
      (fun n ↦ scaledLagrangeCoefficient
        (platformResidualRefinementAlpha C k n) degree
        (platformResidualRefinementReference C k a
          hk ha ha2 hthreshold n))
      atTop
      (nhds (platformReferenceScaledLagrangeCoefficientLimit C k a
        hk ha ha2 hthreshold degree)) := by
  have hmomentCoefficient := tendsto_momentKernelCoefficient (degree : ℝ)
    (momentSequence := fun n ell ↦ ∑ p,
      platformResidualRefinementAlpha C k n p *
        (platformResidualRefinementReference C k a
          hk ha ha2 hthreshold n p)⁻¹ ^ ell)
    (momentLimit := platformReferenceInverseMomentLimit C k a
      hk ha ha2 hthreshold)
    (fun ell ↦ tendsto_platformResidualRefinement_inverseMoment
      C k a hk ha ha2 hthreshold ell) (degree - 1)
  have hpowerCoefficient : Tendsto
      (fun n ↦ PowerSeries.coeff (degree - 1)
        ((PowerSeries.lagrangePhi
          (platformResidualRefinementAlpha C k n)
          (platformResidualRefinementReference C k a
            hk ha ha2 hthreshold n)) ^ degree))
      atTop
      (nhds (momentKernelCoefficient (degree : ℝ)
        (platformReferenceInverseMomentLimit C k a
          hk ha ha2 hthreshold) (degree - 1))) := by
    apply hmomentCoefficient.congr'
    exact Filter.Eventually.of_forall fun n ↦
      (coeff_lagrangePhi_pow_eq_momentKernelCoefficient
        (platformResidualRefinementAlpha C k n)
        (platformResidualRefinementReference C k a
          hk ha ha2 hthreshold n) degree (degree - 1)).symm
  have hscale :=
    tendsto_inverseMonomial_scaledPlatformResidualRefinementReference
      C k a hk ha ha2 hthreshold degree
  have hcoefficientProduct : Tendsto
      (fun n ↦ (degree : ℝ)⁻¹ *
        PowerSeries.coeff (degree - 1)
          ((PowerSeries.lagrangePhi
            (platformResidualRefinementAlpha C k n)
            (platformResidualRefinementReference C k a
              hk ha ha2 hthreshold n)) ^ degree))
      atTop
      (nhds ((degree : ℝ)⁻¹ *
        momentKernelCoefficient (degree : ℝ)
          (platformReferenceInverseMomentLimit C k a
            hk ha ha2 hthreshold) (degree - 1))) :=
    tendsto_const_nhds.mul hpowerCoefficient
  have hcombined : Tendsto
      (fun n ↦ inverseMonomial
          (fun p ↦ (degree : ℝ) *
            platformResidualRefinementAlpha C k n p)
          (platformResidualRefinementReference C k a
            hk ha ha2 hthreshold n) *
        ((degree : ℝ)⁻¹ *
          PowerSeries.coeff (degree - 1)
            ((PowerSeries.lagrangePhi
              (platformResidualRefinementAlpha C k n)
              (platformResidualRefinementReference C k a
                hk ha ha2 hthreshold n)) ^ degree)))
      atTop
      (nhds (Real.exp (-((degree : ℝ) *
          platformReferenceLogMomentLimit C k a hk ha ha2 hthreshold)) *
        ((degree : ℝ)⁻¹ *
          momentKernelCoefficient (degree : ℝ)
            (platformReferenceInverseMomentLimit C k a
              hk ha ha2 hthreshold) (degree - 1)))) :=
    hscale.mul hcoefficientProduct
  rw [platformReferenceScaledLagrangeCoefficientLimit]
  have hresult : Tendsto
      (fun n ↦ scaledLagrangeCoefficient
        (platformResidualRefinementAlpha C k n) degree
        (platformResidualRefinementReference C k a
          hk ha ha2 hthreshold n))
      atTop
      (nhds (Real.exp (-((degree : ℝ) *
          platformReferenceLogMomentLimit C k a hk ha ha2 hthreshold)) *
        ((degree : ℝ)⁻¹ *
          momentKernelCoefficient (degree : ℝ)
            (platformReferenceInverseMomentLimit C k a
              hk ha ha2 hthreshold) (degree - 1)))) := by
    apply hcombined.congr'
    filter_upwards with n
    rw [scaledLagrangeCoefficient_eq_mul_coeff_phi_pow
      (platformResidualRefinementAlpha C k n)
      (platformResidualRefinementReference C k a
        hk ha ha2 hthreshold n)
      (platformResidualRefinementReference_mem_positiveCoordinates
        C k a hk ha ha2 hthreshold n) hdegree]
  simpa only [mul_assoc] using! hresult

/-- Every fixed positive-degree material coefficient converges on the
actual canonical platform refinement. -/
theorem tendsto_scaledLagrangeCoefficientDirectional_platformRefinement
    (C : ResidualConfiguration iota)
    (k a : ℝ) (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a)
    {degree : ℕ} (hdegree : 0 < degree) :
    Tendsto
      (fun n ↦ scaledLagrangeCoefficientDirectional
        (platformResidualRefinementAlpha C k n) degree
        (platformResidualRefinementReference C k a
          hk ha ha2 hthreshold n)
        (platformResidualRefinementTarget C n))
      atTop
      (nhds (platformReferenceScaledLagrangeCoefficientDirectionalLimit
        C k a hk ha ha2 hthreshold degree)) := by
  let momentSequence : ℕ → ℕ → ℝ := fun n ell ↦ ∑ p,
    platformResidualRefinementAlpha C k n p *
      (platformResidualRefinementReference C k a
        hk ha ha2 hthreshold n p)⁻¹ ^ ell
  let velocitySequence : ℕ → ℕ → ℝ := fun n ell ↦
    inverseMomentDirectional
      (platformResidualRefinementAlpha C k n)
      (platformResidualRefinementReference C k a
        hk ha ha2 hthreshold n)
      (platformResidualRefinementTarget C n) ell
  let momentLimit := platformReferenceInverseMomentLimit C k a
    hk ha ha2 hthreshold
  let velocityLimit := platformReferenceInverseMomentVelocityLimit C k a
    hk ha ha2 hthreshold
  have hmoment (ell : ℕ) : Tendsto (fun n ↦ momentSequence n ell)
      atTop (nhds (momentLimit ell)) := by
    simpa only [momentSequence, momentLimit] using!
      tendsto_platformResidualRefinement_inverseMoment
        C k a hk ha ha2 hthreshold ell
  have hvelocity (ell : ℕ) : Tendsto
      (fun n ↦ velocitySequence n ell)
      atTop (nhds (velocityLimit ell)) := by
    simpa only [velocitySequence, velocityLimit] using!
      tendsto_inverseMomentDirectional_platformResidualRefinement
        C k a hk ha ha2 hthreshold ell
  have hmomentCoefficient := tendsto_momentKernelCoefficient
    (degree : ℝ) hmoment (degree - 1)
  have hdirectionalCoefficient :=
    tendsto_momentKernelCoefficientDirectional
      (degree : ℝ) hmoment hvelocity (degree - 1)
  have hscale :=
    tendsto_inverseMonomial_scaledPlatformResidualRefinementReference
      C k a hk ha ha2 hthreshold degree
  have hscaleDirectional :=
    tendsto_inverseMonomialDirectional_scaledPlatformRefinement
      C k a hk ha ha2 hthreshold degree
  have hbaseProduct : Tendsto
      (fun n ↦ (degree : ℝ)⁻¹ *
        momentKernelCoefficient (degree : ℝ)
          (momentSequence n) (degree - 1)) atTop
      (nhds ((degree : ℝ)⁻¹ *
        momentKernelCoefficient (degree : ℝ)
          momentLimit (degree - 1))) :=
    tendsto_const_nhds.mul hmomentCoefficient
  have hdirectionalProduct : Tendsto
      (fun n ↦ (degree : ℝ)⁻¹ *
        momentKernelCoefficientDirectional (degree : ℝ)
          (momentSequence n) (velocitySequence n) (degree - 1)) atTop
      (nhds ((degree : ℝ)⁻¹ *
        momentKernelCoefficientDirectional (degree : ℝ)
          momentLimit velocityLimit (degree - 1))) :=
    tendsto_const_nhds.mul hdirectionalCoefficient
  have hformula := (hscaleDirectional.mul hbaseProduct).add
    (hscale.mul hdirectionalProduct)
  rw [platformReferenceScaledLagrangeCoefficientDirectionalLimit]
  apply hformula.congr'
  filter_upwards with n
  rw [scaledLagrangeCoefficientDirectional_eq_moment
    (platformResidualRefinementAlpha C k n) hdegree
    (platformResidualRefinementReference C k a
      hk ha ha2 hthreshold n)
    (platformResidualRefinementTarget C n)
    (platformResidualRefinementReference_mem_positiveCoordinates
      C k a hk ha ha2 hthreshold n)]
  rfl

end

end Erdos1038
