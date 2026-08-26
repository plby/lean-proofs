import ErdosProblems.Erdos1038.PlatformAdjointModePairing

/-!
# The endpoint-corrected adjoint for finite cosine polynomials

This file packages the mode-by-mode finite Hilbert calculation into the
finite cosine-polynomial identity used in the endpoint-corrected adjoint.
The normalization follows the manuscript convention

`F(theta) = f0 + 2 * sum_n f_n cos(n theta)`.
-/

set_option warningAsError false

open MeasureTheory
open scoped BigOperators

namespace Erdos1038

noncomputable section

/-- A finite cosine polynomial with positive even frequencies indexed as
`2(m+1)` and positive odd frequencies indexed as `2m+1`. -/
def finiteEndpointCosinePolynomial
    {alpha beta : Type*} [Fintype alpha] [Fintype beta]
    (f0 : ℝ) (evenMode : alpha → ℕ) (oddMode : beta → ℕ)
    (evenCoefficient : alpha → ℝ) (oddCoefficient : beta → ℝ)
    (theta : ℝ) : ℝ :=
  f0 +
    2 * ∑ i, evenCoefficient i *
      Real.cos (((2 * (evenMode i + 1) : ℕ) : ℝ) * theta) +
    2 * ∑ i, oddCoefficient i *
      Real.cos (((2 * oddMode i + 1 : ℕ) : ℝ) * theta)

/-- The removable finite Hilbert transform of the nonconstant part of a
finite cosine polynomial, including its spatial factor `2 / r`. -/
def finiteEndpointHilbertTransform
    {alpha beta : Type*} [Fintype alpha] [Fintype beta]
    (r : ℝ) (evenMode : alpha → ℕ) (oddMode : beta → ℕ)
    (evenCoefficient : alpha → ℝ) (oddCoefficient : beta → ℝ)
    (theta : ℝ) : ℝ :=
  (∑ i, evenCoefficient i *
      ((2 / r) * (-oddSecondKindAngularMode (evenMode i + 1) theta))) +
    ∑ i, oddCoefficient i *
      ((2 / r) * (-evenSecondKindAngularMode (oddMode i) theta))

/-- The exterior first variation of a finite cosine polynomial, expressed
through the exact Poisson-coordinate coefficients. -/
def finiteEndpointExteriorVariation
    {alpha beta : Type*} [Fintype alpha] [Fintype beta]
    (r sigmaMinus sigmaPlus rhoMinus rhoPlus f0 : ℝ)
    (evenMode : alpha → ℕ) (oddMode : beta → ℕ)
    (evenCoefficient : alpha → ℝ) (oddCoefficient : beta → ℝ) : ℝ :=
  -endpointAdjointGamma r sigmaMinus sigmaPlus rhoMinus rhoPlus * f0 +
    ∑ i, evenCoefficient i *
      endpointExteriorCosCoefficient r sigmaMinus sigmaPlus
        rhoMinus rhoPlus (2 * (evenMode i + 1)) +
    ∑ i, oddCoefficient i *
      endpointExteriorCosCoefficient r sigmaMinus sigmaPlus
        rhoMinus rhoPlus (2 * oddMode i + 1)

theorem finiteEndpointCosinePolynomial_at_pi
    {alpha beta : Type*} [Fintype alpha] [Fintype beta]
    (f0 : ℝ) (evenMode : alpha → ℕ) (oddMode : beta → ℕ)
    (evenCoefficient : alpha → ℝ) (oddCoefficient : beta → ℝ) :
    finiteEndpointCosinePolynomial f0 evenMode oddMode
        evenCoefficient oddCoefficient Real.pi =
      f0 + 2 * ∑ i, evenCoefficient i -
        2 * ∑ i, oddCoefficient i := by
  classical
  have heven (n : ℕ) :
      (-1 : ℝ) ^ (2 * (n + 1)) = 1 := by
    rw [pow_mul]
    norm_num
  have hodd (n : ℕ) :
      (-1 : ℝ) ^ (2 * n + 1) = -1 := by
    rw [pow_add, pow_mul]
    norm_num
  unfold finiteEndpointCosinePolynomial
  simp_rw [Real.cos_nat_mul_pi, heven, hodd, mul_one, mul_neg]
  rw [Finset.sum_neg_distrib]
  ring_nf

private theorem one_div_pi_mul_integral_endpointAdjointDensity_evenTerm
    {r sigmaMinus sigmaPlus rhoMinus rhoPlus coefficient : ℝ}
    (hm0 : 0 ≤ rhoMinus) (hm1 : rhoMinus < 1)
    (hp0 : 0 ≤ rhoPlus) (hp1 : rhoPlus < 1) (m : ℕ) :
    (1 / Real.pi) *
        (∫ theta in 0..Real.pi,
          endpointAdjointAngularDensity
              sigmaMinus sigmaPlus rhoMinus rhoPlus theta *
            (coefficient *
              ((2 / r) * (-oddSecondKindAngularMode (m + 1) theta)))) =
      coefficient * endpointAdjointEvenCosCoefficient
        r sigmaMinus sigmaPlus rhoMinus rhoPlus m := by
  have hpoint :
      (fun theta : ℝ ↦ endpointAdjointAngularDensity
          sigmaMinus sigmaPlus rhoMinus rhoPlus theta *
        (coefficient *
          ((2 / r) * (-oddSecondKindAngularMode (m + 1) theta)))) =
      fun theta ↦ (coefficient * (2 / r)) *
        (endpointAdjointAngularDensity
            sigmaMinus sigmaPlus rhoMinus rhoPlus theta *
          (-oddSecondKindAngularMode (m + 1) theta)) := by
    funext theta
    ring
  rw [hpoint, intervalIntegral.integral_const_mul]
  have hpair := finiteHilbert_evenMode_adjointPairing
    (r := r) (sigmaMinus := sigmaMinus) (sigmaPlus := sigmaPlus)
      hm0 hm1 hp0 hp1 m
  calc
    (1 / Real.pi) *
          ((coefficient * (2 / r)) *
            (∫ theta in 0..Real.pi,
              endpointAdjointAngularDensity
                  sigmaMinus sigmaPlus rhoMinus rhoPlus theta *
                (-oddSecondKindAngularMode (m + 1) theta))) =
        coefficient * ((2 / r) * (1 / Real.pi) *
          (∫ theta in 0..Real.pi,
            endpointAdjointAngularDensity
                sigmaMinus sigmaPlus rhoMinus rhoPlus theta *
              (-oddSecondKindAngularMode (m + 1) theta))) := by ring
    _ = _ := by rw [hpair]

private theorem one_div_pi_mul_integral_endpointAdjointDensity_oddTerm
    {r sigmaMinus sigmaPlus rhoMinus rhoPlus coefficient : ℝ}
    (hm0 : 0 ≤ rhoMinus) (hm1 : rhoMinus < 1)
    (hp0 : 0 ≤ rhoPlus) (hp1 : rhoPlus < 1) (m : ℕ) :
    (1 / Real.pi) *
        (∫ theta in 0..Real.pi,
          endpointAdjointAngularDensity
              sigmaMinus sigmaPlus rhoMinus rhoPlus theta *
            (coefficient *
              ((2 / r) * (-evenSecondKindAngularMode m theta)))) =
      coefficient * endpointAdjointOddCosCoefficient
        r sigmaMinus sigmaPlus rhoMinus rhoPlus m := by
  have hpoint :
      (fun theta : ℝ ↦ endpointAdjointAngularDensity
          sigmaMinus sigmaPlus rhoMinus rhoPlus theta *
        (coefficient * ((2 / r) *
          (-evenSecondKindAngularMode m theta)))) =
      fun theta ↦ (coefficient * (2 / r)) *
        (endpointAdjointAngularDensity
            sigmaMinus sigmaPlus rhoMinus rhoPlus theta *
          (-evenSecondKindAngularMode m theta)) := by
    funext theta
    ring
  rw [hpoint, intervalIntegral.integral_const_mul]
  have hpair := finiteHilbert_oddMode_adjointPairing
    (r := r) (sigmaMinus := sigmaMinus) (sigmaPlus := sigmaPlus)
      hm0 hm1 hp0 hp1 m
  calc
    (1 / Real.pi) *
          ((coefficient * (2 / r)) *
            (∫ theta in 0..Real.pi,
              endpointAdjointAngularDensity
                  sigmaMinus sigmaPlus rhoMinus rhoPlus theta *
                (-evenSecondKindAngularMode m theta))) =
        coefficient * ((2 / r) * (1 / Real.pi) *
          (∫ theta in 0..Real.pi,
            endpointAdjointAngularDensity
                sigmaMinus sigmaPlus rhoMinus rhoPlus theta *
              (-evenSecondKindAngularMode m theta))) := by ring
    _ = _ := by rw [hpair]

/-- The outer adjoint pairing of the finite Hilbert transform is exactly
the sum of the mode coefficients from the endpoint calculation. -/
theorem one_div_pi_mul_integral_endpointAdjointDensity_finiteTransform
    {alpha beta : Type*} [Fintype alpha] [Fintype beta]
    {r sigmaMinus sigmaPlus rhoMinus rhoPlus : ℝ}
    (hm0 : 0 ≤ rhoMinus) (hm1 : rhoMinus < 1)
    (hp0 : 0 ≤ rhoPlus) (hp1 : rhoPlus < 1)
    (evenMode : alpha → ℕ) (oddMode : beta → ℕ)
    (evenCoefficient : alpha → ℝ) (oddCoefficient : beta → ℝ) :
    (1 / Real.pi) *
        (∫ theta in 0..Real.pi,
          endpointAdjointAngularDensity
              sigmaMinus sigmaPlus rhoMinus rhoPlus theta *
            finiteEndpointHilbertTransform r evenMode oddMode
              evenCoefficient oddCoefficient theta) =
      (∑ i, evenCoefficient i *
        endpointAdjointEvenCosCoefficient r sigmaMinus sigmaPlus
          rhoMinus rhoPlus (evenMode i)) +
        ∑ i, oddCoefficient i *
          endpointAdjointOddCosCoefficient r sigmaMinus sigmaPlus
            rhoMinus rhoPlus (oddMode i) := by
  classical
  have hEvenTerm (i : alpha) : IntervalIntegrable
      (fun theta : ℝ ↦ endpointAdjointAngularDensity
          sigmaMinus sigmaPlus rhoMinus rhoPlus theta *
        (evenCoefficient i * ((2 / r) *
          (-oddSecondKindAngularMode (evenMode i + 1) theta))))
      volume 0 Real.pi := by
    apply Continuous.intervalIntegrable
    exact (continuous_endpointAdjointAngularDensity hm0 hm1 hp0 hp1).mul
      (continuous_const.mul
        (continuous_const.mul
          (continuous_oddSecondKindAngularMode (evenMode i + 1)).neg))
  have hOddTerm (i : beta) : IntervalIntegrable
      (fun theta : ℝ ↦ endpointAdjointAngularDensity
          sigmaMinus sigmaPlus rhoMinus rhoPlus theta *
        (oddCoefficient i * ((2 / r) *
          (-evenSecondKindAngularMode (oddMode i) theta))))
      volume 0 Real.pi := by
    apply Continuous.intervalIntegrable
    exact (continuous_endpointAdjointAngularDensity hm0 hm1 hp0 hp1).mul
      (continuous_const.mul
        (continuous_const.mul
          (continuous_evenSecondKindAngularMode (oddMode i)).neg))
  let evenIntegrand : ℝ → ℝ :=
    ∑ i, fun theta ↦ endpointAdjointAngularDensity
        sigmaMinus sigmaPlus rhoMinus rhoPlus theta *
      (evenCoefficient i * ((2 / r) *
        (-oddSecondKindAngularMode (evenMode i + 1) theta)))
  let oddIntegrand : ℝ → ℝ :=
    ∑ i, fun theta ↦ endpointAdjointAngularDensity
        sigmaMinus sigmaPlus rhoMinus rhoPlus theta *
      (oddCoefficient i * ((2 / r) *
        (-evenSecondKindAngularMode (oddMode i) theta)))
  have hEvenSum : IntervalIntegrable evenIntegrand volume 0 Real.pi := by
    dsimp [evenIntegrand]
    exact IntervalIntegrable.sum Finset.univ (fun i _hi ↦ hEvenTerm i)
  have hOddSum : IntervalIntegrable oddIntegrand volume 0 Real.pi := by
    dsimp [oddIntegrand]
    exact IntervalIntegrable.sum Finset.univ (fun i _hi ↦ hOddTerm i)
  have hEvenIntegral :
      (∫ theta in 0..Real.pi, evenIntegrand theta) =
        ∑ i, ∫ theta in 0..Real.pi,
          endpointAdjointAngularDensity
              sigmaMinus sigmaPlus rhoMinus rhoPlus theta *
            (evenCoefficient i * ((2 / r) *
              (-oddSecondKindAngularMode (evenMode i + 1) theta))) := by
    dsimp [evenIntegrand]
    simpa only [Finset.sum_apply] using!
      intervalIntegral.integral_finsetSum (s := Finset.univ)
        (fun i _hi ↦ hEvenTerm i)
  have hOddIntegral :
      (∫ theta in 0..Real.pi, oddIntegrand theta) =
        ∑ i, ∫ theta in 0..Real.pi,
          endpointAdjointAngularDensity
              sigmaMinus sigmaPlus rhoMinus rhoPlus theta *
            (oddCoefficient i * ((2 / r) *
              (-evenSecondKindAngularMode (oddMode i) theta))) := by
    dsimp [oddIntegrand]
    simpa only [Finset.sum_apply] using!
      intervalIntegral.integral_finsetSum (s := Finset.univ)
        (fun i _hi ↦ hOddTerm i)
  have hpoint :
      (fun theta : ℝ ↦ endpointAdjointAngularDensity
          sigmaMinus sigmaPlus rhoMinus rhoPlus theta *
        finiteEndpointHilbertTransform r evenMode oddMode
          evenCoefficient oddCoefficient theta) =
      fun theta ↦ evenIntegrand theta + oddIntegrand theta := by
    funext theta
    unfold finiteEndpointHilbertTransform evenIntegrand oddIntegrand
    simp only [mul_add, Finset.mul_sum, Finset.sum_apply]
  calc
    (1 / Real.pi) *
          (∫ theta in 0..Real.pi,
            endpointAdjointAngularDensity
                sigmaMinus sigmaPlus rhoMinus rhoPlus theta *
              finiteEndpointHilbertTransform r evenMode oddMode
                evenCoefficient oddCoefficient theta) =
        (1 / Real.pi) *
          (∫ theta in 0..Real.pi,
            evenIntegrand theta + oddIntegrand theta) := by rw [hpoint]
    _ = (1 / Real.pi) *
          ((∫ theta in 0..Real.pi, evenIntegrand theta) +
            ∫ theta in 0..Real.pi, oddIntegrand theta) := by
      rw [intervalIntegral.integral_add hEvenSum hOddSum]
    _ = _ := by
      rw [hEvenIntegral, hOddIntegral, mul_add,
        Finset.mul_sum, Finset.mul_sum]
      simp_rw [one_div_pi_mul_integral_endpointAdjointDensity_evenTerm
          hm0 hm1 hp0 hp1,
        one_div_pi_mul_integral_endpointAdjointDensity_oddTerm
          hm0 hm1 hp0 hp1]

/-- Exact finite-polynomial endpoint correction with an actual adjoint
interval integral on the left and the endpoint value of `F` on the right. -/
theorem finiteEndpointExteriorVariation_sub_adjointPairing
    {alpha beta : Type*} [Fintype alpha] [Fintype beta]
    {r sigmaMinus sigmaPlus rhoMinus rhoPlus : ℝ}
    (hr : r ≠ 0) (hm : 1 - rhoMinus ^ 2 ≠ 0)
    (hp : 1 - rhoPlus ^ 2 ≠ 0)
    (hm0 : 0 ≤ rhoMinus) (hm1 : rhoMinus < 1)
    (hp0 : 0 ≤ rhoPlus) (hp1 : rhoPlus < 1)
    (f0 : ℝ) (evenMode : alpha → ℕ) (oddMode : beta → ℕ)
    (evenCoefficient : alpha → ℝ) (oddCoefficient : beta → ℝ) :
    finiteEndpointExteriorVariation r sigmaMinus sigmaPlus
        rhoMinus rhoPlus f0 evenMode oddMode
          evenCoefficient oddCoefficient -
      (1 / Real.pi) *
        (∫ theta in 0..Real.pi,
          endpointAdjointAngularDensity
              sigmaMinus sigmaPlus rhoMinus rhoPlus theta *
            finiteEndpointHilbertTransform r evenMode oddMode
              evenCoefficient oddCoefficient theta) =
      -endpointAdjointGamma r sigmaMinus sigmaPlus rhoMinus rhoPlus *
        finiteEndpointCosinePolynomial f0 evenMode oddMode
          evenCoefficient oddCoefficient Real.pi := by
  rw [one_div_pi_mul_integral_endpointAdjointDensity_finiteTransform
      hm0 hm1 hp0 hp1,
    finiteEndpointCosinePolynomial_at_pi]
  unfold finiteEndpointExteriorVariation
  exact finite_endpoint_adjoint_coefficient_identity
    hr hm hp f0 evenMode oddMode evenCoefficient oddCoefficient

end

end Erdos1038
