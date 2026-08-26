import ErdosProblems.Erdos1038.PlatformPoissonSecondKind

/-!
# The finite endpoint-adjoint coefficient cancellation

This file isolates the algebraic heart of the endpoint correction.  Once a
finite cosine polynomial has been sent through the finite Hilbert transform,
the exterior derivative and the adjoint pairing have the coefficients below.
The two parity identities show that their difference is exactly evaluation at
`θ = π`, multiplied by `-Γ`.
-/

set_option warningAsError false

open scoped BigOperators

namespace Erdos1038

noncomputable section

/-- The rational value `P_ρ(0)`. -/
def endpointPoissonZero (rho : ℝ) : ℝ :=
  (1 + 2 * rho + rho ^ 2) / (1 - rho ^ 2)

/-- `Γ = ∑ σ_j / K_j`, written in Poisson coordinates. -/
def endpointAdjointGamma
    (r sigmaMinus sigmaPlus rhoMinus rhoPlus : ℝ) : ℝ :=
  (2 / r) *
    (sigmaMinus * rhoMinus / (1 - rhoMinus ^ 2) +
      sigmaPlus * rhoPlus / (1 - rhoPlus ^ 2))

/-- The endpoint normalization `D = ∑ σ_j P_{ρ_j}(0)`. -/
def endpointAdjointD
    (sigmaMinus sigmaPlus rhoMinus rhoPlus : ℝ) : ℝ :=
  sigmaMinus * endpointPoissonZero rhoMinus +
    sigmaPlus * endpointPoissonZero rhoPlus

/-- Coefficient of `f_n` in the exterior first variation. -/
def endpointExteriorCosCoefficient
    (r sigmaMinus sigmaPlus rhoMinus rhoPlus : ℝ) (n : ℕ) : ℝ :=
  -(4 / r) *
    (sigmaMinus * rhoMinus ^ (n + 1) / (1 - rhoMinus ^ 2) +
      sigmaPlus * rhoPlus ^ (n + 1) / (1 - rhoPlus ^ 2))

/-- Coefficient of an even cosine mode in the adjoint pairing. -/
def endpointAdjointEvenCosCoefficient
    (r sigmaMinus sigmaPlus rhoMinus rhoPlus : ℝ) (m : ℕ) : ℝ :=
  (2 / r) *
    (sigmaMinus *
        (2 * rhoMinus * (1 - rhoMinus ^ (2 * (m + 1))) /
          (1 - rhoMinus ^ 2)) +
      sigmaPlus *
        (2 * rhoPlus * (1 - rhoPlus ^ (2 * (m + 1))) /
          (1 - rhoPlus ^ 2)))

/-- Coefficient of an odd cosine mode in the adjoint pairing. -/
def endpointAdjointOddCosCoefficient
    (r sigmaMinus sigmaPlus rhoMinus rhoPlus : ℝ) (m : ℕ) : ℝ :=
  -(2 / r) *
    (endpointAdjointD sigmaMinus sigmaPlus rhoMinus rhoPlus -
      (sigmaMinus *
          ((1 + rhoMinus ^ 2 - 2 * rhoMinus ^ (2 * m + 2)) /
            (1 - rhoMinus ^ 2)) +
        sigmaPlus *
          ((1 + rhoPlus ^ 2 - 2 * rhoPlus ^ (2 * m + 2)) /
            (1 - rhoPlus ^ 2))))

theorem endpointExterior_sub_adjoint_even
    {r sigmaMinus sigmaPlus rhoMinus rhoPlus : ℝ}
    (hr : r ≠ 0) (hm : 1 - rhoMinus ^ 2 ≠ 0)
    (hp : 1 - rhoPlus ^ 2 ≠ 0) (m : ℕ) :
    endpointExteriorCosCoefficient r sigmaMinus sigmaPlus
        rhoMinus rhoPlus (2 * (m + 1)) -
      endpointAdjointEvenCosCoefficient r sigmaMinus sigmaPlus
        rhoMinus rhoPlus m =
      -2 * endpointAdjointGamma r sigmaMinus sigmaPlus rhoMinus rhoPlus := by
  unfold endpointExteriorCosCoefficient endpointAdjointEvenCosCoefficient
    endpointAdjointGamma
  simp only [pow_add, pow_one]
  field_simp [hr, hm, hp]
  ring

theorem endpointExterior_sub_adjoint_odd
    {r sigmaMinus sigmaPlus rhoMinus rhoPlus : ℝ}
    (hr : r ≠ 0) (hm : 1 - rhoMinus ^ 2 ≠ 0)
    (hp : 1 - rhoPlus ^ 2 ≠ 0) (m : ℕ) :
    endpointExteriorCosCoefficient r sigmaMinus sigmaPlus
        rhoMinus rhoPlus (2 * m + 1) -
      endpointAdjointOddCosCoefficient r sigmaMinus sigmaPlus
        rhoMinus rhoPlus m =
      2 * endpointAdjointGamma r sigmaMinus sigmaPlus rhoMinus rhoPlus := by
  unfold endpointExteriorCosCoefficient endpointAdjointOddCosCoefficient
    endpointAdjointD endpointPoissonZero endpointAdjointGamma
  simp only [pow_add, pow_one]
  field_simp [hr, hm, hp]
  ring

/-- The complete finite cosine coefficient calculation.  Even and odd modes
may be indexed by arbitrary finite types; their natural numbers record the
frequencies `2(m+1)` and `2m+1`, respectively. -/
theorem finite_endpoint_adjoint_coefficient_identity
    {α β : Type*} [Fintype α] [Fintype β]
    {r sigmaMinus sigmaPlus rhoMinus rhoPlus : ℝ}
    (hr : r ≠ 0) (hm : 1 - rhoMinus ^ 2 ≠ 0)
    (hp : 1 - rhoPlus ^ 2 ≠ 0)
    (f0 : ℝ) (evenMode : α → ℕ) (oddMode : β → ℕ)
    (evenCoefficient : α → ℝ) (oddCoefficient : β → ℝ) :
    (-endpointAdjointGamma r sigmaMinus sigmaPlus rhoMinus rhoPlus * f0 +
          ∑ i, evenCoefficient i *
            endpointExteriorCosCoefficient r sigmaMinus sigmaPlus
              rhoMinus rhoPlus (2 * (evenMode i + 1)) +
          ∑ i, oddCoefficient i *
            endpointExteriorCosCoefficient r sigmaMinus sigmaPlus
              rhoMinus rhoPlus (2 * oddMode i + 1)) -
        ((∑ i, evenCoefficient i *
            endpointAdjointEvenCosCoefficient r sigmaMinus sigmaPlus
              rhoMinus rhoPlus (evenMode i)) +
          ∑ i, oddCoefficient i *
            endpointAdjointOddCosCoefficient r sigmaMinus sigmaPlus
              rhoMinus rhoPlus (oddMode i)) =
      -endpointAdjointGamma r sigmaMinus sigmaPlus rhoMinus rhoPlus *
        (f0 + 2 * ∑ i, evenCoefficient i -
          2 * ∑ i, oddCoefficient i) := by
  let Gamma := endpointAdjointGamma r sigmaMinus sigmaPlus rhoMinus rhoPlus
  have heven :
      (∑ i, evenCoefficient i *
          endpointExteriorCosCoefficient r sigmaMinus sigmaPlus
            rhoMinus rhoPlus (2 * (evenMode i + 1))) -
        ∑ i, evenCoefficient i *
          endpointAdjointEvenCosCoefficient r sigmaMinus sigmaPlus
            rhoMinus rhoPlus (evenMode i) =
      -2 * Gamma * ∑ i, evenCoefficient i := by
    rw [← Finset.sum_sub_distrib]
    simp_rw [← mul_sub,
      endpointExterior_sub_adjoint_even hr hm hp]
    rw [← Finset.sum_mul]
    ring
  have hodd :
      (∑ i, oddCoefficient i *
          endpointExteriorCosCoefficient r sigmaMinus sigmaPlus
            rhoMinus rhoPlus (2 * oddMode i + 1)) -
        ∑ i, oddCoefficient i *
          endpointAdjointOddCosCoefficient r sigmaMinus sigmaPlus
            rhoMinus rhoPlus (oddMode i) =
      2 * Gamma * ∑ i, oddCoefficient i := by
    rw [← Finset.sum_sub_distrib]
    simp_rw [← mul_sub,
      endpointExterior_sub_adjoint_odd hr hm hp]
    rw [← Finset.sum_mul]
    ring
  change (-Gamma * f0 + _ + _) - (_ + _) = -Gamma * _
  calc
    (-Gamma * f0 +
          ∑ i, evenCoefficient i *
            endpointExteriorCosCoefficient r sigmaMinus sigmaPlus
              rhoMinus rhoPlus (2 * (evenMode i + 1)) +
          ∑ i, oddCoefficient i *
            endpointExteriorCosCoefficient r sigmaMinus sigmaPlus
              rhoMinus rhoPlus (2 * oddMode i + 1)) -
        ((∑ i, evenCoefficient i *
            endpointAdjointEvenCosCoefficient r sigmaMinus sigmaPlus
              rhoMinus rhoPlus (evenMode i)) +
          ∑ i, oddCoefficient i *
            endpointAdjointOddCosCoefficient r sigmaMinus sigmaPlus
              rhoMinus rhoPlus (oddMode i)) =
      -Gamma * f0 +
        ((∑ i, evenCoefficient i *
            endpointExteriorCosCoefficient r sigmaMinus sigmaPlus
              rhoMinus rhoPlus (2 * (evenMode i + 1))) -
          ∑ i, evenCoefficient i *
            endpointAdjointEvenCosCoefficient r sigmaMinus sigmaPlus
              rhoMinus rhoPlus (evenMode i)) +
        ((∑ i, oddCoefficient i *
            endpointExteriorCosCoefficient r sigmaMinus sigmaPlus
              rhoMinus rhoPlus (2 * oddMode i + 1)) -
          ∑ i, oddCoefficient i *
            endpointAdjointOddCosCoefficient r sigmaMinus sigmaPlus
              rhoMinus rhoPlus (oddMode i)) := by ring
    _ = -Gamma * f0 +
        (-2 * Gamma * ∑ i, evenCoefficient i) +
        (2 * Gamma * ∑ i, oddCoefficient i) := by rw [heven, hodd]
    _ = -Gamma *
        (f0 + 2 * ∑ i, evenCoefficient i -
          2 * ∑ i, oddCoefficient i) := by ring

lemma endpointPoissonZero_eq_kernel_zero
    {rho : ℝ} (hrhoOne : rho ≠ 1) (hrhoNegOne : rho ≠ -1) :
    endpointPoissonZero rho = platformPoissonKernel rho 0 := by
  rw [platformPoissonKernel_zero hrhoOne]
  unfold endpointPoissonZero
  have hminus : 1 - rho ≠ 0 := sub_ne_zero.mpr hrhoOne.symm
  have hplus : 1 + rho ≠ 0 := by
    intro h
    apply hrhoNegOne
    linarith
  rw [show 1 - rho ^ 2 = (1 - rho) * (1 + rho) by ring]
  field_simp [hminus, hplus]
  ring

theorem endpointAdjointD_eq_adjointNormalization
    {a xMinus xPlus sigmaMinus sigmaPlus : ℝ}
    (hxMinus : xMinus < a) (hxPlus : xPlus < a) (ha2 : a < 2) :
    endpointAdjointD sigmaMinus sigmaPlus
        (platformRho a xMinus) (platformRho a xPlus) =
      adjointNormalization a xMinus xPlus sigmaMinus sigmaPlus := by
  have hrm := platformRho_mem_Ioo hxMinus ha2
  have hrp := platformRho_mem_Ioo hxPlus ha2
  rw [adjointNormalization_eq_poisson_zero hxMinus hxPlus ha2]
  unfold endpointAdjointD
  rw [endpointPoissonZero_eq_kernel_zero
      (ne_of_lt hrm.2) (by linarith [hrm.1]),
    endpointPoissonZero_eq_kernel_zero
      (ne_of_lt hrp.2) (by linarith [hrp.1])]

lemma endpointGamma_crossingTerm
    {a x sigma : ℝ} (hx : x < a) (ha2 : a < 2) :
    (2 / platformRadius a) *
        (sigma * platformRho a x / (1 - platformRho a x ^ 2)) =
      sigma / platformCrossingScale a x := by
  have hr : 0 < platformRadius a := platformRadius_pos ha2
  have hK : 0 < platformCrossingScale a x :=
    platformCrossingScale_pos hx ha2
  have hrho := platformRho_mem_Ioo hx ha2
  have hsquare : platformRho a x ^ 2 < 1 := by
    simpa [pow_two] using! mul_self_lt_mul_self hrho.1.le hrho.2
  have hden : 0 < 1 - platformRho a x ^ 2 := sub_pos.mpr hsquare
  have hid := platformRho_crossing_identity hx ha2
  field_simp [hr.ne', hK.ne', hden.ne']
  linear_combination sigma * hid

theorem endpointAdjointGamma_eq_crossingScales
    {a xMinus xPlus sigmaMinus sigmaPlus : ℝ}
    (hxMinus : xMinus < a) (hxPlus : xPlus < a) (ha2 : a < 2) :
    endpointAdjointGamma (platformRadius a) sigmaMinus sigmaPlus
        (platformRho a xMinus) (platformRho a xPlus) =
      sigmaMinus / platformCrossingScale a xMinus +
        sigmaPlus / platformCrossingScale a xPlus := by
  unfold endpointAdjointGamma
  rw [mul_add,
    endpointGamma_crossingTerm hxMinus ha2,
    endpointGamma_crossingTerm hxPlus ha2]

end

end Erdos1038
