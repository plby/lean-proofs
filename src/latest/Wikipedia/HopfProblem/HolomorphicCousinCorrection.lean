import Wikipedia.HopfProblem.HolomorphicCousinLocalForcing
import Wikipedia.HopfProblem.HolomorphicCousinConvolutionSolution
import Wikipedia.HopfProblem.HolomorphicCousinConvolutionInfinity
import Wikipedia.HopfProblem.HolomorphicCousinDivision

/-!
# Correcting local cochains by the actual Cauchy--Green solution

The correction in this file is an explicit convergent convolution of the
global forcing term constructed from the local data.  Its antiholomorphic
derivative is proved equal to that forcing term.  Subtraction gives genuine
holomorphic local representatives, and the explicit reciprocal-coordinate
integral supplies their extension at infinity in the normalized patch.
-/

noncomputable section

open Complex Metric Set
open scoped Topology ContDiff

namespace Wikipedia.HopfProblem.HolomorphicCousin.LocalPotential

variable {ι : Type*} (P : LocalPotential ι)

/-- The corrected local representatives, using the proved integral solver. -/
def correctedPart (i : ι) (z : ℂ) : ℂ :=
  P.potential i z - cauchyGreen P.forcing z

/-- The correction makes each local representative holomorphic. -/
theorem correctedPart_analytic (hc : HasCompactSupport P.forcing) (i : ι) :
    AnalyticOnNhd ℂ (P.correctedPart i) (P.domain i) := by
  obtain ⟨hs, he⟩ := cauchyGreen_smooth_dbar_solution P.forcing_contDiff hc
  exact P.corrected_analytic (hs.differentiable (by simp)) he i

/-- The original transition functions are preserved exactly. -/
theorem correctedPart_sub (i j : ι) (z : ℂ) :
    P.correctedPart i z - P.correctedPart j z =
      P.potential i z - P.potential j z :=
  P.corrected_difference (cauchyGreen P.forcing) i j z

/-- Reciprocal-coordinate extension in any patch where the chosen smooth
representative was normalized to zero. -/
def correctedInfinity (u : ℂ) : ℂ := -cauchyGreenInfinity P.forcing u

@[simp] theorem correctedInfinity_zero : P.correctedInfinity 0 = 0 := by
  simp [correctedInfinity]

theorem correctedInfinity_analytic (hc : HasCompactSupport P.forcing)
    {R : ℝ} (hR : 0 < R)
    (hbound : ∀ z ∈ Function.support P.forcing, ‖z‖ ≤ R) :
    AnalyticOnNhd ℂ P.correctedInfinity (ball 0 R⁻¹) :=
  (analyticOnNhd_cauchyGreenInfinity P.forcing_contDiff.continuous hc hR hbound).neg

theorem correctedInfinity_analyticAt_zero (hc : HasCompactSupport P.forcing) :
    AnalyticAt ℂ P.correctedInfinity 0 :=
  (analyticAt_cauchyGreenInfinity_zero P.forcing_contDiff.continuous hc).neg

/-- Exact agreement with the reciprocal-coordinate function. -/
theorem correctedPart_eq_infinity {i : ι} {z : ℂ} (hz : z ≠ 0)
    (hs : P.potential i z = 0) :
    P.correctedPart i z = P.correctedInfinity z⁻¹ := by
  simp only [correctedPart, hs, zero_sub, correctedInfinity,
    cauchyGreenInfinity_inv P.forcing hz]

/-- Dividing by the reciprocal coordinate gives the coefficient in the
infinity frame for `O(-1)`. -/
def correctedInfinityFactor : ℂ → ℂ := dslope P.correctedInfinity 0

theorem correctedInfinityFactor_analytic (hc : HasCompactSupport P.forcing)
    {R : ℝ} (hR : 0 < R)
    (hbound : ∀ z ∈ Function.support P.forcing, ‖z‖ ≤ R) :
    AnalyticOnNhd ℂ P.correctedInfinityFactor (ball 0 R⁻¹) :=
  analyticOnNhd_dslope_zero (inv_pos.mpr hR) (P.correctedInfinity_analytic hc hR hbound)

theorem correctedPart_eq_negativeOne {i : ι} {z : ℂ} (hz : z ≠ 0)
    (hs : P.potential i z = 0) :
    P.correctedPart i z = z⁻¹ * P.correctedInfinityFactor z⁻¹ := by
  rw [P.correctedPart_eq_infinity hz hs]
  exact (zero_mul_dslope P.correctedInfinity_zero z⁻¹).symm

end Wikipedia.HopfProblem.HolomorphicCousin.LocalPotential
