import ErdosProblems.Erdos1038.PlatformAdjointSpatial

/-!
# Paired Abel truncations for the endpoint-corrected adjoint

The manuscript regularizes a cosine expansion by multiplying its `n`th
coefficient by `lambda^n`.  We use paired truncations containing the first
`N` positive odd modes and the first `N` positive even modes.  This is the
finite input for the later Abel passage.
-/

set_option warningAsError false

open MeasureTheory
open scoped BigOperators

namespace Erdos1038

noncomputable section

def platformAbelEvenCoefficient
    (coefficient : ℕ → ℝ) (lambda : ℝ) {N : ℕ} (m : Fin N) : ℝ :=
  lambda ^ (2 * (m.1 + 1)) * coefficient (2 * (m.1 + 1))

def platformAbelOddCoefficient
    (coefficient : ℕ → ℝ) (lambda : ℝ) {N : ℕ} (m : Fin N) : ℝ :=
  lambda ^ (2 * m.1 + 1) * coefficient (2 * m.1 + 1)

/-- The paired finite Abel cosine truncation. -/
def platformAbelFiniteCosinePolynomial
    (f0 : ℝ) (coefficient : ℕ → ℝ) (lambda : ℝ) (N : ℕ)
    (theta : ℝ) : ℝ :=
  finiteEndpointCosinePolynomial f0
    (fun m : Fin N ↦ m.1) (fun m : Fin N ↦ m.1)
    (platformAbelEvenCoefficient coefficient lambda)
    (platformAbelOddCoefficient coefficient lambda) theta

/-- The finite Hilbert transform of the paired Abel truncation. -/
def platformAbelFiniteHilbertTransform
    (r : ℝ) (coefficient : ℕ → ℝ) (lambda : ℝ) (N : ℕ)
    (theta : ℝ) : ℝ :=
  finiteEndpointHilbertTransform r
    (fun m : Fin N ↦ m.1) (fun m : Fin N ↦ m.1)
    (platformAbelEvenCoefficient coefficient lambda)
    (platformAbelOddCoefficient coefficient lambda) theta

/-- The actual two-crossing exterior variation of a paired Abel
truncation. -/
def platformAbelFiniteExteriorVariation
    (a xMinus xPlus sigmaMinus sigmaPlus f0 : ℝ)
    (coefficient : ℕ → ℝ) (lambda : ℝ) (N : ℕ) : ℝ :=
  finitePlatformExteriorVariation a xMinus xPlus
    sigmaMinus sigmaPlus f0
    (fun m : Fin N ↦ m.1) (fun m : Fin N ↦ m.1)
    (platformAbelEvenCoefficient coefficient lambda)
    (platformAbelOddCoefficient coefficient lambda)

theorem platformAbelFiniteCosinePolynomial_at_pi
    (f0 : ℝ) (coefficient : ℕ → ℝ) (lambda : ℝ) (N : ℕ) :
    platformAbelFiniteCosinePolynomial
        f0 coefficient lambda N Real.pi =
      f0 +
        2 * ∑ m : Fin N,
          lambda ^ (2 * (m.1 + 1)) *
            coefficient (2 * (m.1 + 1)) -
        2 * ∑ m : Fin N,
          lambda ^ (2 * m.1 + 1) *
            coefficient (2 * m.1 + 1) := by
  unfold platformAbelFiniteCosinePolynomial
  rw [finiteEndpointCosinePolynomial_at_pi]
  rfl

/-- Exact platform endpoint correction for every paired Abel truncation. -/
theorem platformAbelFiniteExteriorVariation_sub_adjointPairing
    {a xMinus xPlus sigmaMinus sigmaPlus : ℝ}
    (hxMinus : xMinus < a) (hxPlus : xPlus < a) (ha2 : a < 2)
    (f0 : ℝ) (coefficient : ℕ → ℝ) (lambda : ℝ) (N : ℕ) :
    platformAbelFiniteExteriorVariation a xMinus xPlus
        sigmaMinus sigmaPlus f0 coefficient lambda N -
      (1 / Real.pi) *
        (∫ theta in 0..Real.pi,
          platformAngularAdjointDensity
              a xMinus xPlus sigmaMinus sigmaPlus theta *
            platformAbelFiniteHilbertTransform
              (platformRadius a) coefficient lambda N theta) =
      -endpointAdjointGamma (platformRadius a) sigmaMinus sigmaPlus
          (platformRho a xMinus) (platformRho a xPlus) *
        platformAbelFiniteCosinePolynomial
          f0 coefficient lambda N Real.pi := by
  unfold platformAbelFiniteExteriorVariation
    platformAbelFiniteHilbertTransform
    platformAbelFiniteCosinePolynomial
  exact finitePlatformExteriorVariation_sub_platformAdjointPairing
    hxMinus hxPlus ha2 f0
      (fun m : Fin N ↦ m.1) (fun m : Fin N ↦ m.1)
      (platformAbelEvenCoefficient coefficient lambda)
      (platformAbelOddCoefficient coefficient lambda)

end

end Erdos1038
