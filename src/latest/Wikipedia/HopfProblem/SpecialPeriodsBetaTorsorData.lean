import Wikipedia.HopfProblem.SpecialPeriodsBetaTorsorLocalCusp
import Wikipedia.HopfProblem.SpecialPeriodsBetaTorsorCocycleHolomorphic
import Wikipedia.HopfProblem.SpecialPeriodsBetaTorsorCocycleCovariance
import Wikipedia.HopfProblem.SpecialPeriodsBetaTorsorCocycleCusp

/-!
# The beta torsor constructed from actual tau and mu functions

The input consists only of holomorphic tau and mu and their two native
generator equations.  Their proved cyclic identities construct the genuine
all-word additive cocycle over the actual triangle action.  No beta section,
local beta representative, or trivialization is an input.
-/

noncomputable section

open Set UpperHalfPlane
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.SpecialPeriods.BetaTorsor

/-- Actual tau and mu data, prior to constructing any beta function. -/
structure Data where
  tau : ℍ → ℍ
  mu : ℍ → ℂ
  tau_holomorphic : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω tau
  mu_holomorphic : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω mu
  tau_covariant : TauCovariant tau
  mu_one : ∀ z : ℍ, mu (Triangle.generatorOneSL • z) = (1 - mu z) / (tau z : ℂ)
  mu_two : ∀ z : ℍ, mu (Triangle.generatorTwoSL • z) = 1 + mu z / (tau z : ℂ)

namespace Data

variable (D : Data)

/-- The beta cocycle is constructed by the actual skew-permutation
representation and the proved cyclic relations of its native terms. -/
def cocycle : MuTorsor.AffineCocycle :=
  triangleAdditiveCocycle (phiOne D.tau D.mu) (phiTwo D.tau D.mu)
    (phiOne_sum_range D.tau_covariant D.mu_one)
    (phiTwo_sum_range D.tau_covariant D.mu_two)
    (phiOne_holomorphic D.tau_holomorphic D.mu_holomorphic)
    (phiTwo_holomorphic D.tau_holomorphic D.mu_holomorphic)

/-- Its actual additive shift for every word of the triangle group. -/
def shift : TriangleGroup → ℍ → ℂ :=
  triangleAdditiveShift (phiOne D.tau D.mu) (phiTwo D.tau D.mu)
    (phiOne_sum_range D.tau_covariant D.mu_one)
    (phiTwo_sum_range D.tau_covariant D.mu_two)

@[simp] theorem cocycle_scale (g : TriangleGroup) (z : ℍ) : D.cocycle.scale g z = 1 := rfl

@[simp] theorem cocycle_shift (g : TriangleGroup) (z : ℍ) :
    D.cocycle.shift g z = D.shift g z := rfl

theorem cocycle_fibreMap (g : TriangleGroup) (z : ℍ) (u : ℂ) :
    D.cocycle.fibreMap g z u = u + D.shift g z := by
  simp only [MuTorsor.AffineCocycle.fibreMap, D.cocycle_scale,
    Units.val_one, one_mul, D.cocycle_shift]

@[simp] theorem shift_one (z : ℍ) : D.shift 1 z = 0 :=
  triangleAdditiveShift_one ..

theorem shift_mul (g h : TriangleGroup) (z : ℍ) :
    D.shift (g * h) z = D.shift g (triangleGeometricRepresentation h z) + D.shift h z :=
  triangleAdditiveShift_mul ..

theorem shift_inv (g : TriangleGroup) (z : ℍ) :
    D.shift g⁻¹ z = -D.shift g (triangleGeometricRepresentation g⁻¹ z) :=
  triangleAdditiveShift_inv ..

@[simp] theorem shift_generator₁ (z : ℍ) : D.shift triangleGenerator₁ z = phiOne D.tau D.mu z :=
  triangleAdditiveShift_generator₁ ..

@[simp] theorem shift_generator₂ (z : ℍ) : D.shift triangleGenerator₂ z = phiTwo D.tau D.mu z :=
  triangleAdditiveShift_generator₂ ..

theorem shift_holomorphic (g : TriangleGroup) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (D.shift g) :=
  D.cocycle.shift_holomorphic g

/-- The product of the two elliptic generators has exact shift minus one. -/
theorem shift_product (z : ℍ) : D.shift (triangleGenerator₁ * triangleGenerator₂) z = -1 := by
  rw [D.shift_mul, D.shift_generator₁, D.shift_generator₂,
    triangleGeometricRepresentation_generator₂_apply]
  exact phi_product_relation D.tau_covariant D.mu_two z

/-- The actual clockwise cusp word has beta shift one. -/
@[simp] theorem shift_cusp (z : ℍ) : D.shift triangleCuspGenerator z = 1 :=
  triangleAdditiveShift_cusp (phiOne D.tau D.mu) (phiTwo D.tau D.mu)
    (phiOne_sum_range D.tau_covariant D.mu_one)
    (phiTwo_sum_range D.tau_covariant D.mu_two)
    (phi_product_relation D.tau_covariant D.mu_two) z

/-- The entire actual cusp subgroup has the prescribed integer beta shift. -/
@[simp] theorem shift_cusp_zpow (n : ℤ) (z : ℍ) :
    D.shift (triangleCuspGenerator ^ n) z = (n : ℂ) :=
  triangleAdditiveShift_cusp_zpow (phiOne D.tau D.mu) (phiTwo D.tau D.mu)
    (phiOne_sum_range D.tau_covariant D.mu_one)
    (phiTwo_sum_range D.tau_covariant D.mu_two)
    (phi_product_relation D.tau_covariant D.mu_two) n z

/-- A seed's equation under a cyclic generator implies all of the actual
returning-subgroup equations. -/
theorem covariance_zpowers (β : ℍ → ℂ) (g : TriangleGroup)
    (hg : ∀ z : ℍ, β (triangleGeometricRepresentation g z) = β z + D.shift g z)
    {h : TriangleGroup} (hh : h ∈ Subgroup.zpowers g) (z : ℍ) :
    β (triangleGeometricRepresentation h z) = β z + D.shift h z :=
  BetaTorsor.covariance_zpowers D.shift D.shift_one D.shift_mul D.shift_inv β g hg hh z

end Data

end Wikipedia.HopfProblem.SpecialPeriods.BetaTorsor
