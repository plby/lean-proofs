import Wikipedia.HopfProblem.SpecialPeriodsBetaTorsorLocal

/-!
# The cusp primitive and mu invariance from the generator laws

The two elliptic mu equations force invariance under the actual cusp
generator and all its integer powers.  The previously proved tau covariance
then gives the explicit holomorphic cusp beta primitive `-tau`, whose
increment under the clockwise cusp generator is one.
-/

noncomputable section

open Set UpperHalfPlane
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.SpecialPeriods.BetaTorsor

/-- The product of the two elliptic transformations leaves mu unchanged. -/
theorem mu_product {τ : ℍ → ℍ} {μ : ℍ → ℂ}
    (hτ : TauCovariant τ)
    (hμ₁ : ∀ z : ℍ, μ (Triangle.generatorOneSL • z) = (1 - μ z) / (τ z : ℂ))
    (hμ₂ : ∀ z : ℍ, μ (Triangle.generatorTwoSL • z) = 1 + μ z / (τ z : ℂ))
    (z : ℍ) : μ (Triangle.generatorOneSL • (Triangle.generatorTwoSL • z)) = μ z := by
  let p : PeriodPoint := ⟨τ z, μ z, 0⟩
  have hp := congrArg PeriodPoint.μ (p.step₁_step₂ (τ z).ne_zero)
  rw [hμ₁, hμ₂, hτ.2]
  exact hp

theorem mu_product_word {τ : ℍ → ℍ} {μ : ℍ → ℂ}
    (hτ : TauCovariant τ)
    (hμ₁ : ∀ z : ℍ, μ (Triangle.generatorOneSL • z) = (1 - μ z) / (τ z : ℂ))
    (hμ₂ : ∀ z : ℍ, μ (Triangle.generatorTwoSL • z) = 1 + μ z / (τ z : ℂ))
    (z : ℍ) :
    μ (triangleGeometricRepresentation (triangleGenerator₁ * triangleGenerator₂) z) = μ z := by
  rw [map_mul, Equiv.Perm.mul_apply, triangleGeometricRepresentation_generator₁_apply,
    triangleGeometricRepresentation_generator₂_apply]
  exact mu_product hτ hμ₁ hμ₂ z

/-- The cusp invariance of mu is a consequence of the two elliptic laws. -/
theorem mu_cusp {τ : ℍ → ℍ} {μ : ℍ → ℂ}
    (hτ : TauCovariant τ)
    (hμ₁ : ∀ z : ℍ, μ (Triangle.generatorOneSL • z) = (1 - μ z) / (τ z : ℂ))
    (hμ₂ : ∀ z : ℍ, μ (Triangle.generatorTwoSL • z) = 1 + μ z / (τ z : ℂ))
    (z : ℍ) : μ (triangleGeometricRepresentation triangleCuspGenerator z) = μ z := by
  have hp := mu_product_word hτ hμ₁ hμ₂
    (triangleGeometricRepresentation triangleCuspGenerator z)
  have he : triangleGeometricRepresentation (triangleGenerator₁ * triangleGenerator₂)
      (triangleGeometricRepresentation triangleCuspGenerator z) = z := by
    rw [← Equiv.Perm.mul_apply, ← map_mul, triangle_generators_cusp_relation, map_one]
    rfl
  rw [he] at hp
  exact hp.symm

/-- Every integer power of the actual cusp generator leaves mu unchanged. -/
theorem mu_cusp_zpow {τ : ℍ → ℍ} {μ : ℍ → ℂ}
    (hτ : TauCovariant τ)
    (hμ₁ : ∀ z : ℍ, μ (Triangle.generatorOneSL • z) = (1 - μ z) / (τ z : ℂ))
    (hμ₂ : ∀ z : ℍ, μ (Triangle.generatorTwoSL • z) = 1 + μ z / (τ z : ℂ))
    (n : ℤ) (z : ℍ) :
    μ (triangleGeometricRepresentation (triangleCuspGenerator ^ n) z) = μ z := by
  let K := TauEquivariance.intertwiningSubgroup triangleGeometricRepresentation
    (1 : TriangleGroup →* Equiv.Perm ℂ) μ
  have hk : triangleCuspGenerator ∈ K := by
    intro w
    exact mu_cusp hτ hμ₁ hμ₂ w
  exact K.zpow_mem hk n z

/-- The same invariance in the actual horizontal cusp coordinate. -/
theorem mu_cusp_translation {τ : ℍ → ℍ} {μ : ℍ → ℂ}
    (hτ : TauCovariant τ)
    (hμ₁ : ∀ z : ℍ, μ (Triangle.generatorOneSL • z) = (1 - μ z) / (τ z : ℂ))
    (hμ₂ : ∀ z : ℍ, μ (Triangle.generatorTwoSL • z) = 1 + μ z / (τ z : ℂ))
    (z : ℍ) : μ ((-Triangle.width) +ᵥ z) = μ z := by
  simpa only [triangleGeometricRepresentation_cusp_apply] using mu_cusp hτ hμ₁ hμ₂ z

/-- An explicit primitive for the cusp beta equation.  It is not claimed to
solve both elliptic beta equations simultaneously. -/
def cuspPrimitive (τ : ℍ → ℍ) (z : ℍ) : ℂ := -(τ z : ℂ)

theorem cuspPrimitive_holomorphic {τ : ℍ → ℍ}
    (hτ : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω τ) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (cuspPrimitive τ) :=
  (UpperHalfPlane.contMDiff_coe.comp hτ).neg

/-- The clockwise cusp generator has beta increment one. -/
theorem cuspPrimitive_difference {τ : ℍ → ℍ} (hτ : TauCovariant τ) (z : ℍ) :
    cuspPrimitive τ (triangleGeometricRepresentation triangleCuspGenerator z) -
      cuspPrimitive τ z = 1 := by
  rw [cuspPrimitive, cuspPrimitive, tau_covariant_cusp_coe hτ]
  ring

/-- The cusp primitive realizes the exact increment for every integer turn. -/
theorem cuspPrimitive_zpow_difference {τ : ℍ → ℍ} (hτ : TauCovariant τ)
    (n : ℤ) (z : ℍ) :
    cuspPrimitive τ (triangleGeometricRepresentation (triangleCuspGenerator ^ n) z) -
      cuspPrimitive τ z = (n : ℂ) := by
  rw [cuspPrimitive, cuspPrimitive, tau_covariant_cusp_zpow hτ]
  ring

end Wikipedia.HopfProblem.SpecialPeriods.BetaTorsor
