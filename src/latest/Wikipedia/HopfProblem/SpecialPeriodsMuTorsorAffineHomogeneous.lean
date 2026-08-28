import Wikipedia.HopfProblem.SpecialPeriodsMuTorsorAffine
import Wikipedia.HopfProblem.SpecialPeriodsMuGeneratorConstruction

/-!
# The homogeneous μ law for every triangle-group element

The two homogeneous generator equations describe a section for the linear
part of the actual affine cocycle. Its section stabilizer is a subgroup,
and the two triangle generators generate the whole group. Consequently
the homogeneous law holds for every actual geometric group action.
-/

noncomputable section

open Set UpperHalfPlane
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.SpecialPeriods.MuTorsor

namespace AffineCocycle

/-- The associated linear cocycle retains the proved unit scale and sets
the affine translation to zero. -/
def linearPart (c : AffineCocycle) : AffineCocycle where
  scale := c.scale
  shift _ _ := 0
  scale_one := c.scale_one
  shift_one _ := rfl
  scale_mul := c.scale_mul
  shift_mul _ _ _ := by simp
  scale_holomorphic := c.scale_holomorphic
  shift_holomorphic _ := contMDiff_const

@[simp] theorem linearPart_fibreMap (c : AffineCocycle)
    (g : TriangleGroup) (z : ℍ) (u : ℂ) :
    c.linearPart.fibreMap g z u = (c.scale g z : ℂ) * u := by
  exact add_zero _

end AffineCocycle

/-- The actual homogeneous generator laws imply the scale law for all
words in the genuine triangle group. No equivariance is assumed beyond
the two original generator equations. -/
theorem homogeneous_scale_law {τ : ℍ → ℍ} (hτ : TauCovariant τ)
    (hτa : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω τ) {F : ℍ → ℂ}
    (hF : MuGenerator.Homogeneous τ F) (g : TriangleGroup) (z : ℍ) :
    F (triangleGeometricRepresentation g z) = ((cocycle hτ hτa).scale g z : ℂ) * F z := by
  let K := (cocycle hτ hτa).linearPart.sectionStabilizer F
  have h₁ : triangleGenerator₁ ∈ K := by
    intro w
    rw [triangleGeometricRepresentation_generator₁_apply, AffineCocycle.linearPart_fibreMap,
      cocycle_scale_generator₁_val, hF.1 w]
    ring
  have h₂ : triangleGenerator₂ ∈ K := by
    intro w
    rw [triangleGeometricRepresentation_generator₂_apply, AffineCocycle.linearPart_fibreMap,
      cocycle_scale_generator₂_val, hF.2 w]
    ring
  have hle : Subgroup.closure ({triangleGenerator₁, triangleGenerator₂} : Set TriangleGroup) ≤ K :=
    (Subgroup.closure_le _).mpr (by
      intro x hx
      rcases hx with rfl | rfl
      · exact h₁
      · exact h₂)
  rw [triangle_generators_generate] at hle
  have hz := hle (Subgroup.mem_top g) z
  simpa only [AffineCocycle.linearPart_fibreMap] using hz

end Wikipedia.HopfProblem.SpecialPeriods.MuTorsor
