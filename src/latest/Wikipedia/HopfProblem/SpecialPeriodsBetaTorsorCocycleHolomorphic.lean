import Wikipedia.HopfProblem.SpecialPeriodsMuTorsorCore
import Wikipedia.HopfProblem.SpecialPeriodsBetaTorsorCocycle

/-!
# Holomorphic additive cocycles for the beta torsor

Holomorphy of an additive cocycle over the actual triangle action follows
from holomorphy of its values on the two generators.  The proof uses the
proved generation theorem and holomorphy of the geometric triangle action.
-/

noncomputable section

open Set UpperHalfPlane
open scoped BigOperators ContDiff Manifold

namespace Wikipedia.HopfProblem.SpecialPeriods.BetaTorsor

private theorem additive_cocycle_holomorphic
    (b : TriangleGroup → ℍ → ℂ)
    (hone : ∀ z, b 1 z = 0)
    (hmul : ∀ g h z, b (g * h) z = b g (triangleGeometricRepresentation h z) + b h z)
    (hinv : ∀ g z, b g⁻¹ z = -b g (triangleGeometricRepresentation g⁻¹ z))
    (h₁ : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (b triangleGenerator₁))
    (h₂ : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (b triangleGenerator₂))
    (g : TriangleGroup) : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (b g) := by
  have hg : g ∈ Subgroup.closure
      ({triangleGenerator₁, triangleGenerator₂} : Set TriangleGroup) := by
    rw [triangle_generators_generate]
    exact Subgroup.mem_top g
  induction hg using Subgroup.closure_induction with
  | mem g hg =>
    rcases Set.mem_insert_iff.mp hg with rfl | hg
    · exact h₁
    · have he : g = triangleGenerator₂ := Set.mem_singleton_iff.mp hg
      subst g
      exact h₂
  | one =>
    have he : b 1 = fun _ => 0 := funext hone
    rw [he]
    exact contMDiff_const
  | mul g h _ _ ihg ihh =>
    have he : b (g * h) = fun z => b g (triangleGeometricRepresentation h z) + b h z :=
      funext (hmul g h)
    rw [he]
    exact (ihg.comp (triangleGeometricRepresentation_holomorphic h)).add ihh
  | inv g _ ihg =>
    have he : b g⁻¹ = fun z => -b g (triangleGeometricRepresentation g⁻¹ z) :=
      funext (hinv g)
    rw [he]
    exact (ihg.comp (triangleGeometricRepresentation_holomorphic g⁻¹)).neg

private def additiveAffineCocycle
    (b : TriangleGroup → ℍ → ℂ)
    (hone : ∀ z, b 1 z = 0)
    (hmul : ∀ g h z, b (g * h) z = b g (triangleGeometricRepresentation h z) + b h z)
    (hhol : ∀ g, ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (b g)) : MuTorsor.AffineCocycle where
  scale _ _ := 1
  shift := b
  scale_one _ := rfl
  shift_one := hone
  scale_mul _ _ _ := by simp
  shift_mul g h z := by
    simpa only [Units.val_one, one_mul, add_comm] using hmul g h z
  scale_holomorphic _ := contMDiff_const
  shift_holomorphic := hhol

variable (φ₁ φ₂ : ℍ → ℂ)
    (h₁ : ∀ z, ∑ k ∈ Finset.range 3, φ₁ ((Triangle.generatorOnePerm ^ k) z) = 0)
    (h₂ : ∀ z, ∑ k ∈ Finset.range 4, φ₂ ((Triangle.generatorTwoPerm ^ k) z) = 0)
    (hφ₁ : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω φ₁)
    (hφ₂ : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω φ₂)

include hφ₁ hφ₂

/-- Every shift in the constructed triangle cocycle is holomorphic, as a
consequence of the two generator functions being holomorphic. -/
theorem triangleAdditiveShift_holomorphic (g : TriangleGroup) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (triangleAdditiveShift φ₁ φ₂ h₁ h₂ g) := by
  refine additive_cocycle_holomorphic (triangleAdditiveShift φ₁ φ₂ h₁ h₂)
    (triangleAdditiveShift_one φ₁ φ₂ h₁ h₂)
    (triangleAdditiveShift_mul φ₁ φ₂ h₁ h₂)
    (triangleAdditiveShift_inv φ₁ φ₂ h₁ h₂) ?_ ?_ g
  · have he : triangleAdditiveShift φ₁ φ₂ h₁ h₂ triangleGenerator₁ = φ₁ :=
      funext (triangleAdditiveShift_generator₁ φ₁ φ₂ h₁ h₂)
    rw [he]
    exact hφ₁
  · have he : triangleAdditiveShift φ₁ φ₂ h₁ h₂ triangleGenerator₂ = φ₂ :=
      funext (triangleAdditiveShift_generator₂ φ₁ φ₂ h₁ h₂)
    rw [he]
    exact hφ₂

/-- The actual additive beta cocycle as the existing affine-cocycle type.
Its scale is one; its shift is the coefficient constructed from the
skew-permutation representation of the genuine triangle group. -/
def triangleAdditiveCocycle : MuTorsor.AffineCocycle :=
  additiveAffineCocycle (triangleAdditiveShift φ₁ φ₂ h₁ h₂)
    (triangleAdditiveShift_one φ₁ φ₂ h₁ h₂)
    (triangleAdditiveShift_mul φ₁ φ₂ h₁ h₂)
    (triangleAdditiveShift_holomorphic φ₁ φ₂ h₁ h₂ hφ₁ hφ₂)

@[simp] theorem triangleAdditiveCocycle_scale (g : TriangleGroup) (z : ℍ) :
    (triangleAdditiveCocycle φ₁ φ₂ h₁ h₂ hφ₁ hφ₂).scale g z = 1 := rfl

@[simp] theorem triangleAdditiveCocycle_shift (g : TriangleGroup) (z : ℍ) :
    (triangleAdditiveCocycle φ₁ φ₂ h₁ h₂ hφ₁ hφ₂).shift g z =
      triangleAdditiveShift φ₁ φ₂ h₁ h₂ g z := rfl

theorem triangleAdditiveCocycle_fibreMap (g : TriangleGroup) (z : ℍ) (u : ℂ) :
    (triangleAdditiveCocycle φ₁ φ₂ h₁ h₂ hφ₁ hφ₂).fibreMap g z u =
      u + triangleAdditiveShift φ₁ φ₂ h₁ h₂ g z := by
  simp only [MuTorsor.AffineCocycle.fibreMap, triangleAdditiveCocycle_scale,
    Units.val_one, one_mul, triangleAdditiveCocycle_shift]

@[simp] theorem triangleAdditiveCocycle_generator₁ (z : ℍ) (u : ℂ) :
    (triangleAdditiveCocycle φ₁ φ₂ h₁ h₂ hφ₁ hφ₂).fibreMap triangleGenerator₁ z u =
      u + φ₁ z := by
  rw [triangleAdditiveCocycle_fibreMap, triangleAdditiveShift_generator₁]

@[simp] theorem triangleAdditiveCocycle_generator₂ (z : ℍ) (u : ℂ) :
    (triangleAdditiveCocycle φ₁ φ₂ h₁ h₂ hφ₁ hφ₂).fibreMap triangleGenerator₂ z u =
      u + φ₂ z := by
  rw [triangleAdditiveCocycle_fibreMap, triangleAdditiveShift_generator₂]

end Wikipedia.HopfProblem.SpecialPeriods.BetaTorsor
