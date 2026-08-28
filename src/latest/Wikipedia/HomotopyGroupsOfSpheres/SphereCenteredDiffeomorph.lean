import Wikipedia.HomotopyGroupsOfSpheres.SphereCoordinateIsometries
import Mathlib.Geometry.Manifold.LocalDiffeomorph

/-! # The centered sphere coordinates are native smooth partial diffeomorphisms -/

noncomputable section

open Set
open scoped Manifold ContDiff

namespace Wikipedia.HomotopyGroupsOfSpheres.SphereCenteredCoordinates

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

variable (n : ℕ) [Fact (Module.finrank ℝ E = n + 1)]

theorem contMDiff_inverse (z : UnitSphere E) :
    ContMDiff 𝓘(ℝ, Tangent z) (𝓡 n) ∞ (inverse z) :=
  (contDiff_inverse_val z).contMDiff.codRestrict_sphere (fun w ↦ (inverse z w).property)

theorem contMDiffOn_chart (z : UnitSphere E) :
    ContMDiffOn (𝓡 n) 𝓘(ℝ, Tangent z) ∞ (chart z) (chart z).source := by
  apply contDiffOn_stereoToFun.contMDiffOn.comp contMDiff_coe_sphere.contMDiffOn
  intro w hw
  change innerSL ℝ (-z.val) w.val ≠ 1
  exact hw ∘ Subtype.ext ∘ Eq.symm ∘
    (inner_eq_one_iff_of_norm_eq_one (by simp : ‖-z.val‖ = 1) (by simp)).mp

def inverseDiffeomorph (z : UnitSphere E) :
    PartialDiffeomorph 𝓘(ℝ, Tangent z) (𝓡 n) (Tangent z) (UnitSphere E) ∞ where
  __ := (chart z).symm
  contMDiffOn_toFun := (contMDiff_inverse n z).contMDiffOn
  contMDiffOn_invFun := contMDiffOn_chart n z

@[simp] theorem inverseDiffeomorph_apply (z : UnitSphere E) (v : Tangent z) :
    inverseDiffeomorph n z v = inverse z v := rfl

@[simp] theorem inverseDiffeomorph_source (z : UnitSphere E) :
    (inverseDiffeomorph n z).source = univ := rfl

variable [Fact (Module.finrank ℝ F = n + 1)]

theorem contMDiff_sphereIsometry (e : E ≃ₗᵢ[ℝ] F) :
    ContMDiff (𝓡 n) (𝓡 n) ∞ (sphereIsometry e) :=
  (e.contDiff.contMDiff.comp contMDiff_coe_sphere).codRestrict_sphere
    (fun z ↦ (sphereIsometry e z).property)

def sphereIsometryDiffeomorph (e : E ≃ₗᵢ[ℝ] F) :
    Diffeomorph (𝓡 n) (𝓡 n) (UnitSphere E) (UnitSphere F) ∞ where
  __ := sphereIsometry e
  contMDiff_toFun := contMDiff_sphereIsometry n e
  contMDiff_invFun := contMDiff_sphereIsometry n e.symm

@[simp] theorem sphereIsometryDiffeomorph_apply (e : E ≃ₗᵢ[ℝ] F) (z : UnitSphere E) :
    sphereIsometryDiffeomorph n e z = sphereIsometry e z := rfl

end Wikipedia.HomotopyGroupsOfSpheres.SphereCenteredCoordinates
