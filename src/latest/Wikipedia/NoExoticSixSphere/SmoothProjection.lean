import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

/-!
# Smooth orthogonal projection from a local tangent frame

For an injective linear map `A`, orthogonal projection onto its range is
`A (A* A)⁻¹ A*`. This formula proves smooth dependence on an injective local
frame without choosing an orthonormal basis at every point.

These results are used to construct the smoothly varying normal spaces of an
embedded manifold. They do not supply a global frame for those spaces.
-/

open scoped Manifold ContDiff
open Function

namespace NoExoticSixSphere

section LinearAlgebra

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- Adjoint, viewed as a real continuous linear map on operator spaces. -/
noncomputable def realAdjoint : (E →L[ℝ] F) →L[ℝ] (F →L[ℝ] E) where
  toFun A := A.adjoint
  map_add' A B := map_add ContinuousLinearMap.adjoint A B
  map_smul' r A := by simp
  cont := ContinuousLinearMap.adjoint.continuous

/-- The Gram operator of a linear frame. -/
noncomputable def gramOperator (A : E →L[ℝ] F) : E →L[ℝ] E :=
  A.adjoint.comp A

/-- An injective frame has an invertible Gram operator. -/
theorem gramOperator_isInvertible (A : E →L[ℝ] F) (hA : Injective A) :
    (gramOperator A).IsInvertible := by
  have hG : Injective (gramOperator A) := A.adjoint_comp_self_injective_iff.mpr hA
  let g := (LinearEquiv.ofInjectiveEndo (gramOperator A).toLinearMap hG).toContinuousLinearEquiv
  exact ⟨g, by ext v; rfl⟩

/-- The projection formula, defined everywhere using the total operator inverse. -/
noncomputable def gramProjection (A : E →L[ℝ] F) : F →L[ℝ] F :=
  A.comp ((gramOperator A).inverse.comp A.adjoint)

/-- The Gram formula is the actual orthogonal projection onto the frame's range. -/
theorem gramProjection_eq_starProjection (A : E →L[ℝ] F) (hA : Injective A) :
    gramProjection A = A.range.starProjection := by
  ext v
  symm
  apply Submodule.eq_starProjection_of_mem_orthogonal
  · exact ⟨(gramOperator A).inverse (A.adjoint v), rfl⟩
  · rw [A.orthogonal_range]
    change A.adjoint (v - A ((gramOperator A).inverse (A.adjoint v))) = 0
    rw [map_sub]
    change A.adjoint v - gramOperator A ((gramOperator A).inverse (A.adjoint v)) = 0
    rw [(gramOperator_isInvertible A hA).self_apply_inverse, sub_self]

end LinearAlgebra

section Smoothness

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  {B H M : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
  [TopologicalSpace H] {I : ModelWithCorners ℝ B H}
  [TopologicalSpace M] [ChartedSpace H M]

/-- A smooth family of frames gives a smooth family of projections near every
point where the frame is injective. -/
theorem contMDiffAt_gramProjection {A : M → E →L[ℝ] F} {x : M}
    (hA : ContMDiffAt I 𝓘(ℝ, E →L[ℝ] F) ∞ A x) (hinj : Injective (A x)) :
    ContMDiffAt I 𝓘(ℝ, F →L[ℝ] F) ∞ (fun y ↦ gramProjection (A y)) x := by
  have hadj : ContMDiffAt I 𝓘(ℝ, F →L[ℝ] E) ∞ (fun y ↦ (A y).adjoint) x :=
    (realAdjoint.contDiff.contMDiff.contMDiffAt).comp x hA
  have hgram : ContMDiffAt I 𝓘(ℝ, E →L[ℝ] E) ∞ (fun y ↦ gramOperator (A y)) x :=
    hadj.clm_comp hA
  have hinverse : ContMDiffAt I 𝓘(ℝ, E →L[ℝ] E) ∞
      (fun y ↦ (gramOperator (A y)).inverse) x :=
    ContDiffAt.comp_contMDiffAt (f := fun y ↦ gramOperator (A y)) (x := x)
      (gramOperator_isInvertible (A x) hinj).contDiffAt_map_inverse hgram
  exact hA.clm_comp (hinverse.clm_comp hadj)

end Smoothness

end NoExoticSixSphere
