import Wikipedia.HomotopyGroupsOfSpheres.BalancedFrameProjection
import Mathlib.Analysis.InnerProductSpace.Subspace

/-! # Actual Stiefel frames from selected standard coordinate vectors -/

noncomputable section

namespace Wikipedia.HomotopyGroupsOfSpheres.CoordinateFrames

open NoExoticSixSphere NoExoticSixSphere.GLOrthonormalization
open Module Submodule

variable {n r : ℕ}

def columns (f : Fin r ↪ Fin n) (j : Fin r) : Vector n := EuclideanSpace.basisFun (Fin n) ℝ (f j)

theorem columns_orthonormal (f : Fin r ↪ Fin n) : Orthonormal ℝ (columns f) :=
  (EuclideanSpace.basisFun (Fin n) ℝ).orthonormal.comp f f.injective

def spanBasis (f : Fin r ↪ Fin n) :
    OrthonormalBasis (Fin r) ℝ (Submodule.span ℝ (Set.range (columns f))) :=
  (Basis.span (columns_orthonormal f).linearIndependent).toOrthonormalBasis (by
    apply orthonormal_iff_ite.mpr
    intro i j
    change inner ℝ
      ((Basis.span (columns_orthonormal f).linearIndependent i) : Vector n)
      ((Basis.span (columns_orthonormal f).linearIndependent j) : Vector n) = _
    rw [Basis.coe_span_apply, Basis.coe_span_apply]
    exact (orthonormal_iff_ite.mp (columns_orthonormal f)) i j)

theorem spanBasis_apply (f : Fin r ↪ Fin n) (j : Fin r) :
    (spanBasis f j : Vector n) = columns f j := by
  simp [spanBasis]

def isometry (f : Fin r ↪ Fin n) : Vector r →ₗᵢ[ℝ] Vector n :=
  (Submodule.span ℝ (Set.range (columns f))).subtypeₗᵢ.comp (spanBasis f).repr.symm.toLinearIsometry

def frame (f : Fin r ↪ Fin n) : Stiefel.Space n r := Stiefel.ofIsometry (isometry f)

theorem frame_basis (f : Fin r ↪ Fin n) (j : Fin r) :
    (frame f).val (EuclideanSpace.basisFun (Fin r) ℝ j) = columns f j := by
  change ((spanBasis f).repr.symm (EuclideanSpace.basisFun (Fin r) ℝ j) : Vector n) = columns f j
  rw [EuclideanSpace.basisFun_apply, OrthonormalBasis.repr_symm_single, spanBasis_apply]

theorem frame_adjoint_apply (f : Fin r ↪ Fin n) (x : Vector n) (j : Fin r) :
    ((frame f).val.adjoint x) j = x (f j) := by
  have h := (frame f).val.adjoint_inner_right (EuclideanSpace.basisFun (Fin r) ℝ j) x
  rw [EuclideanSpace.basisFun_inner, frame_basis] at h
  simpa only [columns, EuclideanSpace.basisFun_inner] using h

theorem frame_apply (f : Fin r ↪ Fin n) (x : Vector r) :
    (frame f).val x = ∑ j, x j • columns f j := by
  have hx : x = ∑ j, x j • EuclideanSpace.basisFun (Fin r) ℝ j :=
    ((EuclideanSpace.basisFun (Fin r) ℝ).sum_repr x).symm
  calc
    (frame f).val x = (frame f).val (∑ j, x j • EuclideanSpace.basisFun (Fin r) ℝ j) :=
      congrArg (frame f).val hx
    _ = ∑ j, x j • columns f j := by simp only [map_sum, map_smul, frame_basis]

theorem frame_apply_coordinate (f : Fin r ↪ Fin n) (x : Vector r) (i : Fin n) :
    (frame f).val x i = ∑ j, if i = f j then x j else 0 := by
  rw [frame_apply]
  simp [columns, EuclideanSpace.basisFun_apply, Pi.single_apply]

theorem frame_projector_apply (f : Fin r ↪ Fin n) (x : Vector n) (i : Fin n) :
    ((frame f).val.comp (frame f).val.adjoint) x i = ∑ j, if i = f j then x (f j) else 0 := by
  change (frame f).val ((frame f).val.adjoint x) i = _
  rw [frame_apply_coordinate]
  simp only [frame_adjoint_apply]

end Wikipedia.HomotopyGroupsOfSpheres.CoordinateFrames
