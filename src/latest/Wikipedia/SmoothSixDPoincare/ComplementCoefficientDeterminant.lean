import Wikipedia.SmoothSixDPoincare.ComplementQuotient
import Mathlib.LinearAlgebra.Determinant
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# The actual determinant relation for complementary-frame coefficients

The inverse splitting sends the first frame to the first coordinate factor.
Its transition to a second complement is therefore block upper triangular,
with identity first diagonal block and the quotient coefficient as second
block. The determinant of the full frame factors accordingly.
-/

noncomputable section

open Function Module

namespace Wikipedia.SmoothSixDPoincare.FrameField

variable {D Z F : Type*}
  [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A zero lower-left block makes the genuine determinant the product of its two diagonal blocks. -/
theorem det_of_zero_lower_left (T : (D × Z) →L[ℝ] (D × Z))
    (hT : ∀ u : D, (T (u, 0)).2 = 0) :
    T.toLinearMap.det =
      ((ContinuousLinearMap.fst ℝ D Z).comp
        (T.comp (ContinuousLinearMap.inl ℝ D Z))).toLinearMap.det *
      ((ContinuousLinearMap.snd ℝ D Z).comp
        (T.comp (ContinuousLinearMap.inr ℝ D Z))).toLinearMap.det := by
  classical
  let bD := Module.finBasis ℝ D
  let bZ := Module.finBasis ℝ Z
  let A := (ContinuousLinearMap.fst ℝ D Z).comp (T.comp (ContinuousLinearMap.inl ℝ D Z))
  let B := (ContinuousLinearMap.fst ℝ D Z).comp (T.comp (ContinuousLinearMap.inr ℝ D Z))
  let K := (ContinuousLinearMap.snd ℝ D Z).comp (T.comp (ContinuousLinearMap.inr ℝ D Z))
  have hmat : LinearMap.toMatrix (bD.prod bZ) (bD.prod bZ) T.toLinearMap =
      Matrix.fromBlocks (LinearMap.toMatrix bD bD A.toLinearMap)
        (LinearMap.toMatrix bZ bD B.toLinearMap) 0 (LinearMap.toMatrix bZ bZ K.toLinearMap) := by
    ext (i | i) (j | j) <;> simp [LinearMap.toMatrix_apply, hT, A, B, K]
  rw [← LinearMap.det_toMatrix (bD.prod bZ), hmat, Matrix.det_fromBlocks_zero₂₁,
    LinearMap.det_toMatrix, LinearMap.det_toMatrix]

/-- Fixing the first coordinate factor reduces the determinant to the induced second block. -/
theorem det_of_fixed_first_factor (T : (D × Z) →L[ℝ] (D × Z))
    (hT : ∀ u : D, T (u, 0) = (u, 0)) :
    T.toLinearMap.det =
      ((ContinuousLinearMap.snd ℝ D Z).comp
        (T.comp (ContinuousLinearMap.inr ℝ D Z))).toLinearMap.det := by
  classical
  let bD := Module.finBasis ℝ D
  let bZ := Module.finBasis ℝ Z
  let B := (ContinuousLinearMap.fst ℝ D Z).comp (T.comp (ContinuousLinearMap.inr ℝ D Z))
  let K := (ContinuousLinearMap.snd ℝ D Z).comp (T.comp (ContinuousLinearMap.inr ℝ D Z))
  have hmat : LinearMap.toMatrix (bD.prod bZ) (bD.prod bZ) T.toLinearMap =
      Matrix.fromBlocks 1 (LinearMap.toMatrix bZ bD B.toLinearMap) 0
        (LinearMap.toMatrix bZ bZ K.toLinearMap) := by
    ext (i | i) (j | j) <;>
      simp [LinearMap.toMatrix_apply, hT, B, K, Matrix.one_apply, Finsupp.single_apply, eq_comm]
  rw [← LinearMap.det_toMatrix (bD.prod bZ), hmat, Matrix.det_fromBlocks_zero₂₁,
    Matrix.det_one, one_mul, LinearMap.det_toMatrix]

/-- The full frame determinant is the splitting determinant times its true quotient determinant. -/
theorem det_frame_eq_det_split_mul_det_coefficient
    (j : (D × Z) ≃L[ℝ] F) (G : D →L[ℝ] F) (C L : Z →L[ℝ] F)
    (h : (G.coprod C).IsInvertible) :
    (j.symm.toContinuousLinearMap.comp (G.coprod L)).toLinearMap.det =
      (j.symm.toContinuousLinearMap.comp (G.coprod C)).toLinearMap.det *
        ((complementQuotient G C).comp L).toLinearMap.det := by
  let T := G.coprod C
  let R := G.coprod L
  let A := T.inverse.comp R
  have hA : ∀ u : D, A (u, 0) = (u, 0) := by
    intro u
    change T.inverse (G u + L 0) = (u, 0)
    rw [map_zero, add_zero]
    have hi := h.inverse_apply_self (u, 0)
    change T.inverse (G u + C 0) = (u, 0) at hi
    simpa only [map_zero, add_zero] using hi
  have hblock : (ContinuousLinearMap.snd ℝ D Z).comp
      (A.comp (ContinuousLinearMap.inr ℝ D Z)) = (complementQuotient G C).comp L := by
    apply ContinuousLinearMap.ext
    intro v
    change (T.inverse (G 0 + L v)).2 = (T.inverse (L v)).2
    rw [map_zero, zero_add]
  have hdetA : A.toLinearMap.det = ((complementQuotient G C).comp L).toLinearMap.det := by
    rw [det_of_fixed_first_factor A hA, hblock]
  have hfactor : j.symm.toContinuousLinearMap.comp R =
      (j.symm.toContinuousLinearMap.comp T).comp A := by
    apply ContinuousLinearMap.ext
    intro v
    change j.symm (R v) = j.symm (T (T.inverse (R v)))
    rw [h.self_apply_inverse]
  change (j.symm.toContinuousLinearMap.comp R).toLinearMap.det = _
  rw [hfactor]
  have hmul : ((j.symm.toContinuousLinearMap.comp T).comp A).toLinearMap.det =
      (j.symm.toContinuousLinearMap.comp T).toLinearMap.det * A.toLinearMap.det :=
    map_mul LinearMap.det _ _
  rw [hmul, hdetA]

end Wikipedia.SmoothSixDPoincare.FrameField
