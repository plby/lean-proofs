import ErdosProblems.Erdos1148.LatticeVectorAction
import ErdosProblems.Erdos1148.FrameBoxCloseness

/-! # Euclidean lattice-vector lengths in upper triangular and angular coordinates -/

namespace Erdos1148.DukeArithmetic

open scoped MatrixGroups
open Matrix

def vectorLengthSq (v : Fin 2 → ℝ) : ℝ := v 0 ^ 2 + v 1 ^ 2

lemma frameRealVector_comp (g h : SL(2, ℝ)) (v : Fin 2 → ℝ) :
    frameRealVector (g * h) v = frameRealVector h (frameRealVector g v) := by
  apply (g * h).toLin'.injective
  simp only [frameRealVector, LinearEquiv.apply_symm_apply, map_mul, LinearEquiv.mul_apply]

lemma modularVectorLengthSq_eq (g : SL(2, ℝ)) (u v : ℤ) :
    modularVectorLengthSq g u v = vectorLengthSq (frameRealVector g ![(u : ℝ), (v : ℝ)]) := by
  have h := frameRealVector_pair g u v
  change (modularVector g u v).1 ^ 2 + (modularVector g u v).2 ^ 2 = _
  rw [← h]
  rfl

lemma vectorLengthSq_rotationFrame (θ : ℝ) (v : Fin 2 → ℝ) :
    vectorLengthSq (frameRealVector (rotationFrame θ) v) = vectorLengthSq v := by
  have hvec : frameRealVector (rotationFrame θ) v =
      ![Real.cos θ * v 0 + Real.sin θ * v 1, -Real.sin θ * v 0 + Real.cos θ * v 1] := by
    rw [frameRealVector, Matrix.SpecialLinearGroup.toLin'_symm_apply]
    change (((rotationFrame θ)⁻¹ : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) *ᵥ v = _
    rw [Matrix.SpecialLinearGroup.coe_inv]
    ext i
    fin_cases i <;>
      simp [Matrix.mulVec, Fin.sum_univ_two, rotationFrame, Matrix.adjugate_fin_two,
        Matrix.vecHead, Matrix.vecTail]
  rw [hvec]
  dsimp only [vectorLengthSq]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  linear_combination (v 0 ^ 2 + v 1 ^ 2) * Real.sin_sq_add_cos_sq θ

theorem modularVectorLengthSq_cuspFrame (x h θ : ℝ) (hh : h ≠ 0) (u v : ℤ) :
    modularVectorLengthSq (cuspFrame x h θ hh) u v =
      ((u : ℝ) - x * v) ^ 2 / h ^ 2 + h ^ 2 * (v : ℝ) ^ 2 := by
  rw [modularVectorLengthSq_eq, cuspFrame, frameRealVector_comp, vectorLengthSq_rotationFrame]
  have hvec : frameRealVector (upperTriangularFrame x h hh) ![(u : ℝ), (v : ℝ)] =
      ![(u : ℝ) / h - x / h * v, h * (v : ℝ)] := by
    rw [frameRealVector, Matrix.SpecialLinearGroup.toLin'_symm_apply]
    change (((upperTriangularFrame x h hh)⁻¹ : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) *ᵥ
      ![(u : ℝ), (v : ℝ)] = _
    rw [Matrix.SpecialLinearGroup.coe_inv]
    ext i
    fin_cases i <;>
      simp [Matrix.mulVec, upperTriangularFrame, Matrix.adjugate_fin_two, Matrix.vecHead,
        Matrix.vecTail, div_eq_mul_inv] <;> ring
  rw [hvec]
  dsimp only [vectorLengthSq]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  field_simp

end Erdos1148.DukeArithmetic
