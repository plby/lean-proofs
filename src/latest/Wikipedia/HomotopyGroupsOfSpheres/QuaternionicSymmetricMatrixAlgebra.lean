import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicComplexPlane
import Mathlib.Topology.Instances.Matrix
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Algebra.Star.Unitary

/-! # Symmetric unitary matrices as quaternionic skew square roots of minus one -/

noncomputable section

open scoped Matrix

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicSymmetricMatrices

open QuaternionicScalars QuaternionicComplexPlane

local notation "ℍ" => Quaternion ℝ

variable {N : Type*} [Fintype N] [DecidableEq N]

def complexInclusion : Matrix N N ℂ →ₐ[ℝ] Matrix N N ℍ := Quaternion.ofComplex.mapMatrix

def conjugate : Matrix N N ℂ →+* Matrix N N ℂ := (starRingEnd ℂ).mapMatrix

def quaternionMatrix (B : Matrix N N ℂ) : Matrix N N ℍ := B.map embed

def complexMatrix (A : Matrix N N ℍ) : Matrix N N ℂ := A.map coordinate

theorem complexInclusion_injective :
    Function.Injective (complexInclusion : Matrix N N ℂ → Matrix N N ℍ) := by
  intro B C h
  apply Matrix.ext
  intro r s
  exact coeComplex_injective (congrArg (fun A ↦ A r s) h)

omit [Fintype N] [DecidableEq N] in
@[simp] theorem complexMatrix_quaternionMatrix (B : Matrix N N ℂ) :
    complexMatrix (quaternionMatrix B) = B := by
  apply Matrix.ext
  intro r s
  exact coordinate_embed (B r s)

omit [Fintype N] [DecidableEq N] in
theorem quaternionMatrix_injective :
    Function.Injective (quaternionMatrix : Matrix N N ℂ → Matrix N N ℍ) :=
  Function.LeftInverse.injective complexMatrix_quaternionMatrix

omit [Fintype N] [DecidableEq N] in
theorem quaternionMatrix_star (B : Matrix N N ℂ) :
    star (quaternionMatrix B) = -(quaternionMatrix B.transpose) := by
  apply Matrix.ext
  intro r s
  exact embed_star (B s r)

omit [Fintype N] [DecidableEq N] in
theorem quaternionMatrix_skew_iff (B : Matrix N N ℂ) :
    star (quaternionMatrix B) = -(quaternionMatrix B) ↔ B.transpose = B := by
  rw [quaternionMatrix_star, neg_inj, quaternionMatrix_injective.eq_iff]

theorem quaternionMatrix_mul (B C : Matrix N N ℂ) :
    quaternionMatrix B * quaternionMatrix C = -(complexInclusion (B * conjugate C)) := by
  apply Matrix.ext
  intro r s
  change (∑ k, embed (B r k) * embed (C k s)) =
    -((∑ k, B r k * star (C k s) : ℂ) : ℍ)
  simp only [embed_mul_embed, Finset.sum_neg_distrib]
  congr 1
  exact (map_sum Quaternion.ofComplex _ _).symm

theorem conjugate_eq_star_of_symmetric (B : Matrix N N ℂ) (hB : B.transpose = B) :
    conjugate B = star B := by
  apply Matrix.ext
  intro r s
  change star (B r s) = star (B s r)
  exact congrArg star (congrArg (fun A ↦ A r s) hB).symm

theorem quaternionMatrix_square_iff (B : Matrix N N ℂ) (hB : B.transpose = B) :
    quaternionMatrix B * quaternionMatrix B = -1 ↔ B ∈ unitary (Matrix N N ℂ) := by
  rw [quaternionMatrix_mul, conjugate_eq_star_of_symmetric B hB, neg_inj]
  have he : complexInclusion (B * star B) = (1 : Matrix N N ℍ) ↔ B * star B = 1 := by
    rw [← map_one complexInclusion, complexInclusion_injective.eq_iff]
  rw [he, Unitary.mem_iff]
  exact ⟨fun h ↦ ⟨mul_eq_one_comm.mp h, h⟩, fun h ↦ h.2⟩

theorem quaternionMatrix_anticommutes (B : Matrix N N ℂ) :
    Matrix.diagonal (fun _ : N ↦ i) * quaternionMatrix B =
      -(quaternionMatrix B * Matrix.diagonal (fun _ : N ↦ i)) := by
  apply Matrix.ext
  intro r s
  simp only [Matrix.diagonal_mul, Matrix.neg_apply, Matrix.mul_diagonal]
  exact embed_anticommutes (B r s)

theorem quaternionMatrix_complexMatrix (A : Matrix N N ℍ)
    (hA : Matrix.diagonal (fun _ : N ↦ i) * A =
      -(A * Matrix.diagonal (fun _ : N ↦ i))) :
    quaternionMatrix (complexMatrix A) = A := by
  apply Matrix.ext
  intro r s
  apply embed_coordinate
  have h := congrArg (fun B ↦ B r s) hA
  simpa only [Matrix.diagonal_mul, Matrix.neg_apply, Matrix.mul_diagonal] using h

omit [Fintype N] [DecidableEq N] in
theorem continuous_quaternionMatrix :
    Continuous (quaternionMatrix : Matrix N N ℂ → Matrix N N ℍ) := by
  apply continuous_matrix
  intro r s
  exact continuous_embed.comp ((continuous_apply s).comp (continuous_apply r))

omit [Fintype N] [DecidableEq N] in
theorem continuous_complexMatrix :
    Continuous (complexMatrix : Matrix N N ℍ → Matrix N N ℂ) := by
  apply continuous_matrix
  intro r s
  exact continuous_coordinate.comp ((continuous_apply s).comp (continuous_apply r))

/-- Symmetric matrices inside the actual complex unitary group. -/
abbrev Space (N : Type*) [Fintype N] [DecidableEq N] :=
  {B : unitary (Matrix N N ℂ) // B.val.transpose = B.val}

def identity : Space N := ⟨1, Matrix.transpose_one⟩

omit [Fintype N] in
theorem quaternionMatrix_identity :
    quaternionMatrix (1 : Matrix N N ℂ) = Matrix.diagonal (fun _ : N ↦ j) := by
  apply Matrix.ext
  intro r s
  by_cases h : r = s
  · subst s
    simp [quaternionMatrix, Matrix.map_apply, embed]
  · simp [quaternionMatrix, Matrix.map_apply, h, embed]

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicSymmetricMatrices
