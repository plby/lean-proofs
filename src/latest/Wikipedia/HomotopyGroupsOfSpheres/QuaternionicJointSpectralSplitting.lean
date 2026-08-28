import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicJointEigenframe
import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicConjugation

/-! # Joint quaternionic spectral splitting preserves the complex-structure relations -/

noncomputable section

open scoped Matrix

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns

open ComplexStructures

local notation "ℍ" => Quaternion ℝ

section MatrixAlgebra

variable {N : Type*} [Fintype N] [DecidableEq N]

theorem conjugateMatrix_neg (U : SpGroup N) (A : Matrix N N ℍ) :
    conjugateMatrix U (-A) = -(conjugateMatrix U A) := by
  simp only [conjugateMatrix, mul_neg, neg_mul]

theorem conjugateMatrix_identity (U : SpGroup N) : conjugateMatrix U (1 : Matrix N N ℍ) = 1 := by
  rw [conjugateMatrix, mul_one, Unitary.star_mul_self_of_mem U.property]

theorem conjugateMatrix_square_neg_one (U : SpGroup N) (J : Matrix N N ℍ)
    (hJ : J * J = -1) : conjugateMatrix U J * conjugateMatrix U J = -1 := by
  rw [← conjugateMatrix_product, hJ, conjugateMatrix_neg, conjugateMatrix_identity]

theorem conjugateMatrix_anticommute (U : SpGroup N) (J A : Matrix N N ℍ)
    (hJA : J * A = -(A * J)) :
    conjugateMatrix U J * conjugateMatrix U A =
      -(conjugateMatrix U A * conjugateMatrix U J) := by
  rw [← conjugateMatrix_product, hJA, conjugateMatrix_neg, conjugateMatrix_product]

end MatrixAlgebra

variable {n : ℕ}

theorem lowerBlock_splitMatrix (q : ℍ) (A : Matrix (Fin n) (Fin n) ℍ) :
    lowerBlock (splitMatrix q A) = A := rfl

theorem lowerBlock_neg (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℍ) :
    lowerBlock (-A) = -(lowerBlock A) := rfl

theorem lowerBlock_identity (n : ℕ) :
    lowerBlock (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℍ) = 1 := by
  apply Matrix.ext
  intro i j
  simp only [lowerBlock, Matrix.one_apply, Fin.succ_inj]

theorem joint_lowerBlock_relations (U : SpGroup (Fin (n + 1)))
    (A J : Matrix (Fin (n + 1)) (Fin (n + 1)) ℍ)
    (hJ : J * J = -1) (hJA : J * A = -(A * J)) (α : ℝ)
    (hA : conjugateMatrix U A = splitMatrix (α • QuaternionicScalars.i)
      (lowerBlock (conjugateMatrix U A)))
    (hJs : conjugateMatrix U J = splitMatrix QuaternionicScalars.j
      (lowerBlock (conjugateMatrix U J))) :
    lowerBlock (conjugateMatrix U J) * lowerBlock (conjugateMatrix U J) = -1 ∧
      lowerBlock (conjugateMatrix U J) * lowerBlock (conjugateMatrix U A) =
        -(lowerBlock (conjugateMatrix U A) * lowerBlock (conjugateMatrix U J)) := by
  constructor
  · have h := congrArg lowerBlock (conjugateMatrix_square_neg_one U J hJ)
    conv_lhs at h => rw [hJs, splitMatrix_mul, lowerBlock_splitMatrix]
    rw [lowerBlock_neg, lowerBlock_identity] at h
    exact h
  · have h := congrArg lowerBlock (conjugateMatrix_anticommute U J A hJA)
    conv_lhs at h => rw [hJs, hA, splitMatrix_mul, lowerBlock_splitMatrix]
    conv_rhs at h => rw [hA, hJs, lowerBlock_neg, splitMatrix_mul, lowerBlock_splitMatrix]
    exact h

def complexStructureOfMatrix (n : ℕ) (J : Matrix (Fin (n + 1)) (Fin (n + 1)) ℍ)
    (hJ : star J = -J) (hs : J * J = -1) : Space n :=
  ⟨skewOfMatrix n J hJ, by
    change realRepresentation n J * realRepresentation n J = -1
    rw [← map_mul, hs, map_neg, map_one]⟩

theorem exists_joint_spectral_split (n : ℕ)
    (A J : Matrix (Fin (n + 1)) (Fin (n + 1)) ℍ)
    (hA : star A = -A) (hJ : star J = -J) (hs : J * J = -1) (hJA : J * A = -(A * J)) :
    ∃ (α : ℝ) (U : SpGroup (Fin (n + 1))) (B C : Matrix (Fin n) (Fin n) ℍ),
      0 ≤ α ∧ star B = -B ∧ star C = -C ∧ C * C = -1 ∧ C * B = -(B * C) ∧
      conjugateMatrix U A = splitMatrix (α • QuaternionicScalars.i) B ∧
      conjugateMatrix U J = splitMatrix QuaternionicScalars.j C := by
  let K := skewOfMatrix n A hA
  let Q := complexStructureOfMatrix n J hJ hs
  have hQK : Q.val.val * K.val = -(K.val * Q.val.val) := by
    change realRepresentation n J * realRepresentation n A =
      -(realRepresentation n A * realRepresentation n J)
    rw [← map_mul, ← map_mul, ← map_neg]
    exact congrArg (realRepresentation n) hJA
  obtain ⟨α, v, hα, hv, hKv, hQv⟩ := exists_nonnegative_joint_unit_eigenvector Q K hQK
  obtain ⟨U, hUK, hUQ⟩ := exists_joint_eigenframe Q K α v hv hKv hQv
  have hKA : coefficients n K.val = A := coefficients_realAction n A
  have hQJ : coefficients n Q.val.val = J := coefficients_realAction n J
  rw [hKA] at hUK
  rw [hQJ] at hUQ
  have hlow := joint_lowerBlock_relations U A J hs hJA α hUK hUQ
  exact ⟨α, U, lowerBlock (conjugateMatrix U A), lowerBlock (conjugateMatrix U J), hα,
    lowerBlock_skew _ (conjugateMatrix_skew U A hA),
    lowerBlock_skew _ (conjugateMatrix_skew U J hJ), hlow.1, hlow.2, hUK, hUQ⟩

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns
