import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicMixingMatrices
import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicSpectralTheorem

/-! # Transporting quaternionic mixing directions through the actual unitary eigenframe -/

noncomputable section

open scoped Matrix

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns

open NoExoticSixSphere.GLOrthonormalization NoExoticSixSphere.HilbertSchmidt
open NoExoticSixSphere.OrthogonalCommutator

local notation "ℍ" => Quaternion ℝ

section MatrixAlgebra

variable {N : Type*} [Fintype N] [DecidableEq N]

theorem conjugateMatrix_one (A : Matrix N N ℍ) : conjugateMatrix 1 A = A := by
  simp [conjugateMatrix]

theorem conjugateMatrix_inv_cancel (U : SpGroup N) (A : Matrix N N ℍ) :
    conjugateMatrix U⁻¹ (conjugateMatrix U A) = A := by
  rw [← conjugateMatrix_mul, mul_inv_cancel, conjugateMatrix_one]

theorem conjugateMatrix_injective (U : SpGroup N) : Function.Injective (conjugateMatrix U) := by
  intro A B h
  have he := congrArg (conjugateMatrix U⁻¹) h
  simpa only [conjugateMatrix_inv_cancel] using he

theorem conjugateMatrix_add (U : SpGroup N) (A B : Matrix N N ℍ) :
    conjugateMatrix U (A + B) = conjugateMatrix U A + conjugateMatrix U B := by
  simp only [conjugateMatrix, mul_add, add_mul]

theorem conjugateMatrix_smul (U : SpGroup N) (r : ℝ) (A : Matrix N N ℍ) :
    conjugateMatrix U (r • A) = r • conjugateMatrix U A := by
  simp only [conjugateMatrix, mul_smul_comm, smul_mul_assoc]

theorem conjugateMatrix_product (U : SpGroup N) (A B : Matrix N N ℍ) :
    conjugateMatrix U (A * B) = conjugateMatrix U A * conjugateMatrix U B := by
  simp only [conjugateMatrix, mul_assoc]
  rw [← mul_assoc U.val (star U.val), Unitary.mul_star_self_of_mem U.property, one_mul]

theorem conjugateMatrix_commutator (U : SpGroup N) (A B : Matrix N N ℍ) :
    conjugateMatrix U (A * B - B * A) =
      conjugateMatrix U A * conjugateMatrix U B - conjugateMatrix U B * conjugateMatrix U A := by
  have hsub : conjugateMatrix U (A * B - B * A) =
      conjugateMatrix U (A * B) - conjugateMatrix U (B * A) := by
    simp only [conjugateMatrix, mul_sub, sub_mul]
  rw [hsub, conjugateMatrix_product, conjugateMatrix_product]

end MatrixAlgebra

variable {n : ℕ}

theorem squareNorm_realAction_conjugateMatrix (U : SpGroup (Fin (n + 1)))
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℍ) :
    squareNorm (realAction n (conjugateMatrix U A)) = squareNorm (realAction n A) := by
  rw [conjugateMatrix, realAction_mul, realAction_mul]
  exact (squareNorm_right (orthogonalRepresentation n U) _).trans
    (squareNorm_left (orthogonalRepresentation n U⁻¹) _)

theorem squareNorm_commutator_conjugateMatrix (U : SpGroup (Fin (n + 1)))
    (A B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℍ) :
    squareNorm (commutator (realAction n (conjugateMatrix U A))
      (realAction n (conjugateMatrix U B))) =
        squareNorm (commutator (realAction n A) (realAction n B)) := by
  rw [realAction_commutator, realAction_commutator, ← conjugateMatrix_commutator,
    squareNorm_realAction_conjugateMatrix]

/-- The diagonal mixing family transported back by a chosen unitary eigenframe. -/
def transportedMixingLinear (U : SpGroup (Fin (n + 1))) : (Fin n → ℝ) →ₗ[ℝ] SkewSpace n where
  toFun c := skewOfMatrix n (conjugateMatrix U⁻¹ (mixingMatrix QuaternionicScalars.j c))
    (conjugateMatrix_skew U⁻¹ _ (mixingMatrix_skew _ QuaternionicScalars.star_j c))
  map_add' c d := by
    apply Subtype.ext
    change realAction n (conjugateMatrix U⁻¹ (mixingMatrix _ (c + d))) = _
    rw [mixingMatrix_add, conjugateMatrix_add, realAction_add]
    rfl
  map_smul' r c := by
    apply Subtype.ext
    change realAction n (conjugateMatrix U⁻¹ (mixingMatrix _ (r • c))) = _
    rw [mixingMatrix_smul, conjugateMatrix_smul, realAction_smul]
    rfl

theorem transportedMixingLinear_injective (U : SpGroup (Fin (n + 1))) :
    Function.Injective (transportedMixingLinear U) := by
  intro c d h
  apply mixingMatrix_injective QuaternionicScalars.j QuaternionicScalars.j_ne_zero
  apply conjugateMatrix_injective U⁻¹
  exact realAction_injective n (congrArg Subtype.val h)

theorem squareNorm_transportedMixing (U : SpGroup (Fin (n + 1))) (c : Fin n → ℝ) :
    squareNorm (transportedMixingLinear U c).val = squareNorm (mixingSkewLinear n c).val :=
  squareNorm_realAction_conjugateMatrix U⁻¹ _

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns
