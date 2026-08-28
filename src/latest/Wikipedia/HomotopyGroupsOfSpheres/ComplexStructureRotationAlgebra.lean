import Mathlib.Algebra.Star.Basic
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Module

/-! # Algebra of a pair of anticommuting complex structures -/

namespace Wikipedia.HomotopyGroupsOfSpheres.ComplexStructureRotationAlgebra

variable {A : Type*} [Ring A]

theorem reverse_anticommute (J K : A) (h : J * K = -(K * J)) :
    K * J = -(J * K) := by rw [h, neg_neg]

theorem product_square (J K : A) (hJ : J * J = -1) (hK : K * K = -1)
    (h : J * K = -(K * J)) : (J * K) * (J * K) = -1 := by
  calc
    (J * K) * (J * K) = J * (K * J) * K := by simp only [mul_assoc]
    _ = J * (-(J * K)) * K := by rw [reverse_anticommute J K h]
    _ = -((J * J) * (K * K)) := by noncomm_ring
    _ = -1 := by rw [hJ, hK]; simp

theorem product_mul_left (J K : A) (hJ : J * J = -1)
    (h : J * K = -(K * J)) : (J * K) * J = K := by
  calc
    (J * K) * J = J * (K * J) := mul_assoc _ _ _
    _ = J * (-(J * K)) := by rw [reverse_anticommute J K h]
    _ = -(J * J) * K := by noncomm_ring
    _ = K := by rw [hJ]; simp

theorem left_mul_product (J K : A) (hJ : J * J = -1) : J * (J * K) = -K := by
  rw [← mul_assoc, hJ, neg_one_mul]

theorem right_mul_product (J K : A) (hK : K * K = -1)
    (h : J * K = -(K * J)) : K * (J * K) = J := by
  calc
    K * (J * K) = (K * J) * K := (mul_assoc _ _ _).symm
    _ = -(J * K) * K := by rw [reverse_anticommute J K h]
    _ = -J * (K * K) := by noncomm_ring
    _ = J := by rw [hK]; simp

theorem product_star [StarRing A] (J K : A) (hJ : star J = -J) (hK : star K = -K)
    (h : J * K = -(K * J)) : star (J * K) = -(J * K) := by
  rw [star_mul, hK, hJ, neg_mul_neg]
  exact reverse_anticommute J K h

theorem conjugation_rotation [Algebra ℝ A] (J K P : A)
    (hPJ : P * J = K) (hJP : J * P = -K) (hKP : K * P = J) (c s : ℝ) :
    (c • (1 : A) + s • P) * J * (c • (1 : A) + (-s) • P) =
      (c ^ 2 - s ^ 2) • J + (2 * s * c) • K := by
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_add, smul_smul,
    one_mul, mul_one, hPJ, hJP, hKP, smul_neg]
  module

end Wikipedia.HomotopyGroupsOfSpheres.ComplexStructureRotationAlgebra
