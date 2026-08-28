import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicCommutant
import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicScalars

/-! # The quaternionic right scalar relations in real operator coordinates -/

noncomputable section

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns

open NoExoticSixSphere.GLOrthonormalization

local notation "ℍ" => Quaternion ℝ

theorem rightMulLinear_one (n : ℕ) (v : QuaternionSpace n) : rightMulLinear n 1 v = v := by
  apply (WithLp.equiv 2 (Fin (n + 1) → ℍ)).injective
  funext a
  exact mul_one _

theorem rightMulLinear_mul (n : ℕ) (p q : ℍ) (v : QuaternionSpace n) :
    rightMulLinear n (p * q) v = rightMulLinear n q (rightMulLinear n p v) := by
  apply (WithLp.equiv 2 (Fin (n + 1) → ℍ)).injective
  funext a
  exact (mul_assoc _ _ _).symm

theorem rightMulLinear_neg (n : ℕ) (p : ℍ) (v : QuaternionSpace n) :
    rightMulLinear n (-p) v = -(rightMulLinear n p v) := by
  apply (WithLp.equiv 2 (Fin (n + 1) → ℍ)).injective
  funext a
  exact mul_neg _ _

theorem rightAction_one (n : ℕ) : rightAction n 1 = 1 := by
  apply ContinuousLinearMap.ext
  intro v
  rw [rightAction_apply, rightMulLinear_one, (quaternionCoordinates n).apply_symm_apply]
  rfl

theorem rightAction_mul (n : ℕ) (p q : ℍ) :
    rightAction n (p * q) = (rightAction n q).comp (rightAction n p) := by
  apply ContinuousLinearMap.ext
  intro v
  simp only [ContinuousLinearMap.comp_apply, rightAction_apply,
    (quaternionCoordinates n).symm_apply_apply, rightMulLinear_mul]

theorem rightAction_neg (n : ℕ) (p : ℍ) : rightAction n (-p) = -(rightAction n p) := by
  apply ContinuousLinearMap.ext
  intro v
  simp only [rightAction_apply, rightMulLinear_neg, map_neg, neg_apply]

theorem rightAction_i_square (n : ℕ) :
    (rightAction n QuaternionicScalars.i).comp (rightAction n QuaternionicScalars.i) =
      -(1 : Vector (4 * n + 4) →L[ℝ] Vector (4 * n + 4)) := by
  rw [← rightAction_mul, QuaternionicScalars.i_mul_i, rightAction_neg, rightAction_one]

theorem rightAction_j_square (n : ℕ) :
    (rightAction n QuaternionicScalars.j).comp (rightAction n QuaternionicScalars.j) =
      -(1 : Vector (4 * n + 4) →L[ℝ] Vector (4 * n + 4)) := by
  rw [← rightAction_mul, QuaternionicScalars.j_mul_j, rightAction_neg, rightAction_one]

theorem rightAction_i_j_anticommute (n : ℕ) :
    (rightAction n QuaternionicScalars.i).comp (rightAction n QuaternionicScalars.j) =
      -((rightAction n QuaternionicScalars.j).comp (rightAction n QuaternionicScalars.i)) := by
  rw [← rightAction_mul, ← rightAction_mul, QuaternionicScalars.j_mul_i,
    QuaternionicScalars.i_mul_j, rightAction_neg]

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns
