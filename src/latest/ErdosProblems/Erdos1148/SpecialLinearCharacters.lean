import ErdosProblems.Erdos1148.HorocycleGeneration
import Mathlib.Algebra.Group.Units.Hom

/-! # Every abelian character of SL(2,R) is trivial -/

namespace Erdos1148.DukeArithmetic

open scoped MatrixGroups

lemma stableHorocycle_add (r s : ℝ) :
    stableHorocycle (r + s) = stableHorocycle r * stableHorocycle s := by
  apply Subtype.ext
  change (stableHorocycle (r + s)).1 = (stableHorocycle r).1 * (stableHorocycle s).1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [stableHorocycle, Matrix.mul_apply, Fin.sum_univ_two, add_comm]

lemma map_conjugate_comm {G C : Type*} [Group G] [CommGroup C] (f : G →* C) (a u : G) :
    f (a⁻¹ * u * a) = f u := by
  rw [map_mul, map_mul, map_inv]
  simp [mul_comm, mul_left_comm, mul_assoc]

theorem specialLinear_commGroupHom_eq_one {C : Type*} [CommGroup C]
    (f : SL(2, ℝ) →* C) (g : SL(2, ℝ)) : f g = 1 := by
  have hs (r : ℝ) : f (stableHorocycle r) = 1 := by
    have h := congrArg f (diagonal_conjugate_stableHorocycle r (-Real.log 2))
    rw [diagonalFlow_neg (-Real.log 2), map_conjugate_comm] at h
    simp only [neg_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2), mul_two,
      stableHorocycle_add, map_mul] at h
    have heq : f (stableHorocycle r) * 1 = f (stableHorocycle r) * f (stableHorocycle r) := by
      simpa only [mul_one] using h
    exact (mul_left_cancel heq).symm
  have hu (r : ℝ) : f (unstableHorocycle r) = 1 := by
    have h := congrArg f (diagonal_conjugate_unstableHorocycle r (Real.log 2))
    rw [diagonalFlow_neg (Real.log 2), map_conjugate_comm] at h
    simp only [Real.exp_log (by norm_num : (0 : ℝ) < 2), mul_two,
      unstableHorocycle_add, map_mul] at h
    have heq : f (unstableHorocycle r) * 1 = f (unstableHorocycle r) * f (unstableHorocycle r) := by
      simpa only [mul_one] using h
    exact (mul_left_cancel heq).symm
  let : MulAction SL(2, ℝ) C := MulAction.compHom C f
  have hs' (r : ℝ) : stableHorocycle r • (1 : C) = 1 := by
    change f (stableHorocycle r) * 1 = 1
    rw [hs, one_mul]
  have hu' (r : ℝ) : unstableHorocycle r • (1 : C) = 1 := by
    change f (unstableHorocycle r) * 1 = 1
    rw [hu, one_mul]
  have h := specialLinear_fixed_of_horocycles hs' hu' g
  change f g * 1 = 1 at h
  simpa only [mul_one] using h

theorem specialLinear_commMonoidHom_eq_one {C : Type*} [CommMonoid C]
    (f : SL(2, ℝ) →* C) (g : SL(2, ℝ)) : f g = 1 := by
  have h := specialLinear_commGroupHom_eq_one f.toHomUnits g
  exact congrArg (fun u : Cˣ => (u : C)) h

end Erdos1148.DukeArithmetic
