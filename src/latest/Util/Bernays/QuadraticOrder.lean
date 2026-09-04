import Mathlib.Algebra.QuadraticAlgebra.NormDeterminant
import ErdosProblems.Erdos1081.Erdos1081Order

/-!
# Negative-discriminant quadratic orders

The order `ℤ[ω]`, with `ω² = d + bω`, includes odd as well as even
discriminants. No maximality assumption is imposed.
-/

open scoped nonZeroDivisors

namespace Bernays

theorem four_mul_quadraticNorm (d b : ℤ) (z : QuadraticAlgebra ℤ d b) :
    4 * z.norm = (2 * z.re + b * z.im) ^ 2 - (b ^ 2 + 4 * d) * z.im ^ 2 := by
  rw [QuadraticAlgebra.norm_def]
  ring

theorem quadraticNorm_nonneg {d b : ℤ} (hD : b ^ 2 + 4 * d < 0)
    (z : QuadraticAlgebra ℤ d b) : 0 ≤ z.norm := by
  have hn := mul_nonpos_of_nonpos_of_nonneg hD.le (sq_nonneg z.im)
  have hi := four_mul_quadraticNorm d b z
  nlinarith [sq_nonneg (2 * z.re + b * z.im)]

theorem quadraticNorm_eq_zero_iff {d b : ℤ} (hD : b ^ 2 + 4 * d < 0)
    (z : QuadraticAlgebra ℤ d b) : z.norm = 0 ↔ z = 0 := by
  constructor
  · intro hzero
    have hi := four_mul_quadraticNorm d b z
    have him : z.im = 0 := by
      by_contra hz
      have hp : 0 < z.im ^ 2 := sq_pos_of_ne_zero hz
      have hn := mul_neg_of_neg_of_pos hD hp
      nlinarith [sq_nonneg (2 * z.re + b * z.im)]
    have hre : z.re = 0 := by
      rw [QuadraticAlgebra.norm_def, him] at hzero
      nlinarith [sq_nonneg z.re]
    exact QuadraticAlgebra.ext hre him
  · rintro rfl
    exact QuadraticAlgebra.norm_zero

def quadraticOrderNoZeroDivisors {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) :
    NoZeroDivisors (QuadraticAlgebra ℤ d b) where
  eq_zero_or_eq_zero_of_mul_eq_zero := by
    intro x y hxy
    have h : x.norm * y.norm = 0 := by
      rw [← map_mul, hxy, QuadraticAlgebra.norm_zero]
    exact (mul_eq_zero.mp h).imp (quadraticNorm_eq_zero_iff hD x).mp
      (quadraticNorm_eq_zero_iff hD y).mp

def quadraticOrderIsDomain {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) :
    IsDomain (QuadraticAlgebra ℤ d b) := by
  let := quadraticOrderNoZeroDivisors hD
  exact NoZeroDivisors.to_isDomain _

theorem algebraNorm_quadraticOrder (d b : ℤ) (z : QuadraticAlgebra ℤ d b) :
    Algebra.norm ℤ z = z.norm := by
  rw [Algebra.norm_apply]
  exact QuadraticAlgebra.det_toLinearMap_eq_norm z

noncomputable def quadraticOrderClassGroupFintype {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) :
    letI := quadraticOrderIsDomain hD
    Fintype (ClassGroup (QuadraticAlgebra ℤ d b)) := by
  letI := quadraticOrderIsDomain hD
  exact Erdos1081.fintypeClassGroupOfFiniteQuotients
    (bS := QuadraticAlgebra.basis d b) AbsoluteValue.absIsAdmissible

/-- Changing the generator by an integer preserves the order. -/
def quadraticOrderShift (d b k : ℤ) :
    QuadraticAlgebra ℤ (d - b * k - k ^ 2) (b + 2 * k) ≃+* QuadraticAlgebra ℤ d b where
  toFun z := ⟨z.re + k * z.im, z.im⟩
  invFun z := ⟨z.re - k * z.im, z.im⟩
  left_inv z := by ext <;> simp
  right_inv z := by ext <;> simp
  map_mul' x y := by ext <;> simp <;> ring
  map_add' x y := by ext <;> simp <;> ring

theorem quadraticOrderShift_norm (d b k : ℤ)
    (z : QuadraticAlgebra ℤ (d - b * k - k ^ 2) (b + 2 * k)) :
    (quadraticOrderShift d b k z).norm = z.norm := by
  simp only [QuadraticAlgebra.norm_def, quadraticOrderShift, RingEquiv.coe_mk, Equiv.coe_fn_mk]
  ring

end Bernays
