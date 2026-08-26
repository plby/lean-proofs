import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.LinearCombination

/-! Integer spectral restrictions in dimension three. The statements do not
assume that a nonnegative boundary matrix has zero diagonal. -/

namespace Erdos633b

open Matrix

theorem int_coefficients_of_irrational {x : ℝ} (hx : Irrational x) (a b : ℤ)
    (h : (a : ℝ) * x = b) : a = 0 ∧ b = 0 := by
  have ha : a = 0 := by
    by_contra hn
    have hn' : (a : ℝ) ≠ 0 := by exact_mod_cast hn
    exact hx.ne_rational b a ((eq_div_iff hn').mpr (by simpa [mul_comm] using h))
  subst a
  simp only [Int.cast_zero, zero_mul, eq_comm, Int.cast_eq_zero] at h
  exact ⟨rfl, h⟩

namespace ThreeMatrix

def traceInt (D : Matrix (Fin 3) (Fin 3) ℤ) : ℤ := D 0 0 + D 1 1 + D 2 2

def secondInt (D : Matrix (Fin 3) (Fin 3) ℤ) : ℤ :=
  D 0 0 * D 1 1 + D 0 0 * D 2 2 + D 1 1 * D 2 2 -
    D 0 1 * D 1 0 - D 0 2 * D 2 0 - D 1 2 * D 2 1

def toReal (D : Matrix (Fin 3) (Fin 3) ℤ) : Matrix (Fin 3) (Fin 3) ℝ :=
  fun i j => D i j

theorem shifted_det (D : Matrix (Fin 3) (Fin 3) ℤ) (x : ℝ) :
    (x • (1 : Matrix (Fin 3) (Fin 3) ℝ) - toReal D).det =
      x ^ 3 - (traceInt D : ℝ) * x ^ 2 + (secondInt D : ℝ) * x - (D.det : ℝ) := by
  simp [Matrix.det_fin_three, traceInt, secondInt, toReal,
    Matrix.sub_apply, Matrix.smul_apply]
  ring

theorem shifted_det_eq_zero {D : Matrix (Fin 3) (Fin 3) ℤ} {x : ℝ}
    {v : Fin 3 → ℝ} (hv : v ≠ 0) (h : toReal D *ᵥ v = x • v) :
    (x • (1 : Matrix (Fin 3) (Fin 3) ℝ) - toReal D).det = 0 := by
  apply Matrix.exists_mulVec_eq_zero_iff.mp
  refine ⟨v, hv, ?_⟩
  rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, h, sub_self]

theorem nonsquare_coefficients {D : Matrix (Fin 3) (Fin 3) ℤ} {n : ℕ}
    (hn : ¬ IsSquare n) {v : Fin 3 → ℝ} (hv : v ≠ 0)
    (h : toReal D *ᵥ v = Real.sqrt n • v) :
    secondInt D = -(n : ℤ) ∧ D.det = -traceInt D * n := by
  have he := shifted_det_eq_zero hv h
  rw [shifted_det] at he
  have hs : Real.sqrt (n : ℝ) ^ 2 = n := Real.sq_sqrt (Nat.cast_nonneg n)
  have hc : ((n : ℤ) + secondInt D : ℤ) * (Real.sqrt n : ℝ) =
      (traceInt D * n + D.det : ℤ) := by
    simp only [Int.cast_add, Int.cast_mul, Int.cast_natCast]
    linear_combination he - (Real.sqrt n - (traceInt D : ℝ)) * hs
  obtain ⟨ha, hb⟩ := int_coefficients_of_irrational
    (irrational_sqrt_natCast_iff.mpr hn) _ _ hc
  constructor
  · omega
  · linear_combination hb

theorem nonsquare_shifted_det {D : Matrix (Fin 3) (Fin 3) ℤ} {n : ℕ}
    (hn : ¬ IsSquare n) {v : Fin 3 → ℝ} (hv : v ≠ 0)
    (h : toReal D *ᵥ v = Real.sqrt n • v) (x : ℝ) :
    (x • (1 : Matrix (Fin 3) (Fin 3) ℝ) - toReal D).det =
      (x ^ 2 - n) * (x - traceInt D) := by
  obtain ⟨hs, hd⟩ := nonsquare_coefficients hn hv h
  rw [shifted_det, hs, hd]
  push_cast
  ring

theorem exists_negative_eigenvector {D : Matrix (Fin 3) (Fin 3) ℤ} {n : ℕ}
    (hn : ¬ IsSquare n) {v : Fin 3 → ℝ} (hv : v ≠ 0)
    (h : toReal D *ᵥ v = Real.sqrt n • v) :
    ∃ w : Fin 3 → ℝ, w ≠ 0 ∧ toReal D *ᵥ w = -Real.sqrt n • w := by
  have hd : ((-Real.sqrt n) • (1 : Matrix (Fin 3) (Fin 3) ℝ) - toReal D).det = 0 := by
    rw [nonsquare_shifted_det hn hv h, neg_sq, Real.sq_sqrt (Nat.cast_nonneg n)]
    simp
  obtain ⟨w, hw, he⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hd
  refine ⟨w, hw, ?_⟩
  rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, sub_eq_zero] at he
  exact he.symm

end ThreeMatrix

end Erdos633b
