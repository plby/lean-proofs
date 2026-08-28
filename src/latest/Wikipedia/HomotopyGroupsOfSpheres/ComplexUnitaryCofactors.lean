import Wikipedia.HomotopyGroupsOfSpheres.ComplexUnitaryEntryNorm
import Mathlib.LinearAlgebra.Matrix.Adjugate

/-! # Cofactors of complex unitary matrices

The adjugate is the determinant times the conjugate transpose. The selected
three-dimensional minor will be used on the two vectors in the Schur-pivot
preimage equations.
-/

noncomputable section

open scoped Matrix

namespace Wikipedia.HomotopyGroupsOfSpheres.ComplexUnitaryEntryNorm

variable {N : Type*} [Fintype N] [DecidableEq N]

theorem adjugate_eq_det_smul_star (U : unitary (Matrix N N ℂ)) :
    U.val.adjugate = U.val.det • star U.val := by
  have hu : U.val * star U.val = 1 := Unitary.coe_mul_star_self U
  calc
    U.val.adjugate = U.val.adjugate * (U.val * star U.val) := by
      rw [hu, Matrix.mul_one]
    _ = (U.val.adjugate * U.val) * star U.val := by rw [Matrix.mul_assoc]
    _ = U.val.det • star U.val := by
      rw [Matrix.adjugate_mul, Matrix.smul_mul, Matrix.one_mul]

theorem normSq_det (U : unitary (Matrix N N ℂ)) : Complex.normSq U.val.det = 1 := by
  have h := (Matrix.det_of_mem_unitary U.property).1
  have hc : (Complex.normSq U.val.det : ℂ) = 1 := by
    simpa only [Complex.normSq_eq_conj_mul_self, Complex.star_def] using h
  exact_mod_cast hc

theorem cofactor_twelve (U : unitary (Matrix (Fin 3) (Fin 3) ℂ)) :
    U.val 0 0 * U.val 2 1 - U.val 0 1 * U.val 2 0 =
      -U.val.det * star (U.val 1 2) := by
  have h := congrArg (fun A : Matrix (Fin 3) (Fin 3) ℂ ↦ A 2 1)
    (adjugate_eq_det_smul_star U)
  rw [Matrix.adjugate_fin_three] at h
  change -(U.val 0 0 * U.val 2 1) + U.val 0 1 * U.val 2 0 =
    U.val.det * star (U.val 1 2) at h
  linear_combination -h

def minorOne (v w : Fin 3 → ℂ) : ℂ := v 2 * w 0 - v 0 * w 2

theorem minorOne_smul (a b : ℂ) (v w : Fin 3 → ℂ) :
    minorOne (a • v) (b • w) = a * b * minorOne v w := by
  simp only [minorOne, Pi.smul_apply, smul_eq_mul]
  ring

theorem minorOne_mulVec_inputs (U : unitary (Matrix (Fin 3) (Fin 3) ℂ)) (p q : ℂ) :
    minorOne (U.val *ᵥ ![star p, 1, 0]) (U.val *ᵥ ![star q, 0, 0]) =
      -U.val.det * star (U.val 1 2) * star q := by
  calc
    _ = (U.val 0 0 * U.val 2 1 - U.val 0 1 * U.val 2 0) * star q := by
      simp [minorOne, Matrix.mulVec, dotProduct, Fin.sum_univ_three,
        Matrix.cons_val_two]
      ring
    _ = _ := by rw [cofactor_twelve]

end Wikipedia.HomotopyGroupsOfSpheres.ComplexUnitaryEntryNorm
