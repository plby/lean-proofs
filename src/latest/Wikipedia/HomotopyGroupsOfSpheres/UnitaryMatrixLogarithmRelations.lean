import Wikipedia.HomotopyGroupsOfSpheres.SymmetricUnitaryLogarithmRelations
import Wikipedia.HomotopyGroupsOfSpheres.SkewHermitianMatrixExponential
import Wikipedia.HomotopyGroupsOfSpheres.ComplexMatrixFrobeniusIsometry

/-! # Trace, inverse, and reversibility of small unitary logarithms -/

noncomputable section

open scoped Matrix.Norms.Frobenius

namespace Wikipedia.HomotopyGroupsOfSpheres.ComplexMatrixLocalLogarithm

variable {N : Type*} [Fintype N] [DecidableEq N]

theorem logarithm_trace_zero (U : unitary (Matrix N N ℂ)) (hU : U.val ∈ domain N)
    (hdet : U.val.det = 1) : (logarithm U.val).trace = 0 := by
  have ht : |(logarithm U.val).trace.im| < Real.pi :=
    (Complex.abs_im_le_norm _).trans_lt (logarithm_trace_lt U.val hU)
  apply Complex.exp_inj_of_neg_pi_lt_of_le_pi (abs_lt.mp ht).1 (abs_lt.mp ht).2.le
    (by simpa only [Complex.zero_im] using neg_neg_of_pos Real.pi_pos)
    (by simpa only [Complex.zero_im] using Real.pi_pos.le)
  rw [Complex.exp_zero, ← det_exp_skew _ (logarithm_star U.val hU U.property),
    exp_logarithm U.val hU.1, hdet]

theorem logarithm_inverse (U : unitary (Matrix N N ℂ)) (hU : U.val ∈ domain N) :
    (U⁻¹).val ∈ domain N ∧ logarithm (U⁻¹).val = -logarithm U.val := by
  have hn : ‖-logarithm U.val‖ < radius N := by simpa only [norm_neg] using hU.2
  have he : NormedSpace.exp (-logarithm U.val) = (U⁻¹).val := by
    rw [Matrix.exp_neg, exp_logarithm U.val hU.1]
    exact Matrix.inv_eq_left_inv (Unitary.star_mul_self_of_mem U.property)
  refine ⟨?_, ?_⟩
  · rw [← he]
    exact exp_mem_domain _ hn
  · rw [← he]
    exact logarithm_exp _ (mem_safeSource_of_norm_lt _ hn).1

theorem logarithm_reversible (B U : unitary (Matrix N N ℂ)) (hU : U.val ∈ domain N)
    (hrev : U.val.transpose * B.val = B.val * U.val) :
    (logarithm U.val).transpose * B.val = B.val * logarithm U.val := by
  have hconj : ‖B.val * logarithm U.val * star B.val‖ < radius N := by
    rw [ComplexMatrixRealRepresentation.frobenius_norm_conjugate]
    exact hU.2
  have htrans : ‖(logarithm U.val).transpose‖ < radius N := by
    simpa only [Matrix.frobenius_norm_transpose] using hU.2
  have he : NormedSpace.exp (B.val * logarithm U.val * star B.val) =
      NormedSpace.exp (logarithm U.val).transpose := by
    have h : NormedSpace.exp (B.val * logarithm U.val * star B.val) =
        B.val * NormedSpace.exp (logarithm U.val) * star B.val :=
      Matrix.exp_units_conj (Unitary.toUnits B) (logarithm U.val)
    rw [Matrix.exp_transpose, h, exp_logarithm U.val hU.1]
    have hp := congrArg (fun A : Matrix N N ℂ ↦ A * star B.val) hrev
    simpa only [mul_assoc, Unitary.mul_star_self_of_mem B.property, mul_one] using hp.symm
  have hK := exp_injective_small hconj htrans he
  have hp := congrArg (fun A : Matrix N N ℂ ↦ A * B.val) hK
  simpa only [mul_assoc, Unitary.star_mul_self_of_mem B.property, mul_one] using hp.symm

end Wikipedia.HomotopyGroupsOfSpheres.ComplexMatrixLocalLogarithm
