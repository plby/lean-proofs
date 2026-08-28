import Wikipedia.NoExoticSixSphere.RankSixPfaffianNorm
import Wikipedia.NoExoticSixSphere.RankSixSpinMatrix
import Mathlib.Tactic.Module

/-!
# The Hermitian line projection associated to a rank-six complex structure

The matrix is constructed from the explicit spin matrix and its Pfaffian
sign. Idempotence and trace one follow from the checked polynomial identities.
-/

namespace NoExoticSixSphere.RankSixSkewMatrix

theorem spin_square_of_square (A : Matrix6) (hA : A.transpose = -A)
    (hsq : A * A = -(1 : Matrix6)) :
    spin A * spin A = (3 : ℂ) • (1 : Matrix4) -
      (2 * (pfaffian A : ℂ)) • spin A := by
  rw [spin_square, energy_of_square A hA hsq,
    coPfaffian_eq_of_square A hA hsq, spin_real_smul]
  simp [smul_smul, sub_eq_add_neg]

noncomputable def lineProjection (A : Matrix6) : Matrix4 :=
  (1 / 4 : ℂ) • ((1 : Matrix4) - (pfaffian A : ℂ) • spin A)

theorem lineProjection_hermitian (A : Matrix6) :
    (lineProjection A).conjTranspose = lineProjection A := by
  simp [lineProjection, Matrix.conjTranspose_smul, spin_hermitian]

theorem lineProjection_trace (A : Matrix6) : (lineProjection A).trace = 1 := by
  simp [lineProjection, Matrix.trace_smul, Matrix.trace_sub, spin_trace,
    Matrix.trace_one]

theorem lineProjection_idempotent (A : Matrix6) (hA : A.transpose = -A)
    (hsq : A * A = -(1 : Matrix6)) :
    lineProjection A * lineProjection A = lineProjection A := by
  have hp : (pfaffian A : ℂ) * (pfaffian A : ℂ) = 1 := by
    exact_mod_cast (show pfaffian A * pfaffian A = 1 by
      simpa only [pow_two] using pfaffian_sq_one A hA hsq)
  rw [lineProjection, smul_mul_smul, sub_mul, mul_sub, mul_sub]
  simp only [one_mul, mul_one, smul_mul_smul, spin_square_of_square A hA hsq, hp,
    smul_sub, smul_smul]
  module

end NoExoticSixSphere.RankSixSkewMatrix
