import Wikipedia.NoExoticSixSphere.RankSixSkewMatrix

/-!
# The Pfaffian sign of an actual rank-six complex-structure matrix

A quadratic trace identity and a quartic cofactor identity show that a real
skew matrix squaring to minus identity has Pfaffian square one. The proof
uses explicit polynomial identities rather than a determinant expansion.
-/

namespace NoExoticSixSphere.RankSixSkewMatrix

def diagonalEnergy (A : Matrix6) : ℝ :=
  A 0 0 ^ 2 + A 1 1 ^ 2 + A 2 2 ^ 2 + A 3 3 ^ 2 + A 4 4 ^ 2 + A 5 5 ^ 2

theorem trace_square (A : Matrix6) : (skew A * skew A).trace = -2 * energy A := by
  let x01 : ℝ := A 0 1
  let x02 : ℝ := A 0 2
  let x03 : ℝ := A 0 3
  let x04 : ℝ := A 0 4
  let x05 : ℝ := A 0 5
  let x12 : ℝ := A 1 2
  let x13 : ℝ := A 1 3
  let x14 : ℝ := A 1 4
  let x15 : ℝ := A 1 5
  let x23 : ℝ := A 2 3
  let x24 : ℝ := A 2 4
  let x25 : ℝ := A 2 5
  let x34 : ℝ := A 3 4
  let x35 : ℝ := A 3 5
  let x45 : ℝ := A 4 5
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, sum_six]
  change
    ((0) * (0) + (x01) * (-x01) + (x02) * (-x02) + (x03) * (-x03) + (x04) * (-x04) + (x05) *
    (-x05)) + ((-x01) * (x01) + (0) * (0) + (x12) * (-x12) + (x13) * (-x13) + (x14) * (-x14) +
    (x15) * (-x15)) + ((-x02) * (x02) + (-x12) * (x12) + (0) * (0) + (x23) * (-x23) + (x24) *
    (-x24) + (x25) * (-x25)) + ((-x03) * (x03) + (-x13) * (x13) + (-x23) * (x23) + (0) * (0) +
    (x34) * (-x34) + (x35) * (-x35)) + ((-x04) * (x04) + (-x14) * (x14) + (-x24) * (x24) + (-x34)
    * (x34) + (0) * (0) + (x45) * (-x45)) + ((-x05) * (x05) + (-x15) * (x15) + (-x25) * (x25) +
    (-x35) * (x35) + (-x45) * (x45) + (0) * (0)) = -2 * (x01 ^ 2 + x02 ^ 2 + x03 ^ 2 + x04 ^ 2 +
    x05 ^ 2 + x12 ^ 2 + x13 ^ 2 + x14 ^ 2 + x15 ^ 2 + x23 ^ 2 + x24 ^ 2 + x25 ^ 2 + x34 ^ 2 + x35
    ^ 2 + x45 ^ 2)
  ring

theorem energy_smul (c : ℝ) (A : Matrix6) : energy (c • A) = c ^ 2 * energy A := by
  simp only [energy, Matrix.smul_apply, smul_eq_mul]
  ring

theorem coPfaffian_energy_relation (A : Matrix6) :
    4 * energy (coPfaffian A) = 2 * energy A ^ 2 -
      diagonalEnergy (skew A * skew A) - 2 * energy (skew A * skew A) := by
  simp only [diagonalEnergy, energy, Matrix.mul_apply, sum_six]
  let x01 : ℝ := A 0 1
  let x02 : ℝ := A 0 2
  let x03 : ℝ := A 0 3
  let x04 : ℝ := A 0 4
  let x05 : ℝ := A 0 5
  let x12 : ℝ := A 1 2
  let x13 : ℝ := A 1 3
  let x14 : ℝ := A 1 4
  let x15 : ℝ := A 1 5
  let x23 : ℝ := A 2 3
  let x24 : ℝ := A 2 4
  let x25 : ℝ := A 2 5
  let x34 : ℝ := A 3 4
  let x35 : ℝ := A 3 5
  let x45 : ℝ := A 4 5
  change
    4 * ((-x23 * x45 + x24 * x35 - x25 * x34) ^ 2 + (x13 * x45 - x14 * x35 + x15 * x34) ^ 2 +
    (-x12 * x45 + x14 * x25 - x15 * x24) ^ 2 + (x12 * x35 - x13 * x25 + x15 * x23) ^ 2 + (-x12 *
    x34 + x13 * x24 - x14 * x23) ^ 2 + (-x03 * x45 + x04 * x35 - x05 * x34) ^ 2 + (x02 * x45 - x04
    * x25 + x05 * x24) ^ 2 + (-x02 * x35 + x03 * x25 - x05 * x23) ^ 2 + (x02 * x34 - x03 * x24 +
    x04 * x23) ^ 2 + (-x01 * x45 + x04 * x15 - x05 * x14) ^ 2 + (x01 * x35 - x03 * x15 + x05 *
    x13) ^ 2 + (-x01 * x34 + x03 * x14 - x04 * x13) ^ 2 + (-x01 * x25 + x02 * x15 - x05 * x12) ^ 2
    + (x01 * x24 - x02 * x14 + x04 * x12) ^ 2 + (-x01 * x23 + x02 * x13 - x03 * x12) ^ 2) =
    2 * (x01 ^ 2 + x02 ^ 2 + x03 ^ 2 + x04 ^ 2 + x05 ^ 2 + x12 ^ 2 + x13 ^ 2 + x14 ^ 2 + x15 ^ 2 +
    x23 ^ 2 + x24 ^ 2 + x25 ^ 2 + x34 ^ 2 + x35 ^ 2 + x45 ^ 2) ^ 2 -
    (((0) * (0) + (x01) * (-x01) + (x02) * (-x02) + (x03) * (-x03) + (x04) * (-x04) + (x05) *
    (-x05)) ^ 2 + ((-x01) * (x01) + (0) * (0) + (x12) * (-x12) + (x13) * (-x13) + (x14) * (-x14) +
    (x15) * (-x15)) ^ 2 + ((-x02) * (x02) + (-x12) * (x12) + (0) * (0) + (x23) * (-x23) + (x24) *
    (-x24) + (x25) * (-x25)) ^ 2 + ((-x03) * (x03) + (-x13) * (x13) + (-x23) * (x23) + (0) * (0) +
    (x34) * (-x34) + (x35) * (-x35)) ^ 2 + ((-x04) * (x04) + (-x14) * (x14) + (-x24) * (x24) +
    (-x34) * (x34) + (0) * (0) + (x45) * (-x45)) ^ 2 + ((-x05) * (x05) + (-x15) * (x15) + (-x25) *
    (x25) + (-x35) * (x35) + (-x45) * (x45) + (0) * (0)) ^ 2) -
    2 * (((0) * (x01) + (x01) * (0) + (x02) * (-x12) + (x03) * (-x13) + (x04) * (-x14) + (x05) *
    (-x15)) ^ 2 + ((0) * (x02) + (x01) * (x12) + (x02) * (0) + (x03) * (-x23) + (x04) * (-x24) +
    (x05) * (-x25)) ^ 2 + ((0) * (x03) + (x01) * (x13) + (x02) * (x23) + (x03) * (0) + (x04) *
    (-x34) + (x05) * (-x35)) ^ 2 + ((0) * (x04) + (x01) * (x14) + (x02) * (x24) + (x03) * (x34) +
    (x04) * (0) + (x05) * (-x45)) ^ 2 + ((0) * (x05) + (x01) * (x15) + (x02) * (x25) + (x03) *
    (x35) + (x04) * (x45) + (x05) * (0)) ^ 2 + ((-x01) * (x02) + (0) * (x12) + (x12) * (0) + (x13)
    * (-x23) + (x14) * (-x24) + (x15) * (-x25)) ^ 2 + ((-x01) * (x03) + (0) * (x13) + (x12) *
    (x23) + (x13) * (0) + (x14) * (-x34) + (x15) * (-x35)) ^ 2 + ((-x01) * (x04) + (0) * (x14) +
    (x12) * (x24) + (x13) * (x34) + (x14) * (0) + (x15) * (-x45)) ^ 2 + ((-x01) * (x05) + (0) *
    (x15) + (x12) * (x25) + (x13) * (x35) + (x14) * (x45) + (x15) * (0)) ^ 2 + ((-x02) * (x03) +
    (-x12) * (x13) + (0) * (x23) + (x23) * (0) + (x24) * (-x34) + (x25) * (-x35)) ^ 2 + ((-x02) *
    (x04) + (-x12) * (x14) + (0) * (x24) + (x23) * (x34) + (x24) * (0) + (x25) * (-x45)) ^ 2 +
    ((-x02) * (x05) + (-x12) * (x15) + (0) * (x25) + (x23) * (x35) + (x24) * (x45) + (x25) * (0))
    ^ 2 + ((-x03) * (x04) + (-x13) * (x14) + (-x23) * (x24) + (0) * (x34) + (x34) * (0) + (x35) *
    (-x45)) ^ 2 + ((-x03) * (x05) + (-x13) * (x15) + (-x23) * (x25) + (0) * (x35) + (x34) * (x45)
    + (x35) * (0)) ^ 2 + ((-x04) * (x05) + (-x14) * (x15) + (-x24) * (x25) + (-x34) * (x35) + (0)
    * (x45) + (x45) * (0)) ^ 2)
  ring

theorem energy_of_square (A : Matrix6) (hA : A.transpose = -A)
    (hsq : A * A = -(1 : Matrix6)) : energy A = 3 := by
  have h := trace_square A
  rw [skew_eq A hA, hsq] at h
  norm_num [Matrix.trace, sum_six, Matrix.one_apply, Fin.ext_iff] at h
  linarith

theorem coPfaffian_energy_of_square (A : Matrix6) (hA : A.transpose = -A)
    (hsq : A * A = -(1 : Matrix6)) : energy (coPfaffian A) = 3 := by
  have h := coPfaffian_energy_relation A
  rw [skew_eq A hA, hsq, energy_of_square A hA hsq] at h
  norm_num [energy, diagonalEnergy, Matrix.one_apply, Fin.ext_iff] at h
  change 4 * energy (coPfaffian A) = 12 at h
  linarith

theorem pfaffian_sq_one (A : Matrix6) (hA : A.transpose = -A)
    (hsq : A * A = -(1 : Matrix6)) : pfaffian A ^ 2 = 1 := by
  have h := coPfaffian_energy_of_square A hA hsq
  rw [coPfaffian_eq_of_square A hA hsq, energy_smul, neg_sq, energy_of_square A hA hsq] at h
  linarith

end NoExoticSixSphere.RankSixSkewMatrix
