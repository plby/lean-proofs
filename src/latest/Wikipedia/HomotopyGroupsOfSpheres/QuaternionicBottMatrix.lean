import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicSymmetricMatrixAlgebra
import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns

/-!
# An explicit matrix formula for the first two symplectic rotations

For a symmetric complex unitary matrix `B`, the quaternionic matrix
`a I + b i I + c B j` is unitary when `a² + b² + c² = 1`.
This is the concrete family whose nested rotations enter the Bott map.
The present file proves the matrix identities and continuity; it does not
assert a generator or a projected degree.
-/

noncomputable section

open scoped Matrix

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicBottMatrix

open QuaternionicScalars QuaternionicSymmetricMatrices QuaternionicColumns

local notation "ℍ" => Quaternion ℝ

variable {N : Type*} [Fintype N] [DecidableEq N]

def imaginaryAxis (N : Type*) [DecidableEq N] : Matrix N N ℍ :=
  Matrix.diagonal (fun _ ↦ i)

omit [Fintype N] in
theorem imaginaryAxis_star : star (imaginaryAxis N) = -(imaginaryAxis N) := by
  change (Matrix.diagonal (fun _ : N ↦ i))ᴴ = -(Matrix.diagonal (fun _ : N ↦ i))
  rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_neg]
  exact congrArg Matrix.diagonal (funext (fun _ ↦ star_i))

omit [Fintype N] [DecidableEq N] in
private theorem star_real_smul (r : ℝ) (A : Matrix N N ℍ) :
    star (r • A) = r • star A := by
  apply Matrix.ext
  intro i j
  exact Quaternion.star_smul r (A j i)

theorem imaginaryAxis_square : imaginaryAxis N * imaginaryAxis N = -1 := by
  rw [imaginaryAxis, Matrix.diagonal_mul_diagonal]
  simp only [i_mul_i]
  rw [← Matrix.diagonal_neg, Matrix.diagonal_one]

def skewPart (b c : ℝ) (B : Space N) : Matrix N N ℍ :=
  b • imaginaryAxis N + c • quaternionMatrix B.val.val

theorem skewPart_star (b c : ℝ) (B : Space N) :
    star (skewPart b c B) = -(skewPart b c B) := by
  simp only [skewPart, star_add, star_real_smul, imaginaryAxis_star,
    quaternionMatrix_star, B.property, smul_neg, neg_add_rev]
  abel

theorem skewPart_square (b c : ℝ) (B : Space N) :
    skewPart b c B * skewPart b c B = -((b ^ 2 + c ^ 2) • (1 : Matrix N N ℍ)) := by
  have hB : quaternionMatrix B.val.val * quaternionMatrix B.val.val = -1 :=
    (quaternionMatrix_square_iff B.val.val B.property).mpr B.val.property
  have hcross : (b * c) • (imaginaryAxis N * quaternionMatrix B.val.val) +
      (c * b) • (quaternionMatrix B.val.val * imaginaryAxis N) = 0 := by
    rw [show imaginaryAxis N * quaternionMatrix B.val.val =
      -(quaternionMatrix B.val.val * imaginaryAxis N) from
        quaternionMatrix_anticommutes B.val.val, smul_neg, mul_comm c b, neg_add_cancel]
  calc
    skewPart b c B * skewPart b c B =
        ((b * b) • (imaginaryAxis N * imaginaryAxis N) +
          (c * c) • (quaternionMatrix B.val.val * quaternionMatrix B.val.val)) +
        ((b * c) • (imaginaryAxis N * quaternionMatrix B.val.val) +
          (c * b) • (quaternionMatrix B.val.val * imaginaryAxis N)) := by
      simp only [skewPart, add_mul, mul_add, smul_mul_assoc, mul_smul_comm,
        smul_add, smul_smul]
      rw [mul_comm c b]
      abel
    _ = _ := by
      rw [hcross, add_zero, imaginaryAxis_square, hB, ← add_smul,
        ← pow_two b, ← pow_two c, smul_neg]

def matrix (a b c : ℝ) (B : Space N) : Matrix N N ℍ :=
  a • 1 + skewPart b c B

theorem matrix_star (a b c : ℝ) (B : Space N) :
    star (matrix a b c B) = a • 1 - skewPart b c B := by
  simp only [matrix, star_add, star_real_smul, star_one,
    skewPart_star, sub_eq_add_neg]

theorem matrix_unitary (a b c : ℝ) (B : Space N)
    (h : a ^ 2 + b ^ 2 + c ^ 2 = 1) : matrix a b c B ∈ unitary (Matrix N N ℍ) := by
  have hleft : star (matrix a b c B) * matrix a b c B = 1 := by
    rw [matrix_star]
    change (a • 1 - skewPart b c B) * (a • 1 + skewPart b c B) = 1
    calc
      (a • 1 - skewPart b c B) * (a • 1 + skewPart b c B) =
          (a * a) • 1 - skewPart b c B * skewPart b c B := by
        simp only [sub_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]
        module
      _ = 1 := by
        rw [skewPart_square, sub_neg_eq_add, ← add_smul, ← pow_two a,
          ← add_assoc, h, one_smul]
  exact ⟨hleft, mul_eq_one_comm.mp hleft⟩

abbrev Coefficients := {v : ℝ × ℝ × ℝ // v.1 ^ 2 + v.2.1 ^ 2 + v.2.2 ^ 2 = 1}

def family : C(Coefficients × Space N, SpGroup N) where
  toFun z := ⟨matrix z.1.val.1 z.1.val.2.1 z.1.val.2.2 z.2,
    matrix_unitary _ _ _ _ z.1.property⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    have hv : Continuous (fun z : Coefficients × Space N ↦ z.1.val) :=
      continuous_subtype_val.comp continuous_fst
    have hB : Continuous (fun z : Coefficients × Space N ↦ z.2.val.val) :=
      continuous_subtype_val.comp (continuous_subtype_val.comp continuous_snd)
    exact (hv.fst.smul continuous_const).add
      ((hv.snd.fst.smul continuous_const).add
        (hv.snd.snd.smul (continuous_quaternionMatrix.comp hB)))

theorem matrix_apply (a b c : ℝ) (B : Space N) (r s : N) :
    matrix a b c B r s =
      a • (if r = s then 1 else 0) + b • (if r = s then i else 0) +
        c • QuaternionicComplexPlane.embed (B.val.val r s) := by
  simp only [matrix, skewPart, imaginaryAxis, quaternionMatrix, Matrix.add_apply,
    Matrix.smul_apply, Matrix.one_apply, Matrix.diagonal_apply, Matrix.map_apply]
  abel

theorem matrix_zero_coefficient (a b : ℝ) (B : Space N) :
    matrix a b 0 B = a • 1 + b • imaginaryAxis N := by
  simp only [matrix, skewPart, zero_smul, add_zero]

theorem matrix_north (B : Space N) : matrix 1 0 0 B = 1 := by
  simp only [matrix, skewPart, zero_smul, one_smul, add_zero]

theorem matrix_south (B : Space N) : matrix (-1) 0 0 B = -1 := by
  simp only [matrix, skewPart, zero_smul, neg_one_smul, add_zero]

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicBottMatrix
