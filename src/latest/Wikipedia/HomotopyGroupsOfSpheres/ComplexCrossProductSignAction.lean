import Wikipedia.HomotopyGroupsOfSpheres.ComplexCrossProductScalarAction

/-! # The four sign symmetries preserving a diagonal symmetric image -/

noncomputable section

open scoped Matrix

namespace Wikipedia.HomotopyGroupsOfSpheres.ComplexCrossProductUnitary

def boolSign (b : Bool) : ℂ := if b then 1 else -1

theorem boolSign_injective : Function.Injective boolSign := by
  intro x y h
  cases x <;> cases y <;> simp_all [boolSign]
  all_goals norm_num at h

theorem boolSign_star (b : Bool) : star (boolSign b) = boolSign b := by
  cases b <;> simp [boolSign]

theorem boolSign_sq (b : Bool) : boolSign b ^ 2 = 1 := by cases b <;> norm_num [boolSign]

def signs (x y : Bool) : Fin 3 → ℂ := ![boolSign x, boolSign y, boolSign x * boolSign y]

theorem signs_star (x y : Bool) (r : Fin 3) : star (signs x y r) = signs x y r := by
  fin_cases r <;> simp [signs, Matrix.cons_val_two, boolSign_star]

theorem signs_sq (x y : Bool) (r : Fin 3) : signs x y r ^ 2 = 1 := by
  fin_cases r <;> simp [signs, Matrix.cons_val_two, mul_pow, boolSign_sq]

def signVector (x y : Bool) (z : Vector) : Vector := fun r ↦ signs x y r * z r
def signMatrix (x y : Bool) : Matrix (Fin 3) (Fin 3) ℂ := Matrix.diagonal (signs x y)

theorem normPolynomial_signVector (x y : Bool) (z : Vector) :
    normPolynomial (signVector x y z) = normPolynomial z := by
  apply Finset.sum_congr rfl
  intro r _
  change star (signs x y r * z r) * (signs x y r * z r) = star (z r) * z r
  rw [star_mul, signs_star]
  calc
    _ = signs x y r ^ 2 * (star (z r) * z r) := by ring
    _ = _ := by rw [signs_sq, one_mul]

theorem signMatrix_transpose (x y : Bool) : (signMatrix x y).transpose = signMatrix x y := by
  simp [signMatrix]

theorem signMatrix_mul_self (x y : Bool) : signMatrix x y * signMatrix x y = 1 := by
  simp only [signMatrix, Matrix.diagonal_mul_diagonal]
  ext r s
  by_cases h : r = s
  · subst s
    simpa [← pow_two] using signs_sq x y r
  · simp [h]

theorem matrix_signVector (x y : Bool) (z : Vector) :
    matrix (signVector x y z) = signMatrix x y * matrix z * signMatrix x y := by
  ext r s
  simp only [signMatrix, Matrix.mul_diagonal, Matrix.diagonal_mul]
  fin_cases r <;> fin_cases s <;> cases x <;> cases y <;>
    simp [signVector, signs, boolSign, matrix, outer, crossMatrix, Matrix.cons_val_two] <;> ring

def signSphere (x y : Bool) (z : UnitSphere) : UnitSphere :=
  sphereOfNormPolynomial (signVector x y z.val) (by
    rw [normPolynomial_signVector, normPolynomial_unit])

theorem signSphere_val (x y : Bool) (z : UnitSphere) (r : Fin 3) :
    (signSphere x y z).val r = signs x y r * z.val r := rfl

theorem symmetricMap_signSphere (x y : Bool) (z : UnitSphere) :
    (symmetricMap (signSphere x y z)).val.val =
      signMatrix x y * (symmetricMap z).val.val * signMatrix x y := by
  rw [symmetricMap_val, symmetricMap_val]
  change matrix (signVector x y z.val) * (matrix (signVector x y z.val)).transpose = _
  rw [matrix_signVector, Matrix.transpose_mul, Matrix.transpose_mul, signMatrix_transpose]
  simp only [mul_assoc, ← mul_assoc (signMatrix x y) (signMatrix x y),
    signMatrix_mul_self, one_mul]

theorem diagonal_signSphere (x y : Bool) (z : UnitSphere) (d : Fin 3 → ℂ)
    (hd : (symmetricMap z).val.val = Matrix.diagonal d) :
    (symmetricMap (signSphere x y z)).val.val = Matrix.diagonal d := by
  rw [symmetricMap_signSphere, hd]
  simp only [signMatrix, Matrix.diagonal_mul_diagonal]
  ext r s
  by_cases h : r = s
  · subst s
    simp only [Matrix.diagonal_apply_eq]
    calc
      _ = signs x y r ^ 2 * d r := by ring
      _ = _ := by rw [signs_sq, one_mul]
  · simp [h]

theorem signSphere_choices_injective (z : UnitSphere) (h0 : z.val 0 ≠ 0) (h1 : z.val 1 ≠ 0) :
    Function.Injective (fun b : Bool × Bool ↦ signSphere b.1 b.2 z) := by
  intro b c h
  have hzero := congrArg (fun v : UnitSphere ↦ v.val 0) h
  have hone := congrArg (fun v : UnitSphere ↦ v.val 1) h
  apply Prod.ext
  · apply boolSign_injective
    apply mul_right_cancel₀ h0
    exact hzero
  · apply boolSign_injective
    apply mul_right_cancel₀ h1
    exact hone

end Wikipedia.HomotopyGroupsOfSpheres.ComplexCrossProductUnitary
