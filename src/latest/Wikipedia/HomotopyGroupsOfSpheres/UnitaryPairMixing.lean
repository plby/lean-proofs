import Wikipedia.HomotopyGroupsOfSpheres.ScalarBlockMatrices

/-!
# A unitary mixing path with rational complex endpoint coefficients

The two eigenspaces of the block interchange receive phases z and 1.
At z = i the symmetric square is the negative block interchange.
-/

noncomputable section

open scoped Matrix unitInterval

namespace Wikipedia.HomotopyGroupsOfSpheres.UnitaryPairMixing

def matrix (z : Circle) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(1 + (z : ℂ)) / 2, ((z : ℂ) - 1) / 2;
     ((z : ℂ) - 1) / 2, (1 + (z : ℂ)) / 2]

theorem matrix_unitary (z : Circle) : matrix z ∈ unitary (Matrix (Fin 2) (Fin 2) ℂ) := by
  have hn : (z : ℂ).re ^ 2 + (z : ℂ).im ^ 2 = 1 := by
    simpa only [Complex.normSq_apply, pow_two] using Circle.normSq_coe z
  have hr : matrix z * star (matrix z) = 1 := by
    apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
      norm_num [matrix, Matrix.mul_apply, Matrix.star_apply, Fin.sum_univ_two,
        Complex.mul_re, Complex.mul_im, div_eq_mul_inv] <;> nlinarith [hn]
  exact ⟨mul_eq_one_comm.mp hr, hr⟩

def mixing : C(Circle, unitary (Matrix (Fin 2) (Fin 2) ℂ)) where
  toFun z := ⟨matrix z, matrix_unitary z⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply _root_.continuous_matrix
    intro i j
    fin_cases i <;> fin_cases j <;> simp only [matrix] <;> fun_prop

theorem mixing_one : mixing 1 = 1 := by
  apply Subtype.ext
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [mixing, matrix]

def quarter : unitary (Matrix (Fin 2) (Fin 2) ℂ) := mixing (Circle.exp (Real.pi / 2))

theorem quarter_val :
    quarter.val = !![(1 + Complex.I) / 2, (Complex.I - 1) / 2;
      (Complex.I - 1) / 2, (1 + Complex.I) / 2] := by
  have hp : (Circle.exp (Real.pi / 2) : ℂ) = Complex.I := by
    rw [Circle.coe_exp, Complex.exp_mul_I]
    norm_num [← Complex.ofReal_cos, ← Complex.ofReal_sin]
  change matrix (Circle.exp (Real.pi / 2)) = _
  rw [matrix, hp]

theorem quarter_mul_transpose : quarter.val * quarter.val.transpose = !![0, -1; -1, 0] := by
  rw [quarter_val]
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    norm_num [Matrix.mul_apply, Fin.sum_univ_two, Complex.mul_re, Complex.mul_im]

def path : C(I, unitary (Matrix (Fin 2) (Fin 2) ℂ)) :=
  mixing.comp (Circle.exp.comp
    ⟨fun t ↦ (t : ℝ) * (Real.pi / 2), continuous_subtype_val.mul_const _⟩)

theorem path_zero : path 0 = 1 := by
  change mixing (Circle.exp ((0 : ℝ) * (Real.pi / 2))) = 1
  rw [zero_mul, Circle.exp_zero, mixing_one]

theorem path_one : path 1 = quarter := by
  change mixing (Circle.exp ((1 : ℝ) * (Real.pi / 2))) = quarter
  rw [one_mul]
  rfl

variable {N : Type*} [Fintype N] [DecidableEq N]

def blockPath : C(I, unitary (Matrix (N ⊕ N) (N ⊕ N) ℂ)) :=
  ⟨fun t ↦ ScalarBlockMatrices.unitaryMap (path t),
    ScalarBlockMatrices.continuous_unitaryMap.comp path.continuous⟩

theorem blockPath_zero : blockPath (N := N) 0 = 1 := by
  change ScalarBlockMatrices.unitaryMap (N := N) (path 0) = 1
  rw [path_zero, map_one]

theorem blockPath_one :
    blockPath (N := N) 1 = ScalarBlockMatrices.unitaryMap quarter := by
  change ScalarBlockMatrices.unitaryMap (N := N) (path 1) = _
  rw [path_one]

theorem blockPath_one_mul_transpose :
    (blockPath (N := N) 1).val * (blockPath 1).val.transpose =
      Matrix.fromBlocks (0 : Matrix N N ℂ) (-1) (-1) 0 := by
  rw [blockPath_one, ScalarBlockMatrices.unitaryMap_val,
    ScalarBlockMatrices.matrix_transpose, ← ScalarBlockMatrices.matrix_mul,
    quarter_mul_transpose]
  simp [ScalarBlockMatrices.matrix]

end Wikipedia.HomotopyGroupsOfSpheres.UnitaryPairMixing
