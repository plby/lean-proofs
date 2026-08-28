import Wikipedia.HomotopyGroupsOfSpheres.BalancedRealInvolutions

/-! # The balanced diagonal path has determinant one at every time -/

noncomputable section

namespace Wikipedia.HomotopyGroupsOfSpheres.BalancedRealInvolutions

open RealUnitaryMatrices QuaternionicSymmetricMatrices

def phase (n : ℕ) (θ : ℝ) : Index n → Circle :=
  Sum.elim (fun _ ↦ Circle.exp θ) (fun _ ↦ Circle.exp (-θ))

def diagonalPhase (n : ℕ) (θ : ℝ) : Matrix (Index n) (Index n) ℂ :=
  Matrix.diagonal (fun a ↦ (phase n θ a : ℂ))

theorem diagonalPhase_unitary (n : ℕ) (θ : ℝ) :
    diagonalPhase n θ ∈ unitary (Matrix (Index n) (Index n) ℂ) := by
  apply Matrix.mem_unitaryGroup_iff.mpr
  simp only [diagonalPhase, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
    Matrix.diagonal_mul_diagonal, Pi.star_apply, Complex.star_def, Complex.mul_conj,
    Circle.normSq_coe, Complex.ofReal_one, Matrix.diagonal_one]

theorem diagonalPhase_det (n : ℕ) (θ : ℝ) : (diagonalPhase n θ).det = 1 := by
  simp [diagonalPhase, phase, Matrix.det_diagonal, Fintype.prod_sum_type]

def diagonalUnitary (n : ℕ) (θ : ℝ) : unitary (Matrix (Index n) (Index n) ℂ) :=
  ⟨diagonalPhase n θ, diagonalPhase_unitary n θ⟩

def diagonalSymmetric (n : ℕ) (θ : ℝ) : QuaternionicSymmetricMatrices.Space (Index n) :=
  ⟨diagonalUnitary n θ, Matrix.diagonal_transpose _⟩

def diagonalSpecial (n : ℕ) (θ : ℝ) : SpecialSpace (Index n) :=
  ⟨diagonalSymmetric n θ, Circle.ext (diagonalPhase_det n θ)⟩

theorem continuous_diagonalPhase (n : ℕ) : Continuous (diagonalPhase n) := by
  apply Continuous.matrix_diagonal
  apply continuous_pi
  intro a
  cases a with
  | inl a => exact continuous_subtype_val.comp Circle.exp.continuous
  | inr a => exact continuous_subtype_val.comp (Circle.exp.continuous.comp continuous_neg)

theorem continuous_diagonalUnitary (n : ℕ) : Continuous (diagonalUnitary n) :=
  (continuous_diagonalPhase n).subtype_mk _

theorem continuous_diagonalSpecial (n : ℕ) : Continuous (diagonalSpecial n) :=
  (((continuous_diagonalPhase n).subtype_mk _).subtype_mk _).subtype_mk _

theorem diagonalPhase_eq (n : ℕ) (θ : ℝ) :
    diagonalPhase n θ = (Real.cos θ : ℂ) • (1 : Matrix (Index n) (Index n) ℂ) +
      ((Real.sin θ : ℂ) * Complex.I) • complexification (standardMatrix n) := by
  apply Matrix.ext
  intro a b
  by_cases hab : a = b
  · subst b
    cases a with
    | inl a =>
      simp [diagonalPhase, phase, standardMatrix, sign, complexification,
        Circle.coe_exp, Complex.exp_mul_I]
    | inr a =>
      have he : (Circle.exp θ : ℂ)⁻¹ =
          (Real.cos θ : ℂ) - (Real.sin θ : ℂ) * Complex.I := by
        rw [← Circle.coe_inv, Circle.coe_inv_eq_conj, Circle.coe_exp, Complex.exp_mul_I]
        rw [← Complex.ofReal_cos, ← Complex.ofReal_sin]
        simp only [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I,
          mul_neg, sub_eq_add_neg]
      simpa [diagonalPhase, phase, standardMatrix, sign, complexification,
        Circle.coe_exp, Complex.exp_mul_I, sub_eq_add_neg] using he
  · simp [diagonalPhase, standardMatrix, complexification, hab]

theorem diagonalPhase_add (n : ℕ) (θ φ : ℝ) :
    diagonalPhase n θ * diagonalPhase n φ = diagonalPhase n (θ + φ) := by
  rw [diagonalPhase, diagonalPhase, Matrix.diagonal_mul_diagonal, diagonalPhase]
  apply congrArg Matrix.diagonal
  funext a
  cases a <;> simp [phase, Circle.exp_add, mul_comm]

@[simp] theorem diagonalPhase_zero (n : ℕ) : diagonalPhase n 0 = 1 := by
  rw [diagonalPhase_eq]
  simp

@[simp] theorem diagonalPhase_pi (n : ℕ) : diagonalPhase n Real.pi = -1 := by
  rw [diagonalPhase_eq]
  simp

theorem diagonalPhase_half_pi (n : ℕ) :
    diagonalPhase n (Real.pi / 2) = Complex.I • complexification (standardMatrix n) := by
  rw [diagonalPhase_eq]
  simp

end Wikipedia.HomotopyGroupsOfSpheres.BalancedRealInvolutions
