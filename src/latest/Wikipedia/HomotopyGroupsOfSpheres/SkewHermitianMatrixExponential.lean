import Wikipedia.HomotopyGroupsOfSpheres.SymmetricUnitaryExponential

/-! # The determinant of the exponential of a skew-Hermitian complex matrix -/

noncomputable section

open scoped Matrix.Norms.Frobenius

namespace Wikipedia.HomotopyGroupsOfSpheres.ComplexMatrixLocalLogarithm

variable {N : Type*} [Fintype N] [DecidableEq N]

theorem skew_hermitian_diagonalization (K : Matrix N N ℂ) (hK : star K = -K) :
    ∃ (U : unitary (Matrix N N ℂ)) (μ : N → ℝ),
      K = U.val * Matrix.diagonal (fun a ↦ Complex.I * (μ a : ℂ)) * star U.val := by
  let H : Matrix N N ℂ := (-Complex.I) • K
  have hH : H.IsHermitian := by
    change star ((-Complex.I) • K) = (-Complex.I) • K
    rw [star_smul, hK]
    simp only [star_neg, Complex.star_def, Complex.conj_I, neg_neg, smul_neg, neg_smul]
  have hrec : K = Complex.I • H := by
    change K = Complex.I • ((-Complex.I) • K)
    rw [smul_smul]
    simp only [mul_neg, Complex.I_mul_I, neg_neg, one_smul]
  let U := hH.eigenvectorUnitary
  let μ := hH.eigenvalues
  have hd : H = U.val * Matrix.diagonal (fun a ↦ (μ a : ℂ)) * star U.val := by
    simpa only [Unitary.conjStarAlgAut_apply, Function.comp_def] using! hH.spectral_theorem
  refine ⟨U, μ, ?_⟩
  rw [hrec, hd, ← smul_mul_assoc, ← mul_smul_comm]
  congr 2
  apply Matrix.ext
  intro a b
  by_cases hab : a = b
  · subst b
    simp only [Matrix.smul_apply, Matrix.diagonal_apply_eq, smul_eq_mul]
  · simp only [Matrix.smul_apply, Matrix.diagonal_apply_ne _ hab, smul_zero]

theorem det_exp_skew (K : Matrix N N ℂ) (hK : star K = -K) :
    (NormedSpace.exp K).det = Complex.exp K.trace := by
  obtain ⟨U, μ, hU⟩ := skew_hermitian_diagonalization K hK
  let D := Matrix.diagonal (fun a ↦ Complex.I * (μ a : ℂ))
  have htrace : K.trace = ∑ a, Complex.I * (μ a : ℂ) := by
    rw [hU, Matrix.trace_mul_cycle, Unitary.star_mul_self_of_mem U.property,
      one_mul, Matrix.trace_diagonal]
  have hdet : U.val.det * (star U.val).det = 1 := by
    rw [← Matrix.det_mul, Unitary.mul_star_self_of_mem U.property, Matrix.det_one]
  have hdiag : (NormedSpace.exp D).det = Complex.exp (∑ a, Complex.I * (μ a : ℂ)) := by
    change (NormedSpace.exp (Matrix.diagonal (fun a ↦ Complex.I * (μ a : ℂ)))).det = _
    rw [Matrix.exp_diagonal, Matrix.det_diagonal, Complex.exp_sum]
    apply Finset.prod_congr rfl
    intro a _
    rw [Pi.coe_exp, Complex.exp_eq_exp_ℂ]
  have hexp : NormedSpace.exp K = U.val * NormedSpace.exp D * star U.val := by
    calc
      NormedSpace.exp K = NormedSpace.exp (U.val * D * star U.val) := congrArg NormedSpace.exp hU
      _ = U.val * NormedSpace.exp D * star U.val := Matrix.exp_units_conj (Unitary.toUnits U) D
  rw [hexp, Matrix.det_mul, Matrix.det_mul]
  calc
    U.val.det * (NormedSpace.exp D).det * (star U.val).det =
        (NormedSpace.exp D).det * (U.val.det * (star U.val).det) := by ring
    _ = Complex.exp K.trace := by rw [hdet, mul_one, hdiag, htrace]

end Wikipedia.HomotopyGroupsOfSpheres.ComplexMatrixLocalLogarithm
