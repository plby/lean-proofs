import Wikipedia.HomotopyGroupsOfSpheres.SymmetricUnitaryAntipodalSpectrum
import Wikipedia.HomotopyGroupsOfSpheres.BalancedRealClassification

/-!
# Minimum squared norm among antipodal symmetric unitary generators

The least squared norm of a symmetric generator of `-1` is the matrix
rank times `π²`. Among trace-zero generators in even rank, equality
holds exactly for `π` times a balanced real involution. This is a
classification of exponential generators, not yet a deformation theorem
or a lower bound for arbitrary paths.
-/

noncomputable section

namespace Wikipedia.HomotopyGroupsOfSpheres

namespace RealMatrixSquareNorm

variable {N : Type*} [Fintype N] [DecidableEq N]

theorem squareNorm_diagonal (μ : N → ℝ) :
    squareNorm (Matrix.diagonal μ) = ∑ a, μ a ^ 2 := by
  simp [squareNorm, Matrix.diagonal_apply]

theorem conjugate_diagonal_square (U : unitary (Matrix N N ℝ)) (μ : N → ℝ)
    (c : ℝ) (hμ : ∀ a, μ a ^ 2 = c) :
    conjugate U (Matrix.diagonal μ) * conjugate U (Matrix.diagonal μ) =
      c • (1 : Matrix N N ℝ) := by
  have hD : Matrix.diagonal μ * Matrix.diagonal μ = c • (1 : Matrix N N ℝ) := by
    rw [Matrix.diagonal_mul_diagonal, Matrix.smul_one_eq_diagonal]
    apply congrArg Matrix.diagonal
    funext a
    exact (pow_two (μ a)).symm.trans (hμ a)
  rw [conjugate_mul, hD, map_smul]
  change c • (U.val * 1 * U.val.transpose) = c • (1 : Matrix N N ℝ)
  rw [mul_one, ← RealUnitaryMatrices.star_eq_transpose,
    Unitary.mul_star_self_of_mem U.property]

end RealMatrixSquareNorm

namespace ImaginarySymmetricMatrices

theorem odd_speed_sq_ge (m : ℤ) : Real.pi ^ 2 ≤ (Real.pi * (2 * (m : ℝ) + 1)) ^ 2 := by
  have h := BalancedRealInvolutions.integer_odd_speed_range m
  have hs : 1 ≤ (2 * (m : ℝ) + 1) ^ 2 := by
    rcases h with h | h | h | h <;> nlinarith
  have hp := mul_le_mul_of_nonneg_left hs (sq_nonneg Real.pi)
  simpa only [mul_one, mul_pow] using hp

variable {N : Type*} [Fintype N] [DecidableEq N]

theorem antipodal_squareNorm_ge (A : Matrix N N ℝ) (hsym : A.transpose = A)
    (hexp : NormedSpace.exp (imaginary A) = -1) :
    (Fintype.card N : ℝ) * Real.pi ^ 2 ≤ RealMatrixSquareNorm.squareNorm A := by
  obtain ⟨U, m, hA, _⟩ := antipodal_diagonalization A hsym hexp
  rw [hA, RealMatrixSquareNorm.squareNorm_conjugate, RealMatrixSquareNorm.squareNorm_diagonal]
  have h := Finset.sum_le_sum (fun a (_ : a ∈ Finset.univ) ↦ odd_speed_sq_ge (m a))
  simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using h

theorem antipodal_squareNorm_eq_iff (A : Matrix N N ℝ) (hsym : A.transpose = A)
    (hexp : NormedSpace.exp (imaginary A) = -1) :
    RealMatrixSquareNorm.squareNorm A = (Fintype.card N : ℝ) * Real.pi ^ 2 ↔
      A * A = Real.pi ^ 2 • (1 : Matrix N N ℝ) := by
  constructor
  · intro hnorm
    obtain ⟨U, m, hA, _⟩ := antipodal_diagonalization A hsym hexp
    have hsum : ∑ a, ((Real.pi * (2 * (m a : ℝ) + 1)) ^ 2 - Real.pi ^ 2) = 0 := by
      rw [Finset.sum_sub_distrib]
      rw [hA, RealMatrixSquareNorm.squareNorm_conjugate,
        RealMatrixSquareNorm.squareNorm_diagonal] at hnorm
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hnorm, sub_self]
    have hz := (Finset.sum_eq_zero_iff_of_nonneg
      (fun a (_ : a ∈ Finset.univ) ↦ sub_nonneg.mpr (odd_speed_sq_ge (m a)))).mp hsum
    rw [hA]
    apply RealMatrixSquareNorm.conjugate_diagonal_square
    intro a
    exact sub_eq_zero.mp (hz a (Finset.mem_univ a))
  · intro hsq
    rw [RealMatrixSquareNorm.squareNorm_eq_trace, hsym, hsq, Matrix.trace_smul,
      Matrix.trace_one]
    simp only [smul_eq_mul, mul_comm]

end ImaginarySymmetricMatrices

namespace BalancedRealInvolutions

theorem square_eq_pi_sq_iff_scaled_balanced (n : ℕ) (A : Matrix (Index n) (Index n) ℝ)
    (hsym : A.transpose = A) (htrace : A.trace = 0) :
    A * A = Real.pi ^ 2 • (1 : Matrix (Index n) (Index n) ℝ) ↔
      ∃ J : Space n, A = Real.pi • J.val := by
  constructor
  · intro hsq
    have hs : (Real.pi⁻¹ • A).transpose = Real.pi⁻¹ • A := by
      rw [Matrix.transpose_smul, hsym]
    have hq : (Real.pi⁻¹ • A) * (Real.pi⁻¹ • A) = 1 := by
      rw [smul_mul_smul_comm, hsq, smul_smul]
      have hc : (Real.pi⁻¹ * Real.pi⁻¹) * Real.pi ^ 2 = 1 := by
        field_simp
      rw [hc, one_smul]
    have ht : (Real.pi⁻¹ • A).trace = 0 := by
      rw [Matrix.trace_smul, htrace, smul_zero]
    refine ⟨ofRelations n (Real.pi⁻¹ • A) hs hq ht, ?_⟩
    change A = Real.pi • (Real.pi⁻¹ • A)
    rw [smul_smul, mul_inv_cancel₀ Real.pi_ne_zero, one_smul]
  · rintro ⟨J, rfl⟩
    rw [smul_mul_smul_comm, square_eq J, pow_two]

theorem antipodal_squareNorm_eq_iff_balanced (n : ℕ)
    (A : Matrix (Index n) (Index n) ℝ) (hsym : A.transpose = A) (htrace : A.trace = 0)
    (hexp : NormedSpace.exp (ImaginarySymmetricMatrices.imaginary A) = -1) :
    RealMatrixSquareNorm.squareNorm A = (2 * n : ℝ) * Real.pi ^ 2 ↔
      ∃ J : Space n, A = Real.pi • J.val := by
  have hc : (Fintype.card (Index n) : ℝ) = 2 * n := by
    simp [Index, two_mul]
  rw [← hc, ImaginarySymmetricMatrices.antipodal_squareNorm_eq_iff A hsym hexp]
  exact square_eq_pi_sq_iff_scaled_balanced n A hsym htrace

end BalancedRealInvolutions

end Wikipedia.HomotopyGroupsOfSpheres
