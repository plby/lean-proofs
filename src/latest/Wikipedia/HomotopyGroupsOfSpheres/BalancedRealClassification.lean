import Wikipedia.HomotopyGroupsOfSpheres.BalancedSignReindex
import Wikipedia.HomotopyGroupsOfSpheres.RealPermutationMatrices
import Wikipedia.HomotopyGroupsOfSpheres.RealSymmetricInvolutionSpectrum

/-!
# The balanced orbit is exactly the trace-zero symmetric involution locus

This identifies the previously constructed compact orthogonal orbit by
intrinsic matrix equations. The proof supplies an actual orthogonal frame;
it does not require any continuous choice of frames.
-/

noncomputable section

namespace Wikipedia.HomotopyGroupsOfSpheres.BalancedRealInvolutions

open RealUnitaryMatrices

theorem orbitMatrix_mul (n : ℕ) (U V : unitary (Matrix (Index n) (Index n) ℝ)) :
    orbitMatrix n (U * V) = U.val * orbitMatrix n V * U.val.transpose := by
  change (U.val * V.val) * standardMatrix n * (U.val * V.val).transpose = _
  simp only [orbitMatrix, Matrix.transpose_mul, mul_assoc]

theorem diagonal_mem_locus (n : ℕ) (μ : Index n → ℝ)
    (hμ : ∀ a, μ a = 1 ∨ μ a = -1) (hsum : ∑ a, μ a = 0) :
    Matrix.diagonal μ ∈ locus n := by
  obtain ⟨e, he⟩ := exists_sign_reindex n μ hμ hsum
  let P := permutationUnitary e
  have hd : P.val * Matrix.diagonal μ * P.val.transpose = standardMatrix n := by
    calc
      P.val * Matrix.diagonal μ * P.val.transpose = Matrix.diagonal (μ ∘ e) :=
        permutation_conjugation_diagonal e μ
      _ = standardMatrix n := congrArg Matrix.diagonal (funext he)
  have hP : (P⁻¹).val * P.val = 1 := congrArg Subtype.val (inv_mul_cancel P)
  have hPt : P.val.transpose * (P⁻¹).val.transpose = 1 := by
    rw [← Matrix.transpose_mul, hP, Matrix.transpose_one]
  refine ⟨P⁻¹, ?_⟩
  rw [orbitMatrix, ← hd]
  calc
    (P⁻¹).val * (P.val * Matrix.diagonal μ * P.val.transpose) * (P⁻¹).val.transpose =
        ((P⁻¹).val * P.val) * Matrix.diagonal μ * (P.val.transpose * (P⁻¹).val.transpose) := by
      simp only [mul_assoc]
    _ = Matrix.diagonal μ := by rw [hP, hPt, one_mul, mul_one]

theorem mem_locus_of_relations (n : ℕ) (A : Matrix (Index n) (Index n) ℝ)
    (hsym : A.transpose = A) (hsq : A * A = 1) (htrace : A.trace = 0) : A ∈ locus n := by
  obtain ⟨U, μ, hμ, hA, htr⟩ := symmetric_involution_diagonalization A hsym hsq
  have hsum : ∑ a, μ a = 0 := htr.symm.trans htrace
  obtain ⟨V, hV⟩ := diagonal_mem_locus n μ hμ hsum
  refine ⟨U * V, ?_⟩
  rw [orbitMatrix_mul, hV]
  exact hA.symm

theorem mem_locus_iff (n : ℕ) (A : Matrix (Index n) (Index n) ℝ) :
    A ∈ locus n ↔ A.transpose = A ∧ A * A = 1 ∧ A.trace = 0 := by
  constructor
  · intro hA
    exact ⟨transpose_eq ⟨A, hA⟩, square_eq ⟨A, hA⟩, trace_eq_zero ⟨A, hA⟩⟩
  · rintro ⟨hsym, hsq, htrace⟩
    exact mem_locus_of_relations n A hsym hsq htrace

def ofRelations (n : ℕ) (A : Matrix (Index n) (Index n) ℝ)
    (hsym : A.transpose = A) (hsq : A * A = 1) (htrace : A.trace = 0) : Space n :=
  ⟨A, mem_locus_of_relations n A hsym hsq htrace⟩

end Wikipedia.HomotopyGroupsOfSpheres.BalancedRealInvolutions
