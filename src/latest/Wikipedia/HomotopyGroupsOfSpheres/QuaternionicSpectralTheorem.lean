import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicSpectralSplitting

/-!
# Finite-dimensional quaternionic skew-adjoint spectral theorem

Inductively complete actual quaternionic unit eigenvectors to unitary frames.
The resulting diagonal entries are nonnegative real multiples of the fixed
imaginary quaternion `i`. No continuously chosen diagonalization is asserted.
-/

noncomputable section

open scoped Matrix

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns

local notation "ℍ" => Quaternion ℝ

variable {n : ℕ}

theorem splitMatrix_mul (q r : ℍ) (B C : Matrix (Fin n) (Fin n) ℍ) :
    splitMatrix q B * splitMatrix r C = splitMatrix (q * r) (B * C) := by
  apply Matrix.ext
  intro i j
  cases i using Fin.cases <;> cases j using Fin.cases <;>
    simp [splitMatrix, Matrix.mul_apply, Fin.sum_univ_succ]

theorem star_splitMatrix (q : ℍ) (B : Matrix (Fin n) (Fin n) ℍ) :
    star (splitMatrix q B) = splitMatrix (star q) (star B) := by
  apply Matrix.ext
  intro i j
  cases i using Fin.cases <;> cases j using Fin.cases <;>
    simp [splitMatrix, Matrix.star_apply]

theorem splitMatrix_diagonal (q : ℍ) (d : Fin n → ℍ) :
    splitMatrix q (Matrix.diagonal d) = Matrix.diagonal (Fin.cons q d) := by
  apply Matrix.ext
  intro i j
  cases i using Fin.cases <;> cases j using Fin.cases <;>
    simp [splitMatrix, Matrix.diagonal_apply, eq_comm]

theorem conjugateMatrix_mul {N : Type*} [Fintype N] [DecidableEq N]
    (U V : SpGroup N) (A : Matrix N N ℍ) :
    conjugateMatrix (U * V) A = conjugateMatrix V (conjugateMatrix U A) := by
  simp only [conjugateMatrix, Submonoid.coe_mul, star_mul, mul_assoc]

theorem conjugateMatrix_stabilization (V : SpGroup (Fin n)) (q : ℍ)
    (B : Matrix (Fin n) (Fin n) ℍ) :
    conjugateMatrix (stabilization n V) (splitMatrix q B) =
      splitMatrix q (conjugateMatrix V B) := by
  change star (splitMatrix 1 V.val) * splitMatrix q B * splitMatrix 1 V.val =
    splitMatrix q (star V.val * B * V.val)
  rw [star_splitMatrix, splitMatrix_mul, splitMatrix_mul, star_one, one_mul, mul_one]

/-- The actual unitary diagonalization of every quaternionic skew-adjoint matrix. -/
theorem exists_unitary_diagonalization (n : ℕ) (A : Matrix (Fin n) (Fin n) ℍ)
    (hA : star A = -A) :
    ∃ (U : SpGroup (Fin n)) (α : Fin n → ℝ),
      (∀ a, 0 ≤ α a) ∧
        conjugateMatrix U A = Matrix.diagonal (fun a => α a • QuaternionicScalars.i) := by
  induction n with
  | zero =>
    refine ⟨1, Fin.elim0, (fun a => Fin.elim0 a), ?_⟩
    apply Matrix.ext
    intro i
    exact Fin.elim0 i
  | succ n ih =>
    obtain ⟨α, U, B, hα, hB, hU⟩ := exists_spectral_split n A hA
    obtain ⟨V, β, hβ, hV⟩ := ih B hB
    refine ⟨U * stabilization n V, Fin.cons α β, ?_, ?_⟩
    · intro a
      cases a using Fin.cases
      · exact hα
      · exact hβ _
    · rw [conjugateMatrix_mul, hU, conjugateMatrix_stabilization, hV, splitMatrix_diagonal]
      congr 1
      funext a
      cases a using Fin.cases <;> rfl

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns
