import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicJointSpectralSplitting

/-!
# Simultaneous quaternionic diagonalization with a fixed anticommuting structure

A skew generator and an anticommuting complex structure have one unitary
frame in which the generator is diagonal with nonnegative multiples of `i`,
and the complex structure is diagonal with entries `j`.
-/

noncomputable section

open scoped Matrix

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns

local notation "ℍ" => Quaternion ℝ

theorem exists_joint_unitary_diagonalization (n : ℕ) (A J : Matrix (Fin n) (Fin n) ℍ)
    (hA : star A = -A) (hJ : star J = -J) (hs : J * J = -1) (hJA : J * A = -(A * J)) :
    ∃ (U : SpGroup (Fin n)) (α : Fin n → ℝ), (∀ a, 0 ≤ α a) ∧
      conjugateMatrix U A = Matrix.diagonal (fun a ↦ α a • QuaternionicScalars.i) ∧
      conjugateMatrix U J = Matrix.diagonal (fun _ ↦ QuaternionicScalars.j) := by
  induction n with
  | zero =>
    refine ⟨1, Fin.elim0, (fun a ↦ Fin.elim0 a), ?_, ?_⟩ <;>
      apply Matrix.ext <;> intro i <;> exact Fin.elim0 i
  | succ n ih =>
    obtain ⟨α, U, B, C, hα, hB, hC, hCs, hCB, hU, hUJ⟩ :=
      exists_joint_spectral_split n A J hA hJ hs hJA
    obtain ⟨V, β, hβ, hV, hVJ⟩ := ih B C hB hC hCs hCB
    refine ⟨U * stabilization n V, Fin.cons α β, ?_, ?_, ?_⟩
    · intro a
      cases a using Fin.cases
      · exact hα
      · exact hβ _
    · rw [conjugateMatrix_mul, hU, conjugateMatrix_stabilization, hV, splitMatrix_diagonal]
      congr 1
      funext a
      cases a using Fin.cases <;> rfl
    · rw [conjugateMatrix_mul, hUJ, conjugateMatrix_stabilization, hVJ, splitMatrix_diagonal]
      congr 1
      funext a
      cases a using Fin.cases <;> rfl

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns
