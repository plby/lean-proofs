import ErdosProblems.Erdos1148.RotationFrames

/-! # Entry bounds under changes of angular frame -/

namespace Erdos1148.DukeArithmetic

open scoped MatrixGroups

lemma entryCloseOne_iff_entries (η : ℝ) (g : SL(2, ℝ)) :
    EntryCloseOne η g ↔ ∀ i j : Fin 2, |g i j - (1 : Matrix (Fin 2) (Fin 2) ℝ) i j| ≤ η := by
  simp [Fin.forall_fin_two, EntryCloseOne, Matrix.one_apply, and_assoc]

lemma matrix_two_mul_entry_bound (A B : Matrix (Fin 2) (Fin 2) ℝ) {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hA : ∀ i j, |A i j| ≤ a) (hB : ∀ i j, |B i j| ≤ b)
    (i j : Fin 2) : |(A * B) i j| ≤ 2 * a * b := by
  rw [Matrix.mul_apply, Fin.sum_univ_two]
  apply (abs_add_le _ _).trans
  have h0 : |A i 0 * B 0 j| ≤ a * b := by
    rw [abs_mul]
    exact mul_le_mul (hA i 0) (hB 0 j) (abs_nonneg _) ha
  have h1 : |A i 1 * B 1 j| ≤ a * b := by
    rw [abs_mul]
    exact mul_le_mul (hA i 1) (hB 1 j) (abs_nonneg _) ha
  linarith

lemma rotationFrame_abs_entries_le_one (θ : ℝ) (i j : Fin 2) : |rotationFrame θ i j| ≤ 1 := by
  fin_cases i <;> fin_cases j <;>
    simp [rotationFrame, Real.abs_cos_le_one, Real.abs_sin_le_one]

theorem entryCloseOne_rotation_change {η : ℝ} {g : SL(2, ℝ)} (hη : 0 ≤ η)
    (hg : EntryCloseOne η g) (θ φ : ℝ) :
    EntryCloseOne (4 * η + |φ - θ|) ((rotationFrame θ)⁻¹ * g * rotationFrame φ) := by
  let A : Matrix (Fin 2) (Fin 2) ℝ := ((rotationFrame θ)⁻¹ : SL(2, ℝ))
  let B : Matrix (Fin 2) (Fin 2) ℝ := rotationFrame φ
  let M : Matrix (Fin 2) (Fin 2) ℝ := g
  have hA : ∀ i j, |A i j| ≤ 1 := by
    intro i j
    dsimp only [A]
    rw [rotationFrame_inv]
    exact rotationFrame_abs_entries_le_one _ _ _
  have hB : ∀ i j, |B i j| ≤ 1 := rotationFrame_abs_entries_le_one φ
  have hM : ∀ i j, |(M - 1) i j| ≤ η := (entryCloseOne_iff_entries η g).mp hg
  have hAM : ∀ i j, |(A * (M - 1)) i j| ≤ 2 * η := by
    intro i j
    simpa only [mul_one] using matrix_two_mul_entry_bound A (M - 1) zero_le_one hη hA hM i j
  have hAMB : ∀ i j, |(A * (M - 1) * B) i j| ≤ 4 * η := by
    intro i j
    have h := matrix_two_mul_entry_bound (A * (M - 1)) B (by positivity) zero_le_one hAM hB i j
    convert h using 1 <;> ring
  have hAB : ∀ i j, |(A * B - 1) i j| ≤ |φ - θ| := by
    have h := (entryCloseOne_iff_entries _ _).mp (rotationFrame_relative_close θ φ)
    intro i j
    have heq : A * B = (((rotationFrame θ)⁻¹ * rotationFrame φ : SL(2, ℝ)) :
        Matrix (Fin 2) (Fin 2) ℝ) := (Matrix.SpecialLinearGroup.coe_mul _ _).symm
    rw [heq]
    exact h i j
  apply (entryCloseOne_iff_entries _ _).mpr
  intro i j
  change |(((rotationFrame θ)⁻¹ * g * rotationFrame φ : SL(2, ℝ)) :
    Matrix (Fin 2) (Fin 2) ℝ) i j - (1 : Matrix (Fin 2) (Fin 2) ℝ) i j| ≤ _
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  change |(A * M * B - 1) i j| ≤ _
  have heq : A * M * B - 1 = A * (M - 1) * B + (A * B - 1) := by noncomm_ring
  rw [heq, Matrix.add_apply]
  exact (abs_add_le _ _).trans (add_le_add (hAMB i j) (hAB i j))

end Erdos1148.DukeArithmetic
