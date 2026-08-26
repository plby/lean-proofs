import ErdosProblems.Erdos1148.EntryDifferenceCloseness
import ErdosProblems.Erdos1148.FrameBoxCloseness

/-! # Products, inverses, and bounded conjugation of entry neighborhoods -/

namespace Erdos1148.DukeArithmetic

open scoped MatrixGroups

theorem entryCloseOne_inv {η : ℝ} {g : SL(2, ℝ)} (hg : EntryCloseOne η g) :
    EntryCloseOne η g⁻¹ := by
  have hm := Matrix.SpecialLinearGroup.coe_inv g
  unfold EntryCloseOne at hg ⊢
  rw [hm, Matrix.adjugate_fin_two]
  simpa only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, abs_neg] using
    And.intro hg.2.2.2 ⟨hg.2.1, hg.2.2.1, hg.1⟩

theorem entryCloseOne_mul {η δ : ℝ} (hη : 0 ≤ η) (hδ : 0 ≤ δ)
    {g h : SL(2, ℝ)} (hg : EntryCloseOne η g) (hh : EntryCloseOne δ h) :
    EntryCloseOne (η + δ + 2 * η * δ) (g * h) := by
  let A : Matrix (Fin 2) (Fin 2) ℝ := g
  let B : Matrix (Fin 2) (Fin 2) ℝ := h
  have hA : ∀ i j, |(A - 1) i j| ≤ η := (entryCloseOne_iff_entries η g).mp hg
  have hB : ∀ i j, |(B - 1) i j| ≤ δ := (entryCloseOne_iff_entries δ h).mp hh
  have hprod := matrix_two_mul_entry_bound (A - 1) (B - 1) hη hδ hA hB
  have heq : A * B - 1 = (A - 1) + (B - 1) + (A - 1) * (B - 1) := by
    noncomm_ring
  apply (entryCloseOne_iff_entries _ _).mpr
  intro i j
  change |((g * h : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) i j -
    (1 : Matrix (Fin 2) (Fin 2) ℝ) i j| ≤ _
  rw [Matrix.SpecialLinearGroup.coe_mul]
  change |(A * B - 1) i j| ≤ _
  rw [heq, Matrix.add_apply, Matrix.add_apply]
  exact (abs_add_le _ _).trans
    (add_le_add ((abs_add_le _ _).trans (add_le_add (hA i j) (hB i j))) (hprod i j))

theorem entryCloseOne_conjugate {A η : ℝ} (hA : 0 ≤ A) (hη : 0 ≤ η)
    (g : SL(2, ℝ)) (hg : ∀ i j : Fin 2, |g i j| ≤ A)
    {h : SL(2, ℝ)} (hh : EntryCloseOne η h) :
    EntryCloseOne (4 * A ^ 2 * η) (g * h * g⁻¹) := by
  let G : Matrix (Fin 2) (Fin 2) ℝ := g
  let B : Matrix (Fin 2) (Fin 2) ℝ := (g⁻¹ : SL(2, ℝ))
  let M : Matrix (Fin 2) (Fin 2) ℝ := h
  have hB : ∀ i j, |B i j| ≤ A := inverse_entries_bound g hg
  have hM : ∀ i j, |(M - 1) i j| ≤ η := (entryCloseOne_iff_entries η h).mp hh
  have hGM := matrix_two_mul_entry_bound G (M - 1) hA hη hg hM
  have hGMB := matrix_two_mul_entry_bound (G * (M - 1)) B (by positivity) hA hGM hB
  have hGB : G * B = 1 := by
    change (g : Matrix (Fin 2) (Fin 2) ℝ) *
      ((g⁻¹ : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) = 1
    rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
  have heq : G * M * B - 1 = G * (M - 1) * B := by rw [mul_sub, mul_one, sub_mul, hGB]
  apply (entryCloseOne_iff_entries _ _).mpr
  intro i j
  change |(((g * h * g⁻¹ : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) - 1) i j| ≤ _
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  change |(G * M * B - 1) i j| ≤ _
  rw [heq]
  convert hGMB i j using 1 <;> ring

end Erdos1148.DukeArithmetic
