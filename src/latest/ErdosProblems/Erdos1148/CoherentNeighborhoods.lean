import ErdosProblems.Erdos1148.EntryNeighborhoodAlgebra
import ErdosProblems.Erdos1148.LiftForwardClose

/-! # Open quotient neighborhoods admitting coherent small lifts -/

namespace Erdos1148.DukeArithmetic

open scoped MatrixGroups

theorem exists_open_coherent_modular_neighborhood {η : ℝ} (hη : 0 < η)
    (x : ModularOrbitSpace) :
    ∃ (U : Set ModularOrbitSpace) (E : Set SL(2, ℝ)), IsOpen U ∧ x ∈ U ∧
      modularMk '' E = U ∧ LiftForwardClose η 0 E := by
  induction x using Quotient.inductionOn with
  | h g =>
    let δ := min (η / 8) (1 / 2 : ℝ)
    have hδ : 0 < δ := lt_min (by positivity) (by norm_num)
    have hδη : δ ≤ η / 8 := min_le_left _ _
    have hδone : δ ≤ 1 / 2 := min_le_right _ _
    let E : Set SL(2, ℝ) := {h | ∀ i j : Fin 2,
      |(g⁻¹ * h) i j - (1 : Matrix (Fin 2) (Fin 2) ℝ) i j| < δ}
    have hopen : IsOpen E := by
      simp only [E, Set.setOf_forall]
      apply isOpen_iInter_of_finite
      intro i
      apply isOpen_iInter_of_finite
      intro j
      exact isOpen_lt (((continuous_realMatrixEntry i j).comp
        (continuous_const.mul continuous_id)).sub continuous_const).abs continuous_const
    have hg : g ∈ E := by
      intro i j
      simpa only [inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one, sub_self, abs_zero] using hδ
    refine ⟨modularMk '' E, E, ?_, ⟨g, hg, rfl⟩, rfl, ?_⟩
    · exact (MulAction.isOpenQuotientMap_quotientMk (Γ := SL(2, ℤ))
        (T := SL(2, ℝ))).isOpenMap _ hopen
    · intro a ha b hb t ht
      have htzero : t = 0 := le_antisymm ht.2 ht.1
      subst t
      simp only [diagonalFlow_zero, mul_one]
      have ha' := (entryCloseOne_iff_entries δ (g⁻¹ * a)).mpr (fun i j => (ha i j).le)
      have hb' := (entryCloseOne_iff_entries δ (g⁻¹ * b)).mpr (fun i j => (hb i j).le)
      have hprod := entryCloseOne_mul hδ.le hδ.le (entryCloseOne_inv ha') hb'
      have heq : (g⁻¹ * a)⁻¹ * (g⁻¹ * b) = a⁻¹ * b := by group
      rw [heq] at hprod
      have hsq : 0 ≤ δ * (1 / 2 - δ) := mul_nonneg hδ.le (sub_nonneg.mpr hδone)
      exact entryCloseOne_mono hprod (by nlinarith)

end Erdos1148.DukeArithmetic
