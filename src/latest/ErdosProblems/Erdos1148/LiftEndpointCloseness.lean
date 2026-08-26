import ErdosProblems.Erdos1148.LiftForwardClose

/-! # Interpolating coherent closeness between the ends of an orbit segment -/

namespace Erdos1148.DukeArithmetic

open scoped MatrixGroups

theorem entryCloseOne_conjugate_of_endpoints {η T : ℝ} (hT : 0 ≤ T)
    {g : SL(2, ℝ)} (hzero : EntryCloseOne η g)
    (hlast : EntryCloseOne η (diagonalFlow (-T) * g * diagonalFlow T)) :
    ∀ t ∈ Set.Icc 0 T, EntryCloseOne η (diagonalFlow (-t) * g * diagonalFlow t) := by
  apply (entryForwardBowenTube_iff_flow_closeness hT g).mp
  refine ⟨hzero, ?_⟩
  have hlow := ((entryCloseOne_diagonalFlow_conjugate_iff η g T).mp hlast).2.2.1
  have hm := mul_le_mul_of_nonneg_right hlow (Real.exp_pos (-T)).le
  simpa only [mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one] using hm

theorem liftForwardClose_of_endpoints {η T : ℝ} (hT : 0 ≤ T) {E : Set SL(2, ℝ)}
    (hzero : ∀ g ∈ E, ∀ h ∈ E, EntryCloseOne η (g⁻¹ * h))
    (hlast : ∀ g ∈ E, ∀ h ∈ E,
      EntryCloseOne η ((g * diagonalFlow T)⁻¹ * (h * diagonalFlow T))) :
    LiftForwardClose η T E := by
  intro g hg h hh t ht
  have heq (s : ℝ) : (g * diagonalFlow s)⁻¹ * (h * diagonalFlow s) =
      diagonalFlow (-s) * (g⁻¹ * h) * diagonalFlow s := by
    rw [diagonalFlow_neg]
    group
  rw [heq]
  have hlast' := hlast g hg h hh
  rw [heq] at hlast'
  exact entryCloseOne_conjugate_of_endpoints hT (hzero g hg h hh) hlast' t ht

theorem entryCloseOne_conjugate_exp_bound {η t : ℝ} (ht : 0 ≤ t) {g : SL(2, ℝ)}
    (hg : EntryCloseOne η g) :
    EntryCloseOne (η * Real.exp t) (diagonalFlow (-t) * g * diagonalFlow t) := by
  have hη : 0 ≤ η := (abs_nonneg _).trans hg.1
  have hηle : η ≤ η * Real.exp t := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (Real.one_le_exp_iff.mpr ht) hη
  rw [entryCloseOne_diagonalFlow_conjugate_iff]
  refine ⟨hg.1.trans hηle, ?_, ?_, hg.2.2.2.trans hηle⟩
  · exact mul_le_mul hg.2.1 (Real.exp_le_exp.mpr (by linarith)) (Real.exp_pos _).le hη
  · exact mul_le_mul_of_nonneg_right hg.2.2.1 (Real.exp_pos _).le

end Erdos1148.DukeArithmetic
