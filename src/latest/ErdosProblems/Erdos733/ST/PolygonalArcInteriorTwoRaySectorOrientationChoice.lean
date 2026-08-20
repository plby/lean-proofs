import ErdosProblems.Erdos733.ST.PlanarRot90Decomposition
import ErdosProblems.Erdos733.ST.PlanarRot90LinearCombination
import ErdosProblems.Erdos733.ST.PlanarRot90Orthogonal

open Classical
noncomputable section

-- [TABLET NODE: PolygonalArcInteriorTwoRaySectorOrientationChoice]
lemma PolygonalArcInteriorTwoRaySectorOrientationChoice {u v : EuclideanSpace ℝ (Fin 2)}
    (hu : u ≠ 0) (hv : v ≠ 0)
    (hnot_same : ¬ ∃ t : ℝ, 0 < t ∧ v = t • u) :
    (let c : ℝ := inner ℝ v u / (‖u‖ ^ 2)
     let s : ℝ := inner ℝ v (PlanarRot90 u) / (‖u‖ ^ 2)
     v = c • u + s • PlanarRot90 u ∧ (0 < s ∨ s = 0 ∧ c < 0)) ∨
    (let c : ℝ := inner ℝ u v / (‖v‖ ^ 2)
     let s : ℝ := inner ℝ u (PlanarRot90 v) / (‖v‖ ^ 2)
     u = c • v + s • PlanarRot90 v ∧ 0 < s) := by
-- BODY
  let c : ℝ := inner ℝ v u / (‖u‖ ^ 2)
  let s : ℝ := inner ℝ v (PlanarRot90 u) / (‖u‖ ^ 2)
  have hv_rep : v = c • u + s • PlanarRot90 u := by
    simpa [c, s] using PlanarRot90Decomposition u v hu
  rcases lt_trichotomy s 0 with hsneg | hszero | hspos
  · right
    let c' : ℝ := inner ℝ u v / (‖v‖ ^ 2)
    let s' : ℝ := inner ℝ u (PlanarRot90 v) / (‖v‖ ^ 2)
    have hu_rep : u = c' • v + s' • PlanarRot90 v := by
      simpa [c', s'] using PlanarRot90Decomposition v u hv
    refine ⟨hu_rep, ?_⟩
    have hrot_v : PlanarRot90 v = (-s) • u + c • PlanarRot90 u := by
      rw [hv_rep]
      simpa using PlanarRot90LinearCombination u c s
    have hv_norm_sq_pos : 0 < ‖v‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hv)
    have hu_norm_sq_pos : 0 < ‖u‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hu)
    have hnum_pos : 0 < -(s * ‖u‖ ^ 2) := by
      nlinarith
    rw [hrot_v, inner_add_right, inner_smul_right, inner_smul_right,
      PlanarRot90Orthogonal]
    simp
    exact div_pos hnum_pos hv_norm_sq_pos
  · left
    have hc_neg : c < 0 := by
      have hv_col : v = c • u := by
        simp [hv_rep, hszero]
      have hc_not_pos : ¬ 0 < c := by
        intro hcpos
        exact hnot_same ⟨c, hcpos, hv_col⟩
      have hc_ne : c ≠ 0 := by
        intro hc0
        apply hv
        simp [hv_col, hc0]
      exact lt_of_le_of_ne (le_of_not_gt hc_not_pos) hc_ne
    exact ⟨hv_rep, Or.inr ⟨hszero, hc_neg⟩⟩
  · left
    exact ⟨hv_rep, Or.inl hspos⟩
