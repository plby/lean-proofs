import ErdosProblems.Erdos633b.CornerPatternShapes
import ErdosProblems.Erdos633b.CornerPairOrdering
import ErdosProblems.Erdos633b.CornerReindex

/-! Exhaustive angle classification of actual tilings of scalene triangles
with incommensurable angles. No side-rationality hypothesis is used. -/

namespace Erdos633b.Tiling

theorem angle_shapes_of_missing_last_column {T : Triangle} {n : ℕ} (d : Tiling T n)
    (h2 : d.cornerColumnCount 2 = 0)
    (hirr : ¬ ∀ i, IsRational (T.angle i / Real.pi))
    (hscalene : Function.Injective T.angle) :
    ReptilingAngles d.tile T ∨ SixAngleShapes d.tile T := by
  obtain ⟨e, he⟩ := d.actual_corner_pairs_exhaustive h2 hirr hscalene
  have hrow (i : Fin 3) : Triangle.angle (T.reindex e.symm) i =
      (d.cornerAngleCount (e i) 0 : ℝ) * d.tile.angle 0 +
      (d.cornerAngleCount (e i) 1 : ℝ) * d.tile.angle 1 := by
    simpa only [Triangle.angle_reindex, Equiv.symm_symm] using d.corner_two_angle_row h2 (e i)
  have h := angle_shapes_of_corner_pattern d.tile (T.reindex e.symm)
    (d.cornerAngleCount (e 0) 0, d.cornerAngleCount (e 0) 1)
    (d.cornerAngleCount (e 1) 0, d.cornerAngleCount (e 1) 1)
    (d.cornerAngleCount (e 2) 0, d.cornerAngleCount (e 2) 1)
    he (hrow 0) (hrow 1) (hrow 2)
  exact h.imp (reptilingAngles_of_reindex_outer d.tile T e.symm)
    (sixAngleShapes_of_reindex_outer d.tile T e.symm)

theorem incommensurable_scalene_angle_classification {T : Triangle} {n : ℕ} (d : Tiling T n)
    (hirr : ¬ ∀ i, IsRational (T.angle i / Real.pi))
    (hscalene : Function.Injective T.angle) :
    ReptilingAngles d.tile T ∨ SixAngleShapes d.tile T := by
  by_cases hrep : ReptilingAngles d.tile T
  · exact Or.inl hrep
  · obtain ⟨e, he⟩ := d.exists_reindex_zero_last_corner_column hrep
    have h := (d.reindexTile e).angle_shapes_of_missing_last_column he hirr hscalene
    change ReptilingAngles (d.tile.reindex e) T ∨ SixAngleShapes (d.tile.reindex e) T at h
    exact h.imp (reptilingAngles_of_reindex_tile d.tile T e)
      (sixAngleShapes_of_reindex_tile d.tile T e)

theorem incommensurable_nonreptiling_six_shapes {T : Triangle} {n : ℕ} (d : Tiling T n)
    (hirr : ¬ ∀ i, IsRational (T.angle i / Real.pi))
    (hscalene : Function.Injective T.angle) (hrep : ¬ ReptilingAngles d.tile T) :
    SixAngleShapes d.tile T :=
  (d.incommensurable_scalene_angle_classification hirr hscalene).resolve_left hrep

end Erdos633b.Tiling
