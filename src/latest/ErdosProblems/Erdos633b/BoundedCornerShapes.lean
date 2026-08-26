import ErdosProblems.Erdos633b.IncommensurableShapes

/-! The actual corner-pattern exhaustion needs only bounded positive
columns, and applies equally to rational and irrational angle regimes. -/

namespace Erdos633b.Tiling

theorem actual_corner_pairs_of_bounded_columns {T : Triangle} {n : ℕ} (d : Tiling T n)
    (h2 : d.cornerColumnCount 2 = 0)
    (hP : 0 < d.cornerColumnCount 0) (hPb : d.cornerColumnCount 0 ≤ 3)
    (hQ : 0 < d.cornerColumnCount 1) (hQb : d.cornerColumnCount 1 ≤ 3)
    (hscalene : Function.Injective T.angle) :
    ∃ e : Equiv.Perm (Fin 3),
      ((d.cornerAngleCount (e 0) 0, d.cornerAngleCount (e 0) 1),
       (d.cornerAngleCount (e 1) 0, d.cornerAngleCount (e 1) 1),
       (d.cornerAngleCount (e 2) 0, d.cornerAngleCount (e 2) 1)) ∈ cornerPairPatterns := by
  obtain ⟨e, he01, he12⟩ := three_corner_pairs_ordered
    (fun i => d.cornerAngleCount i 0) (fun i => d.cornerAngleCount i 1)
    (fun i => (d.corner_count_le_column i 1).trans hQb) (d.corner_pair_injective h2 hscalene)
  refine ⟨e, sorted_corner_pairs_exhaustive _ _ _ _ _ _
    (d.corner_pair_nonzero h2 (e 0)) (d.corner_pair_nonzero h2 (e 1))
    (d.corner_pair_nonzero h2 (e 2)) he01 he12 ?_ ?_ ?_ ?_⟩
  · rw [d.corner_column_reorder]
    exact hP
  · rw [d.corner_column_reorder]
    exact hPb
  · rw [d.corner_column_reorder]
    exact hQ
  · rw [d.corner_column_reorder]
    exact hQb

theorem angle_shapes_of_bounded_columns {T : Triangle} {n : ℕ} (d : Tiling T n)
    (h2 : d.cornerColumnCount 2 = 0)
    (hP : 0 < d.cornerColumnCount 0) (hPb : d.cornerColumnCount 0 ≤ 3)
    (hQ : 0 < d.cornerColumnCount 1) (hQb : d.cornerColumnCount 1 ≤ 3)
    (hscalene : Function.Injective T.angle) :
    ReptilingAngles d.tile T ∨ SixAngleShapes d.tile T := by
  obtain ⟨e, he⟩ := d.actual_corner_pairs_of_bounded_columns h2 hP hPb hQ hQb hscalene
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

end Erdos633b.Tiling
