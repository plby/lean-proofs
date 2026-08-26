import ErdosProblems.Erdos633b.VertexDirectionSectors

/-! Compactness, null boundary, and angle measure of a genuine vertex sector,
with no restriction on the orientation of the triangle. -/

namespace Erdos633b

local instance : Fact (Module.finrank ℝ Plane = 2) := ⟨by simp [Plane]⟩

theorem direction_image_reverse (o : Orientation ℝ Plane (Fin 2)) (u p : Plane)
    (K : Set Plane) : direction o u p '' K =
      (fun a : Real.Angle => -a) '' (direction (-o) u p '' K) := by
  rw [Set.image_image]
  apply Set.image_congr
  intro q _
  simp only [direction, Orientation.oangle_neg_orientation_eq_neg, neg_neg]

theorem closedDirections_reverse (o : Orientation ℝ Plane (Fin 2)) (u p : Plane)
    (S : Triangle) : closedDirections o u p S =
      (fun a : Real.Angle => -a) '' closedDirections (-o) u p S :=
  direction_image_reverse o u p _

theorem interiorDirections_reverse (o : Orientation ℝ Plane (Fin 2)) (u p : Plane)
    (S : Triangle) : interiorDirections o u p S =
      (fun a : Real.Angle => -a) '' interiorDirections (-o) u p S :=
  direction_image_reverse o u p _

namespace Triangle

theorem vertex_sector_properties_of_sign (S : Triangle)
    (o : Orientation ℝ Plane (Fin 2)) {u : Plane} (hu : u ≠ 0) (j : Fin 3)
    (h : 0 ≤ (o.oangle (S.points (j + 1) - S.points j)
      (S.points (j + 2) - S.points j)).sign) :
    IsCompact (closedDirections o u (S.points j) S) ∧
    (closedDirections o u (S.points j) S \ interiorDirections o u (S.points j) S).Finite ∧
    CircleArcMeasure.measure (closedDirections o u (S.points j) S) =
      ENNReal.ofReal (S.angle j) := by
  rw [S.closedDirections_vertex, S.interiorDirections_vertex,
    S.edge_directions_eq_arc o hu j h, S.openEdge_directions_eq_arc o hu j h]
  have hcont : Continuous (fun a : Real.Angle =>
      direction o u (S.points j) (S.points (j + 1)) + a) := by
    fun_prop
  refine ⟨(CircleArcMeasure.arc_isCompact _).image hcont, ?_, ?_⟩
  · rw [← Set.image_sdiff (add_right_injective _)]
    exact ((Set.toFinite _).subset (CircleArcMeasure.arc_sdiff_openArc_subset _)).image _
  · rw [CircleArcMeasure.measure_translate,
      CircleArcMeasure.measure_arc _ (S.angle_pos j).le (S.angle_lt_pi j).le]

theorem vertex_sector_properties (S : Triangle) (o : Orientation ℝ Plane (Fin 2))
    {u : Plane} (hu : u ≠ 0) (j : Fin 3) :
    IsCompact (closedDirections o u (S.points j) S) ∧
    (closedDirections o u (S.points j) S \ interiorDirections o u (S.points j) S).Finite ∧
    CircleArcMeasure.measure (closedDirections o u (S.points j) S) =
      ENNReal.ofReal (S.angle j) := by
  by_cases h : 0 ≤ (o.oangle (S.points (j + 1) - S.points j)
      (S.points (j + 2) - S.points j)).sign
  · exact S.vertex_sector_properties_of_sign o hu j h
  · have hn : 0 ≤ ((-o).oangle (S.points (j + 1) - S.points j)
        (S.points (j + 2) - S.points j)).sign := by
      rw [Orientation.oangle_neg_orientation_eq_neg, Real.Angle.sign_neg]
      exact (by decide : ∀ s : SignType, ¬0 ≤ s → 0 ≤ -s) _ h
    obtain ⟨hcompact, hfinite, hmeasure⟩ := S.vertex_sector_properties_of_sign (-o) hu j hn
    rw [closedDirections_reverse o u _ S, interiorDirections_reverse o u _ S,
      ← Set.image_sdiff neg_injective]
    refine ⟨hcompact.image continuous_neg, hfinite.image _, ?_⟩
    rw [CircleArcMeasure.measure_reverse, hmeasure]

end Triangle
end Erdos633b
