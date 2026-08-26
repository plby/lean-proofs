import ErdosProblems.Erdos633b.VertexSectorMeasure
import ErdosProblems.Erdos633b.BoundaryAngleRange

/-! At an open-side point a triangle occupies a semicircle of directions.
Only its two boundary rays can fail to meet the triangle interior. -/

namespace Erdos633b.Triangle

local instance : Fact (Module.finrank ℝ Plane = 2) := ⟨by simp [Plane]⟩

theorem direction_boundaryAngle (S : Triangle) {u p q : Plane} (hu : u ≠ 0)
    (i : Fin 3) (hp : p ∈ S.openEdge i) (hq : q ∈ S.support) (hqp : q ≠ p) :
    direction (S.boundaryOrientation i p) u p q =
      direction (S.boundaryOrientation i p) u p (S.points (i + 1)) +
        (S.boundaryAngle i p q : Real.Angle) := by
  have hfirst := S.boundary_ray_ne_zero i hp (i + 1)
  have hlast := sub_ne_zero.mpr hqp
  have he := (S.boundaryOrientation i p).oangle_add hu hfirst hlast
  have hc := HalfPlaneAngles.coe_angle_eq_oangle (S.boundaryOrientation i p) hfirst hlast
    (S.boundary_point_sign i hp hq)
  change (S.boundaryAngle i p q : Real.Angle) = _ at hc
  unfold direction
  rw [hc]
  exact he.symm

theorem closedDirections_openEdge_arc (S : Triangle) {u p : Plane} (hu : u ≠ 0)
    (i : Fin 3) (hp : p ∈ S.openEdge i) :
    closedDirections (S.boundaryOrientation i p) u p S =
      (fun a => direction (S.boundaryOrientation i p) u p (S.points (i + 1)) + a) ''
        CircleArcMeasure.arc Real.pi := by
  apply Set.Subset.antisymm
  · rintro a ⟨q, hq, rfl⟩
    exact ⟨(S.boundaryAngle i p q : Real.Angle),
      ⟨S.boundaryAngle i p q, ⟨S.boundaryAngle_nonneg i p q, S.boundaryAngle_le_pi i p q⟩, rfl⟩,
      (S.direction_boundaryAngle hu i hp hq.1 hq.2).symm⟩
  · rintro a ⟨b, ⟨t, ht, rfl⟩, rfl⟩
    obtain ⟨q, hq, hqp, hqt⟩ := S.boundaryAngle_surjective i hp ht
    refine ⟨q, ⟨hq, hqp⟩, ?_⟩
    rw [S.direction_boundaryAngle hu i hp hq hqp, hqt]

theorem radial_openEdge_point_mem_interior (S : Triangle) (i : Fin 3) {p q : Plane}
    (hp : p ∈ S.openEdge i) (hq : q ∈ S.support) (hqi : 0 < S.coord i q) :
    AffineMap.homothety p (1 / 2 : ℝ) q ∈ interior S.support := by
  apply (S.mem_interior_support_iff_all_coords _).mpr
  intro j
  rw [AffineMap.homothety_eq_lineMap, S.coord_lineMap]
  by_cases hj : j = i
  · rw [hj, hp.1]
    linarith
  · have hpj := hp.2 j hj
    have hqj := S.coord_nonneg hq j
    linarith

theorem closedDirections_openEdge_sdiff_subset (S : Triangle)
    (o : Orientation ℝ Plane (Fin 2)) (u : Plane) (i : Fin 3) {p : Plane}
    (hp : p ∈ S.openEdge i) :
    closedDirections o u p S \ interiorDirections o u p S ⊆
      ({direction o u p (S.points (i + 1)),
        o.oangle u (-(S.points (i + 1) - p))} : Set Real.Angle) := by
  rintro a ⟨⟨q, hq, rfl⟩, hn⟩
  have hqi : S.coord i q = 0 := by
    by_contra hne
    have hpos := lt_of_le_of_ne (S.coord_nonneg hq.1 i) (Ne.symm hne)
    exact hn ⟨AffineMap.homothety p (1 / 2 : ℝ) q,
      S.radial_openEdge_point_mem_interior i hp hq.1 hpos,
      direction_homothety o u p q (by norm_num)⟩
  let r := S.coord (i + 1) q - S.coord (i + 2) q *
    (S.coord (i + 1) p / S.coord (i + 2) p)
  have he : q - p = r • (S.points (i + 1) - p) := by
    rw [S.boundary_relative_coordinates i hp q, hqi, zero_smul, add_zero]
  have hr : r ≠ 0 := by
    intro hr
    rw [hr, zero_smul] at he
    exact hq.2 (sub_eq_zero.mp he)
  rcases lt_or_gt_of_ne hr with hr | hr
  · have hh : direction o u p q = o.oangle u (-(S.points (i + 1) - p)) := by
      unfold direction
      rw [he]
      exact o.oangle_smul_right_of_neg _ _ hr
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    exact Or.inr hh
  · have hh : direction o u p q = direction o u p (S.points (i + 1)) := by
      unfold direction
      rw [he]
      exact o.oangle_smul_right_of_pos _ _ hr
    exact Or.inl hh

theorem openEdge_sector_properties (S : Triangle) (o : Orientation ℝ Plane (Fin 2))
    {u p : Plane} (hu : u ≠ 0) (i : Fin 3) (hp : p ∈ S.openEdge i) :
    IsCompact (closedDirections o u p S) ∧
    (closedDirections o u p S \ interiorDirections o u p S).Finite ∧
    CircleArcMeasure.measure (closedDirections o u p S) = ENNReal.ofReal Real.pi := by
  have hfinite := (Set.toFinite _).subset (S.closedDirections_openEdge_sdiff_subset o u i hp)
  have hbase : IsCompact (closedDirections (S.boundaryOrientation i p) u p S) ∧
      CircleArcMeasure.measure (closedDirections (S.boundaryOrientation i p) u p S) =
        ENNReal.ofReal Real.pi := by
    rw [S.closedDirections_openEdge_arc hu i hp]
    have hcont : Continuous (fun a : Real.Angle =>
        direction (S.boundaryOrientation i p) u p (S.points (i + 1)) + a) := by
      fun_prop
    refine ⟨(CircleArcMeasure.arc_isCompact _).image hcont, ?_⟩
    rw [CircleArcMeasure.measure_translate,
      CircleArcMeasure.measure_arc _ Real.pi_pos.le le_rfl]
  rcases o.eq_or_eq_neg (S.boundaryOrientation i p) (by simp [Plane]) with he | he
  · subst o
    exact ⟨hbase.1, hfinite, hbase.2⟩
  · refine ⟨?_, hfinite, ?_⟩
    · rw [he, closedDirections_reverse (-S.boundaryOrientation i p) u p S, neg_neg]
      exact hbase.1.image continuous_neg
    · rw [he, closedDirections_reverse (-S.boundaryOrientation i p) u p S, neg_neg,
        CircleArcMeasure.measure_reverse, hbase.2]

end Erdos633b.Triangle
