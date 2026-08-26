import ErdosProblems.Erdos633b.DirectionRays
import ErdosProblems.Erdos633b.CircleArcMeasure
import ErdosProblems.Erdos633b.HalfPlaneAngles
import ErdosProblems.Erdos633b.AngleParameter
import ErdosProblems.Erdos633b.BoundaryRadialInterior
import ErdosProblems.Erdos633b.IntervalTransport

/-! Circle-valued direction sectors of a triangle at one of its vertices. -/

namespace Erdos633b

local instance : Fact (Module.finrank ℝ Plane = 2) := ⟨by simp [Plane]⟩

noncomputable def closedDirections (o : Orientation ℝ Plane (Fin 2)) (u p : Plane)
    (S : Triangle) : Set Real.Angle := direction o u p '' (S.support \ {p})

noncomputable def interiorDirections (o : Orientation ℝ Plane (Fin 2)) (u p : Plane)
    (S : Triangle) : Set Real.Angle := direction o u p '' interior S.support

namespace Triangle

theorem closedDirections_vertex (S : Triangle) (o : Orientation ℝ Plane (Fin 2))
    (u : Plane) (j : Fin 3) :
    closedDirections o u (S.points j) S = direction o u (S.points j) '' S.edge j := by
  apply Set.Subset.antisymm
  · rintro a ⟨q, hq, rfl⟩
    have hne : q ≠ S.points j := hq.2
    refine ⟨S.cornerProject j q, S.cornerProject_mem_edge j hq.1 hne, ?_⟩
    exact direction_homothety o u (S.points j) q
      (inv_pos.mpr (S.cornerScale_pos j hq.1 hne))
  · rintro a ⟨q, hq, rfl⟩
    exact ⟨q, ⟨hq.1, S.ne_vertex_of_mem_edge j hq⟩, rfl⟩

theorem interiorDirections_vertex (S : Triangle) (o : Orientation ℝ Plane (Fin 2))
    (u : Plane) (j : Fin 3) :
    interiorDirections o u (S.points j) S = direction o u (S.points j) '' S.openEdge j := by
  apply Set.Subset.antisymm
  · rintro a ⟨q, hq, rfl⟩
    have hne : q ≠ S.points j := by
      intro hqj
      have hc := (S.mem_interior_support_iff_all_coords q).mp hq (j + 1)
      rw [hqj, S.coord_vertex, if_neg ((by decide : ∀ j : Fin 3, j + 1 ≠ j) j)] at hc
      exact lt_irrefl _ hc
    refine ⟨S.cornerProject j q, S.cornerProject_mem_openEdge j hq, ?_⟩
    exact direction_homothety o u (S.points j) q
      (inv_pos.mpr (S.cornerScale_pos j (interior_subset hq) hne))
  · rintro a ⟨q, hq, rfl⟩
    refine ⟨AffineMap.homothety (S.points j) (1 / 2 : ℝ) q,
      S.radial_openEdge_mem_interior j hq (by norm_num) (by norm_num), ?_⟩
    exact direction_homothety o u (S.points j) q (by norm_num)

theorem edgeAngle_image_Icc (S : Triangle) (j : Fin 3) :
    S.edgeAngle j '' Set.Icc (0 : ℝ) 1 = Set.Icc 0 (S.angle j) := by
  have h := (S.edgeAngle_continuous j).continuousOn.image_Icc_of_monotoneOn
    (show (0 : ℝ) ≤ 1 by norm_num) (S.edgeAngle_strictMonoOn j).monotoneOn
  simpa only [S.edgeAngle_zero, S.edgeAngle_one] using h

theorem edgeAngle_image_Ioo (S : Triangle) (j : Fin 3) :
    S.edgeAngle j '' Set.Ioo (0 : ℝ) 1 = Set.Ioo 0 (S.angle j) := by
  have h := (S.edgeAngle_continuous j).continuousOn.image_Ioo_of_strictMonoOn
    (show (0 : ℝ) ≤ 1 by norm_num) (S.edgeAngle_strictMonoOn j)
  simpa only [S.edgeAngle_zero, S.edgeAngle_one] using h

theorem edgeParam_orientation_sign (S : Triangle) (o : Orientation ℝ Plane (Fin 2))
    (j : Fin 3)
    (h : 0 ≤ (o.oangle (S.points (j + 1) - S.points j)
      (S.points (j + 2) - S.points j)).sign) {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ (o.oangle (S.points (j + 1) - S.points j) (S.edgeParam j t - S.points j)).sign := by
  have he : S.edgeParam j t - S.points j =
      (1 - t) • (S.points (j + 1) - S.points j) + t • (S.points (j + 2) - S.points j) := by
    rw [edgeParam, AffineMap.lineMap_apply_module]
    module
  rw [he, o.oangle_sign_smul_add_smul_right]
  rcases ht.eq_or_lt with ht | ht
  · rw [← ht, sign_zero, zero_mul]
  · rw [sign_pos ht, one_mul]
    exact h

theorem direction_edgeParam (S : Triangle) (o : Orientation ℝ Plane (Fin 2))
    {u : Plane} (hu : u ≠ 0) (j : Fin 3)
    (h : 0 ≤ (o.oangle (S.points (j + 1) - S.points j)
      (S.points (j + 2) - S.points j)).sign) {t : ℝ} (ht : 0 ≤ t) :
    direction o u (S.points j) (S.edgeParam j t) =
      direction o u (S.points j) (S.points (j + 1)) + (S.edgeAngle j t : Real.Angle) := by
  have hfirst : S.points (j + 1) - S.points j ≠ 0 := sub_ne_zero.mpr
    (S.independent.injective.ne ((by decide : ∀ j : Fin 3, j + 1 ≠ j) j))
  have hlast := sub_ne_zero.mpr (S.edgeParam_ne_vertex j t)
  have he := o.oangle_add hu hfirst hlast
  have hcoe := HalfPlaneAngles.coe_angle_eq_oangle o hfirst hlast
    (S.edgeParam_orientation_sign o j h ht)
  change (S.edgeAngle j t : Real.Angle) = _ at hcoe
  unfold direction
  rw [hcoe]
  exact he.symm

theorem direction_edgeParam_image (S : Triangle) (o : Orientation ℝ Plane (Fin 2))
    {u : Plane} (hu : u ≠ 0) (j : Fin 3)
    (h : 0 ≤ (o.oangle (S.points (j + 1) - S.points j)
      (S.points (j + 2) - S.points j)).sign)
    (K : Set ℝ) (hK : ∀ t ∈ K, 0 ≤ t) :
    direction o u (S.points j) '' (S.edgeParam j '' K) =
      (fun a => direction o u (S.points j) (S.points (j + 1)) + a) ''
        (((↑) : ℝ → Real.Angle) '' (S.edgeAngle j '' K)) := by
  simp only [Set.image_image]
  apply Set.image_congr
  intro t ht
  exact S.direction_edgeParam o hu j h (hK t ht)

theorem edge_directions_eq_arc (S : Triangle) (o : Orientation ℝ Plane (Fin 2))
    {u : Plane} (hu : u ≠ 0) (j : Fin 3)
    (h : 0 ≤ (o.oangle (S.points (j + 1) - S.points j)
      (S.points (j + 2) - S.points j)).sign) :
    direction o u (S.points j) '' S.edge j =
      (fun a => direction o u (S.points j) (S.points (j + 1)) + a) ''
        CircleArcMeasure.arc (S.angle j) := by
  have he : S.edge j = S.edgeParam j '' Set.Icc (0 : ℝ) 1 := by
    rw [S.edge_eq_segment]
    exact segment_eq_image_lineMap ℝ _ _
  rw [he, S.direction_edgeParam_image o hu j h _ (fun _ ht => ht.1), S.edgeAngle_image_Icc]
  rfl

theorem openEdge_directions_eq_arc (S : Triangle) (o : Orientation ℝ Plane (Fin 2))
    {u : Plane} (hu : u ≠ 0) (j : Fin 3)
    (h : 0 ≤ (o.oangle (S.points (j + 1) - S.points j)
      (S.points (j + 2) - S.points j)).sign) :
    direction o u (S.points j) '' S.openEdge j =
      (fun a => direction o u (S.points j) (S.points (j + 1)) + a) ''
        CircleArcMeasure.openArc (S.angle j) := by
  have he : S.openEdge j = S.edgeParam j '' Set.Ioo (0 : ℝ) 1 := by
    rw [S.openEdge_eq_openSegment]
    exact openSegment_eq_image_lineMap ℝ _ _
  rw [he, S.direction_edgeParam_image o hu j h _ (fun _ ht => ht.1.le), S.edgeAngle_image_Ioo]
  rfl

end Triangle

end Erdos633b
