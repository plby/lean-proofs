import ErdosProblems.Erdos633b.CornerSection
import Mathlib.Geometry.Euclidean.Angle.Unoriented.TriangleInequality
import Mathlib.Topology.Order.IntermediateValue

open scoped NNReal

/-! The angle from the first outer ray is a continuous, strictly increasing
coordinate along the side opposite the corner. -/

namespace Erdos633b.Triangle

noncomputable def edgeParam (T : Triangle) (i : Fin 3) : ℝ →ᵃ[ℝ] Plane :=
  AffineMap.lineMap (T.points (i + 1)) (T.points (i + 2))

noncomputable def edgeAngle (T : Triangle) (i : Fin 3) (t : ℝ) : ℝ :=
  EuclideanGeometry.angle (T.points (i + 1)) (T.points i) (T.edgeParam i t)

theorem edgeParam_coord_self (T : Triangle) (i : Fin 3) (t : ℝ) :
    T.coord i (T.edgeParam i t) = 0 := by
  rw [edgeParam, T.coord_lineMap, T.coord_vertex, T.coord_vertex,
    if_neg (Ne.symm ((by decide : ∀ i : Fin 3, i + 1 ≠ i) i)),
    if_neg (Ne.symm ((by decide : ∀ i : Fin 3, i + 2 ≠ i) i))]
  ring

theorem edgeParam_ne_vertex (T : Triangle) (i : Fin 3) (t : ℝ) :
    T.edgeParam i t ≠ T.points i := by
  intro he
  have h := T.edgeParam_coord_self i t
  rw [he, T.coord_vertex, if_pos rfl] at h
  norm_num at h

theorem edgeParam_injective (T : Triangle) (i : Fin 3) : Function.Injective (T.edgeParam i) :=
  AffineMap.lineMap_injective ℝ (T.independent.injective.ne
    ((by decide : ∀ i : Fin 3, i + 1 ≠ i + 2) i))

theorem edgeParam_mem_edge (T : Triangle) (i : Fin 3) {t : ℝ} (ht : t ∈ Set.Icc 0 1) :
    T.edgeParam i t ∈ T.edge i := by
  rw [T.edge_eq_segment]
  exact lineMap_mem_segment ℝ _ _ ht

theorem edgeAngle_continuous (T : Triangle) (i : Fin 3) : Continuous (T.edgeAngle i) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  have hP : T.points (i + 1) ≠ T.points i := T.independent.injective.ne
    ((by decide : ∀ i : Fin 3, i + 1 ≠ i) i)
  have ha := EuclideanGeometry.continuousAt_angle (V := Plane)
    (x := (T.points (i + 1), T.points i, T.edgeParam i t)) hP (T.edgeParam_ne_vertex i t)
  have hg : Continuous (fun r : ℝ => (T.points (i + 1), T.points i, T.edgeParam i r)) :=
    continuous_const.prodMk
      (continuous_const.prodMk (T.edgeParam i).continuous_of_finiteDimensional)
  have hh : ContinuousAt
      ((fun z : Plane × Plane × Plane => EuclideanGeometry.angle z.1 z.2.1 z.2.2) ∘
        (fun r : ℝ => (T.points (i + 1), T.points i, T.edgeParam i r))) t :=
    ha.comp (f := fun r : ℝ => (T.points (i + 1), T.points i, T.edgeParam i r))
      (x := t) hg.continuousAt
  exact hh

theorem edgeAngle_zero (T : Triangle) (i : Fin 3) : T.edgeAngle i 0 = 0 := by
  rw [edgeAngle, edgeParam, AffineMap.lineMap_apply_zero]
  exact EuclideanGeometry.angle_self_of_ne (T.independent.injective.ne
    ((by decide : ∀ i : Fin 3, i + 1 ≠ i) i))

theorem edgeAngle_one (T : Triangle) (i : Fin 3) : T.edgeAngle i 1 = T.angle i := by
  rw [edgeAngle, edgeParam, AffineMap.lineMap_apply_one]
  rfl

theorem coord_linear_sub_vertex_on_edge (T : Triangle) (i : Fin 3) {q : Plane}
    (hq : q ∈ T.edge i) : (T.coord i).linear (q - T.points i) = -1 := by
  change (T.coord i).linear (q -ᵥ T.points i) = -1
  rw [AffineMap.linearMap_vsub, hq.2, T.coord_vertex, if_pos rfl]
  change (0 : ℝ) - 1 = -1
  ring

theorem angle_pos_of_distinct_edge_points (T : Triangle) (i : Fin 3) {q r : Plane}
    (hq : q ∈ T.edge i) (hr : r ∈ T.edge i) (hne : q ≠ r) :
    0 < EuclideanGeometry.angle q (T.points i) r := by
  by_contra h
  have hz : EuclideanGeometry.angle q (T.points i) r = 0 :=
    le_antisymm (le_of_not_gt h) (EuclideanGeometry.angle_nonneg _ _ _)
  change InnerProductGeometry.angle (q - T.points i) (r - T.points i) = 0 at hz
  obtain ⟨_, c, _, hc⟩ := InnerProductGeometry.angle_eq_zero_iff.mp hz
  have hlin := congrArg (T.coord i).linear hc
  rw [map_smul, T.coord_linear_sub_vertex_on_edge i hq,
    T.coord_linear_sub_vertex_on_edge i hr] at hlin
  change (-1 : ℝ) = c * (-1) at hlin
  have hc1 : c = 1 := by linarith
  rw [hc1, one_smul] at hc
  exact hne (sub_left_injective hc).symm

theorem edgeAngle_add (T : Triangle) (i : Fin 3) {s t : ℝ}
    (hs : 0 ≤ s) (hst : s ≤ t) :
    T.edgeAngle i t = T.edgeAngle i s +
      EuclideanGeometry.angle (T.edgeParam i s) (T.points i) (T.edgeParam i t) := by
  by_cases ht : t = 0
  · have hs0 : s = 0 := by linarith
    subst t; subst s
    rw [EuclideanGeometry.angle_self_of_ne (T.edgeParam_ne_vertex i 0), add_zero]
  · have htpos : 0 < t := lt_of_le_of_ne (hs.trans hst) (Ne.symm ht)
    have hw0 : 0 ≤ s / t := div_nonneg hs htpos.le
    have hw1 : s / t ≤ 1 := (div_le_one htpos).mpr hst
    have hmid : AffineMap.lineMap (T.points (i + 1)) (T.edgeParam i t) (s / t) =
        T.edgeParam i s := by
      rw [edgeParam, AffineMap.lineMap_lineMap_right, div_mul_cancel₀ _ ht]
    have hv : T.edgeParam i s - T.points i =
        (1 - s / t) • (T.points (i + 1) - T.points i) +
          (s / t) • (T.edgeParam i t - T.points i) := by
      rw [← hmid, AffineMap.lineMap_apply_module]
      module
    have hspan : T.edgeParam i s - T.points i ∈ Submodule.span ℝ≥0
        {T.points (i + 1) - T.points i, T.edgeParam i t - T.points i} := by
      rw [Submodule.mem_span_pair]
      exact ⟨⟨1 - s / t, sub_nonneg.mpr hw1⟩, ⟨s / t, hw0⟩, hv.symm⟩
    exact InnerProductGeometry.angle_eq_angle_add_add_angle_add_of_mem_span
      (sub_ne_zero.mpr (T.edgeParam_ne_vertex i s)) hspan

theorem edgeAngle_strictMonoOn (T : Triangle) (i : Fin 3) :
    StrictMonoOn (T.edgeAngle i) (Set.Icc 0 1) := by
  intro s hs t ht hst
  have h := T.edgeAngle_add i hs.1 hst.le
  have hp := T.angle_pos_of_distinct_edge_points i (T.edgeParam_mem_edge i hs)
    (T.edgeParam_mem_edge i ht) ((T.edgeParam_injective i).ne hst.ne)
  linarith

theorem edgeParam_angle_eq_abs (T : Triangle) (i : Fin 3) {s t : ℝ}
    (hs : s ∈ Set.Icc 0 1) (ht : t ∈ Set.Icc 0 1) :
    EuclideanGeometry.angle (T.edgeParam i s) (T.points i) (T.edgeParam i t) =
      |T.edgeAngle i t - T.edgeAngle i s| := by
  rcases le_total s t with h | h
  · rw [abs_of_nonneg (sub_nonneg.mpr ((T.edgeAngle_strictMonoOn i).monotoneOn hs ht h))]
    linarith [T.edgeAngle_add i hs.1 h]
  · rw [abs_of_nonpos (sub_nonpos.mpr ((T.edgeAngle_strictMonoOn i).monotoneOn ht hs h)),
      EuclideanGeometry.angle_comm]
    linarith [T.edgeAngle_add i ht.1 h]

end Erdos633b.Triangle
