import ErdosProblems.Erdos633b.BoundaryAngularCoordinates
import ErdosProblems.Erdos633b.AngleParameter
import ErdosProblems.Erdos633b.BoundaryPointIncidence
import Mathlib.Analysis.Convex.StrictConvexBetween
import Mathlib.Analysis.Convex.PathConnected

/-! An incident triangle's opposite edge maps exactly to its closed angular
interval. The proof uses angle additivity and the intermediate value theorem. -/

namespace Erdos633b.Triangle

theorem ne_vertex_of_mem_edge (S : Triangle) (j : Fin 3) {q : Plane} (hq : q ∈ S.edge j) :
    q ≠ S.points j := by
  intro he
  have hc : S.coord j q = 0 := hq.2
  rw [he, S.coord_vertex, if_pos rfl] at hc
  norm_num at hc

theorem angle_split_of_mem_edge (S : Triangle) (j : Fin 3) {q : Plane} (hq : q ∈ S.edge j) :
    S.angle j = EuclideanGeometry.angle (S.points (j + 1)) (S.points j) q +
      EuclideanGeometry.angle q (S.points j) (S.points (j + 2)) := by
  have hparam : ∃ t ∈ Set.Icc (0 : ℝ) 1, S.edgeParam j t = q := by
    rw [S.edge_eq_segment, segment_eq_image_lineMap] at hq
    exact hq
  obtain ⟨t, ht, hq⟩ := hparam
  have he := S.edgeAngle_add j ht.1 ht.2
  rw [S.edgeAngle_one] at he
  change S.angle j = EuclideanGeometry.angle (S.points (j + 1)) (S.points j) (S.edgeParam j t) +
    EuclideanGeometry.angle (S.edgeParam j t) (S.points j) (S.edgeParam j 1) at he
  have h1 : S.edgeParam j 1 = S.points (j + 2) := AffineMap.lineMap_apply_one _ _
  rwa [hq, h1] at he

theorem boundaryAngle_continuousAt (T : Triangle) (i : Fin 3) {p q : Plane}
    (hp : p ∈ T.openEdge i) (hq : q ≠ p) : ContinuousAt (T.boundaryAngle i p) q := by
  have hP : T.points (i + 1) ≠ p := sub_ne_zero.mp (T.boundary_ray_ne_zero i hp (i + 1))
  have ha := EuclideanGeometry.continuousAt_angle (V := Plane)
    (x := (T.points (i + 1), p, q)) hP hq
  have hg : Continuous (fun r : Plane => (T.points (i + 1), p, r)) :=
    continuous_const.prodMk (continuous_const.prodMk continuous_id)
  exact ha.comp (f := fun r : Plane => (T.points (i + 1), p, r)) (x := q) hg.continuousAt

theorem boundaryAngle_mem_segment (T S : Triangle) (hST : S.support ⊆ T.support)
    (i j : Fin 3) {p q : Plane} (hp : p ∈ T.openEdge i) (hO : S.points j = p)
    (hq : q ∈ S.edge j) :
    T.boundaryAngle i p q ∈ segment ℝ (T.boundaryAngle i p (S.points (j + 1)))
      (T.boundaryAngle i p (S.points (j + 2))) := by
  have hA := S.edge_vertex_mem j (j + 1) ((by decide : ∀ j : Fin 3, j + 1 ≠ j) j)
  have hB := S.edge_vertex_mem j (j + 2) ((by decide : ∀ j : Fin 3, j + 2 ≠ j) j)
  have hn (r : Plane) (hr : r ∈ S.edge j) : r ≠ p := by
    rw [← hO]
    exact S.ne_vertex_of_mem_edge j hr
  have he := S.angle_split_of_mem_edge j hq
  change EuclideanGeometry.angle (S.points (j + 1)) (S.points j) (S.points (j + 2)) = _ at he
  rw [hO, T.boundaryAngle_difference i hp (hST hA.1) (hST hB.1) (hn _ hA) (hn _ hB),
    T.boundaryAngle_difference i hp (hST hA.1) (hST hq.1) (hn _ hA) (hn _ hq),
    T.boundaryAngle_difference i hp (hST hq.1) (hST hB.1) (hn _ hq) (hn _ hB)] at he
  apply mem_segment_iff_wbtw.mpr
  apply dist_add_dist_eq_iff.mp
  rw [Real.dist_eq, Real.dist_eq, Real.dist_eq,
    abs_sub_comm (T.boundaryAngle i p (S.points (j + 1))) (T.boundaryAngle i p q),
    abs_sub_comm (T.boundaryAngle i p q) (T.boundaryAngle i p (S.points (j + 2))),
    abs_sub_comm (T.boundaryAngle i p (S.points (j + 1)))
      (T.boundaryAngle i p (S.points (j + 2)))]
  exact he.symm

theorem boundaryAngle_injOn_edge (T S : Triangle) (hST : S.support ⊆ T.support)
    (i j : Fin 3) {p : Plane} (hp : p ∈ T.openEdge i) (hO : S.points j = p) :
    Set.InjOn (T.boundaryAngle i p) (S.edge j) := by
  intro q hq r hr he
  by_contra hne
  have hqp : q ≠ p := hO ▸ S.ne_vertex_of_mem_edge j hq
  have hrp : r ≠ p := hO ▸ S.ne_vertex_of_mem_edge j hr
  have hd := T.boundaryAngle_difference i hp (hST hq.1) (hST hr.1) hqp hrp
  rw [he, sub_self, abs_zero, ← hO] at hd
  exact (S.angle_pos_of_distinct_edge_points j hq hr hne).ne' hd

theorem boundaryAngle_image_edge (T S : Triangle) (hST : S.support ⊆ T.support)
    (i j : Fin 3) {p : Plane} (hp : p ∈ T.openEdge i) (hO : S.points j = p) :
    T.boundaryAngle i p '' S.edge j =
      segment ℝ (T.boundaryAngle i p (S.points (j + 1)))
        (T.boundaryAngle i p (S.points (j + 2))) := by
  apply Set.Subset.antisymm
  · rintro _ ⟨q, hq, rfl⟩
    exact T.boundaryAngle_mem_segment S hST i j hp hO hq
  · have hcont : ContinuousOn (T.boundaryAngle i p) (S.edge j) := by
      intro q hq
      exact (T.boundaryAngle_continuousAt i hp
        (hO ▸ S.ne_vertex_of_mem_edge j hq)).continuousWithinAt
    have hconv := ((S.edge_convex j).isPreconnected.image (T.boundaryAngle i p) hcont).convex
    exact hconv.segment_subset
      ⟨S.points (j + 1), S.edge_vertex_mem j (j + 1)
        ((by decide : ∀ j : Fin 3, j + 1 ≠ j) j), rfl⟩
      ⟨S.points (j + 2), S.edge_vertex_mem j (j + 2)
        ((by decide : ∀ j : Fin 3, j + 2 ≠ j) j), rfl⟩


theorem boundaryAngle_endpoints_ne (T S : Triangle) (hST : S.support ⊆ T.support)
    (i j : Fin 3) {p : Plane} (hp : p ∈ T.openEdge i) (hO : S.points j = p) :
    T.boundaryAngle i p (S.points (j + 1)) ≠ T.boundaryAngle i p (S.points (j + 2)) := by
  have h1 : j + 1 ≠ j := (by decide : ∀ j : Fin 3, j + 1 ≠ j) j
  have h2 : j + 2 ≠ j := (by decide : ∀ j : Fin 3, j + 2 ≠ j) j
  have h12 : j + 1 ≠ j + 2 := (by decide : ∀ j : Fin 3, j + 1 ≠ j + 2) j
  intro he
  exact S.independent.injective.ne h12
    (T.boundaryAngle_injOn_edge S hST i j hp hO (S.edge_vertex_mem j _ h1)
      (S.edge_vertex_mem j _ h2) he)

theorem boundaryAngle_image_openEdge (T S : Triangle) (hST : S.support ⊆ T.support)
    (i j : Fin 3) {p : Plane} (hp : p ∈ T.openEdge i) (hO : S.points j = p) :
    T.boundaryAngle i p '' S.openEdge j =
      openSegment ℝ (T.boundaryAngle i p (S.points (j + 1)))
        (T.boundaryAngle i p (S.points (j + 2))) := by
  have hA := S.edge_vertex_mem j (j + 1) ((by decide : ∀ j : Fin 3, j + 1 ≠ j) j)
  have hB := S.edge_vertex_mem j (j + 2) ((by decide : ∀ j : Fin 3, j + 2 ≠ j) j)
  have hinj := T.boundaryAngle_injOn_edge S hST i j hp hO
  have hne := T.boundaryAngle_endpoints_ne S hST i j hp hO
  apply Set.Subset.antisymm
  · rintro _ ⟨q, hq, rfl⟩
    have hq' := S.openEdge_subset_edge j hq
    apply mem_openSegment_of_ne_left_right ?_ ?_
      (T.boundaryAngle_mem_segment S hST i j hp hO hq')
    · intro he
      have heq := hinj hA hq' he
      exact S.vertex_not_mem_openEdge j (j + 1) (heq.symm ▸ hq)
    · intro he
      have heq := hinj hB hq' he
      exact S.vertex_not_mem_openEdge j (j + 2) (heq.symm ▸ hq)
  · intro t ht
    have ht' := openSegment_subset_segment ℝ _ _ ht
    rw [← T.boundaryAngle_image_edge S hST i j hp hO] at ht'
    obtain ⟨q, hq, hqt⟩ := ht'
    refine ⟨q, ?_, hqt⟩
    rw [S.openEdge_eq_openSegment]
    apply mem_openSegment_of_ne_left_right ?_ ?_ (S.edge_eq_segment j ▸ hq)
    · intro he
      have hat : T.boundaryAngle i p (S.points (j + 1)) = t := by rw [he, hqt]
      rw [← hat] at ht
      exact hne (left_mem_openSegment_iff.mp ht)
    · intro he
      have hbt : T.boundaryAngle i p (S.points (j + 2)) = t := by rw [he, hqt]
      rw [← hbt] at ht
      exact hne (right_mem_openSegment_iff.mp ht)

theorem boundaryAngle_radial (T : Triangle) (i : Fin 3) (p q : Plane) {r : ℝ}
    (hr : 0 < r) : T.boundaryAngle i p (AffineMap.homothety p r q) = T.boundaryAngle i p q := by
  simp only [boundaryAngle, EuclideanGeometry.angle, AffineMap.homothety_apply, vadd_vsub]
  exact InnerProductGeometry.angle_smul_right_of_pos _ _ hr

theorem boundaryAngle_mem_of_support_shared (T S : Triangle) (hST : S.support ⊆ T.support)
    (i j : Fin 3) {p q : Plane} (hp : p ∈ T.openEdge i) (hO : S.points j = p)
    (hq : q ∈ S.support) (hqp : q ≠ p) :
    T.boundaryAngle i p q ∈ segment ℝ (T.boundaryAngle i p (S.points (j + 1)))
      (T.boundaryAngle i p (S.points (j + 2))) := by
  have hqj : q ≠ S.points j := by rwa [hO]
  have hproj := S.cornerProject_mem_edge j hq hqj
  have he := T.boundaryAngle_mem_segment S hST i j hp hO hproj
  have hr : 0 < (S.cornerScale j q)⁻¹ := inv_pos.mpr (S.cornerScale_pos j hq hqj)
  unfold cornerProject at he
  rwa [hO, T.boundaryAngle_radial i p q hr] at he

end Erdos633b.Triangle
