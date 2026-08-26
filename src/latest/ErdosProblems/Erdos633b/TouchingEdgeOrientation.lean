import ErdosProblems.Erdos633b.TriangleEdgeOrientation
import ErdosProblems.Erdos633b.TouchingHalfPlanes

/-! The positively oriented edge vectors of two tiles meeting along open
edges point in opposite directions. Their direction colors therefore flip. -/

namespace Erdos633b.Triangle

local instance : Fact (Module.finrank ℝ Plane = 2) := ⟨by simp [Plane]⟩

theorem touching_cyclicEdgeVectors_parallel (S R : Triangle)
    (hd : Disjoint (interior S.support) (interior R.support)) (i j : Fin 3) {p : Plane}
    (hpS : p ∈ S.openEdge j) (hpR : p ∈ R.openEdge i) :
    ∃ c : ℝ, S.cyclicEdgeVector j = c • R.cyclicEdgeVector i := by
  obtain ⟨hA, hB⟩ := S.coord_zero_at_touching_edge_endpoints R hd i j hpS hpR
  refine ⟨R.coord (i + 2) (S.points (j + 2)) - R.coord (i + 2) (S.points (j + 1)), ?_⟩
  change S.points (j + 2) - S.points (j + 1) = _
  calc
    _ = (S.points (j + 2) - R.points (i + 1)) -
        (S.points (j + 1) - R.points (i + 1)) := by abel
    _ = _ := by
      rw [R.relative_edge_coordinates i (S.points (j + 2)),
        R.relative_edge_coordinates i (S.points (j + 1)), hA, hB]
      module

theorem touching_positiveEdgeVectors_parallel (S R : Triangle)
    (o : Orientation ℝ Plane (Fin 2))
    (hd : Disjoint (interior S.support) (interior R.support)) (i j : Fin 3) {p : Plane}
    (hpS : p ∈ S.openEdge j) (hpR : p ∈ R.openEdge i) :
    ∃ c : ℝ, S.positiveEdgeVector o j = c • R.positiveEdgeVector o i := by
  obtain ⟨c, hc⟩ := S.touching_cyclicEdgeVectors_parallel R hd i j hpS hpR
  unfold positiveEdgeVector
  split_ifs
  · exact ⟨c, hc⟩
  · refine ⟨-c, ?_⟩
    rw [hc]
    module
  · refine ⟨-c, ?_⟩
    rw [hc]
    module
  · refine ⟨c, ?_⟩
    rw [hc]
    module

theorem touching_positiveEdgeVectors_opposite (S R : Triangle)
    (o : Orientation ℝ Plane (Fin 2))
    (hd : Disjoint (interior S.support) (interior R.support)) (i j : Fin 3) {p : Plane}
    (hpS : p ∈ S.openEdge j) (hpR : p ∈ R.openEdge i) :
    ∃ c : ℝ, 0 < c ∧ S.positiveEdgeVector o j = c • (-R.positiveEdgeVector o i) := by
  obtain ⟨c, hc⟩ := S.touching_positiveEdgeVectors_parallel R o hd i j hpS hpR
  have hc0 : c ≠ 0 := by
    intro h
    rw [h, zero_smul] at hc
    exact S.positiveEdgeVector_ne_zero o j hc
  have hcneg : c < 0 := by
    by_contra hn
    have hcpos : 0 < c := lt_of_le_of_ne (le_of_not_gt hn) (Ne.symm hc0)
    have hpSA : S.coord j (S.points (j + 1)) = 0 := by
      rw [S.coord_vertex, if_neg ((by decide : ∀ j : Fin 3, j ≠ j + 1) j)]
    have hpRA := (S.coord_zero_at_touching_edge_endpoints R hd i j hpS hpR).1
    have hneg := S.coord_neg_at_touching_opposite_vertex R hd i j hpS hpR
    have hS := S.positiveEdgeVector_side_sign o j (S.points (j + 1)) (S.points j) hpSA
    have hR := R.positiveEdgeVector_side_sign o i (S.points (j + 1)) (S.points j) hpRA
    rw [S.coord_vertex, if_pos rfl, sign_one] at hS
    rw [sign_neg hneg] at hR
    rw [hc, o.oangle_smul_left_of_pos _ _ hcpos, hR] at hS
    norm_num at hS
  refine ⟨-c, neg_pos.mpr hcneg, ?_⟩
  rw [hc]
  module

theorem touching_positiveEdgeDirections (S R : Triangle)
    (o : Orientation ℝ Plane (Fin 2)) {u : Plane} (hu : u ≠ 0)
    (hd : Disjoint (interior S.support) (interior R.support)) (i j : Fin 3) {p : Plane}
    (hpS : p ∈ S.openEdge j) (hpR : p ∈ R.openEdge i) :
    S.positiveEdgeDirection o u j = R.positiveEdgeDirection o u i + (Real.pi : Real.Angle) := by
  obtain ⟨c, hc, he⟩ := S.touching_positiveEdgeVectors_opposite R o hd i j hpS hpR
  unfold positiveEdgeDirection
  rw [he, o.oangle_smul_right_of_pos _ _ hc,
    o.oangle_neg_right hu (R.positiveEdgeVector_ne_zero o i)]

theorem touching_positive_edge_color (S R : Triangle)
    (o : Orientation ℝ Plane (Fin 2)) {u : Plane} (hu : u ≠ 0)
    (f : Real.Angle → ZMod 2) (hf : ∀ x, f (x + (Real.pi : Real.Angle)) = f x + 1)
    (hd : Disjoint (interior S.support) (interior R.support)) (i j : Fin 3) {p : Plane}
    (hpS : p ∈ S.openEdge j) (hpR : p ∈ R.openEdge i) :
    f (S.positiveEdgeDirection o u j) = f (R.positiveEdgeDirection o u i) + 1 := by
  rw [S.touching_positiveEdgeDirections R o hu hd i j hpS hpR, hf]

end Erdos633b.Triangle
