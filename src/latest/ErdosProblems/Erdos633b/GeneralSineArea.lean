import ErdosProblems.Erdos633b.SharedAngleArea

/-! Actual area comparison without a shared-angle hypothesis, and the
sine-product identity for every finite congruent-triangle dissection. -/

namespace Erdos633b

local instance : Fact (Module.finrank ℝ Plane = 2) := ⟨by simp [Plane]⟩

namespace Triangle

theorem area_mul_sides_sine_eq (S T : Triangle) :
    T.area * (S.side 1 * S.side 2 * Real.sin (S.angle 0)) =
      S.area * (T.side 1 * T.side 2 * Real.sin (T.angle 0)) := by
  let o : Orientation ℝ Plane (Fin 2) := (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis.orientation
  let F := S.vertexMap T
  have hdet := areaForm_linearMap o F.linear (S.edgeVector 1) (S.edgeVector 2)
  change o.areaForm ((S.vertexMap T).linear (S.edgeVector 1))
    ((S.vertexMap T).linear (S.edgeVector 2)) = _ at hdet
  rw [S.vertexMap_linear_edge T 1, S.vertexMap_linear_edge T 2] at hdet
  have ha := congrArg abs hdet
  rw [abs_mul, S.abs_areaForm_edges, T.abs_areaForm_edges] at ha
  rw [S.area_eq_abs_det_affine_mul T F (fun i => (S.vertexMap_vertex T i).symm), ha]
  ring

end Triangle
namespace Tiling

theorem count_mul_sides_sine_eq {T : Triangle} {n : ℕ} (d : Tiling T n) :
    (n : ℝ) * d.tile.side 1 * d.tile.side 2 * Real.sin (d.tile.angle 0) =
      T.side 1 * T.side 2 * Real.sin (T.angle 0) := by
  apply mul_left_cancel₀ d.tile.area_pos.ne'
  calc
    _ = ((n : ℝ) * d.tile.area) *
        (d.tile.side 1 * d.tile.side 2 * Real.sin (d.tile.angle 0)) := by ring
    _ = T.area * (d.tile.side 1 * d.tile.side 2 * Real.sin (d.tile.angle 0)) := by
      rw [d.area_eq_mul]
    _ = _ := d.tile.area_mul_sides_sine_eq T

theorem normalized_sine_area_identity {T : Triangle} {n : ℕ} (d : Tiling T n) :
    (n : ℝ) * Real.sin (d.tile.angle 0) * Real.sin (d.tile.angle 1) * Real.sin (T.angle 0) =
      (T.side 0 / d.tile.side 2) ^ 2 * Real.sin (T.angle 1) * Real.sin (T.angle 2) *
        Real.sin (d.tile.angle 2) := by
  have ha := d.count_mul_sides_sine_eq
  have hs := d.tile.sine_law 1 2
  have h1 := T.sine_law 1 0
  have h2 := T.sine_law 2 0
  field_simp [(d.tile.side_pos 2).ne']
  linear_combination
    (Real.sin (d.tile.angle 2) * Real.sin (T.angle 0)) * ha +
    ((n : ℝ) * Real.sin (d.tile.angle 0) * Real.sin (T.angle 0) * d.tile.side 2) * hs -
    (Real.sin (d.tile.angle 2) * Real.sin (T.angle 2) * T.side 0) * h1 -
    (Real.sin (d.tile.angle 2) * Real.sin (T.angle 0) * T.side 1) * h2

theorem boundary_sine_sum {T : Triangle} {n : ℕ} (d : Tiling T n) (i : Fin 3) :
    T.side i / d.tile.side 2 * Real.sin (d.tile.angle 2) =
      (d.boundarySideCount i 0 : ℝ) * Real.sin (d.tile.angle 0) +
        d.boundarySideCount i 1 * Real.sin (d.tile.angle 1) +
        d.boundarySideCount i 2 * Real.sin (d.tile.angle 2) := by
  have hb := d.side_eq_three_counts i
  have h0 := d.tile.sine_law 0 2
  have h1 := d.tile.sine_law 1 2
  field_simp [(d.tile.side_pos 2).ne']
  linear_combination Real.sin (d.tile.angle 2) * hb -
    (d.boundarySideCount i 0 : ℝ) * h0 - (d.boundarySideCount i 1 : ℝ) * h1

theorem sine_product_area_identity {T : Triangle} {n : ℕ} (d : Tiling T n) :
    (n : ℝ) * (Real.sin (d.tile.angle 0) * Real.sin (d.tile.angle 1) *
      Real.sin (d.tile.angle 2)) * Real.sin (T.angle 0) ^ 2 =
    ((d.boundarySideCount 0 0 : ℝ) * Real.sin (d.tile.angle 0) +
      d.boundarySideCount 0 1 * Real.sin (d.tile.angle 1) +
      d.boundarySideCount 0 2 * Real.sin (d.tile.angle 2)) ^ 2 *
      (Real.sin (T.angle 0) * Real.sin (T.angle 1) * Real.sin (T.angle 2)) := by
  rw [← d.boundary_sine_sum 0]
  linear_combination (Real.sin (T.angle 0) * Real.sin (d.tile.angle 2)) *
    d.normalized_sine_area_identity

theorem scaled_sine_product_area_identity {T : Triangle} {n : ℕ} (d : Tiling T n)
    (u : ℝ) (hu : u ≠ 0) :
    (n : ℝ) * ((Real.sin (d.tile.angle 0) / u) * (Real.sin (d.tile.angle 1) / u) *
      (Real.sin (d.tile.angle 2) / u)) * (Real.sin (T.angle 0) / u) ^ 2 =
    ((d.boundarySideCount 0 0 : ℝ) * (Real.sin (d.tile.angle 0) / u) +
      d.boundarySideCount 0 1 * (Real.sin (d.tile.angle 1) / u) +
      d.boundarySideCount 0 2 * (Real.sin (d.tile.angle 2) / u)) ^ 2 *
      ((Real.sin (T.angle 0) / u) * (Real.sin (T.angle 1) / u) *
        (Real.sin (T.angle 2) / u)) := by
  field_simp [hu]
  linear_combination d.sine_product_area_identity

end Tiling
end Erdos633b
