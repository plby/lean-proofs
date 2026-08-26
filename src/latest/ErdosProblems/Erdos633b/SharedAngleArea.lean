import ErdosProblems.Erdos633b.AffineAreaScaling
import ErdosProblems.Erdos633b.TriangleEdgeOrientation

/-! Exact Lebesgue-area ratios for triangles with one common angle.
The proof uses the actual affine vertex map and its determinant, with the
absolute area form obtained from the two-dimensional Gram identity. -/

namespace Erdos633b

open MeasureTheory

local instance : Fact (Module.finrank ℝ Plane = 2) := ⟨by simp [Plane]⟩

theorem areaForm_linearMap (o : Orientation ℝ Plane (Fin 2)) (L : Plane →ₗ[ℝ] Plane)
    (x y : Plane) : o.areaForm (L x) (L y) = LinearMap.det L * o.areaForm x y := by
  let b := (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis
  have h := o.volumeForm.eq_smul_basis_det b
  have he : (![L x, L y] : Fin 2 → Plane) = L ∘ ![x, y] := by
    funext i
    fin_cases i <;> rfl
  rw [o.areaForm_to_volumeForm, o.areaForm_to_volumeForm, he]
  have hv (v : Fin 2 → Plane) : o.volumeForm v = o.volumeForm b * b.det v := by
    simpa only [AlternatingMap.smul_apply, smul_eq_mul] using congrArg (fun g => g v) h
  rw [hv (L ∘ ![x, y]), hv ![x, y], Module.Basis.det_comp]
  ring

namespace Triangle

theorem abs_areaForm_edges (S : Triangle) (o : Orientation ℝ Plane (Fin 2)) :
    |o.areaForm (S.edgeVector 1) (S.edgeVector 2)| =
      S.side 1 * S.side 2 * Real.sin (S.angle 0) := by
  have hn1 : ‖S.edgeVector 1‖ = S.side 2 := by
    change ‖S.points 1 - S.points 0‖ = dist (S.points 0) (S.points 1)
    rw [← dist_eq_norm, dist_comm]
  have hn2 : ‖S.edgeVector 2‖ = S.side 1 := by
    change ‖S.points 2 - S.points 0‖ = dist (S.points 2) (S.points 0)
    rw [dist_eq_norm]
  have hcos : inner ℝ (S.edgeVector 1) (S.edgeVector 2) =
      Real.cos (S.angle 0) * (S.side 2 * S.side 1) := by
    have h := InnerProductGeometry.cos_angle_mul_norm_mul_norm (S.edgeVector 1) (S.edgeVector 2)
    rw [hn1, hn2] at h
    exact h.symm
  have hgram := o.inner_sq_add_areaForm_sq (S.edgeVector 1) (S.edgeVector 2)
  rw [hn1, hn2, hcos] at hgram
  have hs : (o.areaForm (S.edgeVector 1) (S.edgeVector 2)) ^ 2 =
      (S.side 1 * S.side 2 * Real.sin (S.angle 0)) ^ 2 := by
    linear_combination hgram - (S.side 1 * S.side 2) ^ 2 * Real.sin_sq_add_cos_sq (S.angle 0)
  have hp : 0 < S.side 1 * S.side 2 * Real.sin (S.angle 0) :=
    mul_pos (mul_pos (S.side_pos 1) (S.side_pos 2))
      (Real.sin_pos_of_pos_of_lt_pi (S.angle_pos 0) (S.angle_lt_pi 0))
  have ha := abs_nonneg (o.areaForm (S.edgeVector 1) (S.edgeVector 2))
  have habs := sq_abs (o.areaForm (S.edgeVector 1) (S.edgeVector 2))
  nlinarith

theorem area_eq_abs_det_affine_mul (S T : Triangle) (F : Plane →ᵃ[ℝ] Plane)
    (h : ∀ i, T.points i = F (S.points i)) : T.area = |LinearMap.det F.linear| * S.area := by
  have hs : T.support = F '' S.support := by
    have he : T.points = F ∘ S.points := funext h
    rw [support, he, Set.range_comp]
    exact (F.image_convexHull (Set.range S.points)).symm
  have hf : (F : Plane → Plane) = (fun x => x + F 0) ∘ F.linear := by
    funext x
    change F x = F.linear x + F 0
    simpa only [vadd_eq_add, add_zero] using F.map_vadd (0 : Plane) x
  have hv : volume T.support = ENNReal.ofReal |LinearMap.det F.linear| * volume S.support := by
    rw [hs, hf, Set.image_comp, Set.image_add_right, measure_preimage_add_right,
      Measure.addHaar_image_linearMap]
  have ha := congrArg ENNReal.toReal hv
  simpa only [area, ENNReal.toReal_mul, ENNReal.toReal_ofReal (abs_nonneg _)] using ha

theorem vertexMap_linear_edge (S T : Triangle) (j : Fin 3) :
    (S.vertexMap T).linear (S.edgeVector j) = T.edgeVector j := by
  change (S.vertexMap T).linear (S.points j -ᵥ S.points 0) = _
  rw [AffineMap.linearMap_vsub, S.vertexMap_vertex, S.vertexMap_vertex]
  rfl

theorem area_eq_ratio_of_shared_angle (S T : Triangle) (h0 : S.angle 0 = T.angle 0) :
    T.area = (T.side 1 * T.side 2 / (S.side 1 * S.side 2)) * S.area := by
  let o : Orientation ℝ Plane (Fin 2) := (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis.orientation
  let F := S.vertexMap T
  have hdet := areaForm_linearMap o F.linear (S.edgeVector 1) (S.edgeVector 2)
  change o.areaForm ((S.vertexMap T).linear (S.edgeVector 1))
    ((S.vertexMap T).linear (S.edgeVector 2)) = _ at hdet
  rw [S.vertexMap_linear_edge T 1, S.vertexMap_linear_edge T 2] at hdet
  have ha := congrArg abs hdet
  rw [abs_mul, S.abs_areaForm_edges, T.abs_areaForm_edges, ← h0] at ha
  have hd : |LinearMap.det F.linear| = T.side 1 * T.side 2 / (S.side 1 * S.side 2) := by
    apply (eq_div_iff (mul_ne_zero (S.side_pos 1).ne' (S.side_pos 2).ne')).mpr
    apply mul_right_cancel₀
      (Real.sin_pos_of_pos_of_lt_pi (S.angle_pos 0) (S.angle_lt_pi 0)).ne'
    calc
      _ = |LinearMap.det F.linear| * (S.side 1 * S.side 2 * Real.sin (S.angle 0)) := by ring
      _ = _ := ha.symm
  rw [S.area_eq_abs_det_affine_mul T F (fun i => (S.vertexMap_vertex T i).symm), hd]

end Triangle
namespace Tiling

theorem count_of_shared_angle {T : Triangle} {n : ℕ} (d : Tiling T n)
    (h0 : T.angle 0 = d.tile.angle 0) :
    (n : ℝ) = T.side 1 * T.side 2 / (d.tile.side 1 * d.tile.side 2) := by
  apply mul_right_cancel₀ d.tile.area_pos.ne'
  rw [← d.area_eq_mul]
  exact d.tile.area_eq_ratio_of_shared_angle T h0.symm

theorem normalized_count_of_shared_angle {T : Triangle} {n : ℕ} (d : Tiling T n)
    (h0 : T.angle 0 = d.tile.angle 0) :
    (n : ℝ) = ((T.side 1 / d.tile.side 2) * (T.side 2 / d.tile.side 2)) /
      (d.tile.side 1 / d.tile.side 2) := by
  rw [d.count_of_shared_angle h0]
  field_simp [(d.tile.side_pos 1).ne', (d.tile.side_pos 2).ne']

end Tiling
end Erdos633b
