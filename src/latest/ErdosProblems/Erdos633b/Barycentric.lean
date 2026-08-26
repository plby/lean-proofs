import ErdosProblems.Erdos633b.Area
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

/-! Barycentric coordinates for arbitrary nondegenerate Euclidean triangles. -/

namespace Erdos633b.Triangle

noncomputable def affineBasis (T : Triangle) : AffineBasis (Fin 3) ℝ Plane :=
  ⟨T.points, T.independent, T.span_eq_top (by simp [Plane])⟩

noncomputable def coord (T : Triangle) (i : Fin 3) : Plane →ᵃ[ℝ] ℝ :=
  T.affineBasis.coord i

theorem coord_vertex (T : Triangle) (i j : Fin 3) :
    T.coord i (T.points j) = if i = j then 1 else 0 :=
  T.affineBasis.coord_apply i j

theorem coord_sum (T : Triangle) (p : Plane) :
    T.coord 0 p + T.coord 1 p + T.coord 2 p = 1 := by
  simpa only [coord, Fin.sum_univ_three] using T.affineBasis.sum_coord_apply_eq_one p

/-- An affine scalar function is determined by its values at the three vertices. -/
theorem affine_scalar_interpolation (T : Triangle) (f : Plane →ᵃ[ℝ] ℝ) (p : Plane) :
    f p = f (T.points 0) * T.coord 0 p + f (T.points 1) * T.coord 1 p +
      f (T.points 2) * T.coord 2 p := by
  have h : f = f (T.points 0) • T.coord 0 + f (T.points 1) • T.coord 1 +
      f (T.points 2) • T.coord 2 := by
    apply AffineMap.ext_on (T.span_eq_top (by simp [Plane]))
    rintro _ ⟨i, rfl⟩
    fin_cases i <;> simp [coord_vertex]
  exact congrArg (fun g : Plane →ᵃ[ℝ] ℝ => g p) h

theorem mem_support_iff_coords (T : Triangle) (p : Plane) :
    p ∈ T.support ↔ 0 ≤ T.coord 1 p ∧ 0 ≤ T.coord 2 p ∧
      T.coord 1 p + T.coord 2 p ≤ 1 := by
  change p ∈ convexHull ℝ (Set.range T.affineBasis) ↔ _
  rw [T.affineBasis.convexHull_eq_nonneg_coord]
  change (∀ i, 0 ≤ T.coord i p) ↔ _
  have hs := T.coord_sum p
  constructor
  · intro h
    exact ⟨h 1, h 2, by linarith [h 0]⟩
  · rintro ⟨hx, hy, hxy⟩ i
    fin_cases i
    · change 0 ≤ T.coord 0 p
      linarith
    · exact hx
    · exact hy

theorem mem_interior_support_iff_coords (T : Triangle) (p : Plane) :
    p ∈ interior T.support ↔ 0 < T.coord 1 p ∧ 0 < T.coord 2 p ∧
      T.coord 1 p + T.coord 2 p < 1 := by
  change p ∈ interior (convexHull ℝ (Set.range T.affineBasis)) ↔ _
  rw [T.affineBasis.interior_convexHull]
  change (∀ i, 0 < T.coord i p) ↔ _
  have hs := T.coord_sum p
  constructor
  · intro h
    exact ⟨h 1, h 2, by linarith [h 0]⟩
  · rintro ⟨hx, hy, hxy⟩ i
    fin_cases i
    · change 0 < T.coord 0 p
      linarith
    · exact hx
    · exact hy

noncomputable def edgeVector (T : Triangle) (i : Fin 3) : Plane :=
  T.points i - T.points 0

theorem coord_linear_edge (T : Triangle) (i j : Fin 3) :
    (T.coord i).linear (T.edgeVector j) =
      (if i = j then 1 else 0) - (if i = 0 then 1 else 0) := by
  change (T.coord i).linear (T.points j -ᵥ T.points 0) = _
  rw [AffineMap.linearMap_vsub, coord_vertex, coord_vertex]
  rfl

noncomputable def latticeShift (T : Triangle) (x y : ℝ) : Plane :=
  x • T.edgeVector 1 + y • T.edgeVector 2

theorem coord_shift_one (T : Triangle) (x y : ℝ) (p : Plane) :
    T.coord 1 (T.latticeShift x y + p) = x + T.coord 1 p := by
  change T.coord 1 (T.latticeShift x y +ᵥ p) = _
  rw [AffineMap.map_vadd]
  simp [latticeShift, coord_linear_edge]

theorem coord_shift_two (T : Triangle) (x y : ℝ) (p : Plane) :
    T.coord 2 (T.latticeShift x y + p) = y + T.coord 2 p := by
  change T.coord 2 (T.latticeShift x y +ᵥ p) = _
  rw [AffineMap.map_vadd]
  simp [latticeShift, coord_linear_edge]

theorem coord_origin_combination (T : Triangle) (h0 : T.points 0 = 0) (x y : ℝ) :
    T.coord 1 (x • T.points 1 + y • T.points 2) = x ∧
      T.coord 2 (x • T.points 1 + y • T.points 2) = y := by
  have h : x • T.points 1 + y • T.points 2 = T.latticeShift x y + T.points 0 := by
    simp [latticeShift, edgeVector, h0]
  rw [h, coord_shift_one, coord_shift_two]
  simp [coord_vertex]

theorem coord_reflect_origin (T : Triangle) (i : Fin 3) (p : Plane) :
    T.coord i ((AffineIsometryEquiv.pointReflection ℝ (T.points 0)) p) =
      2 * T.coord i (T.points 0) - T.coord i p := by
  rw [AffineIsometryEquiv.pointReflection_apply, AffineMap.map_vadd,
    AffineMap.linearMap_vsub]
  change T.coord i (T.points 0) - T.coord i p + T.coord i (T.points 0) = _
  ring

end Erdos633b.Triangle
