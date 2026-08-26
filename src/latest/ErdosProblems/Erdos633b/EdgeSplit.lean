import ErdosProblems.Erdos633b.TriangleMaps
import ErdosProblems.Erdos633b.CoordinateHalfplanes

/-! Exact dissection at any point strictly inside an edge. -/

namespace Erdos633b.Triangle

noncomputable def edgePoint (T : Triangle) (w : ℝ) : Plane :=
  T.latticeShift w 0 + T.points 0

theorem edgePoint_eq (T : Triangle) (w : ℝ) :
    T.edgePoint w = (1 - w) • T.points 0 + w • T.points 1 := by
  simp only [edgePoint, latticeShift, edgeVector]
  module

theorem edgePoint_coords (T : Triangle) (w : ℝ) :
    T.coord 1 (T.edgePoint w) = w ∧ T.coord 2 (T.edgePoint w) = 0 := by
  simp [edgePoint, coord_shift_one, coord_shift_two, coord_vertex]

noncomputable def edgePartMap (T : Triangle) (w : ℝ) : Plane →ᵃ[ℝ] Plane :=
  (((LinearMap.id : ℝ →ₗ[ℝ] ℝ).smulRight (T.edgeVector 1)).toAffineMap.comp
    (w • T.coord 2)) +
  (((LinearMap.id : ℝ →ₗ[ℝ] ℝ).smulRight (T.edgeVector 2)).toAffineMap.comp
    (AffineMap.const ℝ Plane 1 - T.coord 1 - T.coord 2)) + AffineMap.const ℝ Plane (T.points 0)

theorem edgePartMap_apply (T : Triangle) (w : ℝ) (p : Plane) :
    T.edgePartMap w p = T.latticeShift (w * T.coord 2 p)
      (1 - T.coord 1 p - T.coord 2 p) + T.points 0 := rfl

theorem edgePartMap_coords (T : Triangle) (w : ℝ) (p : Plane) :
    T.coord 1 (T.edgePartMap w p) = w * T.coord 2 p ∧
      T.coord 2 (T.edgePartMap w p) = 1 - T.coord 1 p - T.coord 2 p := by
  rw [edgePartMap_apply, coord_shift_one, coord_shift_two]
  simp [coord_vertex]

theorem edgePartMap_injective (T : Triangle) (w : ℝ) (hw : 0 < w) :
    Function.Injective (T.edgePartMap w) := by
  intro p q hpq
  have hx := congrArg (T.coord 1) hpq
  have hy := congrArg (T.coord 2) hpq
  rw [(T.edgePartMap_coords w p).1, (T.edgePartMap_coords w q).1] at hx
  rw [(T.edgePartMap_coords w p).2, (T.edgePartMap_coords w q).2] at hy
  have h2 := mul_left_cancel₀ hw.ne' hx
  exact T.ext_coords (by linarith) h2

noncomputable def edgeFirst (T : Triangle) (w : ℝ) (hw : 0 < w) : Triangle :=
  T.map (T.edgePartMap w) (T.edgePartMap_injective w hw)

noncomputable def edgeSecond (T : Triangle) (w : ℝ) (hw1 : w < 1) : Triangle :=
  edgeFirst (T.reindex (Equiv.swap 0 1)) (1 - w) (sub_pos.mpr hw1)

theorem edgeFirst_points (T : Triangle) (w : ℝ) (hw : 0 < w) :
    (T.edgeFirst w hw).points = ![T.points 2, T.points 0, T.edgePoint w] := by
  funext i
  change T.edgePartMap w (T.points i) = _
  rw [edgePartMap_apply]
  fin_cases i <;> simp [coord_vertex, edgePoint, latticeShift, edgeVector]

theorem edgeSecond_points (T : Triangle) (w : ℝ) (hw1 : w < 1) :
    (T.edgeSecond w hw1).points = ![T.points 2, T.points 1, T.edgePoint w] := by
  have hs : (Equiv.swap (0 : Fin 3) 1) 2 = 2 := by decide
  rw [edgeSecond, edgeFirst_points]
  funext i
  fin_cases i <;> simp [Affine.Simplex.reindex, hs, edgePoint_eq]
  module

theorem edgeFirst_coords (T : Triangle) (w : ℝ) (hw : 0 < w) (p : Plane) :
    T.coord 1 p = w * (T.edgeFirst w hw).coord 2 p ∧
      T.coord 2 p = 1 - (T.edgeFirst w hw).coord 1 p - (T.edgeFirst w hw).coord 2 p := by
  have hx := (T.edgeFirst w hw).affine_scalar_interpolation (T.coord 1) p
  have hy := (T.edgeFirst w hw).affine_scalar_interpolation (T.coord 2) p
  simp only [edgeFirst_points] at hx hy
  have hx' : T.coord 1 p = w * (T.edgeFirst w hw).coord 2 p := by
    simpa [coord_vertex, (T.edgePoint_coords w).1] using hx
  have hy' : T.coord 2 p = (T.edgeFirst w hw).coord 0 p := by
    simpa [coord_vertex, (T.edgePoint_coords w).2] using hy
  exact ⟨hx', by linarith [(T.edgeFirst w hw).coord_sum p]⟩

theorem edgeSecond_coords (T : Triangle) (w : ℝ) (hw1 : w < 1) (p : Plane) :
    T.coord 1 p = (T.edgeSecond w hw1).coord 1 p + w * (T.edgeSecond w hw1).coord 2 p ∧
      T.coord 2 p = 1 - (T.edgeSecond w hw1).coord 1 p - (T.edgeSecond w hw1).coord 2 p := by
  have hx := (T.edgeSecond w hw1).affine_scalar_interpolation (T.coord 1) p
  have hy := (T.edgeSecond w hw1).affine_scalar_interpolation (T.coord 2) p
  simp only [edgeSecond_points] at hx hy
  have hx' : T.coord 1 p =
      (T.edgeSecond w hw1).coord 1 p + w * (T.edgeSecond w hw1).coord 2 p := by
    simpa [coord_vertex, (T.edgePoint_coords w).1] using hx
  have hy' : T.coord 2 p = (T.edgeSecond w hw1).coord 0 p := by
    simpa [coord_vertex, (T.edgePoint_coords w).2] using hy
  exact ⟨hx', by linarith [(T.edgeSecond w hw1).coord_sum p]⟩

theorem mem_edgeFirst_support (T : Triangle) (w : ℝ) (hw : 0 < w) (p : Plane) :
    p ∈ (T.edgeFirst w hw).support ↔
      0 ≤ T.coord 1 p ∧ 0 ≤ T.coord 2 p ∧ T.coord 1 p + w * T.coord 2 p ≤ w := by
  rw [mem_support_iff_coords]
  obtain ⟨hx, hy⟩ := T.edgeFirst_coords w hw p
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨by nlinarith [mul_nonneg hw.le h2], by linarith,
      by nlinarith [mul_nonneg hw.le h1]⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨by nlinarith, by nlinarith, by linarith⟩

theorem mem_edgeSecond_support (T : Triangle) (w : ℝ) (hw1 : w < 1) (p : Plane) :
    p ∈ (T.edgeSecond w hw1).support ↔
      0 ≤ T.coord 2 p ∧ T.coord 1 p + T.coord 2 p ≤ 1 ∧ w ≤ T.coord 1 p + w * T.coord 2 p := by
  rw [mem_support_iff_coords]
  obtain ⟨hx, hy⟩ := T.edgeSecond_coords w hw1 p
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨by linarith, by nlinarith [mul_nonneg (sub_pos.mpr hw1).le h2],
      by nlinarith [mul_nonneg (sub_pos.mpr hw1).le h1]⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨by nlinarith, by nlinarith, by linarith⟩

theorem edgeParts_cover (T : Triangle) (w : ℝ) (hw : 0 < w) (hw1 : w < 1) :
    (T.edgeFirst w hw).support ∪ (T.edgeSecond w hw1).support = T.support := by
  ext p
  rw [Set.mem_union, mem_edgeFirst_support, mem_edgeSecond_support, mem_support_iff_coords]
  constructor
  · rintro (⟨hx, hy, h⟩ | ⟨hy, hsum, h⟩)
    · have hy1 : T.coord 2 p ≤ 1 := by nlinarith
      exact ⟨hx, hy, by nlinarith [mul_nonneg (sub_pos.mpr hw1).le (sub_nonneg.mpr hy1)]⟩
    · have hy1 : T.coord 2 p ≤ 1 := by nlinarith
      exact ⟨by nlinarith [mul_nonneg hw.le (sub_nonneg.mpr hy1)], hy, hsum⟩
  · rintro ⟨hx, hy, hsum⟩
    by_cases h : T.coord 1 p + w * T.coord 2 p ≤ w
    · exact Or.inl ⟨hx, hy, h⟩
    · exact Or.inr ⟨hy, hsum, le_of_not_ge h⟩

theorem edgeParts_disjoint_interiors (T : Triangle) (w : ℝ) (hw : 0 < w) (hw1 : w < 1) :
    Disjoint (interior (T.edgeFirst w hw).support) (interior (T.edgeSecond w hw1).support) := by
  have hR : (T.edgeFirst w hw).support ⊆ {p | T.coordForm 1 w p ≤ w} := by
    intro p hp
    change T.coordForm 1 w p ≤ w
    simpa only [coordForm_apply, one_mul] using ((T.mem_edgeFirst_support w hw p).mp hp).2.2
  have hS : (T.edgeSecond w hw1).support ⊆ {p | w ≤ T.coordForm 1 w p} := by
    intro p hp
    change w ≤ T.coordForm 1 w p
    simpa only [coordForm_apply, one_mul] using ((T.mem_edgeSecond_support w hw1 p).mp hp).2.2
  have hiR := interior_mono hR
  have hiS := interior_mono hS
  rw [T.interior_coordForm_le 1 w w (Or.inl one_ne_zero)] at hiR
  rw [T.interior_coordForm_ge 1 w w (Or.inl one_ne_zero)] at hiS
  apply Set.disjoint_left.mpr
  intro p hp hq
  have hfirst := hiR hp
  have hsecond := hiS hq
  change T.coordForm 1 w p < w at hfirst
  change w < T.coordForm 1 w p at hsecond
  exact lt_asymm hfirst hsecond

end Erdos633b.Triangle
