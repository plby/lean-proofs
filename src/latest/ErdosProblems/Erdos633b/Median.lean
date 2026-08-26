import ErdosProblems.Erdos633b.TriangleMaps
import ErdosProblems.Erdos633b.CoordinateHalfplanes

/-! A median gives an exact dissection of any nondegenerate triangle into two triangles. -/

namespace Erdos633b.Triangle

noncomputable def medianMap (T : Triangle) : Plane →ᵃ[ℝ] Plane :=
  (((LinearMap.id : ℝ →ₗ[ℝ] ℝ).smulRight (T.edgeVector 1)).toAffineMap.comp
    ((1 / 2 : ℝ) • T.coord 2)) +
  (((LinearMap.id : ℝ →ₗ[ℝ] ℝ).smulRight (T.edgeVector 2)).toAffineMap.comp
    (AffineMap.const ℝ Plane 1 - T.coord 1 - T.coord 2)) + AffineMap.const ℝ Plane (T.points 0)

theorem medianMap_apply (T : Triangle) (p : Plane) :
    T.medianMap p = T.latticeShift ((1 / 2 : ℝ) * T.coord 2 p)
      (1 - T.coord 1 p - T.coord 2 p) + T.points 0 := rfl

theorem medianMap_coords (T : Triangle) (p : Plane) :
    T.coord 1 (T.medianMap p) = (1 / 2 : ℝ) * T.coord 2 p ∧
      T.coord 2 (T.medianMap p) = 1 - T.coord 1 p - T.coord 2 p := by
  rw [medianMap_apply, coord_shift_one, coord_shift_two]
  simp [coord_vertex]

theorem medianMap_injective (T : Triangle) : Function.Injective T.medianMap := by
  intro p q hpq
  have hx := congrArg (T.coord 1) hpq
  have hy := congrArg (T.coord 2) hpq
  rw [(T.medianMap_coords p).1, (T.medianMap_coords q).1] at hx
  rw [(T.medianMap_coords p).2, (T.medianMap_coords q).2] at hy
  apply T.ext_coords <;> linarith

noncomputable def firstHalf (T : Triangle) : Triangle := T.map T.medianMap T.medianMap_injective

noncomputable def secondHalf (T : Triangle) : Triangle :=
  firstHalf (T.reindex (Equiv.swap 0 1))

theorem firstHalf_points (T : Triangle) :
    T.firstHalf.points = ![T.points 2, T.points 0, midpoint ℝ (T.points 0) (T.points 1)] := by
  funext i
  change T.medianMap (T.points i) = _
  rw [medianMap_apply]
  fin_cases i <;> simp [coord_vertex, latticeShift, edgeVector, midpoint_eq_smul_add,
    invOf_eq_inv]
  module

theorem secondHalf_points (T : Triangle) :
    T.secondHalf.points = ![T.points 2, T.points 1, midpoint ℝ (T.points 0) (T.points 1)] := by
  have hs : (Equiv.swap (0 : Fin 3) 1) 2 = 2 := by decide
  rw [secondHalf, firstHalf_points]
  funext i
  fin_cases i <;> simp [Affine.Simplex.reindex, hs, midpoint_comm]

theorem coord_midpoint (T : Triangle) :
    T.coord 1 (midpoint ℝ (T.points 0) (T.points 1)) = 1 / 2 ∧
      T.coord 2 (midpoint ℝ (T.points 0) (T.points 1)) = 0 := by
  rw [AffineMap.map_midpoint, AffineMap.map_midpoint]
  simp [coord_vertex, midpoint_eq_smul_add, invOf_eq_inv]

theorem firstHalf_coords (T : Triangle) (p : Plane) :
    T.coord 1 p = (1 / 2 : ℝ) * T.firstHalf.coord 2 p ∧
      T.coord 2 p = 1 - T.firstHalf.coord 1 p - T.firstHalf.coord 2 p := by
  have hx := T.firstHalf.affine_scalar_interpolation (T.coord 1) p
  have hy := T.firstHalf.affine_scalar_interpolation (T.coord 2) p
  simp only [firstHalf_points] at hx hy
  have hx' : T.coord 1 p = (1 / 2 : ℝ) * T.firstHalf.coord 2 p := by
    simpa [coord_vertex, (T.coord_midpoint).1] using hx
  have hy' : T.coord 2 p = T.firstHalf.coord 0 p := by
    simpa [coord_vertex, (T.coord_midpoint).2] using hy
  exact ⟨hx', by linarith [T.firstHalf.coord_sum p]⟩

theorem secondHalf_coords (T : Triangle) (p : Plane) :
    T.coord 1 p = T.secondHalf.coord 1 p + (1 / 2 : ℝ) * T.secondHalf.coord 2 p ∧
      T.coord 2 p = 1 - T.secondHalf.coord 1 p - T.secondHalf.coord 2 p := by
  have hx := T.secondHalf.affine_scalar_interpolation (T.coord 1) p
  have hy := T.secondHalf.affine_scalar_interpolation (T.coord 2) p
  simp only [secondHalf_points] at hx hy
  have hx' : T.coord 1 p = T.secondHalf.coord 1 p + (1 / 2 : ℝ) * T.secondHalf.coord 2 p := by
    simpa [coord_vertex, (T.coord_midpoint).1] using hx
  have hy' : T.coord 2 p = T.secondHalf.coord 0 p := by
    simpa [coord_vertex, (T.coord_midpoint).2] using hy
  exact ⟨hx', by linarith [T.secondHalf.coord_sum p]⟩

theorem mem_firstHalf_support (T : Triangle) (p : Plane) :
    p ∈ T.firstHalf.support ↔
      0 ≤ T.coord 1 p ∧ 0 ≤ T.coord 2 p ∧ 2 * T.coord 1 p + T.coord 2 p ≤ 1 := by
  rw [mem_support_iff_coords]
  obtain ⟨hx, hy⟩ := T.firstHalf_coords p
  constructor <;> rintro ⟨h1, h2, h3⟩ <;> exact ⟨by linarith, by linarith, by linarith⟩

theorem mem_secondHalf_support (T : Triangle) (p : Plane) :
    p ∈ T.secondHalf.support ↔
      0 ≤ T.coord 2 p ∧ T.coord 1 p + T.coord 2 p ≤ 1 ∧ 1 ≤ 2 * T.coord 1 p + T.coord 2 p := by
  rw [mem_support_iff_coords]
  obtain ⟨hx, hy⟩ := T.secondHalf_coords p
  constructor <;> rintro ⟨h1, h2, h3⟩ <;> exact ⟨by linarith, by linarith, by linarith⟩

theorem halves_cover (T : Triangle) : T.firstHalf.support ∪ T.secondHalf.support = T.support := by
  ext p
  rw [Set.mem_union, mem_firstHalf_support, mem_secondHalf_support, mem_support_iff_coords]
  constructor
  · rintro (⟨hx, hy, h⟩ | ⟨hy, hsum, h⟩)
    · exact ⟨hx, hy, by linarith⟩
    · exact ⟨by linarith, hy, hsum⟩
  · rintro ⟨hx, hy, hsum⟩
    by_cases h : 2 * T.coord 1 p + T.coord 2 p ≤ 1
    · exact Or.inl ⟨hx, hy, h⟩
    · exact Or.inr ⟨hy, hsum, le_of_not_ge h⟩

theorem halves_disjoint_interiors (T : Triangle) :
    Disjoint (interior T.firstHalf.support) (interior T.secondHalf.support) := by
  have hR : T.firstHalf.support ⊆ {p | T.coordForm 2 1 p ≤ 1} := by
    intro p hp
    change T.coordForm 2 1 p ≤ 1
    simpa only [coordForm_apply, one_mul] using ((T.mem_firstHalf_support p).mp hp).2.2
  have hS : T.secondHalf.support ⊆ {p | 1 ≤ T.coordForm 2 1 p} := by
    intro p hp
    change 1 ≤ T.coordForm 2 1 p
    simpa only [coordForm_apply, one_mul] using ((T.mem_secondHalf_support p).mp hp).2.2
  have hiR := interior_mono hR
  have hiS := interior_mono hS
  rw [T.interior_coordForm_le 2 1 1 (Or.inr one_ne_zero)] at hiR
  rw [T.interior_coordForm_ge 2 1 1 (Or.inr one_ne_zero)] at hiS
  apply Set.disjoint_left.mpr
  intro p hp hq
  have hfirst := hiR hp
  have hsecond := hiS hq
  change T.coordForm 2 1 p < 1 at hfirst
  change 1 < T.coordForm 2 1 p at hsecond
  exact lt_asymm hfirst hsecond

end Erdos633b.Triangle
