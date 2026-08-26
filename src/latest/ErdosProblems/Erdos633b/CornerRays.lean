import ErdosProblems.Erdos633b.BoundaryTopology

/-! Radial projection from a triangle vertex to the opposite side.
These geometric coordinates prepare the finite corner-angle partition. -/

namespace Erdos633b.Triangle

theorem coord_homothety_vertex (T : Triangle) (i j : Fin 3) (r : ℝ) (p : Plane) :
    T.coord j (AffineMap.homothety (T.points i) r p) =
      r * (T.coord j p - T.coord j (T.points i)) + T.coord j (T.points i) := by
  rw [AffineMap.homothety_apply, AffineMap.map_vadd, map_smul, AffineMap.linearMap_vsub]
  rfl

noncomputable def cornerScale (T : Triangle) (i : Fin 3) (p : Plane) : ℝ :=
  1 - T.coord i p

noncomputable def cornerProject (T : Triangle) (i : Fin 3) (p : Plane) : Plane :=
  AffineMap.homothety (T.points i) (T.cornerScale i p)⁻¹ p

theorem cornerScale_pos (T : Triangle) (i : Fin 3) {p : Plane} (hp : p ∈ T.support)
    (hne : p ≠ T.points i) : 0 < T.cornerScale i p := by
  have hlt : T.coord i p < 1 := lt_of_le_of_ne (T.coord_le_one hp i)
    (fun h => hne (T.eq_vertex_of_coord_eq_one hp i h))
  exact sub_pos.mpr hlt

theorem cornerScale_le_one (T : Triangle) (i : Fin 3) {p : Plane} (hp : p ∈ T.support) :
    T.cornerScale i p ≤ 1 := sub_le_self _ (T.coord_nonneg hp i)

theorem cornerProject_coord_self (T : Triangle) (i : Fin 3) {p : Plane}
    (hp : p ∈ T.support) (hne : p ≠ T.points i) : T.coord i (T.cornerProject i p) = 0 := by
  have hs := (T.cornerScale_pos i hp hne).ne'
  rw [cornerProject, coord_homothety_vertex, coord_vertex, if_pos rfl]
  change (1 - T.coord i p)⁻¹ * (T.coord i p - 1) + 1 = 0
  change 1 - T.coord i p ≠ 0 at hs
  field_simp
  ring

theorem cornerProject_coord_other (T : Triangle) (i j : Fin 3) (hj : j ≠ i) (p : Plane) :
    T.coord j (T.cornerProject i p) = T.coord j p / T.cornerScale i p := by
  rw [cornerProject, coord_homothety_vertex, coord_vertex, if_neg hj]
  simp only [sub_zero, add_zero, div_eq_mul_inv, mul_comm]

theorem cornerProject_mem_edge (T : Triangle) (i : Fin 3) {p : Plane}
    (hp : p ∈ T.support) (hne : p ≠ T.points i) : T.cornerProject i p ∈ T.edge i := by
  refine ⟨(T.mem_support_iff_all_coords _).mpr ?_, T.cornerProject_coord_self i hp hne⟩
  intro j
  by_cases hj : j = i
  · rw [hj, T.cornerProject_coord_self i hp hne]
  · rw [T.cornerProject_coord_other i j hj]
    exact div_nonneg (T.coord_nonneg hp j) (T.cornerScale_pos i hp hne).le

theorem cornerProject_reconstruct (T : Triangle) (i : Fin 3) {p : Plane}
    (hp : p ∈ T.support) (hne : p ≠ T.points i) :
    AffineMap.homothety (T.points i) (T.cornerScale i p) (T.cornerProject i p) = p := by
  rw [cornerProject, ← AffineMap.homothety_mul_apply,
    mul_inv_cancel₀ (T.cornerScale_pos i hp hne).ne', AffineMap.homothety_one]
  rfl

theorem cornerProject_of_edge (T : Triangle) (i : Fin 3) {p : Plane} (hp : p ∈ T.edge i) :
    T.cornerProject i p = p := by
  have hi : T.coord i p = 0 := hp.2
  simp only [cornerProject, cornerScale, hi, sub_zero, inv_one, AffineMap.homothety_one]
  rfl

theorem cornerScale_of_radial (T : Triangle) (i : Fin 3) {p : Plane} (hp : p ∈ T.edge i)
    (r : ℝ) : T.cornerScale i (AffineMap.homothety (T.points i) r p) = r := by
  rw [cornerScale, coord_homothety_vertex, coord_vertex, if_pos rfl, hp.2]
  ring

theorem cornerProject_of_radial (T : Triangle) (i : Fin 3) {p : Plane} (hp : p ∈ T.edge i)
    {r : ℝ} (hr : 0 < r) :
    T.cornerProject i (AffineMap.homothety (T.points i) r p) = p := by
  rw [cornerProject, T.cornerScale_of_radial i hp r, ← AffineMap.homothety_mul_apply,
    inv_mul_cancel₀ hr.ne', AffineMap.homothety_one]
  rfl

theorem cornerProject_mem_openEdge (T : Triangle) (i : Fin 3) {p : Plane}
    (hp : p ∈ interior T.support) : T.cornerProject i p ∈ T.openEdge i := by
  have hne : p ≠ T.points i := by
    intro h
    have hi := (T.mem_interior_support_iff_all_coords p).mp hp (i + 1)
    rw [h, coord_vertex, if_neg ((by decide : ∀ i : Fin 3, i + 1 ≠ i) i)] at hi
    exact lt_irrefl _ hi
  refine ⟨T.cornerProject_coord_self i (interior_subset hp) hne, ?_⟩
  intro j hj
  rw [T.cornerProject_coord_other i j hj]
  exact div_pos ((T.mem_interior_support_iff_all_coords p).mp hp j)
    (T.cornerScale_pos i (interior_subset hp) hne)

end Erdos633b.Triangle
