import ErdosProblems.Erdos633b.CornerRays

/-! Coordinates of an incident triangle after radial projection from its
shared outer corner. The omitted coordinate may have any vertex index. -/

namespace Erdos633b.Triangle

theorem coord_sum_cyclic (T : Triangle) (i : Fin 3) (p : Plane) :
    T.coord i p + T.coord (i + 1) p + T.coord (i + 2) p = 1 := by
  have h := T.coord_sum p
  fin_cases i
  · exact h
  · change T.coord 1 p + T.coord 2 p + T.coord 0 p = 1
    linarith
  · change T.coord 2 p + T.coord 0 p + T.coord 1 p = 1
    linarith

theorem affine_scalar_interpolation_cyclic (T : Triangle) (i : Fin 3)
    (f : Plane →ᵃ[ℝ] ℝ) (p : Plane) :
    f p = f (T.points i) * T.coord i p +
      f (T.points (i + 1)) * T.coord (i + 1) p +
      f (T.points (i + 2)) * T.coord (i + 2) p := by
  have h := T.affine_scalar_interpolation f p
  fin_cases i
  · exact h
  · change f p = f (T.points 1) * T.coord 1 p + f (T.points 2) * T.coord 2 p +
      f (T.points 0) * T.coord 0 p
    linarith
  · change f p = f (T.points 2) * T.coord 2 p + f (T.points 0) * T.coord 0 p +
      f (T.points 1) * T.coord 1 p
    linarith

theorem ext_coords_cyclic (T : Triangle) (i : Fin 3) {p q : Plane}
    (h1 : T.coord (i + 1) p = T.coord (i + 1) q)
    (h2 : T.coord (i + 2) p = T.coord (i + 2) q) : p = q := by
  apply T.affineBasis.ext_elem
  intro k
  change T.coord k p = T.coord k q
  have hp := T.coord_sum_cyclic i p
  have hq := T.coord_sum_cyclic i q
  have hk := (by decide : ∀ i k : Fin 3, k = i ∨ k = i + 1 ∨ k = i + 2) i k
  rcases hk with rfl | rfl | rfl
  · linarith
  · exact h1
  · exact h2

theorem coord_cornerProject_shared (T S : Triangle) (i j k : Fin 3)
    (hO : S.points j = T.points i) (hkj : k ≠ j) (p : Plane) :
    S.coord k (T.cornerProject i p) = S.coord k p / T.cornerScale i p := by
  rw [cornerProject, ← hO, S.coord_homothety_vertex, S.coord_vertex, if_neg hkj]
  simp only [sub_zero, add_zero, div_eq_mul_inv, mul_comm]

theorem corner_other_ne (T S : Triangle) (i j k : Fin 3)
    (hO : S.points j = T.points i) (hkj : k ≠ j) : S.points k ≠ T.points i := by
  rw [← hO]
  exact S.independent.injective.ne hkj

theorem corner_section_scale_identity (T S : Triangle) (i j : Fin 3)
    (hO : S.points j = T.points i) {q : Plane} (hq : q ∈ T.edge i) :
    T.cornerScale i (S.points (j + 1)) * S.coord (j + 1) q +
      T.cornerScale i (S.points (j + 2)) * S.coord (j + 2) q = 1 := by
  have h := S.affine_scalar_interpolation_cyclic j (T.coord i) q
  have hs := S.coord_sum_cyclic j q
  have hq0 : T.coord i q = 0 := hq.2
  rw [hq0, hO, T.coord_vertex, if_pos rfl, one_mul] at h
  dsimp only [cornerScale]
  nlinarith

theorem cornerProject_pair_coords (T S : Triangle) (i j : Fin 3)
    (hO : S.points j = T.points i) :
    S.coord (j + 1) (T.cornerProject i (S.points (j + 1))) =
        (T.cornerScale i (S.points (j + 1)))⁻¹ ∧
    S.coord (j + 2) (T.cornerProject i (S.points (j + 1))) = 0 ∧
    S.coord (j + 1) (T.cornerProject i (S.points (j + 2))) = 0 ∧
    S.coord (j + 2) (T.cornerProject i (S.points (j + 2))) =
        (T.cornerScale i (S.points (j + 2)))⁻¹ := by
  have h1 : j + 1 ≠ j := (by decide : ∀ j : Fin 3, j + 1 ≠ j) j
  have h2 : j + 2 ≠ j := (by decide : ∀ j : Fin 3, j + 2 ≠ j) j
  have h12 : j + 1 ≠ j + 2 := (by decide : ∀ j : Fin 3, j + 1 ≠ j + 2) j
  simp [T.coord_cornerProject_shared S i j (j + 1) hO h1,
    T.coord_cornerProject_shared S i j (j + 2) hO h2,
    coord_vertex, h12, h12.symm]

theorem cornerProject_pair_ne (T S : Triangle) (hST : S.support ⊆ T.support)
    (i j : Fin 3) (hO : S.points j = T.points i) :
    T.cornerProject i (S.points (j + 1)) ≠ T.cornerProject i (S.points (j + 2)) := by
  have h1 : j + 1 ≠ j := (by decide : ∀ j : Fin 3, j + 1 ≠ j) j
  have hu := T.cornerScale_pos i (hST (S.vertex_mem_support (j + 1)))
    (T.corner_other_ne S i j (j + 1) hO h1)
  obtain ⟨hA, _, hB, _⟩ := T.cornerProject_pair_coords S i j hO
  intro he
  rw [he, hB] at hA
  exact (inv_pos.mpr hu).ne' hA.symm

end Erdos633b.Triangle
