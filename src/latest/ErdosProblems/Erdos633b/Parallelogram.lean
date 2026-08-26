import ErdosProblems.Erdos633b.Rectangle

/-! Exact support of a rigidly placed finite parallelogram array. -/

namespace Erdos633b

namespace Triangle

theorem ext_coords (T : Triangle) {p q : Plane}
    (h1 : T.coord 1 p = T.coord 1 q) (h2 : T.coord 2 p = T.coord 2 q) : p = q := by
  apply T.affineBasis.ext_elem
  intro i
  fin_cases i
  · change T.coord 0 p = T.coord 0 q
    linarith [T.coord_sum p, T.coord_sum q]
  · exact h1
  · exact h2

theorem reconstruct (T : Triangle) (p : Plane) :
    T.latticeShift (T.coord 1 p) (T.coord 2 p) + T.points 0 = p := by
  apply T.ext_coords <;> simp [coord_shift_one, coord_shift_two, coord_vertex]

end Triangle

theorem affineMap_two_edges {V : Type*} [AddCommGroup V] [Module ℝ V]
    (f : Plane →ᵃ[ℝ] V) (Q E D : Plane) (u v : ℝ) :
    f (Q + u • (E - Q) + v • (D - Q)) =
      f Q + u • (f E - f Q) + v • (f D - f Q) := by
  rw [show Q + u • (E - Q) + v • (D - Q) =
    (u • (E -ᵥ Q) + v • (D -ᵥ Q)) +ᵥ Q by change _ = _ + Q; abel]
  rw [AffineMap.map_vadd, map_add, map_smul, map_smul,
    AffineMap.linearMap_vsub, AffineMap.linearMap_vsub]
  change u • (f E - f Q) + v • (f D - f Q) + f Q = _
  abel

theorem affineMap_latticeShift (T : Triangle) (g : Plane ≃ᵃⁱ[ℝ] Plane) (u v : ℝ) :
    g (T.latticeShift u v + T.points 0) =
      g (T.points 0) + u • (g (T.points 1) - g (T.points 0)) +
        v • (g (T.points 2) - g (T.points 0)) := by
  change g (u • (T.points 1 - T.points 0) + v • (T.points 2 - T.points 0) + T.points 0) = _
  rw [show u • (T.points 1 - T.points 0) + v • (T.points 2 - T.points 0) + T.points 0 =
      T.points 0 + u • (T.points 1 - T.points 0) + v • (T.points 2 - T.points 0) by abel]
  exact affineMap_two_edges g.toAffineMap (T.points 0) (T.points 1) (T.points 2) u v

def parallelogram (Q U V : Plane) : Set Plane :=
  {p | ∃ u v : ℝ, 0 ≤ u ∧ u ≤ 1 ∧ 0 ≤ v ∧ v ≤ 1 ∧ p = Q + u • U + v • V}

theorem rectangle_image (T : Triangle) (g : Plane ≃ᵃⁱ[ℝ] Plane) (m n : ℝ)
    (hm : 0 < m) (hn : 0 < n) :
    g '' {p | 0 ≤ T.coord 1 p ∧ T.coord 1 p ≤ m ∧ 0 ≤ T.coord 2 p ∧ T.coord 2 p ≤ n} =
      parallelogram (g (T.points 0))
        (m • (g (T.points 1) - g (T.points 0)))
        (n • (g (T.points 2) - g (T.points 0))) := by
  ext p
  constructor
  · rintro ⟨x, ⟨hx, hxm, hy, hyn⟩, rfl⟩
    refine ⟨T.coord 1 x / m, T.coord 2 x / n, div_nonneg hx hm.le,
      (div_le_one hm).mpr hxm, div_nonneg hy hn.le, (div_le_one hn).mpr hyn, ?_⟩
    have h := affineMap_latticeShift T g (T.coord 1 x) (T.coord 2 x)
    rw [T.reconstruct x] at h
    simpa only [smul_smul, div_mul_cancel₀ _ hm.ne', div_mul_cancel₀ _ hn.ne'] using h
  · rintro ⟨u, v, hu, hu1, hv, hv1, rfl⟩
    refine ⟨T.latticeShift (u * m) (v * n) + T.points 0, ?_, ?_⟩
    · simp only [Set.mem_ofPred_eq, Triangle.coord_shift_one, Triangle.coord_shift_two,
        Triangle.coord_vertex]
      have h1 : (1 : Fin 3) ≠ 0 := by decide
      have h2 : (2 : Fin 3) ≠ 0 := by decide
      simp only [h1, h2, if_false, add_zero]
      exact ⟨mul_nonneg hu hm.le, by nlinarith, mul_nonneg hv hn.le, by nlinarith⟩
    · rw [affineMap_latticeShift, smul_smul, smul_smul]

noncomputable def parallelogram_patch (T : Triangle) (g : Plane ≃ᵃⁱ[ℝ] Plane) (m n : ℕ)
    (hm : 0 < m) (hn : 0 < n) :
    Patch T (parallelogram (g (T.points 0))
      ((m : ℝ) • (g (T.points 1) - g (T.points 0)))
      ((n : ℝ) • (g (T.points 2) - g (T.points 0)))) (2 * m * n) := by
  have d := (rectangle_patch T m n hm hn).move g
  rwa [rectangle_image T g m n (by exact_mod_cast hm) (by exact_mod_cast hn)] at d

namespace Patch

/-- Changing the vertex order of the reference does not change any geometric piece. -/
def changeTile {R R' : Triangle} {S : Set Plane} {n : ℕ} (d : Patch R S n)
    (h : R.support = R'.support) : Patch R' S n where
  place := d.place
  covers := by simpa only [← h] using d.covers
  disjoint_interiors := by simpa only [← h] using d.disjoint_interiors

end Patch

end Erdos633b
