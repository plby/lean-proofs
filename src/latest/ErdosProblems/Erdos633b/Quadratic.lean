import ErdosProblems.Erdos633b.Barycentric
import ErdosProblems.Erdos633b.Grid
import ErdosProblems.Erdos633b.Scaling

/-! A complete geometric quadratic subdivision of every nondegenerate triangle. -/

namespace Erdos633b

theorem mem_motion_image_iff (g : Plane ≃ᵃⁱ[ℝ] Plane) (S : Set Plane) (p : Plane) :
    p ∈ g '' S ↔ g.symm p ∈ S := by
  constructor
  · rintro ⟨q, hq, rfl⟩
    simpa using hq
  · intro hp
    exact ⟨g.symm p, hp, g.apply_symm_apply p⟩

theorem mem_interior_motion_image_iff (g : Plane ≃ᵃⁱ[ℝ] Plane) (S : Set Plane) (p : Plane) :
    p ∈ interior (g '' S) ↔ g.symm p ∈ interior S := by
  have h : g '' interior S = interior (g '' S) := g.toHomeomorph.image_interior S
  rw [← h, mem_motion_image_iff]

namespace Triangle

noncomputable def upwardMotion (T : Triangle) (x y : ℝ) : Plane ≃ᵃⁱ[ℝ] Plane :=
  AffineIsometryEquiv.constVAdd ℝ Plane (T.latticeShift x y)

noncomputable def downwardMotion (T : Triangle) (x y : ℝ) : Plane ≃ᵃⁱ[ℝ] Plane :=
  (AffineIsometryEquiv.pointReflection ℝ (T.points 0)).trans (T.upwardMotion (x + 1) (y + 1))

theorem upward_coord_one (T : Triangle) (x y : ℝ) (p : Plane) :
    T.coord 1 (T.upwardMotion x y p) = x + T.coord 1 p := T.coord_shift_one x y p

theorem upward_coord_two (T : Triangle) (x y : ℝ) (p : Plane) :
    T.coord 2 (T.upwardMotion x y p) = y + T.coord 2 p := T.coord_shift_two x y p

theorem downward_coord_one (T : Triangle) (x y : ℝ) (p : Plane) :
    T.coord 1 (T.downwardMotion x y p) = x + 1 - T.coord 1 p := by
  change T.coord 1 (T.upwardMotion (x + 1) (y + 1)
    (AffineIsometryEquiv.pointReflection ℝ (T.points 0) p)) = _
  rw [upward_coord_one, coord_reflect_origin, coord_vertex]
  norm_num
  ring

theorem downward_coord_two (T : Triangle) (x y : ℝ) (p : Plane) :
    T.coord 2 (T.downwardMotion x y p) = y + 1 - T.coord 2 p := by
  change T.coord 2 (T.upwardMotion (x + 1) (y + 1)
    (AffineIsometryEquiv.pointReflection ℝ (T.points 0) p)) = _
  rw [upward_coord_two, coord_reflect_origin, coord_vertex]
  simp only [show (2 : Fin 3) ≠ 0 by decide, if_false, mul_zero]
  ring

theorem upward_inverse_coords (T : Triangle) (x y : ℝ) (p : Plane) :
    T.coord 1 ((T.upwardMotion x y).symm p) = T.coord 1 p - x ∧
      T.coord 2 ((T.upwardMotion x y).symm p) = T.coord 2 p - y := by
  have h1 := T.upward_coord_one x y ((T.upwardMotion x y).symm p)
  have h2 := T.upward_coord_two x y ((T.upwardMotion x y).symm p)
  rw [AffineIsometryEquiv.apply_symm_apply] at h1 h2
  exact ⟨by linarith, by linarith⟩

theorem downward_inverse_coords (T : Triangle) (x y : ℝ) (p : Plane) :
    T.coord 1 ((T.downwardMotion x y).symm p) = x + 1 - T.coord 1 p ∧
      T.coord 2 ((T.downwardMotion x y).symm p) = y + 1 - T.coord 2 p := by
  have h1 := T.downward_coord_one x y ((T.downwardMotion x y).symm p)
  have h2 := T.downward_coord_two x y ((T.downwardMotion x y).symm p)
  rw [AffineIsometryEquiv.apply_symm_apply] at h1 h2
  exact ⟨by linarith, by linarith⟩

theorem mem_upward_image (T : Triangle) (x y : ℝ) (p : Plane) :
    p ∈ T.upwardMotion x y '' T.support ↔
      x ≤ T.coord 1 p ∧ y ≤ T.coord 2 p ∧ T.coord 1 p + T.coord 2 p ≤ x + y + 1 := by
  rw [mem_motion_image_iff, mem_support_iff_coords,
    (T.upward_inverse_coords x y p).1, (T.upward_inverse_coords x y p).2]
  constructor <;> rintro ⟨h1, h2, h3⟩ <;>
    exact ⟨by linarith, by linarith, by linarith⟩

theorem mem_downward_image (T : Triangle) (x y : ℝ) (p : Plane) :
    p ∈ T.downwardMotion x y '' T.support ↔
      T.coord 1 p ≤ x + 1 ∧ T.coord 2 p ≤ y + 1 ∧ x + y + 1 ≤ T.coord 1 p + T.coord 2 p := by
  rw [mem_motion_image_iff, mem_support_iff_coords,
    (T.downward_inverse_coords x y p).1, (T.downward_inverse_coords x y p).2]
  constructor <;> rintro ⟨h1, h2, h3⟩ <;>
    exact ⟨by linarith, by linarith, by linarith⟩

theorem mem_interior_upward_image (T : Triangle) (x y : ℝ) (p : Plane) :
    p ∈ interior (T.upwardMotion x y '' T.support) ↔
      x < T.coord 1 p ∧ y < T.coord 2 p ∧ T.coord 1 p + T.coord 2 p < x + y + 1 := by
  rw [mem_interior_motion_image_iff, mem_interior_support_iff_coords,
    (T.upward_inverse_coords x y p).1, (T.upward_inverse_coords x y p).2]
  constructor <;> rintro ⟨h1, h2, h3⟩ <;>
    exact ⟨by linarith, by linarith, by linarith⟩

theorem mem_interior_downward_image (T : Triangle) (x y : ℝ) (p : Plane) :
    p ∈ interior (T.downwardMotion x y '' T.support) ↔
      T.coord 1 p < x + 1 ∧ T.coord 2 p < y + 1 ∧ x + y + 1 < T.coord 1 p + T.coord 2 p := by
  rw [mem_interior_motion_image_iff, mem_interior_support_iff_coords,
    (T.downward_inverse_coords x y p).1, (T.downward_inverse_coords x y p).2]
  constructor <;> rintro ⟨h1, h2, h3⟩ <;>
    exact ⟨by linarith, by linarith, by linarith⟩

theorem coord_homothety (T : Triangle) (i : Fin 3) (r : ℝ) (p : Plane) :
    T.coord i (AffineMap.homothety (T.points 0) r p) =
      r * (T.coord i p - T.coord i (T.points 0)) + T.coord i (T.points 0) := by
  rw [AffineMap.homothety_apply, AffineMap.map_vadd, map_smul, AffineMap.linearMap_vsub]
  rfl

theorem coord_homothety_one (T : Triangle) (r : ℝ) (p : Plane) :
    T.coord 1 (AffineMap.homothety (T.points 0) r p) = r * T.coord 1 p := by
  simp [coord_homothety, coord_vertex]

theorem coord_homothety_two (T : Triangle) (r : ℝ) (p : Plane) :
    T.coord 2 (AffineMap.homothety (T.points 0) r p) = r * T.coord 2 p := by
  simp [coord_homothety, coord_vertex]

theorem mem_homothetic_support (T : Triangle) (r : ℝ) (hr : 0 < r) (p : Plane) :
    p ∈ (T.homothetic (T.points 0) r hr.ne').support ↔
      0 ≤ T.coord 1 p ∧ 0 ≤ T.coord 2 p ∧ T.coord 1 p + T.coord 2 p ≤ r := by
  rw [support_homothetic]
  constructor
  · rintro ⟨q, hq, rfl⟩
    rw [mem_support_iff_coords] at hq
    rw [coord_homothety_one, coord_homothety_two]
    exact ⟨mul_nonneg hr.le hq.1, mul_nonneg hr.le hq.2.1, by nlinarith [hq.2.2]⟩
  · rintro ⟨h1, h2, h3⟩
    let q := AffineMap.homothety (T.points 0) r⁻¹ p
    have he : AffineMap.homothety (T.points 0) r q = p := by
      dsimp [q]
      rw [← AffineMap.homothety_mul_apply, mul_inv_cancel₀ hr.ne', AffineMap.homothety_one]
      rfl
    have hq1 : r * T.coord 1 q = T.coord 1 p := by rw [← coord_homothety_one, he]
    have hq2 : r * T.coord 2 q = T.coord 2 p := by rw [← coord_homothety_two, he]
    refine ⟨q, (T.mem_support_iff_coords q).mpr ?_, he⟩
    exact ⟨by nlinarith, by nlinarith, by nlinarith⟩

end Triangle

namespace GridCell

noncomputable def motion {n : ℕ} (c : GridCell n) (T : Triangle) : Plane ≃ᵃⁱ[ℝ] Plane :=
  match c with
  | .inl p => T.upwardMotion p.val.1 p.val.2
  | .inr p => T.downwardMotion p.val.1 p.val.2

theorem mem_piece {n : ℕ} (c : GridCell n) (T : Triangle) (p : Plane) :
    p ∈ c.motion T '' T.support ↔ c.Closed (T.coord 1 p) (T.coord 2 p) := by
  cases c with
  | inl q => exact T.mem_upward_image q.val.1 q.val.2 p
  | inr q => exact T.mem_downward_image q.val.1 q.val.2 p

theorem mem_interior_piece {n : ℕ} (c : GridCell n) (T : Triangle) (p : Plane) :
    p ∈ interior (c.motion T '' T.support) ↔ c.Inside (T.coord 1 p) (T.coord 2 p) := by
  cases c with
  | inl q => exact T.mem_interior_upward_image q.val.1 q.val.2 p
  | inr q => exact T.mem_interior_downward_image q.val.1 q.val.2 p

theorem covers (T : Triangle) (n : ℕ) (hn : 0 < n) :
    (⋃ c : GridCell n, c.motion T '' T.support) =
      (T.homothetic (T.points 0) n (by exact_mod_cast hn.ne')).support := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  ext p
  rw [Triangle.mem_homothetic_support T n hn', Set.mem_iUnion]
  constructor
  · rintro ⟨c, hc⟩
    exact c.closed_subset ((c.mem_piece T p).mp hc)
  · rintro ⟨h1, h2, h3⟩
    obtain ⟨c, hc⟩ := exists_closed n hn (T.coord 1 p) (T.coord 2 p) h1 h2 h3
    exact ⟨c, (c.mem_piece T p).mpr hc⟩

theorem disjoint_interiors (T : Triangle) (n : ℕ) :
    Pairwise fun c d : GridCell n =>
      Disjoint (interior (c.motion T '' T.support)) (interior (d.motion T '' T.support)) := by
  intro c d hcd
  apply Set.disjoint_left.mpr
  intro p hc hd
  exact hcd (inside_unique c d ((c.mem_interior_piece T p).mp hc)
    ((d.mem_interior_piece T p).mp hd))

end GridCell

/-- An integer enlargement is dissected into copies of the original triangle. -/
theorem quadratic_enlargement (T : Triangle) (n : ℕ) (hn : 0 < n) :
    ∃ d : Tiling (T.homothetic (T.points 0) n (by exact_mod_cast hn.ne')) (n ^ 2),
      d.tile = T := by
  classical
  let d := Tiling.ofFintype _ T (fun c : GridCell n => c.motion T)
    (GridCell.covers T n hn) (GridCell.disjoint_interiors T n)
  have ha := d.area_eq_mul
  change (T.homothetic (T.points 0) n _).area = (Fintype.card (GridCell n) : ℝ) * T.area at ha
  rw [Triangle.area_homothetic] at ha
  have hc : Fintype.card (GridCell n) = n ^ 2 := by
    have h : (n : ℝ) ^ 2 = (Fintype.card (GridCell n) : ℝ) :=
      mul_right_cancel₀ T.area_pos.ne' ha
    exact_mod_cast h.symm
  rw [← hc]
  exact ⟨d, rfl⟩

/-- Every nondegenerate triangle admits every positive square tile count. -/
theorem quadratic_tiling (T : Triangle) (n : ℕ) (hn : 0 < n) :
    Nonempty (Tiling T (n ^ 2)) := by
  obtain ⟨d, _⟩ := quadratic_enlargement T n hn
  have hr : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have d' := d.homothetic (T.points 0) (n : ℝ)⁻¹ (inv_ne_zero hr)
  rw [Triangle.homothetic_inv] at d'
  exact ⟨d'⟩

end Erdos633b
