import StackExchange.Puzzling139335.N4Diagonal.Defs
import StackExchange.Puzzling139335.RectangularHull.AxisBox

/-!
# The rectangle forced by the mixed endpoint angles

At angles `θ = 0` and `β = π / 2`, the two used intrinsic corners lie on
the positive coordinate axes and bound the prototype by their coordinate
rectangle. A center-containing singleton placement forces both side lengths
to exceed one half. The one-corner condition makes both lengths less than one.
-/

open Set

namespace Puzzling139335.N4Diagonal.Endpoint

open ThreeCorners RectangularHull

/-- Interior membership pulls back through an actual affine isometry. -/
theorem symm_mem_interior_of_mem_interior_image (e : Plane ≃ᵃⁱ[ℝ] Plane)
    {P : Set Plane} {x : Plane} (hx : x ∈ interior (e '' P)) :
    e.symm x ∈ interior P := by
  have himage : e '' interior P = interior (e '' P) := e.toHomeomorph.image_interior P
  rw [← himage] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  simpa only [e.symm_apply_apply] using hy

/-- The used vertices in the mixed endpoint case are on the bottom and left axes. -/
theorem mixed_zero_coordinates (m : Model) (hθ : m.θ = 0)
    (hβ : m.β = Real.pi / 2) : m.p 1 = 0 ∧ m.q 0 = 0 := by
  have hp : m.p 1 ≤ 0 := by
    have h := (m.first_support 0 m.origin_mem).1
    simpa [hθ, ray, perpRay, Schoenflies.Plane.inner_eq] using h
  have hq : m.q 0 ≤ 0 := by
    have h := (m.last_support 0 m.origin_mem).2
    simpa [hβ, ray, perpRay, Schoenflies.Plane.inner_eq] using h
  exact ⟨le_antisymm hp (m.triangle m.p_mem).2.1,
    le_antisymm hq (m.triangle m.q_mem).1⟩

theorem mixed_vertex_coordinates (m : Model) (hθ : m.θ = 0)
    (hβ : m.β = Real.pi / 2) :
    m.p = !₂[m.p 0, 0] ∧ m.q = !₂[0, m.q 1] := by
  obtain ⟨hp, hq⟩ := mixed_zero_coordinates m hθ hβ
  constructor <;> ext i <;> fin_cases i <;> simp [hp, hq]

/-- Both endpoint support cones bound the actual prototype by a coordinate rectangle. -/
theorem mixed_subset_axisBox (m : Model) (hθ : m.θ = 0)
    (hβ : m.β = Real.pi / 2) :
    m.P ⊆ closedAxisBox 0 (m.p 0) 0 (m.q 1) := by
  intro x hx
  have hxle : x 0 ≤ m.p 0 := by
    have h := (m.first_support x hx).2
    simpa [hθ, ray, perpRay, Schoenflies.Plane.inner_eq] using h
  have hyle : x 1 ≤ m.q 1 := by
    have h := (m.last_support x hx).1
    simpa [hβ, ray, perpRay, Schoenflies.Plane.inner_eq] using h
  exact ⟨⟨(m.triangle hx).1, hxle⟩, ⟨(m.triangle hx).2.1, hyle⟩⟩

/-- Neither side length can reach one, since that would give the prototype
a second square corner. -/
theorem mixed_side_lengths_lt_one (m : Model) (hθ : m.θ = 0)
    (hβ : m.β = Real.pi / 2) : m.p 0 < 1 ∧ m.q 1 < 1 := by
  obtain ⟨hp, hq⟩ := mixed_vertex_coordinates m hθ hβ
  have hpne : m.p 0 ≠ 1 := by
    intro hx
    have hcorner : m.p = corner 1 := by
      rw [hp, hx]
      norm_num [corner, Fin.ext_iff]
    have h := m.origin_only_corner 1 (hcorner ▸ m.p_mem)
    exact (by decide : (1 : Fin 4) ≠ 0) h
  have hqne : m.q 1 ≠ 1 := by
    intro hy
    have hcorner : m.q = corner 3 := by
      rw [hq, hy]
      norm_num [corner, Fin.ext_iff]
    have h := m.origin_only_corner 3 (hcorner ▸ m.q_mem)
    exact (by decide : (3 : Fin 4) ≠ 0) h
  exact ⟨lt_of_le_of_ne (m.subset_square m.p_mem).1.2 hpne,
    lt_of_le_of_ne (m.subset_square m.q_mem).2.2 hqne⟩

/-- If either actual singleton placement contains the center in its interior,
both sides of the prototype's endpoint rectangle are longer than one half. -/
theorem mixed_center_forces_large_sides (m : Model) (hθ : m.θ = 0)
    (hβ : m.β = Real.pi / 2)
    (hc : squareCenter ∈ interior (m.e '' m.P) ∨
      squareCenter ∈ interior (m.f '' m.P)) :
    (1 / 2 : ℝ) < m.p 0 ∧ (1 / 2 : ℝ) < m.q 1 := by
  obtain ⟨hp, hq⟩ := mixed_zero_coordinates m hθ hβ
  have hbox := mixed_subset_axisBox m hθ hβ
  rcases hc with he | hf
  · have hpre : m.e.symm squareCenter = !₂[m.p 0 - 1 / 2, (1 / 2 : ℝ)] := by
      rw [m.first_center]
      ext i
      fin_cases i <;> norm_num [hθ, hp, ray, perpRay, sub_eq_add_neg]
    have hi := symm_mem_interior_of_mem_interior_image m.e he
    obtain ⟨hleft, _, _, htop⟩ :=
      mem_interior_closedAxisBox.mp (interior_mono hbox hi)
    rw [hpre] at hleft htop
    change 0 < m.p 0 - 1 / 2 at hleft
    change (1 / 2 : ℝ) < m.q 1 at htop
    exact ⟨by linarith, htop⟩
  · have hpre : m.f.symm squareCenter = !₂[(1 / 2 : ℝ), m.q 1 - 1 / 2] := by
      rw [m.last_center]
      ext i
      fin_cases i <;> norm_num [hβ, hq, ray, perpRay]
    have hi := symm_mem_interior_of_mem_interior_image m.f hf
    obtain ⟨_, hright, hbottom, _⟩ :=
      mem_interior_closedAxisBox.mp (interior_mono hbox hi)
    rw [hpre] at hright hbottom
    change (1 / 2 : ℝ) < m.p 0 at hright
    change 0 < m.q 1 - 1 / 2 at hbottom
    exact ⟨hright, by linarith⟩

end Puzzling139335.N4Diagonal.Endpoint
