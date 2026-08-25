import StackExchange.Puzzling139335.ThreeCorners.Rays

/-!
# The two outer endpoint configurations

The two supporting right cones at either outer pair of endpoint angles
confine the piece to a coordinate rectangle.  The far corner of that
rectangle belongs to the triangle `x + y ≤ 1`.  An interior frame center
would require both side lengths of the rectangle to exceed one half.

Only set membership and supporting-cone containment are used here.  No
connectedness, convexity, or boundary regularity is assumed.
-/

open Set

namespace Puzzling139335.N4Diagonal.Endpoint

noncomputable section

open ThreeCorners

/-- Coordinate bounds on a set become strict at every interior point. -/
theorem interior_coordinate_bounds {P : Set Plane} {p : Plane} {i : Fin 2}
    {a b : ℝ} (h : ∀ x ∈ P, x i ∈ Icc a b) (hp : p ∈ interior P) :
    p i ∈ Ioo a b := by
  have hsubset : P ⊆ (fun x : Plane => x i) ⁻¹' Icc a b := h
  have hmem := interior_mono hsubset hp
  have hpreimage : (fun x : Plane => x i) ⁻¹' interior (Icc a b) =
      interior ((fun x : Plane => x i) ⁻¹' Icc a b) :=
    IsOpenMap.preimage_interior_eq_interior_preimage
      (PiLp.isOpenMap_apply (p := 2) (β := fun _ : Fin 2 => ℝ) i)
      (PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) i) (Icc a b)
  rwa [← hpreimage, interior_Icc] at hmem

private theorem mem_supportCone_pi_div_two_iff (x v : Plane) :
    x ∈ supportCone v (Real.pi / 2) ↔ v 1 ≤ x 1 ∧ x 0 ≤ v 0 := by
  simp [supportCone, Schoenflies.Plane.inner_eq, ray, perpRay,
    sub_nonneg]

private theorem mem_supportCone_pi_iff (x v : Plane) :
    x ∈ supportCone v Real.pi ↔ x 0 ≤ v 0 ∧ x 1 ≤ v 1 := by
  simp [supportCone, Schoenflies.Plane.inner_eq, ray, perpRay,
    sub_nonneg]

private theorem mem_supportCone_three_pi_div_two_iff (x v : Plane) :
    x ∈ supportCone v (3 * Real.pi / 2) ↔ x 1 ≤ v 1 ∧ v 0 ≤ x 0 := by
  rw [show (3 * Real.pi / 2 : ℝ) = Real.pi + Real.pi / 2 by ring]
  simp [supportCone, Schoenflies.Plane.inner_eq, ray, perpRay,
    Real.cos_add_pi_div_two, Real.sin_add_pi_div_two, sub_nonneg]

/-- In the lower endpoint configuration, `B` is the bottom-right corner
and `C` the top-right corner of a rectangle containing the whole piece. -/
theorem outer_low_box_bounds {P : Set Plane} {B C : Plane}
    (htri : ∀ x ∈ P, 0 ≤ x 0 ∧ 0 ≤ x 1 ∧ x 0 + x 1 ≤ 1)
    (h0 : (0 : Plane) ∈ P) (hB : B ∈ P) (hC : C ∈ P)
    (hConeB : P ⊆ supportCone B (Real.pi / 2))
    (hConeC : P ⊆ supportCone C Real.pi) :
    B 1 = 0 ∧ C 0 = B 0 ∧
      ∀ x ∈ P, x 0 ∈ Icc (0 : ℝ) (C 0) ∧ x 1 ∈ Icc (0 : ℝ) (C 1) := by
  have hOrigin := (mem_supportCone_pi_div_two_iff 0 B).mp (hConeB h0)
  have hCB := (mem_supportCone_pi_div_two_iff C B).mp (hConeB hC)
  have hBC := (mem_supportCone_pi_iff B C).mp (hConeC hB)
  refine ⟨le_antisymm (by simpa using hOrigin.1) (htri B hB).2.1,
    le_antisymm hCB.2 hBC.1, ?_⟩
  intro x hx
  have h := (mem_supportCone_pi_iff x C).mp (hConeC hx)
  exact ⟨⟨(htri x hx).1, h.1⟩, ⟨(htri x hx).2.1, h.2⟩⟩

/-- Neither unit-square frame center is interior to the piece in the
lower outer endpoint configuration. -/
theorem outer_low_frameCenters_not_mem_interior {P : Set Plane} {B C : Plane}
    (htri : ∀ x ∈ P, 0 ≤ x 0 ∧ 0 ≤ x 1 ∧ x 0 + x 1 ≤ 1)
    (h0 : (0 : Plane) ∈ P) (hB : B ∈ P) (hC : C ∈ P)
    (hConeB : P ⊆ supportCone B (Real.pi / 2))
    (hConeC : P ⊆ supportCone C Real.pi) :
    B + (1 / 2 : ℝ) • (ray (Real.pi / 2) + perpRay (Real.pi / 2)) ∉ interior P ∧
      C + (1 / 2 : ℝ) • (ray Real.pi + perpRay Real.pi) ∉ interior P := by
  obtain ⟨hB1, hC0, hbox⟩ := outer_low_box_bounds htri h0 hB hC hConeB hConeC
  have hsum := (htri C hC).2.2
  constructor
  · intro hp
    have hx := (interior_coordinate_bounds (fun x hx => (hbox x hx).1) hp).1
    have hy := (interior_coordinate_bounds (fun x hx => (hbox x hx).2) hp).2
    simp [ray, perpRay, hB1] at hx hy
    linarith
  · intro hp
    have hx := (interior_coordinate_bounds (fun x hx => (hbox x hx).1) hp).1
    have hy := (interior_coordinate_bounds (fun x hx => (hbox x hx).2) hp).1
    simp [ray, perpRay] at hx hy
    linarith

/-- In the upper endpoint configuration, `B` is the top-right corner
and `C` the top-left corner of a rectangle containing the whole piece. -/
theorem outer_high_box_bounds {P : Set Plane} {B C : Plane}
    (htri : ∀ x ∈ P, 0 ≤ x 0 ∧ 0 ≤ x 1 ∧ x 0 + x 1 ≤ 1)
    (h0 : (0 : Plane) ∈ P) (hB : B ∈ P) (hC : C ∈ P)
    (hConeB : P ⊆ supportCone B Real.pi)
    (hConeC : P ⊆ supportCone C (3 * Real.pi / 2)) :
    C 0 = 0 ∧ B 1 = C 1 ∧
      ∀ x ∈ P, x 0 ∈ Icc (0 : ℝ) (B 0) ∧ x 1 ∈ Icc (0 : ℝ) (B 1) := by
  have hOrigin := (mem_supportCone_three_pi_div_two_iff 0 C).mp (hConeC h0)
  have hCB := (mem_supportCone_pi_iff C B).mp (hConeB hC)
  have hBC := (mem_supportCone_three_pi_div_two_iff B C).mp (hConeC hB)
  refine ⟨le_antisymm (by simpa using hOrigin.2) (htri C hC).1,
    le_antisymm hBC.1 hCB.2, ?_⟩
  intro x hx
  have h := (mem_supportCone_pi_iff x B).mp (hConeB hx)
  exact ⟨⟨(htri x hx).1, h.1⟩, ⟨(htri x hx).2.1, h.2⟩⟩

/-- Neither unit-square frame center is interior to the piece in the
upper outer endpoint configuration. -/
theorem outer_high_frameCenters_not_mem_interior {P : Set Plane} {B C : Plane}
    (htri : ∀ x ∈ P, 0 ≤ x 0 ∧ 0 ≤ x 1 ∧ x 0 + x 1 ≤ 1)
    (h0 : (0 : Plane) ∈ P) (hB : B ∈ P) (hC : C ∈ P)
    (hConeB : P ⊆ supportCone B Real.pi)
    (hConeC : P ⊆ supportCone C (3 * Real.pi / 2)) :
    B + (1 / 2 : ℝ) • (ray Real.pi + perpRay Real.pi) ∉ interior P ∧
      C + (1 / 2 : ℝ) •
        (ray (3 * Real.pi / 2) + perpRay (3 * Real.pi / 2)) ∉ interior P := by
  obtain ⟨hC0, hB1, hbox⟩ := outer_high_box_bounds htri h0 hB hC hConeB hConeC
  have hsum := (htri B hB).2.2
  constructor
  · intro hp
    have hx := (interior_coordinate_bounds (fun x hx => (hbox x hx).1) hp).1
    have hy := (interior_coordinate_bounds (fun x hx => (hbox x hx).2) hp).1
    simp [ray, perpRay] at hx hy
    linarith
  · intro hp
    have hx := (interior_coordinate_bounds (fun x hx => (hbox x hx).1) hp).2
    have hy := (interior_coordinate_bounds (fun x hx => (hbox x hx).2) hp).1
    have hang : (3 * Real.pi / 2 : ℝ) = Real.pi + Real.pi / 2 := by ring
    simp [ray, perpRay, hang, Real.cos_add_pi_div_two, Real.sin_add_pi_div_two,
      hC0] at hx hy
    linarith

end

end Puzzling139335.N4Diagonal.Endpoint
