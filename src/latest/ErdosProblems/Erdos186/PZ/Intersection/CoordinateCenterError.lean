/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.PZ.Intersection.SideTarget

/-!
# Coordinatewise center errors

The source GAP widths are anisotropic.  These variants retain a separate
center-error allowance in every coordinate instead of replacing all widths
by their sum.
-/

namespace Erdos186.PZ.Intersection

noncomputable section

set_option autoImplicit false

theorem memCube_of_coordinate_center_error {d : ℕ}
    {center base : Fin d → ℝ} {radius : ℝ} {error : Fin d → ℝ}
    {z : LatticePoint d}
    (hz : MemCube center radius z)
    (herror : ∀ i, |center i - base i| ≤ error i) :
    ∀ i, |(z i : ℝ) - base i| ≤ radius + error i := by
  intro i
  calc
    |(z i : ℝ) - base i| =
        |((z i : ℝ) - center i) + (center i - base i)| := by
          congr 1
          ring
    _ ≤ |(z i : ℝ) - center i| + |center i - base i| :=
      abs_add_le _ _
    _ ≤ radius + error i := add_le_add (hz i) (herror i)

/-- Coordinate-box version of membership in the canonical
lattice-restricted target. -/
theorem mem_structuredZonotopeTargetIn_of_coordinateCube {d : ℕ}
    {lattice : Set (LatticePoint d)}
    {structured core : Finset (LatticePoint d)}
    {p₀ z : LatticePoint d} {q : LatticePoint d → ℝ}
    {radius : Fin d → ℝ}
    (hzL : z ∈ lattice) (hp₀ : p₀ ∈ structured)
    (hq : ∀ x ∈ core, 0 ≤ q x ∧ q x ≤ (1 : ℝ) / 2)
    (hthick : ∀ y : Fin d → ℝ, (∀ i, |y i| ≤ radius i) →
      y ∈ centeredZonotope core q)
    (hz : ∀ i,
      |(z i : ℝ) - (realVector p₀ + zonotopeCenter core q) i| ≤
        radius i) :
    z ∈ structuredZonotopeTargetIn lattice structured core := by
  rw [mem_structuredZonotopeTargetIn_iff]
  refine ⟨hzL, p₀, hp₀, z - p₀, ?_, by abel⟩
  apply mem_zonotope_of_sub_center_mem_centeredZonotope core q hq
  apply hthick
  intro i
  have hzi := hz i
  change |((((z - p₀) i : ℤ) : ℝ) - zonotopeCenter core q i)| ≤ radius i
  have heq : (((z - p₀) i : ℤ) : ℝ) - zonotopeCenter core q i =
      (z i : ℝ) - ((p₀ i : ℝ) + zonotopeCenter core q i) := by
    simp only [Pi.sub_apply, Int.cast_sub]
    ring
  rw [heq]
  simpa only [realVector, Pi.add_apply] using hzi

namespace IntersectionSideInput

variable {d : ℕ} {pool : Finset (LatticePoint d)}
    {a : LatticePoint d} {orientation : Orientation}

/-- Lemma 14 with a coordinate-dependent center error. -/
theorem lemma14TargetThickness_of_eq_structuredZonotopeTargetIn_coordinateCenterError
    (I : IntersectionSideInput pool a orientation)
    (structured : Finset (LatticePoint d)) (p₀ : LatticePoint d)
    (q : LatticePoint d → ℝ) (center : Fin d → ℝ)
    (radius : ℝ) (error : Fin d → ℝ)
    (htarget : I.target = structuredZonotopeTargetIn I.lattice
      structured I.roundingCore)
    (hp₀ : p₀ ∈ structured)
    (hcenterError : ∀ i,
      |center i - (realVector p₀ + zonotopeCenter I.roundingCore q) i| ≤
        error i)
    (hq : ∀ x ∈ I.roundingCore,
      0 ≤ q x ∧ q x ≤ (1 : ℝ) / 2)
    (hthick : ∀ y : Fin d → ℝ,
      (∀ i, |y i| ≤ radius + error i) →
      y ∈ centeredZonotope I.roundingCore q) :
    I.Lemma14TargetThickness center radius := by
  intro z hzL hz
  rw [htarget]
  apply mem_structuredZonotopeTargetIn_of_coordinateCube hzL hp₀ hq hthick
  exact memCube_of_coordinate_center_error hz hcenterError

end IntersectionSideInput

end

end Erdos186.PZ.Intersection
