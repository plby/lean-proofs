import ErdosProblems.Erdos633b.Area
import Mathlib.Topology.Algebra.ConstMulAction
import Mathlib.Tactic.Module

/-! Homothetic transport of actual congruent-triangle dissections. -/

open scoped ENNReal
open MeasureTheory

namespace Erdos633b

namespace Triangle

noncomputable def dilate (T : Triangle) (r : ℝ) (hr : r ≠ 0) : Triangle :=
  T.map (AffineMap.homothety (0 : Plane) r) (AffineMap.homothety_injective 0 hr)

theorem dilate_points (T : Triangle) (r : ℝ) (hr : r ≠ 0) (i : Fin 3) :
    (T.dilate r hr).points i = r • T.points i := by
  simp [dilate, Affine.Simplex.map, AffineMap.homothety_apply]

theorem support_dilate (T : Triangle) (r : ℝ) (hr : r ≠ 0) :
    (T.dilate r hr).support = (fun x : Plane => r • x) '' T.support := by
  change convexHull ℝ (Set.range ((AffineMap.homothety (0 : Plane) r) ∘ T.points)) = _
  rw [Set.range_comp, ← AffineMap.image_convexHull]
  simp only [AffineMap.coe_homothety, vsub_eq_sub, sub_zero, vadd_eq_add, add_zero, support]

theorem dilate_inv (T : Triangle) (r : ℝ) (hr : r ≠ 0) :
    (T.dilate r hr).dilate r⁻¹ (inv_ne_zero hr) = T := by
  apply Affine.Simplex.ext
  intro i
  simp only [dilate_points, smul_smul, inv_mul_cancel₀ hr, one_smul]

theorem volume_support_dilate (T : Triangle) (r : ℝ) (hr : r ≠ 0) :
    volume (T.dilate r hr).support = ENNReal.ofReal (r ^ 2) * volume T.support := by
  rw [support_dilate]
  have h := Measure.addHaar_image_homothety (volume : Measure Plane) (0 : Plane) r T.support
  have hd : Module.finrank ℝ Plane = 2 := by simp [Plane]
  simpa only [hd, abs_sq, AffineMap.coe_homothety, vsub_eq_sub, sub_zero,
    vadd_eq_add, add_zero] using h

theorem area_dilate (T : Triangle) (r : ℝ) (hr : r ≠ 0) :
    (T.dilate r hr).area = r ^ 2 * T.area := by
  have h := congrArg ENNReal.toReal (T.volume_support_dilate r hr)
  simpa only [area, ENNReal.toReal_mul, ENNReal.toReal_ofReal (sq_nonneg r)] using h

noncomputable def homothetic (T : Triangle) (c : Plane) (r : ℝ) (hr : r ≠ 0) : Triangle :=
  (T.dilate r hr).move (AffineIsometryEquiv.constVAdd ℝ Plane ((1 - r) • c))

theorem homothetic_points (T : Triangle) (c : Plane) (r : ℝ) (hr : r ≠ 0) (i : Fin 3) :
    (T.homothetic c r hr).points i = AffineMap.homothety c r (T.points i) := by
  change (1 - r) • c + (T.dilate r hr).points i = _
  rw [dilate_points, AffineMap.homothety_apply]
  simp only [vsub_eq_sub, vadd_eq_add]
  module

theorem support_homothetic (T : Triangle) (c : Plane) (r : ℝ) (hr : r ≠ 0) :
    (T.homothetic c r hr).support = AffineMap.homothety c r '' T.support := by
  have he : (T.homothetic c r hr).points = (AffineMap.homothety c r) ∘ T.points := by
    funext i
    exact homothetic_points T c r hr i
  rw [support, he, Set.range_comp]
  exact ((AffineMap.homothety c r).image_convexHull (Set.range T.points)).symm

theorem homothetic_inv (T : Triangle) (c : Plane) (r : ℝ) (hr : r ≠ 0) :
    (T.homothetic c r hr).homothetic c r⁻¹ (inv_ne_zero hr) = T := by
  apply Affine.Simplex.ext
  intro i
  rw [homothetic_points, homothetic_points, ← AffineMap.homothety_mul_apply,
    inv_mul_cancel₀ hr, AffineMap.homothety_one]
  rfl

theorem area_homothetic (T : Triangle) (c : Plane) (r : ℝ) (hr : r ≠ 0) :
    (T.homothetic c r hr).area = r ^ 2 * T.area := by
  have hd : Module.finrank ℝ Plane = 2 := by simp [Plane]
  have h := Measure.addHaar_image_homothety (volume : Measure Plane) c r T.support
  rw [hd, abs_sq, ← support_homothetic T c r hr] at h
  have h' := congrArg ENNReal.toReal h
  simpa only [area, ENNReal.toReal_mul, ENNReal.toReal_ofReal (sq_nonneg r)] using h'

end Triangle

noncomputable def dilatedMotion (g : Plane ≃ᵃⁱ[ℝ] Plane) (r : ℝ) :
    Plane ≃ᵃⁱ[ℝ] Plane :=
  g.linearIsometryEquiv.toAffineIsometryEquiv.trans
    (AffineIsometryEquiv.constVAdd ℝ Plane (r • g 0))

theorem dilatedMotion_smul (g : Plane ≃ᵃⁱ[ℝ] Plane) (r : ℝ) (x : Plane) :
    dilatedMotion g r (r • x) = r • g x := by
  have h : g x = g.linearIsometryEquiv x + g 0 := by simpa using g.map_vadd 0 x
  simp [dilatedMotion, h, smul_add, add_comm]

theorem dilatedMotion_image (g : Plane ≃ᵃⁱ[ℝ] Plane) (r : ℝ) (S : Set Plane) :
    dilatedMotion g r '' ((fun x : Plane => r • x) '' S) =
      (fun x : Plane => r • x) '' (g '' S) := by
  simp only [Set.image_image, dilatedMotion_smul]

namespace Tiling

noncomputable def dilate {T : Triangle} {n : ℕ} (d : Tiling T n) (r : ℝ) (hr : r ≠ 0) :
    Tiling (T.dilate r hr) n where
  tile := d.tile.dilate r hr
  place := fun i => dilatedMotion (d.place i) r
  covers := by
    simp only [Triangle.support_dilate, dilatedMotion_image, ← Set.image_iUnion, d.covers]
  disjoint_interiors := by
    intro i j hij
    simp only [Triangle.support_dilate, dilatedMotion_image]
    have hi (S : Set Plane) : (fun x : Plane => r • x) '' interior S =
        interior ((fun x : Plane => r • x) '' S) :=
      (Homeomorph.smulOfNeZero r hr).image_interior S
    rw [← hi, ← hi]
    exact Set.disjoint_image_of_injective (smul_right_injective Plane hr)
      (d.disjoint_interiors hij)

noncomputable def homothetic {T : Triangle} {n : ℕ} (d : Tiling T n)
    (c : Plane) (r : ℝ) (hr : r ≠ 0) : Tiling (T.homothetic c r hr) n :=
  (d.dilate r hr).move (AffineIsometryEquiv.constVAdd ℝ Plane ((1 - r) • c))

end Tiling

end Erdos633b
