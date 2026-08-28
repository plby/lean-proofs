import Wikipedia.SmoothSixDPoincare.ContinuousDiskExtension
import Mathlib.Topology.Piecewise

/-!
# Continuous radial maps for a boundary-preserving annular extension

The inner map takes the whole space into the unit disk. Its scaled version
fixes the radius-`a` disk and clamps the exterior onto its sphere. A second
unit-disk map agrees on that sphere and vanishes beyond radius `2*a`, allowing
a nullhomotopy extension to become constant outside a compact set.
-/

noncomputable section

open Set Function Metric Topology

namespace Wikipedia.SmoothSixDPoincare.AnnularExtension

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def unitClamp (a : ℝ) (x : E) : E := (max a ‖x‖)⁻¹ • x

omit [NormedSpace ℝ E] in
theorem max_radius_pos {a : ℝ} (ha : 0 < a) (x : E) : 0 < max a ‖x‖ :=
  ha.trans_le (le_max_left _ _)

theorem continuous_unitClamp {a : ℝ} (ha : 0 < a) : Continuous (unitClamp (E := E) a) :=
  ((continuous_const.max continuous_norm).inv₀ (fun x => (max_radius_pos ha x).ne')).smul
    continuous_id

theorem norm_unitClamp {a : ℝ} (ha : 0 < a) (x : E) :
    ‖unitClamp a x‖ = ‖x‖ / max a ‖x‖ := by
  rw [unitClamp, norm_smul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr (max_radius_pos ha x)), div_eq_mul_inv, mul_comm]

theorem norm_unitClamp_le {a : ℝ} (ha : 0 < a) (x : E) : ‖unitClamp a x‖ ≤ 1 := by
  rw [norm_unitClamp ha]
  exact (div_le_one (max_radius_pos ha x)).mpr (le_max_right _ _)

def innerDisk {a : ℝ} (ha : 0 < a) : C(E, closedBall (0 : E) 1) where
  toFun x := ⟨unitClamp a x, mem_closedBall_zero_iff.mpr (norm_unitClamp_le ha x)⟩
  continuous_toFun := (continuous_unitClamp ha).subtype_mk _

theorem unitClamp_of_norm_le {a : ℝ} {x : E} (hx : ‖x‖ ≤ a) :
    unitClamp a x = a⁻¹ • x := by rw [unitClamp, max_eq_left hx]

def clamp (a : ℝ) (x : E) : E := a • unitClamp a x

theorem continuous_clamp {a : ℝ} (ha : 0 < a) : Continuous (clamp (E := E) a) :=
  continuous_const.smul (continuous_unitClamp ha)

theorem clamp_of_norm_le {a : ℝ} (ha : 0 < a) {x : E} (hx : ‖x‖ ≤ a) : clamp a x = x := by
  rw [clamp, unitClamp_of_norm_le hx, smul_inv_smul₀ ha.ne']

theorem norm_clamp {a : ℝ} (ha : 0 < a) (x : E) : ‖clamp a x‖ = min a ‖x‖ := by
  by_cases hx : ‖x‖ ≤ a
  · rw [clamp_of_norm_le ha hx, min_eq_right hx]
  · have hx' : a ≤ ‖x‖ := le_of_not_ge hx
    have hnorm : ‖x‖ ≠ 0 := (ha.trans_le hx').ne'
    rw [clamp, norm_smul, Real.norm_eq_abs, abs_of_pos ha, norm_unitClamp ha,
      max_eq_right hx', div_self hnorm, mul_one, min_eq_left hx']

theorem clamp_mem_annulus {a b : ℝ} (hb : 0 < b) (hab : a ≤ b) {x : E} (hx : a ≤ ‖x‖) :
    a ≤ ‖clamp b x‖ ∧ ‖clamp b x‖ ≤ b := by
  rw [norm_clamp hb]
  exact ⟨le_min hab hx, min_le_left _ _⟩

def exteriorFactor (a : ℝ) (x : E) : ℝ := min 1 (max 0 (2 - ‖x‖ / a))

omit [NormedSpace ℝ E] in
theorem exteriorFactor_nonneg (a : ℝ) (x : E) : 0 ≤ exteriorFactor a x :=
  le_min zero_le_one (le_max_left _ _)

omit [NormedSpace ℝ E] in
theorem exteriorFactor_le_one (a : ℝ) (x : E) : exteriorFactor a x ≤ 1 := min_le_left _ _

def exteriorVector (a : ℝ) (x : E) : E := exteriorFactor a x • unitClamp a x

theorem continuous_exteriorVector {a : ℝ} (ha : 0 < a) :
    Continuous (exteriorVector (E := E) a) := by
  have hf : Continuous (exteriorFactor (E := E) a) := by unfold exteriorFactor; fun_prop
  exact hf.smul (continuous_unitClamp ha)

theorem norm_exteriorVector_le {a : ℝ} (ha : 0 < a) (x : E) : ‖exteriorVector a x‖ ≤ 1 := by
  rw [exteriorVector, norm_smul, Real.norm_eq_abs, abs_of_nonneg (exteriorFactor_nonneg a x)]
  calc
    _ ≤ 1 * 1 := mul_le_mul (exteriorFactor_le_one a x) (norm_unitClamp_le ha x)
      (norm_nonneg _) zero_le_one
    _ = 1 := one_mul _

def exteriorDisk {a : ℝ} (ha : 0 < a) : C(E, closedBall (0 : E) 1) where
  toFun x := ⟨exteriorVector a x, mem_closedBall_zero_iff.mpr (norm_exteriorVector_le ha x)⟩
  continuous_toFun := (continuous_exteriorVector ha).subtype_mk _

theorem exteriorVector_on_sphere {a : ℝ} (ha : 0 < a) {x : E} (hx : ‖x‖ = a) :
    exteriorVector a x = unitClamp a x := by
  have hf : exteriorFactor a x = 1 := by
    unfold exteriorFactor
    rw [hx, div_self ha.ne']
    norm_num
  rw [exteriorVector, hf, one_smul]

theorem exteriorVector_eq_zero {a : ℝ} (ha : 0 < a) {x : E} (hx : 2 * a ≤ ‖x‖) :
    exteriorVector a x = 0 := by
  have hdiv : 2 ≤ ‖x‖ / a := (le_div_iff₀ ha).mpr hx
  have hf : exteriorFactor a x = 0 := by
    unfold exteriorFactor
    rw [max_eq_left (by linarith : 2 - ‖x‖ / a ≤ 0), min_eq_right zero_le_one]
  rw [exteriorVector, hf, zero_smul]

end Wikipedia.SmoothSixDPoincare.AnnularExtension
