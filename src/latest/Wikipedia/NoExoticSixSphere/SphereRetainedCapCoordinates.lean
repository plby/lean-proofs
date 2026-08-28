import Wikipedia.NoExoticSixSphere.SphereCapHomeomorphism
import Wikipedia.NoExoticSixSphere.SphereHemisphereRetraction

/-!
# Actual disjoint closed caps inside the retained open pieces

Axial dilation of scale five transports the closed northern hemisphere
strictly into the retained northern region. Reflection gives the southern
cap. Their inverse coordinates send the opposite whole hemisphere below
height minus one half, as required by the localized coordinate construction.
-/

noncomputable section

open Set Function
open scoped Manifold ContDiff

namespace NoExoticSixSphere.SphereSumNeck

open GLOrthonormalization SphereHemisphereRetraction

def northRetainedCap : Sphere 3 ≃ₜ Sphere 3 :=
  (axisDilationDiffeomorph 5 (by norm_num)).toHomeomorph

def southRetainedCap : Sphere 3 ≃ₜ Sphere 3 :=
  northRetainedCap.trans reflectHeadDiffeomorph.toHomeomorph

theorem northRetainedCap_head (x : North) : (12 / 13 : ℝ) ≤ (northRetainedCap x.val).val 0 := by
  have hx : 0 ≤ x.val.val 0 := (mem_north_iff x.val).mp x.property
  change (12 / 13 : ℝ) ≤ (axisDilation 5 x.val).val 0
  rw [axisDilation_head (by norm_num), le_div_iff₀ (axisDenominator_pos (by norm_num) x.val)]
  dsimp [axisNumerator, axisDenominator]
  linarith

theorem northRetainedCap_mem_northRegion (x : North) : northRetainedCap x.val ∈ northRegion := by
  have hh := northRetainedCap_head x
  have hh2 := mul_self_le_mul_self (by norm_num : (0 : ℝ) ≤ 12 / 13) hh
  have hs := source_head_tail_sq (northRetainedCap x.val)
  have ht : ‖SphereCylinder.tail 2 (northRetainedCap x.val).val‖ ≤ (5 / 13 : ℝ) := by
    nlinarith [norm_nonneg (SphereCylinder.tail 2 (northRetainedCap x.val).val)]
  change 2 * ‖SphereCylinder.tail 2 (northRetainedCap x.val).val‖ < (northRetainedCap x.val).val 0
  linarith

theorem southRetainedCap_mem_southRegion (x : North) : southRetainedCap x.val ∈ southRegion := by
  change 2 * ‖SphereCylinder.tail 2 (reflectHead (northRetainedCap x.val)).val‖ <
    -(reflectHead (northRetainedCap x.val)).val 0
  rw [reflectHead_tail, reflectHead_head, neg_neg]
  exact northRetainedCap_mem_northRegion x

theorem northRetainedCap_opposite {x : Sphere 3} (hx : x.val 0 ≤ 0) :
    (northRetainedCap.symm x).val 0 ≤ -(1 / 2 : ℝ) := by
  change (axisDilation (5 : ℝ)⁻¹ x).val 0 ≤ -(1 / 2 : ℝ)
  rw [axisDilation_head (by norm_num), div_le_iff₀ (axisDenominator_pos (by norm_num) x)]
  dsimp [axisNumerator, axisDenominator]
  linarith

theorem southRetainedCap_opposite {x : Sphere 3} (hx : 0 ≤ x.val 0) :
    (southRetainedCap.symm x).val 0 ≤ -(1 / 2 : ℝ) := by
  change (northRetainedCap.symm (reflectHead x)).val 0 ≤ -(1 / 2 : ℝ)
  apply northRetainedCap_opposite
  rw [reflectHead_head]
  exact neg_nonpos.mpr hx

theorem northRetainedCap_opposite_south (x : North) :
    (northRetainedCap.symm (southRetainedCap x.val)).val 0 ≤ -(1 / 2 : ℝ) :=
  northRetainedCap_opposite (southRegion_head_neg (southRetainedCap_mem_southRegion x)).le

theorem southRetainedCap_opposite_north (x : North) :
    (southRetainedCap.symm (northRetainedCap x.val)).val 0 ≤ -(1 / 2 : ℝ) :=
  southRetainedCap_opposite (northRegion_head_pos (northRetainedCap_mem_northRegion x)).le

end NoExoticSixSphere.SphereSumNeck
