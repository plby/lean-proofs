import Wikipedia.SmoothSixDPoincare.DiskAnnulusHomotopy

/-!
# The actual punctured vector space retracts onto any positive-radius sphere

Keep the original radial normalization as the inverse map. Positive radial
interpolation gives a homotopy from the identity to the specified radius,
so later collapse comparisons can retain their literal overlap map.
-/

noncomputable section

open Set Metric Topology ContinuousMap
open scoped unitInterval

namespace Wikipedia.SmoothSixDPoincare.PuncturedRadial

abbrev Space (N : Type*) [Zero N] := {u : N // u ≠ 0}

variable {N : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N]

def toSphere : C(Space N, sphere (0 : N) 1) :=
  ⟨fun u => RadialExtension.direction u.val u.property,
    ((continuous_subtype_val.norm.inv₀ (fun u => norm_ne_zero_iff.mpr u.property)).smul
      continuous_subtype_val).subtype_mk _⟩

def fromSphere (r : ℝ) (hr : 0 < r) : C(sphere (0 : N) 1, Space N) :=
  ⟨fun u => ⟨r • (u : N), smul_ne_zero hr.ne' (ne_zero_of_mem_unit_sphere u)⟩,
    (continuous_const.smul continuous_subtype_val).subtype_mk _⟩

theorem toSphere_fromSphere (r : ℝ) (hr : 0 < r) (u : sphere (0 : N) 1) :
    toSphere (fromSphere r hr u) = u := by
  apply Subtype.ext
  change ‖r • (u : N)‖⁻¹ • (r • (u : N)) = (u : N)
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr,
    mem_sphere_zero_iff_norm.mp u.property, mul_one, inv_smul_smul₀ hr.ne']

def blendVector (r : ℝ) (q : I × Space N) : N :=
  ((1 - (q.1 : ℝ)) + (q.1 : ℝ) * (r / ‖q.2.val‖)) • q.2.val

theorem continuous_blendVector (r : ℝ) : Continuous (blendVector (N := N) r) := by
  have ht : Continuous (fun q : I × Space N => (q.1 : ℝ)) :=
    continuous_subtype_val.comp continuous_fst
  have hu : Continuous (fun q : I × Space N => q.2.val) :=
    continuous_subtype_val.comp continuous_snd
  exact ((continuous_const.sub ht).add
    (ht.mul (continuous_const.div hu.norm
      (fun q => norm_ne_zero_iff.mpr q.2.property)))).smul hu

theorem blendVector_ne_zero (r : ℝ) (hr : 0 < r) (q : I × Space N) :
    blendVector r q ≠ 0 := by
  have hu : 0 < ‖q.2.val‖ := norm_pos_iff.mpr q.2.property
  have hpos : 0 < (1 - (q.1 : ℝ)) + (q.1 : ℝ) * (r / ‖q.2.val‖) := by
    have h := (convex_Ioi (𝕜 := ℝ) (0 : ℝ)) (by norm_num : (1 : ℝ) ∈ Ioi 0)
      (div_pos hr hu) (sub_nonneg.mpr q.1.property.2) q.1.property.1
      (sub_add_cancel 1 (q.1 : ℝ))
    simpa only [smul_eq_mul, mul_one, mem_Ioi] using h
  exact smul_ne_zero hpos.ne' q.2.property

def deformation (r : ℝ) (hr : 0 < r) :
    (ContinuousMap.id (Space N)).Homotopy ((fromSphere r hr).comp toSphere) where
  toFun q := ⟨blendVector r q, blendVector_ne_zero r hr q⟩
  continuous_toFun := (continuous_blendVector r).subtype_mk _
  map_zero_left u := by
    apply Subtype.ext
    simp [blendVector]
  map_one_left u := by
    apply Subtype.ext
    simp [blendVector, fromSphere, toSphere, RadialExtension.direction,
      div_eq_mul_inv, smul_smul]

def sphereHomotopyEquiv (r : ℝ) (hr : 0 < r) : sphere (0 : N) 1 ≃ₕ Space N where
  toFun := fromSphere r hr
  invFun := toSphere
  left_inv := by
    have heq : toSphere.comp (fromSphere r hr) = ContinuousMap.id (sphere (0 : N) 1) :=
      ContinuousMap.ext (toSphere_fromSphere r hr)
    rw [heq]
  right_inv := ⟨(deformation r hr).symm⟩

end Wikipedia.SmoothSixDPoincare.PuncturedRadial
