import Wikipedia.SmoothSixDPoincare.PuncturedRadialHomotopy

/-!
# The original punctured open ball retracts onto any smaller positive sphere

Use the original radial normalization and interpolate the radius while
remaining strictly inside the open ball. The sphere inclusion retains its
specified physical radius, for comparison with a local degree boundary.
-/

noncomputable section

open Set Metric Topology ContinuousMap
open scoped unitInterval

namespace Wikipedia.SmoothSixDPoincare.PuncturedBall

abbrev Space (E : Type*) [NormedAddCommGroup E] (R : ℝ) := {x : E // x ≠ 0 ∧ ‖x‖ < R}

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (R : ℝ)

def toPunctured : C(Space E R, PuncturedRadial.Space E) :=
  ⟨fun x => ⟨x.val, x.property.1⟩, continuous_subtype_val.subtype_mk _⟩

def toSphere : C(Space E R, sphere (0 : E) 1) :=
  PuncturedRadial.toSphere.comp (toPunctured R)

def fromSphere (r : ℝ) (hr : 0 < r) (hrR : r < R) : C(sphere (0 : E) 1, Space E R) :=
  ⟨fun u => ⟨r • (u : E),
    smul_ne_zero hr.ne' (ne_zero_of_mem_unit_sphere u), by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr,
        mem_sphere_zero_iff_norm.mp u.property, mul_one]
      exact hrR⟩, (continuous_const.smul continuous_subtype_val).subtype_mk _⟩

theorem toSphere_fromSphere (r : ℝ) (hr : 0 < r) (hrR : r < R) (u : sphere (0 : E) 1) :
    toSphere R (fromSphere R r hr hrR u) = u :=
  PuncturedRadial.toSphere_fromSphere r hr u

def blendVector (r : ℝ) (q : I × Space E R) : E :=
  PuncturedRadial.blendVector r (q.1, toPunctured R q.2)

theorem continuous_blendVector (r : ℝ) : Continuous (blendVector (E := E) R r) :=
  (PuncturedRadial.continuous_blendVector r).comp
    (continuous_fst.prodMk ((toPunctured R).continuous.comp continuous_snd))

theorem norm_blendVector (r : ℝ) (hr : 0 < r) (t : I) (x : Space E R) :
    ‖blendVector R r (t, x)‖ = (1 - (t : ℝ)) * ‖x.val‖ + (t : ℝ) * r := by
  have hn : 0 < ‖x.val‖ := norm_pos_iff.mpr x.property.1
  have hscale : 0 ≤ (1 - (t : ℝ)) + (t : ℝ) * (r / ‖x.val‖) :=
    add_nonneg (sub_nonneg.mpr t.property.2)
      (mul_nonneg t.property.1 (div_nonneg hr.le hn.le))
  change ‖((1 - (t : ℝ)) + (t : ℝ) * (r / ‖x.val‖)) • x.val‖ = _
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hscale, add_mul,
    mul_assoc, div_mul_cancel₀ _ hn.ne']

theorem norm_blendVector_lt (r : ℝ) (hr : 0 < r) (hrR : r < R) (t : I) (x : Space E R) :
    ‖blendVector R r (t, x)‖ < R := by
  rw [norm_blendVector R r hr]
  exact (convex_Iio (𝕜 := ℝ) R) x.property.2 hrR
    (sub_nonneg.mpr t.property.2) t.property.1 (sub_add_cancel 1 (t : ℝ))

def deformation (r : ℝ) (hr : 0 < r) (hrR : r < R) :
    (ContinuousMap.id (Space E R)).Homotopy ((fromSphere R r hr hrR).comp (toSphere R)) where
  toFun q := ⟨blendVector R r q,
    PuncturedRadial.blendVector_ne_zero r hr (q.1, toPunctured R q.2),
    norm_blendVector_lt R r hr hrR q.1 q.2⟩
  continuous_toFun := (continuous_blendVector R r).subtype_mk _
  map_zero_left x := by
    apply Subtype.ext
    simp [blendVector, PuncturedRadial.blendVector, toPunctured]
  map_one_left x := by
    apply Subtype.ext
    simp [blendVector, PuncturedRadial.blendVector, toPunctured, fromSphere, toSphere,
      PuncturedRadial.toSphere, RadialExtension.direction, div_eq_mul_inv, smul_smul]

def sphereHomotopyEquiv (r : ℝ) (hr : 0 < r) (hrR : r < R) :
    sphere (0 : E) 1 ≃ₕ Space E R where
  toFun := fromSphere R r hr hrR
  invFun := toSphere R
  left_inv := by
    have h : (toSphere (E := E) R).comp (fromSphere R r hr hrR) =
        ContinuousMap.id (sphere (0 : E) 1) :=
      ContinuousMap.ext (toSphere_fromSphere R r hr hrR)
    rw [h]
  right_inv := ⟨(deformation R r hr hrR).symm⟩

theorem sphereHomotopyEquiv_apply (r : ℝ) (hr : 0 < r) (hrR : r < R)
    (u : sphere (0 : E) 1) : (sphereHomotopyEquiv R r hr hrR u).val = r • (u : E) := rfl

end Wikipedia.SmoothSixDPoincare.PuncturedBall
