import Wikipedia.SmoothSixDPoincare.PuncturedRadialHomotopy

/-!
# The actual exterior of a closed ball retracts onto an enclosing sphere

Positive radial interpolation stays outside the original closed ball.
The resulting homotopy equivalence retains the literal sphere of radius
`r > R` as its forward map. This is the geometric input for a relative
fundamental class supported on a closed ball.
-/

noncomputable section

open Set Metric Topology ContinuousMap
open scoped unitInterval

namespace NoExoticSixSphere.BallExterior

open Wikipedia.SmoothSixDPoincare

abbrev Space (E : Type*) [NormedAddCommGroup E] (R : ℝ) :=
  (closedBall (0 : E) R)ᶜ

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (R : ℝ) (hR : 0 ≤ R)

omit [NormedSpace ℝ E] in
theorem norm_gt (x : Space E R) : R < ‖(x : E)‖ := by
  have h := x.2
  simpa only [mem_compl_iff, mem_closedBall_zero_iff, not_le] using h

include hR in
omit [NormedSpace ℝ E] in
theorem ne_zero (x : Space E R) : (x : E) ≠ 0 := by
  intro h
  have hx := norm_gt R x
  rw [h, norm_zero] at hx
  exact (not_lt_of_ge hR) hx

def toPunctured : C(Space E R, PuncturedRadial.Space E) :=
  ⟨fun x => ⟨x.1, ne_zero R hR x⟩, continuous_subtype_val.subtype_mk _⟩

def toSphere : C(Space E R, sphere (0 : E) 1) :=
  PuncturedRadial.toSphere.comp (toPunctured R hR)

variable (r : ℝ) (hr : R < r)

include hR hr in
theorem radius_pos : 0 < r := lt_of_le_of_lt hR hr

include hR hr in
theorem smul_mem_exterior (u : sphere (0 : E) 1) : r • (u : E) ∈ Space E R := by
  change r • (u : E) ∉ closedBall (0 : E) R
  rw [mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs,
    abs_of_pos (radius_pos R hR r hr), mem_sphere_zero_iff_norm.mp u.2, mul_one]
  exact not_le.mpr hr

def fromSphere (R : ℝ) (hR : 0 ≤ R) (r : ℝ) (hr : R < r) :
    C(sphere (0 : E) 1, Space E R) :=
  ⟨fun u => ⟨r • (u : E), smul_mem_exterior R hR r hr u⟩,
    (continuous_const.smul continuous_subtype_val).subtype_mk _⟩

theorem toSphere_fromSphere (u : sphere (0 : E) 1) :
    toSphere R hR (fromSphere R hR r hr u) = u := by
  apply Subtype.ext
  change ‖r • (u : E)‖⁻¹ • (r • (u : E)) = (u : E)
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (radius_pos R hR r hr),
    mem_sphere_zero_iff_norm.mp u.2, mul_one, inv_smul_smul₀ (radius_pos R hR r hr).ne']

def blendVector (q : I × Space E R) : E :=
  PuncturedRadial.blendVector r (q.1, toPunctured R hR q.2)

theorem continuous_blendVector : Continuous (blendVector (E := E) R hR r) :=
  (PuncturedRadial.continuous_blendVector r).comp
    (continuous_fst.prodMk ((toPunctured R hR).continuous.comp continuous_snd))

include hr in
theorem blendVector_norm_gt (q : I × Space E R) : R < ‖blendVector R hR r q‖ := by
  have hu : 0 < ‖(q.2 : E)‖ := norm_pos_iff.mpr (ne_zero R hR q.2)
  have hc : 0 ≤ (1 - (q.1 : ℝ)) + (q.1 : ℝ) * (r / ‖(q.2 : E)‖) :=
    add_nonneg (sub_nonneg.mpr q.1.2.2)
      (mul_nonneg q.1.2.1 (div_nonneg (radius_pos R hR r hr).le hu.le))
  have ht := (convex_Ioi (𝕜 := ℝ) R) (norm_gt R q.2) hr
    (sub_nonneg.mpr q.1.2.2) q.1.2.1 (sub_add_cancel 1 (q.1 : ℝ))
  change R < ‖((1 - (q.1 : ℝ)) + (q.1 : ℝ) * (r / ‖(q.2 : E)‖)) • (q.2 : E)‖
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hc, add_mul, mul_assoc,
    div_mul_cancel₀ r hu.ne']
  exact ht

include hr in
theorem blendVector_mem_exterior (q : I × Space E R) : blendVector R hR r q ∈ Space E R := by
  simpa only [mem_compl_iff, mem_closedBall_zero_iff, not_le]
    using blendVector_norm_gt R hR r hr q

/-- This homotopy never enters the original closed ball, including at intermediate times. -/
def deformation (R : ℝ) (hR : 0 ≤ R) (r : ℝ) (hr : R < r) :
    (ContinuousMap.id (Space E R)).Homotopy ((fromSphere R hR r hr).comp (toSphere R hR)) where
  toFun q := ⟨blendVector R hR r q, blendVector_mem_exterior R hR r hr q⟩
  continuous_toFun := (continuous_blendVector R hR r).subtype_mk _
  map_zero_left x := by
    apply Subtype.ext
    simp [blendVector, PuncturedRadial.blendVector, toPunctured]
  map_one_left x := by
    apply Subtype.ext
    simp [blendVector, PuncturedRadial.blendVector, toPunctured, fromSphere, toSphere,
      PuncturedRadial.toSphere, RadialExtension.direction, div_eq_mul_inv, smul_smul]

/-- The actual enclosing sphere is homotopy equivalent to the whole original exterior. -/
def sphereHomotopyEquiv : sphere (0 : E) 1 ≃ₕ Space E R where
  toFun := fromSphere R hR r hr
  invFun := toSphere R hR
  left_inv := by
    have h : (toSphere R hR).comp (fromSphere R hR r hr) =
        ContinuousMap.id (sphere (0 : E) 1) :=
      ContinuousMap.ext (toSphere_fromSphere R hR r hr)
    rw [h]
  right_inv := ⟨(deformation R hR r hr).symm⟩

end NoExoticSixSphere.BallExterior
