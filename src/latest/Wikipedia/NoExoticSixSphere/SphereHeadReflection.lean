import Wikipedia.NoExoticSixSphere.SphereHemisphereRadialCoordinates

/-! # Reflection exchanging the original sphere's two cylinder ends -/

noncomputable section

open Set Function
open scoped Manifold ContDiff

namespace NoExoticSixSphere.SphereSumNeck

open GLOrthonormalization

def reflectHeadVector (x : Vector 4) : Vector 4 :=
  SphereCylinder.join 2 (-x 0, SphereCylinder.tail 2 x)

theorem join_head_tail (x : Vector 4) :
    SphereCylinder.join 2 (x 0, SphereCylinder.tail 2 x) = x := by
  ext i
  exact Fin.cases rfl (fun _ ↦ rfl) i

theorem norm_reflectHeadVector (x : Vector 4) : ‖reflectHeadVector x‖ = ‖x‖ := by
  have h := SphereCylinder.norm_join_sq 2 (-x 0) (SphereCylinder.tail 2 x)
  have h' := SphereCylinder.norm_join_sq 2 (x 0) (SphereCylinder.tail 2 x)
  rw [join_head_tail] at h'
  change ‖reflectHeadVector x‖ ^ 2 = _ at h
  nlinarith [norm_nonneg (reflectHeadVector x), norm_nonneg x]

theorem reflectHeadVector_involutive : Involutive reflectHeadVector := by
  intro x
  ext i
  refine Fin.cases ?_ (fun _ ↦ rfl) i
  change - -x 0 = x 0
  exact neg_neg _

def reflectHead (x : Sphere 3) : Sphere 3 :=
  ⟨reflectHeadVector x.val, by
    rw [Metric.mem_sphere, dist_zero_right, norm_reflectHeadVector]
    exact ClosedHemisphere.unit_norm x⟩

theorem reflectHead_involutive : Involutive reflectHead := by
  intro x
  exact Subtype.ext (reflectHeadVector_involutive x.val)

theorem reflectHead_head (x : Sphere 3) : (reflectHead x).val 0 = -x.val 0 := rfl

theorem reflectHead_tail (x : Sphere 3) :
    SphereCylinder.tail 2 (reflectHead x).val = SphereCylinder.tail 2 x.val :=
  SphereCylinder.tail_join 2 _ _

theorem contMDiff_reflectHead : ContMDiff (𝓡 3) (𝓡 3) ∞ reflectHead := by
  let : Fact (Module.finrank ℝ (Vector 4) = 3 + 1) := ⟨finrank_euclideanSpace_fin⟩
  have hv : ContDiff ℝ ∞ reflectHeadVector :=
    (SphereCylinder.join 2).contDiff.comp
      ((contDiff_piLp_apply 2).neg.prodMk (SphereCylinder.tail 2).contDiff)
  have hs : ContMDiff (𝓡 3) (𝓡 4) ∞ (fun x : Sphere 3 ↦ reflectHeadVector x.val) :=
    hv.contMDiff.comp contMDiff_coe_sphere
  exact hs.codRestrict_sphere (fun x ↦ (reflectHead x).property)

def reflectHeadDiffeomorph : Diffeomorph (𝓡 3) (𝓡 3) (Sphere 3) (Sphere 3) ∞ where
  toFun := reflectHead
  invFun := reflectHead
  left_inv := reflectHead_involutive
  right_inv := reflectHead_involutive
  contMDiff_toFun := contMDiff_reflectHead
  contMDiff_invFun := contMDiff_reflectHead

theorem reflectHead_cylinder (t : ℝ) (s : Sphere 2) :
    reflectHead (SphereCylinder.point 2 (t, s)) = SphereCylinder.point 2 (-t, s) := by
  have hn : ‖SphereCylinder.vector 2 (-t, s)‖ = ‖SphereCylinder.vector 2 (t, s)‖ := by
    have h := SphereCylinder.norm_join_sq 2 (-t) s.val
    have h' := SphereCylinder.norm_join_sq 2 t s.val
    change ‖SphereCylinder.vector 2 (-t, s)‖ ^ 2 = _ at h
    change ‖SphereCylinder.vector 2 (t, s)‖ ^ 2 = _ at h'
    nlinarith [norm_nonneg (SphereCylinder.vector 2 (-t, s)),
      norm_nonneg (SphereCylinder.vector 2 (t, s))]
  apply Subtype.ext
  ext i
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · change -((SphereCylinder.point 2 (t, s)).val 0) = _
    rw [SphereCylinder.point_head, SphereCylinder.point_head, hn, mul_neg]
  · change (SphereCylinder.point 2 (t, s)).val j.succ =
      (SphereCylinder.point 2 (-t, s)).val j.succ
    change ‖SphereCylinder.vector 2 (t, s)‖⁻¹ * s.val j =
      ‖SphereCylinder.vector 2 (-t, s)‖⁻¹ * s.val j
    rw [hn]

end NoExoticSixSphere.SphereSumNeck
