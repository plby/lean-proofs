import Wikipedia.NoExoticSixSphere.StereographicInverseDifferential

/-!
# Linear coordinates and derivatives of the actual stereographic chart

The fixed orthonormal coordinates of the pole complement are retained.
The finite inverse derivative at an equator point is the derivative of
the original inverse chart, including its pole and radial terms.
-/

noncomputable section

open scoped ContDiff

namespace NoExoticSixSphere.StereographicEquator

def project (n : ℕ) : V (n + 1) →L[ℝ] V n :=
  (coordinates n).toContinuousLinearEquiv.toContinuousLinearMap.comp
    (ℝ ∙ (spherePole n).val)ᗮ.orthogonalProjectionOnto

def liftL (n : ℕ) : V n →L[ℝ] V (n + 1) :=
  (ℝ ∙ (spherePole n).val)ᗮ.subtypeL.comp
    (coordinates n).symm.toContinuousLinearEquiv.toContinuousLinearMap

theorem liftL_apply (n : ℕ) (x : V n) : liftL n x = lift n x := rfl

theorem project_lift (n : ℕ) (x : V n) : project n (lift n x) = x := by
  change coordinates n ((ℝ ∙ (spherePole n).val)ᗮ.orthogonalProjectionOnto
    ((coordinates n).symm x : V (n + 1))) = x
  rw [Submodule.orthogonalProjectionOnto_mem_subspace_eq_self,
    LinearIsometryEquiv.apply_symm_apply]

theorem lift_project_of_orthogonal (n : ℕ) (x : V (n + 1))
    (hx : inner ℝ (spherePole n).val x = 0) : lift n (project n x) = x := by
  have hm : x ∈ (ℝ ∙ (spherePole n).val)ᗮ :=
    Submodule.mem_orthogonal_singleton_iff_inner_right.mpr hx
  change ((coordinates n).symm (coordinates n
    ((ℝ ∙ (spherePole n).val)ᗮ.orthogonalProjectionOnto x)) : V (n + 1)) = x
  rw [LinearIsometryEquiv.symm_apply_apply]
  exact Submodule.starProjection_eq_self_iff.mpr hm

theorem chart_formula (n : ℕ) (x : Sphere n) :
    sphereProjection n x = (2 / (1 - inner ℝ (spherePole n).val x.val)) • project n x.val := by
  change coordinates n ((2 / (1 - inner ℝ (spherePole n).val x.val)) •
    (ℝ ∙ (spherePole n).val)ᗮ.orthogonalProjectionOnto x.val) = _
  rw [map_smul]
  rfl

theorem chart_equator (n : ℕ) (x : Sphere n) (hx : inner ℝ (spherePole n).val x.val = 0) :
    sphereProjection n x = (2 : ℝ) • project n x.val := by
  rw [chart_formula, hx, sub_zero, div_one]

def finiteAmbient (n : ℕ) (y : V n) : V (n + 1) :=
  (euclideanOnePointSphere n (y : OnePoint (V n))).val

theorem finiteAmbient_eq (n : ℕ) :
    finiteAmbient n = stereoInvFunAux (spherePole n).val ∘ liftL n := by
  funext y
  rw [finiteAmbient, finite_apply]
  change _ = (‖lift n y‖ ^ 2 + 4)⁻¹ •
    ((4 : ℝ) • lift n y + (‖lift n y‖ ^ 2 - 4) • (spherePole n).val)
  rw [norm_lift, smul_add]

theorem contDiff_finiteAmbient (n : ℕ) : ContDiff ℝ ∞ (finiteAmbient n) := by
  rw [finiteAmbient_eq]
  exact contDiff_stereoInvFunAux.comp (liftL n).contDiff

theorem finiteAmbient_derivative_double (n : ℕ) (x : V n) (hx : ‖x‖ = 1) (w : V n) :
    fderiv ℝ (finiteAmbient n) ((2 : ℝ) • x) w =
      (1 / 2 : ℝ) • (lift n w - (inner ℝ x w) • lift n x +
        (inner ℝ x w) • (spherePole n).val) := by
  rw [finiteAmbient_eq, fderiv_comp ((2 : ℝ) • x)
    ((contDiff_stereoInvFunAux (v := (spherePole n).val) (m := ∞)).differentiable
      (by simp) _) (liftL n).differentiableAt,
    ContinuousLinearMap.fderiv]
  change fderiv ℝ (stereoInvFunAux (spherePole n).val) (liftL n ((2 : ℝ) • x)) (liftL n w) = _
  rw [map_smul, liftL_apply, liftL_apply,
    stereoInvFunAux_fderiv_double _ _ ((norm_lift n x).trans hx), inner_lift]

end NoExoticSixSphere.StereographicEquator
