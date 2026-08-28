import Wikipedia.NoExoticSixSphere.OrthogonalVelocity

/-!
# Differentiating the inverse of an orthogonal curve

On the actual orthogonal operators, inversion is the ambient adjoint. Its
derivative is therefore obtained from a continuous real-linear map. The product
rule then gives the usual inverse-derivative formula without choosing charts.
-/

namespace NoExoticSixSphere.OrthogonalVelocity

open GLOrthonormalization OrthogonalPaths

variable {n : ℕ}

theorem inverse_eq_adjoint (a : OrthogonalOperators n) :
    (inverse a).1.1 = a.1.1.adjoint := by
  apply ContinuousLinearMap.ext
  intro v
  apply ext_inner_left ℝ
  intro u
  rw [ContinuousLinearMap.adjoint_inner_right]
  exact ((toEquiv a).inner_map_eq_flip u v).symm

theorem hasDerivAt_inverse_adjoint {a : ℝ → OrthogonalOperators n}
    {A : Vector n →L[ℝ] Vector n} {t : ℝ}
    (h : HasDerivAt (fun r ↦ (a r).1.1) A t) :
    HasDerivAt (fun r ↦ (inverse (a r)).1.1) A.adjoint t := by
  let L : (Vector n →L[ℝ] Vector n) →L[ℝ] (Vector n →L[ℝ] Vector n) :=
    ContinuousLinearMap.adjoint.toContinuousLinearEquiv.toContinuousLinearMap
  have hd := L.hasFDerivAt.comp_hasDerivAt t h
  simpa only [L, inverse_eq_adjoint] using! hd

theorem adjoint_derivative_eq {a : ℝ → OrthogonalOperators n}
    {A : Vector n →L[ℝ] Vector n} {t : ℝ}
    (h : HasDerivAt (fun r ↦ (a r).1.1) A t) :
    A.adjoint = -((inverse (a t)).1.1.comp (A.comp (inverse (a t)).1.1)) := by
  have hd := (hasDerivAt_inverse_adjoint h).clm_comp h
  have heq : (fun r ↦ (inverse (a r)).1.1.comp (a r).1.1) =
      (fun _ : ℝ ↦ (1 : Vector n →L[ℝ] Vector n)) := by
    funext r
    apply ContinuousLinearMap.ext
    intro x
    exact inverse_apply_self (a r) x
  rw [heq] at hd
  have hz := hd.unique (hasDerivAt_const t (1 : Vector n →L[ℝ] Vector n))
  have he : A.adjoint.comp (a t).1.1 = -((inverse (a t)).1.1.comp A) :=
    eq_neg_of_add_eq_zero_left hz
  apply ContinuousLinearMap.ext
  intro x
  have hx := DFunLike.congr_fun he ((inverse (a t)).1.1 x)
  simpa only [ContinuousLinearMap.comp_apply, self_apply_inverse, neg_apply] using hx

theorem hasDerivAt_inverse {a : ℝ → OrthogonalOperators n}
    {A : Vector n →L[ℝ] Vector n} {t : ℝ}
    (h : HasDerivAt (fun r ↦ (a r).1.1) A t) :
    HasDerivAt (fun r ↦ (inverse (a r)).1.1)
      (-((inverse (a t)).1.1.comp (A.comp (inverse (a t)).1.1))) t := by
  rw [← adjoint_derivative_eq h]
  exact hasDerivAt_inverse_adjoint h

/-- Product rule after translating an ambient vector field back to the identity. -/
theorem hasDerivAt_leftTrivialized {a : ℝ → OrthogonalOperators n}
    {b : ℝ → Vector n →L[ℝ] Vector n}
    {A B : Vector n →L[ℝ] Vector n} {t : ℝ}
    (ha : HasDerivAt (fun r ↦ (a r).1.1) A t) (hb : HasDerivAt b B t) :
    HasDerivAt (fun r ↦ (inverse (a r)).1.1.comp (b r))
      (-(((inverse (a t)).1.1.comp A).comp ((inverse (a t)).1.1.comp (b t))) +
        (inverse (a t)).1.1.comp B) t := by
  simpa only [ContinuousLinearMap.neg_comp, ContinuousLinearMap.comp_assoc] using!
    (hasDerivAt_inverse ha).clm_comp hb

end NoExoticSixSphere.OrthogonalVelocity
