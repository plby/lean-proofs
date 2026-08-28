import Wikipedia.HopfProblem.DegreeCollapseSphereRadialDifferential
import Wikipedia.NoExoticSixSphere.SphereCenteredChartDifferential
import Wikipedia.NoExoticSixSphere.LocalInverse
import Wikipedia.NoExoticSixSphere.SphereCompactificationChart
import Mathlib.Analysis.InnerProductSpace.ProdL2

/-!
# The actual centered sphere chart and its fixed ambient linear coordinates

Retain the orthonormal basis used by the existing stereographic chart.
Its ambient derivative at the center is the tangent projection in this
fixed basis. Splitting into the radial coordinate and these tangent
coordinates gives an actual continuous linear equivalence.
-/

noncomputable section

open scoped Manifold ContDiff RealInnerProductSpace

namespace Wikipedia.HopfProblem.DegreeCollapse.SphereCenteredAmbientChart

open NoExoticSixSphere
open Wikipedia.HomotopyGroupsOfSpheres.SphereCenteredCoordinates

abbrev V (n : ℕ) := EuclideanSpace ℝ (Fin n)

local instance (n : ℕ) : Fact (Module.finrank ℝ (V (n + 1)) = n + 1) :=
  ⟨finrank_euclideanSpace_fin⟩

variable {n : ℕ}

def coordinates (z : Sphere n) : Tangent z ≃ₗᵢ[ℝ] V n :=
  (OrthonormalBasis.fromOrthogonalSpanSingleton n (ne_zero_of_mem_unit_sphere (-z))).repr

def ambientChart (z : Sphere n) : V (n + 1) → V n :=
  coordinates z ∘ stereoToFun (-z.val)

theorem modelChart_apply (z x : Sphere n) :
    modelChartPartialDiffeomorph (I := 𝓡 n) z x = ambientChart z x.val := rfl

theorem ambientChart_self (z : Sphere n) : ambientChart z z.val = 0 := by
  change coordinates z (chart z z) = 0
  rw [chart_self, map_zero]

def linearPart (z : Sphere n) : V (n + 1) →L[ℝ] V n :=
  (coordinates z).toContinuousLinearMap.comp (Tangent z).orthogonalProjectionOnto

theorem hasFDerivAt_ambientChart (z : Sphere n) :
    HasFDerivAt (ambientChart z) (linearPart z) z.val :=
  (coordinates z).hasFDerivAt.comp z.val (SphereCenteredChartDifferential.hasFDerivAt_chart z)

theorem linearPart_radial (z : Sphere n) : linearPart z z.val = 0 := by
  change coordinates z ((Tangent z).orthogonalProjectionOnto z.val) = 0
  rw [SphereCenteredChartDifferential.projection_center, map_zero]

def tangentLift (z : Sphere n) : V n →L[ℝ] V (n + 1) :=
  (Tangent z).subtypeL.comp (coordinates z).symm.toContinuousLinearMap

theorem linearPart_tangentLift (z : Sphere n) (w : V n) :
    linearPart z (tangentLift z w) = w := by
  change coordinates z ((Tangent z).orthogonalProjectionOnto
    (((coordinates z).symm w : Tangent z) : V (n + 1))) = w
  rw [Submodule.orthogonalProjectionOnto_mem_subspace_eq_self,
    LinearIsometryEquiv.apply_symm_apply]

theorem tangentLift_inner (z : Sphere n) (w : V n) :
    inner ℝ z.val (tangentLift z w) = 0 := by
  change inner ℝ z.val (((coordinates z).symm w : Tangent z) : V (n + 1)) = 0
  have h := Submodule.mem_orthogonal_singleton_iff_inner_right.mp
    ((coordinates z).symm w).property
  simpa only [inner_neg_left, neg_eq_zero] using h

theorem tangentLift_linearPart (z : Sphere n) (v : V (n + 1)) :
    tangentLift z (linearPart z v) = SphereRadialDifferential.tangentProjection z v := by
  have h : tangentLift z (linearPart z v) = (Tangent z).starProjection v := by
    change (((coordinates z).symm
      (coordinates z ((Tangent z).orthogonalProjectionOnto v)) : Tangent z) : V (n + 1)) = _
    rw [LinearIsometryEquiv.symm_apply_apply]
    rfl
  rw [h]
  change (ℝ ∙ (-z.val))ᗮ.starProjection v = _
  rw [Submodule.starProjection_orthogonal_val,
    Submodule.starProjection_unit_singleton ℝ (by rw [norm_neg, ClosedHemisphere.unit_norm])]
  simp only [inner_neg_left, neg_smul, smul_neg, neg_neg]
  rfl

theorem linearPart_tangentProjection (z : Sphere n) (v : V (n + 1)) :
    linearPart z (SphereRadialDifferential.tangentProjection z v) = linearPart z v := by
  rw [SphereRadialDifferential.tangentProjection_apply, map_sub, map_smul,
    linearPart_radial, smul_zero, sub_zero]

def split (z : Sphere n) : V (n + 1) →L[ℝ] WithLp 2 (ℝ × V n) :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ ℝ (V n)).symm.toContinuousLinearMap.comp
    ((innerSL ℝ z.val).prod (linearPart z))

def join (z : Sphere n) : WithLp 2 (ℝ × V n) →L[ℝ] V (n + 1) :=
  ContinuousLinearMap.smulRight (WithLp.fstL 2 ℝ ℝ (V n)) z.val +
    (tangentLift z).comp (WithLp.sndL 2 ℝ ℝ (V n))

theorem split_apply (z : Sphere n) (v : V (n + 1)) :
    split z v = WithLp.toLp 2 (inner ℝ z.val v, linearPart z v) := rfl

theorem join_apply (z : Sphere n) (p : WithLp 2 (ℝ × V n)) :
    join z p = p.fst • z.val + tangentLift z p.snd := rfl

theorem join_split (z : Sphere n) (v : V (n + 1)) : join z (split z v) = v := by
  rw [join_apply, split_apply]
  simp only [WithLp.toLp_fst, WithLp.toLp_snd]
  rw [tangentLift_linearPart, SphereRadialDifferential.tangentProjection_apply]
  abel

theorem split_join (z : Sphere n) (p : WithLp 2 (ℝ × V n)) : split z (join z p) = p := by
  apply WithLp.ofLp_injective 2
  apply Prod.ext
  · change inner ℝ z.val (join z p) = p.fst
    rw [join_apply, inner_add_right, inner_smul_right, tangentLift_inner,
      real_inner_self_eq_norm_sq, ClosedHemisphere.unit_norm, one_pow, mul_one, add_zero]
  · change linearPart z (join z p) = p.snd
    rw [join_apply, map_add, map_smul, linearPart_radial, linearPart_tangentLift,
      smul_zero, zero_add]

def coordinateEquiv (z : Sphere n) : V (n + 1) ≃L[ℝ] WithLp 2 (ℝ × V n) where
  toFun := split z
  invFun := join z
  left_inv := join_split z
  right_inv := split_join z
  map_add' := (split z).map_add
  map_smul' := (split z).map_smul
  continuous_toFun := (split z).continuous
  continuous_invFun := (join z).continuous

theorem coordinateEquiv_apply (z : Sphere n) (v : V (n + 1)) :
    coordinateEquiv z v = WithLp.toLp 2 (inner ℝ z.val v, linearPart z v) := rfl

theorem coordinateEquiv_symm_apply (z : Sphere n) (p : WithLp 2 (ℝ × V n)) :
    (coordinateEquiv z).symm p = p.fst • z.val + tangentLift z p.snd := rfl


theorem sphereProjection_modelChart (n : ℕ) (x : Sphere n) :
    sphereProjection n x = modelChartPartialDiffeomorph (I := 𝓡 n) (-spherePole n) x := by
  change stereographic' n (spherePole n) x = stereographic' n (-(-spherePole n)) x
  rw [neg_neg]

theorem sphereProjection_ambientChart (n : ℕ) (x : Sphere n) :
    sphereProjection n x = ambientChart (-spherePole n) x.val :=
  (sphereProjection_modelChart n x).trans (modelChart_apply (-spherePole n) x)

theorem ambientChart_equatorial (z : Sphere n) (x : V (n + 1))
    (hx : inner ℝ z.val x = 0) : ambientChart z x = (2 : ℝ) • linearPart z x := by
  change coordinates z ((2 / (1 - inner ℝ (-z.val) x)) •
    (Tangent z).orthogonalProjectionOnto x) =
      (2 : ℝ) • coordinates z ((Tangent z).orthogonalProjectionOnto x)
  rw [map_smul, inner_neg_left, hx, neg_zero, sub_zero, div_one]

end Wikipedia.HopfProblem.DegreeCollapse.SphereCenteredAmbientChart
