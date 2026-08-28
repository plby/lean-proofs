import Wikipedia.HopfProblem.DegreeCollapseQuaternionicHopfFiniteNormal
import Wikipedia.HopfProblem.DegreeCollapseSphereFiniteProductDerivative
import Wikipedia.HopfProblem.DegreeCollapseQuaternionicHopfProductImmersion
import Wikipedia.HopfProblem.DegreeCollapseSphereProductSmoothRegularity

/-!
# Smooth transverse Hopf product columns in the original finite coordinates

First take the finite Hopf right inverse times the real identity. Then
take two copies and retain both original coordinate equivalences. The
result is a smooth right inverse of the actual finite smash-map derivative
along the specified product fiber. No ambient sphere radial column or
geometric framing class is supplied by definition.
-/

noncomputable section

open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.QuaternionicHopfFiniteProductFrame

open NoExoticSixSphere QuaternionicHopf
open FiniteSphereProductCharts hiding V
open QuaternionicHopfFiniteFrame QuaternionicHopfFiniteNormal

theorem hopf_image_ne_pole (q : Sphere 3) :
    sphereMap (SphereFiniteRepresentative.point 7 (finitePoint q)) ≠ spherePole 4 := by
  rw [point_finitePoint, QuaternionicHopfSouthFiber.sphereMap_fiberPoint]
  exact QuaternionicHopfSouthFiber.point_ne_pole

def suspendedPoint (q : Sphere 3) : V 8 := lineCoordinates 7 (finitePoint q, 0)

theorem projection_suspendedInclusion (q : Sphere 3) :
    sphereProjection 8 (QuaternionicHopfProductImmersion.suspendedInclusion q) =
      suspendedPoint q := by
  change sphereProjection 8
    (ProductSphereFiber.slice 7 (QuaternionicHopfSouthFiber.fiberPoint q)) = _
  rw [slice_finite 7 (QuaternionicHopfSouthFiber.fiberPoint_ne_pole q)]
  change sphereProjection 8 (SphereFiniteRepresentative.point 8
    (lineCoordinates 7 (finitePoint q, 0))) = _
  rw [SphereFiniteRepresentative.projection_point]
  rfl

theorem point_suspendedPoint (q : Sphere 3) :
    SphereFiniteRepresentative.point 8 (suspendedPoint q) =
      QuaternionicHopfProductImmersion.suspendedInclusion q := by
  rw [← projection_suspendedInclusion, SphereFiniteRepresentative.point_projection 8
    (QuaternionicHopfProductImmersion.suspendedInclusion_ne_pole q)]

theorem suspended_image_ne_pole (q : Sphere 3) :
    suspendedMap.val (SphereFiniteRepresentative.point 8 (suspendedPoint q)) ≠ spherePole 5 := by
  rw [point_suspendedPoint]
  have h : suspendedMap.val (QuaternionicHopfProductImmersion.suspendedInclusion q) =
      QuaternionicHopfProductFiber.suspendedPoint :=
    (congrArg suspendedMap.val
      (QuaternionicHopfProductFiber.suspendedFiberHomeomorph_val q)).symm.trans
        (QuaternionicHopfProductFiber.suspendedFiberHomeomorph q).property
  exact fun hp ↦ QuaternionicHopfProductFiber.suspendedPoint_ne_pole (h.symm.trans hp)

theorem suspended_contMDiffAt (q : Sphere 3) :
    ContMDiffAt (𝓡 8) (𝓡 5) ∞ suspendedMap.val
      (SphereFiniteRepresentative.point 8 (suspendedPoint q)) :=
  SphereProductSmoothRegularity.product_contMDiffAt basedMap (finitePoint q, 0)
    contMDiff_sphereMap.contMDiffAt (hopf_image_ne_pole q)

theorem suspended_value_zero (q : Sphere 3) :
    SphereFiniteRepresentative.value suspendedMap.val (suspendedPoint q) = 0 := by
  have h := SphereFiniteProductDerivative.value_product basedMap (finitePoint q, 0)
    (hopf_image_ne_pole q)
  change SphereFiniteRepresentative.value suspendedMap.val (suspendedPoint q) =
    lineCoordinates 4 (SphereFiniteRepresentative.value sphereMap (finitePoint q), 0) at h
  rw [value_zero] at h
  exact h.trans (map_zero (lineCoordinates 4))

def suspendedRightInverse (q : Sphere 3) : V 5 →L[ℝ] V 8 :=
  (lineCoordinates 7).toContinuousLinearMap.comp
    (((rightInverse q).prodMap (ContinuousLinearMap.id ℝ ℝ)).comp
      (lineCoordinates 4).symm.toContinuousLinearMap)

theorem suspended_fderiv (q : Sphere 3) :
    fderiv ℝ (SphereFiniteRepresentative.value suspendedMap.val) (suspendedPoint q) =
      (lineCoordinates 4).toContinuousLinearMap.comp
        (((fderiv ℝ (SphereFiniteRepresentative.value sphereMap) (finitePoint q)).prodMap
          (ContinuousLinearMap.id ℝ ℝ)).comp (lineCoordinates 7).symm.toContinuousLinearMap) :=
  SphereFiniteProductDerivative.fderiv_product basedMap (finitePoint q, 0)
    contMDiff_sphereMap.contMDiffAt (hopf_image_ne_pole q)

theorem suspended_derivative_rightInverse (q : Sphere 3) (w : V 5) :
    fderiv ℝ (SphereFiniteRepresentative.value suspendedMap.val) (suspendedPoint q)
      (suspendedRightInverse q w) = w := by
  rw [suspended_fderiv]
  change lineCoordinates 4
    (((fderiv ℝ (SphereFiniteRepresentative.value sphereMap) (finitePoint q)).prodMap
      (ContinuousLinearMap.id ℝ ℝ))
      ((lineCoordinates 7).symm (lineCoordinates 7
        (rightInverse q ((lineCoordinates 4).symm w).1, ((lineCoordinates 4).symm w).2)))) = w
  rw [ContinuousLinearEquiv.symm_apply_apply]
  change lineCoordinates 4
    (fderiv ℝ (SphereFiniteRepresentative.value sphereMap) (finitePoint q)
      (rightInverse q ((lineCoordinates 4).symm w).1), ((lineCoordinates 4).symm w).2) = w
  rw [finite_derivative_rightInverse]
  exact (lineCoordinates 4).apply_symm_apply w

theorem contMDiff_suspendedPoint : ContMDiff (𝓡 3) 𝓘(ℝ, V 8) ∞ suspendedPoint :=
  (lineCoordinates 7).contDiff.contMDiff.comp
    (contMDiff_finitePoint.prodMk_space contMDiff_const)

theorem contMDiff_suspendedRightInverse :
    ContMDiff (𝓡 3) 𝓘(ℝ, V 5 →L[ℝ] V 8) ∞ suspendedRightInverse :=
  contMDiff_const.clm_comp
    ((contMDiff_rightInverse.clm_prodMap contMDiff_const).clm_comp contMDiff_const)

def squarePoint (p : Sphere 3 × Sphere 3) : V 16 :=
  sumCoordinates 8 (suspendedPoint p.1, suspendedPoint p.2)

theorem point_squarePoint (p : Sphere 3 × Sphere 3) :
    SphereFiniteRepresentative.point 16 (squarePoint p) =
      QuaternionicHopfProductImmersion.fiberInclusion p := by
  have h := pairing_finite 8
    (QuaternionicHopfProductImmersion.suspendedInclusion_ne_pole p.1)
    (QuaternionicHopfProductImmersion.suspendedInclusion_ne_pole p.2)
  rw [projection_suspendedInclusion, projection_suspendedInclusion] at h
  exact h.symm

theorem projection_fiberInclusion (p : Sphere 3 × Sphere 3) :
    sphereProjection 16 (QuaternionicHopfProductImmersion.fiberInclusion p) = squarePoint p := by
  rw [← point_squarePoint, SphereFiniteRepresentative.projection_point]

theorem square_value_zero (p : Sphere 3 × Sphere 3) :
    SphereFiniteRepresentative.value (SphereSmash.squareMap suspendedMap) (squarePoint p) = 0 := by
  have h := SphereFiniteProductDerivative.value_square suspendedMap
    (suspendedPoint p.1, suspendedPoint p.2)
    (suspended_image_ne_pole p.1) (suspended_image_ne_pole p.2)
  change SphereFiniteRepresentative.value
    (SphereSmash.squareMap suspendedMap) (squarePoint p) =
    sumCoordinates 5
      (SphereFiniteRepresentative.value suspendedMap.val (suspendedPoint p.1),
        SphereFiniteRepresentative.value suspendedMap.val (suspendedPoint p.2)) at h
  rw [suspended_value_zero, suspended_value_zero] at h
  exact h.trans (map_zero (sumCoordinates 5))

def squareRightInverse (p : Sphere 3 × Sphere 3) : V 10 →L[ℝ] V 16 :=
  (sumCoordinates 8).toContinuousLinearMap.comp
    (((suspendedRightInverse p.1).prodMap (suspendedRightInverse p.2)).comp
      (sumCoordinates 5).symm.toContinuousLinearMap)

theorem square_fderiv (p : Sphere 3 × Sphere 3) :
    fderiv ℝ (SphereFiniteRepresentative.value (SphereSmash.squareMap suspendedMap))
      (squarePoint p) = (sumCoordinates 5).toContinuousLinearMap.comp
        (((fderiv ℝ (SphereFiniteRepresentative.value suspendedMap.val)
          (suspendedPoint p.1)).prodMap
          (fderiv ℝ (SphereFiniteRepresentative.value suspendedMap.val) (suspendedPoint p.2))).comp
          (sumCoordinates 8).symm.toContinuousLinearMap) :=
  SphereFiniteProductDerivative.fderiv_square (m := 8) (n := 5) suspendedMap
    (suspendedPoint p.1, suspendedPoint p.2)
    (suspended_contMDiffAt p.1) (suspended_contMDiffAt p.2)
    (suspended_image_ne_pole p.1) (suspended_image_ne_pole p.2)

theorem square_derivative_rightInverse (p : Sphere 3 × Sphere 3) (w : V 10) :
    fderiv ℝ (SphereFiniteRepresentative.value (SphereSmash.squareMap suspendedMap))
      (squarePoint p) (squareRightInverse p w) = w := by
  rw [square_fderiv, squareRightInverse]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.symm_apply_apply, ContinuousLinearMap.coe_prodMap', Prod.map_apply',
    suspended_derivative_rightInverse, Prod.mk.eta, ContinuousLinearEquiv.apply_symm_apply]

theorem contMDiff_squarePoint :
    ContMDiff ((𝓡 3).prod (𝓡 3)) 𝓘(ℝ, V 16) ∞ squarePoint :=
  (sumCoordinates 8).contDiff.contMDiff.comp
    ((contMDiff_suspendedPoint.comp contMDiff_fst).prodMk_space
      (contMDiff_suspendedPoint.comp contMDiff_snd))

theorem contMDiff_squareRightInverse :
    ContMDiff ((𝓡 3).prod (𝓡 3)) 𝓘(ℝ, V 10 →L[ℝ] V 16) ∞ squareRightInverse :=
  contMDiff_const.clm_comp
    (((contMDiff_suspendedRightInverse.comp contMDiff_fst).clm_prodMap
      (contMDiff_suspendedRightInverse.comp contMDiff_snd)).clm_comp contMDiff_const)

theorem square_derivative_surjective (p : Sphere 3 × Sphere 3) :
    Function.Surjective (fderiv ℝ (SphereFiniteRepresentative.value
      (SphereSmash.squareMap suspendedMap)) (squarePoint p)) :=
  fun w ↦ ⟨squareRightInverse p w, square_derivative_rightInverse p w⟩

end Wikipedia.HopfProblem.DegreeCollapse.QuaternionicHopfFiniteProductFrame
