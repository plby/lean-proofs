import Wikipedia.HopfProblem.DegreeCollapseSphereFiniteTangentDerivative
import Wikipedia.HopfProblem.DegreeCollapseQuaternionicHopfSouthSphereFrame

/-!
# The Hopf normal columns in the actual finite stereographic coordinates

The source chart is differentiated at the original south Hopf fiber. The
fixed target equivalence sends chart coordinates to quaternionic tail
coordinates. Half the transported quaternionic columns give an actual
isometric right inverse of the finite Hopf-map derivative.
-/

noncomputable section

open scoped Quaternion Manifold ContDiff RealInnerProductSpace

namespace Wikipedia.HopfProblem.DegreeCollapse.QuaternionicHopfFiniteFrame

open NoExoticSixSphere QuaternionicHopf QuaternionicHopfSouthPolynomialFrame
open QuaternionicHopfSouthSphereFrame
open SphereCenteredAmbientChart hiding V

theorem target_center : QuaternionicHopfSouthFiber.point = -spherePole 4 := rfl

theorem source_equatorial (q : Sphere 3) :
    inner ℝ (-spherePole 7).val (inclusion q) = 0 := by
  have hp : second (spherePole 7).val = 0 :=
    (QuaternionicHopf.sphereMap_eq_pole_iff _).mp sphereMap_pole
  change inner ℝ (-(spherePole 7).val) (inclusion q) = 0
  rw [inner_neg_left, ← real_inner_comm (spherePole 7).val (inclusion q),
    inner_inclusion, hp, inner_zero_right, neg_zero]

def finitePoint (q : Sphere 3) : V 7 :=
  sphereProjection 7 (QuaternionicHopfSouthFiber.fiberPoint q)

theorem finitePoint_formula (q : Sphere 3) :
    finitePoint q = (2 : ℝ) • linearPart (-spherePole 7) (inclusion q) := by
  rw [finitePoint, sphereProjection_ambientChart]
  exact ambientChart_equatorial _ _ (source_equatorial q)

theorem polynomial_inclusion (q : Sphere 3) :
    polynomial (inclusion q) = QuaternionicHopfSouthFiber.point.val := by
  change polynomial (QuaternionicHopfSouthFiber.fiberPoint q).val = _
  rw [← sphereMap_val, QuaternionicHopfSouthFiber.sphereMap_fiberPoint]

def sourceDifferential (q : Sphere 3) : V 8 →L[ℝ] V 7 :=
  SphereEquatorialChartDifferential.differential (-spherePole 7) (inclusion q)

theorem sourceDifferential_eq_fderiv (q : Sphere 3) :
    sourceDifferential q = fderiv ℝ (ambientChart (-spherePole 7)) (inclusion q) :=
  (SphereEquatorialChartDifferential.fderiv_ambientChart _ _ (source_equatorial q)).symm

theorem finite_derivative_tangent (q : Sphere 3) (v : V 8)
    (hv : inner ℝ (inclusion q) v = 0) :
    fderiv ℝ (SphereFiniteRepresentative.value sphereMap) (finitePoint q)
      (sourceDifferential q v) =
      linearPart QuaternionicHopfSouthFiber.point (fderiv ℝ polynomial (inclusion q) v) := by
  have hx := QuaternionicHopfSouthFiber.fiberPoint_ne_pole q
  have hb : sphereMap (QuaternionicHopfSouthFiber.fiberPoint q) ≠ spherePole 4 := by
    rw [QuaternionicHopfSouthFiber.sphereMap_fiberPoint]
    exact QuaternionicHopfSouthFiber.point_ne_pole
  have hF := SphereFiniteTangentDerivative.value_differentiableAt sphereMap
    (QuaternionicHopfSouthFiber.fiberPoint q) hx contMDiff_sphereMap.contMDiffAt hb
  have hS := (SphereEquatorialChartDifferential.hasFDerivAt_ambientChart _ _
    (source_equatorial q)).differentiableAt
  have hT : DifferentiableAt ℝ (ambientChart (-spherePole 4)) (polynomial (inclusion q)) := by
    rw [polynomial_inclusion, ← target_center]
    exact (SphereCenteredAmbientChart.hasFDerivAt_ambientChart _).differentiableAt
  have h := SphereFiniteTangentDerivative.fderiv_value_tangent sphereMap polynomial sphereMap_val
    (QuaternionicHopfSouthFiber.fiberPoint q) hx hF hS hT
    (contDiff_polynomial.differentiable (by simp) _) v hv
  change fderiv ℝ (SphereFiniteRepresentative.value sphereMap) (finitePoint q)
    (fderiv ℝ (ambientChart (-spherePole 7)) (inclusion q) v) =
      fderiv ℝ (ambientChart (-spherePole 4)) (polynomial (inclusion q))
        (fderiv ℝ polynomial (inclusion q) v) at h
  rw [← sourceDifferential_eq_fderiv, polynomial_inclusion, ← target_center,
    (SphereCenteredAmbientChart.hasFDerivAt_ambientChart _).fderiv] at h
  exact h

def rightInverse (q : Sphere 3) : V 4 →L[ℝ] V 7 :=
  (1 / 2 : ℝ) • (sourceDifferential q).comp
    ((QuaternionicHopfSouthNormal.frame q).comp targetTailEquiv.toContinuousLinearMap)

theorem rightInverse_apply (q : Sphere 3) (w : V 4) :
    rightInverse q w = (1 / 2 : ℝ) • sourceDifferential q
      (QuaternionicHopfSouthNormal.frame q (targetTailEquiv w)) := rfl

theorem finite_derivative_rightInverse (q : Sphere 3) (w : V 4) :
    fderiv ℝ (SphereFiniteRepresentative.value sphereMap) (finitePoint q)
      (rightInverse q w) = w := by
  rw [rightInverse_apply, map_smul, finite_derivative_tangent q _
    (QuaternionicHopfSouthNormal.frame_tangent_sphere q _)]
  have hd := QuaternionicHopfSouthNormal.polynomial_derivative_frame q (targetTailEquiv w)
  change fderiv ℝ polynomial (inclusion q)
    (QuaternionicHopfSouthNormal.frame q (targetTailEquiv w)) = _ at hd
  rw [hd]
  have hj : SphereCylinder.join 3 (0, (2 : ℝ) • targetTailEquiv w) =
      tangentLift QuaternionicHopfSouthFiber.point ((2 : ℝ) • w) := by
    rw [tangentLift_eq_join, map_smul, targetTailEquiv_apply]
  rw [hj, linearPart_tangentLift, smul_smul]
  norm_num

theorem rightInverse_norm (q : Sphere 3) (w : V 4) : ‖rightInverse q w‖ = ‖w‖ := by
  rw [rightInverse_apply]
  have h := SphereEquatorialChartDifferential.half_differential_norm (-spherePole 7)
    (QuaternionicHopfSouthFiber.fiberPoint q) (source_equatorial q)
    (QuaternionicHopfSouthNormal.frame q (targetTailEquiv w))
    (QuaternionicHopfSouthNormal.frame_tangent_sphere q _)
  change ‖(1 / 2 : ℝ) • sourceDifferential q
    (QuaternionicHopfSouthNormal.frame q (targetTailEquiv w))‖ = _ at h
  rw [h, QuaternionicHopfSouthNormal.frame_norm, targetTailEquiv.norm_map]

def rightInverseIsometry (q : Sphere 3) : V 4 →ₗᵢ[ℝ] V 7 where
  toLinearMap := (rightInverse q).toLinearMap
  norm_map' := rightInverse_norm q

theorem finite_derivative_surjective (q : Sphere 3) :
    Function.Surjective
      (fderiv ℝ (SphereFiniteRepresentative.value sphereMap) (finitePoint q)) :=
  fun w ↦ ⟨rightInverse q w, finite_derivative_rightInverse q w⟩

end Wikipedia.HopfProblem.DegreeCollapse.QuaternionicHopfFiniteFrame
