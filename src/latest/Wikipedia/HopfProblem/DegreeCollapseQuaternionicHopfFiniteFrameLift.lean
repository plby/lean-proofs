import Wikipedia.HopfProblem.DegreeCollapseQuaternionicHopfFiniteNormal
import Wikipedia.HopfProblem.DegreeCollapseSphereFiniteFramedCoordinates

/-!
# Lifting the actual finite Hopf columns to their quaternionic formulas

Differentiate the exact forward/inverse chart identity, then use the proved
tangent range to obtain the inverse identity on tangent vectors. This lifts
the original finite right inverse to half the quaternionic normal columns.
The original global framed derivative lifts to the actual south-axis tangent
operator. The suspension's additional real coordinate supplies the radial
half-column without changing its sign or scale.
-/

noncomputable section

open Function
open scoped Quaternion Manifold ContDiff RealInnerProductSpace

namespace Wikipedia.HopfProblem.DegreeCollapse.QuaternionicHopfFiniteFrameLift

open NoExoticSixSphere QuaternionicHopf QuaternionicHopfFiniteFrame
open QuaternionicHopfFiniteNormal
open SphereCenteredAmbientChart hiding V
open SphereFiniteAmbientPoint SphereFiniteRadialCoordinates

theorem ambientChart_inverse (n : ℕ) (u : V n) :
    ambientChart (-spherePole n) (ambientPoint n u) = u := by
  change ambientChart (-spherePole n) (SphereFiniteRepresentative.point n u).val = u
  rw [← sphereProjection_ambientChart, SphereFiniteRepresentative.projection_point]

theorem ambientPoint_finitePoint (q : Sphere 3) :
    ambientPoint 7 (finitePoint q) = QuaternionicHopfSouthPolynomialFrame.inclusion q := by
  change (SphereFiniteRepresentative.point 7 (finitePoint q)).val = _
  rw [point_finitePoint]
  rfl

theorem forward_inverse_derivative (q : Sphere 3) (v : V 7) :
    sourceDifferential q (fderiv ℝ (ambientPoint 7) (finitePoint q) v) = v := by
  have hC : HasFDerivAt (ambientChart (-spherePole 7)) (sourceDifferential q)
      (ambientPoint 7 (finitePoint q)) := by
    rw [ambientPoint_finitePoint]
    exact SphereEquatorialChartDifferential.hasFDerivAt_ambientChart _ _ (source_equatorial q)
  have hA := ((contDiff_ambientPoint 7).differentiable (by simp) (finitePoint q)).hasFDerivAt
  have h := hC.comp (finitePoint q) hA
  have he : ambientChart (-spherePole 7) ∘ ambientPoint 7 = id :=
    funext (ambientChart_inverse 7)
  rw [he] at h
  exact congrArg (fun L : V 7 →L[ℝ] V 7 ↦ L v)
    (h.unique (hasFDerivAt_id (finitePoint q)))

theorem inverse_forward_tangent (q : Sphere 3) (v : V 8)
    (hv : inner ℝ (QuaternionicHopfSouthPolynomialFrame.inclusion q) v = 0) :
    fderiv ℝ (ambientPoint 7) (finitePoint q) (sourceDifferential q v) = v := by
  have hm : v ∈ (fderiv ℝ (ambientPoint 7) (finitePoint q)).range := by
    rw [SphereFiniteAmbientDerivative.derivative_range, ambientPoint_finitePoint]
    exact Submodule.mem_orthogonal_singleton_iff_inner_right.mpr hv
  obtain ⟨w, hw⟩ := hm
  change fderiv ℝ (ambientPoint 7) (finitePoint q) w = v at hw
  rw [← hw, forward_inverse_derivative]

theorem lifted_finite_normal (q : Sphere 3) (w : V 4) :
    fderiv ℝ (ambientPoint 7) (finitePoint q) (rightInverse q w) =
      (1 / 2 : ℝ) • QuaternionicHopfSouthNormal.frame q
        (QuaternionicHopfSouthSphereFrame.targetTailEquiv w) := by
  rw [rightInverse_apply, map_smul, inverse_forward_tangent q _
    (QuaternionicHopfSouthNormal.frame_tangent_sphere q _)]

theorem lifted_normal_coordinates (q : Sphere 3) (r : ℝ) (w : V 4) :
    coordinateOperator (finitePoint q) (WithLp.toLp 2 (r, rightInverse q w)) =
      ((1 / 2 : ℝ) * r) • QuaternionicHopfSouthPolynomialFrame.inclusion q +
        (1 / 2 : ℝ) • QuaternionicHopfSouthNormal.frame q
          (QuaternionicHopfSouthSphereFrame.targetTailEquiv w) := by
  rw [coordinateOperator_apply]
  change ((1 / 2 : ℝ) * r) • ambientPoint 7 (finitePoint q) +
    fderiv ℝ (ambientPoint 7) (finitePoint q) (rightInverse q w) = _
  rw [ambientPoint_finitePoint, lifted_finite_normal]

theorem framedDerivative_coe (q : Sphere 3) :
    SphereThreeTangentFrame.framedDerivative (Subtype.val : Sphere 3 → V 4) q =
      SphereThreeTangentFrame.operator q.val := by
  let : Fact (Module.finrank ℝ (V 4) = 3 + 1) := ⟨finrank_euclideanSpace_fin⟩
  apply ContinuousLinearMap.ext
  intro v
  have ht : SphereThreeTangentFrame.operator q.val v ∈
      (SphereThreeTangentFrame.inclusionDerivative q).range := by
    rw [SphereThreeTangentFrame.range_inclusionDerivative,
      ← SphereThreeTangentFrame.range_operator]
    exact ⟨v, rfl⟩
  obtain ⟨w, hw⟩ := ht
  change SphereThreeTangentFrame.inclusionDerivative q w =
    SphereThreeTangentFrame.operator q.val v at hw
  have h := congrArg (fun L : V 3 →L[ℝ] V 4 ↦ L w)
    (SphereThreeTangentFrame.extensionDerivative_comp_inclusion
      (Subtype.val : Sphere 3 → V 4) contMDiff_coe_sphere q)
  change fderiv ℝ (SmoothSphereAmbient.extension (Stiefel.pole 3)
    (Subtype.val : Sphere 3 → V 4)) q.val (SphereThreeTangentFrame.inclusionDerivative q w) =
      SphereThreeTangentFrame.inclusionDerivative q w at h
  rw [hw] at h
  exact h

theorem framedDerivative_inclusion (q : Sphere 3) :
    SphereThreeTangentFrame.framedDerivative QuaternionicHopfSouthPolynomialFrame.inclusion q =
      QuaternionicHopfSouthFiber.axis.toContinuousLinearMap.comp
        (SphereThreeTangentFrame.operator q.val) := by
  let : Fact (Module.finrank ℝ (V 4) = 3 + 1) := ⟨finrank_euclideanSpace_fin⟩
  have h := SphereFiniteFramedCoordinates.framedDerivative_comp
    QuaternionicHopfSouthFiber.axis.toContinuousLinearMap
    QuaternionicHopfSouthFiber.axis.toContinuousLinearMap.contDiff
    (Subtype.val : Sphere 3 → V 4) contMDiff_coe_sphere q
  rw [ContinuousLinearMap.fderiv, framedDerivative_coe] at h
  exact h

theorem lifted_finite_tangent (q : Sphere 3) :
    (fderiv ℝ (ambientPoint 7) (finitePoint q)).comp
      (SphereThreeTangentFrame.framedDerivative finitePoint q) =
        QuaternionicHopfSouthFiber.axis.toContinuousLinearMap.comp
          (SphereThreeTangentFrame.operator q.val) := by
  have h := SphereFiniteFramedCoordinates.framedDerivative_ambientPoint
    finitePoint contMDiff_finitePoint q
  have he : ambientPoint 7 ∘ finitePoint = QuaternionicHopfSouthPolynomialFrame.inclusion :=
    funext ambientPoint_finitePoint
  rw [he, framedDerivative_inclusion] at h
  exact h.symm

end Wikipedia.HopfProblem.DegreeCollapse.QuaternionicHopfFiniteFrameLift
