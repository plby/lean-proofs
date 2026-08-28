import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicCylinderPhaseSignBoundary
import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicSphereChartJacobian

/-!
# The actual global map has the common local boundary class at all twelve inputs

Choose the real argument of each scalar phase. The original global sphere
map, in the coherent outward source chart and fixed target chart, is
exactly the cylinder phase/sign formula. Its small-boundary homology maps
therefore agree with one fixed invertible linear model.
-/

noncomputable section

open scoped ContDiff

namespace Wikipedia.HomotopyGroupsOfSpheres.ComplexCrossProductUnitary

open QuaternionicSymmetricMatrices QuaternionicBottMatrix

def negativePhaseCircle (u : unitary ℂ) : Circle :=
  ⟨(negativePhase u).val, mem_sphere_zero_iff_norm.mpr (unitary_complex_norm (negativePhase u))⟩

def negativePhaseAngle (u : unitary ℂ) : ℝ := (negativePhaseCircle u).val.arg

theorem exp_negativePhaseAngle (u : unitary ℂ) :
    Circle.exp (negativePhaseAngle u) = negativePhaseCircle u :=
  Circle.exp_arg (negativePhaseCircle u)

theorem exp_negativePhaseAngle_coe (u : unitary ℂ) :
    (Circle.exp (negativePhaseAngle u) : ℂ) = (negativePhase u).val :=
  congrArg (fun q : Circle ↦ (q : ℂ)) (exp_negativePhaseAngle u)

namespace MidpointSeed

open QuaternionicBottMatrix
open Wikipedia.SmoothSixDPoincare
open Wikipedia.HopfProblem.SingularMayerVietoris

attribute [local irreducible] cylinderPhaseSignDerivativeEquiv

theorem spherePreimageSourceChart_sourcePoint (u : unitary ℂ) (b : Bool × Bool)
    (p : ParameterSpace rotatedInput) :
    spherePreimageSourceChart u b p =
      sphereSourcePoint (CylinderLatitude.time p.1) (CylinderLatitude.time p.2.1)
        (preimageSourceChart u b p.2.2) := by
  rw [spherePreimageSourceChart, transportedSphereSourceChart_is_centered,
    sphereSourceChart_eq_sourcePoint]
  change sphereSourcePoint (CylinderLatitude.time p.1) (CylinderLatitude.time p.2.1)
    (SphereCenteredCoordinates.inverse
      (SphereCenteredCoordinates.sphereIsometry (preimageSourceIsometry u b) rotatedInput)
      (SphereCenteredCoordinates.tangentIsometry (preimageSourceIsometry u b)
        rotatedInput p.2.2)) = _
  rw [SphereCenteredCoordinates.inverse_tangentIsometry]
  rfl

theorem preimageSourceChart_symmetric (u : unitary ℂ) (hu : u.val ^ 3 = -1)
    (b : Bool × Bool) (v : SphereCenteredCoordinates.Tangent rotatedInput) :
    symmetricMap (preimageSourceChart u b v) =
      scale (Circle.exp (negativePhaseAngle u))
        (symmetricMap (rotationSphere (signSphere b.1 b.2
          (SphereCenteredCoordinates.inverse rotatedInput v)))) := by
  rw [preimageSourceChart, preimageSourceIsometry_sphere]
  apply Subtype.ext
  apply Subtype.ext
  rw [symmetricMap_scalarSphere (negativePhase u) (negativePhase_cube u hu)]
  change (negativePhase u).val • _ = (Circle.exp (negativePhaseAngle u) : ℂ) • _
  rw [exp_negativePhaseAngle_coe]

theorem sphereCandidateProjection_preimageChart (u : unitary ℂ) (hu : u.val ^ 3 = -1)
    (b : Bool × Bool) (p : ParameterSpace rotatedInput) :
    (sphereCandidateProjection (spherePreimageSourceChart u b p)).val =
      phaseProjection (signSphereInput b.1 b.2) (negativePhaseAngle u)
        (signSourceParameterEquiv b.1 b.2 (cylinderAngularParameters rotatedInput p)) := by
  rw [spherePreimageSourceChart_sourcePoint, sphereCandidateProjection_sourcePoint,
    CylinderLatitude.time_angle, CylinderLatitude.time_angle, phaseProjection,
    localSphere_signSourceParameterEquiv]
  change firstColumnFormula (Real.pi / 2 + CylinderLatitude.angleOffset p.1)
    (Real.pi / 2 + CylinderLatitude.angleOffset p.2.1)
      (symmetricMap (preimageSourceChart u b p.2.2)) =
        firstColumnFormula (Real.pi / 2 + CylinderLatitude.angleOffset p.1)
          (Real.pi / 2 + CylinderLatitude.angleOffset p.2.1)
          (scale (Circle.exp (negativePhaseAngle u))
            (symmetricMap (rotationSphere (signSphere b.1 b.2
              (SphereCenteredCoordinates.inverse rotatedInput p.2.2)))))
  rw [preimageSourceChart_symmetric u hu]

theorem sphereCandidateCoordinates_preimageChart (u : unitary ℂ) (hu : u.val ^ 3 = -1)
    (b : Bool × Bool) :
    sphereCandidateCoordinates input ∘ spherePreimageSourceChart u b =
      cylinderPhaseSignCoordinates b.1 b.2 (negativePhaseAngle u) := by
  funext p
  change fixedTargetCoordinates
    (sphereCandidateProjection (spherePreimageSourceChart u b p)).val =
      phaseSignCoordinates b.1 b.2 (negativePhaseAngle u) (cylinderAngularParameters rotatedInput p)
  rw [phaseSignCoordinates_projection, sphereCandidateProjection_preimageChart u hu]

theorem sphereCandidateCoordinates_preimageChart_zero (u : unitary ℂ) (hu : u.val ^ 3 = -1)
    (b : Bool × Bool) :
    (sphereCandidateCoordinates input ∘ spherePreimageSourceChart u b) 0 = 0 := by
  rw [sphereCandidateCoordinates_preimageChart u hu, cylinderPhaseSignCoordinates_zero]

theorem contDiffAt_sphereCandidateCoordinates_preimageChart
    (u : unitary ℂ) (hu : u.val ^ 3 = -1) (b : Bool × Bool) {n : ℕ∞ω} :
    ContDiffAt ℝ n (sphereCandidateCoordinates input ∘ spherePreimageSourceChart u b) 0 := by
  rw [sphereCandidateCoordinates_preimageChart u hu]
  exact contDiffAt_cylinderPhaseSignCoordinates _ _ _

theorem hasFDerivAt_sphereCandidateCoordinates_preimageChart
    (u : unitary ℂ) (hu : u.val ^ 3 = -1) (b : Bool × Bool) :
    HasFDerivAt (sphereCandidateCoordinates input ∘ spherePreimageSourceChart u b)
      (cylinderPhaseSignDerivativeEquiv b.1 b.2 (negativePhaseAngle u)).toContinuousLinearMap
      0 := by
  rw [sphereCandidateCoordinates_preimageChart u hu]
  exact hasFDerivAt_cylinderPhaseSignDerivativeEquiv _ _ _

def spherePreimageBoundary (u : unitary ℂ) (hu : u.val ^ 3 = -1) (b : Bool × Bool) :
    LocalDegree.BoundaryData (sphereCandidateCoordinates input ∘ spherePreimageSourceChart u b)
      (cylinderPhaseSignDerivativeEquiv b.1 b.2 (negativePhaseAngle u)) Set.univ :=
  Classical.choice (LocalDegree.nonempty_boundaryData_of_contDiffAt
    (cylinderPhaseSignDerivativeEquiv b.1 b.2 (negativePhaseAngle u))
    (hasFDerivAt_sphereCandidateCoordinates_preimageChart u hu b)
    (sphereCandidateCoordinates_preimageChart_zero u hu b) Filter.univ_mem
    (contDiffAt_sphereCandidateCoordinates_preimageChart u hu b))

theorem spherePreimageBoundary_homology_eq (u : unitary ℂ) (hu : u.val ^ 3 = -1)
    (b : Bool × Bool) (k : ℕ) :
    singularHomologyMap (spherePreimageBoundary u hu b).normalizedMap k =
      singularHomologyMap (cylinderPhaseSignBoundary true true 0).normalizedMap k :=
  LocalBoundaryComparison.normalized_homology_eq (parameterBasis rotatedInput)
    (spherePreimageBoundary u hu b) (cylinderPhaseSignBoundary true true 0)
      (cylinderPhaseSignDerivative_relative_det_pos b.1 b.2 (negativePhaseAngle u)) k

theorem targetPreimage_has_coherent_chart (x : Sphere 7) (hx : x ∈ sphereCandidateTargetPreimage) :
    ∃ (r : Fin 3) (b : Bool × Bool),
      spherePreimageEuclideanChart (midpointPhases r) b 0 = x := by
  rw [sphereCandidateTargetPreimage_eq_image] at hx
  obtain ⟨z, hz, rfl⟩ := hx
  rw [midpointTargetPreimage_eq_union] at hz
  obtain ⟨r, hr⟩ := Set.mem_iUnion.mp hz
  obtain ⟨b, hb⟩ := midpoint_fiber_eq_phaseInput z (midpointPhases r) (midpointPhases_cube r) hr
  refine ⟨r, b, ?_⟩
  rw [spherePreimageEuclideanChart_zero, hb]

theorem twelvePreimageBoundary_homology_eq (r : Fin 3) (b : Bool × Bool) (k : ℕ) :
    singularHomologyMap
      (spherePreimageBoundary (midpointPhases r) (midpointPhases_cube r) b).normalizedMap k =
        singularHomologyMap (cylinderPhaseSignBoundary true true 0).normalizedMap k :=
  spherePreimageBoundary_homology_eq _ (midpointPhases_cube r) b k

end MidpointSeed

end Wikipedia.HomotopyGroupsOfSpheres.ComplexCrossProductUnitary
