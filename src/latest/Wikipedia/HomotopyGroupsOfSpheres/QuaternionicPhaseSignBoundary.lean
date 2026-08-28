import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicSignBoundaryHomology
import Wikipedia.HomotopyGroupsOfSpheres.PositiveDerivativeTransport

/-!
# One boundary-homology comparison for all scalar phases and sign patterns

All maps use the same source parameter space and the same actual target
chart. Fixed coordinate transport preserves the phase comparison, and
the proved four-sign comparison then identifies one common boundary map.
-/

noncomputable section

open scoped ContDiff

namespace Wikipedia.HomotopyGroupsOfSpheres.ComplexCrossProductUnitary.MidpointSeed

open QuaternionicBottMatrix
open Wikipedia.SmoothSixDPoincare
open Wikipedia.HopfProblem.SingularMayerVietoris

def phaseSignCoordinates (x y : Bool) (a : ℝ) (p : ParameterSpace rotatedInput) :
    TargetSpace input :=
  targetCoordinateTransport (signSphereInput x y) (signSphereInput_hits_target x y)
    (phaseCoordinates (signSphereInput x y) a (signSourceParameterEquiv x y p))

theorem phaseSignCoordinates_projection (x y : Bool) (a : ℝ)
    (p : ParameterSpace rotatedInput) :
    phaseSignCoordinates x y a p =
      fixedTargetCoordinates
        (phaseProjection (signSphereInput x y) a (signSourceParameterEquiv x y p)) :=
  SphereCenteredCoordinates.tangentTransport_stereoToFun
    (localColumn (signSphereInput x y) 0) (localColumn input 0)
    (targetCenter_eq (signSphereInput x y) (signSphereInput_hits_target x y))
    (phaseColumn (signSphereInput x y) a (signSourceParameterEquiv x y p)).val

theorem phaseSignCoordinates_at_zero_phase (x y : Bool) :
    phaseSignCoordinates x y 0 = signCoordinateMap x y := by
  change targetCoordinateTransport (signSphereInput x y) (signSphereInput_hits_target x y) ∘
    phaseCoordinates (signSphereInput x y) 0 ∘ signSourceParameterEquiv x y = _
  rw [phaseCoordinates_at_zero_phase]
  exact (signCoordinateMap_eq_transport x y).symm

theorem phaseSignCoordinates_zero (x y : Bool) (a : ℝ) : phaseSignCoordinates x y a 0 = 0 := by
  rw [phaseSignCoordinates, map_zero,
    phaseCoordinates_zero _ (signSphereInput_hits_target x y), map_zero]

theorem contDiffAt_phaseSignCoordinates (x y : Bool) (a : ℝ) {n : ℕ∞ω} :
    ContDiffAt ℝ n (phaseSignCoordinates x y a) 0 := by
  have h : ContDiffAt ℝ n (phaseCoordinates (signSphereInput x y) a)
      (signSourceParameterEquiv x y 0) := by
    rw [map_zero]
    exact contDiffAt_phaseCoordinates _ (signSphereInput_hits_target x y) a
  exact (targetCoordinateTransport _ (signSphereInput_hits_target x y)).contDiff.contDiffAt.comp 0
    (h.comp 0 (signSourceParameterEquiv x y).contDiff.contDiffAt)

def phaseSignDerivativeEquiv (x y : Bool) (a : ℝ) :
    ParameterSpace rotatedInput ≃L[ℝ] TargetSpace input :=
  ((signSourceParameterEquiv x y).trans
    (phaseDerivativeEquiv (signSphereInput x y) (signSphereInput_hits_target x y) a)).trans
      (targetCoordinateTransport (signSphereInput x y) (signSphereInput_hits_target x y))

theorem hasFDerivAt_phaseSignDerivativeEquiv (x y : Bool) (a : ℝ) :
    HasFDerivAt (phaseSignCoordinates x y a)
      (phaseSignDerivativeEquiv x y a).toContinuousLinearMap 0 := by
  have h : HasFDerivAt (phaseCoordinates (signSphereInput x y) a)
      (phaseDerivativeEquiv _ (signSphereInput_hits_target x y) a).toContinuousLinearMap
      (signSourceParameterEquiv x y 0) := by
    rw [map_zero]
    exact hasFDerivAt_phaseDerivativeEquiv _ (signSphereInput_hits_target x y) a
  let T := targetCoordinateTransport _ (signSphereInput_hits_target x y)
  exact T.toContinuousLinearMap.hasFDerivAt.comp 0
    (h.comp 0 ((signSourceParameterEquiv x y).toContinuousLinearMap.hasFDerivAt (x := 0)))

theorem phaseSignDerivativeEquiv_at_zero_phase (x y : Bool) :
    phaseSignDerivativeEquiv x y 0 = signCoordinateDerivativeEquiv x y := by
  have h := hasFDerivAt_phaseSignDerivativeEquiv x y 0
  rw [phaseSignCoordinates_at_zero_phase] at h
  have he := h.unique (hasFDerivAt_signCoordinateDerivativeEquiv x y)
  apply ContinuousLinearEquiv.ext
  funext p
  exact congrArg (fun L : ParameterSpace rotatedInput →L[ℝ] TargetSpace input ↦ L p) he

theorem phaseSignDerivative_phase_det_pos (x y : Bool) (a : ℝ) :
    0 < ((phaseSignDerivativeEquiv x y a).trans
      (phaseSignDerivativeEquiv x y 0).symm).toLinearMap.det := by
  rw [phaseSignDerivativeEquiv, phaseSignDerivativeEquiv,
    LocalBoundaryComparison.relativeDet_transport]
  change 0 < (phaseDerivativeComparisonEquiv (signSphereInput x y)
    (signSphereInput_hits_target x y) a).toContinuousLinearMap.det
  rw [phaseDerivativeComparisonEquiv_coe]
  exact phaseDerivativeComparison_det_pos _ (signSphereInput_hits_target x y) a

theorem phaseSignDerivative_relative_det_pos (x y : Bool) (a : ℝ) :
    0 < ((phaseSignDerivativeEquiv x y a).trans
      (phaseSignDerivativeEquiv true true 0).symm).toLinearMap.det := by
  apply LocalBoundaryComparison.relativeDet_pos_trans
    (phaseSignDerivativeEquiv x y a) (phaseSignDerivativeEquiv x y 0)
    (phaseSignDerivativeEquiv true true 0) (phaseSignDerivative_phase_det_pos x y a)
  rw [phaseSignDerivativeEquiv_at_zero_phase, phaseSignDerivativeEquiv_at_zero_phase]
  change 0 < (signDerivativeComparisonEquiv x y).toLinearEquiv.toLinearMap.det
  rw [signDerivativeComparisonEquiv_det]
  norm_num

def phaseSignBoundary (x y : Bool) (a : ℝ) :
    LocalDegree.BoundaryData (phaseSignCoordinates x y a)
      (phaseSignDerivativeEquiv x y a) Set.univ :=
  Classical.choice (LocalDegree.nonempty_boundaryData_of_contDiffAt
    (phaseSignDerivativeEquiv x y a) (hasFDerivAt_phaseSignDerivativeEquiv x y a)
    (phaseSignCoordinates_zero x y a) Filter.univ_mem (contDiffAt_phaseSignCoordinates x y a))

theorem phaseSignBoundary_homology_eq (x y : Bool) (a : ℝ) (k : ℕ) :
    singularHomologyMap (phaseSignBoundary x y a).normalizedMap k =
      singularHomologyMap (phaseSignBoundary true true 0).normalizedMap k :=
  LocalBoundaryComparison.normalized_homology_eq (parameterBasis rotatedInput)
    (phaseSignBoundary x y a) (phaseSignBoundary true true 0)
      (phaseSignDerivative_relative_det_pos x y a) k

end Wikipedia.HomotopyGroupsOfSpheres.ComplexCrossProductUnitary.MidpointSeed
