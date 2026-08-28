import Wikipedia.HomotopyGroupsOfSpheres.CompactifiedPositiveFiberCount
import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicCandidateSeparatedCover
import Wikipedia.SmoothSixDPoincare.LinearSphereEquiv

/-!
# The actual global candidate acts by twelve times a homology isomorphism

All finite-fiber, native regularity, orientation, and neighborhood hypotheses
are supplied by the checked candidate. The result concerns its global map,
not a formal sum of assigned local signs.
-/

noncomputable section

open scoped ContDiff Manifold

namespace Wikipedia.HomotopyGroupsOfSpheres.ComplexCrossProductUnitary.MidpointSeed

open Wikipedia.SmoothSixDPoincare
open Wikipedia.HopfProblem.SingularMayerVietoris

local notation "Parameters" => ParameterSpace rotatedInput
local notation "BoundarySphere" => Metric.sphere (0 : Parameters) 1

attribute [local irreducible] SpherePoint.outwardClassEquiv OnePointCover.sphereHomologyEquiv
  LinearSphereAction.homologyEquiv

def candidateTargetHomologyEquiv :
    SingularHomology (OnePoint Parameters) 7 ≃ₗ[ℤ] SingularHomology BoundarySphere 6 :=
  OnePointCover.sphereHomologyEquiv 1 zero_lt_one 5

theorem candidateTargetHomologyEquiv_apply
    (a : SingularHomology (OnePoint Parameters) 7) :
    candidateTargetHomologyEquiv a = OnePointCover.sphereConnecting 1 zero_lt_one 6 a :=
  OnePointCover.sphereHomologyEquiv_apply 1 zero_lt_one 5 a

def candidateSourceHomologyEquiv :
    SingularHomology (Sphere 7) 7 ≃ₗ[ℤ] SingularHomology BoundarySphere 6 :=
  (SpherePoint.outwardClassEquiv 5 (sourceRadialEquiv rotatedInput)
    (sourceEuclideanEquiv rotatedInput) 5).trans
      (LinearSphereAction.homologyEquiv (sourceEuclideanEquiv rotatedInput) 6)

theorem candidateSourceHomologyEquiv_apply (a : SingularHomology (Sphere 7) 7) :
    candidateSourceHomologyEquiv a =
      singularHomologyMap (LinearSphereAction.sphereMap
        (sourceEuclideanEquiv rotatedInput).toContinuousLinearMap
        (sourceEuclideanEquiv rotatedInput).injective) 6
          (SpherePoint.outwardClass 5 (sourceRadialEquiv rotatedInput)
            (sourceEuclideanEquiv rotatedInput) 5 a) := by
  rw [candidateSourceHomologyEquiv, LinearEquiv.trans_apply,
    LinearSphereAction.homologyEquiv_apply, SpherePoint.outwardClassEquiv_apply]

theorem compactifiedCandidate_homology_count (a : SingularHomology (Sphere 7) 7) :
    candidateTargetHomologyEquiv (singularHomologyMap compactifiedCandidate 7 a) =
      (12 : ℕ) • candidateSourceHomologyEquiv a := by
  let : Fintype sphereCandidateTargetPreimage := sphereCandidateTargetPreimage_finite.fintype
  have hcard : Fintype.card sphereCandidateTargetPreimage = 12 := by
    rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
    exact sphereCandidateTargetPreimage_ncard_eq_twelve
  have h := CompactifiedRegularFiberSum.sphereConnecting_positive_count 5 candidateNeighborhoods
    (sourceRadialEquiv rotatedInput) (sourceEuclideanEquiv rotatedInput) compactifiedCandidate
    compactifiedCandidate_zero_iff compactifiedCandidate_eq_coe
    (fun x hx ↦
      (contMDiffAt_normalizedCandidateCoordinates_target x hx).mdifferentiableAt (by simp))
    isInvertible_normalizedCandidateCoordinates_target normalizedCandidateNormalSign_target
    1 zero_lt_one 5 a
  rw [hcard] at h
  rw [candidateTargetHomologyEquiv_apply, candidateSourceHomologyEquiv_apply]
  exact h

def candidateHomologyComparison :
    SingularHomology (Sphere 7) 7 ≃ₗ[ℤ] SingularHomology (OnePoint Parameters) 7 :=
  candidateSourceHomologyEquiv.trans candidateTargetHomologyEquiv.symm

theorem compactifiedCandidate_homology_twelve (a : SingularHomology (Sphere 7) 7) :
    singularHomologyMap compactifiedCandidate 7 a = (12 : ℕ) • candidateHomologyComparison a := by
  apply candidateTargetHomologyEquiv.injective
  rw [map_nsmul, compactifiedCandidate_homology_count]
  change (12 : ℕ) • candidateSourceHomologyEquiv a =
    (12 : ℕ) • candidateTargetHomologyEquiv
      (candidateTargetHomologyEquiv.symm (candidateSourceHomologyEquiv a))
  rw [LinearEquiv.apply_symm_apply]

end Wikipedia.HomotopyGroupsOfSpheres.ComplexCrossProductUnitary.MidpointSeed
