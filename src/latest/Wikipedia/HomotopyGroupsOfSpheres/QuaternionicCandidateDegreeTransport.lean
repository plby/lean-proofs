import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicCandidateHomologyCount
import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicSphereTargetFiber

/-!
# Exact target transport from the literal degree map to the counted global map

The quaternionic column and pair models are related by the actual coordinate
isometry. The compactified map is therefore a homeomorphic target change of
the precise seven-sphere map whose degree enters the homotopy exact sequence.
-/

noncomputable section

open scoped Matrix

namespace Wikipedia.HomotopyGroupsOfSpheres.ComplexCrossProductUnitary

open QuaternionicColumns QuaternionicFibration

local notation "ℍ" => Quaternion ℝ
local notation "QSphere" => SphereCenteredCoordinates.UnitSphere (QuaternionSpace 1)

def quaternionPairLinearEquiv : QuaternionSpace 1 ≃ₗ[ℝ] QuaternionPlane where
  toFun v := WithLp.toLp 2 (v 0, v 1)
  invFun v := WithLp.toLp 2 ![v.fst, v.snd]
  left_inv v := by
    apply PiLp.ext
    intro i
    fin_cases i <;> rfl
  right_inv v := rfl
  map_add' v w := rfl
  map_smul' r v := rfl

def quaternionPairIsometry : QuaternionSpace 1 ≃ₗᵢ[ℝ] QuaternionPlane where
  __ := quaternionPairLinearEquiv
  norm_map' v := by
    have h : ‖quaternionPairLinearEquiv v‖ ^ 2 = ‖v‖ ^ 2 := by
      rw [WithLp.prod_norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2, Fin.sum_univ_two]
      rfl
    nlinarith [norm_nonneg (quaternionPairLinearEquiv v), norm_nonneg v]

def quaternionTargetHomeomorph : QSphere ≃ₜ Sphere 7 :=
  (SphereCenteredCoordinates.sphereIsometry quaternionPairIsometry).trans baseSphereHomeomorph

attribute [local irreducible] sphereCandidate

theorem sphereCandidateDegreeMap_quaternion (x : Sphere 7) :
    sphereCandidateDegreeMap x = quaternionTargetHomeomorph (quaternionCandidateMap x) := by
  apply Subtype.ext
  rfl

namespace MidpointSeed

open Wikipedia.HopfProblem.SingularMayerVietoris
  Wikipedia.HopfProblem.PeriodTorusHigherHomology

local notation "Parameters" => ParameterSpace rotatedInput

def degreeTargetHomeomorph : Sphere 7 ≃ₜ OnePoint Parameters :=
  quaternionTargetHomeomorph.symm.trans targetCompactification.symm

theorem compactifiedCandidate_eq_degreeMap :
    compactifiedCandidate =
      (degreeTargetHomeomorph : C(Sphere 7, OnePoint Parameters)).comp
        sphereCandidateDegreeMap := by
  apply ContinuousMap.ext
  intro x
  change targetCompactification.symm (quaternionCandidateMap x) =
    targetCompactification.symm (quaternionTargetHomeomorph.symm (sphereCandidateDegreeMap x))
  rw [sphereCandidateDegreeMap_quaternion, Homeomorph.symm_apply_apply]

def degreeTargetHomologyEquiv :
    SingularHomology (Sphere 7) 7 ≃ₗ[ℤ] SingularHomology (OnePoint Parameters) 7 :=
  homotopyEquivHomologyEquiv degreeTargetHomeomorph.toHomotopyEquiv 7

theorem degreeTargetHomologyEquiv_apply (a : SingularHomology (Sphere 7) 7) :
    degreeTargetHomologyEquiv a =
      singularHomologyMap (degreeTargetHomeomorph : C(Sphere 7, OnePoint Parameters)) 7 a := rfl

def degreeHomologyAutomorphism :
    SingularHomology (Sphere 7) 7 ≃ₗ[ℤ] SingularHomology (Sphere 7) 7 :=
  candidateHomologyComparison.trans degreeTargetHomologyEquiv.symm

theorem sphereCandidateDegreeMap_homology_twelve (a : SingularHomology (Sphere 7) 7) :
    singularHomologyMap sphereCandidateDegreeMap 7 a = (12 : ℕ) • degreeHomologyAutomorphism a := by
  apply degreeTargetHomologyEquiv.injective
  have h := compactifiedCandidate_homology_twelve a
  rw [compactifiedCandidate_eq_degreeMap, singularHomologyMap_comp, LinearMap.comp_apply] at h
  rw [map_nsmul, degreeTargetHomologyEquiv_apply]
  rw [h]
  change (12 : ℕ) • candidateHomologyComparison a =
    (12 : ℕ) • degreeTargetHomologyEquiv
      (degreeTargetHomologyEquiv.symm (candidateHomologyComparison a))
  rw [LinearEquiv.apply_symm_apply]

end MidpointSeed

end Wikipedia.HomotopyGroupsOfSpheres.ComplexCrossProductUnitary
