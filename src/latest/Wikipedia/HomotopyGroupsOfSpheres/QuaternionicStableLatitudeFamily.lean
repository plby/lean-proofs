import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicStableBottInput
import Wikipedia.HomotopyGroupsOfSpheres.LatitudeHomeomorph
import Wikipedia.HomotopyGroupsOfSpheres.LatitudeCubeGeneratorComparison

/-!
# The stabilized candidate and Bott cube use the same actual latitude family

The parameter reflection extends to a sphere homeomorphism. After this change
of coordinates, the native cube of the global family is the previously
constructed Bott cube, with its original matrix formula.
-/

noncomputable section

open scoped Topology unitInterval

namespace Wikipedia.HomotopyGroupsOfSpheres.ComplexCrossProductUnitary

open QuaternionicColumns QuaternionicBottMatrix
open Wikipedia.HopfProblem.SphereHomology
open Wikipedia.HopfProblem.DegreeCollapse.SphereCube
open LatitudeDescent

attribute [local irreducible] symplecticHomeomorph symmetricMap sphereFiveHomeomorph
  unreducedSphereCandidate

def operatorStabilizationMap : C(SpGroup (Fin 3), symplecticSubgroup 11) :=
  (symplecticHomeomorph 11 : C(_, _)).comp (stabilizationIterateMap 3 9)

theorem operatorStabilizationMap_one : operatorStabilizationMap 1 = 1 := by
  change symplecticHomeomorph 11 (QuaternionicColumns.stabilizationIterate 3 9 1) = 1
  rw [map_one]
  exact (symplecticMulEquiv 11).map_one

def sphereParameterChange : Sphere 5 ≃ₜ Sphere 5 :=
  basedSphereFiveHomeomorph.trans sphereFiveHomeomorph.symm

theorem sphereParameterChange_apply (z : Sphere 5) :
    sphereFiveHomeomorph (sphereParameterChange z) = basedSphereFiveHomeomorph z :=
  sphereFiveHomeomorph.apply_symm_apply _

def parameterSourceHomeomorph : Sphere 7 ≃ₜ Sphere 7 :=
  doubleHomeomorph 5 sphereParameterChange

theorem parameterSourceHomeomorph_basepoint :
    parameterSourceHomeomorph (DoubleFamily.latitudeBasepoint 5) = sphereCandidateBasepoint := by
  rw [parameterSourceHomeomorph, DoubleFamily.latitudeBasepoint, doubleHomeomorph_point]
  exact Latitude.point_zero_eq 6 _ _

def operatorSphereCandidate : C(Sphere 7, symplecticSubgroup 11) :=
  (symplecticHomeomorph 11 : C(SpGroup (Fin 12), symplecticSubgroup 11)).comp
    (stableSphereCandidate 9)

theorem operatorSphereCandidate_basepoint :
    operatorSphereCandidate sphereCandidateBasepoint = 1 := by
  change symplecticHomeomorph 11 (stableSphereCandidate 9 sphereCandidateBasepoint) = 1
  rw [stableSphereCandidate_basepoint]
  exact (symplecticMulEquiv 11).map_one

def stableOperatorFamily : DoubleFamily 5 (symplecticSubgroup 11) 1 :=
  (unreducedSphereFamily.reparametrize sphereParameterChange).postcompose
    operatorStabilizationMap operatorStabilizationMap_one

theorem stableOperatorFamily_apply (s t : I) (z : Sphere 5) :
    stableOperatorFamily.map (s, (t, z)) = operatorStabilizationMap
      (basedRotation ((s : ℝ) * Real.pi) ((t : ℝ) * Real.pi)
        (symmetricMap (basedSphereFiveHomeomorph z))) := by
  change operatorStabilizationMap
    (twoCubeFamily (symmetricMap (sphereFiveHomeomorph (sphereParameterChange z)), ![s, t])) = _
  rw [sphereParameterChange_apply]
  rfl

theorem stableOperatorFamily_parameter_point (s t : I) :
    stableOperatorFamily.map (s, (t, point 5)) = 1 := by
  rw [stableOperatorFamily_apply, basedSphereFiveHomeomorph_point, symmetricMap_axis,
    basedRotation_identity, operatorStabilizationMap_one]

theorem stableOperatorFamily_nativeCube :
    stableOperatorFamily.nativeCube stableOperatorFamily_parameter_point = stableBottCube := by
  apply GenLoop.ext
  intro u
  change stableOperatorFamily.map
    (u 0, (u 1, quotient 5 (Fin.tail (Fin.tail u)))) = stableBottCube u
  rw [stableOperatorFamily_apply, stableBottCube_apply]
  rfl

theorem stableOperatorFamily_nativeClass :
    stableOperatorFamily.nativeClass stableOperatorFamily_parameter_point =
      stableBottInputMulEquiv (stableInputClass 9) := by
  rw [stableBottInputMulEquiv_class]
  change (⟦stableOperatorFamily.nativeCube stableOperatorFamily_parameter_point⟧ :
    π_ 7 (symplecticSubgroup 11) 1) = ⟦stableBottCube⟧
  rw [stableOperatorFamily_nativeCube]

theorem stableOperatorFamily_toSphereMap :
    stableOperatorFamily.toSphereMap =
      operatorSphereCandidate.comp (parameterSourceHomeomorph : C(_, _)) := by
  rw [stableOperatorFamily, DoubleFamily.postcompose_toSphereMap,
    DoubleFamily.reparametrize_toSphereMap]
  simp only [operatorSphereCandidate, stableSphereCandidate, operatorStabilizationMap,
    unreducedSphereCandidate, parameterSourceHomeomorph, ContinuousMap.comp_assoc]

end Wikipedia.HomotopyGroupsOfSpheres.ComplexCrossProductUnitary
