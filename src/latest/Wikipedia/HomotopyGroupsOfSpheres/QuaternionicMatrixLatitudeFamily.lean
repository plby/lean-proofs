import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicMatrixBottInput
import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicStableLatitudeFamily

/-! # The stable latitude family in the original quaternionic matrix model -/

noncomputable section

open scoped Topology unitInterval

namespace Wikipedia.HomotopyGroupsOfSpheres.ComplexCrossProductUnitary

open QuaternionicColumns QuaternionicBottMatrix LatitudeDescent
open Wikipedia.HopfProblem.DegreeCollapse.SphereCube

theorem matrixStabilization_one : stabilizationIterateMap 3 9 1 = 1 :=
  (QuaternionicColumns.stabilizationIterate 3 9).map_one

def stableMatrixFamily : DoubleFamily 5 (SpGroup (Fin 12)) 1 :=
  (unreducedSphereFamily.reparametrize sphereParameterChange).postcompose
    (stabilizationIterateMap 3 9) matrixStabilization_one

theorem stableMatrixFamily_apply (s t : I) (z : Sphere 5) :
    stableMatrixFamily.map (s, (t, z)) = QuaternionicColumns.stabilizationIterate 3 9
      (basedRotation ((s : ℝ) * Real.pi) ((t : ℝ) * Real.pi)
        (symmetricMap (basedSphereFiveHomeomorph z))) := by
  change QuaternionicColumns.stabilizationIterate 3 9
    (twoCubeFamily (symmetricMap (sphereFiveHomeomorph (sphereParameterChange z)), ![s, t])) = _
  rw [sphereParameterChange_apply]
  rfl

theorem stableMatrixFamily_parameter_point (s t : I) :
    stableMatrixFamily.map (s, (t, point 5)) = 1 := by
  rw [stableMatrixFamily_apply, basedSphereFiveHomeomorph_point, symmetricMap_axis,
    basedRotation_identity, map_one]

theorem stableMatrixFamily_nativeCube :
    stableMatrixFamily.nativeCube stableMatrixFamily_parameter_point = matrixBottCube := by
  apply GenLoop.ext
  intro u
  change stableMatrixFamily.map
    (u 0, (u 1, quotient 5 (Fin.tail (Fin.tail u)))) = matrixBottCube u
  rw [stableMatrixFamily_apply, matrixBottCube_apply]
  rfl

theorem stableMatrixFamily_nativeClass :
    stableMatrixFamily.nativeClass stableMatrixFamily_parameter_point =
      matrixBottInputMulEquiv (stableInputClass 9) := by
  rw [matrixBottInputMulEquiv_class]
  change (⟦stableMatrixFamily.nativeCube stableMatrixFamily_parameter_point⟧ :
    π_ 7 (SpGroup (Fin 12)) 1) = ⟦matrixBottCube⟧
  rw [stableMatrixFamily_nativeCube]

theorem stableMatrixFamily_toSphereMap :
    stableMatrixFamily.toSphereMap =
      (stableSphereCandidate 9).comp (parameterSourceHomeomorph : C(Sphere 7, Sphere 7)) := by
  rw [stableMatrixFamily, DoubleFamily.postcompose_toSphereMap,
    DoubleFamily.reparametrize_toSphereMap]
  simp only [stableSphereCandidate, unreducedSphereCandidate, parameterSourceHomeomorph,
    ContinuousMap.comp_assoc]

end Wikipedia.HomotopyGroupsOfSpheres.ComplexCrossProductUnitary
