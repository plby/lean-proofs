import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicStableBottInput
import Wikipedia.HomotopyGroupsOfSpheres.PointedMapEvaluation

/-! # The actual stable Bott image in the quaternionic matrix model -/

noncomputable section

open scoped Topology unitInterval

namespace Wikipedia.HomotopyGroupsOfSpheres.ComplexCrossProductUnitary

open QuaternionicColumns QuaternionicSymmetricMatrices QuaternionicBottMatrix

theorem operatorInverse_one : (symplecticHomeomorph 11).symm 1 = 1 :=
  (symplecticMulEquiv 11).symm.map_one

def matrixBottInputMulEquiv :
    π_ 5 (Space (Fin 12)) identity ≃* π_ 7 (SpGroup (Fin 12)) 1 :=
  stableBottInputMulEquiv.trans
    (pointedHomeomorphMulEquiv (N := Fin 7) (symplecticHomeomorph 11).symm 1 1 operatorInverse_one)

def matrixBottCube : GenLoop (Fin 7) (SpGroup (Fin 12)) 1 :=
  pointedMapGenLoop ((symplecticHomeomorph 11).symm : C(_, _)) 1 1
    operatorInverse_one stableBottCube

theorem matrixBottInputMulEquiv_class :
    matrixBottInputMulEquiv (stableInputClass 9) =
      (⟦matrixBottCube⟧ : π_ 7 (SpGroup (Fin 12)) 1) := by
  unfold matrixBottInputMulEquiv
  erw [MulEquiv.trans_apply, stableBottInputMulEquiv_class, pointedHomeomorphMulEquiv_mk]
  rfl

theorem matrixBottCube_apply (u : Fin 7 → I) :
    matrixBottCube u = QuaternionicColumns.stabilizationIterate 3 9
      (basedRotation ((u 0 : ℝ) * Real.pi) ((u 1 : ℝ) * Real.pi)
        (symmetricMap (parameterCube (Fin.tail (Fin.tail u))))) := by
  change (symplecticHomeomorph 11).symm (stableBottCube u) = _
  rw [stableBottCube_apply, Homeomorph.symm_apply_apply]

end Wikipedia.HomotopyGroupsOfSpheres.ComplexCrossProductUnitary
