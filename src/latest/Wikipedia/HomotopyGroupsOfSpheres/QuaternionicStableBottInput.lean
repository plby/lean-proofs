import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicParameterCube
import Wikipedia.HomotopyGroupsOfSpheres.SymmetricDoubleBottNative

/-!
# The stabilized explicit five-sphere input under the native Bott isomorphism

Rank twelve agrees with the rank used in the remaining balanced and spinor
comparisons. The image cube has the original matrix formula after nine actual
stabilizations. Primitivity of this input is not assumed.
-/

noncomputable section

open scoped Topology unitInterval

namespace Wikipedia.HomotopyGroupsOfSpheres.ComplexCrossProductUnitary

open QuaternionicColumns QuaternionicSymmetricMatrices QuaternionicBottMatrix

attribute [local irreducible] ComplexStructures.standard AnticommutingStructures.standard
  AnticommutingStructures.ofSymmetricUnitary AnticommutingStructures.symmetricUnitaryHomeomorph
  doubleBottDegreeShiftMulEquiv

local notation "AntiSpace" => AnticommutingStructures.Space (ComplexStructures.standard 11)
local notation "antiPoint" => AnticommutingStructures.standard 11

def toStableAnticommutingCube (p : GenLoop (Fin 5) (Space (Fin 12)) identity) :
    GenLoop (Fin 5) AntiSpace antiPoint :=
  symmetricInputCube (n := 11) (d := 5) p

def stableBottInputMulEquiv :
    π_ 5 (Space (Fin 12)) identity ≃* π_ 7 (symplecticSubgroup 11) 1 :=
  symmetricDoubleBottMulEquiv 5 (n := 11) (by decide)

theorem stableBottInputMulEquiv_mk (p : GenLoop (Fin 5) (Space (Fin 12)) identity) :
    stableBottInputMulEquiv (⟦p⟧ : π_ 5 (Space (Fin 12)) identity) =
      (⟦operatorMatrixCube (n := 11) (d := 5) (toStableAnticommutingCube p)⟧ :
        π_ 7 (symplecticSubgroup 11) 1) :=
  symmetricDoubleBottMulEquiv_mk (n := 11) (d := 5) (by decide) p

def stableBottCube : GenLoop (Fin 7) (symplecticSubgroup 11) 1 :=
  operatorMatrixCube (n := 11) (d := 5) (toStableAnticommutingCube (stableInputCube 9))

theorem stableBottInputMulEquiv_class :
    stableBottInputMulEquiv (stableInputClass 9) =
      (⟦stableBottCube⟧ : π_ 7 (symplecticSubgroup 11) 1) :=
  stableBottInputMulEquiv_mk (stableInputCube 9)

attribute [local irreducible] symmetricMap parameterCube

theorem stableBottCube_apply (u : Fin 7 → I) :
    stableBottCube u = symplecticHomeomorph 11
      (QuaternionicColumns.stabilizationIterate 3 9
        (basedRotation ((u 0 : ℝ) * Real.pi) ((u 1 : ℝ) * Real.pi)
          (symmetricMap (parameterCube (Fin.tail (Fin.tail u)))))) := by
  rw [stableBottCube, operatorMatrixCube_apply]
  change symplecticHomeomorph 11
    (basedRotation ((u 0 : ℝ) * Real.pi) ((u 1 : ℝ) * Real.pi)
      (AnticommutingStructures.toSymmetricUnitary
        ((AnticommutingStructures.symmetricUnitaryHomeomorph 11).symm
          (stableSymmetricInput 9 (parameterCube (Fin.tail (Fin.tail u))))))) = _
  rw [AnticommutingStructures.symmetricUnitaryHomeomorph_symm_apply,
    AnticommutingStructures.toSymmetricUnitary_ofSymmetricUnitary]
  exact congrArg (symplecticHomeomorph 11)
    (basedRotation_stabilizationIterate ((u 0 : ℝ) * Real.pi) ((u 1 : ℝ) * Real.pi)
      (symmetricMap (parameterCube (Fin.tail (Fin.tail u)))) 9)

end Wikipedia.HomotopyGroupsOfSpheres.ComplexCrossProductUnitary
