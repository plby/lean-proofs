import Wikipedia.HomotopyGroupsOfSpheres.CliffordFiveHermitian
import Wikipedia.HomotopyGroupsOfSpheres.UnitaryMixingLinearization
import Wikipedia.HomotopyGroupsOfSpheres.PointedHomotopyPrecomposition

/-!
# A based homotopy to the realified Clifford family

The endpoint formula is an equality of actual symmetric unitary matrices.
No assertion about a generator or a Bott inverse is assumed here.
-/

noncomputable section

open scoped Matrix unitInterval

namespace Wikipedia.HomotopyGroupsOfSpheres.ComplexCliffordFive

open ComplexCrossProductUnitary QuaternionicSymmetricMatrices

def realCoordinates (z : Vector) : CliffordFiveHermitian.Coordinates :=
  ![(z 0).im, (z 1).re, (z 1).im, (z 2).re, (z 2).im]

theorem matrix_eq_realCoordinates (z : Vector) :
    matrix z = ((z 0).re : ℂ) • 1 +
      Complex.I • CliffordFiveHermitian.matrix (realCoordinates z) := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    norm_num [matrix, CliffordFiveHermitian.matrix, realCoordinates,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Complex.mul_re, Complex.mul_im]

def blockIncludedSymmetricMap : C(UnitSphere, Space (Fin 4 ⊕ Fin 4)) :=
  UnitaryBlockConjugation.source.comp unitaryMap

def linearizedSymmetricMap : C(UnitSphere, Space (Fin 4 ⊕ Fin 4)) :=
  UnitaryBlockConjugation.target.comp unitaryMap

theorem linearizedSymmetricMap_val (z : UnitSphere) :
    (linearizedSymmetricMap z).val.val = ((z.val 0).re : ℂ) • 1 +
      Complex.I • RealUnitaryMatrices.complexification
        (ComplexMatrixRealification.matrix
          (CliffordFiveHermitian.matrix (realCoordinates z.val))) := by
  change (UnitaryBlockConjugation.target (unitaryMap z)).val.val = _
  rw [UnitaryBlockConjugation.target_val, unitaryMap_val, matrix_eq_realCoordinates,
    UnitaryBlockConjugation.linearization_hermitian _ _
      (CliffordFiveHermitian.matrix_hermitian _)]

attribute [local irreducible] UnitaryBlockConjugation.source
  UnitaryBlockConjugation.target UnitaryBlockConjugation.mixingHomotopy unitaryMap

def blockMixingHomotopy :
    blockIncludedSymmetricMap.HomotopyRel linearizedSymmetricMap {axis} :=
  pointedHomotopyPrecomp (f := UnitaryBlockConjugation.source)
    (g := UnitaryBlockConjugation.target) (y := 1)
    UnitaryBlockConjugation.mixingHomotopy unitaryMap axis unitaryMap_axis

end Wikipedia.HomotopyGroupsOfSpheres.ComplexCliffordFive
