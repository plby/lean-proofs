import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicDoubleBottNative
import Wikipedia.HomotopyGroupsOfSpheres.SymmetricUnitaryInverseCoordinates

/-! # The composite Bott isomorphism in symmetric matrix coordinates -/

noncomputable section

open scoped Topology

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicBottMatrix

open QuaternionicColumns QuaternionicSymmetricMatrices

variable {n d : ℕ}

attribute [local irreducible] ComplexStructures.standard AnticommutingStructures.standard
  AnticommutingStructures.ofSymmetricUnitary AnticommutingStructures.symmetricUnitaryHomeomorph
  doubleBottDegreeShiftMulEquiv operatorMatrixCube pointedHomeomorphMulEquiv

def symmetricInputCube (p : GenLoop (Fin d) (Space (Fin (n + 1))) identity) :
    GenLoop (Fin d) (AnticommutingStructures.Space (ComplexStructures.standard n))
      (AnticommutingStructures.standard n) :=
  pointedMapGenLoop ((AnticommutingStructures.symmetricUnitaryHomeomorph n).symm : C(_, _))
    identity (AnticommutingStructures.standard n)
    (AnticommutingStructures.symmetricUnitaryHomeomorph_symm_identity n) p

def symmetricDoubleBottMulEquiv (d : ℕ) [NeZero d] (hd : d + 2 < n) :
    π_ d (Space (Fin (n + 1))) identity ≃* π_ (d + 2) (symplecticSubgroup n) 1 :=
  (pointedHomeomorphMulEquiv (N := Fin d)
    (AnticommutingStructures.symmetricUnitaryHomeomorph n).symm
    identity (AnticommutingStructures.standard n)
    (AnticommutingStructures.symmetricUnitaryHomeomorph_symm_identity n)).trans
      (doubleBottDegreeShiftMulEquiv d (n := n) hd)

theorem symmetricDoubleBottMulEquiv_mk [NeZero d] (hd : d + 2 < n)
    (p : GenLoop (Fin d) (Space (Fin (n + 1))) identity) :
    symmetricDoubleBottMulEquiv d (n := n) hd
      (⟦p⟧ : π_ d (Space (Fin (n + 1))) identity) =
      (⟦operatorMatrixCube (n := n) (d := d) (symmetricInputCube (n := n) p)⟧ :
        π_ (d + 2) (symplecticSubgroup n) 1) := by
  unfold symmetricDoubleBottMulEquiv
  erw [MulEquiv.trans_apply]
  erw [pointedHomeomorphMulEquiv_mk
    (AnticommutingStructures.symmetricUnitaryHomeomorph n).symm
    identity (AnticommutingStructures.standard n)
    (AnticommutingStructures.symmetricUnitaryHomeomorph_symm_identity n) p]
  exact doubleBottDegreeShiftMulEquiv_mk (n := n) (d := d) hd
    (symmetricInputCube (n := n) p)

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicBottMatrix
