import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicSecondBottReduction
import Wikipedia.HomotopyGroupsOfSpheres.SymmetricUnitarySpecialHomotopy

/-!
# Reduction of the remaining symplectic groups to symmetric special-unitary matrices

Compose the proved two-step Bott reduction with the explicit matrix
homeomorphism and the determinant-one inclusion isomorphism. The resulting
groups still require the Grassmannian and orthogonal comparison.
-/

noncomputable section

open scoped Topology

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns

open QuaternionicSymmetricMatrices

def symmetricUnitaryCoordinatesMulEquiv (n d : ℕ) [NeZero d] :
    π_ d (AnticommutingStructures.Space (ComplexStructures.standard n))
        (AnticommutingStructures.standard n) ≃*
      π_ d (QuaternionicSymmetricMatrices.Space (Fin (n + 1))) identity :=
  pointedHomeomorphMulEquiv (AnticommutingStructures.symmetricUnitaryHomeomorph n)
    (AnticommutingStructures.standard n) identity
    (AnticommutingStructures.symmetricUnitaryHomeomorph_standard n)

def piSixSpTwoEquivFourthSymmetricSpecialUnitary (n : ℕ) (hn : 6 < n) :
    π_ 6 QuaternionicFibration.SpTwo 1 ≃*
      π_ 4 (SpecialSpace (Fin (n + 1))) specialIdentity :=
  ((piSixSpTwoEquivFourthAnticommutingStructures n hn).trans
    (symmetricUnitaryCoordinatesMulEquiv n 4)).trans (specialInclusionMulEquiv n 2).symm

def piSevenSpTwoEquivFifthSymmetricSpecialUnitary (n : ℕ) (hn : 7 < n) :
    π_ 7 QuaternionicFibration.SpTwo 1 ≃*
      π_ 5 (SpecialSpace (Fin (n + 1))) specialIdentity :=
  ((piSevenSpTwoEquivFifthAnticommutingStructures n hn).trans
    (symmetricUnitaryCoordinatesMulEquiv n 5)).trans (specialInclusionMulEquiv n 3).symm

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns
