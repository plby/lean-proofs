import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicSpecialUnitaryReduction
import Wikipedia.HomotopyGroupsOfSpheres.SymmetricUnitaryReindex
import Wikipedia.HomotopyGroupsOfSpheres.BalancedBottHomotopy

/-!
# Three Bott reductions for the remaining symplectic homotopy groups

Choose an even complex matrix rank, reindex its actual coordinates, and
apply the proved balanced Bott isomorphism. The remaining groups are the
third and fourth native homotopy groups of the balanced real orbit.
-/

noncomputable section

open scoped Topology

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns

open QuaternionicSymmetricMatrices

def balancedIndexEquiv (n : ℕ) (hn : 0 < n) :
    Fin (2 * n - 1 + 1) ≃ BalancedRealInvolutions.Index n :=
  Fintype.equivOfCardEq (by
    simp only [BalancedRealInvolutions.Index, Fintype.card_sum, Fintype.card_fin]
    omega)

def piSixSpTwoEquivThirdBalancedReal (n : ℕ) (hn : 4 < n) :
    π_ 6 QuaternionicFibration.SpTwo 1 ≃*
      π_ 3 (BalancedRealInvolutions.Space n) (BalancedRealInvolutions.standard n) :=
  ((piSixSpTwoEquivFourthSymmetricSpecialUnitary (2 * n - 1) (by omega)).trans
    (specialReindexHomotopyMulEquiv (balancedIndexEquiv n (by omega)) 4)).trans
      (BalancedRealInvolutions.bottDegreeShiftMulEquiv n 3 hn).symm

def piSevenSpTwoEquivFourthBalancedReal (n : ℕ) (hn : 5 < n) :
    π_ 7 QuaternionicFibration.SpTwo 1 ≃*
      π_ 4 (BalancedRealInvolutions.Space n) (BalancedRealInvolutions.standard n) :=
  ((piSevenSpTwoEquivFifthSymmetricSpecialUnitary (2 * n - 1) (by omega)).trans
    (specialReindexHomotopyMulEquiv (balancedIndexEquiv n (by omega)) 5)).trans
      (BalancedRealInvolutions.bottDegreeShiftMulEquiv n 4 hn).symm

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns
