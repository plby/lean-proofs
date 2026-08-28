import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicSecondBottHomotopy
import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicFirstBottReduction

/-!
# Two Bott reductions for the quaternionic groups needed in the sphere computation

Compose the actual stable inclusions and both proved Bott maps. The remaining
groups are `π₄` and `π₅` of the anticommuting complex-structure space. No
vanishing, cyclicity, or projection-degree calculation is asserted here.
-/

noncomputable section

open scoped Topology

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns

def piSixSpTwoEquivFourthAnticommutingStructures (n : ℕ) (hn : 6 < n) :
    π_ 6 QuaternionicFibration.SpTwo 1 ≃*
      π_ 4 (AnticommutingStructures.Space (ComplexStructures.standard n))
        (AnticommutingStructures.standard n) :=
  (piSixSpTwoEquivFifthComplexStructures n hn).trans
    (SecondPaths.bottDegreeShiftMulEquiv 4 (AnticommutingStructures.standard n) (by omega)).symm

def piSevenSpTwoEquivFifthAnticommutingStructures (n : ℕ) (hn : 7 < n) :
    π_ 7 QuaternionicFibration.SpTwo 1 ≃*
      π_ 5 (AnticommutingStructures.Space (ComplexStructures.standard n))
        (AnticommutingStructures.standard n) :=
  (piSevenSpTwoEquivSixthComplexStructures n hn).trans
    (SecondPaths.bottDegreeShiftMulEquiv 5 (AnticommutingStructures.standard n) (by omega)).symm

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns
