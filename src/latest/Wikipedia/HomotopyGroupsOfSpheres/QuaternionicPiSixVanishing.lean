import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicOrthogonalReduction
import Wikipedia.HomotopyGroupsOfSpheres.RankSixComplexStructurePiOne
import Wikipedia.NoExoticSixSphere.OrthogonalBottDegreeShift

/-!
# The actual sixth homotopy group of Sp(2) vanishes

The three symplectic Bott comparisons and the frame connecting isomorphism
reduce this to the second orthogonal group at rank six. The checked
orthogonal Bott comparison and spinor loop contraction finish the calculation.
-/

noncomputable section

open scoped Topology

namespace Wikipedia.HomotopyGroupsOfSpheres

open NoExoticSixSphere NoExoticSixSphere.GLOrthonormalization

namespace OrthogonalLowGroups

def rankSixStructure : OrthogonalComplexStructures.Space 6 := by
  let q : RankSixComplexProjection.UnitSpinor :=
    Classical.choice (NormedSpace.sphere_nonempty_rclike ℂ zero_le_one)
  exact RankSixComplexProjection.fromSpinor q

def rankSixDegreeShiftMulEquiv (d : ℕ) [NeZero d] (hd : d + 3 < 6) :
    π_ d (OrthogonalComplexStructures.Space 6) rankSixStructure ≃*
      π_ (d + 1) (OrthogonalOperators 6) 1 :=
  OrthogonalPolygon.bottDegreeShiftMulEquiv d 1
    (OrthogonalExponential.exp (Real.pi • rankSixStructure.val))
    (by simpa only [inv_one, one_mul] using OrthogonalComplexStructures.exp_pi rankSixStructure)
    rankSixStructure hd

theorem piTwoRankSix_subsingleton : Subsingleton (π_ 2 (OrthogonalOperators 6) 1) := by
  let := RankSixComplexProjection.complexStructure_piOne_subsingleton rankSixStructure
  exact (rankSixDegreeShiftMulEquiv 1 (by decide)).symm.injective.subsingleton

end OrthogonalLowGroups

namespace QuaternionicColumns

theorem piSixSpTwo_subsingleton : Subsingleton (π_ 6 QuaternionicFibration.SpTwo 1) := by
  let := OrthogonalLowGroups.piTwoRankSix_subsingleton
  exact (piSixSpTwoEquivSecondOrthogonal 6 (by decide)).injective.subsingleton

/-- Unconditional vanishing of the native sixth homotopy group of `Sp(2)`. -/
def piSixSpTwoMulEquiv : π_ 6 QuaternionicFibration.SpTwo 1 ≃* PUnit := by
  letI := piSixSpTwo_subsingleton
  letI := uniqueOfSubsingleton (1 : π_ 6 QuaternionicFibration.SpTwo 1)
  exact MulEquiv.ofUnique

end QuaternionicColumns
end Wikipedia.HomotopyGroupsOfSpheres
