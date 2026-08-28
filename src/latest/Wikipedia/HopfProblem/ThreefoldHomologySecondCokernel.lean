import Wikipedia.HopfProblem.ThreefoldHomologySecondDegreeRanks

/-!
# Actual second homology as the second attachment cokernel

The proved injectivity of the original degree-one attachment makes the
genuine next connecting map zero.  Consequently the sum of the actual
piece inclusions surjects onto second homology, and the actual star
sequence identifies precisely its relations.

This reduction preserves the original integer attachment map.  It does
not assert that its still unevaluated second cokernel vanishes.
-/

noncomputable section

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Homology.SecondDegree

open SingularMayerVietoris

/-- The actual connecting map out of second homology vanishes. -/
theorem connecting_one_eq_zero : starConnectingHomomorphism 1 = 0 := by
  apply LinearMap.ext
  intro a
  change starConnectingHomomorphism 1 a = 0
  apply starLeft_one_bijective.injective
  simpa only [map_zero] using (star_exact_at_intersection 1).apply_apply_eq_zero a

/-- Every actual second homology class is a sum of original piece classes. -/
theorem starRight_two_surjective : Function.Surjective (starRightHomologyMap 2) := by
  intro a
  apply (star_exact_at_ambient 1 a).mp
  rw [connecting_one_eq_zero, LinearMap.zero_apply]

/-- Precisely the genuine signed overlap classes give the inclusion relations. -/
theorem starLeft_two_range_eq_ker :
    LinearMap.range (starLeftHomologyMap 2) = LinearMap.ker (starRightHomologyMap 2) :=
  (LinearMap.exact_iff.mp (star_exact_at_pair 2)).symm

/-- The quotient of the original pieces by the actual overlap map is second homology. -/
def attachmentCokernelEquiv :
    (StarPairHomology 2 ⧸ LinearMap.range (starLeftHomologyMap 2)) ≃ₗ[ℤ]
      SingularHomology Space 2 :=
  ((Submodule.quotEquivOfEq _ _ starLeft_two_range_eq_ker).toAddEquiv.trans
    ((starRightHomologyMap 2).quotKerEquivOfSurjective
      starRight_two_surjective).toAddEquiv).toIntLinearEquiv

/-- The quotient equivalence is literally the original sum of piece inclusions. -/
@[simp] theorem attachmentCokernelEquiv_mk (a : StarPairHomology 2) :
    attachmentCokernelEquiv (Submodule.Quotient.mk a) = starRightHomologyMap 2 a := rfl

/-- Second integral homology with its genuine star-cover presentation. -/
def homologyTwoCokernelEquiv :
    SingularHomology Space 2 ≃ₗ[ℤ]
      (StarPairHomology 2 ⧸ LinearMap.range (starLeftHomologyMap 2)) :=
  attachmentCokernelEquiv.symm

@[simp] theorem homologyTwoCokernelEquiv_inclusion (a : StarPairHomology 2) :
    homologyTwoCokernelEquiv (starRightHomologyMap 2 a) = Submodule.Quotient.mk a :=
  attachmentCokernelEquiv.symm_apply_apply (Submodule.Quotient.mk a)

/-- Vanishing of an actual sum of piece classes is exactly an actual attachment relation. -/
theorem starRight_two_eq_zero_iff (a : StarPairHomology 2) :
    starRightHomologyMap 2 a = 0 ↔
      ∃ b : StarOverlapHomology 2, starLeftHomologyMap 2 b = a :=
  star_exact_at_pair 2 a

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Homology.SecondDegree
