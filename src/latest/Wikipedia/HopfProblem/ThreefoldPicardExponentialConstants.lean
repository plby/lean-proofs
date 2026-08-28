import Wikipedia.HopfProblem.ConstantSheafSingularComparisonConcreteSpaces
import Wikipedia.HopfProblem.ThreefoldCohomologySphere
import Wikipedia.HopfProblem.HolomorphicExponentialSheafIntegersULift

/-!
# The integral terms of the threefold's exponential cohomology sequence

The integer sheaf used by the original exponential sequence is literally
the native constant additive sheaf used by the sheaf--singular comparison.
The proved integral singular cohomology calculation therefore gives
vanishing in degrees one and two for the actual source sheaf of that
sequence. No identification of the threefold with a sphere is assumed.

The existing integer/`ULift` sheaf isomorphism also gives the corresponding
vanishing for the universe-lifted integer sheaf. All cohomology groups and
maps here are the original Ext-defined sheaf cohomology groups and maps.
-/

noncomputable section

open CategoryTheory TopologicalSpace

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.PicardExponential

open HolomorphicExponentialSheaf SingularCohomologyFree

/-- The exponential sequence and the comparison use the same integer sheaf. -/
theorem integerSheaf_eq_constant :
    integerSheaf (TopCat.of Space) =
      ConstantSheafFirstCohomology.Constant.sheaf (TopCat.of Space)
        (AddCommGrpCat.of ℤ) := rfl

/-- The genuine integral sheaf--singular comparison for the source of the
original exponential sequence, in degree one. -/
def integerSheafH1Equiv :
    CategoryTheory.Sheaf.H.{0} (integerSheaf (TopCat.of Space)) 1 ≃+
      SingularCohomology Space 1 :=
  ConstantSheafSingularComparison.threefoldIntegralSheafH1Equiv

/-- The same original comparison in degree two. -/
def integerSheafH2Equiv :
    CategoryTheory.Sheaf.H.{0} (integerSheaf (TopCat.of Space)) 2 ≃+
      SingularCohomology Space 2 :=
  ConstantSheafSingularComparison.threefoldIntegralSheafH2Equiv

/-- First cohomology of the actual integer sheaf on the constructed threefold vanishes. -/
theorem integerSheafH1_subsingleton :
    Subsingleton (CategoryTheory.Sheaf.H.{0} (integerSheaf (TopCat.of Space)) 1) := by
  let := CohomologySphere.cohomology_subsingleton 1 (by decide) (by decide)
  exact integerSheafH1Equiv.injective.subsingleton

/-- Second cohomology of the actual integer sheaf on the constructed threefold vanishes. -/
theorem integerSheafH2_subsingleton :
    Subsingleton (CategoryTheory.Sheaf.H.{0} (integerSheaf (TopCat.of Space)) 2) := by
  let := CohomologySphere.cohomology_subsingleton 2 (by decide) (by decide)
  exact integerSheafH2Equiv.injective.subsingleton

theorem integerSheafH1_eq_zero
    (a : CategoryTheory.Sheaf.H.{0} (integerSheaf (TopCat.of Space)) 1) : a = 0 :=
  integerSheafH1_subsingleton.elim a 0

theorem integerSheafH2_eq_zero
    (a : CategoryTheory.Sheaf.H.{0} (integerSheaf (TopCat.of Space)) 2) : a = 0 :=
  integerSheafH2_subsingleton.elim a 0

/-- The degree-one native cohomology object is a zero abelian group. -/
theorem integerSheafH1_isZero : Limits.IsZero
    ((CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology Space) 1).obj
      (integerSheaf (TopCat.of Space))) :=
  AddCommGrpCat.isZero_iff_subsingleton.mpr integerSheafH1_subsingleton

/-- The degree-two native cohomology object is a zero abelian group. -/
theorem integerSheafH2_isZero : Limits.IsZero
    ((CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology Space) 2).obj
      (integerSheaf (TopCat.of Space))) :=
  AddCommGrpCat.isZero_iff_subsingleton.mpr integerSheafH2_subsingleton

/-- The actual integer/`ULift` sheaf isomorphism induces the native cohomology equivalence. -/
def integerSheafULiftCohomologyEquiv (n : ℕ) :
    CategoryTheory.Sheaf.H.{0} (integerSheaf (TopCat.of Space)) n ≃+
      CategoryTheory.Sheaf.H.{0} (integerULiftSheaf (TopCat.of Space)) n :=
  ((CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology Space) n).mapIso
    (integerSheafULiftIso (TopCat.of Space))).addCommGroupIsoToAddEquiv

/-- The equivalence uses the original cohomology map of the actual coefficient isomorphism. -/
theorem integerSheafULiftCohomologyEquiv_apply (n : ℕ)
    (a : CategoryTheory.Sheaf.H.{0} (integerSheaf (TopCat.of Space)) n) :
    integerSheafULiftCohomologyEquiv n a =
      CategoryTheory.Sheaf.H.map.{0} (integerSheafULiftIso (TopCat.of Space)).hom n a := rfl

theorem integerULiftSheafH1_subsingleton :
    Subsingleton (CategoryTheory.Sheaf.H.{0} (integerULiftSheaf (TopCat.of Space)) 1) := by
  let := integerSheafH1_subsingleton
  exact (integerSheafULiftCohomologyEquiv 1).symm.injective.subsingleton

theorem integerULiftSheafH2_subsingleton :
    Subsingleton (CategoryTheory.Sheaf.H.{0} (integerULiftSheaf (TopCat.of Space)) 2) := by
  let := integerSheafH2_subsingleton
  exact (integerSheafULiftCohomologyEquiv 2).symm.injective.subsingleton

theorem integerULiftSheafH1_eq_zero
    (a : CategoryTheory.Sheaf.H.{0} (integerULiftSheaf (TopCat.of Space)) 1) : a = 0 :=
  integerULiftSheafH1_subsingleton.elim a 0

theorem integerULiftSheafH2_eq_zero
    (a : CategoryTheory.Sheaf.H.{0} (integerULiftSheaf (TopCat.of Space)) 2) : a = 0 :=
  integerULiftSheafH2_subsingleton.elim a 0

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.PicardExponential
