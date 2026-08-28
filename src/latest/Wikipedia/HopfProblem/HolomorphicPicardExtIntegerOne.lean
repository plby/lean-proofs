import Wikipedia.HopfProblem.HolomorphicFunctionSheafSphereH1ExtGlobal
import Wikipedia.HopfProblem.HolomorphicExponentialSheafIntegersULift
import Wikipedia.HopfProblem.HolomorphicFunctionSheafSphereH1Cech

/-!
# The constant integer one and the actual degree-zero Ext identity

The section called one is the image of the literal lifted integer `1`
under the genuine constant-sheaf unit.  Naturality gives its restriction
formula, and the degree-zero cohomology comparison identifies the identity
of the constant integer sheaf with precisely this section.
-/

noncomputable section

open TopologicalSpace Opposite CategoryTheory CategoryTheory.Abelian

namespace Wikipedia.HopfProblem.HolomorphicPicard.ExtExtensions

open HolomorphicFunctionSheaf.SphereH1

/-- The actual constant representative of the lifted integer one. -/
def constantIntegerOne (X : TopCat.{0}) (U : Opens X) :
    Section (constantIntegerSheaf X) U :=
  (HolomorphicExponentialSheaf.integerULiftUnit X).app (op U) (ULift.up 1)

@[simp]
theorem constantIntegerOne_restrict (X : TopCat.{0}) {U V : Opens X} (h : V ≤ U) :
    res (constantIntegerSheaf X) h (constantIntegerOne X U) =
      constantIntegerOne X V := by
  exact (ConcreteCategory.congr_hom
    ((HolomorphicExponentialSheaf.integerULiftUnit X).naturality (homOfLE h).op)
    (ULift.up (1 : ℤ))).symm

end Wikipedia.HopfProblem.HolomorphicPicard.ExtExtensions
