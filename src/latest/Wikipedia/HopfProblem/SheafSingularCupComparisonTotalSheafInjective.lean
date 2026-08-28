import Wikipedia.HopfProblem.SheafSingularCupComparisonTotalSheafTerms
import Wikipedia.HopfProblem.SheafSingularCupComparisonRingScalars
import Wikipedia.HopfProblem.SheafCupProductGodementInjective

/-!
# Injectivity of the actual first two total terms

The original complex scalars make the actual Godement stalk groups
divisible. The proved Godement injectivity and the actual binary
biproduct construction therefore give genuine injective sheaves.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Wikipedia.HopfProblem.SheafSingularCupComparison.TotalSheaf

open SheafCupProduct

attribute [local instance] CategoryTheory.Abelian.hasFiniteBiproducts

variable (X : TopCat.{0})

/-- The original degree-zero total term is an injective abelian sheaf. -/
theorem I0_injective : Injective (I0 X) :=
  GodementRing.godement_injective_of_scalarEnd (RingCochains.sheaf X 0)
    (Scalars.scalarEnd (RingCochains.coefficients X 0))

/-- The original degree-one total term is an injective abelian sheaf. -/
theorem I1_injective : Injective (I1 X) := by
  let : Injective (GodementExact.I1 (RingCochains.sheaf X 0)) :=
    GodementRing.doubleGodement_injective_of_scalarEnd (RingCochains.sheaf X 0)
      (Scalars.scalarEnd (RingCochains.coefficients X 0))
  let : Injective (GodementExact.I0 (RingCochains.sheaf X 1)) :=
    GodementRing.godement_injective_of_scalarEnd (RingCochains.sheaf X 1)
      (Scalars.scalarEnd (RingCochains.coefficients X 1))
  exact inferInstanceAs (Injective
    (GodementExact.I1 (RingCochains.sheaf X 0) ⊞ GodementExact.I0 (RingCochains.sheaf X 1)))

end Wikipedia.HopfProblem.SheafSingularCupComparison.TotalSheaf
