import Wikipedia.HopfProblem.PeriodTorusHolomorphicCupTotalTerms
import Wikipedia.HopfProblem.PeriodTorusHolomorphicCohomologyDolbeaultAcyclic
import Wikipedia.HopfProblem.SheafCupProductGodementInjective

/-!
# Genuine injectivity of the first two total terms

The original complex scalar action makes the actual Godement stalk
groups divisible. Its proved injectivity and the actual pair-biproduct
isomorphism give injectivity of the two original total sheaves.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Wikipedia.HopfProblem.PeriodTorusHolomorphicCup.Total.CompatibleOperators

open SheafCupProduct

attribute [local instance] CategoryTheory.Abelian.hasFiniteBiproducts

variable {p : PeriodDomain} (D : CompatibleOperators p)

theorem I0_injective : Injective D.I0 :=
  GodementRing.godement_injective_of_scalarEnd (Derivation.smoothRingSheaf p)
    (PeriodTorusHolomorphicCohomology.Dolbeault.smoothScalarEnd p)

theorem I1_injective : Injective D.I1 := by
  let : Injective (GodementExact.I0 (Derivation.smoothRingSheaf p)) := D.I0_injective
  let : Injective (GodementExact.I1 (Derivation.smoothRingSheaf p)) :=
    GodementRing.doubleGodement_injective_of_scalarEnd (Derivation.smoothRingSheaf p)
      (PeriodTorusHolomorphicCohomology.Dolbeault.smoothScalarEnd p)
  let : Injective (Pairs.sheaf (GodementExact.I0 (Derivation.smoothRingSheaf p))) :=
    Injective.of_iso (Pairs.biprodIso (GodementExact.I0 (Derivation.smoothRingSheaf p))).symm
      inferInstance
  exact inferInstanceAs (Injective
    (GodementExact.I1 (Derivation.smoothRingSheaf p) ⊞
      Pairs.sheaf (GodementExact.I0 (Derivation.smoothRingSheaf p))))

end Wikipedia.HopfProblem.PeriodTorusHolomorphicCup.Total.CompatibleOperators
