import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologyBlowupH1Cech
import Wikipedia.HopfProblem.HolomorphicFunctionSheafSphereH1

/-!
# Genuine first holomorphic sheaf cohomology of the incidence blowup

The actual two-chart analytic argument solves every genuine sheaf
one-cocycle. The proved comparison with global lifting and Ext now gives
vanishing of mathlib's actual `Sheaf.H` in degree one. Neither rationality,
Stein vanishing, nor an assumed Cousin solver is an input.
-/

noncomputable section

namespace Wikipedia.HopfProblem.HolomorphicSheafCohomology.BlowupH1

open HolomorphicFunctionSheaf.SphereH1

theorem blowup_globalLifting : GlobalLifting blowupSheaf :=
  globalLifting_of_cechOneVanishing blowup_cechOneVanishing

instance blowupH1AddCommGroup : AddCommGroup (CategoryTheory.Sheaf.H.{0} blowupSheaf 1) :=
  CategoryTheory.Abelian.Ext.instAddCommGroup

/-- Genuine `H¹(O)` of the actual affine incidence blowup is zero. -/
theorem blowup_h1_subsingleton :
    Subsingleton (CategoryTheory.Sheaf.H.{0} blowupSheaf 1) :=
  subsingleton_h1_of_cechOneVanishing blowupSheaf blowup_cechOneVanishing

theorem blowup_h1_eq_zero (x : CategoryTheory.Sheaf.H.{0} blowupSheaf 1) : x = 0 :=
  h1_eq_zero_of_globalLifting blowupSheaf blowup_globalLifting x

end Wikipedia.HopfProblem.HolomorphicSheafCohomology.BlowupH1
