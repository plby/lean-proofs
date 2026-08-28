import Wikipedia.HopfProblem.HolomorphicFunctionSheafSphereH1
import Wikipedia.HopfProblem.HolomorphicFunctionSheafSphereH1NegativeOneSolvable

/-!
# Genuine first cohomology of the ideal sheaf of infinity

The actual ideal sheaf has solvable one-cocycles on arbitrary sphere
open covers, by the constructed normalized Cousin primitives. The
proved local-lifting and Ext comparison therefore gives genuine
degree-one cohomology vanishing. The companion local-frame results
identify this actual sheaf as the holomorphic line sheaf `O(-1)`.
-/

noncomputable section

open CategoryTheory

namespace Wikipedia.HopfProblem.HolomorphicFunctionSheaf.SphereH1

/-- The actual ideal sheaf lifts global sections across every short
exact sequence in which it is the first term. -/
theorem negativeOne_globalLifting : GlobalLifting negativeOneSheaf :=
  globalLifting_of_cechOneVanishing negativeOne_cechOneVanishing

/-- The degree-one group retains the existing actual Ext operations. -/
instance negativeOneH1AddCommGroup :
    AddCommGroup (CategoryTheory.Sheaf.H.{0} negativeOneSheaf 1) :=
  CategoryTheory.Abelian.Ext.instAddCommGroup

/-- Genuine `H¹(P¹, O(-∞))` is the zero additive group. -/
theorem negativeOne_h1_subsingleton :
    Subsingleton (CategoryTheory.Sheaf.H.{0} negativeOneSheaf 1) :=
  subsingleton_h1_of_cechOneVanishing negativeOneSheaf negativeOne_cechOneVanishing

/-- Every genuine degree-one cohomology class of the actual ideal
sheaf is zero, without any additional hypothesis. -/
theorem negativeOne_h1_eq_zero
    (x : CategoryTheory.Sheaf.H.{0} negativeOneSheaf 1) : x = 0 :=
  h1_eq_zero_of_globalLifting negativeOneSheaf negativeOne_globalLifting x

end Wikipedia.HopfProblem.HolomorphicFunctionSheaf.SphereH1
