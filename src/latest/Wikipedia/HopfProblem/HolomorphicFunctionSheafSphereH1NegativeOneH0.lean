import Wikipedia.HopfProblem.HolomorphicFunctionSheafSphereH1NegativeOneH0Constancy
import Wikipedia.HopfProblem.HolomorphicFunctionSheafSphereH1NegativeOneSheaf
import Wikipedia.HopfProblem.HolomorphicFunctionSheafCohomologyZeroBasic

/-!
# Genuine degree-zero cohomology of the ideal vanishing at infinity

Every global section of the actual ideal sheaf is an actual holomorphic
function on the compact analytic sphere.  It is constant by the maximum
principle and is zero at infinity by its ideal membership.  Thus all its
global sections are zero.  Mathlib's canonical degree-zero comparison
then gives vanishing of the genuine sheaf cohomology group, defined by
`Ext`, rather than a redefinition of cohomology as a space of sections.
-/

noncomputable section

open TopologicalSpace Opposite CategoryTheory
open scoped ContDiff Manifold OnePoint

namespace Wikipedia.HopfProblem.HolomorphicFunctionSheaf.SphereH1

/-- A literal global holomorphic section vanishing at infinity is zero. -/
theorem negativeOne_globalSection_eq_zero (f : NegativeOneSection ⊤) : f = 0 := by
  apply Subtype.ext
  apply ContMDiffMap.ext
  intro x
  change f.val x = 0
  exact (sphere_globalSection_apply_eq f.val x ⟨(∞ : RiemannSphere), trivial⟩).trans
    (f.property trivial)

/-- The actual global section group of the vanishing ideal is the zero group. -/
theorem negativeOne_globalSections_subsingleton : Subsingleton (NegativeOneSection ⊤) := by
  constructor
  intro f g
  exact (negativeOne_globalSection_eq_zero f).trans
    (negativeOne_globalSection_eq_zero g).symm

/-- These are the existing additive operations on genuine degree-zero Ext. -/
instance negativeOneH0AddCommGroup :
    AddCommGroup (CategoryTheory.Sheaf.H.{0} negativeOneSheaf 0) :=
  CategoryTheory.Abelian.Ext.instAddCommGroup

/-- The canonical degree-zero comparison with the literal section ideal. -/
def negativeOneH0GlobalAddEquiv :
    CategoryTheory.Sheaf.H.{0} negativeOneSheaf 0 ≃+ NegativeOneSection ⊤ :=
  CategoryTheory.Sheaf.H.equiv₀ negativeOneSheaf
    (show Limits.IsTerminal (⊤ : Opens (TopCat.of RiemannSphere)) from
      Limits.isTerminalTop)

/-- Genuine `H⁰` of the actual holomorphic ideal sheaf vanishing at infinity
is the zero additive group, without any cohomological vanishing input. -/
theorem negativeOne_h0_subsingleton :
    Subsingleton (CategoryTheory.Sheaf.H.{0} negativeOneSheaf 0) := by
  constructor
  intro x y
  apply negativeOneH0GlobalAddEquiv.injective
  exact (negativeOne_globalSection_eq_zero _).trans
    (negativeOne_globalSection_eq_zero _).symm

/-- Every genuine degree-zero class of the vanishing ideal is zero. -/
theorem negativeOne_h0_eq_zero
    (x : CategoryTheory.Sheaf.H.{0} negativeOneSheaf 0) : x = 0 :=
  negativeOne_h0_subsingleton.elim x 0

end Wikipedia.HopfProblem.HolomorphicFunctionSheaf.SphereH1
