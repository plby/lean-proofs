import Wikipedia.HopfProblem.HolomorphicFunctionSheafSphereH1NegativeOneH0
import Wikipedia.HopfProblem.HolomorphicFunctionSheafSphereH1NegativeOneH1
import Mathlib.Algebra.Category.Grp.Zero

/-!
# The genuine cohomology objects are zero objects

These formulations use mathlib's actual cohomology functor into abelian
groups. They record the proved vanishing as categorical zero objects,
so subsequent exact-sequence arguments can use it directly.
-/

noncomputable section

open TopologicalSpace CategoryTheory

namespace Wikipedia.HopfProblem.HolomorphicFunctionSheaf.SphereH1

/-- Actual first cohomology of the holomorphic-function sheaf is a zero
object of the category of abelian groups. -/
theorem sphere_h1_isZero : Limits.IsZero
    ((CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology
      (TopCat.of RiemannSphere)) 1).obj sphereSheaf) := by
  apply AddCommGrpCat.isZero_iff_subsingleton.mpr
  exact sphere_h1_subsingleton

/-- Actual degree-zero cohomology of the vanishing ideal is a zero object. -/
theorem negativeOne_h0_isZero : Limits.IsZero
    ((CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology
      (TopCat.of RiemannSphere)) 0).obj negativeOneSheaf) := by
  apply AddCommGrpCat.isZero_iff_subsingleton.mpr
  exact negativeOne_h0_subsingleton

/-- Actual degree-one cohomology of the vanishing ideal is a zero object. -/
theorem negativeOne_h1_isZero : Limits.IsZero
    ((CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology
      (TopCat.of RiemannSphere)) 1).obj negativeOneSheaf) := by
  apply AddCommGrpCat.isZero_iff_subsingleton.mpr
  exact negativeOne_h1_subsingleton

end Wikipedia.HopfProblem.HolomorphicFunctionSheaf.SphereH1
