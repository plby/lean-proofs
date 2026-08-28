import Wikipedia.HopfProblem.HolomorphicFunctionSheafSphereH1NegativeOneFrames
import Wikipedia.HopfProblem.HolomorphicFunctionSheafSphereH1NegativeOneCategorical

/-!
# The actual negative-one holomorphic line sheaf and its cohomology

`negativeOneSheaf` is the genuine sheaf of holomorphic functions on the
actual analytic sphere that vanish at infinity. Its local identifications
with the holomorphic-function sheaf are proved by multiplication by the
frames `1` in the finite chart and `u` in the reciprocal chart. They are
linear over the actual section rings on every open subset of either
chart and commute with literal restrictions. Their transition in the
finite coordinate is `z⁻¹`, identifying this actual ideal sheaf as `O(-1)`.

The compact maximum principle and the actual degree-zero comparison
prove `H⁰(P¹, O(-1)) = 0`. The constructed negative-one Cousin primitives,
actual sheaf gluing and Ext exactness prove `H¹(P¹, O(-1)) = 0`. Both are
genuine mathlib sheaf-cohomology groups and categorical zero objects.

The scalar `H¹(P¹, O) = 0` theorem is also imported. No statement of
higher cohomology vanishing on the global threefold is made here.
-/

noncomputable section

open TopologicalSpace CategoryTheory

namespace Wikipedia.HopfProblem.HolomorphicFunctionSheaf.SphereH1

/-- The genuine degree-zero and degree-one cohomology objects of the
actual negative-one line sheaf both vanish. -/
theorem negativeOne_h0_h1_isZero :
    Limits.IsZero ((CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology
      (TopCat.of RiemannSphere)) 0).obj negativeOneSheaf) ∧
    Limits.IsZero ((CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology
      (TopCat.of RiemannSphere)) 1).obj negativeOneSheaf) :=
  ⟨negativeOne_h0_isZero, negativeOne_h1_isZero⟩

end Wikipedia.HopfProblem.HolomorphicFunctionSheaf.SphereH1
