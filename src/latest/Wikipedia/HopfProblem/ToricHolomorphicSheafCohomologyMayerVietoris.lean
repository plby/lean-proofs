import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologyMayerVietorisRestriction

/-!
# Actual Mayer–Vietoris gluing for sheaf cohomology

Mathlib's actual Ext-defined Mayer–Vietoris exact sequence, the proved
open-restriction comparison, and the proved top-open/integer-sheaf
comparison give genuine vanishing criteria for two actual open sets.

In degree one, the inputs are vanishing of the two actual restricted
H¹ groups and surjectivity of the literal difference of section
restrictions. In degree `n+2`, only component Hⁿ⁺² and intersection
Hⁿ⁺¹ vanishing are required. Positive-degree acyclicity therefore glues
when both opens and their intersection are acyclic and the actual
section difference is onto. These are generic gluing theorems, not
assertions of any unproved analytic acyclicity for a particular toric
space or cusp.
-/
