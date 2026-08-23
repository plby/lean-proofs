/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
This is a Lean formalization of a solution to Erdős Problem 957.
https://www.erdosproblems.com/forum/thread/957

Informal authors:
- Adrian Dumitrescu

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos957.md
-/
import ErdosProblems.Erdos957.Assembly
import ErdosProblems.Erdos957.Case2SplitProduced

/-!
# Erdős Problem 957

For a finite planar point set, the product of the multiplicities of its
smallest and largest distances is at most
`(9 / 8) * n ^ 2 + O(n)`.  The geometric input below is constructed from the
actual cyclic hull, its produced dependent transfer rows, and the completed
weight-aware collision analysis.  No geometric proposition is assumed by
the public theorem.
-/

namespace Erdos957

noncomputable section

open Erdos957GeometryCore

/-- The unconditional geometric transfer certificate.  The final
degree-five Case-2 residual is instantiated with the produced coherent row
family; all Case-4 and weighted collision fields are discharged inside the
imported completion modules. -/
theorem geometryProducesTransfer : GeometryProducesTransfer :=
  Erdos957Case2SplitProduced.geometryProducesTransfer

/-- Uniform linear-error form of Erdős Problem 957. -/
theorem erdos957 : HasLinearErrorBound :=
  erdos957_linearErrorBound_of_geometry geometryProducesTransfer

/-- Literal uniform epsilon formulation of the `9 / 8 + o(1)` bound. -/
theorem erdos957_asymptotic : HasNineEighthsAsymptoticBound :=
  erdos957_asymptotic_of_geometry geometryProducesTransfer

/-- Filter-at-infinity formulation of the `9 / 8 + o(1)` bound. -/
theorem erdos957_filter : HasNineEighthsFilterBound :=
  erdos957_filter_of_geometry geometryProducesTransfer

end


end Erdos957

#print axioms Erdos957.geometryProducesTransfer
#print axioms Erdos957.erdos957
#print axioms Erdos957.erdos957_asymptotic
#print axioms Erdos957.erdos957_filter
