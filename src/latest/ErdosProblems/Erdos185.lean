/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- Original license: Apache 2.0. Note: This file has been modified. -/
/-
This is a Lean formalization of a solution to Erdős Problem 185.
https://www.erdosproblems.com/forum/thread/185

Informal authors:
- Pandelis Dodos
- Vassilis Kanellopoulos
- Konstantinos Tyros

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos185.md
-/
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos185.Corollary
import ErdosProblems.Erdos185.DHJ.Increment

/-!
# Erdős Problem 185

The maximum size of a subset of the ternary cube containing no three
distinct Euclidean-collinear points is little-oh of the size of the cube.

The substantive combinatorial input is the specialized density
Hales--Jewett theorem proved in the `Erdos185.DHJ` modules by the finite
density-increment argument of Dodos--Kanellopoulos--Tyros.  A combinatorial
line is a Euclidean line, so the density theorem applies to every Moser set.
-/

namespace Erdos185

/-- Density Hales--Jewett for the ternary alphabet, in the exact cardinality
form needed for Erdős Problem 185. -/
theorem density_hales_jewett_three : DensityHalesJewettThree :=
  DHJ.densityHalesJewettThree_of_increment DHJ.ternaryIncrementPrinciple

/-- **Erdős Problem 185.** If `f3 n` is the largest cardinality of a subset
of `{0,1,2}^n` containing no three distinct Euclidean-collinear points, then
`f3 n = o(3^n)`. -/
theorem erdos_185 :
    Asymptotics.IsLittleO Filter.atTop
      (fun n : ℕ ↦ (f3 n : ℝ))
      (fun n : ℕ ↦ (3 : ℝ) ^ n) :=
  f3_isLittleO_three_pow_of_densityHalesJewettThree density_hales_jewett_three

end Erdos185

#print axioms Erdos185.erdos_185
