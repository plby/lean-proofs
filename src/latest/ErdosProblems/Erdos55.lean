/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/
import ErdosProblems.Erdos55.LowerBound
import ErdosProblems.Erdos55.UpperAssembly

/-!
# Erdős Problem 55

Conlon, Fox, and Pham proved the sharp growth order for Ramsey-complete sets.
Uniformly for every number of colors `r ≥ 2`, there is a positive Ramsey
`r`-complete set with counting function `O(r (log N)^2)`.  Conversely, an
absolute sufficiently small constant times `r (log N)^2` cannot be an
eventual upper bound for the counting function of any Ramsey `r`-complete
set.

The definitions use finite sets of elements, so every monochromatic sum has
distinct summands.  The eventual threshold may depend on the coloring, as in
the original problem.
-/

namespace Erdos55

/-- The complete sharp-order Conlon--Fox--Pham resolution of Erdős Problem
55, comprising both the uniform construction and the matching obstruction. -/
theorem erdos_55 : ConlonFoxPhamResolution :=
  ⟨conlonFoxPham_upperBound, conlonFoxPham_lowerBound⟩

end Erdos55

#print axioms Erdos55.erdos_55
