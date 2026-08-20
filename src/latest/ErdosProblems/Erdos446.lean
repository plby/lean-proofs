/-
Copyright (c) 2026 The Formal Conjectures Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors
-/

import ErdosProblems.Erdos446.FinalAssemblySkeleton
import ErdosProblems.Erdos446.UpperFinalAssembly
import ErdosProblems.Erdos446.UpperSieveClusterReduction
import ErdosProblems.Erdos446.UpperTrimmedFinalEndpoint

/-!
# Erdős Problem 446

Let `delta n` be the density of integers divisible by an integer strictly
between `n` and `2 * n`, and let `deltaR r n` be the density of integers with
exactly `r` such divisors.  Ford proved the sharp order

`delta n ≍ 1 / ((log n) ^ alpha446 * (log (log n)) ^ (3 / 2))`

and, for every fixed positive `r`, the lower comparison
`delta n = O(deltaR r n)`.  In particular `deltaR 1` is not little-oh of
`delta`; this disproves the second assertion proposed in the problem.
-/

namespace Erdos446

open Filter Asymptotics
open scoped Topology

/-- Ford's unconditional sharp upper estimate for the half-open divisor
interval.  Together with the already formalized lower estimate this gives the
exact order of `delta`. -/
theorem epsilon_isBigO_growth446 :
    (fun y : ℕ ↦ epsilon y (2 * y)) =O[atTop] growth446 :=
  epsilon_isBigO_growth446_of_exists_sieveCluster
    exists_pos_dyadicUpperSieveClusterReduction
    exists_smoothSquarefreeClusterUpperBlockCount

/-- The complete resolution of Erdős Problem 446. -/
theorem erdos_446 : Resolution446 :=
  resolution446_of_upper epsilon_isBigO_growth446

/-- The sharp growth-rate answer to Erdős Problem 446. -/
theorem erdos_446_growth : GrowthResolution446 :=
  erdos_446.1

/-- Ford's lower comparison for every fixed positive multiplicity. -/
theorem erdos_446_fixed_multiplicity : FixedMultiplicityResolution446 :=
  erdos_446.2.1

/-- The proposed assertion `deltaR 1 = o(delta)` is false. -/
theorem erdos_446_not_little_o :
    ¬ (deltaR 1 =o[atTop] delta) :=
  erdos_446.2.2

end Erdos446

#print axioms Erdos446.erdos_446
