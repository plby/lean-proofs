/-
Copyright (c) 2026 The Formal Conjectures Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors
-/

import ErdosProblems.Erdos446.FinalInterfaceDraft
import ErdosProblems.Erdos446.FixedMultiplicityDensityLower

/-!
# Erdős Problem 446: final assembly boundary

This module keeps the final public theorem free of hypotheses.  The theorem
`resolution446_of_upper_and_modelDensity` below is only the assembly bridge;
its `_of_` name records the two analytic inputs still being proved.

The intended unconditional upper input is:

* `epsilon_isBigO_growth446`:
  `(fun n ↦ epsilon n (2 * n)) =O[atTop] growth446`;
The prescribed-multiplicity input
`exists_fixedMultiplicityModelDensityLower` is now proved unconditionally in
`FixedMultiplicityDensityLower`.

Once those declarations land, the main file should contain the unconditional
proof

```
theorem erdos_446 : Resolution446 :=
  resolution446_of_upper_and_modelDensity
    epsilon_isBigO_growth446
    exists_fixedMultiplicityModelDensityLower
```

and expose its three components under descriptive theorem names.  In
particular, the final theorem must not quantify over either input.
-/

namespace Erdos446

open Filter Asymptotics
open scoped Topology

/-- Final assembly from the sharp union upper bound and the genuine
fixed-multiplicity arithmetic model.  This theorem contains no hidden
number-theoretic assumption: both inputs are explicit propositions whose
unconditional proofs are supplied by the analytic modules. -/
theorem resolution446_of_upper_and_modelDensity
    (hupper : (fun n : ℕ ↦ epsilon n (2 * n)) =O[atTop] growth446)
    (hfixedModel : ∀ r : ℕ, 1 ≤ r →
      ∃ M : ℕ, ∃ c : ℝ, ∃ Y : ℕ,
        0 < c ∧ FixedMultiplicityModelDensityLower r M c Y) :
    Resolution446 := by
  apply resolution446_of_upper_and_fixedMultiplicity_lower hupper
  intro r hr
  obtain ⟨M, c, Y, hc, hmodel⟩ := hfixedModel r hr
  exact exists_eventually_epsilon_mul_le_epsilonR_of_modelDensity
    hr hc hupper hmodel

/-- Final resolution once the sharp union upper bound is supplied.  The
fixed-multiplicity construction is unconditional and is discharged here. -/
theorem resolution446_of_upper
    (hupper : (fun n : ℕ ↦ epsilon n (2 * n)) =O[atTop] growth446) :
    Resolution446 :=
  resolution446_of_upper_and_modelDensity hupper
    exists_fixedMultiplicityModelDensityLower

end Erdos446
