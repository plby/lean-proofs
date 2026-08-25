/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos822.SlowCutoffLog

/-!
# Erdős Problem 822: shared development

Problem 822 asks whether the values of `n + Nat.totient n` have positive
lower density. This module gathers the existing development under its own
import path; clients can import the smaller modules they need directly.

The reusable interfaces include:

* `ErdosProblems.Erdos822.PrimeIntervals`: eventual lower bounds for the
  number of primes in `(x / 2, x]`.
* `ErdosProblems.Erdos822.PrimeReciprocal`: lower bounds for reciprocal
  prime sums over intervals, including intervals between fixed powers.
* `ErdosProblems.Erdos822.FiniteEnergy`: fiber counts, collision pairs,
  and the finite Cauchy--Schwarz bound for the size of an image.
* `ErdosProblems.Erdos822.Assembly`: conversion of finite counting and
  collision-energy estimates into positive lower density.

Erdos48 and Erdos240 use the prime-distribution interfaces; Erdos356 and
Erdos981 use finite collision energy. Erdos980 uses the more specialized
sieve estimates. None of these uses requires the conclusion of Problem 822.

## Proof status

`Erdos822.LinearEnergyWitness.lowerDensity_pos` proves the desired density
conclusion from a family of input sets of linear size and linear collision
energy. The existing development does not construct such a witness without
an additional energy estimate. In particular,
`exists_oddRaw_collisionEnergy_le_of_logMassMainSum` still assumes a bound
for the arithmetic main-weight sum. There is no unconditional `erdos_822`
theorem in this module.
-/
