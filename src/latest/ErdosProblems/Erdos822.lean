/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos822.GILEnergy

/-!
# Erdős Problem 822

Problem 822 asks whether the values of `n + Nat.totient n` have positive
lower density. Gabdullin, Iudelevich, and Luca proved the affirmative answer
in Theorem 1.4 of "Numbers of the form k+f(k)" (2024).

The construction and all three collision ranges are proved in the helper
modules. `GILEnergy` supplies the unconditional linear energy bound;
`GILInputSize` supplies linearly many inputs. The perfect-power bridge and
finite Cauchy–Schwarz argument then give the exact lower-density conclusion.
The detailed mathematical proof and source audit are in `tex/822.tex`.

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

-/

namespace Erdos822

open Filter

/-- The values of `n + φ(n)` have positive lower density. -/
theorem totientRange_lowerDensity_pos : 0 < totientRange.lowerDensity := by
  obtain ⟨S, C, c, hS, hC, hc, hsize⟩ := exists_eventually_gilOuterInputs_card_linear
  obtain ⟨K, hK, henergy⟩ := exists_eventually_gilOuterInputs_energy_linear
    (by omega : 0 < S) hC.le
  let w := linearEnergyWitness_of_eventually_filteredOddPerfectPower_energy
    (B := fun N ↦ gilCofactors N S C) hc hK
    (fun N ↦ gilCofactors_subset_oddRaw N S C)
    (by simpa only [gilOuterInputs, Nat.cast_pow] using hsize)
    (by simpa only [gilOuterInputs] using henergy)
  exact w.lowerDensity_pos

/-- The affirmative resolution, with `True` the explicit value of `answer(True)`. -/
theorem erdos_822 :
    True ↔ 0 < (Set.range fun n : ℕ ↦ n + Nat.totient n).lowerDensity := by
  constructor
  · intro _
    simpa only [totientRange_eq] using totientRange_lowerDensity_pos
  · intro _
    trivial

#print axioms erdos_822

end Erdos822
