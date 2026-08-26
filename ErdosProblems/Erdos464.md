# Erdős Problem 464

[EPC](https://www.erdosproblems.com/464) ·
[announcement](https://www.erdosproblems.com/forum/thread/464#post-7120) ·
[source request](https://aristotle.harmonic.fun/dashboard/requests/f9894d2d-4bb1-42da-9301-e508aa881b17)

## Scope and authorship

For a strictly increasing sequence of positive natural numbers with consecutive
ratios at least `1 + ε₀`, where `ε₀ > 0`, the theorem gives an irrational `θ`
such that zero is not in the closure of the nearest-integer distances of `θ * a k`.
This implies non-density modulo one; it avoids the vacuous literal reading
of nearest-integer distances being non-dense in `[0, 1]`, since all such distances
are at most `1/2`. The theorem does not claim a quantitative bound in terms of
`ε₀`, nor the full Hausdorff-dimension result.

The informal proof is Bernard de Mathan's nested-interval construction from
*Numbers contravening a condition in density modulo 1*,
[Acta Math. Acad. Sci. Hungar. 36, 237–241](https://doi.org/10.1007/BF01898138).
JoshuaB's 21 June 2026 comment identifies the formalization as the argument for
Theorem 1, Part 1, produced by **Aristotle** from de Mathan's paper.
The metadata credits **Aristotle and JoshuaB**, whose public handle is retained
because no fuller human name was established.

## Provenance and port

The user supplied the five source modules listed below and explicitly confirmed
`leanprover/lean4:v4.28.0` as their original toolchain. The supplied files do not
include a Mathlib pin or a license notice; neither is inferred. The inaccessible
Aristotle dashboard was not used to retrieve any files.

| Supplied source | SHA-256 before modification |
| --- | --- |
| Main.lean | `631b2b0b2d9375385a6b0b383b70bc4114ef5bb9543c26947c244e2de391e58d` |
| NDist.lean | `30fb638f1724ced88ace49662dd979874024491deb73c2f505963c96c1936555` |
| Uncountable.lean | `3bdb35a435c2d9447007e600af87141f2649828b523db7b4d04e71eb28ed3928` |
| Refinement.lean | `1fcfb818f6d33c650270874561a3d6497a60c874c569ae9695f41ffc51972561` |
| Construction.lean | `83338e2d861d905ecbeb5a1955d9de6f95cbef1d5cefdaeac0cec617daee3bdf` |

The port moves the modules into the `Erdos464` namespace, rewrites project imports,
updates conversion, algebra, and Cantor-scheme proofs for Lean/Mathlib 4.33.0,
removes unused namespace openings, and names the final result
`Erdos464.erdos_464`. Its conclusion is the source's stronger avoidance assertion.
The independent Comparator challenge imports only Mathlib and restates that result
without importing the construction or any solution definitions.

## Verification

- `lake build ErdosProblems.Erdos464 Erdos464` passes on Lean/Mathlib 4.33.0.
  The solution emits no warnings; the independent challenge has the expected
  placeholder warning.
- `Erdos464.erdos_464` depends only on `propext`, `Classical.choice`, and `Quot.sound`.
- Independent `lean4export` exports pass `Comparator.compareAt` and
  `Comparator.checkAxioms`; a fresh Lean environment accepts kernel replay of the
  exported solution.
- The full Linux sandbox/Nanoda runner was not run because this macOS environment
  lacks `landrun`. Nanoda remains enabled in the Comparator configuration.
- Metadata, registrations, challenge/configuration consistency, source hashes,
  and the absence of proof placeholders, `native_decide`, custom axioms, and
  unsafe declarations were checked.
