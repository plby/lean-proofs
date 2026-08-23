This is a formalization of both affirmative results in
[Erdős Problem 1105](https://www.erdosproblems.com/1105).

The corrected `antiRamseyNum` counts only colors actually used on edges of
the complete graph. A rainbow copy is a vertex-injective graph homomorphism,
not an induced embedding. Diagonal pairs are not edges and do not contribute
colors. The Comparator challenge uses the same corrected definitions and
requests the affirmative statements, not their negations.

The two complete results are:

* `Erdos1105.erdos_1105_parts_i`: the cycle asymptotic for every `k ≥ 3`;
* `Erdos1105.erdos_1105_parts_ii`: the exact path formula for every
  `5 ≤ k ≤ n`, including both parities and the special six-vertex case.

Both theorems use only `propext`, `Classical.choice`, and `Quot.sound`.
There are no `sorry` proofs, additional axioms, or unproved structural
hypotheses in the solution. The challenge's `sorry` declarations are the
usual Comparator specification stubs, not solution proofs.

## Proof organization

The supporting modules are in
[`Erdos1105/`](../src/latest/ErdosProblems/Erdos1105/).

* `Basic.lean` defines the corrected anti-Ramsey number and rainbow copies.
  `Blocks.lean` and `PathConstructions.lean` provide the lower bounds.
* `CycleUpper.lean` proves the full cycle asymptotic using private-color
  deletion, representative components, and a monochromatic quotient.
* `PathBoundReduction.lean` reduces arbitrary path-free colorings to the
  connected-representative case, using bridge-color closure, representative
  component counting, and color-preserving deletion.
* `ConnectedOddUpper.lean` and `ConnectedEvenUpper.lean` prove the connected
  bounds. Their structural inputs are proved using cycle saturation, core
  deletion, longest-path rotations, and clique and split-graph arguments.
  `SharpCliqueRainbow.lean` excludes the sharp clique-core equality case by
  peeling to the boundary order and finding the forbidden rainbow path.
* `ConnectedPathSix.lean` handles `P₆`. In particular, `ThreePetalCopy.lean`
  extracts three triangles sharing a root from the high-edge rooted-path
  case, and `ThreePetalRainbow.lean` produces a rainbow six-vertex path.
  Its finite path choices are checked by kernel reduction, without
  `native_decide`.
* `PathUpper.lean` combines all cases and proves the exact path formula.

The path argument follows the representative-graph approach in
[Yuan's Theorem 1](https://arxiv.org/html/2102.00807). The development also
proves the needed connected-path extremal bounds and stability arguments;
these are not imported as axioms. `RootedPathEdges.lean` reuses the proved
Erdős–Gallai cycle bound from the Erdős 767 development.

## Verification

From `src/latest`, `lake build ErdosProblems.Erdos1105` succeeds.
Both final declarations report exactly the three standard axioms above.
The full Comparator run against the checked-in two-target configuration
passed statement comparison, permitted-axiom checking, and both the Lean
and Nanoda kernels: `Your solution is okay!`.

The workstation is macOS, so the development check uses Comparator's upstream
`scripts/fake-landrun.sh`, not the Linux security sandbox. This distinction
does not replace or disable statement comparison or either kernel check.
Nanoda was built from revision `6ae1f0cd962f081f6c423454c5da729d841236a7`.

The previous file proved that an incorrect, diagonal-inclusive upstream
formalization was false. That audit is preserved separately in
[`UpstreamAudit.lean`](../src/latest/ErdosProblems/Erdos1105/UpstreamAudit.lean),
under `Erdos1105.UpstreamAudit`; it is not imported by the solution and is not
a disproof of the classical problem.

Available for:

* [Mathlib/Lean v4.33.0](../src/latest/ErdosProblems/Erdos1105.lean).
