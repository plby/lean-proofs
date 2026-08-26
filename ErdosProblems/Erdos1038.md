This is an imported formal proof claim for [Erdős Problem 1038](https://www.erdosproblems.com/1038), from [Shouqiao Wang's full-solution claim](https://www.erdosproblems.com/forum/thread/1038/proof-claims#proof-claim-8).

The formalization determines the infimum and supremum of the measure of
`{x : ℝ | |f(x)| < 1}` for nonconstant monic real polynomials whose roots all
lie in `[-1, 1]`. The infimum is an explicitly defined constant
`L ≈ 1.834430475762661…`; the supremum is `2√2`. The imported stronger theorem
also includes certified numerical bounds, nonattainment of the infimum,
and the equality cases for the supremum.

## Attribution and source

The informal proof is credited to Shouqiao Wang and GPT-5.6 Sol, building on
Terence Tao's earlier upper bound and reductions. The formal proof is
attributed to **GPT**, as requested by the repository contributor; the
source does not specify the exact model version used for formalization.
The source is released under the MIT license, copyright 2026 Shouqiao Wang.

The import is pinned to the [formalization commit
`dc20752268ede5a3548e3d63ae74e45c3cfcf78c`](https://github.com/ShouqiaoW/erdos/tree/dc20752268ede5a3548e3d63ae74e45c3cfcf78c/1038/lean)
of July 19, 2026. Its standalone package declares version `0.1.0` and uses
Lean `4.27.0` and mathlib `v4.27.0` (commit
`a3a10db0e9d66acbebf76c5e6a135066525ac900`). The `version` field in
`data/sources.yaml` records that original Lean version.

## Repository version

* [Mathlib/Lean v4.33.0](../src/latest/ErdosProblems/Erdos1038.lean).
* [Comparator challenge](../src/latest/ComparatorChallenges/ErdosProblems/Erdos1038.lean)
  and [configuration](../src/latest/ComparatorChallenges/ErdosProblems/Erdos1038.json).

The port updates Lean and mathlib APIs and keeps all finite certificates
checked by kernel reduction. The final theorem is `Erdos1038.erdos_1038`.
Its permitted axioms are only `propext`, `Classical.choice`, and `Quot.sound`;
the Comparator configuration also enables the independent nanoda kernel.

Normal Lean compilation and the full source/axiom audit passed. The Comparator
setup is provided, but a full Comparator run was not completed; further
Comparator validation was skipped at the contributor's request.
