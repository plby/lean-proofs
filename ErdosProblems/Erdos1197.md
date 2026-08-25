This is a formalized proof of [Erdős Problem 1197](https://www.erdosproblems.com/forum/thread/1197).

It is available for these Mathlib (and Lean) versions:

* [Mathlib/Lean v4.33.0](../src/latest/ErdosProblems/Erdos1197.lean) (latest stable release, unconditional).
* [Mathlib/Lean v4.32.0](../src/v4.32.0/ErdosProblems/Erdos1197.lean).
* [Mathlib/Lean v4.30.0](../src/v4.30.0/ErdosProblems/Erdos1197.lean).
* [Mathlib/Lean v4.29.1](../src/v4.29.1/ErdosProblems/Erdos1197.lean).

The latest version proves `Erdos1197.bm_approx_data` using Kronecker approximation
and `chebyshev_asymptotic` from `PrimeNumberTheoremAnd.Consequences`.
Its supporting modules are in
[`src/latest/ErdosProblems/Erdos1197`](../src/latest/ErdosProblems/Erdos1197).
Both `bm_approx_data` and `not_erdos_1197` depend only on `propext`,
`Classical.choice`, and `Quot.sound`; the source files guard these axiom checks.
The older versioned snapshots still assume `bm_approx_data`.

From `src/latest`, check the latest proof with:

```sh
lake build ErdosProblems.Erdos1197
lake env leanchecker ErdosProblems.Erdos1197
```
