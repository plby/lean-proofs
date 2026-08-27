This is an unconditional Lean formalization for [Erdős Problem 587](https://www.erdosproblems.com/forum/thread/587).

For the largest size of a subset of `{1,...,N}` with no nonempty square subset sum,
the development proves a cube-root lower bound and the upper bound
`K * N^(1/3) * max(1, log(log N))^16` for all sufficiently large `N`.
In particular, the growth is `N^(1/3 + o(1))`.

The [independent log-log reconstruction](../tex/erdos587/LOGLOG_RECONSTRUCTION.md)
records the analytic and geometric proof. The Comparator setup checks the lower
bound, the earlier logarithmic upper bound, the log-log upper bound, and the
growth consequence.

It is available for these Mathlib (and Lean) versions:

* [Mathlib/Lean v4.33.0](../src/latest/ErdosProblems/Erdos587.lean) (latest stable release).
