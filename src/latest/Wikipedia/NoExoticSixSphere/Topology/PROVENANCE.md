# Source provenance

`VanKampen.lean`, `SimplyConnectedSphere.lean`, and the additions in `Compat.lean`
are adapted from [mathlib PR #28246](https://github.com/leanprover-community/mathlib4/pull/28246),
head commit `037ad801e1e5a5b7aa1750957c07f7769812effc`, authored by Sebastian Kumar.
The Apache 2.0 license and copyright notices are retained.

The PR is an external source, not part of the installed mathlib. These copies are
checked locally with the project's Lean 4.33.0 toolchain. Their imports are routed
through this directory, and the PR's additions to existing mathlib files are
isolated in `Compat.lean`. No installed dependency is modified. No computational
limit is increased.

Additional local compatibility changes replace the induction step's `grind`
call with an explicit path-junction cancellation and homotopy composition.
The original call reached its default E-matching-round threshold in this
toolchain; that threshold was not increased. Endpoint range proofs are also
made explicit to avoid dependent-index rewriting failures.

The supplied result is simple connectivity of spheres of dimension at least two,
not classification of their smooth structures.
