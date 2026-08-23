The first line of the file should be a comment like `/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/` saying which version of Mathlib is being used.

The next comment block should include license information if any exists.  Specifically, it should state the license if there is one and note that the file has been modified.

The next comment block should state the original authors, first of the informal proof and then of the formal proof.  Finally, the comment block should give a reference for where to obtain the original formalization.

The file should build cleanly with `lake lean`.

The file should be included in `All.lean`, and so build cleanly with `lake build`.

The file should not emit any warnings.

It is nice to include a more general result that implies a more specific result, but the final theorem should preferably be named `erdos123` or `not_erdos123`, and should be a "leaf result" that captures the precise statement that Erdős conjectured.

At the end of the file, the command `#print axioms erdos123` should be used for whatever the main theorem is.  There can be multiple such lines.  After each such line, there should be a comment saying what the output of this line is.

Any non-standard axioms used should be imported from `Axioms.lean`.

The proofs should all be sorry-free.

The proofs should not use `native_decide`.

The file should mostly be wrapped in a namespace, like `namespace Erdos123`.

There should be no usage of `noncomputable section`.

Unused variables should actually be removed, as opposed to simply prefixed by an underscore.
