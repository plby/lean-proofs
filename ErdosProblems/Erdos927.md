# Erdős Problem 927

[EPC](https://www.erdosproblems.com/927) ·
[formalization comment](https://www.erdosproblems.com/927#post-6850) ·
[original source](https://gist.githubusercontent.com/JohnEdwardJennings/24c9debc9854cb118fbc1314c70941c3/raw/b4fc5ef91876a89018b10508c479c000258504fb/Erdos927.lean) ·
[selected source](https://github.com/Jayyhk/erdos-lean/tree/cc6c94bd3f9de7c4cf7703ed40d8fd06380780a3/problems/927)

## Statement and scope

Here `g(n)` counts the largest possible number of **distinct maximal-clique
sizes** in a graph on `n` vertices. Maximal means inclusion-maximal, not
maximum cardinality. Counting all complete subgraphs would give a different,
trivial extremal problem.

`Erdos927.not_erdos_927` states that there are no constants `C` and `n₀`
such that `g(n) + Nat.log 2 n + logStar(n) ≤ n + C` for every `n ≥ n₀`.
Thus even the eventual upper-bound direction of the conjectured asymptotic
formula fails. `logStar` iterates the integer base-two logarithm until the
value is at most one.

The imported construction proves
`N ≤ g(N) + Nat.log 2 N + 6` on the unbounded sequence `N = spN(n)`,
for `n ≥ 16`. This subsequence suffices for the disproof; the port does not
claim to formalize the stronger published lower bound for every sufficiently
large vertex count. The root theorem adds an arbitrary starting threshold
to the source's uniform-bound disproof.

## Authorship and source selection

The mathematics is **Joel H. Spencer**'s *On cliques in graphs*,
Israel Journal of Mathematics 9 (1971), 419–421, also listed in
[Spencer's publication list](https://cs.nyu.edu/~spencer/papers/vita.pdf).
The original file explicitly credits **John Jennings** and
**Aristotle (Harmonic)** and carries Jennings's 2026 copyright notice.
Jennings posted the EPC comment on 5 June 2026.

The original gist has a single revision,
`b4fc5ef91876a89018b10508c479c000258504fb`, created 5 June 2026.
It contains five uses of native evaluation. The selected collection snapshot
is `cc6c94bd3f9de7c4cf7703ed40d8fd06380780a3`; **Jake Mallen** added its
kernel-checked replacements in `fe9faab7d74233d75614b9d69e9682dc9fee2e38`,
with a later comment update in `806d0b587ea7a2fb5afd5154edfe416a0cd404a4`.
The comparison with the original shows the replacement proofs, an explicit
small-value calculation, and final-statement cleanup. Mallen's formal credit
records this work separately from the original authorship.

The EPC editor link explicitly selects Mathlib 4.28.0. The selected copy's
`lean-toolchain` also specifies `leanprover/lean4:v4.28.0`, and its Mathlib
dependency is pinned to `8f9d9cff6bd728b17a24e163c9402775d9e6a365`.
That original version is recorded in `sources.yaml`.

The original file specifies Apache 2.0. Its copyright notice is preserved,
modified files are marked, and the standard license text is included in
`Erdos927/LICENSE`; the gist itself did not supply a separate license file.

## Port and Comparator

The proof is split into `Definitions`, `Basic`, `Graph`, `Lookup`, `Medium`,
`Big`, `Small`, and `Construction`. Classical instances are local to
definitions or proofs. The final theorem directly states the negative answer,
without a proposition wrapper.

The independent Comparator challenge imports only Mathlib and repeats the
maximal-clique predicate, maximal-clique-size count, extremal function,
integer iterated logarithm, and final theorem. It contains no construction
or solution imports.

The port proves graph relabeling by inclusion of the sets of clique sizes,
separates cardinality simplification from unfolding vertex-size definitions,
and replaces fragile offset unfoldings with recurrence identities. The
largest finite check is reduced to the first level using the existing
deep-level bound. All finite computations use kernel-checked proofs.

## Verification

- `lake build ErdosProblems.Erdos927 Erdos927` passes on Lean/Mathlib 4.33.0.
  The solution emits no warnings; the independent challenge has its expected
  placeholder warning.
- `not_erdos_927` depends only on `propext`, `Classical.choice`, and `Quot.sound`.
- Independent exports pass `Comparator.compareAt` and `Comparator.checkAxioms`;
  a fresh Lean environment accepts kernel replay of the exported solution.
- The full Linux sandbox/Nanoda runner was not run because this macOS
  environment lacks `landrun`. Nanoda remains enabled in the configuration.
- Metadata, unique registrations, license notices, configuration consistency,
  and the absence of solution placeholders, `native_decide`, custom axioms,
  unsafe declarations, `run_cmd`, and file/process IO were checked.
