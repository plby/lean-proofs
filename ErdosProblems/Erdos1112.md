# Erdős Problem 1112

## Statement

For integers `k ≥ 3` and `1 ≤ d₁ < d₂`, a lacunarity ratio with the property
in [Problem 1112](https://www.erdosproblems.com/1112) exists exactly when
`d₂ ≥ k + 1`.

The main theorem `Erdos1112.erdos_1112` states this dichotomy with a natural
ratio. `erdos_1112_int` states the same equivalence with an integer ratio,
using the source's proved bridge between the two formulations. Both final
statements expand the conclusion wrappers `Question` and `RatioWorks`.

The import also retains the explicit existence ratio `192 * d₂` and the
strong non-existence result: when `d₂ ≤ k`, every prescribed sequence of
lower ratios admits a single positive, strictly increasing sequence `B`
that meets the `k`-fold sumset of every admissible `A`.

The definitions retain the important quantifiers and conventions:

- `B` is positive and strictly increasing, including for ratios below two.
- `A` is positive; the additive gap bounds force strict increase when
  `d₁ ≥ 1` and avoid truncated-subtraction ambiguities.
- The sumset allows repeated summands.
- The quantifier order is `∃ r, ∀ B, ∃ A`.

## Source and attribution

[Johan Land's EPC comment, 6 July 2026](https://www.erdosproblems.com/1112#post-7375)
links the complete development. [Thomas Bloom's comment, 13 July 2026](https://www.erdosproblems.com/1112#post-7517)
reports checking that the main theorem faithfully formalizes the claim and
that the source compiles without admissions; he distinguishes that check
from understanding the mathematical proof.

The imported source is
[`beetree/math_erdos_1112`, commit `63ed94d3e802782aeb521095c17d6109a2dc57b5`](https://github.com/beetree/math_erdos_1112/tree/63ed94d3e802782aeb521095c17d6109a2dc57b5).
The initial complete publication was commit
`8c154d2ac4f7763467bc8230860399d8971a0cb1` on 6 July; the integer-ratio bridge
was added in `e011ee07196026484dc4a28bfb1fac8725254f31` on 14 July.

Johan Land is the named human author. The source's
[provenance section](https://github.com/beetree/math_erdos_1112/blob/63ed94d3e802782aeb521095c17d6109a2dc57b5/paper/erdos1112.tex)
attributes the mathematical arguments and Lean formalization to his work
with **Claude Fable 5 and Claude Opus 4.8**. Land selected the statement,
set targets and strategy, chose routes, and audited the constructions.
**GPT-5.5 and Gemini 3.1** supplied advice and adversarial review, rather
than being identified as the formal proof writers. The AI fields in
`sources.yaml` record these tools' contributions, not a claim that the
paper lists them as authors.

## Versions and license

The upstream `lean/lean-toolchain` pins **Lean 4.27.0**. Its manifest pins
Mathlib to **`a3a10db0e9d66acbebf76c5e6a135066525ac900`**, and
formal-conjectures to `75573bb6ae02bcb7008714e2bdb11ee09a52d142`.
The imported Lean files use Mathlib directly and do not require a new
formal-conjectures dependency.

This repository's port targets **Lean/Mathlib 4.33.0**. The upstream
Apache 2.0 `LICENSE` and `NOTICE`, including **Copyright 2026 Johan Land**,
are preserved under `src/latest/ErdosProblems/Erdos1112/`.

## Layout and verification

The source statement file becomes `Definitions.lean`. The proof modules
retain their `Existence`, `NonEx`, and `Sharp` organization. The root
`Erdos1112.lean` assembles the four final results and prints their axioms.
The finite certificate arguments use kernel-checked proofs; the import
does not introduce `native_decide` or additional mathematical axioms.

The port updates the finite-sum and set-predicate APIs, replaces obsolete
negation syntax and redundant tactics, narrows classical scopes, closes
the original `CaseL` namespaces explicitly, and removes unused helper
hypotheses. In particular, strong non-existence does not need `d₁ < d₂`;
that unused hypothesis is omitted from this companion result. The main
dichotomy retains the original problem's hypotheses.

The independent Comparator challenge repeats only the definitions needed
to state the four final results and registers all four in its configuration.

`lake build ErdosProblems.Erdos1112 Erdos1112` passes with no solution
warnings. The independent challenge emits only its four intentional
placeholder warnings; unrelated dependency checkout notices remain.
All four final results print only `propext`, `Classical.choice`, and
`Quot.sound` as axioms.

Both modules were exported with `lean4export`. Comparator's `compareAt`
accepted all four theorem statements and their definitions, and
`checkAxioms` accepted the same four theorems with only those three
permitted axioms. Replaying the exported solution declarations in a fresh
Lean kernel environment also succeeded.

The full Linux sandbox/Nanoda runner is unavailable on this host. The
checks above use the local Comparator APIs and Lean kernel; Nanoda remains
enabled in the committed configuration for the standard Linux runner.
