# Erdős Problem 353

[EPC](https://www.erdosproblems.com/353) ·
[Koizumi formalization](https://www.erdosproblems.com/forum/thread/353#post-7085) ·
[cyclic quadrilateral formalization](https://www.erdosproblems.com/forum/thread/353#post-7095) ·
[equilateral polygon formalization](https://www.erdosproblems.com/forum/thread/353#post-7098)

## Scope and authorship

The combined theorem covers all five questions: every measurable set of infinite
planar Lebesgue measure contains the vertices of a unit-area isosceles trapezoid,
an isosceles triangle, a right triangle, and a cyclic quadrilateral. There is also
a measurable set of infinite measure in which every strictly convex equilateral
polygon has area less than one.

The triangle and trapezoid arguments are by **Junnosuke Koizumi**,
[paper](https://arxiv.org/abs/2501.01914). The cyclic quadrilateral and polygon
arguments are by **Vjekoslav Kovač and Bruno Predojević**,
[paper](https://arxiv.org/abs/2412.11725).
The formalizations are by **Aristotle and JoshuaB**, who posted all three editor
links. His public profile does not identify a fuller human name; this repository
uses his published handle rather than guessing an identity.

## Provenance

All three links explicitly select the **Mathlib 4.28.0** editor project.
Their complete compressed-code URLs are retained in `data/urls.yaml`:

| Source | URL key | Aristotle request ID |
| --- | --- | --- |
| Koizumi | `JoshuaB_353_koizumi` | `75cddfef-5f21-4eef-8490-7ed7d1163368` |
| Cyclic quadrilateral | `JoshuaB_353_cyclic` | `c4fea4e2-cb48-4377-beea-4d91133951ca` |
| Equilateral polygon | `JoshuaB_353_polygon` | `f90b7996-0e71-4e59-87d2-03504f3d6c45` |

SHA-256 of the decoded original Lean text:

- Koizumi: `62114207fdce73367e2be68eca98e70c87b9a776cd4d49c297763d908a091d80`
- Cyclic: `ad853891d239b0bb507459f839b414a870a6455a89d0bdf379c4e86d9aa4e588`
- Polygon: `e3120d1f725f3407eb180ca424c0304a3e665bc082d697f74d8b36115bd8ee0c`

No separate license notice was found in the linked source text.

## Statement corrections and port

The original trapezoid predicate allowed crossed quadrilaterals: the ordered
points `(0,0), (4,0), (1,1), (3,1)` meet its area, parallelism, equal-leg,
equal-diagonal, and distinctness requirements. The imported public predicate also
requires strict convexity. A new coordinate lemma proves this for the original
construction, whose last two vertices are a common contraction of the first two.
The source predicate is retained only as the proof helper `RawIsoTrapArea1`.

The polygon source quantified an infinite-measure set `S`, but its vertex
hypothesis referred to the fixed construction `inS` instead of membership in `S`.
The imported theorem corrects this to `∀ i, C i ∈ S` and also proves the witness
measurable. The original argument already establishes the required bound for that
witness. Polygons are encoded by a cyclic list of at least three vertices, with
every non-adjacent vertex strictly to the left of every oriented edge. Degenerate,
repeated, multiply traced, or collinear-vertex encodings are not included.

The Lean 4.33 port updates measure-theory and differentiation APIs and makes
several tactic arguments explicit. The geometric corrections are checked in the
same kernel as the imported proofs. The independent Comparator challenge contains
only geometric definitions and the combined theorem, without the constructions
or helper lemmas. Its definitions are split into three independent modules to
match the source-file boundaries and stabilize Lean's generated proof names for
`Fin 2` indices. The challenge imports no solution code.

## Verification

- `lake build ErdosProblems.Erdos353 Erdos353` passes on Lean/Mathlib 4.33.0.
  The solution files emit no warnings; the challenge's intentional `sorry` is
  expected. Existing dependency-checkout warnings are unrelated to this import.
- `#print axioms Erdos353.erdos_353` reports exactly `propext`, `Classical.choice`,
  and `Quot.sound`.
- Independent `lean4export` exports pass `Comparator.compareAt` for the theorem
  and all referenced definitions, and `Comparator.checkAxioms` permits only the
  three standard axioms. A fresh Lean environment accepts kernel replay of the
  exported solution.
- The complete Linux sandbox/Nanoda runner was not run: this macOS environment
  lacks `landrun`. The Comparator configuration enables Nanoda for that runner.
- Source URL references, decoded-source hashes, import registrations, and
  challenge/configuration structure were checked. There are no proof placeholders,
  `native_decide`, custom axioms, or unsafe declarations in the solution.
