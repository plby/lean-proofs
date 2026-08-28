# Erdős Problem 577 — final verification report

## Result

The exact Erdős–Faudree theorem is proved in Lean/Mathlib v4.33.0:
for every natural k, a finite simple graph of order 4*k with minimum
degree at least 2*k contains k pairwise vertex-disjoint cycles of exactly
four vertices. Chords are allowed. The cases k=0 and k=1 are explicit.

Main file: `src/latest/ErdosProblems/Erdos577.lean`.

- `Erdos577.erdos_faudree`: pointwise degree formulation, conclusion `HasPacking G k`.
- `Erdos577.exists_disjoint_four_cycles`: an actual embedding
  `Fin k × Fin 4 ↪ V` with every cyclic adjacency proved.
- `Erdos577.erdos_faudree_min_degree`: the formulation using `G.minDegree`.

`Packing.vertices` enforces distinctness within each cycle and disjointness
between cycles. `Packing.adjacent` requires the four cyclic edges only.
`HasPacking` is `Nonempty (Packing G k)`; it hides no graph hypotheses.
The main proof passes to a saturated extension, preserving the degree
bound, obtains an actual strong chain, and applies the proved weighted
degree contradiction from Claims2.5–2.7. No desired theorem is assumed.

## Files

- `tex/577.tex`: complete mathematical source proof, dependencies,
  constructions, and Leanization map; 21,851 lines, 254 compiled pages.
  Proposition9.82, the exact theorem, is on PDF214. Historical unfinished
  alternative branches in Sections2–8 are explicitly identified and are
  not dependencies of the complete source route in Section9.
- `src/latest/ErdosProblems/Erdos577.lean`: the three main theorems.
- `src/latest/ErdosProblems/Erdos577/`: 850 supporting Lean modules,
  `Verification.lean`, this report, `PROGRESS.md`, and `SOURCE_AUDIT.md`.
- Final twelve supporting modules: `ThreeRowsChoice`, `TripleFinalChoice`,
  `TripleFinalGeometry`, `TripleFinalChain`, `TripleOrientedLabels`,
  `TripleFinalRows`, `TripleFinalSelection`, `TripleFinalFactor`,
  `TripleFinalExcluded`, `TripleGivenBlock`, `ClaimTwoSeven`, `FinalCount`.
- `tmp/erdos577/verify_lean_sources.py`, `verify_final_constructions.py`,
  and `audit_final.py`: source checks, independent construction tests,
  and the final evidence audit. They are not proof oracles.

The complete filename and SHA-256 manifest is
`tmp/erdos577/validation/lean-final-audit.json`.
All 838 supporting proof modules from checkpoint80 are unchanged.
The supplied complete Wang2010 PDF retains SHA-256
`938ae213a338d882f0753883e0ef0b83f144397ed795ecb1ae292c6409590399`.
No files were staged or committed, and no computational limits were raised.

## Exact verification commands and results

Working directory: `/root/code/lean-proofs/src/latest`.
All three commands exited 0:

```sh
/root/.config/elan/toolchains/leanprover--lean4---v4.33.0/bin/lake build ErdosProblems.Erdos577 ErdosProblems.Erdos577.Verification
/root/.config/elan/toolchains/leanprover--lean4---v4.33.0/bin/lake env lean ErdosProblems/Erdos577.lean
/root/.config/elan/toolchains/leanprover--lean4---v4.33.0/bin/lake env lean ErdosProblems/Erdos577/Verification.lean
```

The full build reports 9,557 jobs. Both Verification runs contain the
same 2,032 ordered axiom reports, including all 30 new public declarations
and all three main theorems. The only axioms are `propext`,
`Classical.choice`, and `Quot.sound`; there are no new or project-local
axioms. There are no task warnings. Existing BoundedGaps/AINTLIB
dirty-checkout warnings are unrelated and unchanged.

Working directory: `/root/code/lean-proofs`.
All commands below exited 0:

```sh
python3 tmp/erdos577/verify_lean_sources.py
python3 tmp/erdos577/verify_final_constructions.py
python3 tmp/erdos577/verify_triple_low.py
python3 tmp/erdos577/audit_final.py
python3 -m py_compile tmp/erdos577/audit_final.py tmp/erdos577/verify_final_constructions.py tmp/erdos577/verify_lean_sources.py
pdflatex -interaction=nonstopmode -halt-on-error -output-directory=tmp/erdos577/validation tex/577.tex
git diff --check -- tex/577.tex src/latest/ErdosProblems/Erdos577.lean src/latest/ErdosProblems/Erdos577
git diff --cached --name-only -- tex/577.tex src/latest/ErdosProblems/Erdos577.lean src/latest/ErdosProblems/Erdos577
```

The source scan covers all 852 task Lean files. There are no placeholders,
forbidden declarations, computational-option overrides, or native proof
evaluation. Imports are acyclic and every module is reachable from
Verification. The final cached-diff command prints nothing. The audit
also checks whitespace in untracked Lean and TeX files and preserves the
earlier proof hashes and the 2,002-report prefix.

Independent tests check all 4,096 three-row masks, the 13 heavy patterns
and 32 valid choices, and 8,192 actual graph constructions. Both final
factor cases have 4,096 instances. Exact cycle edges, disjoint supports,
preserved block scores and untouched blocks are checked. Earlier low-row
tests also pass. These fixtures are not claimed globally feasible or
counterexamples; the Lean proofs do not depend on Python results.

Final TeX pass487 has 254 pages, with no warnings or overfull/underfull
boxes. All twelve changed pages and the mathematical main page214 were
rendered and visually checked. Seven checks use pixel-identical pass486
images, confirmed by byte comparison. All mathematical pages3–229 remain
textually unchanged from the pre-implementation checkpoint80 PDF.

## Evidence

All files are under `tmp/erdos577/validation/`:

- `lean-final-build.txt`, `lean-final-main-direct.txt`, `lean-final-axioms.txt`.
- `lean-final-audit.json`, `final-audit-run.txt`, `final-new-declarations.json`.
- `lean-sources-scan.json`, `final-constructions-independent.json`.
- `tex-pass487.txt`, `577-pass487.txt`, `577.pdf`, `final-pdf-pages.json`.
- `final-pass487-*.png`: the inspected final PDF pages.

The prior checkpoints and source audits remain as history. All 82 proof
milestones are complete; there is no remaining proof or validation gap
for the stated exact theorem.
