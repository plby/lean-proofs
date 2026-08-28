# Wang 2010: source and dependency audit

## User-supplied principal source — 2026-08-26

The complete paper is now available. This supersedes the missing-source
warning in the older shared guide; that guide is preserved unchanged.

- Hong Wang, *Proof of the Erdős–Faudree Conjecture on Quadrilaterals*,
  Graphs and Combinatorics 26 (2010), 833–877.
- DOI: 10.1007/s00373-010-0948-3.
- PDF: `/root/code/lean-proofs/tmp/erdos-proof-sources-20260825-01a03b42/user-supplied/20260826/x577.pdf`.
- Searchable text: the same path with `.txt` appended.
- Independently checked size: 706,955 bytes; 45 PDF pages; unencrypted.
- Independently checked SHA-256:
  `938ae213a338d882f0753883e0ef0b83f144397ed795ecb1ae292c6409590399`.
- No original TeX was supplied. PDF text is a search aid, not authoritative
  for formulas. Poppler emits a shared-object-hint warning but renders the
  inspected pages successfully.

Theorem **B**, printed 834 / PDF 2, has exactly order 4k and minimum degree
at least 2k, with k vertex-disjoint cycles of length **four**. PDF pages 2
and 4 were visually inspected. Theorem A has different order/degree
hypotheses and is not the requested boundary theorem.

## Proof map and audit state

The complete transcription, including all of §4 and the references, has
now been read. A truncated tool response around PDF 29–30 was explicitly
re-read in full. The source route is now fully reconstructed in TeX,
including Claims 2.1–2.7 and the final exact theorem. All source pages
used through PDF 45 have been visually checked during adaptation.
**None of this is a completed Lean formalization or main-theorem build.**

| Item | Printed / PDF pages | Status and role |
| --- | --- | --- |
| Theorem B and definitions | 834–835 / 2–3 | Exact statement checked; chord count = induced block edges minus four |
| §2, Claims 2.1–2.7 and final deduction | 835–836 / 3–4 | Read; formulas on PDF 4 visually checked |
| Lemmas 3.1–3.6 | 836–840 / 4–8 | Explicit TeX proofs, including a direct proof of the cited 3.4(a); supplemental finite checks pass |
| Lemmas 4.1–4.2 and Claim 2.1 | 840–842 / 8–10 | Explicit TeX proofs; Claim 2.1 uses the earlier saturation and attachment reductions with scope made explicit |
| Lemma 4.3, patterns (3)–(8) | 842–845 / 10–13 | Explicit TeX proof with all row cases and replacement constructions; finite check passes |
| Lemma 4.4, patterns (9)–(20) | 845–849 / 13–17 | Complete TeX proof of the initial stage and all six exclusions; finite construction checks pass |
| Lemma 4.5 | 849–851 / 17–19 | Complete TeX proof excludes (14); all finite construction checks pass; maximizing choice explicit |
| Lemma 4.6 | 851–853 / 19–21 | Complete TeX proof excludes (13); finite factors and both score comparisons checked |
| Lemma 4.7 | 853–855 / 21–23 | Complete TeX proof of exclusions (4), (5), (7); all complementary paths and exchanges checked |
| Lemma 4.8 | 855–856 / 23–24 | Complete TeX proof excludes (6); five reductions and final factors checked |
| Lemma 4.9 and Corollary 4.9.1 | 856–858 / 24–26 | Corrected seven-vertex version proved explicitly in TeX; all construction checks pass |
| Claim 2.2 | 858 / 26 | Complete TeX proof via twelve paths, a local involution, and the corrected core corollary |
| Lemmas 4.10–4.11 | 858–860 / 26–28 | Complete explicit TeX proofs; inside bounds and all construction checks pass |
| Claim 2.3 and the joint setup | 860–864 / 28–32 | Complete TeX proof, separating the condition-(I) part of 4.12; finite checks pass |
| Subclaim (b) and reduction to Case II | 861–862 / 29–30 | Explicit TeX proof and all finite checks pass, using the already proved Claim 2.3 |
| Remaining part of Lemma 4.12 | 864–865 / 32–33 | Complete TeX proof with all transfer checks; finite block choice includes an explicit tie break |
| Lemma 4.13 and Claim 2.4 conclusion | 865–867 / 33–35 | Complete TeX proof, including changed-center variants and alternate pair; local/global checks pass |
| Claim 2.5 | 867–868 / 35–36 | Complete TeX proof with the local involution, corrected six-contact count, and final factor checks |
| Lemmas 4.14–4.16 | 868–870 / 36–38 | Corrected transfer and nonvacuous dense-pair lemma proved; all preparation checks pass |
| Claim 2.6 | 870–874 / 38–42 | Complete TeX proof; explicitly count sparse-side attachments, prove uniqueness and both equality counts |
| Claim 2.7 | 874–877 / 42–45 | Complete TeX proof; universal heavy-block conclusion, 48 explicit table witnesses, and final two-stage exchange |

## Reuse and external dependencies

1. Wang uses Randerath–Schiermeyer–Wang (1999), *On quadrilaterals in a
   graph*, Discrete Mathematics 203, 229–237, to start with a triangle
   remainder. The existing TeX `prop:triangle-exists` supplies an independent
   saturation/path-exchange proof of that starting point **in an edge-maximal
   counterexample**. Section 9 now explicitly takes that finite supergraph
   maximum first. This is sufficient for the main contradiction; it is not
   a claim about existence of a triangle remainder in every unsaturated
   counterexample. This reduction is now proved in Lean by
   `Saturated.exists_triangle_chain`, including the full path exchange,
   all unchanged blocks, and the exact boundary degree count.
2. Wang's feasible chains maximize total chords, then the number of K4
   blocks. These are exactly the first two scores already used in the
   reconstruction. Later five-set refinements must not be silently assumed
   for arbitrary feasible chains.
3. Existing `prop:singleton-attached` supplies the existence conclusion of
   Claim 2.1. New `prop:wang-strong-exists` makes its scope precise: maximize
   a third score only to obtain one attached chain, then forget that third
   condition. Later lemmas concern arbitrary strong feasible chains with
   the first two scores, not only the specially chosen attached member.
   This existence reduction is now kernel proved as
   `Saturated.exists_strong_chain`. Its four weighted finite cases have
   696 explicit positive witnesses; the graph-copy transport, both block
   scores, and attachment maximum are checked. The `Strong` Lean structure
   retains only feasibility and the actual attachment, not the third maximum.
4. Lemma 3.4(a) cites Lemma 2.7 of Wang (2004), *On quadrilaterals in a
   graph*, Discrete Mathematics 288, 149–166. It is a finite eight-vertex
   statement. New `lem:wang-eleven-paw` gives a direct proof by the leaf
   degree and the noncentral row degrees. Its 27,488-graph check passes;
   only eight graphs are nonfactors, all having the stated exception.
   Thus the mathematical cited dependency is discharged, though the proof
   still needs Lean implementation. It is needed in Claims 2.6 and 2.7.
5. Lemmas 3.1–3.3 and 3.4(b)–3.6 have proofs or finite observations in the
   supplied paper. Every needed observation and exchange still requires a
   legitimate proof in the final TeX and Lean; the citation is not an axiom.
6. The paper's Lemma 4.2 excludes a remainder containing **two disjoint
   edges** when the chord gain is at least two. New TeX
   `lem:wang-matching-exchange` proves the needed local matching exchange
   by a four-entry contact matrix, without local optimality. Then
   `lem:wang-matching-score-bound` combines it with the existing path-score
   bound and gives the exact two-edge remainder conclusion. This is an
   explicit adaptation, not an identification of the two different bounds.

The new TeX `lem:wang-almost-seven-clique` and
`lem:wang-dense-triangle-outside` give explicit proofs of Lemmas 3.1 and
3.2. Their supplementary finite checks passed 273 / 126 / 13 / 25
constructions for the four parts of 3.1 and all 5,280 minimal graphs for
3.2 (5,208 factors and 72 strict gains). These are not Lean checks.
The matching-exchange check passes all 45,760 nine-contact graphs:
per diagonal, factor / triangle-dense-block / path-complete-block counts
are (8064,3168,208), (8256,3064,120), (8256,3064,120), (9312,2112,16).
The TeX `lem:wang-common-triple` gives an explicit proof of Lemma 3.3.
Its check covers 1,600 row-pattern graphs: 1,116 meet the threshold,
952 fail the no-replacement hypothesis, 104 fail the matching-gain
hypothesis, and all 60 remaining graphs have the required common triple
and exact weighted sum nine.

`lem:wang-nine-triangle-paw` proves 3.4(b) directly, using the new
3.4(a). Its check covers 13,455 input graphs, of which 13,215 have a
universally replaceable triangle row; every one has a factor.

`lem:wang-path-classification` proves all of 3.5, including its extra
replacement conclusions. The noncomplete-block case follows from the
matching exchange. For the complete-block case the proof splits on the
larger endpoint row degree and spells out the factors and triangle/K4
constructions. Of 26,333 contact masks, 25,419 have factors, 694 have
triangle/K4 witnesses, and 220 give the two stated patterns (88 type A,
132 type B). All 660 additional replacement assertions and all 220
triangle/five-edge-block assertions pass the independent finite check.

`lem:wang-chain-replacements` proves 4.1 by one-vertex edge counts and
two-row intersections. Checks cover 20 terminal inputs (nine satisfy the
no-improvement condition) and 316 triangle inputs (231 improve; all 85
survivors satisfy the structural conclusions).

`lem:wang-local-obstructions`, `lem:wang-two-leaf-classification`, and
`lem:wang-first-classification` give the full 4.3 argument. The independent
check covers 104,136 graphs: 102,440 factors, 1,340 triangle gains, eight
matching gains, and 348 instances of patterns (3)–(8). Its 144 outside-pair
constructions all pass.

`lem:wang-weighted-initial` proves only the initial stage of 4.4, retaining
all twelve patterns (9)–(20), with the extra replacement assertions for
(10)–(12). The check covers 100,928 graphs; all remaining patterns and
300 outside-pair constructions pass. The final six-pattern conclusion
is now proved in `cor:wang-weighted-classification` by all six exclusions.
All checks in this section are research checks, not kernel proofs.

`lem:wang-improved-path-transfer` derives local path optimality from the
global path-score bound after improving another block by one. It does not
silently assume path optimality of a feasible chain.
`lem:wang-exclude-eighteen-twenty` then excludes (18),(20) by the two path
orders and explicit three-block factors; 220 exceptional-path instances
per pattern pass their factor checks.

`lem:wang-exclude-sixteen-seventeen` excludes (16),(17). It uses an inside
degree sum at most 19, the high-path alternatives, re-exposes q4 without
changing either score, and checks five paths to forbid all column pairs
except {x0,x1}. The resulting intersection has size at least three and
gives the final factor. For each pattern, eight inside variants, 40
five-path constructions, 2,500 high-path factors and 84 low-path factors
pass their supplementary checks.

`lem:wang-exclude-nineteen` strengthens the center restriction to an empty
row, proves the local involution that exchanges the two path presentations,
and gives seven explicit insertion tests. The involution preserves the
eight-vertex core and defines a new strong feasible chain; it is not
assumed to preserve outside adjacencies as a graph automorphism. In path
pattern B, at most one allowed contact is missing, and the original paw
reduces this to three cases. The check verifies the four center exclusions,
local symmetry, seven paths, and 40,584 threshold extensions of the 220
exceptional path masks. All extensions have insertion factors.

Pattern (15) is handled by `lem:wang-fifteen-setup`,
`lem:wang-fifteen-lfour`, `lem:wang-fifteen-dense`, and
`lem:wang-exclude-fifteen`. The first three prove the missing center
contacts, a uniform outside-block bound for the fourth path, and the
forced twelve-vertex configuration. The final proof constructs two
feasible terminal chains, bounds a six-vertex inside degree sum by 32,
forces an outside column with four neighbors, and uses two seven-row
path/two-cycle tables to obtain a four-block factor. It does not need the
source's longer separate treatment of the high-path case at the third block.

The pattern-(15) check covers 56,320 L4 extensions (56,140 insertion
factors; all 180 survivors obey the uniform bound) and 40,584 threshold
L3 extensions (40,576 insertion factors, four split factors, four rigid
cores). It also checks 512 optional inside-edge variants, all fourteen
complement tables, all twenty endpoint triples, and 504 four-block lifts
over the nine nonimproving terminal/quad patterns. These are supplementary
finite checks, not Lean proofs. No later Wang claim was assumed to prove 4.4.

The TeX now proves Wang 4.5 in `lem:wang-fourteen-heavy`,
`lem:wang-fourteen-dense`, and `lem:wang-exclude-fourteen`. It uses the
actual pattern (14), corrects the initial replacement block index, and
distinguishes a feasible terminal from a strongly attached terminal.
The extra finite maximum over occurrences is used only in the final lemma,
after the second-block analysis exhibits center degree two.
The final four-terminal insertion uses two explicit complementary cycles;
there is no omitted "easy to check" partition. PDF pages 18–19 and TeX
pages 159–163 (pass 306) were visually inspected.
The new finite check covers 163,099 large-terminal cases, 1,464
small-terminal cases, 1,536 inside variants, 2,592 four-block factors,
and 26,333 pigeonhole matrices, all successfully. These are research
checks rather than Lean proofs. No later source claim is used by 4.5.

The TeX also proves Wang 4.6 in `lem:wang-thirteen-dense`,
`lem:wang-thirteen-setup`, `lem:wang-thirteen-universal`, and
`lem:wang-exclude-thirteen`. The path step has eight explicit insertion
rows, and all thirteen later path complements are listed as two cycles.
The source's appeal to the second maximum is expanded: if the new edge
total is larger use the first maximum; equality requires an old diamond
and then the number of complete blocks increases. The leaf-degree-one
case uses equality of two neighborhoods to transfer universal
replaceability, instead of silently assuming a diagonal.
PDF pages 20–21 were visually inspected. Finite checks pass for 40,584
path extensions, 2,048 inside variants, eight terminal exposures, 62,852
nonuniversal-row cases, and 112,808 final cases. These do not replace
the written argument or the required later Lean proof.

The new `cor:wang-small-leaf-weighted` proves the weighted bound for leaf
degree at most two. Wang 4.7 is then reconstructed in `lem:wang-four-pairs`,
`lem:wang-exclude-four`, and `lem:wang-exclude-five-seven`. Its local
complementary paths are proved by the at-most-one missing contact, including
all endpoint-pair cases. For a complete designated block, the alternative
chain retains both scores and exchanges the two noncentral pairs.
All common-triple hypotheses in the (7) exclusion are stated explicitly.
The supplementary check passes 396 complementary triples across 22 graphs,
22 diamond exposures, 11 complete exchanges, 80 replacement intersections,
and 616 reduced (7) cases. PDF pages 22–23 and TeX pages 166–169 (pass 311)
were visually checked. TeX pages 163–167 from pass 309 were also checked
for the preceding 4.6 proof. These remain mathematical and research checks,
not Lean theorem validation.

`lem:wang-exclude-six` now proves Wang 4.8. Its five cases are exactly
the five possible missing contacts after a transfer to (5) is forbidden.
The two explicit relabelings and both feasible terminal chains preserve
the five-edge block score. Twelve path complements are written out.
The final use of a row of size at least three is ordinary replacement
at two vertices meeting a common three-set; the proof does not silently
declare x2 a feasible terminal. The check passes eleven initial graphs,
two relabelings, six terminal exposures, 1,232 reduced (22),(23) cases,
and 4,236 / 4,836 factors in the two (24) branches.
PDF pages 23–24 were checked, including the replacement-index slip below.

The corrected core argument is now proved in `lem:wang-two-heavy-blocks`,
`lem:wang-core-obstruction`, and `cor:wang-core-consequences`. The core is
explicitly T union B. Direct and bridge routes preserve both scores;
the uniform thirteen-contact conclusion forces two dense outside blocks.
The fifteen-contact inside equality gives a complete seven-set and two
fully specified factor constructions. The corollary's second part is
proved without the unused global outside-neighbor condition or z2.
All finite construction checks in `check_wang_core.py` pass, including
840 inside equality cases. Its initial fixture union-assignment bug was
fixed and the whole check rerun, without altering a mathematical premise.

`lem:wang-exclude-eight` and `cor:wang-claim-two-two` now complete Claim 2.2.
The local permutation is explicitly (x0 x3)(x2 q1), used only to construct
another feasible chain. Twelve paths cover every insertion/endpoint pair.
The equality case fixes the high reflection before the triangle gain,
so the displayed blocks are disjoint. Every hypothesis of the corrected
seven-core corollary is verified at its application; the final count
is 35<=33. The supplementary check passes all 2,208 reduced cases.
PDF pages 24–26, TeX pages 171–175 (pass 316), and pages 174–177
(pass 318) were visually checked. Pages 169–172 (pass 313) were also
checked for the preceding 4.8 proof.

Wang 4.10 and 4.11 are now proved explicitly in
`lem:wang-full-row-obstruction` and `lem:wang-two-vertex-core`.
The former separates the two possible core routes and corrects the
terminal-exposure index. The latter includes the implicit zero leaf
row into the core block, the coupled bound giving 23 inside contacts,
and a global path-transfer lemma permitting two changed blocks.
The finite checks in `check_wang_full_rows.py` and
`check_wang_two_vertex_core.py` pass. Source pages 27–28 and the new
TeX pages 176–180 (passes 320/322) were visually checked.
Claim 2.3 has since been completed by the joint setup, dense-core
classification, and the condition-(I) part of Wang 4.12. A center
exchange handles its other heavy-block orientation while retaining
the dense block. The reconstruction proves Claim 2.3 before using it
in Subclaim (b), so that later use is not a circular assumption.
The 93 admissible core patterns and 1,953 outside-neighbor pairs
pass direct checks. Source pages 29–32 and TeX pages 179–186
(pass 327, 200 pages) were visually checked. At that point the
other-block route of 4.12 still required the later argument;
Claims 2.4–2.7 remain outstanding.

Subclaim (b) and the Case II reduction are now explicit in
`lem:wang-joint-eight-rows` and `lem:wang-joint-case-two-reduction`.
The original dense block is retained through both center exchanges;
the phrase replacing the old first block does not assert that this
old block becomes the new dense one. The 534 row cases and both
exchange families pass `check_wang_joint_eight.py`. Pass 330 compiles
202 pages cleanly, and pages 185–188 were visually checked.

The other-block route of 4.12 is now proved in
`lem:wang-joint-bridge-obstruction`. It reuses the local four-row
argument only after checking the new complementary factors, score
preservation, and both core-corollary applications. All 29,388 routes
pass the supplementary check. The maximal-core lemma explicitly
breaks equal triangle-contact scores by the center-plus-noncentral
sum; this justifies the ten-contact conclusion in the seven-sum case.
Pass 333 has 204 pages and no warnings; pages 187–190 were checked.

The notation e(S,T) has been clarified for overlapping sets: it is the
sum of degrees from S into T, so e(S,S)=2e(S). This is the convention
used by all inside-degree counts; e(S) separately counts induced edges.

## Validation location after the environment refresh

The earlier `/tmp/erdos577-validation/` directory is absent in the refreshed
environment. Historical results above remain recorded, but old temporary
files are not claimed to be currently available. New outputs are saved
under the project directory `tmp/erdos577/validation/`.
The supplied paper and project source files persisted. LaTeX and Poppler
were missing and were restored through approved `apt-get update` and
`apt-get install -y --no-install-recommends texlive-latex-base
texlive-latex-recommended texlive-fonts-recommended poppler-utils`.
No resource-limit option was set. New validation is being rerun there.
The Lean launcher fails inside the refreshed sandbox with `error: failed
to locate application`, but an approved launch outside it succeeds.
The project's `lake env lean --version` likewise reports Lean 4.33.0
(commit `d8b18978322de05a8f3dba51ef03cf5461676c17`) outside the sandbox.
No installation change was necessary; this is not a main theorem build.

The shared project filesystem subsequently filled during PDF preview
rendering (125 GB used, 84 KB available; Poppler PNG write error, exit 139).
An approved move relocated only generated validation outputs to
`/root/.cache/erdos577-01a03c40-validation/`, preserving the old
`tmp/erdos577/validation/` path as a symlink and verifying the PDF hash
across the move. The supplied paper, TeX, scripts, and other tasks' files
were untouched. Rendering and builds resumed. No quota or computational
limit was raised.

## Final arithmetic to retain exactly

Write the strong remainder as x0–x1 with triangle x1,x2,x3. No factor
forces x0 to have exactly one neighbor in the triangle. For a block Q,
put a=e(x0,Q) and b=e(x2,Q)+e(x3,Q). Claims 2.5–2.7 imply 2a+b<=8:
for a=4 use 2.6, for a=3 use 2.7; if a<=2 and 2a+b>=9 then a+b>=7,
and 2.5 forces either a=0 or (a,b)=(1,6), both impossible at that threshold.
The weighted inside degree sum is 2*1+2+2=6. Hence
8k <= 6+8(k-1) = 8k-2, a contradiction. The k=0 and k=1 cases are
already explicit in the existing draft. This calculation is not a
substitute for proving Claims 2.5–2.7.

## Claim 2.4 completion

The source adaptation now includes all of 4.13 and Claim 2.4.
`lem:wang-final-initial` handles the initial leaf and score-preserving
cases. The loss, opposite-pair, three-row, and full-row lemmas verify
all remaining cases, with the complete-core variant used when the
center changes in (28). `lem:wang-final-full-row-excluded` proves the
inside bound 46 and both five-cycle factor constructions.
`cor:wang-final-local-classification` is universal over all qualifying
outside blocks and valid for the alternate core pair. Its two uses
give `cor:wang-claim-two-four`.

The local check passes 34,691 inputs and the global check verifies
65,408 inside variants, 10,080 final six-row factors, 24 alternate-pair
checks, and 192 final Claim 2.4 factors. Pass 348 compiles 213 pages
without warnings. The proof pages were checked visually; a duplicated
final-count heading was caught in the preview and removed. Claims
2.5–2.7 and all main Lean implementation/validation remain outstanding.

## Source slips and pending checks

- **Confirmed in the rendered PDF:** Lemma 4.5 opening (PDF 17) prints
  N(x2,Q1)={c1,c4,c2}, while pattern (14) and the subsequent argument
  require {c1,c4,c3}. Use the actual pattern (14) in the adaptation.
- **Confirmed in the newly rendered PDF 17:** the end of the (15)
  analysis prints e(z0,Qp)=4 with no Qp defined there. The block is Q2.
  The adaptation derives its four leaf contacts directly and uses Q2.
- **Confirmed in the rendered PDF:** its opening continuation (PDF 18)
  prints x0⇒(Q2,cr) for cr∈Q1. The replacement refers to Q1, since the
  removed vertex belongs to that block. Do not copy the printed Q2 index.
- **Confirmed in the rendered PDF:** Claim 2.1's proof (PDF 9) twice
  prints ci∈V(T), although ci denotes a vertex of Qr. The intended
  vertex set in both statements is Qr.
- **Confirmed in the rendered PDF:** Lemma 4.7's complementary-path
  argument (PDF 22, printed 854) has e(x1,Q2)=4 when the leaf has only
  one high neighbor in Q1. The block there is Q1; Q2 is chosen later.
  The reconstruction uses the ten possible contacts to Q1 directly.
- **Confirmed in the rendered PDF:** Lemma 4.8, PDF 24 / printed 856,
  begins with x2→(Q2,c2), although c2 is in Q1. Use Q1. The TeX proof
  displays the actual replacement cycle on Q1-c2+x2.
- **Confirmed printed definition; required corrected version now proved:**
  Lemma 4.9 (PDF 24) and Corollary 4.9.1 (PDF 25) print G0=[F,Q2].
  The proof treats G0 as seven vertices: G0+d3 supplies two spanning
  quadrilaterals after x0 is inserted elsewhere; G0+x0+dr-zi has eight
  vertices; and G0-{x1,z1,z2} is a four-set. Also its case
  e(F,Q2)+e(d2d4,F∪Q2)>=15 would be impossible if G0=F∪Q2,
  given the preceding bounds 12 and one contact per low vertex.
  The needed interpretation is G0=T∪Q2. Lemma 4.10 on PDF 26 explicitly
  uses that seven-vertex definition. The new TeX proves the required
  T∪Q2 version and explicitly verifies its use in Claim 2.2; later uses
  must continue to use that corrected statement.
- **Confirmed in the rendered PDF:** the end of Lemma 4.10 (PDF 27 /
  printed 859) says x0⇒(Qt,d2), although d2 belongs to Qr. The terminal
  exposure takes place in Qr, and the resulting terminal is then
  universally replaceable on the distinct outside block Qt. The new
  proof uses explicit block names A and J to keep these steps separate.
- **Additional finite choice made explicit:** PDF 30 / printed 862
  chooses Q2 by maximum triangle contacts alone. PDF 33 / printed 865
  then concludes that a seven-contact x1+x3 row sum entails at least
  ten triangle contacts. When another qualifying block has row sum
  eight and nine triangle contacts, the tie needs resolution. The
  adaptation also maximizes x1+x3 contacts among equal triangle totals.
  This is a legitimate finite choice inside the fixed chain.
- **Confirmed in the rendered PDF and repaired in 4.13:** PDF 35 /
  printed 867 pairs the triangle [z1,d1,d4] with [z2,d2,c4,d4].
  Those sets overlap at d4 and omit d3. In the preceding row pattern,
  the required disjoint five-edge quadrilateral is [z2,d2,c4,d3].
  This corrected set is used explicitly in `lem:wang-final-full-row-pattern`.
- **Changed-center hypothesis repaired by an explicit variant:** PDF 34 invokes
  4.11 with either the original paw or the paw centered at x2. In
  the loss case of (28), the distinguished z1,z2 need not meet x2,
  whereas 4.11 assumes both meet its center. The new lemma
  `lem:wang-two-vertex-core-five` drops these adjacency assumptions
  under the smaller two-row bound five. Its proof keeps the possible
  z2–d4 contact and uses 11+6+3+3=23 for the path's inside sum.
  Pattern (28) is labeled with both neighbors of x2 in the complementary
  block when x2 has two; a losing complement thus leaves exactly one,
  so the changed-center two-row sum is 1+4=5. All 736,512 inside
  variants and 108,504 final factors pass the research check. This
  explicitly proved variant must be used in 4.13's loss case, not
  the original 4.11 with unmet center hypotheses.
  The further lemma `lem:wang-two-vertex-core-complete` handles two
  center neighbors as well, using another center neighbor's missing
  low-vertex edge. This is essential for the final alternate pair:
  the initially optional pattern-(28) label refinement cannot be
  imposed again without changing that pair. Its 132 inputs and
  4,356 final factors pass the research check; pass 338 compiles
  207 pages cleanly and pages 180–181 were checked.
- **Confirmed in the rendered PDF:** the end of Claim 2.5 (PDF 36)
  prints e(b1b2,d2d3d4)=3 after applying Lemma 3.3. That lemma gives
  **6**, which supplies the complete rows used by the following exchange.
- **Confirmed in the rendered PDF:** Lemma 4.14's alternative hypothesis
  says y⇒(Qr,z), with z∈Qi and i!=r. Its proof replaces z in Qi, so use
  y⇒(Qi,z). The same proof later has an undefined c4 in a degree estimate;
  there the transferred vertex is z.
- **Confirmed and repaired by an explicit proof:** Lemma 4.15 prints e(x0,Qi)>=3
  next to e(T,Qi)>=11. For a feasible chain this is incompatible with
  Claim 2.2. The likely intended index is Q1. Better, its displayed proof
  uses only the already assumed x0⇒(Q1,z), not the degree hypothesis.
  The new `lem:wang-dense-pair-obstruction` proves the nonvacuous version
  with no leaf-degree premise. Its universal quantifier over further
  heavy blocks is explicit before either block is chosen.
- **Counting scope clarified in Claim 2.6:** PDF 40 defines attachment
  as any degree-one row, then uses (40) for a T1 attachment and (41)
  for a Z2 attachment without supplying the other cases. The adapted
  proof counts only the sparse side specified by the block's type.
  Its avoidance, uniqueness, and equality lemmas concern precisely
  these contacts. This is sufficient for the bound 20 per other side;
  no assertion about degree-one rows on a dense side is assumed.
- **Confirmed in the rendered PDF and corrected:** Property 4 of
  Claim 2.6 (PDF 42) displays two quadrilaterals on eight vertices
  followed by a count of three. The adaptation uses the two displayed
  cycles and explicitly checks their complements. The later s3 class
  is taken from H2, the same further-block family as s1 and s2, not H1.
- **Final triangle case made explicit:** the Claim 2.7 table handles all
  four possible locations of the distinguished neighbor in each of
  the twelve core patterns, with no implicit interchange of b and c.
  In a remaining triangle containing both the old center and that
  neighbor, a possible edge rY immediately gives a factor. Only after
  excluding it is Y treated as having one noncentral triangle neighbor
  for the corrected 4.14 application.

## Mathematical completion and new research checks

The complete TeX source route ends in `thm:erdos577-mathematical`
(Proposition 9.82 in pass 359), with the exact final contradiction
8*k <= 6+8*(k-1) = 8*k-2. There are no remaining source claims in that
route. The earlier alternative reconstruction is preserved but is not
needed by this final route. The Leanization plan includes an acyclic
module order and inspected Mathlib 4.33.0 interfaces.

All four scripts below pass with default computational settings and are
research checks only, not proof oracles or kernel-certified results:

| Script | Verified constructions |
| --- | --- |
| `check_wang_twelve.py` | Two first-block patterns; 212 heavy rows, 320 factor lifts, 26 dense labelings, 416 forbidden core contacts, 7,488 pair completions, 104 final factors |
| `check_wang_final_preparations.py` | 204 two-leaf inputs: 52 dense outcomes, 120 factors, 32 new-chain violations; 455 core four-sets; 7,488 pair completions and 208 final factors; 104 full-leaf and 19,968 three-leaf inside estimates |
| `check_wang_full_leaf.py` | 2,340 core complements, 488 replacement lifts, 416 neighbor patterns, 1,821 adjacent-pair gains, 1,768 inside matchings, 65 changed-core exchanges, 76 final increases; 44,521 dense-side factors, 6,175 triangle-side factors; 51,759 final 8/4 cases split into 51,363 forbidden insertions and 396 factors |
| `check_wang_triple_leaf.py` | All 72 labeled ten-contact cores; 48 witnesses (34 U, 5 V, 9 remaining triangles); 22,464 pair completions, 312 common-triple factors, nine remaining triangle factors and inside bounds; 149 low-paw rows, 184 factors, 88 full-leaf exposures, 26 changed chains, 676 final factors |

The four scripts pass `python3 -m py_compile`. Their JSON outputs are
saved in `tmp/erdos577/validation/wang-{twelve,final-preparations,full-leaf,triple-leaf}.json`.
Pass 359 compiles the 230-page document without warnings or overfull/underfull
boxes. The new mathematical proof pages 197–212 were visually checked
from pass 357; later edits only reformatted the implementation-interface list.

The exact theorem remains **unformalized** in this repository. No successful
Lean main build or final axiom audit is claimed.

## Lean preliminary checkpoint — 2026-08-27

All four conclusions of Wang 3.1 now have explicit symbolic Lean proofs in
`AlmostComplete.lean`. The seven-vertex graph is complete or becomes complete
after one missing cross edge is added. Paths or triangles are selected to
remove an endpoint of that possible missing edge. The labeling construction
puts the exceptional four-clique vertex first or last according to whether
the missing triangle endpoint is the distinguished triangle vertex.

Wang 3.2 is now proved for every actual feasible chain in `DenseOutside.lean`.
Its independent finite proof retains the triangle, the old cycle, its exact
diagonal mask, and all sixteen cross bits. There are 3,289 masks satisfying
the two-contact and nine-contact hypotheses in each diagonal case. The
148/80/80/72 minimal witnesses are actual factors or strictly larger block
edge counts, not attachment improvements. All four coverage and witness
modules pass kernel checking; exact row-count identities and graph copies
then give the original-graph result. The proof uses only the first maximizing
condition of feasibility. No desired source theorem is assumed.

The checkpoint also proves ordered paws from strong chains, actual cyclic
vertex replacements, complete-core obstructions, and arbitrary selected-block
splicing with both score inequalities and global factor lifting.
`lake build ErdosProblems.Erdos577.Verification` and the direct Lean check pass
under the approved Lean 4.33.0 runtime. The 60-result intermediate axiom audit
uses only `propext`, `Classical.choice`, and `Quot.sound`; 55 task Lean files
pass the forbidden-placeholder, computational-option, native-evaluation, and
acyclic-import scans. See `validation/lean-preliminaries-{build,axioms}.txt`
and `validation/lean-preliminaries-audit.json` under `tmp/erdos577/`.

The main theorem and later source claims remain pending. Pass 363 of the
231-page TeX compiles cleanly; its updated Leanization pages 213–215 were
visually checked. This is an intermediate proof checkpoint, not completion.

## Paw preliminary checkpoint — 2026-08-27

Wang 3.4(a) now has a complete Lean proof in `PawEleven`. All 6,872
qualifying cross-edge masks are covered by 36 explicit factor witnesses
or four exact exceptional masks. The latter are proved to be precisely
cyclic rotations of the source's rows. `PawEncoding` proves actual
adjacency/count identities and an injective graph copy; `CycleLabels`
preserves the quadrilateral's support under the chosen rotation. The
theorem has no hidden feasibility or induced-cycle assumption.

Wang 3.4(b) is also proved in `PawNine`. The eleven-contact theorem first
forces leaf degree one and triangle count nine in a hypothetical local
nonfactor. Actual universal replacement forces a row of degree at least
three meeting every old internal degree-two vertex. These two necessary
conditions are independently proved from the internal degree bound for
quadrilaterals. The diagonal mask identifies the degree-two columns.
The three nonzero diagonal cases have 60/60/84 factor witnesses and
848/848/880 qualifying masks. All witness and coverage proofs pass, as
do the count/adjacency transport and final actual-graph factor theorem.
`PawClique` derives the zero-terminal-contact conclusion for a complete
block with nine triangle contacts in a strong chain.

An implementation issue in the single-edge graph's default decision
instance was resolved using `decidable_of_iff` and a proved equivalence,
as prescribed by Lean's own `Init/PropLemmas.lean`. Rewriting a `Decidable`
type across `propext` prevented kernel reduction. The graph did not
change, and no axiom, native evaluation, or computational-limit increase
was introduced. Parentheses make the Boolean coverage disjunction
explicit; generated long lines were reformatted without linter options.

`LocalAssembly`, `LocalScoreBounds`, and `ScoredExchange` prove exact
score transfers from an explicit local triangle conversion. They do not
assume the still-pending strengthened path-exchange theorem.

The combined checkpoint builds 77 supporting proof modules plus the audit.
All 83 audited results use only the three standard foundational axioms;
all 78 task Lean files pass the source and import scans. Exact outputs
are `validation/lean-paw-preliminaries-{build,axioms}.txt` and
`validation/lean-paw-preliminaries-audit.json`. TeX pass 365 is 232 pages,
compiles without warnings or box issues, and pages 214–216 were visually
checked. The exact main theorem and remaining source claims are pending.

## Bounded-loss path checkpoint — 2026-08-27

`PathLoss` now proves the strengthened local exchange and the global
path-remainder score bound. The local threshold is exactly
min(edgeCount of the old block,5). The zero-diagonal case reuses the
original path theorem; the other cases have 200/200/152 positive witnesses
covering all 26,333 cross masks with at least nine contacts. Their
coverage/witness build times were 143s/23s, 149s/22s, and 137s/18s.
`PathLossTransport` reuses the path labeling and retains the actual old
diagonals. Both induced-edge scores and the complete-block tie are
transported by proved additive identities. The global theorem has the
exact degree and cardinality hypotheses and assumes only feasibility,
not a further path maximum. The empty-block-family contradiction is included.

The combined build has 91 proof modules plus `Verification`; 93 results
pass the standard-axiom-only audit. Its 92-file source scan passes, with
the main theorem still absent. Exact outputs are
`validation/lean-path-score-{build,axioms}.txt` and
`validation/lean-path-score-audit.json`. TeX pass 367 is 232 pages and
compiles without warnings or box issues; pages 7–8, 212, and 214–215 were
visually checked. The final exact mathematical theorem remains on page 212.

The matching input, positive path-reduction transport, general four-remainder
degree count, and arbitrary-remainder splicing also build. The local
matching theorem and its global score bound are the next obligations;
their generated case tables are not assumed results.

## Matching checkpoint — 2026-08-27

The preceding pending matching obligation is now discharged. `MatchingExchange`
proves Wang 3.6 for arbitrary graphs, using 232 explicit positive witnesses:
16 factors, 184 triangle/five-edge reductions, and 32 path/six-edge reductions.
The coverage proof checks all 26,333 qualifying sixteen-bit masks in the
kernel. Coverage and witness modules built in 153s and 23s, respectively.
The exact global `TriangleChain.Feasible.matching_score_bound` uses the
proved general four-remainder count, exact remainder splicing, and the
already certified path-score bound. It needs no additional maximum.

The combined 95-proof-module checkpoint builds (8,801 jobs); its direct
100-result axiom audit contains only `propext`, `Classical.choice`, and
`Quot.sound`. Logs are `validation/lean-matching-{build,axioms}.txt` and
`validation/lean-matching-audit.json`. The common-triple work is subsequent
work, not part of this checkpoint; the main theorem remains unproved.

## Common-triple and terminal-replacement checkpoint — 2026-08-27

`CommonTriple` now proves Wang 3.3 for the actual graph. Its nine-label
model retains only the four source rows (leaf, two noncentral triangle
vertices, outside vertex) and the actual old diagonals. Positive outcomes
are actual common-neighbor replacements or matching-remainder gains. The
four witness counts are 8/8/8/12. Each case has 279 qualifying masks;
all 65,536 conditional inputs are kernel-checked in 256 rows. The residual
conclusion is equality at nine and a common triple in a cyclic rotation,
with the required outside edge to its middle vertex. There is no
center-to-block assumption. Build times were 148s/3s, 150s/3.8s,
147s/3.9s, and 146s/4.2s for coverage/witnesses; final assembly took 3.5s.

`TerminalReplacements` implements part (1) of the source replacement lemma
(Wang 4.1). Its local swap leaves the triangle unchanged and has exact
support and score. Feasibility forces the internal degree three at every
removed vertex with three remaining terminal contacts. This supplies
the diagonal, every replacement at terminal degree at least three, and
the complete-block conclusion at degree four. The dense-row estimates,
their complete-block consequences, and path reversal are also proved.

The combined checkpoint has 113 proof modules plus `Verification` and
builds in 8,819 jobs, predominantly cached. All 119 audited results use only
the standard three foundational axioms. The 114-file placeholder/limit/
native-evaluation scan and acyclic-import check pass. Exact logs are
`validation/lean-common-triple-{build,axioms}.txt` and
`validation/lean-common-triple-audit.json`. TeX pass 368 is 232 pages with
no warnings or box issues; updated pages 214–216 were visually inspected.
The remaining diamond/path/paw classifications and global claims are
Lean obligations. The exact main theorem is still absent and unproved.

## Dense triangle and path-optimality checkpoint — 2026-08-27

`DenseTriangle` completes Wang 4.1(2)–(3). The three noncomplete diagonal
cases use 60/20/20 explicit strict-improvement witnesses. All 1,264 qualifying
sixteen-bit masks per case are covered except the exact diamond rows.
The residual transport proves the old score five, total ten, two distinct
full rows, and the low row's exact agreement with the old diagonal endpoints.
The complete-block branch uses proved row estimates. Thus ten contacts give
two universal replacements and eleven give a complete block and all three.
No no-factor hypothesis or further maximum is needed for these restrictions.
Coverage/witness times were 101s/8.5s, 105s/5.3s, and 101s/5s; final assembly
built in 3.5s.

`PathOptimality` and `PathCliqueReduction` prove that a path partition at
score E*+1 cannot admit a local path improvement or a nondecreasing triangle
conversion. The matching exchange therefore forces every heavy block of
such a partition to be complete. `CliqueLabels` proves the actual arbitrary
cyclic labeling and the exact two-contact replacement criterion. The full
complete-block path classification remains a separate obligation.

The combined checkpoint has 125 proof modules plus `Verification`, with
8,831 build jobs and 132 selected results passing the standard-axiom-only
audit. All 126 Lean files pass the placeholder, computational-limit,
native-evaluation and acyclic-import scans. Logs are
`validation/lean-dense-triangle-{build,axioms}.txt` and
`validation/lean-dense-triangle-audit.json`. TeX pass 369 is 232 pages with
no warnings or box issues; updated pages 215–216 were visually checked.
The exact main theorem and remaining global claims are still unproved in Lean.

## Full path classification checkpoint — 2026-08-27

`PathClassification` proves all of Wang 3.5 in the original graph. Its
finite complete-block model has 132 positive witnesses (factors or triangle/
complete-block conversions) and 220 residual certificates. Each residual
specifies a Boolean path reversal and an injective block permutation, checks
the exact A/B row restrictions, the contact bound ten, and every required
common-column replacement. The actual transport uses exact cross bits and
the proved two-contact replacement criterion, not monotonicity for negative
row restrictions. Positive outcomes transfer by injective graph copies.
The additional five-edge triangle reduction uses the already proved path
exchange. No source local maximum is silently assumed: `PathOptimality`
supplies it from the global bound when needed.

Coverage built in 150s, positive witnesses in 16s, residual certificates
in 10s, and finite assembly in 3.3s. Exact transport took 3.8s; actual
pattern transport and final assembly took 3.4s each. A simplifier issue
was resolved by retaining the relabeled cycle explicitly and using a
restricted simplification list, without any computational option change.

The checkpoint has 133 proof modules plus `Verification`, 8,839 build jobs,
and 140 selected results with only the standard foundational axioms. All
134 Lean files pass the source scans and acyclic-import check. Logs are
`validation/lean-path-classification-{build,axioms}.txt` and
`validation/lean-path-classification-audit.json`. TeX pass 370 is 232 pages,
with no warnings or box issues; pages 215–216 were visually inspected.
The first paw classification and later global claims remain Lean obligations.
The exact main theorem is still absent and unproved.

## Full first paw classification checkpoint — 2026-08-27

`FirstPawClassification` completes source Lemma 4.3, including the
outside-vertex clauses in (3) and (8). The four old diagonal masks use
264/112/112/84 minimal positive witnesses and 0/137/137/74 residual
certificates, with 26,034 qualifying masks per diagonal. Every positive
outcome is an actual factor, strict triangle-score gain, or two-edge gain;
the previously proved global bounds exclude it. The residuals retain exact
positive and negative row and diagonal data, an optional interchange of
noncentral triangle vertices, and a genuine old cyclic order.

The outside clauses use twelve explicit unordered neighbor-pair factors.
`OutsideLabeling` replaces the leaf by an arbitrary outside vertex and
proves the exact eight-vertex support; graph-copy transport uses no edge
from that outside vertex to the triangle. All pair witnesses and transports
compile. A default recursion-depth failure in a flattened 264-element
membership proof was resolved by using nested short groups, without
changing any computational limit.

The combined build passes with 160 proof modules plus `Verification`
(8,866 jobs). All 156 audited results use only `propext`, `Classical.choice`,
and `Quot.sound`. The 161-file source and acyclic-import scans pass.
Exact logs are `validation/lean-first-paw-{build,axioms}.txt` and
`validation/lean-first-paw-audit.json`. The weighted classification and
later global claims remain Lean obligations; the main theorem is unproved.

TeX pass 372 compiles to 232 pages without warnings or box issues; the
updated first-paw plan pages 215–216 were visually checked.

## Initial weighted classification and path transfers — 2026-08-27

`WeightedPawClassification` proves the complete initial stage of Wang 4.4,
including all twelve alternatives (9)–(20). It reuses the certified first-paw
positive witnesses, without assuming the later six exclusions. Each diagonal
case has 25,232 qualifying masks and 52/124/124/42 exact residual certificates.
The center row is unrestricted. The old cycle order and both positive and
negative row/diagonal conditions are transported exactly.

The universal replacements in (10)–(12) use the proved complete-block and
nonneighbor-degree criteria. `TripleReplacements` verifies the six outside
neighbor pairs; `PawCommonFactor` proves the complementary cycle and exact
set partition. Thus the outside factor needs no additional paw adjacency.
All clauses and the actual feasible-chain theorem build.

`PathTransfer` proves exact gain one, the upper path score, all three local
prohibitions beside every unchanged block, and the full path classification
there. `PathCommonAlternatives` proves the two common-replacement alternatives
for either path orientation. `OutsideCoreCount` proves the exact incidence
split and the four/five-row heavy-block deductions, including empty outside
families. `PawInduced` and `PawSplitFactors` prove further explicit local
prerequisites. The global weighted exclusions themselves remain pending.

Coverage times were 197s/196s/200s/205s; residual checks were
5.5s/8.2s/8.2s/4.9s. The combined build has 187 proof modules plus Verification
(8,893 jobs). The direct 184-result audit uses only the standard three axioms;
all 188 task Lean files pass the placeholder, limit, native-evaluation, and
acyclic-import scans. Exact logs are `validation/lean-weighted-paw-{build,axioms}.txt`
and `validation/lean-weighted-paw-audit.json`. TeX pass373 produces233pages
without warnings or box issues; pages215–217 were visually checked.

The first assembled check encountered a full project filesystem (error28).
With explicit tool approval, only this task’s generated IR directory was
relocated to `/root/.cache/erdos577-01a03c40-lean-ir`; its original path is a
symlink. All559 files (1,170,254,429bytes) were SHA-256 verified before deleting
the originals and again through the symlink. No sources, other tasks, quotas,
or computational settings changed. The repeated build and direct audit pass.
Evidence: `validation/weighted-paw-disk-full.txt` and `validation/lean-ir-relocation.txt`.
The exact main theorem remains absent and unproved in Lean.

## Global adjacent-leaf exclusions — 2026-08-27

`WeightedAdjacentExcluded` completes `lem:wang-exclude-eighteen-twenty`.
The two center noncontacts follow from explicit factors. The missing-edge
implication is checked for all pairs in each of two maximal local graphs;
`UpperCounts` transfers the actual contact upper bound through the injective
labeling. This is an upper adjacency implication, not an incorrect use of
positive copy monotonicity. The path and complementary complete block have
exact supports and a proved strict gain. The heavy-block count includes the
empty-family contradiction. Both final factors are explicit: one in the
original chain, the other after a concrete local paw/block exchange. No
additional feasibility or maximum is assumed for that alternate chain.

The combined194-proof-module checkpoint builds in8900jobs; its direct
198-result audit has only the three standard axioms. All195 checkpoint
files pass the forbidden-placeholder, computational-limit, native-evaluation,
and acyclic-import scans. Exact outputs are
`validation/lean-weighted-adjacent-{build,axioms}.txt` and
`validation/lean-weighted-adjacent-audit.json`. The subsequently added
`PawIndexedFactors` also builds and the current196-file source scan passes.
TeX pass374 is233pages without warnings or box issues. Updated pages216–217
were visually checked; unchanged page215 was checked in pass373.
Patterns16/17,15,19 and all later global claims remain Lean obligations.
The exact main theorem remains absent and unproved.

## Opposite-leaf preparation — 2026-08-27

`WeightedOppositePreparation` proves the local data and global preparation
for (16)/(17): both center noncontacts; the actual five-row bound nineteen
via two upper graphs and exact missing-edge implications; the exposed path
and its complementary one-edge gain even when the old block is chordless;
the heavy outside-block inequality; and a terminal exposure preserving the
block edge count and both feasibility scores. The exposed terminal’s universal
replacement follows from the already proved feasibility theorem.

`CommonReplacementAlternatives` proves the included-row clique dichotomy
and a replacement within any three prescribed contacts, with the latter’s
small index choice checked in the kernel. `PathRowCounts` proves pattern B’s
reversal invariance, row bounds, and exact nine-contact equality when the
first middle row has at most two contacts. The global exclusions of (16)/(17)
are still pending; these helpers do not silently assume them.

The combined checkpoint has 203 proof modules plus Verification, 8,909 build
jobs, and 217 selected results using only the three standard axioms. All 204
files pass placeholder, computational-limit, native-evaluation, and acyclic
import scans. Exact outputs are `validation/lean-weighted-opposite-preparation-`
`{build,axioms}.txt` and `validation/lean-weighted-opposite-preparation-audit.json`.
TeX pass 375 is 233 pages without warnings or box issues; updated pages
216–217 were visually checked. The exact main theorem remains unproved.

## Complete global exclusions (16)/(17), 2026-08-27

`WeightedOppositeExcluded` proves both global exclusions with the original
cardinality, minimum-degree, feasibility, and no-packing hypotheses. No
later source claim is used. `LocalPathPartition.common_partition` turns a
common-neighbor replacement into an explicit partition by three ordinary
quadrilaterals. The ten finite instances use only the graph with diagonal
mask0 and cross mask15621, whose rows are5,0,13,3. Their paths, quadrilaterals,
disjointness, and exact covers are kernel checked. `PawPartialCopy` proves
that these positive edges embed into every actual pattern16/17 instance.

The high branch in `WeightedOppositeHigh` uses both path orientations.
An interface gap in the original path classification was closed explicitly:
`PathMiddleReplacements.common_for_middle` proves the common-replacement
property for either specified middle row of degree3, not only for an
existentially selected row. Pairwise row-union bounds give the common
neighbor; the complete-block criterion gives the replacement. The full
middle row contains the other middle row by equality in the cardinality
of the three-column set. The strengthened assertion and its proof are
also present in the TeX path lemma.

The low branch proves the five forbidden pairs, then a per-column bound
of one plus the indicator of a common leaf/center neighbor. Summation and
the eleven-contact heavy inequality force at least three common neighbors
also adjacent to the exposed old vertex. The earlier three-contact
replacement lemma and the tenth explicit partition finish the factor.

Validation: 210 proof modules plus Verification; build8916jobs; direct
Lean check; 238 selected axiom reports, all using only propext,
Classical.choice, Quot.sound. The 211-file source scan has no forbidden
declarations/options/evaluation and acyclic imports. TeX pass377 has233
pages, no warnings or box issues; changed pages143,216,217 were visually
checked. Logs: `validation/lean-weighted-opposite-excluded-{build,axioms}.txt`
and `validation/lean-weighted-opposite-excluded-audit.json`.
The main theorem is absent and explicitly excluded from this audit.

## Complete global exclusion (19), 2026-08-27

`WeightedNineteenExcluded` completes the global exclusion with the original
graph and cardinality/degree hypotheses. Three center contacts give explicit
two-cycle factors; the last gives a five-edge local improvement over the
old chordless block. The two absent leaf edges and exact row data then
identify the induced core with `PawModel.graph 0 38659`, rows3,0,7,9.
All 64 adjacency implications are explicitly proved; the positive copy gives
the converse. `ExactCopyCounts` transfers exact induced counts from this core.

The two ordered paths are [7,3,1,0] and [6,5,0,1], each with inside sum13
and a five-edge complementary quadrilateral. The paired averaging lemma
counts both copies of the overlapping vertices and handles an empty outside
family. Seven kernel-checked local path partitions supply the insertion
prohibitions. `WeightedNineteenSwap` constructs the alternate paw, block,
and chain explicitly, proves score equality, and verifies exchanged path
supports and retention of every untouched block. No automorphism of the
whole graph is assumed.

`PathSevenInsertions` proves the paired outside bound16 for A and B.
The A case uses degree-sum obstructions and a common neighbor; reversed A
violates the first insertion. In B, a full leaf and two full middle rows
would violate that insertion. Equality in the row bounds gives total9 and
a full first endpoint. Common-neighbor replacements bound the two extra
rows. The shorter single-noncontact argument used in Lean is stated and
proved alongside the original outside-two-set argument in the TeX.
Both presentations now contradict the heavy total17.

Validation: 220 proof modules plus Verification; build8926jobs; direct
Lean check; 272 selected results using only propext, Classical.choice,
Quot.sound; clean221-file source scan and acyclic imports. TeX pass379
produces234pages without warnings or box issues. Pages155,212,216–218
were visually checked; the strengthened path proof pages143–145 were
checked in pass377. Logs are `validation/lean-weighted-nineteen-excluded-`
`{build,axioms}.txt` and the corresponding audit.json. The exact main
theorem is still absent and is not part of this intermediate audit.

## Pattern15 preparation, L4 bounds, and third-path orientation, 2026-08-27

`PawDiagonalCopy` proves monotonicity in the old diagonal mask and a partial
cross-edge copy retaining its specified diagonals. Pattern15 uses positive
core `PawModel.graph 1 28417` and upper core `PawModel.graph 1 28481`.
The upper core retains the optional center–column2 edge. The other three
center contacts give two explicit factors or a six-edge block improvement
over the old diamond. All64 upper adjacency implications are proved.

`WeightedFifteenPaths` certifies L3=[7,4,0,1] and L4=[5,3,1,0], their
complete complements, strict gain1, inside sums≤14, and paired averaging.
`WeightedFifteenFactors` certifies and transports all ten local path
partitions; no optional edge is needed for any insertion witness.
`PathFifteenFourth` and `WeightedFifteenFourth` prove every uniform bound
in source Lemma9.20 of the TeX. The A argument uses equivalent linear
degree-sum inequalities; B uses the full middle/end rows and center degree2.
The paired heavy block therefore has L3≥9, L4≤8, and total≥17.

`PathFifteenThird` proves the third path's B case has paired total≤16;
its forward A orientation violates insertion9. The global theorem
`WeightedFifteen.third_patternA` returns only reverse A, with the complete
block, count≤10, and common-replacement assertions retained. The remaining
reverse-A forced configuration and final sixteen-vertex contradiction are
not yet Lean theorems. Exact next steps and both twelve-vertex cycles are
in `tmp/erdos577/weighted-fifteen-implementation-plan.md`.

Combined checkpoint: 229 proof modules plus Verification; build8935jobs;
direct Lean check; 298 standard-axiom-only reports; clean source/options
scan with acyclic imports. TeX pass383 is234pages without warnings or box
issues; changed pages216–218 were visually checked. Logs are
`validation/lean-weighted-fifteen-third-{build,axioms}.txt` and the matching
audit.json. The 227-module/295-result fourth-path checkpoint is also retained.
The exact main theorem remains absent and outside these intermediate audits.

## Complete pattern15 exclusion and final weighted classification, 2026-08-27

`WeightedFifteenDense` completes the remaining reverse-A case. At center
degree2, the paired heavy count contradicts the two empty extra rows.
At center degree3, any extra contact is in the fourth column; two explicit
twelve-vertex partitions exclude it. The paired equality then forces the
leaf row4, center/oldq0 rows3, and the three zero rows. Every factor is a
partition by actual four-cycles, with extra chords allowed.

`WeightedFifteenDenseModel` has32 compulsory edges. Its upper graph adds
the optional old center–oldq2 edge and all8 unspecified b/oldq2 contacts
to the new block. The copy maps every compulsory edge; all144 actual
upper-adjacency implications are explicit. The six specified row bounds
are4,4,7,6,3,8, summing to32. Thus an upper estimate is never inferred from
positive-copy monotonicity. `OutsideSelectedCount` proves the third block
has≥13 contacts, including the empty-outside contradiction.

`SelectedChainExchange` preserves both optimization scores for an arbitrary
selected block family and retains the explicitly chosen terminal.
`WeightedFifteenDenseTerminals` proves both local constructions have total
edge score11 and one complete block, exposes h or w, and retains every
outside block. The terminal replacement theorem therefore applies to the
one with at least3 contacts. No third-score assumption is introduced.

`WeightedFifteenDenseTables` checks all14 path-and-two-cycle rows, and
all10 triples for each five-element endpoint set. A single broad finite
coverage decision exceeded the default recursion depth; the proof was
split into explicitly enumerated subsets instead. No limit changed.
`WeightedFifteenFinalFactors` transports the rows through the actual copy,
closes the chosen path with the four-contact column, and joins the two
complementary cycles with the replacement block. `WeightedFifteenExcluded`
extends this local factor by all unselected blocks and contradicts the
original no-packing hypothesis. The exact global exclusion is now proved.

`WeightedPawFinalClassification` combines the original twelve-pattern
classification with all six proved exclusions15–20. The final conclusion
is exactly9–14, with every replacement and outside-factor clause in10–12.
This completes source Lemma4.4, without assuming later source claims.

Combined validation:242 proof modules plus Verification;8948 build jobs;
independent direct Lean check;327 selected results, all using only
`propext`, `Classical.choice`, `Quot.sound`; clean243-file source scan with
acyclic imports. Logs are `validation/lean-weighted-paw-final-{build,axioms}.txt`
and `validation/lean-weighted-paw-final-audit.json`. TeX pass385 is234pages
without warnings or box issues; updated pages216–218 were visually checked.
The main theorem remains absent and unproved. The next formal obligations
begin with source Lemma4.5, excluding pattern14.

## Pattern14 heavy-block preparation, 2026-08-27

`WeightedFourteenPreparation` proves all numerical conclusions of TeX
Lemma9.24 (`wang-fourteen-heavy`). The positive core is
`PawModel.graph 0 23813`, rows5,0,13,5. Both forbidden center contacts
give explicit two-cycle factors. The upper core `PawModel.graph 1 23893`
retains the optional first diagonal and both remaining center contacts.
All64 upper-adjacency implications are proved; the actual weighted inside
bound27 transfers through the injective labeling. Two overlapping four-sets
represent precisely the weight2,2,1,1,1,1, so the existing paired averaging
lemma supplies an outside block with weight≥17, including the empty-family
contradiction.

`PawTerminalExchange` presents any given paw as the same remainder and
preserves both scores; the no-packing hypothesis proves it is strong.
Its generic leaf exchange underlies three explicit terminal presentations
in `WeightedFourteenTerminals`. Their edge counts are equal to the old
block's, the original triangle is retained, and all outside blocks remain.
A high terminal is universally replaceable, and every outside column then
has at most one neighbor in the triangle.

All12 `WeightedFourteenFactors` rows are explicit `LocalPathPartition`
witnesses. `WeightedFourteenHighLow` excludes pair sums5 and6.
`PawColumnCount` proves the triangle/leaf count and a replacement among
three prescribed candidates from only two contacts in a complete block.
These exclude pair sum7 in `WeightedFourteenHighRows`. The remaining
full rows force a complete block, empty third-terminal row, and a center
contact. `WeightedFourteenFullGain` constructs a two-block partition with
a triangle remainder and first-score gain1. Exact finite supports and the
two actual edge counts are proved; selected-block feasibility contradicts
the gain. Thus every terminal row is≤2.

Dense-triangle bounds exclude the two zero leaf rows.
`FirstPawLeafCount` proves that a one-contact leaf has at most9 total
contacts in every first-classification pattern. Applying this after the
positive-leaf and nine-contact hypotheses have been proved forces both
principal rows to equal2. The third row lies in1–2, both paw totals are≥9,
and if the original total is9 the third row equals2.
`WeightedFourteenAlternatePaw` is the actual paw[7,2,1,3], with the same
triangle, and gives a strong feasible chain keeping all outside blocks.

Validation:256 proof modules plus Verification;8962 successful build jobs;
independent direct Lean check;356 reports using only `propext`,
`Classical.choice`, `Quot.sound`; clean257-file scan and acyclic imports.
Logs are `validation/lean-weighted-fourteen-preparation-{build,axioms}.txt`
and the corresponding audit.json. TeX pass386 is234pages without warnings
or box issues; changed plan pages216–219 were visually checked.
No computational setting, source outside the task, staging, or commit changed.
The forced configuration and global exclusion of14 are still pending;
the exact main theorem remains absent and unproved.

## Lean checkpoint — pattern14 forced-block filters and columns

Eight further proof modules implement the next part of TeX Lemma9.25.
`WeightedPawLeafTwo` selects14 from the proved six-pattern weighted
classification. `FirstPawLeafTwo` removes3/7/8, bounds the center in5,
and proves the center has at least3 contacts in6. `RowSaturation` proves
equality of actual and allowed row filters from inclusion and cardinality.
`PawCenterTwo` gives exact rows[5,5,13,5] and total9 for any heavy paw with
leaf2 and center≤2, using the actual global weighted theorem. For case5,
the old five-edge count also proves the sole diagonal after relabeling.
Both paw normalization and unchanged cycle support are explicit.

`WeightedFourteenColumnAvoidance` accepts a supplied replacement, exposes
its removed vertex as terminal, and applies the no-packing triangle bound.
Thus a triangle column with≥2 contacts cannot be replaced; its two low
cycle neighbors cannot both meet any of the three exposed terminals.
`OddEraseTriangles` constructs the two remaining triangles from the first
diagonal and the resulting actual quadrilateral replacements.
`FirstPawSixColumns` proves the exact columns3,1,2,1 and the two possible
matrices[3,13,7,1] and[3,15,5,1] from the second-column bound.
`WeightedFourteenSixPreparation` supplies that bound globally: the q1–v1
edge, center replacement, and FactorTable8 give a factor; once the edge
is absent, q1 itself can replace v1, so the triangle-column bound applies.
This proves total9 and the two matrices without assuming a source lemma.

Validation:264 proof modules plus Verification;8970 successful build jobs;
independent direct Lean exit0;374 ordered axiom reports in each run, using
only `propext`, `Classical.choice`, and `Quot.sound`. The265-file scan has
no violations and acyclic imports. `git diff --check` passes.
Logs are `validation/lean-weighted-fourteen-filtered-{build,axioms}.txt`
and `validation/lean-weighted-fourteen-filtered-audit.json`.
TeX pass387 has235pages,20,554source lines, and no warnings or box issues;
pages216–220 and235 were rendered and visually checked.
No computational settings, other-task sources, staging, or commits changed.
The strict-score step choosing the first case6 matrix, alternate-paw
comparison, remaining case4 analysis, and global exclusion14 are still
unproved in Lean. The exact main theorem remains absent and unproved.

## Lean checkpoint — case6 excluded; full-column score argument

`TriangleHighContact` proves that a two-contact terminal must meet a
complete triangle column when the block has at most5edges. Otherwise,
after ruling out both low contacts by an actual terminal replacement,
the opposite contact and one low contact form a new triangle remainder.
`LocalChain.exists_with_block` constructs the new chain with the complete
block formed from the old triangle and the designated vertex. Its6edges
contradict the existing first-score bound.
`WeightedFourteenSixRows` applies this to the already feasible exposed-q1
chain and uses FactorTable8 to select the exact matrix[3,13,7,1].

`FirstPawRowBounds` supplies the noncentral bounds for4 and6, including
the normalized version. `DiamondLabels` identifies the unique nonneighbor
of row13 and recovers the other low vertex from the internal degrees.
`WeightedFourteenSixAlternate` first-classifies the actual alternate
strong paw. Case4 contradicts the original center's three-contact row;
case5 would force its center to have2 contacts, whereas the actual
center has1 or3. Case6 forces both swaps to be false and its two low
vertices to be the original lows in reverse order. Its leaf therefore
meets the original fourth vertex.
`WeightedFourteenSixExcluded` builds three explicit cycles on the12-label
join, with index sets{7,11,1,2}, {0,8,10,9}, {3,4,5,6}. The exact image
partition and selected-factor theorem give the global contradiction.
Thus only cases4/5 remain at any heavy block of pattern14.

### Correction to the TeX reconstruction's complete-block ordering

The old sentence asserting that a complete block would let a degree2
terminal replace the first high vertex was too early: if that terminal
meets the removed vertex, only one neighbor remains. This was an error in
our reconstruction, not in Wang's argument. The complete source was
rechecked visually at PDF19, printed851. There the inference is inside
the contrary assumption that the terminal misses the high vertex.
The TeX now retains that assumption until the strict-score contradiction
forces the contact. In case4, it then excludes a complete block because
the center has≥3 contacts and can replace any vertex of a complete block,
contradicting FactorTable8. `TriangleHighContactAny` verifies the contact
argument without a score premise and includes the complete-block branch.
The theorem and the remaining proof construction are unchanged.

Validation:271 proof modules plus Verification;8977 successful build jobs;
independent direct Lean exit0;388 matching axiom reports in both runs,
using only `propext`, `Classical.choice`, `Quot.sound`. The272-file source
scan is clean with acyclic imports. `git diff --check` passes.
Logs: `validation/lean-weighted-fourteen-six-excluded-{build,axioms}.txt`
and the corresponding audit.json. TeX pass388 produces235pages with no
warnings or box issues; pages162–163 and217–220 were rendered and checked.
The complete source page19 was also rendered and checked without altering
the supplied PDF. No computational settings, staging, commits, or other
tasks' sources changed. Case4, the joint rows, the final14 exclusion,
later source claims, and the exact main theorem remain unproved in Lean.

## Lean checkpoint — the full forced second block for14

Seven further modules complete TeX Lemma9.25, including its strong
centerdegree2 occurrence. `FirstPawFourColumns` proves the exact leafrow5
and a complete high triangle column in4. Its rotation by2 is an actual
cyclic relabeling preserving the original Pattern4 and block support.
`FirstPawFourExact` converts the forbidden low center pair into centerrow13
or7, then uses total≥9 to force both noncentral rows5 and total9. Reflection
normalizes to13, and the equal noncentral rows permit undoing the paw swap.
`WeightedFourteenFourRows` supplies the global hypotheses in the repaired
order: the exposed q1 meets the complete high column; FactorTable8 forbids
the center replacement; a complete block and two low center contacts
would each allow that replacement. Thus the sole diagonal and exact
matrix[5,13,5,5] are proved in the original paw labeling.

`WeightedFourteenPawRows` combines4/5. `RowSaturationIncluded` proves that
included mask contacts are exact when they exhaust the degree, by equality
of finite filters. `WeightedFourteenJointRows` applies the unrestricted
high-column contact lemma at both highs to both feasible terminal chains,
using a rotation by2 for the second application. Both degree2 rows are
exactly5. This gives every row of the source's six-vertex setR.
`WeightedFourteenCenterTwo` proves the final assertion of9.25. It uses the
actual alternate strong paw in4, and the normalized original paw in5.
The returned chain, paw support, block membership, Pattern14, and exact
center degree are all explicit; no new maximum or extra hypothesis occurs.

The TeX preserves its original finite-maximum argument and now explains
the equivalent direct choice after(14d): use the proved occurrence with
centerdegree2, then apply the forced-block lemma again. The Lean final
exclusion may use this explicit existential witness rather than formalize
another maximum. This does not impose extra optimality on arbitrary chains.

Validation:278 proof modules plus Verification;8984 successful build jobs;
independent direct Lean exit0;404 matching ordered reports with only
`propext`, `Classical.choice`, `Quot.sound`; clean279-file source scan and
acyclic imports. `git diff --check` passes. Logs are
`validation/lean-weighted-fourteen-forced-{build,axioms}.txt` and the audit.json.
TeX pass390 has235pages and20,591source lines, without warnings or box
issues. The new mathematical explanation on pages162–163 was viewed in389;
plan pages217–220 were viewed again in390 after moving an isolated table
header to the next page with its first row. No computational settings,
staging, commits, or other-task sources changed. Lemma9.26's final14
exclusion, the later claims, and the exact main Lean theorem remain unproved.

## Lean checkpoint — pattern14 fully excluded

Nine further modules implement TeX Lemma9.26 and finish Wang Lemma4.5.
`HighPairLeafExchange` proves an actual quadrilateral replacement at either
low vertex and exact induced-edge equality when the opposite diagonal is
absent. Equal edge counts preserve both feasibility scores through the
existing score-transfer theorem. `WeightedFourteenDenseRows` represents the
three possible unique extra triangle contacts without assuming an automorphism.
`WeightedFourteenDenseTerminals` exposes all four specified terminals in actual
feasible chains, retaining the original triangle and every unselected block.

`WeightedFourteenDenseModel` constructs the three positive twelve-vertex copies.
The old center row is only used after it has been proved exact from degree2
and the two forbidden contacts. `WeightedFourteenDenseTable` gives twelve
explicit insertion rows in each of the three graphs. Each row has a three-path
and two complementary four-cycles, with all supports, disjointness, edges,
and endpoint coverage checked by the Lean kernel at unchanged defaults.
The table covers every inserted terminal and unordered pair of other terminals;
reversing endpoint orientation is handled in the transport proof.

`WeightedFourteenDenseUpper` needs only the four terminal rows of an upper graph.
Their degrees are5,4,5,4, for total18. No absence of irrelevant optional edges
is assumed. `WeightedFourteenDenseHeavy` applies selected-family averaging
to the actual degree sum and block cardinality, including the empty-family
case, yielding a third block with≥9 contacts. `WeightedFourteenDenseFactors`
proves the two finite pigeonhole steps: a terminal row≥3, then a column meeting
two other terminals because their remaining sum≥5. Its explicit insertion
factor uses four cycles of exactly four vertices. The selected-factor theorem
retains all other old blocks.

`WeightedFourteenExcluded.excluded_center_two` assembles that contradiction.
`WeightedFourteenExcluded.excluded` selects the already proved actual strong
centerdegree2 occurrence and discharges the extra degree premise. Its final
interface assumes only a feasible chain with the specified paw remainder;
there is no assumed source claim, extra maximizing hypothesis, or oracle.

Validation:287 proof modules plus Verification,8993 successful build jobs,
direct Lean exit0,429 matching ordered axiom reports using only `propext`,
`Classical.choice`, and `Quot.sound`. The288-file scan has no forbidden
declarations, computational options, or native evaluation, and imports are
acyclic. `git diff --check` passes. Exact logs are
`validation/lean-weighted-fourteen-excluded-{build,axioms}.txt` and the audit.json.
TeX pass392 produces235pages and20,606source lines without warnings or box
issues. Updated plan pages217–221 were rendered and checked; a now-unnecessary
forced page break was removed to avoid leaving most of page218 blank.
The mathematical exclusion itself is unchanged from the completed TeX proof.
No staging, commits, computational-limit changes, or other-task edits occurred.
Pattern13 (starting with TeX9.27/source4.6), later global claims, and the exact
main Lean theorem remain unproved. The unbudgeted goal stays active.

## Lean checkpoint — forced second block for pattern13

Seven further modules complete TeX Lemma9.27, the initial forced-block
part of Wang Lemma4.6. This does not yet complete that source lemma or
exclude pattern13. The complete source transcription was rechecked at
PDF19–20, printed851–852; all of TeX9.27–9.30 belongs to source4.6.
The implementation plan's broader source4.6–4.8 heading was corrected:
source4.7 and4.8 concern the subsequent first-paw pattern exclusions.

`WeightedThirteenModel` uses positive mask32001 and upper mask32081,
with raw rows[1,0,13,7] and[1,5,13,7]. Two explicit two-cycle factors
forbid the center's contacts with both old low vertices.
`WeightedThirteenUpper` proves all64 upper adjacency implications;
the generator independently checks the two path-degree lists2,5,5,3.
`WeightedThirteenPaths` proves the exact complementary supports and
edgeCount=newOldCount+1 in both cases, retaining the optional first
diagonal. Each inside path sum≤15; paired averaging gives total≥17,
including an empty outside family. `WeightedThirteenSymmetry` uses
the actual paw swap and cycle reflection, preserving supports and
exchanging the actual paths. It chooses an orientation with L2≥9.

`WeightedThirteenFactors` supplies the eight literal path/complement
witnesses and their actual global insertion prohibitions.
`PathThirteenRows` excludesB by the paired bound16. The first middle
row cannot have degree3; exact_nine gives rows2,2,3,2. An explicit
common column and the complete-block retained-contact criterion bound
the outside low row by1, while another insertion bounds the outside
noncentral row by2. ForwardA is excluded by its CommonA assertion.
In reverseA, the two outer rows lie in three columns and have≥2
contacts, while the middle row has≥3. The complete-block insertion
tests bound the outside pair by4. Equality in the paired threshold
forces both triple rows3 and the middle row4. The last insertion makes
the low outside row0, so the other outside row is4. Exact finite row
saturation identifies the common three columns.

`WeightedThirteenDense.dense_at_heavy` applies the already proved path
transfer, all eight actual insertion restrictions, and the analytical
lemmas. `exists_dense_block` adds the actual simultaneous relabeling.
Both return the complete second block and every one of the six exact
rows. No new maximum, source theorem assumption, or finite-search oracle
is introduced. The interface only needs feasibility of the given chain.

TeX retains the original mathematical proof and adds the short direct
retained-contact argument for the outside low row≤1 used in Lean.
The Leanization plan now maps every component of9.27 to its module.
Validation:294 proof modules plus Verification,9000 successful build
jobs, independent direct Lean exit0,449 matching ordered axiom reports
with only `propext`, `Classical.choice`, `Quot.sound`. The295-file
source scan is clean and imports acyclic; generator syntax and
`git diff --check` pass. Logs are
`validation/lean-weighted-thirteen-dense-{build,axioms}.txt` and audit.json.
TeX pass394 has235pages and20,629source lines with no warnings or box
issues; mathematical pages163–165 and plan pages218–221 were rendered
and checked. No computational settings, staging, commits, or other-task
sources changed. Next is9.28's alternate strong paw, weighted third
block, and thirteen insertion rows. The final main theorem remains absent
and unproved, and the persistent goal remains active.

## Lean checkpoint — pattern13 third-block setup complete

Nine further modules complete TeX Lemma9.28. The complete source argument
on PDF20, printed852, was rechecked; universal replacement and the final
exclusion are still the remaining parts of Wang Lemma4.6.

`WeightedThirteenDenseModel` gives the35-edge positive twelve-vertex copy
and144 actual upper implications. Optional old center contacts, the first
old diagonal, and unspecified contacts from the old highs to the new block
are retained. Inside degrees of leaf,v1,v2,oldq1,oldq3 are bounded by2,9,9,6,3.
The leaf is intentionally counted twice, giving31. `OutsideSelectedPairs`
proves paired selected-family averaging from both exact degree identities;
the two three-sets need not be disjoint. `WeightedThirteenDenseHeavy` uses
the actual cardinalities and minimum degree to force third-block weight≥13,
including the empty outside-family contradiction.

`WeightedThirteenAlternatePaw` constructs a local chain on the paw and the
second block only. The remainder has terminalleaf and triangle{center,v1,v2};
the new block{b,c,v0,v3} is complete. Both old and new block counts are6,
so the existing equal-score transfer preserves both maxima. Presenting
the explicit new paw gives a strong chain retaining every other block.
No additional maximizing choice or selected-two score assumption is used.

`WeightedThirteenDenseTables` gives13 explicit path-and-two-cycle rows.
The kernel checks all edges, supports, disjointness, and complete coverage
of the six endpoint pairs for leaf insertion. `WeightedThirteenDenseFactors`
transports the actual factors and proves that five contacts from the other
four rows, with universal leaf insertion, yield a factor. The global
`WeightedThirteenDenseConsequences` exposes all13 insertion prohibitions
and proves the leaf row≤2 from the weight13. Selected-factor splicing keeps
all unaffected blocks and yields cycles of exactly four vertices.

`SmallLeafWeightedBound` proves the uniform estimate2*leaf+b+c≤8 for a paw
remainder with leaf≤2. Zero leaf and weight<7 are handled explicitly;
otherwise the actual weighted classification leaves9/13, with14 removed
by the fully proved exclusion. `WeightedThirteenThirdSetup` applies this
to the actual alternate strong paw, giving the low-row sum≥5, and combines
it with the third-block existence and leaf bound. The exact TeX9.28
conclusion is proved, not merely its conditional numerical reduction.

Validation:303 proof modules plus Verification;9009 successful build jobs;
independent direct Lean exit0;474 matching ordered axiom reports using only
`propext`, `Classical.choice`, `Quot.sound`. No task lint warnings remain.
The304-file source/option scan and acyclic import check pass. The generator's
syntax check, independent13-row checker, and `git diff --check` pass.
Logs: `validation/lean-weighted-thirteen-setup-{build,axioms}.txt`, audit.json,
and `validation/weighted-thirteen-third-table-independent.json`.
TeX pass395 has235pages and20,656lines without warnings or box issues;
mathematical pages164–166 and plan pages218–221 were rendered and checked.
The uniform small-leaf estimate is now stated and proved explicitly in TeX.
No computational settings, staging, commits, or other-task sources changed.
Next: TeX9.29's universal low-row replacements, including both matching-score
gains and the complete-block tie. The exact main Lean theorem remains absent
and unproved; the full persistent goal stays active.

## Lean checkpoint — pattern13 universal rows complete

`WeightedThirteenUniversal.third_low_universal` now proves TeX9.29, the
universal-replacement portion of source4.6. It applies to either old low
vertex in the actual dense configuration whenever its third-block degree
is at least3 and that block has weighted sum≥13. No new optimum or
unproved source claim is assumed.

`ThreeContactLabels` gives an actual cyclic rotation with exact row7;
degree4 and a present opposite diagonal already imply universality.
`WeightedThirteenLowTerminals` exposes either low vertex when the first
old block is chordless, with equality of both scores. Thus the contrary
branch has the old first diagonal. `ThreeContactScore` proves the exact
one-edge replacement gain, including either value of the other diagonal.
`SelectedMatchingScore` obtains the selected-family bound by actual
splicing into the global matching-remainder bound.

The43-edge sixteen-vertex positive model has explicit actual transport.
The missed-vertex table has four matching remainders for each low choice,
with complementary scores6,6,oldthird+1. The resulting two-edge gain
excludes all four unwanted missed-vertex contacts. The common-neighbor
table has four triangle remainders for each choice. Its new score≥16 and
complete count≥2 contradict the old score≤16 and complete count1, using
both feasibility maxima explicitly. The thirteen-row table handles the
middle column. `ThreeColumnCounts` proves the disjoint-row bound3;
`WeightedThirteenThirdRows` derives the contradictory total≤12.

Combined build and direct check pass:315proof modules plus Verification,
9021build jobs,504matching ordered axiom reports, onlypropext/choice/Quot.
The316-file source scan is clean and imports are acyclic. The main file
is still absent. The independent literal checker verifies8matching cases,
16optional-diagonal score comparisons, and8triangle exchanges, always
with cycle length4. Exact commands are in PROGRESS.md; logs are
`validation/lean-weighted-thirteen-universal-{build,axioms}.txt` and
`validation/lean-weighted-thirteen-universal-audit.json`.
TeX pass396 has236pages and20,672lines, with no warnings or box issues.
Mathematical pages165–166 and plan pages218and221 were rendered and checked.
Only the Leanization plan changed; the mathematical proof was preserved.
No computational limits, staging, commits, or other-task files changed.
Next is TeX9.30, the final exclusion of13. The exact theorem is unproved
and the persistent goal remains active.

## Lean checkpoint — pattern13 excluded; precise small-leaf classification

`WeightedThirteenExcluded` completes TeX9.30 and all of Wang Lemma4.6.
The two original low rows have total at least five. Universal insertion
of the second would make three rows pairwise disjoint and contradict
weight13. Thus that low has degree at most two, and the first is
universal. Its insertion rows give the doubled leaf/new-row interval7–8.
Four extra literal path-and-two-cycle rows supply the remaining factors.
`ReplacementRowTransfer` transports an actual inserted cycle along
neighbor-row inclusion. `ThreeRowReplacement` uses this to give either
the required common insertion or universal replacement of the new row.
The resulting factors exclude leaf degrees zero and one.

`TwoContactLabels` gives an actual rotation/reflection for the degree-two
leaf. The opposite pair yields a common permitted leaf insertion. For
the adjacent pair, `ThreeCrossQuad` proves the mixed quadrilateral from
two adjacent pairs and at least three cross contacts. The actual four
blocks use only the35-edge old core; no optional old first diagonal is
assumed. If that factor is unavailable, the remaining row counts force
both new rows to be the full opposite pair. A universal three-contact row
forces a third-block diagonal, and either diagonal gives the final leaf
insertion. `final_leaf_two_false` covers both cases. `excluded_dense`
and `excluded` apply the already proved dense configuration and third
block setup, without introducing another maximum. The exported theorem
`TriangleChain.Feasible.not_weighted_pattern13` requires only feasibility
and the actual paw remainder, not an additional strong-chain premise.

`SmallLeafClassification` completes TeX9.31. Exclusions13and14 leave
only pattern9 in the positive small heavy case. Undoing the noncentral
normalization preserves that symmetric pattern; the two original
neighbor filters are equal and form an actual three-element subset of
the original block. The general doubled bound≤8 was already proved.

Verification passes:330 proof modules plus Verification,9036 build jobs,
534 matching ordered reports from both build and direct Lean, and only
`propext`, `Classical.choice`, `Quot.sound`. The331-file forbidden/limit
scan is clean and imports are acyclic. The independent final checker
passes4 extra insertion rows,5 mixed cross-contact configurations, and11
leaf-pair geometry checks, all with cycle length exactly four.
Logs: `validation/lean-weighted-thirteen-excluded-{build,axioms}.txt`,
`validation/lean-weighted-thirteen-excluded-audit.json`, and
`validation/weighted-thirteen-final-tables-independent.json`.
TeX pass397 has236pages and20,697lines without warnings or box issues.
Mathematical pages166–167 and plan pages218–219and221–222 were rendered
and checked. The mathematical proof was preserved; only its Leanization
plan changed. No computational limits, staging, commits, or other-task
sources changed. The exact main Lean file remains absent and its theorem
unproved. The persistent goal is active. Next: TeX9.32/source4.7.

## Lean checkpoint — pattern4 excluded; pattern5 also excluded

`FirstPawFourPaths.complementary_path` completes TeX9.32. The actual
contact count is exactly the count of the ten allowed entries. Its lower
bound9 leaves at most one absent entry; the selected positive core also
covers a graph with all ten entries present. Ten18-edge cores carry180
literal path partitions, with full coverage of three terminals and six
unordered endpoint pairs per terminal. Endpoint reversal handles both
orders. Copy transport proves the exact original support and four-cycle
complement. The actual chain's no-factor hypothesis excludes every
resulting common insertion, retaining all other blocks.

`FirstPawFourExcluded` completes TeX9.33. The full upper graph includes
the optional low diagonal and gives repeated-leaf inside weight22.
The exact outside average produces a block of weight≥13, also treating
an empty outside family by contradiction. A finite incidence pigeonhole
and feasible-terminal replacement bound the leaf row by2 and the five
rows by≥11. Twenty explicit local chains expose either low terminal
with block score5. The first feasibility maximum forces equality of
the actual score; the complete-block score is consequently unchanged.
Each low row is≤2, contradicting the doubled small-leaf bound8.

For the complete old block, ten explicit exchanges interchange the
noncentral pairs. The chosen high is met by the leaf and the other
high meets all three triangle vertices; this choice covers a one-contact
leaf as well as a two-contact leaf. The new block is complete. Both
scores, all original outside blocks, and the actual weighted rows are
preserved. The new paw's positive edges, center degree≥3, noncentral
noncontacts, and cross total≥9 are all proved. The noncontacts are
checked against the full upper graph, not inferred from a positive copy.
The two three-row sums add to≥13; one is≥7. `SmallLeafCommon` and
`ThreeSetReplacement` turn the common three-set into a forbidden
insertion. No additional maximizing assumption is introduced.

`FirstPawFiveExcluded` proves the pattern5 half of TeX9.34 by the
common three-set and the allowed two-element intersection. Pattern7
is still required before counting9.34 or claiming all of source4.7.
The nine-contact hypothesis is explicit in both4/5 exclusions: it is
not part of the row-only `Pattern4` or `Pattern5` definitions.

Combined build and direct Lean check pass with349proof modules plus
Verification,9055build jobs, and585ordered axiom reports. Every report
uses only `propext`, `Classical.choice`, and `Quot.sound`. The350-file
forbidden/limit scan is clean, imports are acyclic, and the exact main
file is still absent. Independent checks cover180path witnesses,
20terminal exchanges, and10complete swaps with exact four-cycles.
Logs: `validation/lean-first-paw-four-excluded-{build,axioms}.txt`,
`validation/lean-first-paw-four-excluded-audit.json`, and
`validation/first-paw-four-{pairs,exchanges}-independent.json`.
TeX pass399 has237pages and20,730lines without warnings or box issues;
mathematical pages167–169 and plan pages219and222–223 were rendered
and checked. Only the Leanization plan changed. Computational limits,
staging, commits, and other tasks' files were untouched. The checkpoint
is33of82numbered milestones, not an estimate of remaining effort.
Next is pattern7, then source4.8/pattern6. The exact theorem is unproved
and the persistent goal remains active.

## Lean checkpoint — pattern7 excluded; Wang4.7 complete

The nine `FirstPawSeven` modules complete TeX9.34 and the remaining
pattern7 case of source4.7. Pattern4 and pattern5 were already excluded.
The exact positive core is `PawModel.graph 1 22385`, with18edges and
cross rows[1,7,7,5], totaling9contacts. Independent checking corrected
our earlier planning note that had incorrectly counted10; the source
proof and Lean matrix were unchanged. All64 actual upper adjacency
implications are proved, using the already established absence of
extra leaf–triangle edges. The four distinguished inside degrees
are2,2,4,5, giving bound13 and an outside block with≥9contacts.

The alternate paw is[7,6,5,2] and its replacement block is[0,1,3,4].
Its positive block has5edges, and the first feasibility maximum
forces the actual score tie; the complete-block score is consequently
unchanged. The original leaf and old low vertex7 are both feasible
terminals. All original outside blocks are retained. Six explicit
path partitions cover all three endpoint pairs for each terminal,
in either order, and force both outside terminal rows≤2.

`FirstPawSevenTriple` supplies every hypothesis of `Paw.common_triple`.
The original leaf is outside both the alternate paw and the heavy
block. The third original insertion test supplies the no-replacement
premise; the alternate chain's proved matching bound supplies the
no-two-edge-gain premise. The positive small-leaf case comes from
the precise classification; the zero-leaf case uses the two-row sum≥7.
The resulting cyclic labeling makes both noncentral rows meet its
last three vertices and joins the original leaf to its third vertex.
`FirstPawSevenFinalFactor` constructs the actual cycles
[5,9,8,11], [0,1,2,10], [3,4,7,6]. They partition exactly the twelve
selected vertices. `not_first_paw_pattern7` retains all other blocks
in the global contradiction. The combined5-or7 theorem is also proved.

Both combined Lake build and direct Lean check pass:358proof modules
plus Verification,9064jobs,612ordered axiom reports, and only
`propext`, `Classical.choice`, `Quot.sound`. The359-file forbidden/limit
scan is clean and imports are acyclic. The independent literal check
covers the alternate score, all six insertion witnesses, twelve ordered
endpoint cases, and all four outside-diagonal cases of the final factor.
Every cycle has length exactly four. Logs are
`validation/lean-first-paw-seven-excluded-{build,axioms}.txt`,
`validation/lean-first-paw-seven-excluded-audit.json`, and
`validation/first-paw-seven-independent.json`.
TeX pass400 has237pages and20,751lines, with no warnings or box issues.
Mathematical page169 and plan pages219and222–223 were rendered and
checked. Only the Leanization plan changed. There were no limit
increases, staging, commits, or other-task edits. The exact main file
is still absent and its theorem unproved. The goal remains active.
Next is TeX9.35, pattern6/source4.8; the checkpoint is34of82milestones,
not an estimate of remaining effort.

## Lean checkpoint — pattern6 exact reduction and terminal setup

Thirteen new proof modules implement the initial part of TeX9.35.
`PawEdgeCount` proves the exact four-edge count for a paw remainder
without extra leaf edges. `FirstPawSixModel` records the ten allowed
cross contacts and the five critical ones. The essential positive graph
has paw[7,6,2,5] and block[4,0,1,3]; all required positive edges and
the new pattern5 restrictions are proved. The full upper graph retains
all ten possible contacts. `FirstPawSixEssential` constructs an actual
feasible replacement chain when all five critical contacts are present.
Both block scores are5 and both paw scores4, so `edgeCount_union`
preserves the cross-contact count≥9. The proved pattern5 exclusion
therefore gives the required missing critical contact.

The exact ten-entry contact count leaves at most one missing contact.
`FirstPawSixCases` derives precisely source rows22–26, with masks
6115,2035,5619,5107,6130. `FirstPawSixCaseModel` and
`FirstPawSixCaseUpper` prove actual positive and exact adjacency transport.
Both directions, including every nonedge, are used in the two
normalizations25→24 and26→23. These normalizations preserve both scores
and retain every outside block. `reduce_to_three_cases` returns an
actual feasible chain with exact rows22,23,or24; it is a reduction,
not the exclusion of those cases or the main theorem.

`FirstPawSixTerminalModel` certifies six local chains, two in each case.
Their paws are[7,4,0,5] and[3,1,5,0], with blocks[6,1,3,2] and[2,4,7,6].
Both blocks have5edges. `FirstPawSixTerminals.exists_alternate` proves
feasibility of the actual presentations, exact terminal/remainder
identities, and retention of all further blocks. The other exposed
terminal is explicitly outside each alternate paw. The common-triple
contradictions for22/23 and the weighted contradiction for24 remain.
Milestone35 and source4.8 are not yet complete.

Verification passes:371proof modules plus Verification,9077build jobs,
658ordered axiom reports from both combined build and direct Lean,
and only `propext`, `Classical.choice`, `Quot.sound`. The372-file
forbidden/limit scan is clean and imports are acyclic. Independent
checks cover all1024allowed masks,11dense masks,6essential exchanges,
five exact cases, both normalizations, and all six terminal exchanges.
Logs: `validation/lean-first-paw-six-reduction-{build,axioms}.txt`,
`validation/lean-first-paw-six-reduction-audit.json`, and
`validation/first-paw-six-reduction-independent.json`.
TeX pass402 has238pages and20,771lines, without warnings or box issues.
Mathematical page170 and plan pages219and223–224 were rendered and
checked. Only the Leanization plan changed. No limits, staging, commits,
or other-task sources changed. The exact main file remains absent and
its theorem unproved. The goal is active, with34of82milestones complete
and the setup of35 proved. This is not an estimate of remaining effort.

## Lean checkpoint — pattern6 cases22/23 excluded

Eight new modules implement both common-triple contradictions in TeX9.35.
`FirstPawSixSmallModel` uses the exact source22/23 cores and the four-set
R={7,0,5,3}. The inside sums are14and13. Six positive path partitions
in each core cover both terminals and all endpoint pairs among the other
three members ofR. Actual adjacency transport proves each insertion
obstruction in the original chain; no negative edge is inferred from a
positive copy. `IndexedInsertionBound` supplies the general five-contact
pigeonhole argument against universal replacement.

`FirstPawSixSmallRows` applies both already-proved feasible alternate
chains to obtain the two row bounds≤2. `FirstPawSixSmallTriple` applies
the precise small-leaf classification in F1 and then the common-triple
lemma. Its inserted vertex is explicitly outside F1 and the outside
block; the matching-score obstruction is obtained from F1's actual
feasible chain. The no-common-insertion premise comes from the original
chain. `FirstPawSixSmallFinalFactor` constructs the disjoint cycles
[5,9,8,11],[0,1,3,10],[2,4,7,6] on all twelve vertices.
`FirstPawSixSmallExcluded` splices this factor into the original partition
and retains every unselected block, giving both contradictions.

The combined build and direct Lean check pass:379proof modules plus
Verification,9085build jobs,675ordered reports, and only `propext`,
`Classical.choice`, `Quot.sound`. The380-file forbidden/limit scan is
clean and imports are acyclic. Independent checks cover all12 insertion
witnesses,24ordered endpoint cases, and8final factors (both cores and
all four outside diagonal choices). Logs are
`validation/lean-first-paw-six-small-{build,axioms}.txt`,
`validation/lean-first-paw-six-small-audit.json`, and
`validation/first-paw-six-small-independent.json`.

TeX pass403 has238pages and20,781lines, with no warnings or box issues.
Changed plan pages219and223–224 were rendered and visually checked.
The mathematical argument is unchanged. Case24's weighted contradiction
remains; pattern6/source4.8 and milestone35 are not yet complete.
The exact main file remains absent, its theorem unproved, and the goal
active. The verified milestone count stays34of82, not an effort estimate.
No computational limits, staging, commits, or other-task sources changed.

## Lean checkpoint — full pattern6 and final first classification

Ten new proof modules complete TeX9.35and9.36, including all of Wang
Lemma4.8. `FirstPawSixWeightedModel` uses exact case24 rows[3,15,5,1].
`FirstPawSixWeightedHeavy.inside_exact` proves the actual weighted inside
sum20 by exact adjacency transport; the original leaf is counted twice.
The paired average produces an outside block of weight≥13. Eight actual
path partitions certify all six leaf endpoint pairs and both noncentral
insertions. The leaf-degree bound2 follows from its actual terminal chain.

In the large three-row branch, the common triple of the two original
noncentral rows forces cdegree≥3. Its alternate feasible chain supplies
universal replacement; the other two rows have a common neighbor, giving
the forbidden insertion. In the other branch,
`SmallNoncentralClassification` applies the proved weighted classification
and exclusions13/14. It undoes the actual noncentral swap and proves
three common neighbors and the doubled-small-row bound8 in10–12.
Applied to the alternate paw, this forces an original noncentral degree≥3.
Ordinary replacement into the common three-set gives the contradiction,
without assuming that this vertex is a feasible terminal.

`FirstPawSixExcluded` assembles the exact five-case reduction, both
normalizations, and all three final contradictions. Its statement keeps
the explicit original contact threshold≥9. `FirstPawFinalClassification`
then leaves only patterns3/8, exact leafdegree1 and total9. The outside
factors are transported back to the original triangle and block support.
It also proves the positive-leaf bound9, the leafdegree≥2 bound8, and
the unrestricted block bound12, completing TeX Corollary9.36.

Combined build and direct Lean both pass:389proof modules plus
Verification,9095build jobs,695ordered reports, using only `propext`,
`Classical.choice`, `Quot.sound`. The390-file forbidden/limit scan is
clean; imports are acyclic. Independent checks cover weight20,8insertion
witnesses,12ordered leaf pairs,128explicit three-cycle lifts, all4small
noncentral row cases, and both surviving exact first matrices.
Logs:`validation/lean-first-paw-final-{build,axioms}.txt`,
`validation/lean-first-paw-final-audit.json`, and
`validation/first-paw-final-independent.json`.

TeX pass404 has239pages and20,798lines, with no warnings or box issues.
Changed plan pages219–220and223–225 were rendered and checked.
The mathematical proof is unchanged. The verified count is36of82
numbered milestones, not an effort estimate. Next is the seven-vertex
core argument starting at9.37/source4.9. The exact main file remains
absent, its theorem unproved, and the goal active. No limits, staging,
commits, or other-task sources changed.

## Lean checkpoint — core transfer routes and heavy outside-block shape

Ten new proof modules implement the first part of TeX9.37. `TerminalSwap`
proves exact triangle/terminal/block identities and both score equalities
for an ordinary equal-score terminal swap. Its high-pair version reuses
the existing replacement-cycle and score lemmas and does not require
a paw attachment. `CoreTransferRoutes` constructs both direct and bridge
routes. The route record contains actual feasible chains, retained blocks,
and complementary partitions, with no assumed core estimate. In the
bridge, `TwoStageReplacement` proves the exact two-cycle complement.

`CoreTransferConsequences` transfers local and selected-family factor
obstructions to the actual exposed terminal chains. Universal replacement
gives triangle-column and total bounds; dense triangle contacts bound
either exposed low row by1. `CoreTransferCount` proves the six-row set's
cardinality and contact identities. Its first average handles an empty
outside family. Its second average removes an actual first heavy block
and proves a distinct second one, conditional on the uniform upper
bound13 that the remaining argument must establish.

`CommonPathFactor` closes an actual three-vertex path at a common
replacement. `PartitionReplacement` combines arbitrary complementary
partitions on their exact supports. `CoreTransferLowFactor` uses these
to combine the given factor on T∪B∪{q2} with two more four-cycles.
`CoreTransferSmallPaw` applies this four-cycle factor when remainder
contacts≤8. `CoreTransferHeavyShape` then excludes a positive leaf
via the proved first classification and the low-terminal factor
obstruction. Every qualifying outside block has leafdegree0, both low
degrees≤1, triangle contacts≥11, is complete, and permits every triangle
vertex replacement. The core remains T∪B, of size7, excluding the leaf.

Combined build and direct Lean pass:399proof modules plus Verification,
9105build jobs,718ordered axiom reports, all using only `propext`,
`Classical.choice`, `Quot.sound`. The400-file forbidden/limit scan is
clean and imports are acyclic. Independent literal checks cover4direct
and192bridge replacement/score cases,64four-cycle low-paw factors, and
41,371small averaging instances,20of which meet the surplus hypothesis.
Arbitrary chains, factors, and natural-number averages are proved in Lean;
the Python checks are not trusted proof oracles.
Logs:`validation/lean-core-transfer-shape-{build,axioms}.txt`,
`validation/lean-core-transfer-shape-audit.json`, and
`validation/core-transfer-shape-independent.json`.

TeX pass405 has239pages and20,814lines, with no warnings or box issues.
Changed plan pages219–220and224–225 were rendered and checked.
The mathematical proof is unchanged. Milestone37 still requires the
uniform total13/d4degree1 conclusion using the distinguished core vertex,
and the final factor involving two distinct heavy blocks. The verified
milestone count remains36of82. The exact main theorem remains unproved
and its main file absent. The goal stays active; no blocker is present.
No limits, staging, commits, or other-task sources changed.

## Lean checkpoint — complete two-heavy-block transfer bound, TeX9.37

Nine new proof modules complete the remaining steps of TeX9.37.
`ThreeSetChoice` retains specified triangle vertices in exact three-set
enumerations. `TriangleOneBlockFactor` and `TriangleTwoBlockFactor`
construct actual factors on eight and twelve vertices, with explicit
cycle edges and disjoint supports. `CoreTransferMissingContact` applies
these to the distinguished vertex in T or B, using the actual low-terminal
chain's local or selected-family factor obstruction. No induced-cycle
condition or assumed core obstruction is introduced.

`TriangleContactBounds` proves that one missing entry bounds the triangle
total by11, and that every column has at least2contacts when the total is
at least11. `CoreTransferHeavyExact` proves total13 and fourth-low degree1
for every qualifying outside block. It explicitly separates the zero
first-low row from the missing-contact case. `CoreTransferFinalFactor`
finds a common triangle neighbor of the two low neighbors and constructs
three disjoint four-cycles with the two ordinary block replacements.
`CoreTransferInsideBound` applies the already proved two-block average
with the proved uniform13bound. `CoreTransferSourceBounds` derives the
direct lower bound35 and bridge lower bound47 from their actual routes.

Both full build and direct Lean pass:408proof modules plus Verification,
9114build jobs,732ordered axiom reports. The only reported axioms are
`propext`, `Classical.choice`, and `Quot.sound`. All409modules are reachable
from Verification; the forbidden/limit scan is clean and imports are
acyclic. Independent finite checks cover52exact-count cases,240two-cycle
and960three-cycle missing-contact factors, and2704final three-cycle
factors. Python is not used as a proof oracle.
Logs:`validation/lean-core-transfer-final-{build,axioms}.txt`,
`validation/lean-core-transfer-final-audit.json`, and
`validation/core-transfer-final-independent.json`.

TeX pass406 has239pages and20,826lines, with no warnings or box issues.
Changed plan pages219–220and224–225 were rendered and checked. The full
mathematical proof is unchanged. The verified milestone count is37of82,
not an estimate of remaining effort. TeX9.38–9.39, the rest of source4.9,
and later global claims remain. The exact main theorem is unproved and
its file absent. The goal stays active; no blocker is present. No limits,
staging, commits, or other-task sources changed.

## Lean checkpoint — Wang4.9 and both core consequences

Fourteen new proof modules complete TeX9.38–9.39. `CoreReplacementFactor`
combines an actual core factor with a terminal replacement and extends it
over all unselected blocks; hence the old terminal row has degree≤2.
`FeasibleHighPair` proves a useful stronger statement: a feasible terminal
meeting both highs has exactly those contacts when the low diagonal is
absent, using the first maximum alone. `CoreObstructionRoutes` applies
this after the actual equal-score bridge swap and derives each exposed
low's core degree≤1 from the stated outside-neighbor factor hypothesis.

`CoreObstructionCounts` proves the exact inside identities and the
strong-chain paw contact bounds. `CoreDirectObstruction` gives34<35.
Its `direct_core_degree_le_one` proves the first conclusion of the core
corollary. `CoreObstructionRoutes.direct_inside_bound_of_highs` proves
the second; it has neither an outside-neighbor nor a second distinguished
vertex hypothesis. The seven-set is always T∪B, excluding the old terminal.

`CoreBridgeBounds` bounds the paw contacts on C and D and gives the
preliminary core sum≤15. `CoreCliqueEquality` proves that total12paw
contacts force zero leaf degree, all12triangle contacts, and a complete
seven-set. `CompleteCoreExtension` combines two disjoint cycles with
the complete four-vertex complement. `CoreCliqueFactorSupport`,
`CoreCliqueOffcenterFactor`, and `CoreCliqueCenterFactor` implement the
two explicit equality-case factors. `CoreCliqueEqualityExcluded` selects
the unique low neighbor, proves the center case must use the fourth
cycle vertex, and excludes equality15. The sharper14bound gives the
bridge upper bound46 in `CoreBridgeInsideBound`. `CoreObstruction`
then joins the direct and bridge routes and contradicts35or47respectively.

All these are Lean proofs about actual cycles, block partitions, and
feasible chains. The outside-neighbor factor property is the explicit
mathematical premise of Wang4.9, not an axiom or an assumed main theorem.
Every required property of the direct/bridge routes is proved.

Full build and direct check both pass:422proof modules plus Verification,
9128build jobs,766ordered axiom reports, using only `propext`,
`Classical.choice`, `Quot.sound`. All423modules are reachable from
Verification, imports are acyclic, and forbidden/limit scans are clean.
Independent checks cover8high-pair score cases,104equality candidates,
840offcenter and420center three-cycle factors, and42first-low center
exclusions. Python is not a proof oracle.
Logs:`validation/lean-core-obstruction-{build,axioms}.txt`,
`validation/lean-core-obstruction-audit.json`, and
`validation/core-obstruction-independent.json`.

TeX pass409 has239pages and20,841lines, without warnings or box issues.
Changed plan pages219–220and225–226 were rendered and checked. The
mathematical proof is unchanged. The verified milestone count is39of82,
not an estimate of remaining effort. Next are pattern(8)'s exclusion
and Claim2.2, TeX9.40–9.41. The exact main theorem remains unproved
and its file absent. The goal remains active with no blocker. No limits,
staging, commits, or other-task sources changed.

## 2026-08-27 — Pattern (8) preparation

TeX9.40 is partially implemented in eight new modules. The exact induced
core retains the optional second diagonal. Its involution gives an actual
feasible alternate chain with both scores unchanged, and preserves the
four-row set and every outside block. Inside sum≤14 gives an outside block
with≥9 contacts. Twelve actual insertion partitions cover all endpoint pairs;
no row is universal, every row is≤3, and the two actual terminal rows are≤2.
Cyclic normalization makes the first old low row have degree3 and gives its
exact three-contact row on the outside block with the low diagonal absent.
The strict-score branch, final core contradiction, and Claim2.2 remain.

Full build and direct check pass:430proof modules plus Verification,
9136jobs,811ordered axiom reports, only `propext`, `Classical.choice`,
`Quot.sound`. All431modules are reachable, imports are acyclic, and the
forbidden/limit scan is clean. Independent checks cover both optional
diagonals,128involution adjacency cases,24literal path partitions,
24ordered endpoint cases, five row-bound cases, and eight nonuniversal
cyclic labelings. TeX pass410:240pages,20,860lines, no warnings or box
issues; plan pages220–221and225–226 were rendered and visually checked.
The count remains39of82 completed milestones, not remaining effort.
Logs: `validation/lean-first-paw-eight-preparation-{build,axioms}.txt`,
`validation/lean-first-paw-eight-preparation-audit.json`, and
`validation/first-paw-eight-preparation-independent.json`.

A default-heartbeat failure in the alternate-score proof was resolved by
splitting proved helpers and avoiding a dependent support rewrite. No limit
was changed. A later disk-full error was resolved by approved relocation of
only this task's generated Lean library artifacts, with SHA-256 verification
of all2,155files before and after. Evidence: `validation/lean-lib-relocation.json`.
No sources, other tasks, quotas, staging, commits, or computational settings
were changed. The exact main Lean theorem is still unproved and absent.

## 2026-08-27 — Pattern (8) strict gain and high-pair terminal

Four additional modules complete Step4 of the pattern8 plan.
`FirstPawEightColumns` proves each low column meets at most one of the
other three rows. `FirstPawEightRigidity` proves the exact six-contact
saturation and exceptional row shape. `FirstPawEightGain` constructs
blocks[5,9,7,10] and[1,4,6,2], triangle[0,8,11], and singleton3 on the
actual twelve vertices. The first block has the old block's exact score,
including its optional second diagonal. The second has6edges; the outside
old block has≤5. `FirstPawEightHighPair` reflects the actual outside cycle
and, when necessary, uses the proved alternate chain, forcing one of the
two possible terminals to meet both highs. No fresh score maximum is assumed.

Full build and direct Lean check both pass:434proof modules plus Verification,
9140jobs,825ordered axiom reports with only `propext`, `Classical.choice`,
`Quot.sound`. All435modules are reachable from Verification, imports are
acyclic, and placeholder/forbidden/limit scans are clean. Independent checks
examine4096row masks,24six-contact candidates, eight exceptional row shapes,
and32strict score exchanges, including both old optional diagonals, both
terminal choices, and the high reflections. The score gains are1or2.
The arbitrary-graph exchange and all transport are proved in Lean; Python
is never imported or used as an oracle. Logs:
`validation/lean-first-paw-eight-high-pair-final-{build,axioms}.txt`,
`validation/lean-first-paw-eight-high-pair-final-audit.json`,
`validation/first-paw-eight-high-pair-independent.json`.

TeX pass412 has240pages and20,870source lines, no warnings or box issues.
Plan pages220–221and226–227 were rendered and visually checked. The
mathematical proof is unchanged. All builds pass after the task-only library
cache relocation. No limits, staging, commits, or other-task files changed.
The milestone count remains39of82, with9.40 partially implemented, not an
estimate of remaining effort. Next are the low-row bounds, final35≤33
contradiction, and Claim2.2. The exact main Lean theorem remains unproved
and absent; the goal remains active without a blocker.

## 2026-08-27 — Complete pattern8 exclusion and Claim2.2

`FirstPawEightLowBounds` exposes each outside low as an actual terminal,
proves its triangle degree≤1 and old-block degree≤1, and assembles the exact
inside upper bound33. `FirstPawEightLeafExcluded` excludes the third row's
first-low contact, locates its high contact, and supplies the seven-core
factor plus distinct triangle witnesses p2and the center. The already-proved
core corollary gives35 on the same six-row set, contradicting33. The actual
cycle reflection handles either high orientation. `FirstPawEightExcluded`
then assembles both original and swapped high-pair terminal branches.
`ClaimTwoTwo` excludes8 from the surviving first classification and restores
the original noncentral labels by cycle reflection. Pattern3 retains exact
rows[1,15,9,3] and only its first diagonal. No optional pattern8 diagonal was
silently removed, and no fresh maximizing premise or main theorem was assumed.

Full build and direct check pass:438proof modules plus Verification,
9144jobs,837ordered selected axiom reports, only `propext`, `Classical.choice`,
`Quot.sound`. All439modules are reachable, imports are acyclic, and the
placeholder/forbidden/limit scans are clean. Independent checks cover4seven-core
factors,8low-terminal replacements,4triangle-witness cases,144inside counts,
4third-row masks, and16label-restoration bits. These checks are supplemental;
the arbitrary-graph arguments and their transport are Lean proofs.
Logs: `validation/lean-claim-two-two-final-{build,axioms}.txt`,
`validation/lean-claim-two-two-final-audit.json`,
`validation/claim-two-two-independent.json`.

TeX pass413:240pages,20,880source lines, no warnings or box issues.
Plan pages220–221and225–227 were rendered and visually checked. The mathematical
proof is unchanged; the plan now records both9.40and9.41 fully implemented.
The count is41of82 milestones,50%, not an estimate of remaining effort.
The exact main theorem remains unproved and its main file absent. The full
proof of9.42/Wang4.10 was read, and its concrete next stages are in
`tmp/erdos577/full-row-implementation-plan.md`. The goal remains active
without a blocker. No limits, staging, commits, or other-task sources changed.

## 2026-08-27 — Wang4.10 preparation

Six new modules prove the first four stages of TeX9.42.
`FullRowFirstBlock` gives the seven-contact dichotomy, universal replacement
by the specified noncentral vertex, the first-block score tie and actual
feasible swap, and the unique triangle neighbor of the exposed last vertex.
`FullRowInsertions` certifies all six complementary paths and12ordered
endpoint cases, then proves the common-neighbor insertion. The complete case
uses a common set of cardinality≥3; the other case uses the six positive paths
with the second diagonal. It does not assume that the first diagonal is absent.
`FullRowSwap` makes the actual exchanged chain strong, preserving both scores,
and bounds its new first-block paw contacts by8. `FullRowCompleteBlock`
exposes every vertex of the complete outside block with exact scores and
proves the triangle and seven-core column bounds. `OneContactLabels` supplies
an actual cycle rotation. `FullRowColumns` proves triangle totals4and0 for
the two locations of the distinguished full row, including distinctness of
its block from the outside block. The full obstruction remains incomplete.

Full build and direct Lean check pass:444proof modules plus Verification,
9150jobs,866ordered selected axiom reports with only `propext`,
`Classical.choice`, `Quot.sound`. All445modules are reachable, imports are
acyclic, and placeholder/forbidden/limit scans are clean. Independent checks
cover12literal pair paths,12ordered endpoint cases,99clique common insertions,
6seven-contact row cases,4first-block and4full-block score ties,10unique rows,
and16unique-contact cyclic labelings. Python is never a Lean oracle.
Logs: `validation/lean-full-row-preparation-final-{build,axioms}.txt`,
`validation/lean-full-row-preparation-final-audit.json`, and
`validation/full-row-preparation-independent.json`.

The TeX proof now includes the six explicit neighbor-pair complementary
paths, with the first column described as chosen neighbors, not a full row.
Pass415:241pages,20,912source lines, no warnings or box issues. Pages177–178,
220–221,227–228 were rendered and visually checked. The exact mathematical
Proposition9.82 remains on page212. The Leanization plan records9.42as partial.
The count remains41of82 completed milestones, not an effort estimate.
The current progress log was shortened; its entire previous version was
preserved unchanged in `tmp/erdos577/progress-history-before-full-row-preparation.md`.

Next: prove the low-to-first-block bounds by actual three/four-cycle factors,
then inside bounds33and41 and the heavy-block contradictions. The full goal
remains active; no blocker is present. The exact main Lean theorem remains
unproved and absent. No limits, staging, commits, or other-task files changed.

## 2026-08-27 — Wang4.10 factors and inside averages

Five more modules complete stages5–6 of TeX9.42. `FullRowCommonFactor`
joins the actual two-cycle common-path factor to an actual complementary
partition and extends the selected factor while retaining all other blocks.
`FullRowFirstBlockBound` gives both actual contradictions: three cycles when
the distinguished full row is p3, four when it lies in B. The construction
works for every u∈A. No core-factor premise or center–z edge is needed for
this intermediate degree bound; those hypotheses remain in the full source
statement and are used elsewhere. The other case uses the actual B-z+p3
replacement, not an assumed partition oracle.

`FullRowInsideCounts` verifies the exact swapped support, both vertex bounds6,
and F'contactsA=5or1. `FullRowInside` proves the two six-row inside bounds33and41.
`FullRowHeavy` proves the selected family cardinals2and3, applies the existing
symbolic averaging argument, and returns a retained **original** block with
at least13contacts, distinct from Q,A,and optional B. Empty outside families
are included. These are intermediate results; the dense and small-paw final
factor contradictions, the full9.42obstruction, and the main theorem remain open.

Consolidated build and direct Lean check both exit0:449proof modules plus
Verification,450Lean files,9155jobs,887ordered selected axiom reports.
Only `propext`, `Classical.choice`, and `Quot.sound` occur. Every module is
reachable from Verification, imports are acyclic, and the forbidden/limit
source scan is clean. A proof-search heartbeat failure in a four-set union
identity was resolved with `union_assoc` and `union_left_comm`; no limit changed.
Independent checks reuse the previous insertion/column tests and verify192
three-cycle and3072four-cycle partitions with exact disjoint supports,32
vertex-bound combinations, swapped supports, and42averaging instances that
include zero outside blocks. Python remains supplementary, never a Lean oracle.

Evidence: `validation/lean-full-row-inside-final-{build,axioms}.txt`,
`validation/lean-full-row-inside-final-audit.json`, and
`validation/full-row-inside-independent.json`. Commands are in PROGRESS.md.
The TeX proof now records the exact complements and the bound for every A
vertex; the plan maps the five new modules and lists the remaining factor cases.
Pass417 has241pages and20,931source lines, with no warnings or box issues.
Pages177–178,221–222,227–228 were rendered and visually checked; the main
mathematical Proposition9.82 remains on page212.

The milestone count remains41of82, plus partial9.42; it is not a remaining
effort estimate. Goal active, no blocker, no main Lean file, no staging or
commits, and no other-task files or computational settings changed.

## 2026-08-27 — Full Wang4.10 and global path transfer complete

Nine further full-row modules finish every case of TeX9.42.
`FullRowDenseShape` applies the proved Claim2.2 to the actual exchanged paw.
A positive leaf row gives Pattern3, a low with two contacts, and an actual
core factor, completed by the **original** full-leaf replacement. Thus the
new leaf row is0. Actual low exposures then give both low rows≤1, triangle
contacts≥11, a complete heavy block, and all triangle replacements.
`FullRowDenseCount` proves the disjoint-row center contact with the bounds
center+low1+low3≤4 and triangle≤center+8 if no such contact exists.
The resulting≤12 contradicts13. This argument avoids an unnecessary split
on whether the center row is full and assumes no extra graph edges.

`FullRowDenseFactors` constructs both three-cycle partitions.
`FullRowDistinguishedFactor` completes the selected partition either with
the actual fourth paw vertex or with the actual B-z+p3 replacement, retaining
all unselected original blocks. `FullRowDenseExcluded` gives both dense-case
global contradictions. `FullRowSmallShape` exposes the larger low in A and
proves universal replacement on retained J, triangle columns≤1, and the
common replacement in both low orientations. `FullRowSmallFactor` constructs
the exact three-cycle core, then adds Q-q3+p2 for four cycles; the optional
B replacement gives the fifth. `FullRowSmallExcluded` checks both global
completions. `FullRowObstruction.full_row_obstruction` assembles both locations
and both heavy-block cases. Its seven-core premise is exactly T∪B, never F∪B.

`GlobalPathTransfer` also proves TeX9.43. It takes an arbitrary whole path
partition with score c.edgeScore+1 and uses the previously proved global
path bound, no-triangle-tie result, and classification at the upper score.
There is no assumption that only one original block changed. This is the
interface needed by the next two-vertex core obstruction.

All459proof modules plus Verification build and directly check:460Lean files,
9165build jobs,915ordered selected axiom reports, only `propext`,
`Classical.choice`, and `Quot.sound`. All modules are reachable from
Verification, imports are acyclic, and forbidden/limit scans pass. No new
axiom, oracle, computational setting, staging, commit, or other-task edit.
Independent tests reuse the previous cases and add960dense factors,
1280small factors,1208disjoint-row count cases, and35small-shape arithmetic
cases. Both low orientations and exact disjoint supports are checked.
These finite tests are supplementary; the arbitrary-graph proofs are in Lean.

Evidence: `validation/lean-full-row-obstruction-final-{build,axioms}.txt`,
`validation/lean-full-row-obstruction-final-audit.json`, and
`validation/full-row-obstruction-independent.json`. Exact commands are in
PROGRESS.md. TeX pass421:242pages,20,961source lines, no warnings or box issues.
Pages177–179,221–222,227–229,241–242 were rendered and visually checked.
The mathematical main Proposition9.82 remains on page212. The TeX adds the
disjoint-row inequality and records9.42and9.43as fully implemented.

The milestone count is now43of82; this52.4% is a count, not an effort estimate.
The two-vertex core proof9.44has been read and its exact six-stage plan is in
`tmp/erdos577/two-vertex-core-implementation-plan.md`. Goal active, no blocker.

## 2026-08-27: first three stages of the two-vertex core obstruction

Wang4.11/TeX9.44now has its first three stages proved, but the full lemma
is not yet formalized. The completed milestone count remains43of82.
Six modules prove the equal-score exposure and unique seven-core neighbor,
the complete replacement's gain, the exact disjoint replacement supports,
the matching-score argument forcing degree3, and all four local exclusions.
The supports leave exactly the positive path(q3,x,r,b); inducedness is not
assumed in the matching argument. Its later use still needs the missing edges.

The core-complement factor extension uses the actual supplied quadrilateral
on K\{z1,z2,r}, not a complete-core assumption. All factor constructions retain
the unselected original blocks. The second-core last-contact exclusion uses
the center–z2 edge; the other exclusions need neither center–z edge. In
particular the coupled statement is proved both from its two positive edges
and from the exact degree2row. This preserves the distinction required by9.45.

All465proof modules plus Verification build and directly check:466Lean files,
9171build jobs,945ordered selected axiom reports, only `propext`,
`Classical.choice`, and `Quot.sound`. All task modules are reachable from
Verification. The forbidden-source and unchanged-limit scan is clean and
imports are acyclic. No exact main Lean file exists. No new axioms, staging,
commits, subagents, or other-task changes were used.

Independent checks cover24equal-score exposures,48unique-row cases,
128two-block replacements,64gain2exclusions,64score ties,192crossing quads,
640center-contact factors and320each of the other three factor families.
Additional paw edges and exact disjoint supports are included. These checks
are supplementary, never imported as a Lean oracle.

Evidence: `validation/lean-two-core-local-final-build.txt`,
`validation/lean-two-core-local-final-axioms.txt`,
`validation/lean-two-core-local-final-audit.json`, and
`validation/two-core-preparation-independent.json`. Exact commands are in
PROGRESS.md. TeX pass423has242pages and20,993source lines, with no warnings or
box issues. Pages179–181,213,222,229–230,and242were rendered and visually checked.
The exact mathematical Proposition9.82is on page213. The updated text spells
out the two-block support identities and the supplied-core-complement extension.

Next: stage4's inside bound23, stage5's outside averaging and whole path
partition, then stage6's classification alternatives and final factors.
The goal stays active; no blocker has arisen.

## 2026-08-27: complete Wang4.11 / TeX9.44

The full two-vertex core obstruction is now proved in `TwoCoreObstruction.lean`
as `Erdos577.TwoCore.two_vertex_core_obstruction`.
Its signature retains both displayed source center–core contacts and the exact
seven-vertex core premise. The first center contact is unnecessary in this
proof but is retained in the source-facing statement. The main Erdős577Lean
theorem is still absent and unproved. The completed count is44of82milestones;
approximately53.7% counts milestones, not remaining effort.

TwoCoreInsideRows proves zero leaf contacts onB, leafinside degree3, the
internal pair total5, first-block pair bound1+t, and the coupled bound5.
The coupled count uses K=T∪B: the last triangle row is epsilon∈{0,1},
the last Bdegree is≤3, and t+epsilon≤2. TwoCoreInside assembles≤23from the
actual source hypotheses. TwoCorePathPartition selects an outside block
with≥9contacts, including the empty-outside contradiction, and constructs
the whole path partition at scoreE+1with all unselected blocks retained.

The existing Classified.common_alternatives theorem tracks reversal explicitly;
no fresh arbitrary path ordering or extra inducedness assumption is used.
TwoCoreFinalFactors constructs the four-cycle factor onF∪B∪Q∪Jin the first
alternative and the two-cycle factor onF∪Jin the second. Both complete to a
spanning packing by retaining all unselected blocks. TwoCoreObstruction
joins these facts with the global path transfer. No conditional oracle remains
in the proof of9.44.

Consolidated build and direct Lean both exit0:470proof modules plus Verification,
471Lean files,9176build jobs,957ordered selected axiom reports. Only `propext`,
`Classical.choice`, and `Quot.sound` occur. All modules are reachable from
Verification, imports are acyclic, and forbidden-placeholder/limit scans pass.
No staging, commits, subagents, or other-task changes were made.

Independent checks add280inside-arithmetic cases,1560outside-average cases,
5120factors for each final alternative, and3072scored whole partitions.
They explicitly retain an extra unselected block and check exact disjoint
supports. Python supplies no Lean oracle. Evidence is in
`validation/lean-two-core-obstruction-final-{build,axioms}.txt`,
`validation/lean-two-core-obstruction-final-audit.json`, and
`validation/two-core-obstruction-independent.json`.

TeX pass424:242pages,21,008source lines, no warnings or box issues.
Pages179–181,213,222,229–230,and242were rendered and visually checked.
The text includes the equivalent triangle–block count and marks9.44fully
implemented. Proposition9.82remains on page213. The next five-contact variant
was reread and its exact plan is in `tmp/erdos577/five-contact-core-implementation-plan.md`.
Both center–core contacts must be dropped there; z2q3is not assumed absent.
Goal active; this turn made verified progress and no blocker arose.

## 2026-08-27: complete five-contact variant, TeX9.45

`Erdos577.TwoCore.five_contact_core_obstruction` in TwoCoreFiveObstruction.lean
now proves the full variant with neither center–zi contact assumed. It retains
the possible z2q3edge. The exact core is still T∪B, and its complementary
quadrilateral is supplied explicitly. The completed count is45of82milestones
(approximately54.9%, a milestone count only). The main Lean theorem remains absent.

TwoCoreInsideRows now has last_core_coupled_of_block_bound, which bounds the
triangle–block total by the Bdegree bound plus2. The old last_core_coupled
statement is preserved and proved from it. TwoCoreInsideBudget proves the
inside bound23whenever the pair-row and coupled-core budgets sum to≤11.
The original inside_upper is a proved6+5instance. TwoCoreFiveInside proves
the5+6instance without second_core_last_absent or any center–zi hypothesis.
TwoCoreConclusion proves the shared final contradiction from the actual
replacement scores and crossing/complementary quadrilaterals. The full9.45
theorem joins these facts. The original9.44source-facing statement is unchanged
and passes the complete regression build and axiom audit.

All474proof modules plus Verification build and directly check:475Lean files,
9180build jobs,963ordered selected axiom reports. Only `propext`,
`Classical.choice`, and `Quot.sound` occur. All modules are reachable from
Verification, imports are acyclic, and forbidden-placeholder/limit scans pass.
No new axioms, computational-limit increases, staging, commits, subagents,
or other-task changes were made.

Independent checks rerun the previous core suites and add300arithmetic cases,
43,008actual row configurations, and1536factors for each final alternative.
There are5376row cases and192paired factor cases with both center contacts
absent and z2q3present. Exact disjoint supports and unselected blocks are checked.
The first script attempt exposed a test-helper restriction on self-pairs;
the incidence sums now explicitly exclude loops, matching simple-graph degrees.
This was a Python harness correction, not a change to a mathematical assumption.

Evidence: `validation/lean-five-core-final-{build,axioms}.txt`,
`validation/lean-five-core-final-audit.json`, and
`validation/five-contact-core-independent.json`. TeX pass425has242pages and
21,017source lines, no warnings or box issues. Pages180–181,213,222–223,
229–230,and242were rendered and visually checked. Proposition9.82stays on213.
The plan records the shared budgets/conclusion and9.45as complete.

The complete-core variant9.46was reread; its plan is in
`tmp/erdos577/complete-core-implementation-plan.md`. Its degree2case must use
inside_upper with a selected center neighborwonly for the missing last contact,
while retaining the original z2for the crossing quad. Goal active; no blocker.
The exact main Lean theorem remains unproved and the main file remains absent.

## 2026-08-27: complete two-full-row variant, TeX9.46

`Erdos577.TwoCore.complete_core_obstruction` in TwoCoreCompleteObstruction.lean
now proves9.46with the exact complete-block and two-full-row assumptions,
center degree at most2, and neither distinguished center contact assumed.
The complementary four-cycle is constructed, not passed as a premise.
The milestone count is46of82(approximately56.1%, not an effort estimate).
The exact main theorem and Claims2.3–2.7remain unproved in Lean.

TwoCoreCompleteComplement proves the exact core-complement identity, its
four-clique structure for every distinct pair in the complete block, and
the existence of a center neighbor different from a prescribed vertex when
the center row has degree2. The degree0or1case reduces to the five-contact
variant. In the degree2case, the selected neighbor supplies the missing last
contact through an actual three-cycle factor. The low-level inside_upper
uses this selected neighbor only for its degree estimate. The final crossing
quad and obstruction_of_inside retain the original distinguished pair.
No adjacency between the selected neighbor and the other low cycle vertex
is assumed. The original9.44and9.45statements pass regression verification.

Consolidated build and direct Lean both exit0:476proof modules plus Verification,
477Lean files,9182build jobs,967ordered selected axiom reports. Only propext,
Classical.choice, and Quot.sound occur. Every module is reachable from
Verification; imports are acyclic and source/limit scans pass. No new axiom,
placeholder, computational setting, staging, commit, subagent, or other-task
change was introduced.

The independent test reruns prior core checks and adds12original complements,
60small-center cases,108neighbor choices, and12,096each of inside counts,
forbidden-contact factors, and scored whole partitions. Among these are8064
cases where the selected neighbor differs from the original second vertex
and lacks the extra cycle contact an incorrect substitution would need.
There are2688cases with neither original distinguished center contact.
Exact disjoint supports, the original crossing pair, and an unselected
block's retention are checked. These tests provide no Lean oracle.

Evidence: validation/lean-complete-core-final-{build,axioms}.txt,
validation/lean-complete-core-final-audit.json, and
validation/complete-core-independent.json. TeX pass427has242pages and21,033
source lines, no warnings or box issues. Pages181–182,213,222–223,229–230,
and242were rendered and visually checked. Proposition9.82remains on213.
The mathematical text and Leanization plan explicitly distinguish the selected
neighbor used in the count from the original pair used in the final factor.

The next joint initial exchange9.47and exposed-leaf exclusion9.48were reread.
The implementation plan records existing strong first-swap APIs and the
six-slot weighted count, in which the third triangle vertex is counted twice.
It is at tmp/erdos577/joint-setup-implementation-plan.md. Goal active, no blocker.

## 2026-08-27: complete joint initial exchange, TeX9.47

`Erdos577.JointClaims.initial_exchange_and_six_row_sum` in JointSetup.lean
now proves all conclusions of9.47. The milestone count is47of82(about57.3%,
counting milestones rather than effort). Claims2.3–2.7and the exact main
theorem remain unproved in Lean. The main file is still absent.

JointSetupRows preserves the exact two starting alternatives and their
conditional row clauses. It derives the first-three leaf contacts, universal
noncentral replacement inII, triangle column bound1, and pairwise disjoint
triangle rows. The general column bound uses an actual terminal swap and
the global no-factor condition; it assumes no feasibility of that new chain.
JointSetupFactors constructs both local factors that force the third row0.
The leaf-degree3case is handled by its full other noncentral row and column
disjointness, rather than being silently treated as a full leaf.

JointSetupSwap uses the existing score-preserving FullRow first swap and
constructs the paw(q3,b,r,c) with exact support. Its chain is strong, both
scores are unchanged, and every unselected block remains. A failed b
replacement ofq3forcesI. JointSetupCount defines the weight as contacts
from the paw plus the singleton rowsc andq3; c is counted twice. The inside
bound is the sum8+8+2+0+2+3=23. Three degree-decomposition identities and
the six minimum-degree slots force an outside block of weight≥13, including
the empty-family contradiction. JointSetup assembles these facts and states
the final displayed inequality with coefficient2on the original third vertex.

Consolidated build and direct Lean both exit0:481proof modules plus Verification,
482Lean files,9187build jobs,988ordered selected axiom reports. Only propext,
Classical.choice, and Quot.sound occur. Every task module is reachable from
Verification, imports are acyclic, and source/limit scans pass. No new axiom,
placeholder, computational setting, staging, commit, subagent, or other-task
change was introduced. Ordinary finite-support and coercion errors and linter
warnings were corrected without disabling checks or increasing limits.

Independent checks reuse the existing full-row helpers. They cover9universal
terminal rows,73,728column factors, both zero-row factors,8scored exchanges,
the two failed noncentral replacements, and both optional-diagonal states
in the leaf-degree3case. The inside sums are21,22,23; the extra occurrence
ofc contributes exactly2in these checked configurations. The696outside
arithmetic cases include24empty-outside cases. Disjoint supports, both score
identities, and an unselected retained block are checked. Python is not a Lean oracle.

Evidence: validation/lean-joint-setup-final-{build,axioms}.txt,
validation/lean-joint-setup-final-audit.json, and
validation/joint-setup-independent.json. TeX pass428has242pages and21,062
source lines, no warnings or box issues. Pages182–183,213,222–223,229–230,
and242were rendered and visually checked. Proposition9.82remains on213.
The uniform six-slot derivation was added before implementation, and the
Leanization plan now marks9.47complete. The next exact construction plan is
tmp/erdos577/joint-heavy-leaves-implementation-plan.md. Goal active, no blocker.

## 2026-08-27: complete exposed-leaf exclusion, TeX9.48

`Erdos577.JointClaims.heavy_leaves_zero` in JointHeavyLeaves.lean now proves
both exposed leaves have zero row on every old block satisfying the six-row
threshold13, and the remaining weighted triangle count is≥13. There is no
additional maximizing choice and no restriction to a specially selected
heavy block. The count is48of82milestones(about58.5%, not an effort estimate).
Claims2.3–2.7and the exact main theorem remain unproved; the main file is absent.

JointLeafCounts derives the exact positive-leaf counts and outside factor
from Claim2.2. JointLeafWeighted excludes9,13,14and forces the normalized-paw
swap before transferring the replacement clauses of10–12to the original
third vertex. Both high-row and common-neighbor replacement conclusions are
proved with the actual vertex and original block support.

JointLeafFactors constructs the two three-cycle factors and retains all
unselected original blocks. It reuses the existing common-path splice with
the noncentral paw labels swapped for the first factor, and the actual
crossing partition plus replacementUnion for the second. JointLeafCommon
proves the common selections, two-contact nonneighbor replacement, missing
triangle contacts, and the two-cycle completion in either leaf orientation.

JointLeafSmallHigh excludes a high exposed leaf when the third degree≤2.
JointLeafSmall finishes that entire degree range using the two actual
chains and Claim2.2, including the immediate contradiction for two zero
leaf rows. JointLeafDenseCounts proves the two totals≤8in the other range.
JointLeafLarge handles both weighted-triple alternatives and closes with
the existing full-row obstruction. Its final branch splits directly on the
original CaseOne proposition: the factor excludes it, and CaseTwo follows
from the original disjunction. No new center-row hypothesis is inserted.

Consolidated build and direct Lean both exit0:490proof modules plus Verification,
491Lean files,9196build jobs,1007ordered selected axiom reports. Only propext,
Classical.choice, and Quot.sound occur. Every task module is reachable from
Verification, imports are acyclic, and source/limit scans pass. No new axiom,
placeholder, computational setting, staging, commit, subagent, or other-task
change was introduced. A block-support rewrite and linter issues were fixed
without suppressing checks or increasing any limit.

Independent tests rerun the joint-setup checks and add384weighted row cases,
1536universal replacements,4224common insertions,512pattern9pair exclusions,
2304first three-cycle factors,384CaseIfactors, and16two-cycle factors in
each leaf orientation. Small/high, small/short, both-zero, large/pair, and
final-full-row arithmetic counts are15,38,75,63,1. Both normalization
orientations, optional diagonals, exact disjoint supports, and an unselected
block's retention are checked. Python supplies no Lean oracle.

Evidence: validation/lean-joint-leaves-final-{build,axioms}.txt,
validation/lean-joint-leaves-final-audit.json, and
validation/joint-leaves-independent.json. TeX pass430has243pages and21,087
source lines, no warnings or box issues. Pages183–184,186,213,222–223,
229–230,and243were rendered and visually checked. Proposition9.82remains
on213. The zero-leaf small case and direct CaseIsplit were added before
implementation; the plan records9.48complete. A stray plus sign in the
following lemma's prose was corrected without changing its mathematics.

The entire next core lemma9.49was reread, including all eight patterns and
its explicit outside factors. Its plan is in
tmp/erdos577/joint-core-implementation-plan.md. The title's CaseIIrefers to
the dense outside case; it does not permit dropping CaseOne on the first
block. Goal active; this turn made verified proof progress and no blocker arose.

## 2026-08-27: finite classification and local constructions in TeX9.49

The23JointCore modules now prove the eight source patterns, complementary
quadrilaterals with the primary five-edge bound, universal third-row
replacements, and the outside-neighbor factor. The full9.49lemma is not yet
complete: its high-contact complete-complement choice, zero first-block rows,
and inside17/22bounds remain. The count stays48of82milestones, about58.5%by
count and not an effort estimate. The exact main theorem remains unproved.

The finite row reconstruction has316admissible cases. Ninety-three have
explicit cyclic labels in patterns27–34. Every other case is covered by an
already proved DenseTriangle strict improvement. Bounded coverage is checked
by Lean's kernel; the source row order is preserved during transport. The
unused outside row is trimmed by a proved bitwise submask, so no zero-row
premise is hidden in the classification.

The eight positive core models have168explicit two-cycle factors, one for
each unordered pair of core neighbors. The new injective labeling requires
only avoidance of the seven-vertex core, allowing the outside vertex to be
the original leaf. Exact support images, complementary sets, and erasures
are proved. JointCoreLocal.core_outside_factor and local_core_pair use the
original two row bounds and Feasible, with no further maximization.

Full Lake build and direct Lean both exit0:513proof modules plus Verification,
514Lean files,9219build jobs,1060ordered selected axiom reports. All53new
public theorems are included. Only propext, Classical.choice, and Quot.sound
occur. All modules are reachable from Verification; import and source scans
pass. No placeholder, new axiom, computational-limit change, staged file,
commit, subagent, or other-task edit was introduced. The decidable adjacency
of edge unions and explicit graph-copy coercions were fixed without changing
limits or suppressing checks.

Independent checks enumerate exact four-cycle walks,93cyclic relabelings,
223strict triangle improvements,23optional-edge models,483outside factors,
92replacements,92complements, and65,536trimmed encodings. Python is not a
Lean oracle. Evidence: validation/lean-joint-core-finite-final-{build,axioms}.txt,
validation/lean-joint-core-finite-final-audit.json, and
validation/joint-core-finite-independent.json. The audit records SHA-256
digests for all new Lean modules, Verification, and the TeX source.

TeX pass431has243pages and21,120source lines, with no warnings or box issues.
The finite route was described before implementation, then the exact partial
status was recorded. Pages222–224and243were rendered and visually checked.
The implementation plan records the remaining work and the existing
dense_triangle_clique_label API for the high-contact choice. Goal remains
active with verified progress and no blocker.

## 2026-08-27: complete dense seven-vertex core, TeX9.49

JointClaims.dense_seven_vertex_core in JointDenseCore.lean proves every source
clause under the original row bounds and CaseOne∨CaseTwo. It does not assume
Claim2.3or2.4. The count is now49of82milestones, about59.8%by count, not effort.
The exact main theorem remains absent and unproved, and the goal remains active.

Ten new modules complete this milestone. The high-contact pair comes from
the existing dense_triangle_clique_label theorem, with an actual cyclic
four-tuple and complete primary complement. Every four-set in a graph missing
at most one edge has the required quadrilateral, proved by explicit neighbor
subsets. The low-contact case retains its SourcePattern tag rather than only
forgetting to positive edges. All prescribed replacements and complements
are carried through to the final theorem.

Every first-block column has at most one core neighbor, by an actual terminal
replacement retaining the other core block. The selected vertex's contact
with the first block yields the cycle(u,x,r,z), the noncentral replacement,
and the secondary complementary quadrilateral. The general partial-core
completion retains all other original blocks. CaseIuses its complete first
block and two remaining noncentral contacts; CaseIIuses the already proved
universal replacement. The inside rows are at most5,6,6,5, giving17and22.

Full Lake build and direct Lean both exit0:523proof modules plus Verification,
524Lean files,9229build jobs,1079ordered selected axiom reports. All19new public
theorems are printed, including the full dense-core theorem; only propext,
Classical.choice, and Quot.sound occur. All modules are reachable, imports
are acyclic, and source/limit scans pass. No staging, commits, new axioms,
placeholders, subagents, or computational-limit changes occurred. A default
heartbeat failure in an automated set-reordering step was resolved by explicit
insert_comm identities, without raising limits or suppressing checks.

Independent tests rerun the complete finite-core regression and add770
near-clique four-sets,13high-contact cores,360three-cycle factors retaining an
unselected block, and504inside configurations covering CaseIand both CaseII
leaf degrees. Exact four-cycle walks and disjoint supports are checked.
The bounds17and22are both attained locally. Python supplies no Lean oracle.

Evidence: validation/lean-joint-dense-core-final-{build,axioms}.txt,
validation/lean-joint-dense-core-final-audit.json, and
validation/joint-dense-core-independent.json. TeX pass433has243pages and21,143
source lines, no warnings or box issues. Pages222–224and243were rendered and
visually checked. The high-contact route was recorded before implementation;
the completed status is now in the Leanization plan. The next CaseIobstruction
and Claim2.3proofs were reread at TeX9.50–9.51. No blocker is present.

## 2026-08-27: global preparation for the CaseI obstruction, TeX9.50

The original row inequalities now imply the entire heavy-block preparation
in JointFirst.exists_restricted_heavy_block. Fifteen modules after9.49prove
the second strong terminal, the inside22budget, the outside nine-contact
block, all four arm-triple exclusions, the common-insertion prohibition,
and row bounds3,3,2,2with the stronger bounds on the two actual terminals.
The mixed-leaf factor uses the noncentral first-block replacement and a
secondary core complement; its selected-partition completion retains every
other block. No optimizing choice beyond Feasible was introduced.

The direct core obstruction is transported to both actual strong terminal
chains. The strict score argument is also proved in both chains: the primary
core complement has at least5edges and the crossing complete block has6;
the selected old blocks have at most6and exactly4. The remaining set has
cardinality4and contains the specified triangle. The first block and every
unselected block are retained by selected_edges_le. This avoids the invalid
assumption that any three arms with their center form a feasible remainder.

The finite research has12,288admissible configurations:12,104common insertions,
152direct-core cases,32strict gains. Its global constructions are proved,
but the finite coverage and arbitrary-graph cyclic transport remain pending.
Therefore9.50and Claim2.3are not marked complete; the count stays49of82.
The exact main file remains absent and the goal active, with no blocker.

Full Lake build and direct Lean exit0:538proof modules plus Verification,
539Lean files,9244build jobs,1112ordered selected axiom reports. All33new
public theorems have reports, using only propext, Classical.choice, Quot.sound.
Every module is reachable; imports are acyclic; placeholder and limit scans
pass. A default-heartbeat failure in a set rearrangement was fixed with
explicit insert_comm identities, with no limit increase or suppressed check.
No staging, commits, subagents, placeholders, new axioms, or other-task edits.

Independent checks rerun the previous core regressions and add96replacement
patterns,41,472arm-triple factors with a retained block,5,472direct-pattern
transports, and1,152strict gains across36core models. All arm roles and both
leaf orientations occur; cycles have exactly four vertices; the least gain
is one. Python is not a Lean oracle. Evidence is in
validation/lean-joint-first-preparation-final-{build,axioms}.txt,
validation/lean-joint-first-preparation-final-audit.json, and
validation/joint-first-preparation-independent.json.

TeX pass434has244pages and21,176source lines, without warnings or box issues.
The finite route was written before implementation, and its remaining status
is explicit. Pages223–225and244were rendered and visually checked; the exact
mathematical theorem remains Proposition9.82on page213. The next step is the
finite row classifier, preserving the positive one-row replacement geometry
without imposing nonexistent edges among the four arms.

## 2026-08-27: CaseI obstruction and Claim2.3, TeX9.50–9.51 complete

Sixteen modules complete the remaining finite classification and Claim2.3.
RowReplacementModel uses an explicit three-vertex path for each positive
single-row replacement; its finite table is kernel checked. The transport
requires only the actual row edges and the two block diagonals, not a graph
on the other arms. The96positive and160negative cases were also checked
independently against actual four-cycle walks.

JointFirstRowEncoding encodes four independent rows. The finite classification
checks all four diagonal masks and65,536row masks each, using1024bounded
kernel proofs. The12,288admissible configurations divide into12,104common
insertions,152direct core patterns, and32strict gains. Cyclic labels and
negative diagonal information are preserved in JointFirstPatternTransport.
JointFirstObstruction.case_one_dense_false combines this complete split
with the proved global preparation and both actual terminal chains.

JointCaseOneLabels extracts the center neighbor and two disjoint noncentral
neighbors and labels the complete first block. JointCaseOneExposed proves
the full, positive, and two-contact rows after the last-vertex exchange.
JointCaseOneExcluded splits the heavy block's weighted row sum, applying
the dense obstruction in the original or exchanged center while retaining
the same heavy block and third triangle vertex. ClaimTwoThree then proves
TriangleChain.Feasible.claim_two_three for both original noncentral labels.
No Claim2.4or extra maximizing choice is used.

Full build and direct Lean exit0:554proof modules plus Verification,
555Lean files,9260build jobs,1136ordered selected axiom reports. All24new
public theorems have reports; only propext, Classical.choice, Quot.sound
occur. Imports are acyclic, every module is reachable, and source/limit
scans pass. Computational limits remain unchanged; no staging, commits,
new axioms, placeholders, subagents, or other-task edits occurred.

Independent checks rerun the earlier core/preparation regressions and read
the actual Lean replacement/candidate data. They cover262,144encodings,
22CaseIlabelings,13weighted-center splits, both noncentral orientations,
exact disjoint four-cycle supports, and retained blocks. The kernel proofs
do not call Python. Evidence is in validation/lean-claim-two-three-final-
{build,axioms}.txt, validation/lean-claim-two-three-final-audit.json, and
validation/claim-two-three-independent.json.

TeX pass435has244pages and21,202source lines, without warnings or box issues.
Pages223–225and244were rendered and visually checked; Proposition9.82remains
on page213. The checkpoint is now51of82milestones, about62.2%by count, not
effort. The next obligation is the eight-row alternative9.52, followed by
Claims2.4–2.7. The exact main theorem is still absent/unproved and the goal
remains active. No blocker is present.

## 2026-08-27: the eight-row alternative, TeX 9.52 complete

Nine JointEight modules prove the complete source alternative, without
assuming Claim 2.4 or adding a maximizing choice of the outside block.
The pointwise theorem every_eight_heavy_block applies to every block with
eightWeight at least 17. The existence theorem obtains such a block from
the inside budget 31. Both zero leaf rows and all alternatives B1–B3 retain
their exact bounds; eta is Fin 2, so both natural subtractions are faithful.

JointEightRows and JointEightCount use the newly available Claim 2.3 to
remove the original center row and add its inside degree 3 and the exposed
terminal's inside bound 5. Exact partition counting handles an empty outside
family. JointEightTerminal and JointEightLowTerminal use the actual exchanged
paw for the two weighted branches, Claim 2.2, and its outside factor.
They prove the universal terminal row, triangle-column bound, disjoint
leaf/third rows, and the complete selected block in the low branch.

JointEightWeighted excludes the swapped weighted normalization and identifies
the original center as the high noncentral row. JointEightHighZero uses
Claim 2.3 in the exchanged chain to remove its positive center row, then
constructs the displayed pair of four-cycles for pattern 12. JointEightLowZero
labels an arbitrary complete block by two prescribed distinct vertices and
constructs the low-branch pair. Here the seventeen threshold already implies
a positive center row when the third row is positive; this directly reaches
the factor that the TeX proof uses to deduce a zero center row. JointEightFactors
completes either pair with the first-block replacement and every unselected
block. No edge between the two exposed leaves is required.

Full build and direct Lean exit 0: 563 proof modules plus Verification,
564 Lean files, 9269 build jobs, and 1159 ordered selected axiom reports.
All 23 new public results are included; only propext, Classical.choice,
and Quot.sound occur. Imports are acyclic and every task module is reachable
from Verification. Source and computational-option scans pass. No limits,
other-task files, staging, commits, new axioms, or placeholders were introduced.

The independent check reruns the prior core, preparation, and Claim 2.3
regressions, then checks 288 common-neighbor factors, 288 pattern-12 factors,
288 complete-block factors, six first-block cases, and all 3125 degree
vectors. Each constructed factor has disjoint exact four-cycle supports
and an unchanged outside block. Python is not used by the Lean proof.
Evidence: validation/lean-joint-eight-final-{build,axioms}.txt,
validation/lean-joint-eight-final-audit.json, and
validation/joint-eight-independent.json.

TeX pass 436 has 245 pages and 21,215 source lines, with no warnings or
box issues. Pages 224, 225, 232, 244, and 245 were rendered and visually
checked. The exact mathematical theorem, Proposition 9.82, remains on page 213.
The verified count is 52 of 82 milestones (63.4% by count, not effort).
The next target is TeX 9.53, the reduction of a failure of Claim 2.4 to
Case II. The exact main Lean theorem is still absent and unproved. The
unbudgeted goal remains active; no blocker is present.

## 2026-08-27: failure-to-Case-II reduction, TeX 9.53 complete

JointClaims.case_two_reduction in JointCaseTwoReduction.lean handles a failed leaf/noncentral
sum for either original noncentral label. It produces an actual strong
chain, a Case II first block, and a distinct core block with both required
heavy inequalities. The triangle remains unchanged. The intermediate
second-row version also retains the original third vertex.

JointCaseTwoLabels uses cyclic rotations for the exact CaseTwo clauses.
The labeling itself needs no diagonal hypothesis, although the full-leaf
case is complete by the already proved feasibility consequence.
JointSingleExchange constructs the exceptional paw (v,b,r,c), its exact
support, and the full rows of both v and r on P-v+x. The first uses the
clique and full xrow; the second uses triangle-column disjointness and the
pendant edge rx. The terminal-degree bound and attachment to b prove the
new chain is strong. Both optimization scores and every other block are
retained. The reduction keeps the original heavy A through either center
exchange; it does not replace A by an unrelated old first block.

Three modules and nine public results were added. Full build and direct
Lean exit 0: 566 proof modules plus Verification, 567 Lean files, 9272 jobs,
1168 ordered selected axiom reports. Only propext, Classical.choice, and
Quot.sound occur. Every module is reachable; imports, source scans,
computational-option scans, and whitespace checks pass. No limits, axioms,
placeholders, staging, commits, subagents, or other-task files changed.

Independent checks rerun all previous regressions and verify 36 cyclic
labelings across all four diagonal masks, 13 degree splits, 50 heavy row
patterns, and 800 exceptional exchanges. The new checks include exact
disjoint partitions, both full new rows, attachment degree one, preserved
edge/complete scores, and retention of A. The general feasibility and
reduction arguments are proved in Lean, not supplied by Python.
Evidence: validation/lean-joint-case-two-final-{build,axioms}.txt,
validation/lean-joint-case-two-final-audit.json, and
validation/joint-case-two-independent.json.

TeX pass 437 has 245 pages and 21,226 lines, with no warnings or box issues.
Pages 224, 225, 232, 233, 244, and 245 were rendered and checked visually.
The exact mathematical theorem remains Proposition 9.82 on page 213.
The verified count is now 53/82 milestones (64.6% by count, not effort).
Next is the other-block obstruction, TeX 9.54; its full proof was read and
the implementation plan records the actual second terminal, inside30
bound, triple completions, and reuse of the certified row classification.
The exact main Lean theorem is still absent and unproved. Goal active;
no blocker is present.

## 2026-08-27: other-block obstruction, TeX 9.54 complete

JointBridge.other_block_false excludes B1, B2, and B3 for every distinct
other block under the original CaseTwoCore and feasibility hypotheses.
It needs neither Claim2.4 nor the later additional maximizing choice.
The full, missed, and direct terminal routes each produce an actual strong
chain with the same triangle, both scores, and retained unselected blocks.
No arbitrary arm triple is assumed feasible.

Fourteen new modules and26 public proved results construct the route,
core-column bound, disjoint contact rows, inside bound30, heavy outside
block, and all four triple exclusions. TwoReplacementPartition combines
the two actual replacements with the selected-core completion. The
certified JointFirstRows classification is reused unchanged. Both direct
obstructions and strict gains apply in the two actual terminal chains.

Full build and direct Lean exit0:580 proof modules plus Verification,
581 Lean files,9286 build jobs,1194 ordered selected axiom reports.
Only propext, Classical.choice, and Quot.sound occur. Every module is
reachable from Verification; source, import, computational-limit, and
whitespace scans pass. No staging, commits, subagents, new axioms,
placeholders, computational-limit increases, or other-task edits.

Independent regressions rerun previous checks and cover36 core models,
816 routes (480 full,144 missed,192 direct),12,096 core completions,
13,824 common-neighbor completions,144 inside graphs attaining bound30,
124,416 triple completions across all four omitted arms, and3,456 strict
gains across both leaves. All cycles have exactly four vertices, exact
partitions and retained blocks. Python supplies no Lean oracle.
Evidence: validation/lean-joint-bridge-final-{build,axioms}.txt,
validation/lean-joint-bridge-final-audit.json, and
validation/joint-bridge-independent.json.

TeX pass438 has246 pages and21,235 source lines, without warnings or box
issues. Pages224,225,233,234,245,246 were rendered and visually checked.
Proposition9.82 remains on page213. The live fragment passes static checks;
browser rendering remains unchecked because the optional runtime is absent.
The verified milestone count is54/82 (65.9% by count, not remaining effort).
Next is TeX9.55, the additional maximizing choice and refined core labels.
The exact main theorem is absent and unproved. Goal active; no blocker.

## 2026-08-27: maximal core and prescribed-triple insertion, TeX9.55–9.56 complete

JointMaximalCore makes the two finite choices of a block within one fixed
chain. It applies the eight-row alternative and the proved other-block
obstruction to obtain a good qualifying block. The first maximum and tie
maximum together force ten triangle contacts when the chosen center/third
sum is seven. The reduction handles failure at either noncentral vertex,
keeps the original triangle, and records the zero center row on Q.

Seven new modules add18 public proved results. The128 finite source-row
inputs have23 allowed rows;19 remain after the new seven-sum bound. The
refinement explicitly excludes29/30, labels equal b/r rows as31 with the
additional edge, and unequal rows as32 with its additional edge. In28,
two b-neighbors are normalized to the first two labels. Arbitrary-graph
transport preserves exact row equality and inequality, not merely lower
degree bounds. The normalized28 complement is proved complete directly.
JointCoreRefinedSelection reuses all four source complements and the
universal third-row replacement. JointMaximalDenseCore retains every old
core conclusion, including outside factors, zero rows, inside17/22, and
the separately chosen complete complement at eleven triangle contacts.

TeX9.56 is exactly the existing FullRow.replacement_in_first_three in
FullRowInsertions.lean. Its six neighbor-pair paths remove indices2,1,2,0,0,0,
so every removed vertex belongs to indices0,1,2. Only the stated1–3 diagonal,
an outside vertex, and degree at least2 are assumed. The declaration is
already in the current full build and selected axiom report. No redundant
wrapper or new certificate was added; this milestone is completion by reuse.

Full build and direct Lean both exit0:587 proof modules plus Verification,
588 Lean files,9293 jobs,1212 ordered selected axiom reports. Only propext,
Classical.choice, and Quot.sound occur. All modules are reachable and imports
are acyclic. Source, computational-option, Python syntax, and whitespace
checks pass. No new axioms, placeholders, limit changes, staging, commits,
subagents, or other-task modifications.

Independent checks rerun the prior regressions and verify510 nonempty
qualifying degree families, the essential tie case,140 refined labelings,
560 core complements,560 third replacements,12 normalized28 cliques,
six equal31 and18 unequal32 labels. The prescribed-triple test covers
22 row graphs,44 replacement witnesses, and12 pair paths. These checks
are independent regressions; Python supplies no Lean oracle.
Evidence: validation/lean-joint-maximal-final-{build,axioms}.txt,
validation/lean-joint-maximal-final-audit.json, and
validation/joint-maximal-independent.json.

TeX pass441 has246 pages and21,256 source lines, without warnings or box
issues. Pages224,225,234,235,245,246 were rendered and visually checked.
The exact mathematical theorem remains Proposition9.82 on page213.
The live fragment passes static checks, without a browser-render claim.
The verified count is56/82 milestones (68.3% by count, not effort).
Next is TeX9.57, the initial cases of Wang4.13. Its full proof is read and
the plan distinguishes the actual two terminal chains from a four-arm
star, which is not available here because Y need not meet r.
Main theorem absent and unproved. Goal active; no blocker.

## 2026-08-27: initial cases of Wang4.13, TeX9.57 complete

JointFinal.Core.initial_cases applies to an arbitrary outside block with
at least nine arm contacts. It bounds both terminal rows by two and proves
the exact nine-contact, common-triple conclusion when the old terminal
row is zero or the complementary core block has the same edge count.
The Core structure is constructed by the previously proved maximal-core
selection. It does not assume the optional pattern28 normalization, so
later alternate distinguished pairs are not restricted inadvertently.

Twelve new JointFinal modules add36 public results. Factor completions
prove P1 and P2 using actual selected-block partitions. The second terminal
is exposed in its actual chain centered at the original second triangle
vertex; no edge from that terminal to the old center is assumed. The
terminal-degree arguments exclude universal/full/three-contact rows,
including both possible diagonals. The zero-leaf case proves the strict
crossing gain, and the equal-complement case constructs an actual strong
chain with both scores preserved before applying the common-triple lemma.

Full build and direct Lean exit0:599 proof modules plus Verification,
600 Lean files,9305 jobs,1248 ordered selected axiom reports. Only propext,
Classical.choice, and Quot.sound occur. All modules are reachable from
Verification and imports are acyclic. Source, computational-option,
Python syntax, audit, and whitespace checks pass. No new axioms,
placeholders, computational-limit changes, staging, commits, subagents,
or other-task edits.

Independent regression checks36 core models,82,944 factor completions,
144 exposed chains,112 equal-score exchanges,1,152 strict crossing gains,
262,144 row inputs,1,268 restricted states,eight excluded full-leaf states,
48 empty-leaf conclusion states,20 empty-leaf strict gains,24 equal-score
conclusion states,and48 matching gains. Exact four-cycles, partitions,
scores,and retained blocks are checked. Python is not a Lean oracle.
Evidence: validation/lean-joint-final-initial-{build,axioms}.txt,
validation/lean-joint-final-initial-audit.json,and
validation/joint-final-initial-independent.json.

TeX pass442 has246 pages and21,274 source lines, without warnings or box
issues. Pages224,225,234,235,245,246 were rendered and visually checked.
The exact mathematical theorem remains Proposition9.82 on page213.
Verified milestone count:57/82 (69.5% by count, not effort). Next is the
losing complementary block, TeX9.58; its complete proof has been read.
The main Lean theorem remains absent and unproved. Goal active; no blocker.

## 2026-08-27: losing complementary block, TeX9.58 complete

JointFinal.Core.losing_complement proves all clauses of the loss lemma.
Six JointLoss modules add18 public results. The strict edge loss forces
the exact countsA6,D5 and at most ten triangle contacts. Patterns27,29,30,
32,33,34 are excluded with their exact diagonal/refined-row consequences.
The two remaining patterns retain the original labels and do not assume
the optional28 normalization. Their complete auxiliary block is explicit.

ProhibitionA uses a selected-block partition with a four-vertex remainder
containing the proposed triangle. For the original terminal, the actual
chain is presented with the specified paw; for the second terminal, the
proved exposed chain retainsA,J and the original triangle. ProhibitionB
completes an arbitrary four-arm factor with the tertiary core complement
andQ-Y+b, retaining every unselected block. ProhibitionL checks both
terminals and both orders of the distinguished vertices in every cyclic
labeling. The exposed28 branch applies the complete-core variant and
does not invent center contacts. These proofs need no extra optimization
or assumed form of Claim2.4.

An initial broad propositional tactic hit the unchanged default heartbeat
bound. Replacing that set-permutation step with three explicit finite-set
identities resolved it. No computational options or limits changed.
Full build and direct Lean exit0:605 proof modules plus Verification,
606 Lean files,9311 jobs,1266 ordered selected axiom reports. Only propext,
Classical.choice, and Quot.sound occur. All modules are reachable from
Verification, imports are acyclic, and all source/option/whitespace scans
and Python syntax checks pass. No placeholders, new axioms, staging,
commits, subagents, or other-task edits.

Independent checks cover128 source inputs,23 allowed rows,ten refined low
rows,four losing rows,84 two-neighbor core factors,16 actual exposures,
13,440 triangle-partition trials,6,656 strict triangle gains,5,040 four-arm
factor completions,and1,536 low-pattern hypothesis checks. The latter
split768 old-original,192 exposed-original,and576 exposed-complete cases.
All cycles have exactly four vertices; supports,scores,and retained blocks
are checked. Python supplies no Lean oracle.
Evidence: validation/lean-joint-loss-final-{build,axioms}.txt,
validation/lean-joint-loss-final-audit.json,and
validation/joint-loss-independent.json.

TeX pass443 has246 pages and21,288 source lines, without warnings or box
issues. Pages224,225,234,235,236,245,246 were rendered and visually checked.
The exact mathematical theorem remains Proposition9.82 on page213.
The verified count is58/82 milestones (70.7% by count, not effort).
Next is the opposite-pair bounds, TeX9.59. The main Lean theorem remains
absent and unproved. Goal active; no blocker.

## 2026-08-27: opposite-pair bounds, TeX9.59 complete

JointFinal.Core.opposite_pair_bounds proves all five inequalities for
either distinguished order and every cyclic labeling with the required
three positive contacts. Core.exists_opposite_pair_labels chooses the
heavier row and such an actual cycle labeling; the full-row case is
retained. The proof works for the original Core and positive old-leaf,
nine-contact hypotheses without using the additional strict loss premise.

Seven JointPair modules add25 public proved results. PairRows is an
explicit record of row degrees and the six asymmetric insertion
prohibitions, constructed from the actual Core. No row classification
is assumed. Explicit four-cycle paths and finite sums prove the low
pair bounds. The high-pair argument supplies the actual original and
exposed strong chains to the previously proved direct-core corollary.
The reflection is(v.rotate2).reverse, preserving the middle neighbor
and low diagonal. The triangle neighbor and distinct replacer are the
original center and third vertex; they need not be the exposed center.
The forced low diagonal then gives universal distinguished replacement,
and the proved finite row sums contradict seven required contacts.

Full build and direct Lean exit0:612 proof modules plus Verification,
613 Lean files,9318 jobs,1291 ordered selected axiom reports. Only propext,
Classical.choice, and Quot.sound occur. All modules are reachable from
Verification, imports are acyclic, and source/option/whitespace scans and
Python syntax checks pass. No new axioms, placeholders, computational
limits, staging, commits, subagents, or other-task edits.

Independent regression covers32,768 normalized row inputs,64 insertion
masks,64 opposite-pair paths,16 universal-row paths,and64 degree splits.
There are282 admissible row states and64 direct obstruction witnesses;
226 states remain after excluding all high-pair witnesses. The actual
core check has2,048 applications and factors:1,536 old,512 exposed,
with384 using the reflected labels. The93 heavier-row choices have360
included-three labeling witnesses,including29 full-row choices. Exact
four-cycle partitions, both scores on exposure, and retained blocks are
checked. The prior loss regression is rerun. Python is not a Lean oracle.
Evidence: validation/lean-joint-pair-final-{build,axioms}.txt,
validation/lean-joint-pair-final-audit.json,and
validation/joint-pair-independent.json.

TeX pass444 has246 pages and21,301 source lines, without warnings or box
issues. Pages225,226,234,235,245,246 were rendered and visually checked.
The mathematical main theorem remains Proposition9.82 on page213.
Verified count:59/82 milestones (72.0% by count, not remaining effort).
Next is the exact three-neighbor distinguished row, TeX9.60. The main
Lean theorem remains absent and unproved. Goal active; no blocker.

## 2026-08-27: three-neighbor distinguished case, TeX9.60 complete

JointFinal.Core.three_distinguished_conclusion proves the exact common
triple and nine-contact conclusion for every qualifying outside block
when both original distinguished degrees are at most three. The heavier
chosen row then has degree exactly three. The original Core, strict
primary loss, and positive old-terminal hypothesis are retained.
Neither the local source classification nor Claim2.4 is assumed.

Thirteen JointThree modules add39 public results. FinalRows records only
already proved restrictions, with Core.final_rows supplying its actual
construction. The low diagonal is excluded by universal insertion and
row coverage. Every two-contact terminal row is one of the two adjacent
pairs within the distinguished triple; the excluded pairs use actual
triangles, disjoint five-edge quadrilaterals, and the low obstruction.
Two identical terminal pairs give the explicit cycles(X,v0,Y,v1) and
(z,v2,v3,w). The two different pairs lead to triangle gains in the correct
Y or X seven-set, excluding old-terminal degree two. The final obstruction
uses the exposed terminal, reversed cyclic labels, and swapped distinguished
order. Rotation gives the required common triple and exposed neighbor.

Full build and direct Lean exit0:625 proof modules plus Verification,
626 Lean files,9331 jobs,and1330 ordered selected axiom reports. Only
propext,Classical.choice,andQuot.sound occur. Every new public result is
selected; all modules are reachable and imports acyclic. Source/option
scans,Python syntax,and all-source whitespace checks pass. The only
intermediate errors were finite-set ordering and an unused-instance
warning; they were corrected without changing computational limits.
No placeholders,new axioms,staging,commits,subagents,or other-task edits.

Independent regression checks16,384 normalized inputs,98 admissible row
states,68 triangle-gain witnesses,16 two-cycle-factor witnesses,and16
low-pattern witnesses (these classes can overlap). The12 surviving rows
have degrees1,2,3,3 and the required common triple;48 cyclic conclusion
labels cover both original distinguished orders. The two positive
five-edge constructions are checked on all64 four-vertex graphs,192
triangle partitions are checked under all dihedral labels and outside
orders,and the explicit old/final gains and parallel factors are checked.
Prior pair and loss regressions rerun unchanged. Python supplies no Lean
oracle; the arbitrary-graph theorem is proved directly in Lean.
Evidence: validation/lean-joint-three-final-{build,axioms}.txt,
validation/lean-joint-three-final-audit.json,and
validation/joint-three-independent.json.

TeX pass445 has246 pages and21,318 source lines,without warnings or box
issues. Pages195,196,225,226,234,235,245,246 were rendered and visually
checked. The mathematical main remains Proposition9.82 on page213.
Verified count:60/82milestones (73.2% by count,not remaining effort).
Next is the full-row configuration,TeX9.61,then its exclusion and Claim2.4.
The main Lean theorem remains absent and unproved. Goal active;no blocker.

## 2026-08-27: full-row configuration, TeX9.61 complete

JointFinal.Core.exists_full_distinguished_pattern selects the exact full-row
configuration when either original distinguished row has degree four.
The actual cyclic labels have rows1,6,15,6,present high diagonal,absent low
diagonal,and exactly nine contacts. The original Core,strict loss,and
arbitrary qualifying outside block are retained. This proves the source
classification; the configuration's exclusion in9.62 remains unproved.

Five JointFull modules add16public results. The full row is universally
replaceable,so P1 makes the old-terminal and other distinguished rows
disjoint. Rotations and reversals preserve all proved restrictions and
normalize every old-terminal adjacent pair. The actual insertion path
excludes the required diagonal; the existing triangle-gain/low-pattern
obstruction then gives degree one. Finite row sums force the two remaining
degrees and total nine. The other distinguished row and exposed terminal
are normalized in the exact cyclic orders,with no new center adjacency.
The final disjoint triangle and five-edge quadrilateral use the corrected
last vertex from the TeX proof. FullPattern records only actual adjacency
rows and the two diagonal conditions; no classification is assumed.

Full build and direct Lean exit0:630proof modules plus Verification,
631Lean files,9336jobs,and1346ordered selected axiom reports. Only
propext,Classical.choice,andQuot.sound occur. Every new public result is
selected; all modules are reachable and imports acyclic. Source/option
scans,Python syntax,and all-source whitespace checks pass. One broad
simplifier reached the default recursion limit; targeted simplification
resolved it without changing any computational limit. No placeholders,
new axioms,staging,commits,subagents,or other-task edits.

Independent regression covers16,384normalized inputs,128admissible states,
96gain,24factor,and24low-pattern witnesses (overlapping classes). The eight
surviving states have exactly the stated full-row pattern,with16labels
across both original distinguished orders. Twelve old-terminal orientations,
six exposed-terminal gains,and two corrected final partitions are checked.
The printed repeated vertex is detected as an actual overlap. Earlier
three-neighbor,pair,and loss regressions rerun unchanged. Python supplies
no Lean oracle; the arbitrary-graph theorem is proved directly in Lean.
Evidence:validation/lean-joint-full-pattern-final-{build,axioms}.txt,
validation/lean-joint-full-pattern-final-audit.json,and
validation/joint-full-pattern-independent.json.

TeX pass446 has246pages and21,330source lines,without warnings or box
issues. Pages195,196,225,226,234,235,236,245,246 were rendered and visually
checked. The mathematical main remains Proposition9.82 on page213.
Verified count:61/82milestones (74.4% by count,not remaining effort).
Next is the full-row exclusion,TeX9.62,then the local classification and
Claim2.4. The main Lean theorem remains absent and unproved. Goal active;
no blocker. The preceding three-neighbor checkpoint is preserved at
`tmp/erdos577/progress-history-before-joint-full-pattern.md`.

## 2026-08-27: full-row exclusion and local classification, TeX9.62–9.63 complete

JointFinal.Core.full_pattern_false excludes the exact remaining full-row
configuration; Core.full_distinguished_false applies in either original
distinguished order. Core.local_conclusion then proves the nine-contact
common-triple conclusion for every qualifying outside block, with no added
loss, positive-terminal, or classification hypothesis. This completes the
local source Lemma4.13. Claim2.4 and the exact main theorem remain unproved.

Thirteen modules add23 public results. The two actual terminal exposures
preserve the original triangle, both scores, and unselected blocks. The
low new terminal is only required to be Feasible: it has no assumed old
triangle attachment. Its unique core neighbor and first-block degree bound
follow by actual packing contradictions. The separate inside bounds35,7,4
sum to46 on six distinct vertices. Finite averaging supplies the outside
thirteen-contact block, also handling an empty remaining block family.
Both feasible-terminal routes and the original maximizing family prove
the paw bound8. The two exact five-cycle partitions complete the exclusion.
The universal classification assembles the proved zero/equal/three/full
cases without assuming a desired conclusion or a later source claim.

Full build and direct Lean exit0:643 proof modules plus Verification,
644 Lean files,9349 jobs,and1369 ordered selected axiom reports. Only
propext,Classical.choice,andQuot.sound occur. All23 new public results are
selected. Every module is reachable from Verification; imports are acyclic.
Source/option scans,Python syntax,git diff --check,and explicit whitespace
checks of all untracked Lean/TeX files pass. All current Lean sources and
the TeX have hashes in the audit. No placeholders,new axioms,computational
limit changes,staging,commits,subagents,or other-task edits were introduced.

The independent regression checks512 actual exposures,2816 first-block
neighbor trials with6400 factors,2048 lifted five-cycle factors,and32704
inside graphs attaining35,7,4,46. It checks16384 outside-row inputs,1336
admissible universal cases,1376 local factors in each terminal direction,
six maximal-core numerical cases,and all four local classification routes.
The earlier full-pattern,three-neighbor,pair,and loss regressions rerun
unchanged. These fixtures check positive constructions and finite identities;
they are not claimed globally feasible or minimum-degree graphs. An initial
inside fixture allowed a forbidden Y–t edge through the first-block mask.
Restricting that mask to respect the prescribed FullPattern row corrected
the fixture; no Lean theorem or mathematical hypothesis was changed.
Python supplies no proof oracle. The arbitrary-graph results are Lean proofs.

Evidence:validation/lean-joint-full-exclusion-final-{build,axioms}.txt,
validation/lean-joint-full-exclusion-final-audit.json,and
validation/joint-full-exclusion-independent.json. TeX pass447 has247 pages
and21350 source lines,without warnings or box issues. Pages196,197,225,226,
235,236,237,246,247were rendered and visually checked. The mathematical
main remains Proposition9.82 on page213. Verified count:63/82milestones
(76.8% by count,not remaining effort). Next is Claim2.4,TeX9.64.
The goal stays active; no blocker is present. The preceding full-pattern
checkpoint is preserved unchanged at
`tmp/erdos577/progress-history-before-joint-full-exclusion.md`.

## 2026-08-27: Wang Claim2.4, TeX9.64 complete

TriangleChain.Feasible.claim_two_four proves the sum bound6 for both
original noncentral paw labels. It retains the original order,minimum
degree,absence-of-packing,feasible-chain,paw-presentation,and block
hypotheses. No later source claim or assumed classification is used.

Eight new modules add14 public results. The original common triple gives
an exact factor in the actual exposed chain whenever b meets either
distinguished core vertex. Its complementary block is the original
tertiary block. The two missing edges force at most ten triangle contacts,
and the refined source rows leave only27/28. Their reversal preserves
the exact source conditions; all clauses of the reversed Core, including
the new secondary complements and zero first-block rows, are proved.
The optional28 initial normalization is not imposed on the reversed pair.

The universal local conclusion bounds the first classified block by9.
The inside budget31 then gives a distinct second heavy block, including
the empty-family contradiction. Two independent replacements partition
the exact twelve-vertex set into three quadrilaterals. The complementary
four-clique and the actual exposed first block complete the five-cycle
factor. All unselected blocks are retained. Core.impossible assembles
both classifications, and the existing maximal reduction restores the
two original noncentral bounds.

Full build and direct Lean exit0:651 proof modules plus Verification,
652 Lean files,9357 jobs,and1383 ordered selected axiom reports. Only
propext,Classical.choice,andQuot.sound occur. All14 new public results are
selected; every module is reachable and imports are acyclic. Source and
option scans,Python syntax,and all-source whitespace checks pass. A broad
propositional tactic hit the default heartbeat limit; explicit finite-set
rewrites replaced it. No computational limit was changed. No placeholders,
new axioms,staging,commits,subagents,or other-task edits were introduced.

Independent regression covers128 rows,the three remaining source rows,
24 reversed cores,192 core complements,96 actual exposures,4096 missing-edge
four-cycle factors,6144 final five-cycle factors,and180 extra-diagonal
variants. The eight reversed28 two-neighbor cases have row{0,3},not the
optional initial row{0,1}. Both scores,exact supports,unselected blocks,
both original failure routes,and the empty family are checked. Positive
fixtures are not claimed globally feasible or minimum-degree graphs;
Python supplies no Lean oracle. All previous regressions rerun unchanged.

Evidence:validation/lean-claim-two-four-final-{build,axioms}.txt,
validation/lean-claim-two-four-final-audit.json,and
validation/claim-two-four-independent.json. TeX pass448 has247 pages and
21366 source lines,without warnings or box issues. Pages197,198,225,226,
236,237,246,247were rendered and visually checked. The mathematical main
remains Proposition9.82 on page213. Verified count:64/82milestones
(78.0% by count,not remaining effort). Next is pattern12's exclusion in9.65
and Claim2.5 in9.66. The main Lean theorem remains absent and unproved;
the goal is active with no blocker. The prior progress log is preserved at
`tmp/erdos577/progress-history-before-claim-two-four-complete.md`.

## 2026-08-27 — weighted pattern12 and Claim2.5 complete (TeX9.65–9.66)

Twenty-one WeightedTwelve modules plus ClaimTwoFive prove the remaining
pattern exclusion and the seven-contact conclusion for the original paw
labels. Both original first-block diagonals are included. The local
involution is an actual paw and quadrilateral exchange, preserving the
five-set, both scores, and every unselected block. It is not assumed to
be an automorphism of the full graph.

The exact inside19 count gives the first heavy block. Both full-leaf
factor contradictions and Claim2.2 force the two leaf rows to vanish,
and the block is complete with at least11 triangle contacts. Every edge
from the first block to the dense core is excluded by an actual factor.
The dense-pair labels use cyclic indices2,3, with0,1 in the complete
complement. The new strong chain is explicitly constructed and has both
scores unchanged. No extra triangle contact is silently assumed.

The inside20 bound gives the second heavy block. All three common-neighbor
insertions have exact cycle completions, including both mixed pairs.
The original exposed strong chain suffices to make its terminal universal;
the intermediate terminal need not attach to the newly exchanged triangle.
Both small-leaf bounds and the actual matching-score obstruction supply
every premise of the common-triple lemma, including the zero-leaf branch.
Both choices of the old third vertex's distinguished neighbor give the
final partial factor. Its complement is a four-cycle by the previously
proved dense-seven-set theorem. The exposed first block completes the
four-cycle factor and retains all other blocks. Claim2.5 restores exact
equal neighbor filters and noncentral degree sum6, or the explicit zero leaf.

Full build and direct Lean exit0:673 proof modules plus Verification,
674 Lean files,9379 jobs,and1443 ordered selected axiom reports. All60
new public declarations are selected; only propext,Classical.choice,and
Quot.sound occur. Imports are acyclic and every module is reachable.
Source/placeholder/option scans,Python syntax,and all-source whitespace
checks pass. A large insertion proof reached the default heartbeat limit;
named proved sublemmas and explicit set rewrites fixed it without changing
any computational limit. No placeholders,new axioms,staging,commits,
subagents,or other-task edits were introduced.

Independent construction checks cover312 dense-label inputs,168 valid
dense-pair models,1008 actual exchanges,336 inside bounds with maximum20,
416 cross-contact factors,96,768 insertion factors,and204,288 final
four-cycle factors. Both distinguished-contact choices,95 extra-chord
variants,the unattached intermediate terminal,and empty outside families
are checked. Previous Claim2.4 regressions rerun unchanged. These positive
fixtures are not claimed globally feasible or minimum-degree graphs;
Python supplies no Lean oracle.

Evidence: validation/lean-claim-two-five-final-{build,axioms}.txt,
validation/lean-claim-two-five-final-audit.json,and
validation/weighted-twelve-independent.json. TeX pass450 has247 pages,
21400 source lines,and no warnings or box issues. Pages198,199,225,226,
227,236,237,247 were rendered and visually checked. Proposition9.82
remains on page213. The verified count is66/82 (80.5% by milestone count,
not an effort estimate). The exact main Lean theorem remains absent and
unproved. The goal is active with no blocker. Next is TeX9.67, the
two-exposed-leaf lemma. Checkpoint64's log is preserved unchanged at
`tmp/erdos577/progress-checkpoint64.md`.

## 2026-08-27 — two exposed leaves and corrected Wang4.14 complete (TeX9.67–9.68)

Eight TwoExposed modules and LeafTransport prove both complete statements.
PawPair records the actual interchanged centers and common triangle with
distinct leaves. Its symmetry exchanges the two given chains and labels;
their other blocks need not agree, and no whole-graph automorphism is used.
Claim2.2 transfers its outside-vertex factor through the other chain.
The zero-leaf alternative forces both leaves zero; otherwise both have
degree at least3 and one is full.

For the ordered full leaf, Claim2.5 gives both weighted bounds6. The
zero-third-row case has exact degrees1,3,3. The actual replacement at
the unique noncentral neighbor preserves both block scores and gives
new leaf and noncentral degrees4, contradicting Claim2.4. In the positive
case, the two weighted inequalities directly imply the two degree-one
rows and a positive center row. This also covers the printed separate
degree-two exclusion. Three disjoint neighbor rows and the fourth block
vertex give the stated exact two-cycle factor, retaining every other block.

The transport theorem constructs both score-preserving routes and retains
the common block. In the bridge route the second replacement is explicitly
Q-z+y, where z belongs to Q; it is not performed in the dense block A.
The intermediate terminal requires no triangle attachment. Either original
noncentral neighbor is handled by actual paw relabeling, restoring the
original five-set and triangle in the result. The result applies to any
feasible chains with the stated paw and attachment data; no later claim
or unexplained source oracle is assumed.

Full build and direct Lean exit0:682 proof modules plus Verification,
683 Lean files,9388 jobs,and1470 ordered selected axiom reports. All27
new public declarations are selected; only propext,Classical.choice,and
Quot.sound occur. All modules are reachable and imports are acyclic.
Source/placeholder/option scans,Python syntax,and all-source whitespace
checks pass. No computational limits,other-task files,or source papers
were changed. No staging,commits,subagents,or placeholders were introduced.

Independent checks cover192 zero-row exchanges,240 positive two-cycle
factors,240 added-chord variants,the three scalar cases,13 dense cores,
156 direct routes,and936 bridge routes. They verify both original
noncentral choices,pair symmetry,both scores,exact supports,different
other-block families,and all retained blocks. The bridge intermediate
terminal is explicitly unattached. The fixtures are positive construction
checks,not globally feasible or minimum-degree graphs; Python is not a
Lean oracle. Previous Claim2.5 regressions rerun unchanged.

Evidence: validation/lean-two-exposed-final-{build,axioms}.txt,
validation/lean-two-exposed-final-audit.json,and
validation/two-exposed-independent.json. TeX pass452 has248 pages,
21424 source lines,and no warnings or box issues. Pages200,201,226,227,
237,238,247,248 were rendered and visually checked. Proposition9.82
remains on page213. Verified count:68/82 (82.9% by milestone count,
not remaining effort). The exact main Lean theorem is still absent
and unproved. The goal remains active with no blocker. Next is the
nonvacuous dense-pair obstruction,TeX9.69/corrected Wang4.15.
Checkpoint66's log is preserved unchanged at
`tmp/erdos577/progress-checkpoint66.md`.

## 2026-08-27 — nonvacuous dense-pair obstruction complete (TeX9.69)

RawCoreCompletion and nine DensePair modules prove corrected Wang4.15.
The printed incompatible premise requiring at least3 original leaf
contacts with the dense block is absent. PairConfig.leaf_zero separately
proves that the row is zero from the actual dense core. No extra leaf
degree or exposed-vertex triangle attachment is assumed in the final theorem.

The cyclic source labels are d=(a4,a3,a1,a2). Reversal fixes d2=a1
and exchanges the pairs(a1,a2),(a1,a3), preserving the whole core support.
The strong pair chains and their complete complements are actual local
replacements with both scores unchanged. A raw triangle-chain completion
handles the exposed terminal even without a paw. All three insertion
obstructions are completed by explicit cycle partitions. The actual
exposed feasible chain proves the terminal row bound2; Claim2.5 supplies
the zero-leaf or equal-three-row alternatives in the pair chain. Its
matching-score bound supplies the other common-triple premise.

The common-triple theorem is universal over qualifying outside blocks.
It bounds the second row sum on the first selected block by9, giving
inside31 and a distinct second block. The five-cycle factor retains all
unselected blocks. Its final triangle-plus-a4 set only needs the cycle
(a4,b,r,c); it is not assumed complete, since r–a4 may be the missing edge.

Full build and direct Lean exit0:692 proof modules plus Verification,
693 Lean files,9398 jobs,and1494 ordered selected reports. All24 new
public declarations are selected; only propext,Classical.choice,and
Quot.sound occur. All modules are reachable and imports are acyclic.
The682 previously verified proof modules have unchanged hashes.
Source/placeholder/option scans,Python syntax,and all-source whitespace
checks pass. No computational limits,other-task files,or source papers
were changed. No staging,commits,subagents,or placeholders were introduced.

Independent positive checks cover312 label inputs,96 paired dense cores,
3360 four-subsets,20 first-block cases,11,520 equal-score exchanges,
55,296 insertion factors,and20,736 final five-cycle factors. These include
5184 noncomplete final triangle complements and324 added-chord variants.
Both pairs,scores,exact supports,retained blocks,and the unattached
exposed terminal are checked. The prior small-core regression is rerun.
The script documents its sampled cross-products; these fixtures are not
claimed globally feasible or minimum-degree graphs. Python is not a Lean oracle.

Evidence: validation/lean-dense-pair-final-{build,axioms}.txt,
validation/lean-dense-pair-final-audit.json,and
validation/dense-pair-independent.json. TeX pass454 has249 pages,
21451 source lines,and no warnings or box issues. Pages200,201,213,226,
227,238,239,249 were rendered and visually checked. Proposition9.82
remains on page213. Verified count:69/82 (84.1% by milestone count,
not remaining effort). The exact main Lean theorem is still absent
and unproved. The goal remains active with no blocker. Next is TeX9.70,
the full- and three-leaf preparations. Checkpoint68's log is preserved at
`tmp/erdos577/progress-checkpoint68.md`.

## 2026-08-27 — both large-leaf preparations complete (TeX9.70)

Fifteen LargeLeaf modules prove both complete statements in the original
graph and original noncentral labels. The first step bounds every first-block
vertex by one contact into a dense seven-set and gives simultaneous actual
core labels. In the full-leaf branch, the ordered2,0 noncentral case has
center degree0 by Claims2.3–2.5. The five-row inside19 average and transport
supply a dense block. Center neighbors in that block have zero contacts
with the first block: occupied columns violate the core bound, and other
columns yield an explicit three-cycle factor. Both inside22 bounds feed
the proved nonvacuous dense-pair obstruction. The resulting degree-at-most-one
bound is universal before its application to an actual changed-center chain.
That new original-center row has old degree plus1, forcing the old row0.
Both scores are preserved and the dense block is obtained by the same average.

In the three-leaf branch, three occupied triangle columns leave at most
one first-block--core edge. The core pair contributes at most13 inside,
so both inside22 estimates hold. The dense-pair obstruction forbids every
compatible equal-score replacement. The first and low-column score
comparisons force both diagonals, then a degree2 row through the missed
leaf column. The split-row factor excludes all dense outside blocks.
Only after that exclusion is the five-row transfer applied to occupied
columns. It excludes the missed leaf column and forces the remaining
diagonal. Exact set cardinalities fill the three leaf columns. A split
noncentral row again gives the explicit two-cycle factor. The final
neighbor filters are equal to the leaf's filter and empty in either
original noncentral order. No later claim or classification oracle is used.

Full build and direct Lean exit0:707 proof modules plus Verification,
708 Lean files,9413 jobs,and1524 ordered selected reports. All30 new
public declarations are selected, with only propext,Classical.choice,
and Quot.sound. Imports are acyclic and all modules are reachable.
The692 prior proof modules have unchanged hashes. Source/placeholder/
option scans,Python syntax,and all-source whitespace checks pass. No
computational limits,source papers,or other-task files were changed.
No staging,commits,subagents,or placeholders were introduced.

Independent checks cover13,104 two-neighbor core factors,52 leaf-core
factors,12 five-row sums,56 changed-center exchanges,4320 cross-contact
factors,18,432 full-leaf inside estimates,and36,864 three-leaf inside
estimates. Both inside maxima are22. There are48 low-column equal-score
replacements,168 two-row low replacements,three no-compatible shapes,
six split-row factors,and32 occupied-column inputs with four final local
shapes. Both noncentral orders,scores,supports,and retained blocks are
checked. The prior dense-pair regression is rerun. Sampled products are
explicitly documented; fixtures are not claimed globally feasible or
minimum-degree graphs, and Python supplies no Lean oracle.

Evidence: validation/lean-large-leaf-final-{build,axioms}.txt,
validation/lean-large-leaf-final-audit.json,and
validation/large-leaf-independent.json. TeX pass456 has249 pages,
21484 source lines,and no warnings or box issues. Pages201,202,203,213,
227,228,238,239,249 were rendered and visually checked. Proposition9.82
remains on page213. Verified count:70/82 (85.4% by milestone count,
not remaining effort). The exact main Lean theorem is still absent and
unproved. The goal remains active with no blocker. Next is TeX9.71,
the full-leaf core restrictions. Checkpoint69's log is preserved at
`tmp/erdos577/progress-checkpoint69.md`.

## 2026-08-27: TeX9.71 full-leaf core restrictions complete

The ten FullLeafCore modules prove the actual labeled setting and all
four prohibitions. Configuration assumes only the feasible chain,paw,
distinct blocks,full leaf row,marked noncentral edge,and dense contacts.
Every first-five vertex is an actual feasible terminal preserving both
scores and retaining the other blocks. The raw core completion proves
the arbitrary-triple prohibition without a terminal attachment premise.
The two-neighbor insertion is completed by the actual seven-core factor.

The explicit bridge(X,r,b,Y) has a disjoint support partition with each
second-five local factor. It proves the reverse matching degree bound;
the first bound comes from the core column restriction. Matching
uniqueness is proved at both endpoints. Both center degree lower bounds
are derived from the dense triangle rows and the common third vertex.
The two common-neighbor prohibitions each close an actual three-vertex
path,then use the dense complementary four-set and the retained blocks.

The interchange constructs the actual strong chain and paw(Y,b,r,c),
with complete first blockQ-Y+X. Both original scores are equal. The
triangle,first triple,both five-sets,twelve-set,and every further block
are unchanged. The marked vertices have unique core neighborsr,b,
so both have zero contacts withZ2. This proves the additional objective
equality before maximality is transferred. The maximizing configuration
is an attained value of the finite set0 through20,not an assumed oracle.
Its actual strong paw presentation is proved. The initial configuration
comes from TeX9.70 with either original noncentral labeling.

Full build and direct Lean exit0:717 proof modules plus Verification,
718 Lean files,9423 jobs,and1578 ordered reports. All54 new public
declarations are selected,and only propext,Classical.choice,Quot.sound
occur. All task modules are reachable; imports are acyclic. All707
previous proof modules and the principal PDF retain their exact hashes.
Source/placeholder/option/native-evaluation and all-source whitespace
checks pass. No computational limits,other-task files,or source papers
were changed. No staging,commits,subagents,or placeholders.

Independent construction checks cover52 core geometries,260 terminal
presentations,21,840 first insertions,9100 first arbitrary-triple factors,
780 second-triple factors,260 second general factors,3120 second
insertions,and3904 common-neighbor factors for each center. All7072
matching/score variants are checked. Every factor is tested in both
original noncentral labelings. All13 dense cores and all4 marked first
vertices are used. Exact supports,all three scores,and retained blocks
are checked. General factor fixtures use documented deterministic splits,
not all possible factors. The previous large-leaf regression is rerun.
Fixtures are not claimed globally feasible or minimum-degree graphs;
Python supplies no Lean oracle.

Evidence: validation/lean-full-leaf-core-final-{build,axioms}.txt,
validation/lean-full-leaf-core-final-audit.json,and
validation/full-leaf-core-independent.json. TeX pass457 has250 pages,
21514 source lines,and no warnings or box issues. Pages203,204,213,227,
228,239,240,250 were rendered and visually checked. Proposition9.82
remains on page213. Verified count:71/82 (86.6% by milestone count,
not effort). Claims2.6–2.7 and the exact main Lean theorem remain
unproved. The goal stays active with no blocker. Next is TeX9.72,the
two heavy-block types; its plan is full-leaf-heavy-implementation-plan.md.
Checkpoint70's log is preserved at tmp/erdos577/progress-checkpoint70.md.

## 2026-08-27: high-row and opposite-pair branches of TeX9.72 complete

Sixteen FullLeafHeavy modules add40 proved public declarations. The
high-first-row branch gives the complete block,at least9 first-triple
contacts,and both second-side matching bounds. The two removable clique
vertices and the exact upper bound8 for two low columns are explicit.
Universal replacement is never identified with degree4 without proof.

The opposite-pair inequalities give second sum11–12,high-column sum≥9,
first sum≥9,and first-triple sum≥5. They exclude every universal second
row and select a degree3 row. The both-low subcase uses a proved crossing
count,the prescribed-edge dense-core triangle extension,and two actual
complete blocks. Its exact triangle remainder forcesJ complete,which
contradicts nonuniversality directly. Thus the Lean proof does not need
the source's intermediate missing-diagonal premise in this subcase.

For the consecutive triple,every hypothesis of the earlier corrected
CoreTransfer.core_obstruction is derived. Every A vertex has≥2 triangle
neighbors,and the distinct universally replaceable triangle vertex is
chosen. The original complete block gives the actual equal-score bridge;
R3 bounds its two low columns by2 each. Cycle reversal,the high-index
exchange,and the actual marked-leaf interchange cover every original
labeling. The final no_opposite_first_pair statement has no leaf-order
or cycle-orientation hypothesis.

The general insertion complement is exactly{x}+(J-v). Separate selected
score theorems bound the actual two-block partition by6+e(J) for a
triangle remainder and7+e(J) for a matching remainder. They are ready
for the adjacent-pair proof; that branch is not claimed complete.

Full build and direct Lean exit0:733 proof modules plus Verification,
734 Lean files,9439 jobs,and1618 ordered reports. Only propext,
Classical.choice,and Quot.sound occur. All40 new declarations are
selected,all modules reachable,and imports acyclic. All717 prior proof
modules and the principal PDF retain their hashes. Source/placeholder/
option/native and all-source whitespace scans pass. No limits,other-task
files,source papers,staging,commits,subagents,or placeholders changed.

Independent checks cover126 prescribed-edge triangle extensions,4160
two-complete-block partitions,and4160 comparisons for each remainder
type. Exact score gains0,1,2 distinguish the two allowances. There are11
removable-row cases,384 low-column bounds,3289 high-row local factors,
374 crossing matrices,10 admissible opposite count vectors,and both
consecutive degree3 masks. All13 dense cores occur in the core/score
checks. The local matrices are exhaustive; the high-row factor check
uses a documented fixed complete core and marked vertex. The previous
full-leaf-core regression is rerun. These are positive construction
fixtures,not globally feasible or minimum-degree examples,and no
Python result is used by Lean as an oracle.

Evidence: validation/lean-heavy-opposite-final-{build,axioms}.txt,
validation/lean-heavy-opposite-final-audit.json,and
validation/heavy-opposite-independent.json. TeX pass461 has250 pages,
21536 source lines,and no warnings or box issues. Pages204,205,206,213,
227,228,239,240,250 were rendered and visually checked. Earlier passes
458–460 had an underfull table paragraph and are superseded by461.
Milestone count stays71/82: the adjacent-pair and degree-one branches,
the full heavy-block classification,Claims2.6–2.7,and the exact main
Lean theorem remain unfinished. No blocker. Continue with
tmp/erdos577/full-leaf-adjacent-implementation-plan.md. The previous
checkpoint is preserved at tmp/erdos577/progress-checkpoint71.md.

## 2026-08-27: adjacent-case preparation in TeX9.72 verified

FullLeafHeavyAdjacentLabels adds six public declarations. An actual
first row of degree2 is adjacent by the proved opposite-pair exclusion.
If the block were complete,an explicit interchange of its middle labels
would make the two neighbors opposite. Thus its edge count is≤5.
The first-side bound10 gives second-side contacts≥11. Rotation followed
by reversal exchanges the opposite column pairs while preserving the
adjacent first row,selecting a pair with≥6 contacts. The combined theorem
Configuration.adjacent_heavy_preparation preserves the exact support.
The lower edge bound5 and diamond exclusion are still pending.

Full build and direct Lean exit0:734 proof modules plus Verification,
735 Lean files,9440 build jobs,and1624 ordered selected reports. Only
propext,Classical.choice,and Quot.sound occur. All six new declarations
are selected,all modules reachable,and imports acyclic. All733 previous
proof modules and the principal PDF retain their hashes. Placeholder,
option,native-evaluation,and full-source whitespace scans pass.

Independent checks cover192 cycle row labelings,144 complete-graph
opposite labelings,575 heavy column vectors,and1215 heavy row-count
inputs. All four diagonal choices,exact support,and preservation of the
adjacent row are checked. These fixtures are not claimed globally
feasible or minimum-degree graphs. They are not Lean oracles.

Evidence: validation/lean-adjacent-labels-{build,axioms}.txt,
validation/lean-adjacent-labels-audit.json,and
validation/adjacent-labels-independent.json. TeX pass462 has250 pages,
21540 source lines,and no warnings or box issues. Pages227,228,239,240,
250 were rendered and viewed; the first213 pages have unchanged extracted
text. The Leanization map records the new preparation. The previous log
is preserved at tmp/erdos577/progress-checkpoint71-opposite.md.
Count stays71/82,with milestone72 partial and the exact main theorem
unproved. No blocker,limits changes,subagents,staging,or commits.

## 2026-08-27: the entire adjacent-pair branch of TeX9.72 is verified

Seven new modules from FullLeafHeavyAdjacentGeometry through
FullLeafHeavyAdjacentExcluded add25 selected public declarations.
The exact fifth-edge argument constructs both core blocks and both
possible remainders. Four contacts with both center rows full give two
complete blocks via the dense four-subset theorem. The alternative
second-set completeness supplies the otherwise missing neighbor edge.
The prescribed-edge triangle extension gives weight at least11.
Triangle and matching score comparisons retain distinct allowances.

After labeling the unique diagonal,the low-column bounds imply a
first-triple bound5 directly from the opposite-pair exclusion. A row
of degree2 missing the distinguished low vertex contradicts the heavy
sum via second≤11 and first≤9. Thus every such row meets the low vertex,
and its column bound improves the triple total to4. The second total
is≥13 and the distinguished column has≥3 neighbors. A common neighbor
is chosen distinct from the actual replacing row. Either of the two
original marked-center prohibitions now gives the contradiction,without
an extra marked-leaf swap. Configuration.first_rows_le_one restores
the arbitrary original labels and bounds all low-case first rows by1.

Full build and direct Lean exit0:741 proof modules plus Verification,
742 Lean files,9447 jobs,and1649 ordered reports. Only propext,
Classical.choice,and Quot.sound occur. All25 new declarations are
selected,and all modules are reachable with acyclic imports. All734
earlier proof modules and the principal PDF retain their hashes.
Forbidden-source,option,native-evaluation,and all-source whitespace
scans pass. No task warning or computational-limit change.

Independent checks cover all13 dense cores,25 four-contact splits,208
three-contact neighbor-edge cases,5018 heavy core pairs,12788 matching
and7284 triangle remainder partitions,10 low replacements,432 triple
bound5 and256 triple bound4 matrices,880 common-neighbor inputs,and8
final count inputs. The factor fixtures fix the marked leaf and vertex;
earlier opposite and label regressions are rerun. All four diagonal
choices and exact supports are checked. Fixtures are not claimed
globally feasible or minimum-degree graphs,and Python is no Lean oracle.

Evidence: validation/lean-adjacent-excluded-{build,axioms}.txt,
validation/lean-adjacent-excluded-audit.json,and
validation/adjacent-excluded-independent.json. TeX pass464 has250 pages,
21558 source lines,and no warnings or box issues. Pages227,228,229,239,
240,250 were rendered and viewed. The first213 pages have unchanged
extracted text. Pass463 had two underfull warnings,superseded by464.
The preceding progress log is preserved at
tmp/erdos577/progress-checkpoint71-adjacent-labels.md.
Count stays71/82: the final degree-one branch and type assembly remain.
Claims2.6–2.7 and the exact main Lean theorem are still unproved. No
blocker,staging,commits,subagents,source-paper changes,or limit increases.

## 2026-08-27: milestone72,the full heavy-block classification,complete

Five new modules from FullLeafHeavyLeafRowBounds through
FullLeafHeavyTypes add17 selected public declarations. Exact sums over
one and two erased vertices prove the sixteen-contact equality step.
A marked common neighbor forces one full row and every other row to
have degree3. Reversing the actual replacing/common rows in the center
prohibition yields a contradiction. Disjoint neighbor filters force
center degree4 and second contacts16 whenever a marked leaf is positive.

The heavy threshold then makes both marked leaves positive. Applying
both original center restrictions gives both center degrees4. Each
center has exactly three neighbors inA,contradicting the dense triangle
sum≥11. Thus both marked rows are zero. Second contacts≥18 give a full
row,and its actual replacements bound every first-triple column by1.
No additional marked-leaf interchange or maximizing premise is assumed.

Type40 and Type41 are defined by their actual degree conjunctions.
Configuration.heavy_types proves that every heavy further block has
one type. Configuration.heavy_types_disjoint proves their second-side
bounds≥18 and≤4 incompatible. This completes every branch and the full
conclusion of TeX9.72,so the milestone count advances to72/82.

Full build and direct Lean exit0:746 proof modules plus Verification,
747 Lean files,9452 jobs,and1666 ordered selected reports. Only propext,
Classical.choice,and Quot.sound occur. All17 new declarations are
selected. Every module is reachable; imports are acyclic. All741 earlier
proof modules and the principal PDF retain their hashes. No task warning.
Placeholder,option,native-evaluation,and all-source whitespace scans pass.

Independent checks cover12 row bounds,5 sixteen-contact equalities,
all13 dense cores,and594816 candidate marked-contact inputs. The80
models satisfying the actual local replacement restrictions have the
proved equality and disjointness properties. All four diagonal and
marked-column choices are checked. There are73 type40 matrices,501
type41 matrices,36573 pairs verifying type disjointness under the heavy
threshold,211 matrices of second total≥18,and5832 heavy type40 inputs
with actual full rows. Earlier adjacent,opposite,and label regressions
are rerun. Fixtures are not claimed globally feasible or minimum-degree
graphs,and no Python result is used by Lean as an oracle.

Evidence: validation/lean-full-leaf-types-{build,axioms}.txt,
validation/lean-full-leaf-types-audit.json,and
validation/full-leaf-types-independent.json. TeX pass465 has250 pages,
21573 source lines,and no warnings or box issues. Pages227,228,229,239,
240,250 were rendered and viewed; the first213 pages have unchanged
extracted text. The Leanization map records the completed classification.
The preceding log is preserved at
tmp/erdos577/progress-checkpoint71-adjacent-excluded.md.

Next is sparse-contact avoidance,TeX9.73; read
tmp/erdos577/full-leaf-sparse-avoid-implementation-plan.md. Claims2.6–2.7
and the exact main Lean theorem remain unproved. The goal remains active
with no blocker. No staging,commits,subagents,source-paper changes,or
computational-limit increases.

## 2026-08-27: milestone73, sparse contacts avoid the matching, complete

FullLeafSparseGeometry, FullLeafSparsePreparation, and FullLeafSparseAvoid
add9 selected public declarations. The first preparation proves that a
heavy type41 block is complete with at least9 first-triple contacts.
Every second-side vertex lies in an actual core triangle with a complete
complement. A second-side total of18 gives at least10 triangle contacts.

A matching edge and a positive sparse row produce an actual paw. On
the type40 side, its triangle contacts give the eleven-contact factor;
the exceptional pattern is excluded by its leaf degree3 versus degree1.
On the type41 side, the complete-block/nine-contact theorem gives the
factor directly. Exact support equalities contradict the earlier first
and second no-factor theorems. Both designated endpoint degrees are0.

The sparse-attachment predicate records the block type and designated
side. Configuration.matching_endpoints_not_sparse gives the packaged
conclusion with an explicit heavy-block hypothesis. No stronger claim
about all degree-one rows or additional maximality premise is assumed.
This proves TeX9.73 completely; the milestone count advances to73/82.

Full build and direct Lean exit0:749 proof modules plus Verification,
750 Lean files,9455 jobs,and1675 ordered selected axiom reports. Only
propext,Classical.choice,and Quot.sound occur. All9 new declarations
are selected. All modules are reachable with acyclic imports. All746
earlier proof modules and the principal PDF retain their hashes.
No task warnings. Placeholder,option,native-evaluation,and full-source
whitespace scans pass. No computational limits changed.

Independent checks cover84 type41 numeric inputs,65 prescribed core
triangles,2110 triangle-contact bounds,3792 one-leaf/eleven-contact paw
factors,and3588 complete-block/nine-contact paw factors. There are260
first-endpoint and65 second-endpoint global factor fixtures. All13 dense
cores and all four first-endpoint diagonal choices are covered. Exact
factor supports, retained blocks, and actual matching edges are checked;
the global fixtures fix the marked vertex and first endpoint. Local paw
cross matrices and centers are exhaustive. Earlier heavy-type and branch
regressions are rerun. Fixtures are not claimed globally feasible or
minimum-degree graphs. No Python result is used as a Lean oracle.

Evidence: validation/lean-sparse-avoid-{build,axioms}.txt,
validation/lean-sparse-avoid-audit.json,and
validation/sparse-avoid-independent.json. TeX pass467 has250 pages,
21584 source lines,and no warnings or box issues. Final pages227,228,229,
239,240,241,250 were rendered and viewed. The first213 pages have unchanged
extracted text. Pass467 fixes a missing map space in the otherwise clean
pass466. The preceding log is preserved at progress-checkpoint72.md.

Next is the maximal sparse-core refinement,TeX9.74; read
tmp/erdos577/full-leaf-sparse-refinement-implementation-plan.md. Claims2.6–2.7
and the exact main Lean theorem remain unproved. The goal remains active
with no blocker. No staging,commits,subagents,source-paper changes,or
computational-limit increases.

## 2026-08-27: milestone74, sparse-core refinement, complete

Eight modules from FullLeafSparseCounts through FullLeafSparseRefinement
add16 selected public declarations. Positive-row filters turn matching
and sparse contact sums into cardinalities; their disjointness gives
rho+t≤5. Both marked rows full permit three actual terminal swaps:
X to Y on Q, Y to d on J, then d to X on the changed Q. The original
paw is restored, both scores are preserved at every step, and all
intermediate chains are feasible. No attachment is assumed for the
intermediate terminal d. The additional maximum gives t≤rho+1.

For four sparse rows, every prescribed four-subset contains a path
between the centers whose removal leaves a complete core complement.
The proof treats a complete core and every location of its possible
single gap. Core replacement columns have degree at most1. Their total
four forces both center rows on J to vanish. A new actual paw and local
chain replace the core triangle and complete block, preserving both
scores. The new coordinate is3; the disjoint-filter bound gives old
rho≤1. Maximality excludes this case. The actual marked-leaf interchange
restores arbitrary original labels. Maximal.type41_refinement proves
completeness, at least10 triple contacts, and rho≥2 at equality, with
the additional maximizing premise explicit. This completes TeX9.74.

Full build and direct Lean exit0:757 proof modules plus Verification,
758 Lean files,9463 jobs,and1691 ordered selected axiom reports. Only
propext,Classical.choice,and Quot.sound occur. All16 new declarations
are selected. All modules are reachable; imports are acyclic. All749
earlier proof modules and the principal PDF retain their hashes.
No task warnings. Placeholder,option,native-evaluation,and full-source
whitespace scans pass. No computational limits changed.

Independent checks cover32 positive-row masks,1351 full-column matrices,
9276 compatible matching/sparse pairs,65 core-path choices,and50 final
numeric models. The27040 three-swap chains cover all13 dense cores,
all four marked vertices, every first-triple matrix missing at most3
contacts, and every full column. The17280 changed-core chains cover
all four-row sparse matchings and every valid path choice for each
core and marked vertex. Exact remainders, retained blocks, and both
scores are checked, including intermediate unattached terminals.
Earlier avoidance and heavy regressions are rerun. Fixtures are not
claimed globally feasible or minimum-degree graphs; Python is no oracle.

Evidence: validation/lean-sparse-refinement-{build,axioms}.txt,
validation/lean-sparse-refinement-audit.json,and
validation/sparse-refinement-independent.json. TeX pass469 has251 pages,
21604 source lines,and no warnings or box issues. Pages227,228,229,240,
241,242,251 were rendered and viewed. The first213 mathematical pages
have unchanged extracted text. Pass468 had three underfull table lines;
wording changes resolve them in469 without changing the mathematics.
The preceding log is preserved at progress-checkpoint73.md.

Next is sparse uniqueness,TeX9.75; read
tmp/erdos577/full-leaf-sparse-unique-implementation-plan.md. Claims2.6–2.7
and the exact main Lean theorem remain unproved. Goal active, no blocker.
No staging,commits,subagents,source-paper changes,or limit increases.

## 2026-08-27: milestone75, uniqueness of sparse attachments, complete

Ten modules from FullLeafSparseDoubleExclusion through FullLeafSparseUnique
add17 selected public declarations. The two three-cycle partition
obstructions are derived from actual complementary core quadrilaterals
and the bridge, retaining every unselected block. The exact twelve-set
partition reuses the earlier parallel-replacement splice. In type40,
eighteen contacts supply a common neighbor and two distinct full rows;
the resulting partition contradicts the first-side obstruction.

All three type41 common-column factors are proved: the direct factor,
the recentered common cycle, and the exchanged replacements. The result
is universal in every shared second-side vertex and both neighboring
columns before it is reused in the count. Two totals≥11 force a common
triple neighbor. At a total10, refinement gives rho=2 and three sparse
rows. Their union with the two matching endpoints is the entire second
five-set. Every other sparse row belongs to this three-set. A full row
on the first block and the common-column exclusion bound each other
block column's combined triple and second-side degree by3. Summation
gives12, so the heavy total is≤20. The final uniqueness theorem covers
both designated sparse types and explicitly excludes mixed-side cases.

Full build and direct Lean exit0:767 proof modules plus Verification,
768 Lean files,9473 jobs,and1708 ordered selected axiom reports. Only
propext,Classical.choice,and Quot.sound occur. All17 new declarations
are selected. All modules are reachable with acyclic imports. All757
earlier proof modules and the principal PDF retain their hashes.
No task warnings. Placeholder,option,native-evaluation,and full-source
whitespace scans pass. No computational limits changed.

Independent checks cover5275 full-row avoidance choices,712336 dense
column pairs,39936 first-side global factors,392352 local common-column
factors,and780 second-side global factors. The three local branch counts
are374784,14400,and3168. Every ten-contact matrix pair, common vertex,
and permitted high-row choice is checked. Global fixtures cover all13
dense cores and all four marked vertices. The first side covers all
diagonal and neighboring-column choices with fixed dense matrices;
all211-by-211 dense matrix pairs are covered separately by the choice
checks. There are80 equality row covers and62208 final column bounds.
Every factor has exact support and retained blocks. Earlier refinement,
avoidance,and heavy regressions are rerun. Fixtures are not claimed
globally feasible or minimum-degree graphs. Python is no Lean oracle.

Evidence: validation/lean-sparse-unique-{build,axioms}.txt,
validation/lean-sparse-unique-audit.json,and
validation/sparse-unique-independent.json. TeX pass470 has251 pages,
21622 source lines,and no warnings or box issues. Pages227,228,229,240,
241,242,251 were rendered and viewed. The first213 mathematical pages
have unchanged extracted text. The preceding log is preserved at
progress-checkpoint74.md. Next is equality in the ten-row count,9.76;
read tmp/erdos577/full-leaf-equality-implementation-plan.md.
Claims2.6–2.7 and the exact main Lean theorem remain unproved. Goal active,
no blocker. No staging,commits,subagents,paper changes,or limit increases.

## 2026-08-27: milestone76, equality in the ten-row count, complete

Twelve modules from FullLeafEqualitySets through FullLeafEquality add67
selected public declarations. Actual finite attachment and matching sets
give the coverage bound8-2*rho. Sparse uniqueness identifies the union's
cardinality with the sum over heavy blocks. The further family has k-3
members, with k≥3 derived from the actual twelve-vertex core. Its empty
case is included. The exact inside sum is22+2*rho+contacts(Z2,K).

The ten minimum-degree inequalities force equality in all three bounds:
core sum30, sparse coverage8-2*rho, and the total further-block budget.
Finite summand inequalities give equality at each block. The complete
core and actual attachments for every unmatched vertex follow. Each
heavy nonsparse side has all20 contacts. If rho<3, three equal-score
terminal swaps exchange an unmatched first vertex with a sparse column,
retaining the original paw, marked edge, dense block, and every other
block. The maximizing coordinate increases by1, so rho=3. Both matching
triples have actual injective Fin3 labels with exact supports and edges.
Their inside degrees5 and7 give the exact combined sum36.

Full build and direct Lean exit0:779 proof modules plus Verification,
780 Lean files,9485 jobs, and1775 ordered selected axiom reports. Only
propext, Classical.choice, and Quot.sound occur. All67 new declarations
are selected. All modules are reachable with acyclic imports. All767
earlier proof modules and the principal PDF retain their hashes. No
task warnings. Placeholder, option, native-evaluation, and full-source
whitespace scans pass. A scan initially matched an ordinary English
word in a module comment; the comment was reworded and the complete
build, direct Lean check, and scan were repeated against the final files.

Independent checks cover136 partial matchings,22896 sparse assignments,
2416 equality covers,7072 inside identities,240 complete matching degree
cases,1440 injective labelings,65520 actual three-swap chains, and439952
numeric slack cases with32 equality cases. All13 dense cores, four
marked vertices, unmatched pairs, and neighboring columns are covered.
The exact supports, retained blocks, both scores, original paw, marked
edge, and objective increase are checked. The empty further family is
included. Sparse uniqueness and its earlier regressions are rerun.
Fixtures are not claimed globally feasible or minimum-degree graphs;
finite numeric cases do not replace the Lean proof for all k.
Python is not a Lean oracle.

Evidence: validation/lean-full-leaf-equality-{build,axioms}.txt,
validation/lean-full-leaf-equality-audit.json, and
validation/full-leaf-equality-independent.json. TeX pass471 has251 pages,
21652 source lines, and no warnings or box issues. Pages227–232,241–243,
251 were rendered and viewed, including every changed extracted-text
page. The first213 mathematical pages remain unchanged. The preceding
log is preserved at progress-checkpoint75.md. Next is the final six-row
alternative,9.77; read tmp/erdos577/full-leaf-six-rows-implementation-plan.md.
Claims2.6–2.7 and the exact main theorem remain unproved. Goal active,
no blocker. No staging, commits, subagents, paper changes, or limit increases.

## 2026-08-27: milestone77, the final six-row alternative, complete

Fifteen FullLeafSix modules add31 selected public declarations. Actual
terminal swaps and complete-core replacements construct a strong paw
for every first matching endpoint, preserving both scores and all further
blocks. The earlier final paw classification's counts and outside factor
hold for both surviving patterns and give the positive-paw bound directly.
Exact finite sums prove the low-row alternative. Universal replacements,
core column bounds, and the nine-triangle-contact factor reduce the
high-row branch to8+4.

An opposite second row forces first columns3,1,3,1 and the low diagonal.
The remaining two second rows are distinct and give two actual
quadrilaterals on exactly eight vertices. Their supports and disjointness
are checked before the global factor obstruction. Opposite pairs are
excluded in every cycle labeling. A two-neighbor second row exists and
is adjacent. Complete-block relabeling excludes completeness. The
single-diagonal labeling preserves the adjacent row; its replacement
bounds the last first column by1. Seven remaining contacts force a
three-neighbor first row and the missing diagonal. The final theorem
proves all three alternatives for every qualifying further block.

Full build and direct Lean exit0:794 proof modules plus Verification,
795 files,9500 jobs,1806 ordered reports, only propext, Classical.choice,
and Quot.sound. All31 new declarations are selected. All modules are
reachable with acyclic imports. All779 earlier proof modules and the
principal PDF retain their hashes. No task warnings, placeholders,
option overrides, native evaluation, or whitespace errors. No limits changed.

Independent checks include720 actual strong-paw chains and77760 global
opposite-case factors, with all four marked vertices and60 full matchings.
They cover all nine first matrices, six second assignments, both diagonal
choices, and first-vertex choices. Both scores, exact supports, and all
unselected blocks are checked. Additional counts:57 paw cases,2 low and16
high numeric cases,9 opposite-free masks,24 complete-block labelings,
16 single-diagonal labelings,117 diamond matrices,153 three-row witnesses.
Earlier equality and sparse regressions are rerun. Fixtures are not
claimed globally feasible or minimum-degree graphs; finite checks do
not supply Lean oracles.

Evidence: validation/lean-full-leaf-six-rows-{build,axioms}.txt,
validation/lean-full-leaf-six-rows-audit.json, and
validation/full-leaf-six-rows-independent.json. TeX pass472 has251 pages,
21681 source lines, no warnings or box issues. All16 changed text pages
229–233 and241–251 were rendered and viewed. The first213 mathematical
pages are unchanged. Checkpoint76 is preserved exactly. Next: Claim2.6's
final degree count9.78; read tmp/erdos577/claim-two-six-implementation-plan.md.
Claim2.6, Claim2.7, and the exact main theorem remain unproved. Goal active,
no blocker. No staging, commits, subagents, source-paper changes, or limit increases.

## 2026-08-27: milestone78, Wang's Claim2.6, complete

Four modules, ClaimTwoSixCounts, ClaimTwoSixContributions, ClaimTwoSixParity,
and ClaimTwoSix, add11 selected public declarations. Every further block
attains the six-row upper bound12. Its fixed first-row degree and
second-triple contact total are exactly(0,12),(4,0),or(2,6). Each first
row is even and each weighted contribution3*d+e is12.

An equivalent parity argument was added to the TeX mathematical proof
before Lean implementation, preserving the original three-class count.
Actual selected-core partitions for arbitrary rows and a single vertex
give the global identity3*degree(q)+contacts(T2,univ)=36+12*(k-3)=12*k.
Minimum degree forces degree(q)=2*k, but its inside degree5 and even
outside sum make it odd. The empty further family is included. A
positive noncentral row supplies an actual Configuration and its attained
finite maximum, now impossible. TriangleChain.Feasible.claim_two_six
therefore gives both original noncentral rows zero without any additional
maximizing-configuration hypothesis. Claim2.6 is fully proved.

Full build and direct Lean exit0:798 proof modules plus Verification,
799 files,9504 jobs,1817 ordered reports, only propext, Classical.choice,
and Quot.sound. All11 new declarations are selected. All modules are
reachable with acyclic imports. All794 earlier proof modules and the
principal PDF retain their hashes. Source, option, native-evaluation,
and untracked-file whitespace scans pass. No task warnings or limit changes.

Independent checks cover9841 actual graphs for all class assignments
with zero to eight further blocks, at exact order4*k. Actual global
degrees, the weighted identity, odd first degree, and the required
minimum-degree contradiction are checked. The original class comparison
has5782 first-branch and4059 second-branch cases. All216 mixed first
matrices and924 mixed second matrices are checked separately; their
Cartesian product is not enumerated, and the global fixtures use
representative mixed matrices. Earlier six-row and equality regressions
are rerun. An initial fixture interface error passed ranges to a helper
expecting sets; inputs were normalized and the full suite rerun successfully.
Fixtures are not claimed globally feasible, and Python supplies no oracle.

Evidence: validation/lean-claim-two-six-{build,axioms}.txt,
validation/lean-claim-two-six-audit.json, and
validation/claim-two-six-independent.json. TeX pass475 has253 pages,
21722 source lines, no warnings or box issues. Eighteen selected pages
209–214,229–234,241–244,252–253 were rendered and viewed, covering the
mathematical addition, implementation map, boundaries, and final pages.
Not all later reflowed pages were individually rechecked. The first208
pages are unchanged. The final mathematical theorem now spans213–214.
Checkpoint77 is preserved exactly. Next: universal triple pattern9.79;
read tmp/erdos577/universal-triple-implementation-plan.md. Claim2.7 and
the exact main Lean theorem remain unproved. Goal active, no blocker.
No staging, commits, subagents, paper changes, or computational-limit increases.

## 2026-08-28: milestone79, universal Property A, complete

UniversalTripleWeight, UniversalTriple, and UniversalTripleLabels add12
selected public declarations. The actual degree partition and inside
degrees1,2,2 give a nine-contact weighted block, including an empty-family
contradiction. The small-leaf bound and Claim2.6 force leaf degree3.
The earlier preparation gives the complete block and exact neighbor
filters. Its triangle bound is extended to include the selected block
using the stronger four-contact bound.

Actual noncentral interchange and cyclic rotation create a
UniversalTriple.Configuration, with unchanged leaf, triangle and remainder
support. The center row is restricted to the omitted block vertex by
disjoint triangle filters. Configuration existence and the triangle bound
are proved for every strong chain, and also for every feasible paw
presentation. This universal scope is necessary for the later exchanges.
The weighted partition and label argument were detailed in TeX before
Lean implementation; the Leanization map is updated afterward.

Full Verification build and direct Lean exit0:801 proof modules plus
Verification,802 files,9507 jobs,1829 ordered reports, only propext,
Classical.choice and Quot.sound. The1817-report prefix is retained.
All12 new declarations are selected, all modules reachable, imports
acyclic, all798 earlier proof modules and the principal PDF unchanged.
An initial proof-style warning was corrected; the full build and direct
Lean were rerun before the clean final audit. No task warnings, source
violations, untracked-file whitespace errors, or changed limits remain.

Independent checks inspect65536 cross masks and combine the already-proved
row consequences. They reduce14016 masks after the degree restrictions
to16 exact local patterns, check384 cyclic-label transports in both
noncentral orders, and verify80 actual global degree partitions with
zero to four blocks. All preceding Claim2.6 and six-row regressions rerun.
The fixtures are not claimed globally feasible or minimum-degree
counterexamples, and Python supplies no oracle for Lean.

Evidence: validation/lean-universal-triple-{build,axioms}.txt,
validation/lean-universal-triple-audit.json, and
validation/universal-triple-independent.json. TeX pass476 has253 pages,
21761 source lines, no warnings or box issues. All28 changed text pages
209–233 and242–244 were rendered and viewed. The first208 pages are
unchanged; the mathematical main theorem remains on213–214.
Checkpoint78 is preserved exactly. Next is the universally quantified
heavy-block classification9.80; read
tmp/erdos577/triple-heavy-block-implementation-plan.md. Claim2.7 and
the exact main Lean theorem remain unproved. Goal active, no blocker.
No staging, commits, subagents, paper changes, or computational-limit increases.

## 2026-08-28: shared heavy-block preparation within9.80, audited

The milestone count remains79/82. Nine modules through TripleHeavyCount
add41 selected declarations. The exact five-row inside count is17+2*epsilon,
bounded by19; the actual degree partition supplies a heavy block with at
least11 contacts, including the empty-family contradiction. Both first-block
replacements are complete. The exposed-terminal chain preserves both
scores and all other blocks without an assumed triangle attachment.
The local triangle-core factor is completed to the exact global packing.

For every qualifying block in the high-contact branch, the leaf row is0,
triangle total10, exposed row1, and block edge count at least5. The
unconditional eleven-contact paw theorem excludes all three remaining
first-block columns, using the possibly lower-score complementary block
only in the factor, not as an assumed feasible chain. An actual unique
neighbor supplies HighCore. A generic core-triangle exchange proves that
an at-least-as-dense quadrilateral complement has equal score and yields
a strong chain preserving both original scores. The exact seven-vertex
core gives inside row bounds4,5,7,7 and the budget23, then a nine-contact
block outside both selected blocks. Neither U nor V is yet excluded;
the12 core cases, low-contact branch, Claim2.7 and main assembly remain.

Full build and direct Lean exit0:810 proof modules plus Verification,
811 files,9516 jobs,1870 ordered axiom reports, only propext,
Classical.choice and Quot.sound. All41 new declarations are selected.
The1829-report prefix and all801 earlier proof-module hashes are preserved.
Imports are acyclic and every module is reachable. Source, computational
option, native-evaluation and untracked-file whitespace scans pass.
No task warnings; unchanged BoundedGaps/AINTLIB dirty-checkout warnings remain.

Independent checks cover1584 actual high-core graphs,66 triangle matrices,
three block diagonal choices, four marked positions and two center-edge
choices. They check31680 four-row budgets,16680 equal-score attached
exchanges,5856 strict gains,1536 local quadrilateral remainders, and all
65536 outside masks. Seventy-five masks satisfy the four selected global
minimum-degree inequalities; every one has at least9 outside contacts.
All prior Property A, Claim2.6 and six-row regressions are rerun. Fixtures
are not asserted globally feasible or counterexamples; neither the
pending exclusions nor the main theorem is supplied by Python.

Evidence: validation/lean-triple-heavy-preparation-{build,axioms}.txt,
validation/lean-triple-heavy-preparation-audit.json, and
validation/triple-heavy-preparation-independent.json. TeX details were
extended before Lean implementation; the map records the precise partial
scope. Pass477 requested the normal reference rerun. Final pass478 has
254 pages and21796 source lines, with no warnings or box issues.
Fourteen selected pages210–215,230–232,243–245,253–254 were rendered and
viewed; not all later reflowed pages were individually rechecked. The
first209 pages are unchanged and the mathematical main theorem is on214.
Checkpoint79 is preserved exactly. Next read
tmp/erdos577/triple-forbidden-triangles-implementation-plan.md. Goal active,
no blocker. No staging, commits, subagents, paper changes, or limit increases.

## 2026-08-28: both forbidden-triangle exclusions within9.80, audited

The milestone count remains79/82. Seven TripleForbidden modules add31
selected declarations. UCase and VCase encode exactly the triangle,
bridge, complement score and three further quadrilateral complements
in the mathematical proof. Their actual paws have different centers;
both yield strong chains preserving both scores and all unselected blocks.
The generic partial-factor completions retain the original first block
or the appropriate actual replacement. All six common-insertion
prohibitions are proved by explicit cycles and global factor assembly.

The original feasible terminal chains bound the extra row by two.
Claim2.5 and the proved matching-score bound supply the hypotheses of
the common-triple theorem with actual cyclic labels. The middle-vertex
replacement and the final cycle through the correct center give the
two contradictions, UCase.false and VCase.false. Neither exclusion is
assumed. The twelve-pattern coverage and48 witnesses, C configuration,
low-contact branch, Claim2.7 and exact main theorem remain unproved.

Full Verification build and direct Lean both exit0:817 proof modules
plus Verification,818 files,9523 jobs,1901 ordered axiom reports,
only propext, Classical.choice and Quot.sound. All31 new declarations
are selected. The1870-report prefix and all810 earlier proof-module
hashes are preserved. Every module is reachable, imports are acyclic,
and source and untracked-file whitespace scans pass. No task warnings;
the preexisting BoundedGaps/AINTLIB dirty-checkout warnings are unchanged.

Independent tests enumerate1584 actual high-core graphs and8472 U/V
configurations, with6144 equal-score and2328 strict-score chains.
They verify406656 common-pair factors and33888 final factors, including
all cyclic removal positions and both optional outside-block diagonals.
All cycles have exactly four vertices and every factor has an exact
disjoint16-vertex cover. The preceding preparation, Property A,
Claim2.6 and six-row regressions rerun. Fixtures are not claimed globally
feasible or counterexamples; Python is not a Lean oracle or a proof of
the pending twelve-pattern coverage.

Evidence: validation/lean-triple-forbidden-triangles-{build,axioms}.txt,
validation/lean-triple-forbidden-triangles-audit.json and
validation/triple-forbidden-triangles-independent.json. The complete
U/V mathematical arguments were already in TeX before implementation.
Its map now describes the actual proofs and outstanding work. Pass479
has254 pages and21815 source lines, no warnings or box issues. All seven
changed text pages230–234,244–245 were rendered and viewed. All other
pages, including the first229 and mathematical main theorem on214,
are textually unchanged from478. The principal PDF hash is unchanged.
The preceding progress log is preserved; the current snapshot is
tmp/erdos577/progress-checkpoint79-forbidden-triangles.md. Next read
tmp/erdos577/triple-core-coverage-implementation-plan.md. Goal active,
no blocker. No staging, commits, subagents or computational-limit changes.

## 2026-08-28: entire high-contact branch within9.80, audited

Fifteen modules through TripleHighExcluded add84 selected declarations.
The milestone count remains79/82. CCase has the source triangle, marked
vertex, complement score and core budget17. An actual factor excludes
its center–exposed edge. Its strong chain preserves both scores and
outside blocks. The five distinct rows have inside budget27 and force
an eleven-contact block; proved leaf transport contradicts the universal
triangle bound on the new chain. Thus CCase.false is fully proved.

All twelve literal source models and forty-eight witnesses are certified:
34 U,5 V and9 C entries. The192 stored cyclic orders include repetitions
of C's single complement in unused slots. Each entry gives the full
case hypotheses, including scores and the C upper degree budget.
Explicit permutations and bounded kernel proofs cover66 complete row
masks and6 allowed diamond masks. The proved dense-triangle theorem
excludes every other diamond shape by a strict improvement. Removing
only the outside row leaves all core bits unchanged, and the actual
source-classification theorem retains every distinguished paw label.

Actual graph copies preserve the old block score, paw labels and exact
core adjacency. The U/V/C image theorems transport every required graph
fact; C's upper count uses exact adjacency, not merely a positive copy.
The48 witnesses therefore apply to the original graph. HighCore.false
and Configuration.heavy_paw_contacts_le_eight complete the high-contact
branch for every qualifying heavy block. The low-contact branch,
Claim2.7 and exact main theorem remain. No completion of9.80 is claimed.

Full Verification build and direct Lean exit0:832 proof modules plus
Verification,833 files,9538 jobs,1985 ordered reports using only propext,
Classical.choice and Quot.sound. All84 new public declarations are
selected. The1901-report prefix and all817 earlier proof-module hashes
are preserved. Every module is reachable, imports are acyclic, source
and untracked-file whitespace scans pass. Intermediate style warnings
were corrected without changing computational settings. Final task
warnings are absent; the preexisting BoundedGaps/AINTLIB warnings remain.

Independent checks cover1584 high-core graphs and3456 C configurations,
1728 center-edge factors,1248 equal-score and480 strict-score chains,
and1728 five-row budgets. The largest fixture value is26, within the
proved27 bound. All1048576 outside masks are checked;225 satisfy the
five selected minimum-degree bounds. The12/48 table,72 column candidates,
1152 witness transports and4608 stored cyclic-order transports pass,
with extra edges outside the core permitted. Earlier U/V, preparation,
Property A, Claim2.6 and six-row regressions rerun. Fixtures are not
claimed globally feasible or counterexamples; Python is not a Lean oracle.

Evidence: validation/lean-triple-high-{build,axioms}.txt,
validation/lean-triple-high-audit.json and validation/triple-high-independent.json.
All mathematical arguments were already in TeX before implementation;
its Leanization map now records the full high-contact result. Pass480
had one underfull line; rephrasing the map removed it. Final pass481
has254 pages and21844 source lines, with no warnings or box issues.
All seven changed text pages230–235,244 were rendered and viewed; every
other page is textually unchanged from479, including the first229 and
mathematical main theorem on214. The principal PDF hash is unchanged.
The preceding log is preserved; current snapshot:
tmp/erdos577/progress-checkpoint79-high-contact.md. Next read
tmp/erdos577/triple-low-contact-implementation-plan.md. Goal active,
no blocker. No staging, commits, subagents or computational-limit changes.

## 2026-08-28: universal heavy-block lemma9.80 complete, audited

Six modules through TripleHeavyBlock add17 selected declarations and
complete milestone80/82. The low branch derives completeness and exact
rows3,4 with triangle total4. An actual selected-family factor excludes
common leaf/third columns. The third row is at most1; its remaining
case has two explicit cycles on the exact eight vertices and is excluded.
The positive second-row case uses two actual terminal swaps, complete
replacement blocks with equal scores, and the paw(u,b,r,c). Its full
leaf row and positive noncentral r-row contradict Claim2.6.
Configuration.heavy_block is now universal over every qualifying
configuration, with both noncentral rows zero and the three-row bound11.

Full Verification build and direct Lean exit0:838 proof modules plus
Verification,839 files,9544 jobs,2002 ordered axiom reports. All use only
propext, Classical.choice and Quot.sound. All17 public declarations are
selected; the1985-report prefix and all832 preceding proof-module hashes
are preserved. Import reachability, acyclicity, forbidden-placeholder,
computational-option and whitespace scans pass. The principal PDF is
unchanged. No task warnings; unrelated package warnings remain unchanged.

Independent tests check3125 count tuples,55 satisfying the hypotheses,
15 non-full-leaf tuples,648 common-column factors,72 third-row factors
and384 actual terminal swaps. Both optional center–exposed edges are
included. Fixtures are not claimed globally feasible or counterexamples,
and Python is not a Lean oracle. Evidence is in
validation/lean-triple-low-{build,axioms}.txt,
validation/lean-triple-low-audit.json and validation/triple-low-independent.json.

Only the Leanization map changed; all mathematics preceded implementation.
Final TeX pass483 has254 pages and21845 source lines without warnings or
box issues. Changed pages231,244,245 were rendered and viewed clean.
All other pages match481, including the first229 and the mathematical
main theorem on214. Snapshot: tmp/erdos577/progress-checkpoint80.md.
Claim2.7 and exact main assembly remain; the main Lean file is absent.
Next read tmp/erdos577/claim-two-seven-implementation-plan.md.
Goal active, no blocker; no staging, commits, subagents or limit increases.

## 2026-08-28: exact theorem complete, final audit

All82 milestones are complete. Twelve final supporting modules and the
main file add30 selected declarations. The three-row selection gives a
common neighbor leaving a complete block. The actual changed chain has
paw(c,r,X,u), exact block family and both original scores. Marked Property A
retains the actual center and identifies the shared noncentral vertex.
Rows1 and0 exclude the two changed blocks from both later selections.
The two final factors are explicit selected-family partitions, including
the complete first-block retention. Claim2.7 is proved for the specified
original block in either label order. The doubled-leaf bound8 contradicts
the proved threshold9; saturation and a strong chain finish the theorem.

src/latest/ErdosProblems/Erdos577.lean proves erdos_faudree,
exists_disjoint_four_cycles and erdos_faudree_min_degree, for every
natural k. Zero and one are separate branches. The conclusion uses
an injective Fin k × Fin4 embedding with all four cyclic edges; no
inducedness, strict degree inequality, or longer cycles are substituted.

Full build9557 jobs and both direct Lean commands exit0. All2032 ordered
reports use only propext, Classical.choice and Quot.sound. All852 Lean
files are reachable and imports acyclic; forbidden-source scans pass.
The2002-report prefix and all838 earlier supporting proof hashes are
preserved. The principal PDF hash is unchanged. No placeholders, new
axioms, limit increases, staging, commits or subagents. One intermediate
factor proof reached the default heartbeat bound; explicit partition
types and associative union identities resolved it without raising limits.
A dependent filter rewrite was replaced by explicit membership transport.
Final task warnings are absent; unrelated package warnings remain.

Independent checks enumerate4096 row masks,13 heavy patterns,32 choices,
and8192 actual graph constructions, split4096/4096 between the final cases.
All exact cycle supports, edges, untouched blocks and scores pass.
Low-contact tests rerun. Fixtures are not claimed globally feasible or
counterexamples; Python supplies no Lean oracle.

TeX pass487 has254 pages and21851 source lines, without warnings or box
issues. All12 changed pages plus the main theorem page214 were inspected;
seven pass486 views are byte-identical to their pass487 renders. Pages3–229
are textually unchanged from checkpoint80, so the mathematical proof
preceded implementation. The introduction and map now report certification.
The older unfinished alternative route is explicitly outside the final proof.

Exact commands and full result: FINAL_REPORT.md. Authoritative evidence:
validation/lean-final-audit.json, lean-final-{build,axioms}.txt,
lean-final-main-direct.txt, final-constructions-independent.json,
tex-pass487.txt and577.pdf. Final snapshot:
tmp/erdos577/progress-checkpoint82-final.md. No required work remains.
