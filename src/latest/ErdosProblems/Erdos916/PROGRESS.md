# Erdős 916 progress log

- Phase: 2 — Lean formalization.
- Verified: the detailed source-backed solution and Leanization plan are in
  `tex/916.tex`.
- Verified: exact wheel witnesses and transports, minimum dense-set extraction,
  `(2,3)`-circuit minimum degree, false-twin pair deletion, connectedness,
  the three-terminal path/block theorem, and the false-twin-to-wheel circuit
  theorem all type-check under the default limits.
- Verified: `Assembly.lean` type-checks the complete dense-graph conclusion
  from the source-level AHT false-twin theorem; the extracted circuit carries
  the necessary four-vertex lower bound.  A fresh
  `lake build ErdosProblems.Erdos916.Assembly` completed all 8721 jobs.
- Verified: the conditional assembly's dependency audit contains only `propext`,
  `Classical.choice`, and `Quot.sound`.
- Verified: `AHTUniverse.lean` isolates the finite relabelling step from a
  universe-zero AHT theorem to the universe-polymorphic principle used by the
  final assembly, and passes its direct Lean check.
- Verified: the complete source-level AHT Lemma 6.3 is in
  `AHTSourceLemma63.lean`; its exported common-neighbor theorem produces
  degree-three false twins and its dependency audit is standard only.
- Verified: `AHTK32Routing.lean` and `AHTMinimalThreeConnected.lean` prove
  AHT Lemma 4.5 and Corollary 4.6, including the universe transport; the
  resulting edge-minimal three-connectivity theorem passes Lean.
- Verified: `AHTSourceLemma65.lean` proves the complete source-level AHT
  Lemma 6.5 from the closeness hypothesis, producing two disjoint
  degree-three false-twin pairs.
- Verified: `AHTSection7TwoSeparation.lean` proves the minimal-end torso
  center-confinement and boundary-crossing branch, including the
  `K₃,₃-e` to ambient false-twin lift.  Its Claim (10) layer now also
  constructs both source two-fans with target-clean paths, normalizes their
  surviving arms, and closes every boundary-ending first-fan orientation when
  the path avoids `a,a'`.  The two displayed second-fan wheel shapes and an
  exhaustive collision-obstruction reduction now pass Lean as well; the
  remaining task is the first-hit rerouting that turns every listed collision
  into an already-forbidden boundary-ending fan.
- Verified: the current fragment/replacement API in
  `AHTSourceLemma64.lean` and the complete Theorem 6.6 Case 1 endgame in
  `AHTSourceTheorem66Case1.lean` both pass direct Lean checks.
- Verified: the Theorem 6.6 component-boundary argument in
  `AHTSourceTheorem66Case4.lean` passes Lean with standard dependencies.
  The corrected Case 5 certificate in
  `AHTSourceTheorem66Case5Deleted.lean` places the Watkins--Mesner splitter on
  the centre-deleted graph, maps its attachment edges back to the ambient
  graph, and passes both Lean and the standard-axiom audit.  The corrected
  deleted-centre Case 3 cardinality certificate also passes Lean, including
  all component-set, attachment, and ambient degree transports.  The older
  ambient Case 3/5 certificates are intentionally unused.
- Verified: `AHTSourceLemma64.lean` now proves replacement-graph
  three-connectivity and excludes all new pin vertices as wheel centres under
  the default limits.  Its next checked layer proves the exterior two-fan,
  first-exit, and old non-pin degree/ambient-embedding infrastructure needed
  for the remaining old-vertex wheel-centre transfer.  The complete
  no-gadget branch is also checked: any replacement wheel whose rim avoids
  the two artificial vertices lifts to an ambient wheel.  The gadget-rim
  extraction is checked as well: rims through one or both artificial pins
  yield explicit old-graph pin-to-pin paths, including the repeated-pin and
  degenerate-side cases.  The next checked layer chooses an exterior boundary
  path through a prescribed neighbour, trims and maps prepared pin paths back
  to ambient paths, and closes those paths into ambient cycles.  It remains to
  discharge the finite one-/two-pin centre cases and package replacement
  almost-wheel-freeness.
- Verified: `AHTWatkinsMesnerSplitter.lean` type-checks the Type-0
  fan/Menger extraction, maximal routed separators, candidate parts, and
  complement two-connectivity.  It also reduces a failure of condition
  (vii) to an unmatched boundary-to-boundary component path.  The next
  checked layer constructs the two Menger linkages, paired connector stems,
  initial side graphs, cut-defect certificate, and a minimal connector pair.
  Splitter condition (v), the exchange proof that this minimal pair is
  two-connected, the remaining contradiction for (vii), and final
  minimization/extraction remain.
- Verified: `AHTPairBridge.lean` explicitly converts the source-level
  two-pair certificate into the connectivity/torso certificate consumed by
  Section 7; the conversion passes Lean and does not rely on definitional
  equality between the independently developed records.
- Current gap: the source-level proof of the AHT false-twin theorem, specifically
  the remaining parts of Lemmas 6.4–6.6 and the final two-separator induction.
- Current work: finish fragment replacement, Lemma 6.6, and the final
  AHT two-separator/minimal-counterexample assembly.
- Next: instantiate `DegreeThreeFalseTwinPrinciple`, export the theorem from
  `Erdos916.lean`, then run the target build, forbidden-token scan, and
  `#print axioms` audit.
