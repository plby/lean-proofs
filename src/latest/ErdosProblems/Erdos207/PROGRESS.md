# Erdős 207 formalization progress

## 2026-08-27 — completed and verified

- Phase: complete. `Erdos207.erdos_207` in `ErdosProblems/Erdos207.lean`
  proves the exact problem, with both admissible congruence classes, all
  sufficiently large orders, and the edge-count bound `j + 3`.
- The actual initial law, source-correct compressed cover-down transition,
  finite forward constants and backward error schedule, terminal extraction,
  and absorption are proved. The final bridge uses the girth cutoff `g + 2`.
- Verified on Lean 4.33.0: direct main check; main/audit Lake build (9989
  jobs); 2373 prerequisite axiom reports, with zero unexpected axiom lists
  and zero Lean errors.
- The final main theorem's `#print axioms` output is exactly
  `[propext, Classical.choice, Quot.sound]`. No new/project-local assumption
  occurs in its dependency closure.
- A comment-aware scan of all 1519 Lean files found zero forbidden proof
  placeholders or computational-limit settings. A separate `set_option`
  search has no matches. `git diff --check` passes.
- The genuine counterexample to the old stronger distribution invariant is
  preserved in `LaterEdgeDistributionObstruction.lean`; the completed proof
  uses the corrected residual distribution throughout.
- `tex/207.tex` contains the detailed mathematical reconstruction and
  Leanization plan. Two final TeX passes produce 131 pages (1014393 bytes)
  without warnings, undefined references, or overfull/underfull boxes.
  Representative statement, coefficient, audit, and conclusion pages were
  rendered for visual review; long Lean identifiers now wrap within margins.
- Repaired draft type-inference, cast, and normalization failures without
  changing any computational limits. No current Lean failures remain.
  Existing dirty dependency-package warnings are unrelated to this proof.
- Next: hand off the completed files. Nothing was staged or committed.

Final verification commands, from `src/latest/`:

```sh
lake env lean ErdosProblems/Erdos207.lean
lake build +ErdosProblems.Erdos207:olean +ErdosProblems.Erdos207.KSSSTrajectoryAudit:olean
lake env lean ErdosProblems/Erdos207/KSSSTrajectoryAudit.lean
git diff --check
```

TeX verification, from the repository root (run twice):

```sh
pdflatex -no-shell-escape -interaction=nonstopmode -halt-on-error -output-directory /tmp/erdos207-tex-check.ElfMwu tex/207.tex
```

The entries below are historical checkpoints, not the final proof status.

## 2026-08-26 — absorber-rooted moments and quantitative configuration drift

Current phase: Lean prerequisites for the source-correct coupled process;
the unconditional construction and final theorem remain unfinished.

Latest continuation checkpoint: the expanded main/audit build passes
(9951 jobs), and the 2291-declaration audit reports zero unexpected axiom
lists and zero Lean errors. All dependencies remain limited to `propext`,
`Classical.choice`, and `Quot.sound`. This audits prerequisites only.
The simultaneous future-typicality path is now checked through actual
canonical quasi tails and actual raw-link local degree tails. It includes
finite order/pattern/pin/future-level unions, the exact master-loss event,
real cutoffs, normalized density ratios, and explicit power/error budgets.
The raw-link degree theorem retains the prior bad-overlap probability.
All 371 additions since the 1920 checkpoint pass the 2291-declaration audit;
the main/audit build and direct main check pass. No limits were changed.
Latest compiled TeX checkpoint: 124 pages, 971346 bytes, with no warnings.
The source link sampler, corrected distribution update, actual local/quasi
tails, coverage conditioning, and master-law update now form one checked
transition. Coverage holds on its entire conditioned support, and updated
compression retains every deterministic invariant. The growing overlap
cutoff has its full polynomial/error tail; left/quasi power bounds preserve
the incoming coefficient. The indexed source families omit singleton
outside obstructions, so an explicit checked bridge now restores the full
absorber family using the old stage's singleton-safe availability and
selected set. Updated availability is exactly equal, not weakened.
Stage-indexed source coefficients retain the growing zero-prefix bank term.
All of these pass the 2291 audit and direct main check. Explicit rounded
link degree/cap/Hall choices additionally pass direct checks and await the
next expanded audit. Draft finite-pair, cast, and support-predicate inference
errors were repaired; no computational limits were changed.
The actual retained-level process scales, initial density/availability
floor, finite backward error schedule, and initial geometric-error power
comparison are now included in that audit. The direct main check passes.
Support-preserving reserve recentering and its all-support source-geometry
corollary also pass direct checks and are imported for the next audit.
No new proof failures remain at this checkpoint. Next: instantiate the
common numerical stage thresholds and conditioned reference/overlap/spoke
bounds, assemble the full cover-down step, and close the master recursion.
The latest continuation constructs the actual prepared reserve law with
nonempty regularized triangle families on every good-outcome fiber. The
same reserve sample supports regularization, internal supplies and link
reference counts; the joint conditioning retains the corrected reserve
distribution and its exact reciprocal loss. Good-outcome subtype
reindexing introduces no further loss. Current-vertex graph encodings
preserve all edge and pair-degree counts, and the actual stopped local
process is globally legal even on early-stopped outcomes. Fixed-envelope
all-order regularization now has an arbitrary inverse-power exceptional
degree-gap bound, and its decoded current-process geometry holds on the
entire support. The source-crude joint failure and conditional sparse
mixed law are checked with their full polynomial incoming-error loss.
All 35 additions since the 2178 checkpoint passed direct source checks,
the main/audit build, and the expanded axiom audit; the direct main check
also passed. Draft cast, decidable-instance, and type-inference errors
were repaired without changing limits. The new files have no forbidden
placeholder or limit-setting matches. The explicit regularization
precision, integer-gap and sampling-exponent budgets now pass, as do
simultaneous auxiliary-degree control and its reserve-law conditioning.
The fixed-envelope regularizer is instantiated on those actual families.
Actual sparse-process data on the current vertex subtype now checks;
an explicit subtype choice and an edge-membership conversion repaired
the draft finite-enumeration mismatch. The local mixed law transports to
ambient vertices with exactly the same scales and error, including test
families outside the current support. These 14 further declarations pass
the expanded build and 2227-declaration audit. The actual frozen sparse
law is now assembled, including its full exceptional-probability bound,
positive prior conditioning, and global legality on failed kernel outcomes.
The genuine correlated raw internal kernel now has a checked corrected
reserve update, source left-moment coverage bound, and conditioned
intermediate residual-link state. The first-stage size ratio is retained
in an explicit feasible physical exponent schedule; local analytic scale
comparisons and the augmented source coefficient bound also check. The
affine and gradual initial-law theorems now expose their bank-exponent
bound through strengthened versions, while preserving the old interfaces.
These 20 further declarations pass the expanded build and 2247 audit;
the direct main check passes. Draft finite-index inference and finite-set
normalization errors were repaired with explicit types/lemma namespaces.
No limits were changed and the changed Lean files have no forbidden
placeholder matches. Next: transport the fixed stage multipliers to every
retained level, instantiate the remaining numerical matching/future-loss
budgets, and close the corrected master recursion. The final theorem is absent.
The source left moment now checks through its two-density rooted weights,
corrected reserve realization, actual candidate count, normalized tail,
and scheduled-edge terminal success. The terminal failure certificate
avoids an invalid future-residual monotonicity step. The main direct
check also passes. Finite left-order and ambient-edge unions now check,
as do their application to the actual raw internal kernel and conditioning
on complete internal coverage with the corrected reserve law. These are
included in the 2032 audit. The prior bad-event probability is retained.
The matching audit found that the saved uncentered uniform mixing scalar
is not implied by typicality: N*C >= d^2 already makes its required
strict inequality impossible. It remains a valid conditional theorem.
The source centered discrepancy, sharper paired-bisection probability,
exact Hall-candidate transport, concrete attainable Hall scalars, and
recentring on actual residual-neighbor sets all pass the 2068 audit.
The relative reserve concentration is audited as well. Reference-scale
concentration and its simultaneous finite-event bound now check; unlike
an actual-mean lower-tail argument, these allow tiny or zero codegree
means. The actual size/degree/codegree test family, its composition
with iteration typicality, and its centered-Hall application are audited.
The source link-degree
window retains the one-vertex endpoint loss. The actual joint reservoir
and cover law, its totalization on bad prior inputs, retained source
geometry, canonical marked-moment tail, and finite pinned-edge/order
unions now pass the 2114 audit. The forbidden tail is joint, not assumed
uniformly over prior fibers. A monolithic probability proof hit the
default heartbeat limit; smaller named geometry lemmas and explicit
kernel/sample-space arguments repaired it without changing limits.
Candidate pair safety, actual degree bounds, centered matching inputs,
the joint-link source failure bound, and the corrected conditional master
update now pass. Rounded caps retain the full polynomial additive-error
factor. The direct main check was rerun successfully on 27 August.
The actual simultaneous internal reserve-supply probability now checks,
as does its joint event with source link-reference concentration. Prior bad
mass is retained, and explicit exponent gaps give every prescribed inverse
power of failure. Rounded integer supply/degree/left/stopping cutoffs check.
The preliminary mixed law now supplies a fixed-moment leftover-degree
bound using the current support size, including its full additive-error
factor and prior bad-input probability. One degree event gives the internal
schedule bound, nonsampled spoke bound, and twice-degree internal spoke
loss. These events now imply success of the actual raw internal kernel.
Its rounded point scale is at most 64 divided by the reserve supply scale.
All 25 additions pass the expanded audit. Draft type-inference and cast
errors were repaired; no limits were changed. The direct main check passes.
The actual reservoir/cover kernel now supplies future-degree control
through the representable available-link family, with the M+1 fan factor.
The deterministic local/quasi typicality proof was strengthened to require
only packing and avoidance; its old full-cover theorem remains a corollary.
Thus future typicality is proved on raw outcomes without assuming coverage
on failed samples. The exact cap-driven conditional master update checks.
These ten further declarations pass the 2178 audit and direct main check.
Next: assemble the fixed-envelope preliminary law and all stage parameters
into the unconditional finite master induction.
The exact unconditional final theorem remains absent.
The proper quasi-moment now checks completely: two-colour multiplicity,
empty/triangle/edge rooted weights, canonical residual joint inclusion,
future-prefix promotion, moments, and a realized forbidden-vertex tail.
`SourceQuasiExtensionLoss` bounds the actual master-step availability loss
by pattern support, local neighbor losses, and these quasi-obstructions.
All 43 new declarations passed the expanded audit and direct main check.
Draft failures were ordinary missing lemma names and a power-monotonicity
tactic choosing the wrong direction; the explicit proofs use default limits.
Latest TeX: 107 pages, 877476 bytes, warning-free and backed up.
Next: finite forbidden-order/pattern unions, local inner-edge degree tails,
and actual stage scalar budgets. The unconditional final theorem is absent.
`SourceLinkForbiddenOrders` now identifies the forbidden sample family as
the exact finite union over orders and proves the corresponding cardinal
and probability bounds. The next estimate is the source D1 sampled
pair-collision tail; it must retain the probability of sampling both copies
of the common inner edge. The previous full-reservoir star bound is not
being substituted for this sharper estimate.
That estimate now checks in `PairWitnessSampling`: a collision at each of
`h` different neighbors costs `(M*sigma^2)^h`, using disjoint two-coordinate
witness blocks and only joint inclusion. The factorial tail retains this
gain. `SimultaneousLinkCollision` proves the actual inner-edge block
disjointness in both orientations. `SampledLinkCollisionControl` proves
that every dynamic pair-conflict at an unprocessed centre belongs to this
collision process. All seventeen additions are in the clean 1872-target
audit. Initial simplification and decidable-instance errors were repaired
without changing limits. `ReserveCommonCenterTail` now checks the source
two-spoke overlap tail, including the full additive prior-error factor;
its coordinate-count injection and next audit are being completed.
The coordinate injection, fixed sampled-count cover, canonical forbidden
tail, and simultaneous pinned-edge/order unions now check and are audited.
`RawSampledLinkCoverLaw` returns the empty family on failed bit samples,
preserving all structural properties and the exact unconditioned point
scale. `SampledLinkGoodProbability` combines sharp Hall, actual collision,
and forbidden failure events. The remaining scalar hypotheses are not
claimed automatically. Four new power inequalities bound the collision
mean and marked-weight ratio, including the nonconstant zero-prefix bank
coefficient. The 1895-target audit has no unexpected axioms or Lean errors.
Latest TeX: 105 pages, 865690 bytes, warning-free and backed up.
Next: finish the size-sensitive sharp Hall sum, derive its geometric tail,
and assemble actual stage parameters and future-typicality success.
The sharp Hall sum and its geometric specialization now check and are
included in the clean 1906-target audit; the direct main check passes.
`SmallHallCounting` bounds each size class by a power of the two side
cardinalities. `SharpHallSumBound` retains that size in the sampling
exponent, and `SharpHallGeometricTail` obtains the simultaneous bound
`8*card(O)*(N+1)^2*2^(-t)` under the explicit candidate and slack budgets.
The raw cover also records genuine link-family geometry, and
`ResidualRawSampledLinkLaw` checks the corrected three-residual-edge,
two-reserve-spoke update without a conditioning loss or added error.
These declarations and the disjoint-witness inner-edge tails now pass the
1920-declaration audit. `LinkInnerEdgeSampling` counts damage in an arbitrary
fixed internal edge set, with scale `(M+1)*sigma`, retaining the later-level
set size. The source quasi-moment reconstruction now spells out all rooted
cases and the proper-extension restriction; the TeX compiles warning-free
to 107 pages (874877 bytes) and is backed up. Next: formalize this marked
quasi-moment, then assemble actual future-typicality and stage parameters.
The remaining
future-typicality work must use inner-edge image counts and the source
marked quasi-moment, not the earlier coarse whole-vertex-star and full
rooted-active caps. Those older conditional lemmas are preserved.
`LocalForbiddenLegality` proves the exact local/global avoidance equivalence,
including the zero- and one-new-triangle cases and decoded regularization.
`LocalForbiddenStoppedLaw` proves global packing, disjointness and avoidance
on every supported stopped state. `ResidualGraphMixedAdjoin` supplies the
quantitative update directly from conditional mixed bounds, including
positive-event prior conditioning.

The corrected reserve-aware distribution, independent reserve sampling,
reserve-preserving adjoin partition and numeric update now check and are
audited. The reserve scalar proof needed explicit reassociation before
applying an inequality; no limits were changed. `InternalEdgeResidualError`
retains the preliminary additive error through the actual scheduled-edge
composition: main point scale `alpha + eta*delta`, error coefficient
`(2*J)^(card Q + card E)`. It also derives this input directly from the
sparse graph mixed law. The TeX explains these arguments and compiles
warning-free to 94 pages (806758 bytes); the checked source is backed up.

The corrected two-partition augmented-reserve update now checks and is
audited, as does its composition with the preliminary graph mixed law and
actual conditional internal kernel. The reserve-forcing link update keeps
both the three old residual edges and the two reserve spokes per new link
triangle, giving constant `2*max(C^5*factor,J)` and error `b+delta`.
Its genuine simultaneous-link specialization is audited. These updates do
not assert that the required good-fiber or scalar hypotheses hold automatically.

Uniform parameter checkpoint: `SourceUniformCoefficient` absorbs a stage
constant using the stronger eventual condition `C*t*p ≤ tau`, giving
coefficients `9*24^d` independent of recursive constants. This avoids a
circular decay-exponent choice. `KSSSHomogeneousScale` proves the exact
denominator exponent is subhomogeneous under simultaneous scaling of
`b,k,Rmin`; hence the physical ratio has a fixed positive lower bound.
Both modules are audited. A real-cast simplification was repaired at default
limits. Latest TeX: 96 pages, 813508 bytes, warning-free and backed up.

`RelativeRawInternalStructure` now checks and is audited: even failed raw
outcomes preserve packing, global avoidance, and relative scheduled-edge
provenance. `ResidualRootedThreatProbability` transfers the selected-only
rooted moment bounds without the invalid old uncovered-edge condition.
`ResidualMasterIteration` gives corrected conditioning, pushforward, and
probabilistic update rules. `InitialResidualMasterLaw` proves that the
constructed initial pattern law starts this invariant for admissible orders,
including residual even degrees and all pointwise legality clauses.
The direct main check passes. Latest TeX: 96 pages, 816522 bytes.

Corrected compression, finite induction, conditioning and terminal extraction
now check and are audited. `InitialResidualCompression` and
`EventualResidualMasterBase` provide the actual compressed base with the
original source well-spread certificates. Containment required the genuine
initial legal-availability subset lemma and explicit finite-cardinality
simplification; these repairs used default limits.

Parameter audit: the literal saved power-vortex sizes become comparable near
the root, and the earlier sufficient ambient exponent can charge the top
free exponent twice. Neither is a valid substitute for the source's gradual
contraction. The sound package is preserved. `TerminalJumpChain` checks
finite induction along a selected chain; `PowerVortexStepRatios` checks
positive, terminal and ambient size ratios. `AffineInitialVortexExponent`
checks a sharper actual initial construction with `R = Rfixed + step*ell`,
where all fixed parameters precede the choice of step and length. These new
modules await inclusion in the next expanded audit. The draft retained-chain
ratio proof has one final arithmetic elaboration issue under investigation.
`CoverDownDensityScalars` is being checked for the exact survival/reserve
and two-spoke density cancellations.

The first twenty geometry/scalar additions passed the 1727-target audit;
all eight cover-down density cancellations check. The retained-chain ratio
elaboration was repaired using an explicit cardinal inequality.
A second interface audit confirmed that old adjacent-level typicality alone
does NOT justify jumping over old levels. The correct solution, now checked
and included in the 1737-target audit, transfers the original all-neighbor
and all-proper-pattern bands to a reindexed vortex BEFORE recursion.
`ReindexedPowerSource` reproves the source prefix bounds directly from the
same absorber geometry. `ReindexedInitialMasterLaw` retains the original
distribution error instead of incorrectly reducing its old union-bound
coefficient. `InitialRetainedVortexLaw` packages these facts simultaneously
for every strictly increasing rooted reindexing, and the affine initial
construction now supplies that stronger certificate.

`RetainedPowerVortex` and `EventualGradualMasterBase` also build: the latter
chooses the finite length after the fixed initial parameters and constructs
an actual compressed base on the retained vortex for all sufficiently large
admissible orders. Their expanded audit is next. A draft
`RetainedVortexPowerGeometry` is checking the unified per-stage cardinal and
ratio exponents, including the distinct first-stage rounding cost.
Latest TeX compiles warning-free to 98 pages (828767 bytes).

The retained-vortex geometry and the dyadic stage-scale comparisons now
check and are audited. `CrossScaleRegularizationScalars` proves the actual
local/global density, coefficient and rounded-horizon inequalities.
`SourceFullRootWeight` checks the source profile sums with no omitted
triangles, including the middle-root `z/n` saving and full-root endpoint.
`ResidualReserveCandidateLaw` retains the residual-edge and reserve factors
in joint candidate prescriptions, including the additive conditional error.
The direct main check passes. The source's marked-link moment remains an
independent obligation: the old uniform reservoir bound is too coarse and
is not being substituted for it. A TeX typo found by compilation was fixed.

The marked-link edge-exposure bounds now check, including WS3's order-four
endpoint, a general pinned-edge bound, and the two-edge coefficient
`(1+(ell+1)^2)*j^ell*z/n`. `SourceLinkUnderlyingFamily` assembles the
complete nonexceptional unmarked root split. All eighteen new prerequisite
theorems are included in the clean 1777-target audit. The TeX compiles
warning-free (100 pages, 840510 bytes) and its checked source is backed up.
The multiplicity-preserving three-mark encoding and its full extension
bound now check. The initial/later classes encode a fibre of size at most
`4^(j-2)`; root deletion has exactly `j-2-card Q` remaining triangle
coordinates. Candidate edge blocks are genuinely disjoint. A noninitial,
nondistinguished triangle supplies the extra factor `p`. The sharp empty
and exceptional cases, all nonexceptional cases and the fully fixed root
are assembled by `SourceLinkMomentWeights.sourceLink_hasExtensionBound`.
No maximum-extension bound is assumed by that theorem. Its point-weight,
block-weight, fan-budget and source-scale hypotheses remain explicit.
The 1807-target audit and direct main check pass. Latest TeX: 101 pages,
844808 bytes, warning-free and backed up. Canonical source edge weights
and their precise reserve-spoke cancellations now check.
`SourceLinkFanGeometry` derives two crossing edges from exactly two inner
vertices and proves the distinguished-fan bound by an injective third-vertex
map. `SourceLinkCanonicalMoment` instantiates the whole extension theorem
with the paper's actual weights. The elementary `w ≥ 1` ratio follows from
`a ≥ 1`, `p,r ≤ 1`, and `u ≤ n`. All thirteen canonical additions are in
the clean 1820-target audit. Latest TeX: 101 pages, 845850 bytes,
warning-free and backed up.

The actual joint probability application now checks. `SourceLinkRealizedCoordinates`
identifies coordinate inclusion with the corrected full-union residual event,
including reserve prescriptions on crossing coordinates and the exact
prefix-level weight. `SourceLinkJointInclusion` handles every coordinate
set: incompatible colour or non-graph prescriptions have probability zero.
`SourceLinkCodeCardinality` proves the coordinate cutoff `4*(j-2)` and
index bound `4^(j-2)*(N+1)^(3*j)`. `SourceLinkCanonicalMomentProbability`
combines the genuine joint law and the proved canonical extension bound,
retaining the full additive error multiplied by the polynomial index count.
The 1830-target audit and direct main check pass. Latest TeX: 102 pages,
847799 bytes, warning-free and backed up. All development scans remain
clean except old English comments containing the scanned words.

Next interface check: the source bounds deletion degrees INSIDE sampled
links. The older `IsSimultaneousRootedGood` controls all rooted active
configurations, and the older relevant-bad relation filters only by ambient
candidacy, not sample membership. Those stronger conditional statements
remain valid but must not be inferred from this marked moment. Use the
sample-restricted bad relation AND the candidate-filtered local reservoir;
noncandidate bit-selected pairs must not supply hypothetical forbidden
configurations. `SampledRelevantLinkCover` now checks the local deterministic
bridge: replace `R` by `R'=R.filter r`, pass membership in `R'` as the
relation to robust Hall, and filter the reservoir in forbidden participation
as well. Both theorems are audited. The primary source Section 10.2, lines
1993--2045, confirms this is the required D2 deletion degree.

`SourceLinkMarkedWitness` now constructs the actual three-colour partition
`E∩I`, `(E\I)∩D`, `E\(I∪D)`. Historical legality supplies a noninitial
member and another terminal member; residual-edge feasibility excludes the
distinguished sampled triangle from the old selected union. Every resulting
coordinate is realized. `SourceLinkSampledForbiddenCount` chooses one
witness per sampled forbidden triangle and injects by its retained root,
proving the exact cardinal domination by the marked selected count.
The full 1842-target audit and direct main check pass. Latest TeX: 102 pages,
850455 bytes, warning-free and backed up. No new placeholders or limit
increases are present.

`SampledLinkForbiddenDegree` now checks both oriented injections from
sampled forbidden neighbors to sampled forbidden triangles. For any
dynamic state inside `I∪D∪Q` and local reservoir inside `Q`, its local
forbidden participation is global participation in that same union.
The exact total sampled bad degree is at most the sampled pair-conflict
degree plus the controlled sampled forbidden count, in both orientations.
The 1846-target audit and direct main check pass. Latest TeX: 102 pages,
851101 bytes, warning-free and backed up.

`SampledCandidateSimultaneousCover` now globalizes the filtered bridge.
Filtering each bit by ambient candidacy gives exactly the local sampled
candidate pair sets. The global filtered reservoir is contained in the
original reservoir and in availability, hence retains the original
`sigma^card Q` joint inclusion bound. The dynamic simultaneous iterator
now takes sampled deletion-degree hypotheses in these filtered reservoirs.
The 1852-target audit and direct main check pass. Latest TeX: 102 pages,
852221 bytes, warning-free and backed up.

Current next step: sum the sampled forbidden bounds over forbidden orders,
construct the source-correct good-fiber event and
discharge the actual good-fiber, scalar and
polynomial-error hypotheses of the corrected cover-down update.
The final unconditional theorem remains absent.

Sparse and residual-law checkpoint: twenty-one new modules, containing
58 new prerequisite theorems, are imported by both the main entry point
and the expanded 1649-target axiom audit. The combined entry-point/audit
build passes (4177 jobs), as does the direct main check. The audit passes:
1649 declarations, zero unexpected axiom lists, zero Lean errors. The
earlier audit-only generated-file gap was repaired. The exact unconditional
theorem is still absent.

Source Sections 9 and 10.1 confirm that extended pattern tracking is
initial-only. The ordinary sparse nibble now separates analytic exponent
`b` and stopping exponent `c`, with `2*c ≤ b`. Sharp rounded schedules
retain the actual `E/A` selection normalization. Joint ordinary-process
success supplies inactivity control; Markov's inequality retains the
exceptional prior-input loss `(badInput + bandError + crudeError) / delta`.
The coupled joint-horizon theorem and the assembled sparse conditional
mixed law now type-check.

The master audit found another literal source-interface discrepancy:
prescribing a later triangle and its own three edges double-counts initial
uncovered-edge density. `LaterEdgeDistributionObstruction` proves a
concrete finite counterexample on three vertices and eight equally likely
outcomes. At `p = 1/8`, `C = 4`, zero error, the corrected residual law
holds but the old graph-restricted law would assert `1/8 ≤ 1/48`.
This concerns an auxiliary interface, not the final existence problem.
Old definitions and their proved conditional theorems remain intact.

The corrected `ResidualGraphDistribution` tests genuine working-graph
edges uncovered by the full selected union. Its empty-test-graph bridge
reuses all selected-only crude tails. Corrected mixed coordinates, local
degree tails through all source orders, and their geometric-error cutoff
specialization also check. The supported adjoin partition exposes all
three old residual edges of each new triangle. Its product-scale and
constant estimates are proved in `ResidualAdjoinScalars`. These two
scalar lemmas and the two finite conditional-failure lemmas have individual
axiom audits using only `propext`, `Classical.choice`, `Quot.sound`.

Recovery failures: vanished temporary targets left dangling generated-cache
links. Their exact directory targets were restored without changing the
links or source configuration. The standard cache download failed with
TLS errors; local source builds restored dependencies. Transient shared
Mathlib generated-file failures were resolved by retrying after artifacts
appeared. Proof repairs used explicit function equalities and predicates,
finite-set arguments and real coercions. Broad simplification of the
finite counterexample hit the default recursion bound; an exact probability
rewrite resolved it. No computational limits were increased.

Latest completed TeX check: warning-free, 92 pages, 795068 bytes, backed up
before the next quantitative-adjoin paragraph. Twenty new-module and
entry-point placeholder/limit scans are clean. `ResidualLocalPolynomialBudget`
now checks and is audited. It retains the explicit incoming exponent loss
`3*R + R*(3*q)*s + c` in actual all-order local-degree control, instead of
requiring a geometric prior error.
`ResidualGraphAdjoinNumeric` now checks and is audited. It gives the supported current-level
triangle scale and the quantitative update with conditional additive error.
Its required positive-mass-only version of the exact adjoin probability
lemma has been added while preserving the original wrapper. Both are
audited after local-definition unfolding and shadowed-lemma repairs.
An interrupted combined build reported only an entry-point failure;
the direct recheck and full rebuild both pass without source or limit changes.
The TeX explains the factor `2*max(C^3*factor,J)` and
additive error `b+delta` before these Lean changes.
The next mathematical bridge, now detailed in the TeX, recovers global
packing and forbidden avoidance from the actual regularized local constraints.
Next: formalize this bridge and propagate the compatible
residual law through cover-down, and discharge the actual parameter hierarchy
and master recursion. In particular retain additive conditional errors and
polynomial prior-error losses; do not infer exponential decay from fixed
moments or apply the geometric-error specialization without its hypothesis.

Historical previous fully audited verification: the expanded entry point builds (4137 jobs).
The 1591-target prerequisite
audit passes with no project-local axioms. This does not audit a final
existence theorem, which is not yet present. The new stopped-law moment
and tail also check and build; they reuse sharp joint inclusion without
a factorial loss. Ordered two-family exposure and its uniform power
cancellation now check and build, as do the absorber counts for every
nonempty root size.

General initial-data and horizon checkpoint: decoding each regularized
order gives its exact auxiliary root degrees. Their degree gaps supply
configuration regularity with trajectory coefficients `Delta_(d+3)/A^d`.
The actual regularized union is initially legal and constructs the KSSS
parameter package from explicit scalar inputs. Existing pair-average and
graph-pair encodings turn triangle regularity into the pair half of the
same initial-regularity predicate. In sparse stages, `t*p ≤ tau` cancels
the extra `t` in local-degree bounds, giving fixed trajectory coefficients
and explicit density-floor inequalities. State marginals allow genuinely
data-dependent horizons and floors in both ambient and current-vertex
source-crude estimates. The stopped clock equals chosen cardinality;
the joint horizon-failure bound retains bad input, conditional band error,
and retrospective crude error as `eta + beta + epsilon`. Existing
`GlobalPatternJump` already supplied the localization witness injection;
three duplicate helpers written during this checkpoint were removed and
the existing proof reused. Two new corollaries give all localized cutoffs
when `t^(k+r)` is below every tracked-set size; this size hypothesis still
needs the later-stage hierarchy and does not replace initial absorber
localization. Main build: 4137 jobs; direct main check and 1591-target
prerequisite axiom audit pass, with no unexpected axioms or Lean errors.
All new-module scans are clean. TeX: 89 pages, warning-free and backed up.
Indexed real-time coercion, first-marginal rewriting and an import-level
name collision were fixed at default limits. Next: discharge actual
recursive-stage scalar and tracked-set inputs, apply general pattern
trajectory bounds and conditional success, then graph-restricted
well-distributedness, cover-down and master recursion. The exact final
theorem remains absent.

Current-type source-crude checkpoint: local rooted and gain configurations
map injectively into their exact ambient classes. Pair-local witnesses
preserve the pinned pair and pair-sharing exclusion; common witnesses
preserve distinctness and cross-root exclusions. Both selected remainders
are exact images. The four statistic comparisons imply ambient crude
bounds give current-type bounds. Under the unchanged prior law, the
conditional process on `W.U k` now inherits the actual ambient source-crude
failure estimate; the ambient active predicate agrees on image states and
retains the local availability floor. Main build: 4127 jobs; direct main
check and 1562-target prerequisite audit pass with zero unexpected axioms
or Lean errors. New-module scans are clean. TeX: 87 pages, warning-free
and backed up. Pair-witness data were made independent of proof-case
elimination, and finite-set inequality normalization was corrected at
default limits. Next: connect this general source crude bound to the
current-type trajectory-success construction, assemble actual regularized
initial data and graph-restricted master recursion. The final theorem is
still absent.

Current-vertex transport checkpoint: the source tail sum is now bounded at
the literal existing dyadic cutoffs on `Fin W.terminalSize`, with full
polynomial prior-error budgeting. Injective vertex maps preserve packing,
forbidden avoidance, legality, the greedy invariant and each transition.
Uniform sampling and the complete timed stopped law commute with these
maps, including frozen states. Restriction to a vertex subtype recovers
supported ambient triple systems, forbidden families and states exactly;
the support hypothesis is explicit and no constraint is silently removed.
Main build: 4121 jobs; direct main check and 1531-target prerequisite audit
pass with zero unexpected axioms or Lean errors. New-module scans are clean.
TeX: 87 pages, warning-free and backed up. Constructor equality, finite-law
decidability and one implicit embedding argument were repaired at default
limits. Next: transfer the four crude statistics from the ambient image
back to the current vertex subtype, then supply the general source crude
failure bound to the current-vertex trajectory and master recursion. The
unconditional theorem remains absent.

Global source-crude checkpoint: the exact four-statistic union bound now
checks, including the larger common selected-witness observable. A single
explicit source coefficient bounds every source-order sum and has a proved
polynomial bound in the vortex weight and source parameter. Witness and
observable cardinalities have uniform polynomial bounds. The fixed-moment
global budget retains the full amplified prior error; a separate lemma
quantifies the exponent loss for polynomially small prior errors. The
actual conditional stopped greedy law supplies both the support and joint
inclusion input for the global bound, including frozen states and without
conditioning on success. Main build: 4116 jobs; direct main check and
1498-target prerequisite axiom audit pass with zero unexpected axioms or
Lean errors. New-module placeholder/limit scans are clean. TeX: 86 pages,
warning-free and backed up. Projection types, gain exponent unfolding,
scalar monotonicity and power normalization were repaired at default limits.
Next: specialize to current-vertex power cutoffs, transport the actual
nibble to that vertex subtype, and complete graph-restricted master
recursion. The unconditional final theorem remains absent.

Four-tail and stopped-law checkpoint: all four generalized source-family
tails now check for all source orders, retaining the full additive-law
error with polynomial witness cardinalities. Forward and reverse gain
exposures preserve omission multiplicity and leave `n^(a-1)`; the final
gain exception is controlled by distinct WS2 pairs. The global crude
event uses a larger common selected-witness count than the earlier
available-pair count. Integration inspection caught this mismatch;
new injective decoding proves the required stronger tail, without
changing either statistic or weakening the event. The actual conditional
stopped greedy kernel supplies the shared old--new joint-inclusion law,
including frozen states, and initial containment supplies its terminal
support. Fixed source-cover extraction and order restriction also check.
Main build: 4108 jobs; direct main check and 1466-target prerequisite
axiom audit pass with zero unexpected axiom lists or Lean errors. New
source scans are clean. TeX: 85 pages, warning-free and backed up.
Projection inference, a universal support predicate, finite-sum product
normalization and disjointness arguments were repaired at default limits;
temporary diagnostic tracing was removed. Next: combine the exact four
statistics into a global crude failure bound, discharge fixed-moment
numerical budgets, transport the actual nibble to the current vertex
subtype, and complete graph-restricted master recursion. The final
unconditional theorem remains absent.

Forward gain checkpoint: source lifting preserves gain noncontainment,
the exact two-triangle omitted-root intersection, and the local omitted
size. The actual active gain count is dominated by fixed source witnesses.
Forward exposure records literal source partitions; its first omitted
part recovers the original omission set, giving an injective class code.
The source two-family bound and the checked forward exponent budget
leave exactly the power `n^(a-1)` for omitted size `a`. The coefficient
and power-ratio lemmas are explicit and reusable for reverse exposure.
Main build: 4095 jobs; direct entry-point check and 1433-target
prerequisite axiom audit pass with no unexpected axioms. New-module
placeholder/limit scans are clean. TeX: 84 pages, warning-free and
backed up. An intersection-inclusion argument was made explicit at
default limits. Next: reverse gain exposure, distinct equal-remainder
exception, full fourth source-union tail, actual nibble inputs and
vertex restriction, then master recursion. The final theorem is absent.

Generalized common-threat checkpoint: localized distinct configuration
pairs lift to distinct fixed-source configurations, including equal-root
cases. Terminal-bridge exposure embeds injectively into the literal
two-family source system. Good and swapped classes cancel all terminal-size
powers; the exceptional same-order class uses the off-diagonal WS2
omission bound. Finite exposure-class sums give a full extension bound.
Polynomial witness counts and decoded-image domination give the actual
common-threat tail, first for one source-order pair and then for all
ordered source pairs. Both probability-error terms remain explicit.
Main build: 4091 jobs; direct main check and 1419-target prerequisite
axiom audit pass, with only standard logical axioms. New-module scans
are clean. TeX: 83 pages, warning-free and backed up at that checkpoint.
Dependent record projections, swap reindexing, and a parenthesization
error in a finite cardinality sum were repaired at default limits.
Next: gain-defect source lifting and the fourth generalized source tail,
then actual nibble law inputs, vertex restriction and master recursion.
The unconditional final theorem remains absent.

Generalized source-union checkpoint: pair-local threats now encode
injectively into fixed source codes with a pinned terminal edge. The
nonempty mixed source bound supplies every extension weight, including
the source-order-four case. The pair-threat tail retains both the moment
term and polynomial-witness additive-error term. Finite dependent sums
combine every source order for both the pair and rooted statistics;
no independence across counts is assumed. Main build: 4081 jobs; direct
main check and 1389-target prerequisite axiom audit pass, with no
unexpected axioms. New-module placeholder/limit scans are clean. TeX:
82 pages, warning-free after rerunning labels, and backed up. Two
elaboration mismatches (finite singleton union and pair projection)
were repaired without changing limits. Next: terminal-bridge common
threats, including the distinct equal-remainder exception, then gain
defects and the actual generalized nibble. The final theorem is absent.

Generalized-root checkpoint: conditional old/new inclusion now retains the
exact prior additive error, with a vortex-weighted specialization derived
from the graph-restricted prior law. Moving prescribed selected triangles
into an enlarged source root yields a full extension-weight bound for
every root, not just an expectation. Witness cardinality is polynomial
in the ambient order. Actual localized rooted configurations encode into
these fixed source witnesses, yielding the first generalized crude tail
for one source order with both moment and additive-error terms. Main build:
4074 jobs; direct main check and 1373-target prerequisite audit pass with
only standard logical axioms. New-module scans are clean. TeX: 82 pages,
compiled without warnings and backed up. Product argument order, implicit
union coordinates, and coefficient normalization were repaired at default
limits. Next: pair-local threats via the existing mixed nonempty edge-root
bound, then distinct common threats and gain defects, source-order sums,
vertex-subtype transport and the actual generalized nibble. The final
unconditional existence theorem remains absent.

All-order fixed-envelope checkpoint: the established order inputs now
discharge a common proposal parameter `p0/2`, common horizon `n^(j-3)`,
and every blocked-family bound uniformly over the prior-data law. Finite
induction constructs deterministic regularizers for all orders with
structural properties at every state and total gap-failure probability
bounded by the sum of the orderwise budgets. Canonical fixed-shell
envelopes preserve source coefficients at every future prefix. Every
actual decoded regularized constraint is proved to localize the fixed
augmented ambient source families; packing is preserved. Main build:
4067 jobs; direct main check and 1356-target prerequisite axiom audit
pass. New-module forbidden-token scans are clean. TeX: 80 pages, compiled
without warnings after the label rerun and backed up. The final theorem
is absent. Next: generalized nibble crude-statistic bounds for these
localized fixed sources, correct vertex-subtype transport, then actual
protected-graph nibble, master recursion and final validation. Keep the
prior-law additive error explicit in the new mixed moments; the existing
absorber-specific crude theorem cannot be used for the general family.

Actual random-order checkpoint: common configuration-space encoding now
preserves the exact original regularizer output law at a shared horizon.
Decoded successful outputs have genuine auxiliary witnesses with avoidance,
uniformity, maximum-degree and gap bounds; their failure probability is
derived from the actual regularizer. These laws are assembled over varying
auxiliary types in the full prior-data distribution. A fixed deterministic
shell envelope is selected with source spread and increment certificates,
while preserving that distribution exactly. At power scales, freezing with
`rho=exp(-t/2)` retains a vanishing failure probability. Structural order
properties are separated from the old pointwise envelope-support assertion:
a fixed envelope need not lie inside every realized available universe.
Deterministic order choices have uniformity, maximum bounds, exclusion of
earlier subsets, coverage, and new-constraint containment at every state;
their gap-failure probability is bounded by the coupled witness-failure
probability in the original data law. Main build: 4061 jobs; direct main
check and 1340-target prerequisite audit pass with only standard logical
axioms. New-module scans are clean. TeX: 80 pages, compiled without warnings
after the label rerun and backed up. Namespace resolution, implicit
projection predicates, and support inference were repaired at default limits.
Next: finish the combined order-step interface, discharge uniform numerical
inputs and perform finite all-order induction, then generalized nibble and
master recursion. The unconditional theorem remains absent.

Independent-envelope checkpoint: finite monotone Bernoulli couplings,
product/restriction identities, and exact adaptive-process marginals now
check. The actual stopped regularizer is coupled below geometric proposals
in a fixed ambient universe, even when its auxiliary coordinates vary.
All accepted configurations lie in the proposal union; its joint-inclusion
bound is `(2*beta)^|U|`. A common larger horizon preserves the exact original
output law. Encoding varying auxiliary state types preserves the independent
data--seed marginal. Finite-fiber averaging selects a good fixed seed with
conditional failure below `rho` when `eta+epsilon/rho<1`; conditioning on
that seed preserves the entire original-data law. The fixed source-envelope
theorem supplies well-spreadness, separate increments, support containment,
and the explicit remaining failure budget. Main build: 4050 jobs; direct
entry-point check and 1315-target prerequisite axiom audit pass. The first
expanded audit lacked its four new module imports; adding them repaired the
harness, and the rerun reports zero errors or unexpected axiom lists. New-module
forbidden-token scans are clean. TeX: 79 pages, compiled without warnings
after the label rerun and backed up. Type inference and a dependent-rewrite
failure were repaired at default limits. Next: assemble these interfaces
over the actual prior-data law at every forbidden order, then generalize
the nibble estimates and finish master recursion. The final theorem is
still absent.

Decoded-constraint checkpoint: uniformity and exclusion of earlier
subsets prove that the regularized union is an antichain. Injective
decoding gives an inclusion-minimal forbidden family, with all members
packing and all orders in the intended range. Avoiding this family
avoids every original localized constraint. Main build: 4033 jobs;
direct main check passes; the 1236-target prerequisite audit reports
only standard logical axioms. New-module scans are clean. TeX: 77 pages
without warnings and backed up. Next: reuse vertex-support restriction,
extend absorber-specific crude process estimates to the actual
regularized family, then protected-graph nibble and master recursion.
The unconditional final theorem is still absent.

Source audit for the next step: KSSS Goodness (source lines 1339--1374)
requires ambient forbidden source families fixed independently of prior
random data. The checked pointwise adaptive augmentation and its sharp
counts do not imply that independence. The paper uses a binomial
dominating family at source lines 1939--1942. The TeX now distinguishes
the valid joint-inclusion replacement for count tails from this separate
dependency and reconstructs an independent proposal-table/thinning
coupling plus averaging argument. Next implement that coupling before
using augmented families in the generalized nibble. No existing checked
theorem is invalidated; none asserts the missing independence.

Eventual-input checkpoint: fixed power gaps now supply every numerical
condition of the source regularizer, including the full two-term failure
budget. The degree-gap allowance is the mathematical value `8192*t`.
A common threshold covers all forbidden orders and is combined with
the actual finite-order construction, retaining the separate increment
certificate. Assumptions left at this interface are the actual source
bounds, normalized local degrees, auxiliary mass, and power-scale data;
no regularization success certificate is assumed. Main build: 4032 jobs;
direct main check passes; all 1229 prerequisite axiom targets use only
standard logical axioms. New module scans are clean. TeX: 77 pages,
compiled without warnings and backed up. A multiplication-lemma name and
a local finite-index instance were repaired at default limits. Next:
decode the regularized constraint family, instantiate the actual
protected-graph nibble, and complete graph-restricted master recursion.
The unconditional final theorem remains absent.

Sharp-increment checkpoint: the actual protected graph loses at most
`|U|*n` edges, and exact edge-triangle double counting gives a regularized
family of size at least `p^3*tau*n^3/192`. Actual iteration data therefore
give a nonempty auxiliary universe and the normalized mass bound.
The initial prefix has a larger original spread coefficient than inner
prefixes; a further refinement retains only new-family count increments.
The adaptive law's original good-count event has the same proved failure
bound. Its certificate survives extraction, trimming, the finite-order
induction, and future-prefix transport. Each future prefix now keeps its
own original coefficients, adding only `(a,3*a)`; the large outer error
is not propagated. Earlier interfaces remain proved corollaries.
Main build: 4027 jobs; direct main check passes; all 1217 axiom targets
use only standard logical axioms. Changed Lean module scans are clean.
TeX: 77 pages without warnings; backup refreshed. Failures were an
existing helper name, namespace resolution, and a nonnegative-real
subtraction coercion; repaired at default limits. Next: discharge the
all-order numerical inputs at power scales, instantiate the protected
graph nibble, and finish graph-restricted master recursion. The final
unconditional theorem remains absent.

Finite-order checkpoint: supported hypergraphs decode exactly from the
available-triangle subtype, with vertex and maximum degrees preserved.
Scalar budgets now hold uniformly over every valid earlier regularized
family. A finite induction constructs all forbidden orders, exporting
uniformity, degree gap, avoidance/covers, source augmentation, and support.
The constructed families retain source bounds at all future prefixes.
This theorem has explicit numerical inputs; their eventual application
to actual stage data remains in progress. Main build: 4015 jobs; direct
main check passes; the 1188-target audit has no unexpected axioms or Lean
errors. TeX: 76 pages without warnings. Type inference, endpoint-index
normalization, and an additive-order mismatch were repaired without
raising limits. Next: actual auxiliary mass and eventual regularization
inputs, then graph-restricted nibble and master recursion. Final theorem
still absent.

Future-prefix checkpoint: the regularization output now retains exact
support of every added configuration. Pure outer-profile cardinalities
and the signed-scale inequality transport all four source well-spread
conditions to later prefixes without enlarging their coefficients.
Distinct configuration pairs and the exceptional terminal pair condition
are handled explicitly. Protected availability lies in the required
shell. The original order-step interface is preserved as a corollary.
Main build: 4008 jobs; direct main check passes; all 1167 audit targets
use only standard logical axioms. TeX: 76 pages without warnings after
the label rerun. Failures were a finite-index type inference mismatch,
an overbroad exponent rewrite, and one redundant tactic; repaired at
default limits. Next: auxiliary subtype degree transport, finite-order
regularization, then graph-restricted master recursion. Final theorem
still absent.

Power-budget checkpoint: inverse-power density bounds discharge every
numerical assumption of actual reserve regularization. Fixed exponents
with `a>=4*b+1`, `L>=4*b+c+1`, and `L>=2*b+2*e+1` give the inner-size
margin and exponential parameters growing at least linearly in `t`.
Both polynomial-exponential failure bounds tend to zero. Main build:
4003 jobs; direct entry-point check passes; the compact 1144-target
audit reports no unexpected axioms or Lean errors. TeX: 75 pages,
compiled without warnings and backed up. New module scans are clean.
Next: retain augmentation support and transport source well-spreadness
to future prefixes, then finite-order regularization and recursive
master construction. The unconditional final theorem is still absent.

Protected-regularization checkpoint: the scalar loss transfer gives the
regularizer's pair error and clique bounds on every reserve-good outcome.
The protected availability has a proved regularized subfamily. Its failure
under the actual reserve law is at most
`12*(n+1)^4*exp(-r*p^4*tau^6*n/8)`, assuming the explicit inner-size,
relative-error, and triangle-sampling scalar budgets. Original clique
estimates are supplied by actual iteration typicality; no post-reserve
regularity certificate is an additional hypothesis. Main build: 3999 jobs;
direct main check passes; all 1132 prerequisite axiom targets use only
standard logical axioms. New-module token scans are clean. TeX: 75 pages,
compiled without warnings. Two finite-family aliases and a redundant
simplification were repaired without changing any limits. Next: discharge
the reserve scalar budgets at power scales, then finite regularized-order
induction and the graph-restricted recursive master construction. The
unconditional final theorem is still absent.

Reserve-loss checkpoint: proper extension triangles lie in the clique
formed by their root pattern and extension vertex. Surviving base edges,
an extension outside the inner set, and unreserved spokes preserve that
extension in the actual protected availability. This gives the exact
finite loss bound. The existing independent reserve-edge law now has
exponential spoke tails; a fixed polynomial-size clique index gives
simultaneous failure at most `12*(|D|+1)^4*exp(-r*a/4)`. The estimates
are taken before exposing the reserve, and only then restricted to
surviving cliques. Main build: 3994 jobs; direct main check passes; all
1125 prerequisite axiom targets use only standard logical axioms.
New-module token scans are clean. TeX: 74 pages without warnings.
Failures were an adjacency/edge-set elaboration mismatch and one local
definition not unfolded by simplification; fixed without limit changes.
Next: apply the checked scalar loss transfer to regularize the protected
availability, instantiate the reserve probability budget and finite
regularized-order induction, then complete graph-restricted recursion.
The unconditional final theorem remains absent.

Stage-graph regularization checkpoint: exact injective encodings identify
ordinary graph edges, typed triples, clique support, and proper extensions.
Pair-pattern proper extensions count incident triangles exactly. Full
iteration typicality loses at most the pattern's vertex count when made
proper. The two-density correction keeps the separate availability density
and its budget cancels exactly. At error `<=1/768` and density scale
`p^4*tau^6*n>=1536`, actual iteration-typical stage data supply all geometric
regularizer inputs. For fixed `tau0>0`, `tau>=tau0`, and `p>=n^(-1/6)`,
one local-order threshold also supplies the density and sampling-failure
budgets; the ambient vertex type can be larger than the local stage.
Main build: 3977 jobs; direct main check passes; all 1107 prerequisite
axiom targets use only standard logical axioms. The compact audit checker
avoids truncating the growing output. New-module token scans are clean.
TeX: 73 pages without warnings; backup refreshed. Failures were API names
and implicit-lambda binder insertion, repaired without limit changes.
Next: preserve these clique-extension estimates after the actual reserve
and inner-graph deletion, complete finite regularized-order induction,
then the graph-restricted master recursion and final theorem. The final
unconditional Erdős 207 theorem remains absent.

All-order degree-budget checkpoint: localization commutes with source
family unions, and orders smaller than the local order contribute nothing.
The actual all-order maximum-degree tail keeps every additive error term.
For fixed moment order `s >= 3*R+1`, explicit budgets give a reciprocal
term plus a polynomial-times-geometric term, both tending to zero.
A single threshold works for all original orders, with canonical cutoff
`t*kappa`; its sum has exactly the density-normalized scale required by
the hypergraph regularizer. The actual graph-law degree-control theorem
now follows with an arbitrarily small prescribed failure probability.
Main build: 3965 jobs; direct main check passes; all 1065 prerequisite
axiom targets use only standard logical axioms. New-module token scans
are clean. TeX: 73 pages without warnings. Failures were finite empty-set
lemma spelling and one division-lemma argument, fixed at default limits.
Next: stage-graph encoding/typicality and finite regularized-order
induction, then graph-restricted master recursion. Final theorem absent.

Triangle-regularization checkpoint: the signed five-set gadget has exact
Kronecker-delta edge sums. Finite sums give the exact balanced edge mean;
the actual correction has absolute size at most `5/24`. Hereditary-layer
double counting proves the factors six and two in the eligible-clique
counts from proper extension vertices. Independent-bit relative tails
and the limit `2*n^2*exp(-n^(1/6)/16) -> 0` prove the full source triangle
regularization lemma with a threshold uniform in C. Main build: 3957 jobs;
direct main check passes; all 1048 audited prerequisites use only standard
logical axioms. New-module token scans are clean. TeX: 73 pages, checked.
Recent failures were finite-set API argument order, one missing real cast,
and Mathlib theorem namespaces, repaired without changing any limits.
Next: connect regularization to the actual stage-graph representation,
combine local degrees across configuration orders, and finish the
graph-restricted recursive construction and final theorem. The
unconditional Erdős 207 theorem is still absent.

Actual local-degree checkpoint: all mixed-root cases, including the
order-four exception and its WS3 side condition, now supply the full source
maximum-extension-weight bound. The additive-error moment theorem keeps
`epsilon * witnessCount^s`; witness counts are polynomial with explicit
coefficient. A graph-restricted strong law supplies the actual mixed
selected/residual set, excluding edges outside the working graph. Actual
local forbidden degrees inject into its selected witness count, and both
fixed-triangle and simultaneous maximum-degree tails are checked. Main
build: 3943 jobs; direct main source check passes; all 1000 prerequisite
axiom targets use only standard logical axioms. New-module token scans
are clean. TeX: 72 pages, no warnings; backup refreshed. Recent failures
were term layout, finite predicate instances, projected types, and rewrite
order; fixed without changing any limits. Next: instantiate finite order
and failure budgets, finish triangle regularization and the source-correct
recursive master transition, then terminal absorption and the final theorem.
The unconditional Erdős 207 theorem remains absent.

Mixed local-degree checkpoint: source witnesses retain the original
configuration and selected-part pair, preserving multiplicities. The
remaining terminal triangles have exactly `j-3` members and `3*(j-3)`
distinct edges. The mixed coordinate weight factors exactly, and the
unrooted estimate retains `p^(3*(j-3))`. The corrected nonempty triangle-root
case, its injective encoding, impossible-root cases, and the inverse-power
fan cancellation all check. Main build: 3927 jobs; direct main check passes;
all 957 audited targets use only standard logical axioms. New-module token
scans are clean. TeX: 70 pages, no warnings, backup refreshed at this
checkpoint. Next: finish the edge-only root cases (including order four),
combine the maximum mixed extension weight, and instantiate the actual
local-degree tail. Full order induction, graph-restricted recursion, and
the final unconditional theorem remain unfinished.

Source-correct order-step checkpoint: injective decoding preserves the
regularizer's joint inclusion. One actual law now supplies simultaneous
degree regularity and source augmentation. The exact binomial comparison
cancels graph density, and the actual forbidden family is constructed from
collision pairs, supersets of earlier constraints, and the trimmed current
family. Both rooted counting bounds, the combined `9*n^(3*k-4)` bound,
and its explicit density threshold check. The finite order-step theorem
preserves avoidance of the original family and includes all genuinely added
constraints in the well-spread superfamily. Main build: 3922 jobs; direct
main check passes; all 937 audited targets use only standard logical axioms.
New-module token scans are clean. TeX: 70 pages, no warnings; backup refreshed
at this checkpoint. Failures were ordinary instance mismatches, implicit
types, and redundant tactics, now fixed without limit increases.
Next: the source mixed edge/triangle moment estimate for actual local
forbidden degrees, then uniform order budgets and the graph-restricted
recursive master construction. The unconditional final theorem is absent.

Actual adaptive regularization checkpoint: the explicit finite-state kernel
preserves forbidden-family avoidance, both maximum-degree potentials, and
the geometric gap clock. Its horizon is the initial integer gap. The final
law has maximum degree at most nine times the original maximum, degree-gap
failure at most `2*|V|*initialGap*exp(-b/8192)`, and factorial-free joint
inclusion bounded by the geometric sum of the actual batch hazards. The
main build (3906 jobs), direct main check, and all 882 prerequisite axiom
audits pass; only standard logical axioms occur. New-module token scans
are clean. TeX compiles to 68 pages without warnings; backup refreshed.
The generic failure-bound call initially exceeded default elaboration
heartbeats; explicit arguments fixed it without changing any limits.
Next: injective configuration decoding, simultaneous regularity and source
augmentation, and the actual graph-restricted recursive construction.
The unconditional final theorem remains absent.

Actual one-step regularization checkpoint: the nonidentical-Bernoulli
product law has a checked centered exponential moment and simultaneous
subset concentration bound. The weighted hypergraph normalizer, edge
probability bounds, incident-edge bijection, and both mean losses are
proved. Under explicit binomial and forbidden-degree budgets, one common
law strictly halves the old degree spread and bounds every accepted
increment by `4*a`, with failure at most `2*|V|*exp(-a/8192)`. Its sampled
simple uniform hypergraph avoids the forbidden family, and its literal
degrees equal the counted sampling variables. Main build: 3889 jobs;
direct main check passes; all 810 audited targets use only standard logical
axioms. New-module forbidden-token scans are clean. TeX: 66 pages without
warnings, backup refreshed. Recent failures were implicit functions,
subtype sums, cast normalization, and a missing import; these are fixed
without any resource-limit changes. Next: instantiate the scalar budgets,
iterate regularization with controlled sampling probabilities, and complete
the actual graph-restricted recursive master transition and absorption.
The final unconditional Erdős theorem remains absent.

Sharp source-weight checkpoint: all three general-moment estimates now
build using the signed source profile scale. The exact cancellation keeps
`n^d/n^f`, including negative net exponents. Terminal-omission codes preserve
multiplicities; the two-family source witnesses inject into ordered exposure
codes, counting shared selected triangles only once. The source's printed
symmetric-error-to-halving inference has a checked arithmetic counterexample;
the stronger mean-centered error bound yields strict contraction and is also
checked. This is not a counterexample to the problem or regularization lemma.
Main build: 3881 jobs; direct main check passes; all 777 audit targets use
only standard logical axioms. New-module forbidden-token scan is clean.
TeX: 65 pages, no warnings at that checkpoint; the subsequent explicit
Bernoulli-concentration paragraph is awaiting recompilation. Next: actual
nonidentical-Bernoulli concentration and hypergraph regularization, then
the graph-restricted recursive master construction and final absorption.
The final unconditional existence theorem is still absent.

Simultaneous augmentation checkpoint: one actual independent-bit law now
preserves all four source well-spreadness conditions, with parameters
`(y + a, z + 3*a)` and explicit failure at most
`(j+3)*(|V|+1)^(3*j+6)*2^(-s)`. A supported successful outcome exists
when the exact finite failure bound is below one. All three pair types,
root counts, and the order-four count use this same law. The main build
(3874 jobs), direct main check, and 745-target axiom audit pass. All
audited targets use only standard logical axioms; changed-module scans
are clean. TeX compiles to 64 pages without warnings; backup refreshed.
Next: sharp source-weight interfaces and regularization for the actual
graph-restricted recursive master transition, then cover-down and absorption.
The final unconditional existence theorem is still absent.

Actual candidate-tail checkpoint: the random universe is defined as
terminal vertex-disjoint `(j-2)`-triangle sets, and packing is proved.
Complement/remainder injections give the exact polynomial root and pair
candidate counts. The order-four count is linear in the terminal size.
All three actual sampled-family tails build and are audited. Main build:
3862 jobs; direct check passes; all 691 audit targets use only standard
logical axioms. New-module token scans are clean. TeX: 62 pages, no
warnings, backup refreshed before the new zero-profile paragraph.
Next: zero-profile augmentation geometry, simultaneous failure bounds,
and source-preserving random augmentation, then the recursive transition.
The unconditional final theorem remains absent.

Random-pair checkpoint: disjoint two-bit blocks for random--random WS2
pairs and injective one-bit blocks for both mixed orientations are proved.
The actual sampled-family identity and a generating-function upper tail
give `2^(-s)` under cutoff at least four times the mean and `4*s`.
Main build: 3859 jobs; direct main check passes; the 677-target audit uses
only standard logical axioms. New sampling modules have clean token scans.
TeX: 62 pages, no warnings, backup refreshed. Remaining work includes
candidate-count budgets, the simultaneous source-preserving random
augmentation theorem, and the actual recursive transition/final absorption.
The terminal candidate universe and its extension/pair counts are being
checked separately; they are not yet part of the 677-target audit.

Actual all-prefix checkpoint: `eventually_exists_initial_typical_pattern_law_with_source_bounds`
now returns the actual initial law and source-correct absorber bounds on
every vortex prefix. Positive prefixes have fixed coefficients, from the
explicit budget `bankSubsetCount * levelSize ≤ ambientSize`; the zero
prefix uses the global empty/nonempty-bank split. WS4 retains a fixed
coefficient there as well. All earlier initial-law/state APIs are preserved.
The added exponent gap precedes the ambient exponent, so no circular
parameter choice is introduced. Main build: 3843 jobs; 662-target audit
passes with only standard logical axioms. New-source token scans are clean.
TeX: 61 pages, no warnings, backup refreshed. An uninstantiated index and
an implicit arithmetic goal caused default-heartbeat failures; explicit
indices and a direct transitive inequality fixed them, with no limit changes.
Next: random augmentation and source-correct recursive master transition.
The final unconditional Steiner-system theorem remains absent.

Source well-spreadness checkpoint: all source WS1--WS4 conditions are now
proved for localized absorber-induced families, with explicit hypotheses
`bankSubsetCount ≤ |U₀|` and `bankSubsetCount * |Uₖ| ≤ |U₀| * z`.
The signed strict-bank, finite encoding, derived-family, genuine-pair,
off-diagonal split, and order-four terminal arguments all build. The
proof preserves the full terminal denominator and distinctness in WS2.
Main build: 3841 jobs; direct main check passes; all 652 audited targets
depend only on the standard logical axioms. New-module forbidden-token
scan is clean. TeX: 61 pages, no warnings, backup refreshed.
Recent failures were ordinary implicit-parameter, finite-predicate,
coercion, multiplication-side, and lemma-name errors, now fixed.
Next: instantiate the bank/level budgets in the actual power-vortex
package, then source-correct random augmentation and recursive transition.
The unconditional Erdős 207 theorem is still absent.

Signed-profile checkpoint: the cross-multiplied monomial and exact-bank
count build, retaining negative source exponents through a positive
terminal denominator. `SourceVortexWellSpread` retains distinct pairs
in WS2. A duplicate helper name caused an integration failure; the new
module now imports the existing stronger helper instead. Main build and
direct check pass. All 618 audit targets use only the standard three
logical axioms (some use a subset); no new/project-local axioms occur.
Changed-module forbidden-token scan is clean. TeX compiled without
warnings to 59 pages and was backed up before the next strict-count
paragraph. Next: strict signed exact-bank counts, A2 localization, and
the source-correct recursive transition. The final theorem is absent.

Unconditional initial-law checkpoint: `eventually_exists_initial_typical_pattern_law`
builds, with the same fixed exponent choices and a polynomial--geometric
failure threshold below one half. One conditioned state law is supported
on exact typicality, coupled/crude bands, original absorber avoidance,
containment, and the full horizon. It also satisfies the graph-restricted
product estimate with an order-independent constant. The exact schedules
give survival at most `2*p` and point weight at most `1048576*Cρ/N`.
The common-law data were factored out of `KSSSPatternHorizon`, and the
original theorem and earlier eventual state theorems remain checked.
Main build: 3830 jobs; 606-target axiom audit: only `propext`,
`Classical.choice`, `Quot.sound`. Direct main check passes; changed-module
forbidden-token scan is clean. TeX: 59 pages, no warnings, backup refreshed.
Recent failures were coercions, natural time inference, rounded zero cases,
and support-map elaboration; all are fixed at this checkpoint.
Next: source-correct signed-profile well-spreadness and graph-restricted
recursive master transition, followed by final cover-down and absorption.
The unconditional Problem 207 theorem is still absent.

Exact typicality checkpoint: `eventually_exists_initial_typical_pattern_nibble`
now builds. The graph-neighbor identity, working/uncovered-pattern inclusion,
proper/full extension correction, positive target lower bound, and exact
nonnegative-real multiplicative inequalities are all proved. Direct main
check passes; the 566-target audit has only the standard three axioms.
TeX compiles without warnings to 58 pages, with backup refreshed. The
graph-restricted bounded sharp-law theorem also builds, reusing the
retrospective recurrence without assuming `1 ≤ C*p`.
Next: instantiate the live-edge supply and rounded schedules from the
coupled event, prove constant survival/point bounds, then complete the
signed-profile recursion. The final theorem remains absent.

Unconditional pattern-initial checkpoint: `eventually_exists_initial_pattern_coupled_nibble`
builds and supplies one actual horizon outcome with all coupled, crude,
degree, and relative-pattern bands. The root exponent precedes the bank and
global cutoff exponents; all initial and localized budgets are instantiated.
Direct main check passes. The 556-target audit has only `propext`,
`Classical.choice`, and `Quot.sound`. A missing parenthesis in the finite
threshold and a missing audit import were corrected. The latest compiled
TeX has 57 pages without warnings; the new typicality bridge paragraph is
awaiting compilation. Next: convert the bands to exact iteration-typicality,
then derive the working-graph product law and signed-profile recursion.
The unconditional final theorem is still absent.

Simultaneous relative-pattern checkpoint: the actual power-kernel theorem,
single-pattern stopped-law geometric tail, and two-sided bands over any
fixed finite set/pattern indices all build. A fixed coefficient threshold
covers every bounded pattern independently of the later bank exponent.
The finite graph-pattern encoding is polynomial and the working-graph
restriction is explicit. Initial proper-pattern errors reuse the saved
absorber loss bounds, with the endpoint correction included. The joint
localized cutoff failure bound is `|I|*N^5*2^(-t)`.
The 537-target audit passes with only standard logical axioms. The entry
point builds in 3788 jobs; newest TeX compiles without warnings to 56 pages.
Recent elaboration failures concerned casts, scope, initial-time
normalization, and finite-event predicates; all are fixed at this checkpoint.
Next: combine degree, relative-pattern, and localized-cutoff events on one
actual law; instantiate all level-size budgets with the power-vortex
package, then complete the live-edge law and signed-profile recursion.
The unconditional final theorem is still absent.

Relative-pattern checkpoint: `KSSSOnTrajectories.pattern_relative_centered_drift`
now builds from the actual coupled hazards and selector denominators, with
the remaining explicit deterministic size/Taylor budgets visible. The
relative envelope has terminal bound `16/t^b`; its growth and upper step
bound, positive pattern-target lower bound, normalized actual kernel
moments, and size-dependent exponential optimization all build.
`timedStoppedAbsorber_localizedTwoAway_relative_power_tail` gives cutoff
`|U|/t^r`. Its minimum-set-size requirement handles the constant exposed
fiber, while its ambient-size requirement handles the bank term. This
avoids a circular root-exponent choice without adding an inner vortex gap.
All 506 audited prerequisites use only the three standard logical axioms.
The first checks exposed a wrong import name, a missing positivity fact,
and algebraic normalization goals; each was fixed without changing limits.
Next: simultaneous localized bounds, remaining deterministic scalar budgets,
and actual relative-pattern concentration, followed by the live-edge law
and recursive transition. The final theorem is still absent. The latest
TeX compile has 55 pages; the newest size-proportional-cutoff paragraph
awaits compilation.

Localized-pattern checkpoint: exact source trajectory derivatives and
coefficient-explicit Taylor bounds, the absorber-localized two-away extension
weight and actual stopped-law geometric tail, and the pattern jump and
conditional second-moment estimates all build. The localized estimate keeps
the small-set factor and the fully exposed root fiber separately; it does
not use the inadequate unrestricted bank powerset coefficient. The jump
bound retains the constant pair-loss term `3 + m*K`.
The 467-target audit reports only the three standard logical axioms. TeX
compiles without warnings to 55 pages. Next: relative extension-count
concentration, simultaneous local cutoffs, live-edge law, and recursive
transition. Absolute-count error alone would not provide the required
relative precision; the writeup now records exact cancellation for `Y/f`.
The final theorem is still absent.

Earlier pattern-hazard checkpoint: the actual coupled event now supplies the
extension hazard bound with explicit coefficient
`h + m*(q+1) + (h+m)*m + choose(h+m,2)` times the coupled error.
Vertical stars are counted once per base vertex. Available two-away
threats use pair-local and common-witness overlap bounds, and excluded
base-star intersections are controlled separately. Canonical root
injectivity follows by erasing the extension vertex. The normalized
actual restricted drift and target-error quotient inequality also build.
The 432-target audit reports only the three standard logical axioms.
`KSSSPatternTrajectory` separately builds with exact first/second
derivatives and the source ODE identity; it is not yet in that audit.
Next: coefficient-explicit discrete target bounds, localized jumps,
pattern concentration, live-edge law, and the recursive transition.
The latest TeX compile produced 53 pages; subsequent analytic additions
await a new compile. The final theorem is still absent.

Pattern-statistic continuation: `PatternSurvivalKernel` proves the exact
killed expectation and its normalized selector restriction, including
no resurrection of a covered base pattern. `ProperPatternExtensions`
reuses the canonical third-vertex uniqueness lemma and bounds the endpoint
convention discrepancy by the pattern support size. `PatternExtensionDynamics`
proves exact one-step loss, symmetric closed-threat incidence, and the
transposed restricted drift. All four new pattern modules build, and the
398-target audit has only `propext`, `Classical.choice`, and `Quot.sound`.
The first checks exposed a missing decidability instance and explicit
endpoint proofs; these were fixed without changing limits.
Next: separate vertical pair stars from forbidden threats, control their
overlaps and localized jumps, and prove pattern concentration. The final
existence theorem remains absent. The latest TeX additions await compilation.

Latest coupled-process checkpoint: `KSSSPowerParameters.exists_good_horizon`
builds and checks the actual coupled nibble from explicit regular initial
data, with no assumed kernel estimates or availability floors. Both signed
trajectory tails and all four crude tails concern the same frozen law.
Residual geometry and the exact insertion counter hold on positive-mass
support. The summed failure coefficient is bounded by
`8*(q+1)^2*(N+1)^6`, and its dyadic geometric tail tends to zero.
The 264-target prerequisite audit again reports only the three standard
logical axioms. The direct main check and new-file forbidden-token scan
pass; the last TeX compile has 46 pages and awaits the latest additions.
Next: construct the initial rooted configuration regularity, using
permutation symmetry of the full Erdős family and explicit absorber
perturbation counts, then lift the source-correct estimates to the recursive
well-distributed vortex law. This is not the final existence theorem.

Unconditional degree-regular initial stage: `eventually_exists_initial_degree_coupled_nibble`
now builds and checks. The root exponent is chosen after the fixed envelope
constant, ensuring every vortex set satisfies the concentration-size bound.
The actual initial degree margins are proved from separated-level loss 15
and the outer absorber-degree bound. The common stopped law reaches its
full horizon with original coupled trajectories, all four crude bounds,
and degree bands on every vortex level. The 374-target audit reports only
`propext`, `Classical.choice`, and `Quot.sound`; direct main check passes.
Latest TeX: 52 pages, no warnings, backup refreshed.
Next: bounded-pattern extension statistics (tracked only while the base
pattern edges survive), live-working-graph distribution, and signed-profile
recursive transition. The literal unconditional fixed-pattern statement
cannot survive coverage of a base edge: all its extension triangles then
disappear. This source-scope correction is recorded in TeX and is being
formalized in `PatternSurvival`. It does not change the final problem.

Degree-martingale continuation: the explicit envelope
`16*M*t/t^s/p^(B+2)` now builds with relative error at most `16/t`.
Both actual centered drifts are nonpositive on the coupled/degree event.
Actual centered jumps are bounded by three and second moments by `64*M/L`.
The 357-target audit and direct main check pass. The vortex-size
exponential optimization also builds (not yet in that audit), using
`theta=t^s/M`, `M≥t^(2s+2b+3)`, and signed margin `8*M*t/t^s`.
Current step: apply this to the actual refined stopped law, then combine
initial margins and a finite union over all required vertex-set indices.
Existing `InitialVortexTypicality` gives initial degree loss at most 15 on
every separated inner level; the outermost full level uses the absorber
degree bound plus one. These avoid relying on the older fixed exponent
200 fine-error package for arbitrarily large `B`.
Latest TeX compile: 51 pages, no warnings. New files have no placeholders
or computational-limit changes. Final Erdős 207 remains unfinished.

Auxiliary-statistics checkpoint: exact uncovered-neighbor dynamics, the
two-neighbor jump bound, conditional second moment, pair-star drift error,
and residual-clock normalization build and pass the 346-target audit.
The statistic is proved equal to the actual residual graph degree into
the specified vertex set. `KSSSRefinedStopping` proves the trajectory and
crude failure bounds for any stronger active event by reapplying the
same concentration/moment results to that new law. The graph-restricted
distribution conversion also builds, without requiring `C*p ≥ 1`.
Next: finish the explicit degree-envelope budgets and concentration,
then the bounded-pattern extension statistics and live-edge product law.
The newest TeX additions await a cross-reference pass; last compile was
50 pages. The unconditional final Steiner-system theorem is still absent.

Unconditional initial-stage checkpoint: `eventually_exists_initial_coupled_nibble`
now builds and checks. It chooses fixed coefficient/envelope/exponent data,
constructs the actual absorber, proves initial regularity, and extracts a
state at the integer density horizon. It retains original absorber-family
avoidance, all coupled bands, all crude bounds, and fewer than `E/t^b+3`
residual pairs. This is not yet vortex typicality or a recursive law.
The 319-target axiom audit and direct main check pass; TeX compiles to
50 pages. No new axioms or computational-limit changes.

Distribution-interface audit: the old unrestricted `Sym2` prescription
includes persistent diagonal pairs. The checked
`PersistentPairDistributionObstruction` proves it forces `1 ≤ C*(p+b)`.
Fixed reserved graph edges create the same issue in the literal source
all-edges formulation. TeX records the discrepancy. The next distribution
interface restricts prescriptions to the initial working graph; old
conditional results remain intact. Next: prove the live-edge product law
and the additional vertex-set extension statistics, then the signed-profile
recursive construction. Do not regard the old stronger interface as an
unconditional input.

Initial-regularity checkpoint: `initial_absorber_coupled_regularity` now
builds from explicit small-support budgets. Pair counts, positive initial
densities, unavailable-triangle counts, and root perturbations are proved.
The unnecessary bank-pair support and flexible-root-size assumptions were
removed from this new chain by recounting over every first endpoint.
The direct main check and 304-target audit pass, with only `propext`,
`Classical.choice`, and `Quot.sound`. The new-file forbidden-token scan is
clean. TeX compiles without warnings to 49 pages. Current work: discharge
the explicit budgets using the existing power-vortex package. Recursive
well-distribution and the unconditional final theorem still remain.

Initial-regularity continuation: permutation transitivity and exact root
incidence give the full-family degree. The bank-derived extra count reuses
`DerivedAbsorberCount`; the unavailable-triangle loss uses the existing
strong two-root count. Restriction to initial availability preserves
avoidance. A deleted genuine configuration contains a proper derived
member. The new `DerivedBankVertex` lemma shows that such a member contains
a bank-support vertex outside any non-bank root. This yields a sufficient
minimalization-loss bound
`|verticesOn bank| * 2^(j^3)*(j+1)*(N+1)^(j-4)` by fixed-vertex span coding.
The combined two-sided initial root perturbation theorem, including the
separate order-four endpoint, builds and passes the 284-target audit.
The normalized coefficient and initial-error power arithmetic also check;
their final common-scale wrapper is under build verification. Latest TeX
cross-reference check has 48 pages. No new axioms or limit changes.
Next: instantiate these budgets with the actual tiny absorber, recover
pair regularity by exact double counting, and construct initial coupled
parameters. Recursive well-distribution and final absorption remain open.

Earlier coupled-kernel checkpoint: the exact indexed frozen-law union bound,
all fifteen fixed-hierarchy scalar budgets, and the actual availability,
pair-selector, and root-selector lower bounds build. The complete pair
centered kernel estimates build without extra drift/jump/variance hypotheses.
The configuration raw jump and second moment, endpoint-safe slope, actual
threat bound, and minimal-family drift estimates also build. The final
configuration centering wrapper is under direct Lean iteration. Earlier
coercion, index-rewrite, and stale imported-object errors were repaired;
no computational limits changed. The 251-target audit uses only
`propext`, `Classical.choice`, and `Quot.sound`. Next: finish configuration
centering, assemble the actual active-state kernel bounds, and prove that
residual-pair geometry is automatic on the frozen process support.
The latest completed TeX cross-reference pass has 45 pages; further
configuration paragraphs have been added and await the next TeX check.

Growing-moment refinement: all four actual stopped-process geometric tails
now check and build. The first rooted count, pair-local selected count,
common-threat selected count, and gain-defect count have `2^(-s)` tails
under their explicit positive cutoff inequalities. The old fixed-order
bounds remain intact. A stale TeX paragraph suggesting that the old coarse
bound sufficed for the growing-order application was corrected.

The finite-image collision inequality, exact available-witness/terminal
configuration correspondence, and exact three-pair-star count now check
and build. `ClosedThreatCardinality.lean` proves the full threat-count
identity up to the selected common-threat multiplicity error. The exact
diagonal correction is two for closed threats (three for open threats).
`ClosedThreatTrajectoryError.lean` and `AbsorberClosedThreatCount.lean`
also check. The former transfers pair and terminal trajectory errors;
the latter verifies the packing and order hypotheses for every subfamily
of the actual absorber forbidden family. Initial subtype/projection
rewrite errors were resolved with explicit types; limits were unchanged.
Next: bound two-root threat intersections through the pair-local and
common-threat witness images, then assemble the coupled concentration
inputs. The two-root pair-sharing contribution is proved at most nine.
The current TeX compiles to 31 pages and includes these count proofs.

The two-root and pair-star overlap estimates now check and build, with
explicit bounds `9 + 3*P + 3*P' + Q` and `3 + P`. Root targets already
fall into the mixed witness cases, so no extra two-root diagonal term
is needed. `AbsorberOrderGeometricTails.lean` checks that the actual
order classes inherit the first and fourth geometric tails; the inclusion
proof excludes singleton second configurations by their two-element
available intersection.

`CrudeStatisticIndex.lean` and `GeometricCrudeStateTails.lean` now check
and build. The simultaneous failure bound is
`4*(q+1)^2*(|V|+1)^6*(1/2)^s`, under the explicit moment-cutoff conditions.
The cardinality proof uses only polynomially many root/order indices,
not all subsets of ambient triples. Initial power-lemma arity and
association errors were corrected explicitly. `CrudeStateConsequences.lean`
also checks and builds: it supplies the pointwise overlap, terminal loss,
threat trajectory, and minimal-family redundant-witness bounds.
Next: derive discrete trajectory errors from actual derivative/curvature
estimates and close the coupled supermartingale inequalities. The full
unconditional construction is still not established. The TeX now compiles
to 32 pages; a final cross-reference pass is pending after the latest additions.

Analytic continuation: `UnitStepTaylor.lean` proves the one-step error
bound from two mean-value inequalities. `KSSSPairCurvature.lean` proves
the exact pair slope and curvature, including the polynomial representation
at zero density. The curvature arithmetic and
`KSSSPairCurvatureBound.lean` give a coefficient-explicit error bound
for the pair trajectory over a full unit interval. The source ODE slope
is identified by uniqueness of derivatives. Instance-normalization and
pointwise-function unfolding errors were fixed without raising limits.
The TeX includes the exact coefficient formula and now compiles to 33 pages.
Next: configuration-trajectory curvature at time zero, growing error
envelopes, and quantitative supermartingale inequalities.

The endpoint-safe configuration curvature is now checked and built, not
just stated. `PowerProductCurvature.lean` derives the four polynomial terms
for arbitrary natural degrees. `PowerDerivativeBounds.lean` handles the
zero-degree cases before using exponent cancellation.
`KSSSAvailableCoefficientBounds.lean` bounds the available trajectory and
both derivatives from the finite coefficient budgets.
`PowerProductCurvatureBound.lean` combines the four terms, and
`KSSSConfigurationCurvatureBound.lean` proves the explicit configuration
curvature and unit-step error. Missing derivative imports, an absolute-value
lemma name, and positivity projections were fixed at default limits.
Next: direct Bernoulli growth of the inverse-density error envelopes,
then combine these analytic and combinatorial errors in the drift inequalities.

The direct inverse-power Bernoulli inequality and both source envelope
growth bounds now check and build. `CenteredStepBounds.lean` proves signed
drift, jump, and second-moment centering; `CenteredRootConcentration.lean`
connects these to the existing root-survival concentration theorem.
`GlobalPairTrajectory.lean` reuses the repository's exact pair double count
to recover the global availability error, residual-pair count, and the
root-preserving denominator error. `ConfigurationDriftArithmetic.lean`
separates class-count and denominator errors explicitly.
`PairStarDriftError.lean` now checks the actual pair kernel against its
target equation. `ConfigurationDriftTrajectoryError.lean` checks the
positive- and zero-chosen-count target equations, retaining the crude
gain, overlap, count, and denominator errors. Remaining work is the
numerical simplification of these bounds under source parameter choices,
initial regularity, and the full coupled stopping argument. None of the
current concentration interfaces asserts those missing inputs.
The TeX compiles to 35 pages with cross-references resolved. All saved Lean development remains free
of forbidden proof shortcuts and computation-limit increases.

Continuation: source Step 1--2 was rechecked against the supplied original
TeX. The writeup now specifies positive selector-denominator bounds and
explicit scaled drift constants, including the pair coefficient
`12*k + 48*C + 60`. Next: prove these numerical inequalities in Lean,
then discharge their product budgets from the source trajectories and
crude thresholds. No final existence theorem has been added or claimed.

Explicit-scale continuation: `CoupledDenominatorBudget.lean`,
`CoupledDriftBudgetArithmetic.lean`, `KSSSIndexedThreat.lean`, and
`PairStarScaledDrift.lean` check and build. The actual pair drift has
coefficient `12*k + 48*C + 60`; the closed-threat bound includes its
two-unit diagonal correction. `ConfigurationProductBudget.lean`,
`KSSSConfigurationScale.lean`, and `KSSSConfigurationProductBounds.lean`
check and build, proving the count and adjacent-envelope product bounds
directly from the finite coefficient budgets. Both Taylor errors now
check on the source envelope scale under the explicit sufficient condition
`A0 ≤ scale * E0^2`; no time-zero division is used.
`RootSelectorDenominatorBudget.lean` builds. The actual positive- and
zero-chosen configuration drift wrappers are being checked. Fixed early
normalization and argument-order errors without increasing limits.
The TeX compiles to 36 pages. Next: combine the source-scale drift and
Taylor constants with envelope growth, and finish the concentration inputs.

The configuration drift wrappers now check and build, as do the exact
source-slope identities and both centered-drift inequalities. The upper
one-step envelope bounds also build under the residual-clock margin six.
The pair survival predicate in the sharp source branch is now explicitly
`PairUncovered`: a still-uncovered pair with an empty star must be counted
as a lower-band failure, not frozen away. Its exact conditional kernel
identity and stopped concentration theorem check and build. Existing
`PairAlive` theorems are preserved unchanged. The exact pair jump and
variance using the expected loss also check.
`KSSSTrajectoryState.lean` defines the full coupled trajectory event,
including every residual pair; its availability and closed-threat
consequences check. `KSSSPairStateDrift.lean` now checks the actual
pair drift from this event and the crude bounds, without a separate
assumed threat estimate. The terminal/nonterminal configuration jump
bounds are being rebuilt after supplying one missing explicit family
argument. Next: complete variance inputs and the frozen stopping argument.

Configuration jump and variance completion: all four bound wrappers now
build, including the special zero-chosen variance proof and the terminal
loss case. `TimedStoppedIndexedInvariant.lean` proves the indexed support
induction and exact insertion counter under active-state nonemptiness.
`TimedStoppedTwoEventSuccess.lean` checks the common-law frozen extraction;
it uses no independence assumption and no union over times.
The exact trajectory index has at most `|V|^2 + (q+1)^2*|V|^3` entries.
`IndexedBandFailure.lean` proves the signed-event comparison from an
explicit initial margin. The source trajectory-event specialization is
being rebuilt; a misspelled logical lemma name was corrected. Next:
instantiate its two signed tails with uniform quantitative jump/variance
budgets, discharge the initial margins and parameter hierarchy, and prove
the source-strength coupled concentration theorem. The unconditional
construction and final theorem are still unfinished.

The indexed trajectory-failure specialization now checks; its initial
margin is required only at tracked positive-mass outcomes. This prevents
an unjustified regularity requirement for roots that were initially
unavailable. The exact time-zero trajectory and envelope values, empty
positive-chosen classes, and the initial numerical margin are being
checked in `KSSSInitialValues.lean`.
Source audit: re-read Goodness and the initial-nibble verification. Its
first verification bullet displays `|A|/|E|`, missing the factor three
present in Goodness and exact double counting. The TeX records this;
our proofs use `3*|A|/|E|` and retain endpoint exclusions in extension
counts. This is not a counterexample to the problem.

Parameter-hierarchy reuse: the existing `DyadicPowerScale.lean` already
provides an integer scale `t` for every ambient order `N`, with
`t^R ≤ N ≤ 2^R*t^R` and explicit eventual lower bounds on `t`.
`PowerHierarchyArithmetic.lean` absorbs fixed coefficients into powers
of this scale. These are sound and reusable for the new sharp branch;
they are not the obsolete coarse-tail estimate. A useful next hierarchy
is `p ≥ t^(-b)`, `E ≥ N^2/t^b`, `A/E ≥ N/t^b`, and
`scale = N/t^a`, choosing `a > b*(B+3)+1` and then `R` large enough
to dominate the crude-gain/overlap exponents. This order avoids circular
dependence: finite trajectory coefficients first, envelope exponent `B`
next, and the common power denominator `R` last.

The time-zero identities and `KSSSInitialMargins.lean` now check.
They prove all initially tracked signed margins from the actual pair and
zero-class regularity bounds plus `3*eta*(A0/E0)+margin ≤ scale`;
positive-chosen classes are exactly empty. The initial regularity itself
is still an explicit input, not a proved property of the absorber data.
The finite envelope-exponent choice also checks. The new real-coefficient
dyadic hierarchy helpers are being checked before instantiating the
density/error power gaps. The latest TeX check is 39 pages with resolved
cross-references; a new final cross-reference pass follows the dyadic note.

Dyadic continuation: `DyadicTrajectoryScaleBounds.lean` and
`KSSSDyadicPairBounds.lean` check and build, giving the actual pair lower
bound and `error ≤ target/4` from `a ≥ b*B + 3*b + 2`.
`DyadicAvailabilityFloor.lean` builds the real floor
`N^3/(4*t^(5*b+1))` from the coupled trajectory event.
`DyadicMomentFloor.lean` builds a positive integer floor and the exact
joint-inclusion ratio with `N+1`. `DyadicCrudeCutoffs.lean` checks all
four growing-moment cutoff conditions with one explicit power exponent.
The actual stopped-law specialization is being built. Remaining tasks
include bounding the absorber coefficients on this scale, establishing
the full uniform signed trajectory tails, initial regularity, and the
unconditional recursive construction. A first audit attempt before its
new dependency finished failed only on the missing object file; the
subsequent completed 171-target audit passed with standard logical axioms.

Bank-coefficient continuation: `AbsorberCrudeCoefficientPolynomial.lean`
proves a uniform bound `D(q)*(bank.card+1)^(2*q)` for all four actual
coefficients. `PowerAbsorberCrudeCoefficients.lean` discharges them from
the saved power-vortex bank estimate and specializes the stopped tail.
`DyadicGeometricDecay.lean` proves that every fixed polynomial factor
times `2^(-dyadicPowerScale R N)` tends to zero for all orders, not only
a subsequence. These modules build. Initial cast and nonnegative-square
normalization failures were fixed without changing computational limits.

`PowerAmbientBudgets.lean` builds the explicit scalar exponent gaps for
`x ≤ L*error`, the Taylor size condition, crude domination, and the gain
scale. `KSSSPowerCrudeBudgets.lean` builds the actual two-root overlap
bound and the minimal-family redundant-gain bound with coefficient one.
`KSSSConfigurationActualProducts.lean` builds both target-numerator
products and the actual-count product. The positive-chosen assembled
state-drift proof checks; the zero-chosen branch also builds after
an explicit local-definition normalization. Next: uniform jump, variance,
and deterministic-increment power bounds, then signed concentration and
initial regularity. The TeX currently compiles to 41 pages. The final
unconditional theorem is still absent; none of the prerequisite audits
is a final existence-theorem audit.

`KSSSConfigurationStateDrift.lean` now derives both actual configuration
drifts from the coupled event, including every class-count product,
global denominator error, closed-threat error, and target numerator.
The scalar exponential-parameter optimization now checks and builds:
`theta = 1/(N^z*t^H)`, with `H ≥ v+m+1` and `R ≥ H+m+2`,
turns the dimension-scaled margin/variance estimates into exponent at
most `-t`. The uniform process estimates needed to apply this lemma
remain the next substantive obligation.

Uniform-power continuation: `KSSSUniformCountBounds.lean` builds the
actual configuration-count bound from the coupled error corridor and
`A0/E0 ≤ N`. Its scale bound explicitly retains the positive-clock
hypothesis. A failed product-positivity elaboration was repaired using
the exact nonnegative-power factors; preliminary import checks failed
only because that module had not yet built, and subsequent direct main
and full audit checks passed. `ConfigurationVariancePower.lean` checks
the move numerator, inverse-ambient second-moment bound, and centered
variance bound without discarding the essential `1/N` factor. The TeX
now compiles to 43 pages with resolved references. Next: bind the raw
jump cutoffs and variance estimates to every actual tracked class,
derive uniform deterministic increments, and apply the checked
exponential optimization to the single frozen law.

`DyadicConfigurationJump.lean` now checks and builds both actual jump
branches with bound `N^z*t^(k+2)`, including the separate terminal loss
case. The 205-target audit again reports only `propext`,
`Classical.choice`, and `Quot.sound`; this remains a prerequisite audit.
The 43-page TeX check passes with resolved references. Next: combine
the uniform actual count bounds, these jump cutoffs, and the exact
configuration variance formula, then bound deterministic increments
uniformly on the stopped time interval. All newly saved Lean files and
the entry point pass the forbidden-placeholder/limit-setting scan.

`KSSSUniformCountBounds.lean` now also derives the class-count bounds
directly from `KSSSOnTrajectories` and bounds actual closed-threat sizes.
`DyadicConfigurationVariance.lean` checks and builds both actual
second-moment branches with bound `N^(2*z)/N * t^(k+5*b+8)`.
The 209-target audit, direct main check, and 3651-job build all pass;
the TeX has 43 pages and the scoped forbidden-token scan has no matches.
The source selector-denominator floor remains an explicit input to this
variance wrapper, to be obtained from `root_selector_denominator_budget`
and the already checked density/product lower bounds at active states.

Next numerical target: the source configuration slope is bounded by
`N^z/N * t^(5*b+6)` using the same move-numerator bound and the
available-trajectory denominator. Each Taylor/envelope-increment term
is at most `N^z/N * t^(2*b+1)` once fixed coefficients are below `t`.
Thus their total deterministic increment may use exponent `5*b+7`.
Centering then permits variance exponent
`max (k+5*b+8) (10*b+14) + 2`. The checked optimization applies with
initial-margin exponent `m = a+b*q`, `H ≥ varianceExponent+m+1`,
and `R ≥ H+m+2`; jump domination must also be verified. The pair
branch needs its analogous uniform slope/variance estimates. These
calculations must be formalized before claiming uniform signed tails.

`PowerSelectorBounds.lean` now builds the root-selector density floor,
the move-numerator quotient bound with exponent `5*b+6`, and the
envelope/clock quotient with exponent `2*b+1`.
`PowerDeterministicIncrement.lean` builds their scalar combination with
exponent `5*b+7`, conditional on the source slope bound. The actual
source slope and time-uniform application remain next. A missing
absolute-value lemma name was corrected to `abs_add_le`; no limits were
changed. Latest checks: 3653-job build, direct main check, 213-target
standard-axiom audit, scoped forbidden-token scan, and a 43-page TeX
compile all pass. No final Erdős 207 existence theorem has been added.

`KSSSConfigurationSlopePower.lean` checks and builds the two endpoint-safe
source slope bounds from the trajectory counts, source threat size, and
available-trajectory floor. `KSSSDeterministicIncrementPower.lean` builds
the actual configuration and pair trajectory-plus-envelope increment
bounds using their proved Taylor and envelope estimates; the pair
slope power bound is still an input to specialize next. Latest checks:
3655-job build, direct main, 217-target standard-axiom audit, scoped
forbidden-token scan, and the 43-page TeX compile all pass.
Next: prove the pair slope and second-moment power estimates, discharge
the analytic selector floor, and assemble uniform signed concentration
on the single frozen law. Initial regularity and the unconditional
recursive absorption construction remain unfinished.

`KSSSPairPowerBounds.lean` now checks and builds the actual source pair
slope and slope-plus-drift-error bounds. `DyadicPairJumpVariance.lean`
builds the actual pair jump bound `t^(k+1)` and second moment
`t^(k+2*b+2)/N`, using the expected loss. A local denominator rewrite
was made explicit; an initial dependent-file check preceded its build
and was subsequently replaced by the successful full build and audit.
Latest verification: 3657-job build, direct main, 222-target audit
with standard logical axioms only, scoped forbidden-token scan, and
43-page TeX compile all pass. Next: uniform signed concentration and
the single-law frozen extraction, keeping initial regularity explicit
until it has been proved for the actual absorber data.

The dimension-uniform initial margin, centered power bounds, and both
actual stopped-law geometric-tail specializations now check and build.
`KSSSPowerExponentChoice.lean` constructs the concentration exponents
explicitly, with an arbitrary extra fixed denominator lower bound.
`KSSSCoefficientChoice.lean` chooses one envelope exponent for all actual
indexed drift coefficients and proves an eventual fixed coefficient
threshold. These are noncircular choices: coefficients, then `B`, then
the integer exponents, then the ambient order. Latest verification:
3662-job build, direct main, 234-target audit with standard logical
axioms only, scoped forbidden-token scans, and 44-page TeX compile.
Next: apply the signed tails uniformly over the exact trajectory index,
using residual pairs rather than nonempty stars and preserving the
positive-mass initial-tracking restriction, then the frozen extraction.

Fourth-moment progress: the indexed gain-defect remainder and its exact
cardinality, forward and reverse exposures, exhaustive three-way split,
and both exponent budgets check and build. The equal-remainder omission
injection and actual absorber exceptional weight also check and build.
Both fixed-class injections preserve the entire omission set. Their actual
absorber bounds and the sums over forward/reverse exposure codes now check
and build. The weighted three-way split and full fixed-order absorber
extension bound now check and build. Importing the third- and fourth-moment
branches exposed a collision between automatically named decidability
instances; assigning the new fourth-moment instance an explicit unique
name fixed this without changing either proposition.
The expanded 58-target audit and main rebuild pass. The actual
noncontained gain-defect pair injection checks; summing the second order
now checks and builds as well. The count is gated on root availability,
matching the source's tracking domain. Its equality with the full sum of
redundant witnesses in a minimal family now checks and builds; an overly
aggressive cardinality congruence was replaced by an explicit finite-set
equality, and the remaining natural-number cast was normalized explicitly.
The actual fourth-statistic moment and stopped-process tail now check.
An attempted check before that dependency rebuilt failed only because its
object file was absent; the subsequent complete check passed.
The moment build and expanded 62-target audit pass, with only standard
logical axioms. The new-file forbidden-placeholder scan has no matches.
Next: establish the multiplicity-preserving terminal-class loss bound
required by concentration. The TeX now spells out the pair-sharing versus
common-threat witness injection. `TerminalConfigurationLoss.lean`,
`TerminalLossWitnesses.lean`, and `TerminalLossCount.lean` now check:
the loss count is at most three pair-local selected-witness bounds plus
one common-threat selected-witness bound. Every lost configuration is
retained in an injective code; no multiplicity is discarded. Initial
errors in an erase-commutation lemma name and the order of an intersection
were corrected. Next connect these indexed selected counts to the actual
absorber forbidden family and instantiate the concentration cutoffs.

The actual-family connection now checks and builds. Singleton forbidden
members cannot enter common-threat witnesses. Packinghood excludes the
order-four antecedent, and all other nonsingleton absorber members embed
in the indexed family. `AbsorberCommonThreatSelectedMoment.lean` and
`AbsorberPairSelectedMoment.lean` check selected-witness moments and tails
for every subfamily of the actual absorber forbidden family.

Source audit: KSSS Lemma 3.7 and its crude-statistic applications use a
growing moment order. The older `2^(d*s*s)` estimate is valid but only
sufficient for fixed-order applications; its overbroad comments were
corrected while preserving the theorem. Re-read the full source proof
(lines 424--467). `BoundedIntersectionMoment.lean` checks and builds with the
stronger constant `((d+1)*(s*d+1)^d)^s`, reusing the existing bounded-subset
count. `BoundedIntersectionTail.lean` and `BoundedMomentPowerBudget.lean`
check and build the geometric tail and explicit power-scale cutoff.
`TimedStoppedBoundedMomentTail.lean` also checks the actual stopped-law
application, including support-only domination and the legal-state invariant.
The next step is to instantiate these growing-moment bounds for the four
crude statistics and complete the threat-count/trajectory concentration bridge.
The documentation correction caused a normal dependency rebuild, with no
computation-limit changes. This polynomial-in-order refinement is necessary before obtaining
the source-strength stretched-exponential crude-statistic tails.
The reverse fibre proof initially used a product constructor simplification
against a variable pair and an invalid tactic phrase; explicit projections
and finite-filter membership fixed these errors. All checks retain default
computational limits. The TeX includes the exact coefficients and compiles
to 29 pages before the latest actual-statistic paragraph.

Source audit finding: source W2 explicitly counts distinct configurations;
the older `Vortex.profiledEqualRemainderPairs` includes the diagonal.
Preserved its sound coarse results and clarified the predicate's comment.
The sharp branch now uses `distinctEqualRemainderPairs`. Its genuine
configuration span argument, injective bounded-span count, derived singleton
saving, and derived/genuine split all check. The combined actual absorber
W2 count checks and builds, with coefficient
`2 * pairExactBankExtensionCoefficient q B + 2^(j^3) * (j+1)` and exponent
`j-4`. The order-four non-derived family is proved empty. One early check
ran before a dependency had finished building; retry after completion
passed. `EqualRemainderOmissionWeight.lean` now checks: every omission witness
is retained and the sharp total bound is `2^(j-3) * W2Coefficient * n^(z-1)`.
The updated TeX compiles to 27 pages, with the source discrepancy and both
genuine/derived proofs documented. The expanded 40-target audit passes with
only `propext`, `Classical.choice`, and `Quot.sound` (the two arithmetic-only
targets use only `propext` and `Quot.sound`). The main entry point rebuilds
(3343 jobs) and checks directly. The final existence theorem remains absent.
The broad forbidden-word scan finds only ordinary English uses in older
comments ("unsafe-pair relation" and "admit transparent coarse bounds"),
not declarations or proof shortcuts; the newly added files have no matches.

- `GreedyRootedConfigurationMoment.lean` now compiles and builds. Its
  legal-state hypothesis is needed only on positive-mass support. Retaining
  the actual root cardinality in the dependent omitted-family index avoids
  a simplification timeout without changing any computational limits.
- `AbsorberRootedCount.lean` proves the sharp strong root count for the
  actual absorber-induced family, summing exact bank classes only over
  subsets of size at most `q`. `AbsorberRootedMoment.lean` instantiates the
  first crude-statistic moment with exponent `j-c-5`. Both check and build.
- `DriftErrorArithmetic.lean` and `GreedyConfigurationDriftError.lean`
  prove explicit numerator and denominator errors, including the zero
  configuration class. The usable intersection hypothesis is restricted
  to edge-disjoint triangles, as in the source; packinghood of each tracked
  configuration supplies this restriction. Both check and build.
- `GreedyConfigurationJump.lean` bounds gains and losses by two-root
  classes and proves the pointwise jump bound. `GreedyConfigurationVariance.lean`
  proves a second-moment bound using the gain-plus-loss budget instead of
  squaring the worst jump. Both check and build.
- `PackingForbiddenFamily.lean` proves that removing non-packing forbidden
  members, followed by inclusion-minimal reduction, leaves the entire
  greedy kernel unchanged. This checks and builds.
- `RootSurvivalKernel.lean` checks the exact survival-weighted expectation
  identity, the empty-survival-set case, and non-revival of unavailable roots.
  `RootObservableConcentration.lean` is the next check: it applies the existing
  finite stopped-kernel theorem through this conditioning identity.
- Re-read source Step 1--3 and the crude-statistic definitions. The terminal
  configuration class cannot use the positive-omission first moment; a
  separate two-configuration multiplicity estimate is still required.
- The previous 22-target prerequisite axiom audit passed with only standard
  axioms. The expanded 32-target audit and rebuilt main entry point are next.
- The expanded TeX compiles to 25 pages. A second pass is needed after the
  latest label changes. The main file now imports the new checked branches;
  it still explicitly does not assert the final existence theorem.

Next: the root-concentration bridge and expanded validation are complete.
`CommonThreatWitness.lean`, `CommonThreatExposure.lean`, and
`CommonThreatOrdering.lean` now check and build: the indexed remainder,
exposed-root cardinality identity, and root-exponent split are exact.
The ordered exceptional branch has empty extension root, equal orders,
and equal remainders; in the other branch the two counting exponents are
at most the actual selected-remainder cardinality. The 42-target audit
and expanded main check pass. `CommonThreatExposureClass.lean` is being
checked for the injection retaining the bridge, its finite count, exact
weight, and root-bound corollary. The first check reported dependent rewrite
errors at the subtype-valued pair encoding; unpacking that subtype before
rewriting removes the dependency on the exposure parameters. The corrected
file now checks and builds. `AbsorberCommonThreatClassWeight.lean` also
checks and builds: the nonexceptional fixed-class weight has the exact
ambient-independent bound `(r-2) * 2^(r-2+|Q'|) * B_q^2`.
Finish the uniform third-moment weight bound from this partition, then
the fourth-moment bounds, terminal losses, and coupled concentration.

The exposure code set and its bound `2^(2*|H|) * (q+1)^2` now check and
build in `CommonThreatExposureCode.lean`. `CommonThreatGoodWeight.lean` is
now checks and builds: the finite-fibre partition and the uniform sum of
all nonexceptional classes have bound `q * (q+1)^2 * 2^(7*q+1) * B_q^2`.
`CommonThreatSwap.lean` checks and builds the swap equivalence and exhaustive
three-way split. `CommonThreatWeightSplit.lean` checks and builds;
its first attempt rewrote the wrong occurrence of the reversed-order sum,
now corrected by explicitly supplying the reindexing lemma's parameters.
`CommonThreatExceptionalWeight.lean` and `AbsorberCommonThreatWeight.lean`
now check and build: the full fixed-order extension weight is bounded by
two good-class constants plus the sharp off-diagonal omission constant.
`CommonThreatFamilyUnion.lean` checks the injective order encoding and
generic summation bound. `AbsorberCommonThreatFamily.lean` and
`GreedyCommonThreatPairs.lean` check and build the aggregate weight bound
and injection of actual ordered configuration pairs into selected witnesses.
`GreedyCommonThreatMoment.lean` checks and builds the moment and stopped-law
tail. An implicit-parameter application first exhausted the default
heartbeat limit; explicitly supplying the law, state type, and coefficient
resolved it. No computation limits were changed.
`GainDefectWitness.lean` and `GainDefectExposure.lean` check the exact fourth
moment remainder and forward exposure alternative. The reverse exposure
and its equal-remainder exception are next. A transient disk-full failure
left the new exposure file empty; its complete contents were restored and
checked. No prior proof source was lost.
The updated TeX compiles to 29 pages including the detailed fourth-moment
case split. The main setup metadata was
relocated to the task-owned temporary cache after the shared disk filled;
sources were preserved.
The latest TeX source remains complete;
only the mathematical development remains incomplete, not the file itself.

## 2026-08-26 — gain defect, minimality, and the first nibble weight bound

- `ConfigurationGainDefectWitness.lean` proves that every bad gain in a
  packing with at least three available members is witnessed by a distinct
  forbidden configuration with exactly two available members. The number
  of bad choices is at most twice the number of these witnesses.
- `GreedyConfigurationDrift.lean` proves the exact conditional gain-minus-
  loss formula, including the zero-class case. Direct checks and ordinary
  Lake builds pass.
- `MinimalForbiddenFamily.lean` proves the inclusion-minimal reduction,
  avoidance equivalence, and equality of the entire greedy kernel.
  `MinimalGainDefect.lean` proves that a redundant witness in this reduced
  family has a nonempty part outside the tracked configuration and that
  every member of this outside part is already chosen. Both check.
- The rebuilt partial main entry point checks with
  `lake env lean ErdosProblems/Erdos207.lean`. It still contains no final
  existence theorem, so this is not completion of the goal.
- `KSSSTrajectoryAudit.lean` now audits seventeen prerequisites; each reports
  exactly `[propext, Classical.choice, Quot.sound]`.
- Re-read the supplied original TeX's complete four-part nibble-moment lemma
  and its proofs (source lines 933--1076). `VortexNibbleExponentSplit.lean`
  checks the two root-exponent alternatives used there.
- `OmittedFamilyWeight.lean` checks the uniform two-root omitted-member
  extension bound `2^m * B * n^(z-1)`, retaining witness multiplicities.
  The exact weighted-count formula and the finite `2^m` omission count are
  proved, not assumed. The root extension count remains an explicit
  hypothesis to instantiate from the existing configuration counts.

Next: link the first crude configuration statistic to this weight system,
then prove the two-configuration extension estimates needed for threat
intersections and the gain-defect moment. Coupled concentration, an
unconditional initial law, and the final existence theorem remain open.

## 2026-08-26 — exact configuration loss and audited prerequisites

- Checked the exact restricted-selector pair drift, including the diagonal
  `+1` for open threats. Configuration gains, retained members, and losses
  now form an exact finite partition, with the correct real increments.
- Checked root-preserving loss selectors and their transposed count.
  Reused the existing Bonferroni lemma to prove the explicit error
  `|(loss selectors).card - (d-c)*H| ≤ (d-c)*epsilon +
  ((d-c) + choose(d-c,2))*K` from uniform threat and intersection estimates.
- `KSSSTrajectoryAudit.lean` passes. Every one of its twelve audited
  prerequisites depends only on `propext`, `Classical.choice`, and
  `Quot.sound`. This is a prerequisite audit, not a final-theorem audit.
- The TeX now compiles with `pdflatex -no-shell-escape -interaction=nonstopmode
  -halt-on-error -output-directory /tmp/erdos207-tex-check.ElfMwu tex/207.tex`.
  Removed the unavailable optional list-formatting dependency, restored
  missing macros and the previously inspected document tail, and escaped
  literal underscores. The final pass produces 23 pages without unresolved
  reference warnings. A complete source backup is in that temporary directory.
- The shared volume again ran out of space. Relocated only this task's
  generated `lib/lean/ErdosProblems/Erdos207` and `ir/ErdosProblems/Erdos207`
  cache directories to `/tmp/erdos207-build-cache.6RZ4N3`, with symlinks at
  their original locations. No source, unrelated output, or cache content
  was deleted; no computational limit was changed.

Next: finish the bad-gain witness count (a distinct forbidden family with
exactly two available members), then prove the required crude moment bounds
and coupled concentration. The unconditional construction remains open.

## 2026-08-26 — source-correct coupled trajectory

- The factorial-tail initial-product chain and separate stopping scale now
  build successfully. `survival^7 ≤ (Efinal/Einitial)^4` and its canonical
  specialization are checked, as is the `T = t²` scale separation.
- Found and proved a separate quantitative obstruction in
  `AggregateTailObstruction.lean`: for `q ≥ 5`, at least two vertices,
  `scale ≥ 1`, and the canonical aggregate cutoff, the existing five-event
  failure upper bound is at least one. Increasing the witness moment or
  ambient order cannot instantiate this certificate. The valid conditional
  corridor lemmas are preserved; they are not an unconditional initial law.
- Re-read KSSS's trajectory definitions and Step 1/Step 2 calculations.
  `tex/207.tex` now records the obstruction, exact polynomial trajectory
  normalization, all first derivative identities, and explicit coefficient
  bounds. The non-vanishing `exp(-rho)` correction is retained.
- `KSSSTrajectories.lean`, `KSSSTrajectoryBounds.lean`,
  `KSSSPoissonCurvature.lean`, and `KSSSSourceNormalization.lean` pass direct
  Lean checks. They include configuration derivatives at time zero, the
  Poisson second derivative, and identification with the source's formulas.
- `GreedyClosedThreats.lean` proves exact deletion classification, symmetry,
  the self-deletion contribution, and pair-star incidence transposition.
  The source excludes the target from its threat set but suppresses a `+1`
  in one displayed exact drift equality. This term is harmless in the
  subsequent error bound, but is explicitly retained in the Lean drift.
- `GreedyConfigurationClasses.lean` proves exact one-step class transitions.
  The restricted-kernel drift and finite gain/loss partition are being
  checked next.
- Ordinary-limit Lake builds pass for the trajectory/obstruction/closed
  threat bundle (3401 jobs), coefficient bounds (3101 jobs), and the minimal
  configuration-class module (1116 jobs). The shared volume remains nearly
  full; source and unrelated artifacts are preserved.

Current phase: missing source-correct random-process estimate. Next: finish
the exact stochastic drift, control configuration losses and gains with
the crude intersection statistics, and establish coupled concentration.
The unconditional initial law, final main theorem, and final theorem axiom
audit are still outstanding. The goal is active, not complete.

## 2026-08-26 — separate residual witness order and degree cutoff

- Read the supplied KSSS22b source guide and original TeX, including the
  initial-sparsification extension statistics. The main entry point remains
  explicitly partial; no unconditional final theorem has been proved.
- Audited the new fixed-threshold vertex-star tail. Its bound is valid but
  does not supply polynomial residual-degree shrinkage at the current scales:
  it pays a variance proportional to the total number of process steps and
  requires a fixed-threshold drift comparable with the original star size.
- Added the complete factorial-moment argument to `tex/207.tex`. Counting
  all small witnesses retains the denominator `R.choose s`; only the fixed
  witness order `s`, not the growing degree cutoff `R`, enters interference.
- `JointInclusionFactorialTail.lean` passes direct Lean checking, including
  the exact expectation identity, Markov tail, binomial-ratio power bound,
  and simultaneous finite union bound.
- Added and checked the tracked-edge specialization and the sharper
  logarithmic bound `survival^7 ≤ (Efinal/Einitial)^4`.
- A dependency build failed with `no space left on device`. It was stopped;
  no source or unrelated artifact was removed. After disk space became
  available again, the same target was restarted at ordinary limits.

The subsequent aggregate-tail audit above supersedes the plan to close
the initial law by scalar choices alone.

## 2026-08-22 — coupled inverse-power outer corridor

- Audited the earlier constant-offset corridor and found that its endpoint
  hypotheses force the nominal upper barrier below the nominal lower
  barrier; it therefore cannot be instantiated by the genuine schedule.
- Replaced it with a coupled widening window of the form `A / E^k`, where
  `E` is the exact eligible-pair clock.  The cross-multiplied sharp-rate
  margins, one-step center drift, inverse-power growth, and rounded endpoint
  comparisons are all now proved at ordinary limits.
- `CoupledOuterCorridor.lean` traps the actual recursive lower and upper
  schedules between these barriers for every time through the prescribed
  stopping horizon.  `lake build ErdosProblems.Erdos207.CoupledOuterCorridor`
  passes.

The current obligation is to instantiate the coupled scale facts from the
fine dyadic power hierarchy, normalize the time-zero window against the
already proved initial offset bounds, and then feed the certified recursive
product law into the first compressed transition.

## 2026-08-21 — exact recursive initializer and fine safety margin

- `OuterOnlyRecursiveSharpSchedule.lean` now initializes the recursive
  floor/ceiling schedules directly from the exact outer cardinality and the
  near-full live-pair floor.  The scheduled availability comparisons are
  definitional, so no independent time-zero approximation remains.
- `FineInitialOuterSharpActive.lean` lifts that initializer to the power
  vortex package and discharges all structural hypotheses from fine
  typicality, the inherited outer-pair survival invariant, and the exact
  first-level cardinal estimate.
- The initial typicality exponent was strengthened from `3` to `24`.  This
  leaves room for the square-root martingale buffer and for amplification in
  the coupled upper/lower trajectory before the prescribed stopping clock.
- Direct Lean checks and ordinary default-limit Lake builds pass for the
  fine package, its exact initial pair bounds, the sharp initializer, and the
  recursive schedule chain.

The current obligation is the explicit rational arithmetic for the
perturbed quadratic corridor, using the exact eligible-pair clock and the
outside-vertex normalization.  That certificate then feeds the already
verified recursive initial-product interface.

## 2026-08-21 — fine first-level hierarchy and explicit stop clock

- Tightened the separated-vortex capacity estimate to charge only genuine
  positive levels; the first positive level may now have exponent `E - 1`.
- Added a fine initial package with typicality error `t⁻³`, retaining the
  older `t⁻¹` interface by monotonicity.  Its eventual dyadic construction
  and its near-full outer-only live-pair floor type-check.
- Added the canonical division-by-three stop clock, leaving any prescribed
  eligible-pair reserve within two pairs.
- Converted rounded quadratic corridors into the uniform lower/upper and
  availability certificate consumed by the recursive initial product law.
- Removed that product law's obsolete dependence on the quantitatively
  unusable uniform-denominator estimate; it now accepts the time-varying
  corridor certificate directly.

The current obligation is the explicit fine-error arithmetic for the
rounded corridor, followed by the existing initial compressed transition.

## 2026-08-21 — rounded ordered quadratic corridor

- Added the finite self-certifying barrier induction, including preservation
  of the natural lower-schedule/upper-schedule order from the corresponding
  deletion-rate order.
- Proved cross-multiplied sharp-rate comparisons and the automatic ordering
  of the exact outer lower and upper rates.
- Specialized the barrier induction to the outer availability formulas and
  then eliminated all recursive schedule values: it now suffices to check
  explicit inequalities at the quadratic floor/ceiling endpoints.
- Added the power-vortex initial live-pair floor, exact outer-only cutoff,
  and a dyadic exponent criterion making the first positive level small.
- Direct Lean checks and ordinary Lake builds pass through
  `RoundedOuterQuadraticBarrier.lean` and
  `InitialPowerOuterOnlyBounds.lean`.

The current obligation is the fixed-constant power arithmetic for the
rounded corridor, followed by the already checked initial product and
compressed-transition interfaces.

## 2026-08-21 — recursive product law and time-varying barriers

- Specialized the fractional envelope to the exact recursive outer-only
  schedules.  The total survival product now telescopes to the terminal
  envelope ratio, while the point-transfer term is bounded by the same
  envelope with an explicit fixed `2^(3*K)` factor.
- Packaged those estimates with the recursive trajectory targets and the
  five-event absorber failure theorem in
  `OuterSharpRecursiveProductLaw.lean`; the resulting complete initial
  product-law interface type-checks.
- Added `SharpRecursiveBarrier.lean`.  Arbitrary explicit real sub- and
  super-solutions now trap both recursive envelopes and their natural
  floor/ceiling schedules.  This replaces the quantitatively unusable
  uniform final-denominator bound in the long first phase.

The current obligation is to instantiate these comparisons with the
time-varying quadratic pair-degree barriers, then feed the certified first
product law through the localized initial compressed transition.

## 2026-08-21 — exact fractional-envelope cubic cancellation

- Verified that the attempted half-sized hybrid shortcut does not remove the
  long sparsification: its raw outside degree is too large for the internal
  cover scalar.  The corrected hybrid cardinality and gap modules themselves
  type-check, but the final assembly continues through the sharp schedule.
- Added `CubicSurvivalCancellation.lean`.  A fractional positive envelope now
  telescopes every bounded-sharp survival product; a quadratic initial pair
  count and the local `D⁻¹ R³` estimate give the required inverse-cubic
  normalization; the result feeds directly into the retrospective
  `transferPointWeight` theorem.
- Direct Lean checks pass for the new scalar module and for the updated
  hybrid schedule, package, transition-data, and initial outer-only bounds.

The current obligation is to instantiate the fractional envelope with the
recursive sharp power-vortex schedules, then pass the resulting product law
through the already verified compressed transitions and terminal extraction.

## 2026-08-21 — sharp A2 bank absorption and packaged master bound

- Proved that the number of bank subfamilies of size at most the girth
  cutoff is absorbed by the ambient level-zero cardinality once the explicit
  power-exponent gap holds.  The proof normalizes the cubic absorber-bank
  bound and keeps the strict ambient factor needed in KSSS Lemma 7.2.
- Packaged absorber separation, bounded-bank absorption, and the sharp A2
  count into the exact `HasExtensionBound` statement required by every
  positive compressed-master update.
- Direct Lean checks pass for `PowerBankSubsetAbsorption.lean` and
  `PowerLocalizedMasterExtension.lean`; ordinary Lake builds pass through
  the latter (`2513` jobs).

The current obligation is the explicit initial stopped-process schedule and
its scalar estimates, followed by the finite sequence of compressed power-
vortex transitions.

## 2026-08-21 — padded-root localization and first-moment fiber bound

- Split the empty-root localized extension weight exactly into empty and
  nonempty remainders.  The empty summand is at most six by the padded
  pair-root obstruction bound.
- Proved the stronger root-localization property of the explicit sphere and
  cycle-cover absorber: a flexible root in an arbitrary forbidden outside
  family is either present in another outside triangle or is charged to one
  of at most fourteen root candidates of an exposed vertex.
- Threaded this certificate through the padded separated-vortex and initial
  power-vortex packages without changing the older root-bounds interface.
- Combined root localization with absorber-separated levels to prove that a
  fixed localized rooted remainder `R` has at most `45 * R.card + 28`
  witnesses, independently of the ambient order and the full bank size.
- Direct Lean checks pass for `PaddedAbsorberRootLocalization.lean` and
  `SeparatedLocalizedRootedThreat.lean`; the ordinary Lake build passes
  through `InitialPowerVortexPackage` (`2066` jobs).

The remaining rooted estimate is the sharp W4 weighted count for the
distinct nonempty remainders.  It must retain the A2 local/support split and
the extra inverse ambient factor in the support branch, rather than use the
global `inducedVortexCoefficient`.

## 2026-08-21 — initial outer-only transition state

- Added `InitialPowerTransitionData.lean`.  The packaged level-zero
  pointwise master state now yields, at the first positive vortex level, the
  exact absorber-greedy invariant, outside-pair-survival invariant, and empty
  chosen-family certificate required by the sharp scheduled initial law.
- The proof derives the greedy invariant from the already checked pointwise
  master clauses and uses the separated-vortex identity `U₀ = univ` for graph
  support; its only remaining quantitative input is the explicit first-level
  pair-extension gap.
- Direct Lean checking passes for `InitialPowerTransitionData.lean`.

The current work is the explicit sharp initial schedule and its first
compressed transition, followed by the uniform later-stage scalar package.

## 2026-08-21 — all-orders dyadic power hierarchy and base law

- Defined an explicit decreasing common-base power schedule for the separated
  vortex and proved its antitonicity, exact terminal value, and capacity
  reduction to one top-power inequality.
- Defined `dyadicPowerScale E n = 2^(log₂(n)/E)` and proved the two-sided
  integer estimate `t^E ≤ n ≤ 2^E t^E`, monotonicity, and an explicit
  threshold theorem showing that the scale eventually dominates every fixed
  constant.  Thus the construction applies to every large `n`, not merely
  perfect powers.
- Proved elementary fixed-coefficient/lower-power domination lemmas and used
  them to discharge all six absorber and initial-typicality scalar
  inequalities for sufficiently large `n` under the transparent exponent
  gaps `156 * rootPower + 2 ≤ E` and `step * ell + 1 ≤ E`.
- Packaged the resulting absorber, exact power vortex, localization and root
  bounds, and initial typicality in `InitialPowerVortexPackage`.
- Generalized the deterministic compressed base-law constructor so its
  pointwise available family may be a subset of the fixed ambient family.
  Consequently every admissible packaged initial vortex now supplies the
  exact level-zero `IsCompressedMasterLaw` used by the finite induction.
- Direct Lean checks pass for `PowerSeparatedVortex.lean`,
  `DyadicPowerScale.lean`, `PowerHierarchyArithmetic.lean`,
  `InitialDyadicHierarchy.lean`, `MasterLawCompression.lean`, and
  `InitialPowerVortexPackage.lean`.

The remaining scalar work begins at the level-zero-to-one scheduled
sparsification and then the uniform sparse-reserve transition between
successive power levels.

## 2026-08-21 — absorber-separated gradual vortex

- Proved that every absorber-graph vertex lies in the bank support, using
  the absorption-bank certificate on the empty leave.
- Constructed an explicit cardinal vortex whose every positive level is the
  flexible root set together with a prefix disjoint from the entire absorber
  support.  Positive-level cardinalities are exact whenever the scheduled
  free size fits the available complement.
- Proved the corresponding mixed initial-typicality theorem: only level zero
  pays the global polynomial absorber loss; every positive level uses the
  uniform root degree bound `15` and rooted extension loss `h + h^2 * 36`.
- Packaged the padded high-girth absorber, separated vortex, exact level
  sizes, support bounds, localization, root bounds, and initial typicality in
  `PaddedAbsorberSeparatedVortex.lean`.
- Direct Lean checks pass for `InitialVortexTypicality.lean`,
  `SeparatedCardinalVortex.lean`, and
  `PaddedAbsorberSeparatedVortex.lean`; the ordinary Lake build passes for
  `SeparatedCardinalVortex`.

The remaining obligation is the explicit eventual scalar hierarchy: choose
the logarithmic/power-sized free-level schedule, feed the scheduled initial
law into the first compressed transition, iterate the sparse-reserve later
transition, and invoke terminal extraction.

## 2026-08-21 — localized fixed-reserve terminal success at later stages

- Replaced the remaining ambient rooted-cap demand in the fixed-reserve
  residual-internal cover by the exact cap on missing third vertices in the
  next vortex set.
- Added the localized fixed-reserve supply and raw-kernel packages, then
  threaded their localized outcome through the correlated later stage,
  relative residual-link reconstruction, rooted conditioning, sparse
  conditioning, inherited master support, and the sparse compressed
  transition.
- Both conditioning losses now use `strongLocalizedRootedTail`, and both
  extension hypotheses use `LocalizedRootedThreatWitness`; the terminal
  internal-cover certificate and the probabilistic cap therefore refer to
  the same candidate set.
- Direct Lean checks pass through
  `RelativeReserveProtectedSparseCompressedTransition.lean`.

All known structurally overstrong ambient-root hypotheses have now been
removed from the initial and later transitions.  The remaining obligation is
the explicit eventual finite parameter hierarchy and gradual-vortex
instantiation.

## 2026-08-21 — localized master loss threaded through all transitions

- Proved the localized deterministic master extension-loss decomposition and
  its cardinal and `ℝ≥0` bounds.  Only forbidden completions whose missing
  third vertex lies in the actual future extension set are charged.
- Lifted that estimate through the common master typicality-loss event, its
  finite-law probability bound, the supported robust-link transition, and
  the star-capped typical transition.
- Updated both the first initial-product transition and every later
  reserve-protected sparse transition to use a rooted-active cap on the
  current vortex, rather than the quantitatively impossible ambient cap.
- Generalized the explicit localized master-union extension bound to every
  later multiplier `p ≤ 1`, and proved the ambient inverse-power lower bound
  used for the finite `b` parameter.
- Direct Lean checks pass for all new localized modules and both updated
  transition modules.  Ordinary Lake builds pass through
  `LocalizedSupportedCompressedTypicalStarTransition.lean`.

The structural obstruction in the later master update is removed.  The
remaining obligation is the explicit finite scalar hierarchy for the
initial sharp schedule, the gradual vortex transitions, and the terminal
extraction.

## 2026-08-21 — localized first transition and prefix-vortex weight

- Replaced the globally charged first rooted-cap event by the exact localized
  event whose missing triangle has its third vertex in the scheduled next
  vortex set.  Proved the corresponding first-moment bound, extraction,
  conditioning, residual-link partition, preliminary/internal composition,
  initial product stage, and first compressed transition.
- Proved a sharp localized rooted-threat extension estimate.  The only free
  designated-triangle choice contributes `|U|`, rather than the ambient
  vertex order.  Both multiplier regimes are formalized; for multipliers at
  least one an explicit one-power-shifted coefficient handles a designated
  triangle already present in the planted root.
- Proved that a triangle's level in a vortex prefix embeds to its full-vortex
  truncated level.  Consequently the exact initial master-union point weight
  is dominated by multiplier two on the prefix, giving the required localized
  master extension bound by pointwise monotonicity.
- Direct Lean checks pass for
  `VortexLocalizedRootedThreatWeight.lean`,
  `LocalizedMasterUnionRootedThreatWeight.lean`, and every localized stage
  through `LocalizedInitialProductCompressedTransition.lean`.  The ordinary
  Lake dependency build for `VortexLocalizedRootedThreatWeight` completes
  successfully (`1764` jobs).

The first compressed transition now has an explicit, finite rooted-extension
constant.  The current obligation is to instantiate the remaining scalar
inequalities across the gradual vortex and feed the terminal compressed law
to the already checked outside-packing reduction.

## 2026-08-21 — exact outer-only residual-incidence interface

- Removed an overstrong first-transition hypothesis which charged every edge
  outside the next vortex set to the outer-only initial process.  Crossing
  edges are deliberately never selected there, so such a global survival
  estimate cannot hold at the required small error.
- Replaced it by the exact event needed by the internal cover: a uniform cap
  on stars in `preliminaryResidualInternalEdges`, whose two endpoints both
  lie outside the next vortex set.  Added a generic conditioning lemma for an
  explicitly bounded residual-star event and threaded this corrected event
  through the initial internal stage, rooted residual-link stage, and first
  compressed transition.
- Proved that the sharp scheduled tracked-edge law supplies the corrected
  event with the existing explicit union-bound tail.  Also proved that the
  canonical outer-only absorber-greedy initial state simultaneously carries
  the absorber invariant and outside-pair-survival invariant supplied by
  iteration typicality.
- Direct Lean checks pass for all modified modules through
  `InitialProductCompressedTransition.lean` and for the new sharp scheduled
  outer-only residual-incidence theorem.

The first transition is now quantitatively compatible with the gradual
vortex.  The next obligation is to package these two sharp scheduled outputs
into the first compressed transition and then close the finite scalar
hierarchy used at every later sparse-reserve stage.

## 2026-08-21 — gradual-vortex correction and scheduled initial support

- Corrected the proposed top-level route: the checked one-stage terminal
  extraction is a valid specialization, but the padded absorber occupies
  `O(|X|^156)` vertices, while a sparse residual-link transition requires
  residual outer incidence small compared with `|X|`.  A single initial
  sparsification cannot satisfy both constraints.  The complete construction
  must therefore use the gradual vortex already described in `tex/207.tex`.
- Added `OuterOnlySharpScheduledInitialProductLaw.lean`.  It combines the
  time-dependent sharp scheduled product estimate with the absorber-greedy
  support invariant, yielding in one theorem the initial product law together
  with subset, packing, forbidden-avoidance, and first-vortex-disjointness
  certificates required by the first compressed transition.
- Its direct Lean check passes, and
  `lake build ErdosProblems.Erdos207.OuterOnlySharpScheduledInitialProductLaw`
  completes successfully (`2003` jobs).

The current obligation is to feed this supported scheduled law into the first
compressed transition, then instantiate the explicit gradual vortex and close
the finite scalar hierarchy for the later sparse transitions.

## 2026-08-21 — one-stage terminal extraction and initial-phase composition

- Specialized the general terminal extraction theorem to level one of the
  one-stage vortex.  The new theorem turns a suitable compressed master law
  directly into the outside packing required by the KSSS cover-down interface.
- Proved the exact powerset convolution for two consecutive selected/uncovered
  initial product phases.  The event for the union is partitioned by the old
  prescribed triangles, while every prescribed uncovered edge is required to
  survive both phases.
- Derived a scalar composition theorem: survival probabilities multiply, the
  strong constant becomes `2 * C₁ * C₂`, and errors combine as
  `b₁ + b₂ + b₁ * b₂`, with explicit control of large patterns.
- Direct Lean checks and an ordinary Lake build pass for
  `InitialProductComposition` and `OneStageTerminalExtraction` (`2072` jobs).

The one-stage extraction remains useful as a specialization and regression
check, but the final construction uses the gradual-vortex induction.

## 2026-08-21 — sampled reserve and sparse residual-link transition

- Replaced the quantitatively invalid `preCap + dInc` lower-link loss by the
  correct sparse-reserve decomposition.  A protected preliminary triangle
  has at most one inner vertex, so all of its crossing edges lie outside the
  sampled reserve; conditioned nonsampled crossing stars, rather than the
  full preliminary clock, control the resulting residual-link upper bounds.
- Proved exact binomial sampled-link degree and codegree tails, a simultaneous
  sampled-link event, and its union bound.  Conditioned the independent
  reserve before the later preliminary/internal randomness and retained both
  the deterministic compressed-law support certificate and the sampled-link
  bounds.
- Added the sparse rooted output and conditioned simultaneously on rooted
  threat caps, preliminary-star caps, and nonsampled residual crossing-star
  caps.  The actual residual-link lower degree now loses only `dInc`; upper
  degree and codegree add only `dCross`.
- Completed the corresponding compressed transition in
  `RelativeReserveProtectedSparseCompressedTransition.lean`.  Its direct
  Lean check passes, and its ordinary Lake build completes successfully
  (`2116` jobs).

The remaining construction obligation is the top-level instantiation.  The
current route uses a one-stage vortex: all future-stage typicality budgets are
vacuous, while the sparse sampled reserve supplies the terminal link scale.
The next step is to combine the padded absorber, pure initial compressed law,
one sparse transition, and terminal extraction under one explicit eventual
parameter hierarchy.

## 2026-08-21 — sparse-reserve preliminary caps replace full reserve

- The full-crossing-reserve specialization was a useful diagnostic but cannot
  close the vortex step: it removes every crossing pair from the preliminary
  graph, while the residual link cover cannot absorb all of those pairs when
  the next vortex layer is much smaller.
- Reverted to the genuine sparse reserve and proved the exact surviving
  geometry: every protected preliminary triangle meets the next vortex set in
  at most one vertex.
- Proved that localized covered neighbors inject into preliminary triangles
  through their outside center.  The preliminary C4 law survives the attached
  internal kernel as an unchanged marginal, so a binomial union bound permits
  simultaneous conditioning on strict preliminary vertex-star caps and rooted
  threat caps.
- Packaged the conditioned law in
  `RelativeReserveProtectedCappedRootedOutput`, proved localized loss
  `caps(v) + d`, and updated the later compressed transition to use a uniform
  bound `preCap + dInc`.
- Direct Lean checks pass for the probability bridge, correlated stage,
  two-cap rooted conditioning, localized loss, and compressed transition.
  Ordinary Lake builds pass through
  `RelativeReserveProtectedLocalizedLoss` (`2092` jobs).

The remaining construction obligation is to instantiate this sparse-reserve
transition with one explicit vortex/scalar hierarchy and connect the last
compressed law to the absorber extraction.

## 2026-08-21 — full crossing reserve removes preliminary localized loss

- The previous `2 * n + d` localized-loss estimate was formally correct but
  quantitatively unusable: the preliminary clock `n` is quadratic in the
  current vortex order, whereas the residual-link degree scale is linear.
- Specialized the crossing reserve to density one and proved that its law is
  supported exactly on all crossing edges.  Consequently the protected
  preliminary graph has only outside--outside edges, so every supported
  preliminary triangle is disjoint from the next vortex set.
- Threaded this outer-only certificate through the relative preliminary,
  correlated, and rooted laws.  Proved that the preliminary family contributes
  zero localized neighbors, leaving the exact deterministic loss `d` from the
  scheduled internal-edge incidence alone.
- Updated the complete later compressed transition to use loss `dInc`.
  Direct Lean checks pass for every modified module; ordinary Lake builds pass
  through `RelativeReserveProtectedLocalizedLoss` (latest: `2092` jobs).

The remaining construction obligation is the explicit hierarchy: instantiate
the initial product transition, the full-reserve later-stage constructor at
each compressed level, and the final absorber extraction with one common set
of sufficiently-large scalar choices.

## 2026-08-21 — localized loss and complete later compressed transition

- Threaded the stopped preliminary process's exact clock invariant through
  both conditioning layers and the relative correlated rooted output.  Every
  supported preliminary addition therefore contains at most `n` triangles.
- Proved a structural packing estimate that such a family covers at most
  `2 * n` neighbors of any outside vertex in the next vortex layer.
- Combined that estimate with the scheduled internal-incidence cap `d` to
  derive the previously missing localized loss bound `2 * n + d`; no
  vertex-disjointness from the next layer is assumed.
- Built the complete later-stage constructor from the twice-conditioned
  reserve-protected law through rooted conditioning and the sharp star-capped
  compressed master update.
- Direct checks pass for the new localized-loss and transition modules, and
  `lake build ErdosProblems.Erdos207.RelativeReserveProtectedCompressedTransition`
  completes successfully (`2112` jobs).

The remaining construction obligation is now numerical and finite: choose a
single explicit hierarchy of vortex sizes and error/density parameters that
instantiates the initial constructor, every later transition, and the final
absorber extraction.

## 2026-08-21 — relative correlated stage and rooted residual links

- Completed the reserve-protected preliminary/raw-internal composition over
  an arbitrary old `I/D` packing.  The sharp update charges only the new
  family at base `alphaPre + etaPre * Dint⁻¹`, while preserving selection,
  old/new disjointness, packing, forbidden avoidance, and exact accumulation
  into the terminal raw chosen family.
- Generalized the relative composition input to a support-sensitive
  leave-graph hypothesis; this is the form supplied by a conditioned
  compressed master law.
- Conditioned the complete relative correlated law on the rooted-cap event
  and constructed its canonical residual links with the old `I/D` split.
  Proved algebraically that the resulting `internalStageFamily` is exactly
  the correlated new difference, including away from law support.
- Direct checks and ordinary Lake builds pass for
  `RelativeReserveProtectedCorrelatedStage.lean` (`2083` jobs) and
  `RelativeReserveProtectedCorrelatedRooted.lean` (`2090` jobs).

The next obligation is the later compressed transition: combine this rooted
output with localized preliminary/internal loss control and the existing
star-capped robust link update, then instantiate the finite vortex/scalar
hierarchy.

## 2026-08-21 — first product law enters the compressed induction

- Combined the partition-preserving rooted initial product law with the
  sharp star-capped compressed master update.
- The distinguished long-nibble family remains the probabilistic `initial`
  family, while the deterministic state keeps `I = D = ∅` and treats the
  complete preliminary/internal family as the current-stage family `R`.
- The initial pointwise certificate now supplies typicality, leave support,
  triangle structure, parity, and legality at this boundary; no duplicated
  postulates are needed.
- `InitialProductCompressedTransition.lean` passes its direct Lean check and
  ordinary Lake build (`Build completed successfully (2107 jobs)`).

The next obligation is the analogous reusable constructor for a later
compressed law after pointwise conditioning, followed by the explicit
finite scalar hierarchy shared by all vortex stages.

## 2026-08-21 — correlated reserve-protected terminal extraction

- Defined the exact final family, augmented reserve, and canonical residual
  links of the correlated preliminary/internal stage.
- Connected the rooted correlated output law to the supported terminal
  typical-link pipeline, including structural packing, reserve avoidance,
  mixing, Hall, rooted-deletion, and normalization hypotheses.
- `ReserveProtectedCorrelatedTerminal.lean` passes its direct Lean check and
  its ordinary Lake build (`Build completed successfully (2102 jobs)`).

The one-stage scalar audit rules out using this theorem directly at density
one: its terminal side-deletion allowance would have to dominate the ambient
order while its residual-link lower bound is supported only on the much
smaller absorber root.  The current obligation is therefore the first scalar
constructor in the gradual compressed vortex iteration; the correlated
terminal theorem is retained for the final, low-density stage.

## 2026-08-21 — parity derived inside the sharp compressed transition

- Proved deterministically that a master cover step preserves even degrees:
  the old graph is the disjoint union of the graph covered by the selected
  triangle packing and the updated graph, and the covered part has degree
  twice the number of selected triangles through each vertex.
- Removed the sharp star-capped transition's unsupported postulate that the
  updated random graph is even.  It now assumes only parity of the old
  supported graph and derives updated parity from simultaneous-cover support.
- Direct checks pass for `MasterIterationUpdate.lean` and
  `SupportedCompressedTypicalStarTransition.lean`; ordinary Lake builds pass
  for both dependency targets (latest: 2,070 jobs).

The current obligation is the scalar constructor for the first compressed
stage: instantiate the rooted partition-preserving intermediate law, robust
link parameters, and initial pointwise/cumulative support in one checked
transition.

## 2026-08-21 — tracked residual law and partition-preserving compression

- Exposed the sharp edge-only survival law for arbitrary bounded trackable
  edge families in the stopped initial process, then specialized it to the
  fully scheduled sharp process.  This replaces the unusable coarse mixed
  product bound in the residual outer-incidence conditioning step.
- Conditioned the initial product law on bounded residual outer incidence
  while retaining the reserve-aware strong law, and composed it with the raw
  internal cover.  Direct checks and ordinary builds pass for the tracked
  residual and bounded-sharp modules.
- Generalized the supported compressed master transition so its structural
  `I/D/R` decomposition may differ from the probabilistic `initial/later`
  classification, provided the latter is a disjoint partition of the same
  accumulated family.  The first-nibble family therefore remains `initial`
  after compression instead of incorrectly acquiring a later-stage scale.
- `MasterIterationData.lean` and
  `SupportedCompressedMasterTransition.lean` pass ordinary Lake builds; both
  supported typical-transition callers pass direct Lean checks.
- Rejected the one-stage shortcut quantitatively: the absorber root must have
  size at most about `n^(1/156)`, whereas a single supported initial phase
  cannot reduce the residual degree to that scale.  The active construction
  is the gradual finite-vortex induction from the mathematical writeup.

The current obligation is to condition the raw internal law on rooted
success, reconstruct its residual links with structural `I = D = ∅`, and
feed the resulting partition-preserving law into the first nonterminal
compressed transition.

## 2026-08-21 — reserve-protected law and fixed-reserve composition

- Proved the product law for the preliminary greedy process in the exact
  reserve-protected graph, retaining independent costs for newly selected
  triples and residual nonsampled crossing edges.
- Conditioned the preliminary endpoint on bounded residual internal
  incidence without losing trajectory support, reserve avoidance, or the
  normalized two-family product estimate.
- Built the fixed-reserve internal kernel and composed it with the augmented
  reserve distribution law.  Active reserve wedges are transferred through
  the protected geometry into the pair-safe candidate family used by the
  scheduled internal cover.
- Direct checks pass for
  `PreliminaryResidualInternalFixedReserveKernel.lean`,
  `PreliminaryResidualInternalFixedReserveComposition.lean`,
  `ReserveProtectedPreliminaryInternalComposition.lean`, and
  `ReserveProtectedConditionedPreliminaryLaw.lean`.  The conditioned-law
  ordinary build completed successfully (1,985 jobs).

The current obligation is the reserve-good event used before the preliminary
process.  It must simultaneously give every residual internal edge enough
active reserve wedges and leave at least one protected preliminary extension
for every protected outer edge, with a uniform failure estimate suitable for
`jointBind_conditionedReserveEdges`.

## 2026-08-21 — reserve-protected preliminary geometry

- Formalized the exact KSSS preliminary graph `G \ (R ∪ G[U])` as the
  spanning graph whose edges are the outer edges of `G` outside the sampled
  reserve.
- Restricted the preliminary availability to triples whose three pairs lie
  in that graph, and proved that every selected preliminary family is
  disjoint from the reserve.
- Proved that a residual outside edge and two active reserve spokes define a
  triangle avoiding both the old and preliminary packings; lifted this to an
  inclusion of every active reserve-wedge vertex in the pair-safe internal
  candidate family.
- Identified the protected graph's residual outer edges with the original
  residual outer edges minus the sample, and proved that sampled reserve
  union new residual crossings is the standard augmented reserve.
- `ReserveProtectedPreliminaryGeometry.lean` passes its direct Lean check and
  ordinary Lake build (`Build completed successfully (1974 jobs)`).

The current obligation is the law-level bridge: run the conditioned
preliminary kernel on this reserve-dependent graph/family, retain the mixed
selection/non-sampled-residual estimate, and bind the verified internal
kernel using the active-wedge inclusion above.

## 2026-08-21 — polynomial exact-bank coefficient repair

- Restricted every exact absorber-bank code to bank subfamilies of cardinality
  at most `q`, which is forced by the definition of a short forbidden
  configuration.
- Reindexed the local and aggregate pair two-away sums over
  `subsetsUpToCard B q`; the exact bank intersection is proved to lie in that
  finite index set.
- Replaced the exponential `2 ^ |B|` coefficient by the polynomial bound
  coming from `card_subsetsUpToCard_le`, and propagated the correction through
  the local and aggregate absorber coefficient bounds.
- Direct Lean checks pass for `PairTwoAwayAbsorberBound.lean`,
  `PairAggregateTwoAwayAbsorberBound.lean`,
  `AbsorberCoefficientBounds.lean`, and
  `AggregateAverageAbsorberCoefficientBounds.lean`.  The paired dependency
  build completed successfully (1,744 jobs).

The current obligation is the exact existence closure: instantiate the
one-stage vortex from a padded absorber, run the supported long preliminary
and internal kernels, and discharge the scalar hypotheses of the robust
terminal extraction theorem.

## 2026-08-21 — support-aware preliminary/internal composition

- Bound the support-restricted preliminary law to the existing-reserve
  internal kernel at the next vortex layer.
- Normalized the genuinely new internal family exactly as
  `Mstar ∪ (Q \ (I ∪ (D ∪ Mstar)))`, retaining the old `I/D` split in
  the reserve-aware distribution law.
- Constructed the canonical residual links on the conditioned joint support
  and proved every intermediate-link, center, side, and reserve-spoke
  certificate needed by the simultaneous robust-link stage.
- `SupportedPreliminaryInternalStage.lean` passes its direct Lean check and
  its ordinary Lake build (`Build completed successfully (2028 jobs)`).

The next obligation is to instantiate the robust simultaneous link-cover
law on this support and apply the support-sensitive one-step master update.

## 2026-08-21 — support-aware relative preliminary kernel

- Generalized the stopped preliminary product estimate to an arbitrary old
  packing, charging only the newly selected difference from the initial
  chosen family; its conditioned and explicit-`epsilon` forms pass direct
  Lean checks.
- Added a support-sensitive law-of-total-probability estimate and threaded it
  through both the exact and numeric augmented-reserve updates.  Totalized
  state-dependent preliminary kernels now need their sharp estimate only at
  old states of positive mass.
- Built the totalized conditioned relative preliminary kernel.  On ready
  states it is supported on terminal activity, satisfies the pure product law
  with explicit `1 - epsilon` denominator, and retains the complete relative
  greedy trajectory certificate.
- Proved the structural endpoint needed by the internal stage: the genuinely
  new triples lie in the old stage availability, are disjoint from the old
  `I/D` split, and their union with that split is a packing.
- Direct checks pass for `FiniteJointBind`,
  `ConditionedPreliminaryGreedyJointLaw`,
  `PreliminaryAugmentedReserveLaw`,
  `PreliminaryAugmentedReserveNumeric`, and
  `SupportedConditionedPreliminaryKernel`; updated dependency builds pass.

The next obligation is to bind this supported preliminary kernel to the
existing-reserve conditioned internal kernel and the robust link kernel in a
single stage constructor, while retaining cumulative coverage and selection.

## 2026-08-21 — active-conditioned preliminary law

- Proved the preliminary selected/residual product estimate with the terminal
  activity event included, so the estimate has no additive stopped-process
  error.
- Conditioned the stopped preliminary law on full terminal activity.  The
  resulting law is supported entirely on completed preliminary states and
  satisfies a pure product estimate for prescribed selected triangles and
  prescribed residual crossing edges.
- Exposed the conditioning loss uniformly: if inactivity has probability at
  most `epsilon < 1`, the two product bases are at most
  `alpha / (1 - epsilon)` and `eta / (1 - epsilon)`, while the conditioning
  event itself has probability at least `1 - epsilon`.
- `ConditionedPreliminaryGreedyJointLaw.lean` passes both its direct Lean
  check and an ordinary Lake build (1,954 jobs before the final explicit-
  denominator strengthening; its strengthened source check also passes).

The next obligation is to compose this completed preliminary law with the
state-dependent reserve conditioning and sharp internal-edge kernel, then
instantiate the robust simultaneous link law in one supported master step.

## 2026-08-21 — existing-reserve conditioning and terminal extraction

- Added the missing ordering bridge for the actual master pipeline.  An
  existing reserve-aware law (after reserve sampling and the preliminary
  phase) can now be conditioned directly on internal-kernel readiness; a
  failure bound `epsilon < 1` gives event mass at least `1 - epsilon` and
  the exact factor loss `C / (1 - epsilon)`.
- Bound the conditioned law to the sharp supported internal-edge kernel and
  retained both the reserve-aware update and complete internal-edge cover
  support.
- Proved a terminal shortcut with no weakened conclusion: support of the
  intermediate residual-link state and the final simultaneous link cover
  supplies an actual `IsMasterCoverStep`; any positive-mass joint outcome,
  together with cumulative coverage, is immediately a
  `HasKSSSOutsidePacking` certificate.
- Direct checks pass for
  `ConditionedExistingReserveInternalUpdate.lean` and the strengthened
  `MasterCoverDownExtraction.lean`.  An ordinary combined Lake build with
  `ConditionedPreliminaryGreedyJointLaw.lean` completed successfully
  (2,051 jobs).

The next obligation is the intermediate-stage scalar instantiation and
finite vortex induction.  Only intermediate stages require the verified
typicality/rooted-cap update; the final stage now exits directly through the
support theorem above.

## 2026-08-21 — preliminary selected/uncovered law verified

- Proved the exact uniform probability of retaining a prescribed uncovered
  edge family in one active greedy step, as a finite cardinality ratio.
- Double-counted edge--triangle incidences: if each prescribed edge has at
  least `d` available extensions, at least `|B| d / 3` current choices cover
  one of the prescribed edges.
- Lifted the resulting one-step survival factor together with selected
  triangles through the entire stopped trajectory, obtaining the checked
  product `alpha ^ |Q| * eta ^ |E|`.
- Correctly separated threshold loss.  The genuine residual event is bounded
  by the activity-gated product event plus the terminal probability that the
  available family has fallen below `D`; no contraction is asserted on a
  frozen state.
- Identified the stopped residual with
  `preliminaryResidualCrossingEdges` and proved the full equation-(8.7) form
  `alpha ^ |Q| * eta ^ |E| + epsilon`, including the impossible case where a
  prescribed edge lies outside the crossing graph.
- Direct checks pass for `StoppedGreedyUncoveredSurvival`,
  `GreedyCoveringChoiceCount`, and `PreliminaryGreedyJointLaw`; ordinary Lake
  builds pass through the first two dependency chains.

The next obligation is quantitative: derive the uniform per-edge supply from
the regularized preliminary family throughout every active state and prove
that the terminal availability-floor failure has probability at most the
chosen additive error.  These two inputs turn the checked conditional law
into the concrete preliminary `Mstar` kernel used by the augmented-reserve
master update.

## 2026-08-21 — sharp internal-stage probability scale verified

- Bridged every successful internal random-greedy outcome to the canonical
  intermediate graph state and residual links, and totalized this
  construction as a finite law whose support retains the exact certificates.
- Removed an unnecessary factorial loss from the generic inhomogeneous
  joint-inclusion argument.  The sharp recurrence now bounds simultaneous
  inclusion by the product of the cumulative point hazards.
- Specialized the sharp theorem to the internal C4 process: every prescribed
  family of newly chosen triangles has probability at most
  `D⁻¹ ^ |Q|`, with no horizon factor.
- Integrated that exact `D⁻¹` cost into the conditioned reserve/internal
  update.  `InternalEdgeIntermediateState`, `InternalEdgeIntermediateLaw`,
  `SharpInhomogeneousJointInclusion`, `SharpInternalEdgeC4Law`,
  `SharpInternalEdgeSupportedKernel`, and
  `ConditionedInternalReserveUpdate` pass their direct checks; the new sharp
  dependency chain also passes ordinary Lake builds.

The next obligation is the preliminary `Mstar` law.  Its uncovered crossing
edges must be adjoined to the sampled reserve, and the KSSS preliminary
joint-inclusion estimate must prove that this augmented residual reserve is
strongly well distributed before the sharp internal kernel is applied.

## 2026-08-21 — probability-level T1--T3 closure verified

- Proved the deterministic extension-loss decomposition: an extension lost
  at a master step is accounted for by a pattern vertex, a removed incident
  edge, or a rooted forbidden completion.  Cardinal and `NNReal` budget
  versions now discharge the exact T2--T3 typicality clause.
- Proved simultaneous selected-star and rooted-active cap tails.  C4
  joint-inclusion bounds control every selected triangle star; strong
  well-distributedness supplies the rooted configuration moments; a finite
  union bound combines the two failures.
- Packaged those cap events into `MasterTypicalityLossEvent`, then into the
  reserve-aware probability-level master update.  The update derives all
  next-stage degree and extension clauses on one common event rather than
  postulating typicality in every supported outcome.
- Exposed the updated strong-distribution law and used it to derive the
  rooted-active cap failure bound directly from reserve-aware simultaneous
  link hypotheses.  `MasterExtensionLoss`, `MasterTypicalityLossCaps`,
  `MasterTypicalityLossProbability`, `ReserveAwareMasterIterationCapsUpdate`,
  `StrongRootedThreatProbability`, and
  `ReserveAwareMasterIterationStrongRooted` pass direct Lean checks; the
  dependency builds through the new probability modules also pass.

The next obligation is to compose the preliminary and internal cover laws
with this explicit one-step endpoint, then choose the finite scalar hierarchy
and iterate it down the vortex to produce `KSSSOutsidePackingTheorem`.

## 2026-08-21 — conditioned reserve/internal C4 update verified

- Replaced deterministic selection of one favorable reserve realization by
  a positive-probability simultaneous wedge-supply event.  The exact
  Chernoff union bound is now retained at the law level and works in every
  state-dependent fiber of a joint master law.
- Proved dependent joint conditioning: if every reserve fiber fails with
  probability at most `epsilon < 1`, the joint good event has probability at
  least `1 - epsilon`; conditioning preserves reserve-aware strong
  distribution with the explicit factor loss `C / (1 - epsilon)`.
- Strengthened the internal-edge stage pointwise: every good reserve outcome
  supports a complete scheduled random-greedy cover, and the genuinely new
  triangles satisfy the uniform exponential C4 estimate
  `internalEdgeC4Factor D horizon ^ |Q|`.
- Bound that pointwise kernel to an arbitrary reserve-aware master law.  The
  update preserves all prescribed reserve-edge factors, advances the
  later-triangle scale under explicit numeric assumptions, and retains the
  internal-edge coverage certificate in support.
- Direct checks pass for `FiniteJointConditioning`,
  `SimultaneousReserveWedgeLaw`, `ConditionedReserveMasterLaw`,
  `InternalEdgeConditionedKernel`, and `InternalEdgeReserveAwareUpdate`.
  Ordinary builds pass through the first four (latest: 1,760 jobs).

The next obligation is to combine this correlated internal kernel with the
preliminary outside-cover law, then feed their union and the verified
simultaneous link kernel into the one-step master update with next-stage
typicality.

## 2026-08-21 — reserve-aware simultaneous master update verified

- Strengthened strong well-distributedness to retain independent inclusion
  factors for prescribed reserve edges, and proved the upgrade after the
  reserve-edge Bernoulli sample.
- Proved that every genuine simultaneous link-family packing contributes
  exactly two distinct crossing reserve edges per selected triangle.  A
  structurally impossible prescribed family now has probability exactly
  zero; a possible family retains its sharp C4 inclusion bound.
- Constructed the robust simultaneous cover law with support remembering
  both the link-cover certificate and the originating link family, and
  connected residual links to the sampled reserve once all nonreserve
  crossing edges have been covered.
- Factored the exact per-triangle contribution as
  `alpha * C^2 * reserveDensity^2`, recombined every powerset part with the
  next later-triangle scale, and discharged the complete scalar partition
  inequality under explicit parameter comparisons.
- Direct checks and ordinary Lake builds pass through
  `ReserveStrongWellDistributed`, `LinkReserveAccounting`,
  `ReserveAwareSimultaneousMasterLaw`,
  `SimultaneousRobustLinkCoverFamilyLaw`, `ReserveSupportedResidualLink`, and
  `ReserveLinkFactor`.  `LaterTriangleScaleUpdate` passes its direct check.

The next obligation is to package this verified law update with the internal
cover law, pointwise master-step support, parity, and next-stage typicality,

## 2026-08-21 — corrected stage separation at compressed transitions

- Corrected the sharp initial transition so that newly chosen internal
  triangles are charged at the output level `i+1`, rather than at the old
  typicality level.  The old interface made the first nontrivial scale
  inequality impossible because it compared an inner-stage sampling rate to
  the ambient-level triangle weight.
- Decoupled the stage indexing of the strong product law from the stage
  indexing of the old pointwise typicality certificate in the generic
  compressed master update.  Both stages advance to the same output, but they
  need not already coincide before the update.
- Propagated that separation through the localized star-capped transition and
  the sparse relative transition.  The direct checks pass for
  `SupportedCompressedMasterTransition`,
  `SupportedCompressedTypicalStarTransition`,
  `InitialProductCompressedTransition`, and
  `RelativeReserveProtectedSparseCompressedTransition`; ordinary Lake builds
  pass through the first two updated dependency chains.

The next obligation is to compose the conditioned reserve, relative
preliminary, correlated internal, sparse rooted, and compressed transition
steps into the reusable later-stage induction wrapper, with the old
pointwise stage kept separate from the new product-weight stage.
then iterate the resulting master kernel down the vortex.

## 2026-08-21 — simultaneous C4/robust-link stage verified

- Encoded every chosen outer link in one dependent-sum Bernoulli reservoir;
  the center/outside separation makes the global pair-to-triangle map
  injective, so the complete reservoir satisfies the exact C4
  joint-inclusion inequality.
- Constructed conditioning and deterministic-selection laws for good global
  reservoirs, including the per-triangle-base form needed by the
  strong-distribution update.
- Proved a simultaneous two-sided robust-Hall union bound over every center
  and every oriented small-obstruction group, with a candidate-count
  specialization manufacturing the disjoint witness groups.
- Added the exact dynamic bridge from a robust global sample to a safe
  simultaneous crossing-link cover.  Unsafe pairs are precisely pair
  conflicts or forbidden participants; bounded deletion degree on both
  orientations gives a safe matching at every reached state.  Covered-degree
  and rooted-active cutoffs imply those two deletion-degree bounds.
- Added the joint-law adjoin identity and factor-absorption theorem: the C4
  link law can be adjoined to an old strongly distributed law by partitioning
  each prescribed family over its powerset.
- Direct checks and ordinary Lake builds pass through
  `ConditionedEncodedSelection`, `SimultaneousLinkReservoirSampling`,
  `SimultaneousLinkCoverLaw`, `FiniteJointBind`,
  `StrongWellDistributedAdjoin`, `SimultaneousRobustHallSampling`, and
  `SimultaneousRobustLinkCover` (latest build: 1630 jobs).

The next obligation is the one-outcome global rooted-active cutoff for all
centers and all dynamically reached states, together with its scalar failure
estimate.  Combining it with the robust-Hall bound will give the positive
good event required by the simultaneous C4 cover law.

## 2026-08-21 — relative-extension-preserving dynamic link stage verified

- Proved a support-sensitive relative-extension tail estimate for one
  Bernoulli link reservoir and combined it with the rooted cutoff and every
  two-sided robust-Hall witness event on one sampled outcome.
- Strengthened the safe matching endpoint so the selected matching is
  retained as a subfamily of its reservoir.  A root-changing monotonicity
  lemma transfers the reservoir extension bound to that actual matching.
- Added scalar and iteration-typical single-center wrappers returning both
  the safe residual-link cover and the post-matching relative-extension
  certificate, including the empty-link case.
- Added an arbitrary-invariant dynamic center iterator and specialized it to
  the remaining-center point weight.  Injectivity of the outside-center map
  bounds the initial total weight by three sampling densities, independently
  of the number of centers.
- Lifted the threaded invariant through the master crossing-cover assembly.
  `IterationDynamicMasterLinkStageRelativeExtension.lean` now returns the
  exact `IsMasterCoverStep` certificate together with the terminal relative
  extension bound for the enlarged packing.
- Direct checks and ordinary Lake builds pass through
  `TwoSidedLinkCoverRelativeExtension`,
  `RobustHallSamplingScalarRelativeExtension`,
  `IterationChosenLinkCoverRelativeExtension`,
  `DynamicCrossingLinkInvariant`,
  `DynamicCrossingLinkRelativeExtension`,
  `DynamicMasterCrossingCoverRelativeExtension`, and
  `IterationDynamicMasterLinkStageRelativeExtension` (latest build: 1904
  jobs).

The next obligation is the law-level C4 output for the complete simultaneous
link-matching stage, followed by the updated strong-distribution and
iteration-typicality estimates.  The deterministic per-state bridge is now
fully available and no longer loses the relative extension invariant.

## 2026-08-20 — reduced dynamic scalars and relative-extension extraction verified

- Replaced the remaining state-dependent link-density, bisection, sampling,
  endpoint-degree, and rooted-failure hypotheses by fixed scalar budgets and
  deterministic monotonicity lemmas.  The resulting reduced dynamic master
  wrapper leaves only the genuinely relative extension bound to be supplied
  by the outer random law.
- Proved the exact product/binomial identity for the union weight of the
  initial and later master families.  Strong well-distributedness now gives a
  joint-inclusion estimate for every bounded prescribed subfamily of that
  union.
- Proved an abstract relative-extension theorem: a joint-inclusion estimate
  for a selected family bounds the expected extension weight after deleting
  it, with the point weight augmented by the new relative weight.
- Took a finite union bound over every root occurring in the bounded
  configuration family.  Consequently one outcome of a strongly
  well-distributed master law satisfies a uniform `HasExtensionBound` for all
  relative remainders simultaneously.
- Direct checking passes for `StrongRelativeExtension.lean`; an ordinary Lake
  build of it together with `IterationDynamicMasterLinkStageReduced.lean`
  completed successfully (1903 jobs).

The next obligation is to compose the outer-law extraction with the internal
cover and link-reservoir joint-inclusion laws, so the reduced dynamic link
stage receives its relative extension budget at every reached state.

## 2026-08-20 — joint Bernoulli link/root event verified

- Proved that the encoding of a sampled bipartite link pair by its triangle
  through the current center is injective.  Consequently an arbitrary fixed
  family of reservoir triples has joint-inclusion probability at most the
  corresponding power of the Bernoulli sampling density (and probability
  zero if one of its triples is outside the link image).
- Applied the relative rooted-threat configuration moment bound to that
  exact link law and took a single finite union bound over the disjoint union
  of both link sides.  Failure of a natural-number cutoff is converted to the
  Markov threshold `rootCutoff + 1`, avoiding an off-by-one loss.
- Added the scalar-budget corollary which directly supplies the `hrootBad`
  hypothesis of the corrected robust-Hall link-cover theorem.
- Direct checks and ordinary Lake builds pass for
  `LinkReservoirSampling.lean` and `LinkReservoirRootedMoment.lean` (latest
  build: 1626 jobs).

The next obligation is the outer-law estimate for the relative rooted
extension budget at a dynamically reached master state, followed by the
degree and numeric parameter bounds needed to invoke the dynamic link stage.

## 2026-08-20 — dynamic crossing-link master bridge complete

- Replaced the unsound fixed-link iterator by a finite state-dependent
  crossing-link sweep.  Each outer center is now partitioned using the exact
  residual graph at the state where that center is processed, so triangles
  chosen for earlier centers cannot invalidate later link obligations.
- Proved the dynamic master wrapper: coverage by the enlarged total packing
  is transferred to the newly selected stage family using the invariant that
  the current graph lies in the leave of the old selected families.
- Proved residual containment from the internal-edge cover and residual
  parity at every reached state.  The parity proof isolates `P ∩ A`; old
  selected triangles need not be triangles of the current graph because they
  cover no current graph edge.
- Joined iteration typicality, paired balanced-bisection sampling, the empty
  residual-link case, two-sided Hall mixing, sampled obstruction counting,
  and concrete deletion/root bounds into one chosen single-center extension.
- Assembled the preceding facts into
  `exists_masterCoverStep_of_dynamic_link_scalars`, which simultaneously
  handles every outer center under uniform statewise scalar estimates.
- Direct checks and ordinary Lake builds pass through
  `DynamicCrossingLink`, `DynamicMasterCrossingCoverStage`,
  `DynamicResidualStructure`, `IterationChosenLinkCover`, and
  `IterationDynamicMasterLinkStage` (latest build: 1886 jobs).

The next obligation is to derive the uniform degree/root cutoffs and discharge
the remaining scalar inequalities from the KSSS parameter hierarchy, then
feed the resulting master step into the law-level iteration update.

## 2026-08-18 — chosen residual-link typicality bridge complete

- Added independent paired balanced-bisection sampling and an exact fair-bit
  literal tail estimate.  Pair classification proves
  `degree ≤ 2 * doublePairs + singlePairs + 2`; the resulting scalar union
  bound chooses one bisection with the required minimum cross degree.
- Added the ambient available-link relation and exact bridges to both
  orientations of `linkAvailableRelation`, including degree and codegree
  cardinalities.  Full-link upper bounds pass deterministically to each side.
- Specialized iteration typicality to one-edge and two-edge-star patterns.
  The formal lower-degree estimate retains the exact one-vertex endpoint
  loss; the codegree target is `p^3 * eta^2 * |U|`.
- Restricted these full next-level bounds to the exact residual-neighbor set.
  Every lost link neighbor is charged to an edge already covered at the
  center, while upper degrees and codegrees pass by inclusion.
- Composed the residual estimates, paired sampler, corrected two-sided Hall
  calculation, and concrete deletion bounds.  The complete single-center
  chain now produces both a chosen `IsResidualBipartition` and the safe
  `HasLinkCoverExtension` required by the master crossing-cover stage.
- Direct source checks and ordinary Lake builds pass through
  `PairedBisectionDegreeScalar`, `IterationLinkExtensions`,
  `IterationLinkTypicality`, `ResidualLinkTypicality`,
  `IterationChosenLink`, and `TypicalChosenLinkCover` (latest build: 1879
  jobs).

The next obligation is uniform scalar parameter discharge and simultaneous
instantiation at every outer center, followed by the remaining master-stage
probability/update estimates.

## 2026-08-18 — corrected two-sided Hall and chosen-link interface

- Replaced the false all-obstruction robust-Hall premise by the KSSS
  two-sided small-obstruction argument: small Hall sets are controlled in
  each orientation, while a large left obstruction would induce a small
  right obstruction by complementation.
- Added exact relation-counting, sampling, left/right deletion, normalized
  mixing, second-moment, and codegree-moment layers, culminating in a safe
  two-sided random link cover.
- Added `ChosenCrossingLink.lean`, so the link stage consumes a genuinely
  chosen balanced residual bisection rather than the arbitrary canonical
  half used by the preliminary interface.
- Added `ChosenMasterCrossingCoverStage.lean`, lifting that correction through
  the complete deterministic master-step assembly while preserving selection,
  disjointness, packing, forbidden avoidance, and outside-edge coverage.
- Direct source checks and ordinary Lake builds pass through every corrected
  two-sided module and `ChosenCrossingLink.lean`.  The chosen master-stage
  module is the current check target.

## 2026-08-18 — robust link-matching cover endpoint complete

- Added `LinkMatchingTriangles.lean`.  A bijection between two separated
  inner vertex classes now gives an edge-disjoint family of triples through
  one outer center, covering every spoke on both sides.  The file also proves
  the old/new packing union lemma and a reservoir-relative forbidden-safety
  criterion.
- Added `RandomLinkMatchingCover.lean`.  The exact robust Hall sampling
  theorem is now connected to concrete triples: the candidate-count and
  finite union-bound hypotheses produce an available matching family which
  remains a packing with the prior family, avoids all forbidden
  configurations, and covers the full bipartite link.
- Direct source checks and ordinary Lake builds pass for both modules.

## 2026-08-18 — concrete B-stage blockers and rooted moments complete

- Added `InternalEdgeRandomBlockerBound.lean`.  Residual graph degree and a
  rooted-active cutoff now discharge the random cover law's support-uniform
  blocker premise; a second theorem derives that cutoff from the initial
  rooted count and a per-new-triangle witness bound.
- Added `RelativeRootedThreatMoment.lean`.  The relative remainder
  `rootedThreatRemainder z \ P₀` is proved to encode exactly the rooted
  witnesses active after adjoining a random later-stage family to `P₀`.
- Extended `InternalEdgeRandomMoments.lean`: B4 now yields moments and Markov
  tails for the actual rooted-active forbidden count, in addition to vertex
  stars.
- Direct source checks and ordinary Lake builds pass for all three modules;
  the latest moment build completed 1750 jobs.

## 2026-08-18 — internal-stage moment output complete

- Added `InternalEdgeRandomMoments.lean`, converting B4 into a joint-inclusion
  estimate for the genuinely new family `chosen \ P₀`; prescribed families
  meeting `P₀` are handled as impossible events.
- Applied the finite configuration-moment lemma to every vertex star and
  derived both the exact moment estimate and its Markov upper tail.
- Direct source checking and an ordinary Lake build pass for
  `InternalEdgeRandomMoments.lean` (1748 jobs in the module build).

## 2026-08-18 — random internal-edge cover stage complete

- Strengthened `InternalEdgeProcessInvariant` with the exact insertion budget
  `(chosen \ P₀).card ≤ exposed edges` and proved threshold nonfailure for
  every reachable state satisfying a legal-candidate floor.
- Proved the quantitative reserve legality inequality: if the active reserve
  supply exceeds the union of pair and forbidden blockers by `D`, then at
  least `D` legal reserve third vertices remain.
- Added `InternalEdgeRandomCoverStage.lean`.  It tracks ambient containment
  through the scheduled kernel, combines the simultaneous reserve event with
  a uniform blocker bound, and constructs a terminal law all of whose support
  covers every internal outer edge.
- The same terminal law satisfies the horizon-free B4 estimate
  `P[Q ⊆ chosen] ≤ |Q|! D⁻ⁿ` for every family `Q` disjoint from the
  initial packing.
- Direct source checking passes for `InternalEdgeRandomCoverStage.lean`.

## 2026-08-18 — scheduled internal-edge random greedy and B4 complete

- Added `InternalEdgeRandomGreedy.lean`: a finite time-inhomogeneous law
  exposes each internal outer edge once, skips already covered edges, chooses
  uniformly from legal reserve-supported third vertices above a threshold,
  and records threshold failure in an absorbing bit.
- Proved support-level correctness: every positive-mass state is a legal
  greedy extension, and every nonfailed terminal state covers the complete
  scheduled edge list.
- Proved the scheduling injection: a triangle with two endpoints outside the
  inner vortex set and third vertex inside it can be proposed at only one
  position of a duplicate-free edge list.
- Derived the horizon-free KSSS B4 estimate
  `P[Q ⊆ chosen] ≤ |Q|! * D⁻|Q|`; the cumulative hazard of each triangle is
  at most `D⁻¹`, rather than `|edges| D⁻¹`.
- Direct source checking passes for `InternalEdgeRandomGreedy.lean`.

## Current phase

Phase 2 (Lean formalization): the finite constrained-greedy probability
layer now includes exact deletion statistics, a structural classification of
all deletions, weighted two-away threats, a time-dependent stopped availability
envelope, explicit linear pair trajectories, and an aggregate availability
martingale driven by the total two-away incidence rather than its maximum.  The high-girth absorber bank
has been restricted to realizable cycle-cover decompositions, eliminating
spurious in-side roots, and exact initial pair-codegree lower bounds are now
verified.  The exact-bank pair-local threat coefficient is independent of the
ambient padding, and separate pair-local/global cutoffs now propagate through
the scheduled phase while preserving every uncovered outside pair.  All five
failure estimates (pair concentration, pair-local cutoff, global cutoff,
aggregate incidence, and total availability) are now assembled on one timed
law with a verified positive-mass full-phase extraction theorem.  Numerical
trajectory discharge and padded-absorber scalar instantiation are also
verified.  A finite vortex layer now partitions all triples by deepest level
and formalizes KSSS conditions (W1)--(W4).  Exact profile factorization and
cancellation prove the ambient-size-free W1 nonempty-root coefficient
`(r+1)^ell z` and W4 singleton coefficient `(r+1)^ell y`.  Exact
absorber-induced W1--W4 bounds, indexed aggregation, a level-restricted
stopped greedy kernel, point-weighted factorial joint inclusion, and the
density-sensitive W4/rooted-threat estimates are now verified.  The reserve
graph layer now has an exact independent active-set law and a finite Chernoff
bound, specialized to the two-edge wedges used to cover every internal
leftover edge.  The adaptive master iteration, eventual parameter selection,
and terminal vortex cover-down remain in progress.

## 2026-08-18 — reserve-wedge Chernoff bound complete

- Added `IndependentBlockSampling.lean` and
  `IndependentBlockConcentration.lean`: pairwise-disjoint coordinate blocks
  have the exact joint active/inactive law and exact active-set distribution;
  summing it over the powerset gives the finite bound
  `P[X ≤ k] ≤ 2^k(1-q/2)^m`, hence `P[X ≤ k] ≤ exp(-qm/4)` whenever
  `k ≤ qm/4`.
- Added `ReserveBlockSampling.lean` and `ReserveWedgeSampling.lean`: crossing
  reserve blocks specialize the abstract law, distinct candidate vertices for
  one fixed outer edge use disjoint two-edge wedges, and their lower-tail
  failure is at most `exp(-r²|S|/4)`.
- Added `IterationReserveCandidates.lean`: the one-edge instance of iteration
  typicality supplies the deterministic candidate window and the two required
  adjacencies, so the exponential reserve-wedge estimate applies directly to
  a KSSS internal leftover edge.
- Direct source checks and ordinary Lake builds pass through
  `IterationReserveCandidates.lean` (1711 jobs in the latest module build).

## 2026-08-18 — vortex profile weights started

- Added `Vortex.lean`: nested finite vortex sets, deepest triangle levels,
  the disjoint level partition, and the exact sum of level counts.
- Added `VortexWellSpread.lean`: exact finite W1--W4 predicates, bounded
  profile boxes, endpoint/middle root exponents, and monotonicity.
- Added `VortexWeight.lean`: exact level-wise product-weight factorization,
  profile decomposition of extension sums, cancellation of profile scales,
  and the uniform W1/W4 extension coefficients.
- Direct checks pass for all three new modules; ordinary builds pass through
  `VortexWellSpread.lean`.

## 2026-08-18 — scalar padded averaged phase complete

- Added `AverageOutsidePairSurvival.lean`: the common averaged law preserves
  every eligible outside pair that remains in the leave.
- Strengthened `AverageAbsorberPhase.lean` so its extracted state retains that
  support invariant on the same five-event outcome.
- Added `LinearAverageAbsorberPhase.lean`: all pair drift, jump, target-window,
  and variance hypotheses are discharged by the explicit linear rates.
- Added `AverageAbsorberCoefficientBounds.lean`: the total-incidence first
  moment and the complete five-term failure expression are bounded solely in
  terms of ambient order, absorber support size, and bank size.
- Added `PaddedAveragePhaseConstruction.lean`: an explicit pair theta,
  availability theta, and both scalar variance budgets now produce the
  realizable padded absorber and a genuine exact-length averaged phase from
  scalar inequalities only.
- Added `OutsideAliveExtraction.lean`: an exhausted absorber-greedy state
  retaining outside-pair survival is immediately a KSSS outside packing.
- Direct checks and ordinary builds pass through
  `PaddedAveragePhaseConstruction.lean` (1790 jobs in the latest build).

## 2026-08-18 — averaged availability phase complete

- Added `GreedyDeletionIncidence.lean`: summing the exact deletion
  classification over all available selectors bounds the conditional mean
  availability loss by `3Δ` plus the normalized total available two-away
  incidence.
- Added `TimedStoppedTotalTwoAway.lean`: the total incidence has an explicit
  first-moment envelope from A2 and a single Markov tail, avoiding a maximum
  cutoff in the availability drift.
- Added `AverageAvailabilityConcentration.lean`: the centered total
  availability deficit has verified nonpositive drift, conditional variance,
  and an exponential stopped-process tail.
- Added `TimedAveragePairBand.lean`, `TimedAveragePairBandSuccess.lean`, and
  `AverageAbsorberPhase.lean`.  Pair-star concentration and aggregate
  availability concentration now share one stopped law; the concrete theorem
  instantiates all five probability bounds and returns a state with the exact
  insertion count and every cutoff/floor invariant.
- Direct source checks and ordinary Lake builds pass through
  `AverageAbsorberPhase.lean` (1775 jobs in the latest module build).

## 2026-08-18 — exact pair-local bound and two-cutoff phase complete

- Added `PairFamilyTwoAwayWeight.lean`, `PairExactBankWeightedBound.lean`,
  and `PairTwoAwayAbsorberBound.lean`.  Active pair-local witnesses inject
  into the exact absorber bank, and their extension weight is bounded by an
  explicit coefficient depending only on `q` and the bank, never on the
  number of padded ambient vertices.
- Added the resulting local cutoff failure estimate to
  `TimedStoppedPairTwoAway.lean` and integrated it with the pair-band and
  global A2 failures in `LinearAvailabilitySchedule.lean`.
- Generalized the positive-mass phase extraction to preserve an arbitrary
  supported state predicate.  `OutsidePairSurvival.lean` now carries the
  conjunction of the absorber invariant and all surviving outside leave pairs
  through the same two-cutoff timed law.
- Added the scalar absorber-bound interface
  `exists_linearScheduledAbsorberGreedy_phaseTwoCutoffs_of_absorberBounds` in
  `PaddedPairPhase.lean`.
- Direct source checks and ordinary Lake builds pass through the refactored
  timed phase, scheduled phase, outside-survival layer, and padded scalar
  interface.

## 2026-08-18 — sharp alive-pair concentration integrated

- Added `AlivePairVariance.lean`: non-pair selectors preserve a pair above
  the strict `3+K` floor; pair-cover selectors account for at most `d²` of
  the three-pair deletion incidence; and the survival-masked second moment is
  at most `d(3+K)(3Δ+K)/|A|`.
- Added `SharpPairConcentration.lean`: matching survival-weighted exponential
  bounds for both upper and lower pair-star deviations.
- Propagated the sharp drift `d(3δ-2-Δ)/|A|` and the linear variance budget
  through the simultaneous union bound, timed pair-band bootstrap, linear
  trajectories, and clipped availability schedule.
- Direct source checks and ordinary Lake builds pass for every changed layer
  through `LinearAvailabilitySchedule.lean`.

## Verified facts

- `tex/207.tex` contains the reconstructed KSSS proof and Leanization map.
- The deterministic high-girth absorber, its polynomial size bound, padding,
  localization, and final certificate-to-Steiner reduction type-check.
- The absorber-induced rooted-threat family has a linear ambient extension
  bound after exact-bank endpoint regrouping and a separate order-four count.
- A general finite single-insertion kernel has factorial joint-inclusion
  bounds without an independence assumption.
- The threshold-stopped constrained-greedy law inherits those bounds at
  cumulative point scale `fuel / D`.
- Vertex-star and rooted-threat moments hold simultaneously on one
  positive-mass stopped trajectory retaining the full greedy invariant.
- Exact initial outside-candidate accounting and packing degree identities
  turn those bounds into common-leave candidate surplus under an explicit
  finite loss budget.
- Every deletion is either caused by a shared pair or by a forbidden
  configuration having exactly two unselected triangles; consequently a
  two-away cutoff `K` gives the deterministic one-step bound `3|V| + K`.
- Two-away configurations are encoded as rooted weighted witnesses, including
  a fixed-family comparison with the original absorber extension budget.
- Time-inhomogeneous monotone single-insertion kernels have factorial joint
  inclusion bounds at cumulative hazard `∑ i < t, δ i`.
- The envelope-stopped greedy kernel has point hazard `(D i)⁻¹` and preserves
  the scheduled availability floor whenever
  `D(i+1) + (3|V|+K) ≤ D(i)`.
- A2 now gives a concrete two-away extension bound: the order-at-least-five
  part is injected into fixed-size absorber families, while order four has at
  most `3|V|` witnesses.
- The envelope-stopped moment and union-bound argument returns a positive-mass
  state with the cutoff intact; its support certificate proves that the state
  made exactly the scheduled number of insertions.
- The crude `3|V|` collision loss has been refined to `3Δ`, where `Δ` is the
  maximum current available pair-codegree.
- Every available pair-codegree injects into a leave-graph neighborhood, so a
  maximum leave-degree estimate supplies the required pair cutoff.
- Packing degree-sum identities give the exact deterministic envelope
  `|V|-1-(6|P|-(|V|-1)^2)` for every leave degree.
- The pair-envelope stopped kernel has inhomogeneous joint-inclusion bounds
  and a support/progress invariant.  With the deterministic packing schedule,
  pair-cutoff failure is eliminated as a first stopping reason.
- The A2 moment, Markov, and union-bound argument has been transferred to the
  pair-envelope process.  Its extraction theorem returns a genuine full-length
  packing with the absorber invariant, availability floor, and two-away cutoff.
- A selected vertex star has an exact Bernoulli one-step increment whose
  conditional first and second moments are its available-star density.
- The timed stopped-kernel exponential inequality now needs jump bounds only
  on positive-mass successors.  It gives a verified lower-tail theorem for
  each selected vertex-star trajectory under an active-region density bound.
- For a fixed pair-extension family of size `d`, selecting inside the family
  deletes the entire family.  Double counting gives at least `d²` ordered
  deletion incidences and the corresponding negative conditional drift.
- The full three-pair overlap correction gives the sharper lower deletion
  incidence `d(3δ-2)` under a nonzero pair floor `δ`; transposed deletion
  selectors give the matching upper incidence `d(3Δ+K)`.
- Monotone availability transfers both drift inequalities and the conditional
  second-moment estimate to one fixed initial pair-star observable.
- Fixed-pair upper and lower stopped exponential concentration now use the
  actual drift and variance estimates, with jump bounds checked only on
  positive-mass successors.  The lower tail is survival-weighted, so the
  catastrophic transition covering the tracked pair contributes no alive
  terminal failure.
- A finite union bound over `PairOn V` gives simultaneous concentration for
  every still-uncovered vertex pair, with separate upper and lower
  deterministic envelopes so that the two-sided hypotheses are nonvacuous.
- Pair-star lower and upper failures are now restricted to alive pairs.  A
  killed-kernel comparison proves that imposing the pair-specific stop does
  not change the probability of any alive terminal event.
- Strict alive-pair deviation bounds imply the full pair cutoff and floor:
  dead pair-stars are empty, while alive pair-stars satisfy the real-valued
  envelopes.  Together with a positive global availability schedule this
  rules out premature pair-band stopping.
- The common timed law combines the alive-pair bootstrap and the A2 two-away
  moment bound.  Its positive-probability extraction preserves an arbitrary
  kernel invariant, reaches the scheduled horizon, retains the cutoff and
  availability floor, and records the exact number of insertions.
- On an alive-to-alive transition, pair-sharing deletions from a fixed pair
  star inject into the three vertices of the selected triangle.  Thus the
  lower-deviation jump is the sharper `3+K`, not `3Δ+K`; this proved bound is
  now built directly into every simultaneous and timed pair bootstrap.
- Explicit linear pair targets now start at each exact initial codegree.  The
  upper rate is the floor-forced deletion rate divided by initial
  availability; the lower rate is the cutoff deletion rate divided by a
  deterministic availability floor.  Their drift, jump, target-window, and
  conditional-variance obligations reduce to scalar phase inequalities.
- The padded absorber now carries explicit maximum-degree and bank-cardinality
  bounds; every bank triangle is supported either on an absorber edge or wholly
  inside the flexible set.
- The cycle-cover bank has been replaced by the realizable subbank consisting
  of all sphere out-sides and only those in-sides arising from flexible-set
  cycle covers.  It retains A1, A2, localization, and the full absorption
  theorem while excluding impossible singleton roots.
- For the corrected bank, every initially illegal third vertex for a pair
  outside the absorber and flexible-set pairs lies in an absorber-neighbor or
  bank-support exceptional set.  Consequently its initial available star has
  the exact lower bound `|V| - 2 - 3C` under a common structural bound `C`.
- Every flexible-set pair has empty initial available star: A1 supplies a bank
  triangle on that pair, which forms an order-four forbidden singleton with
  any outside triangle.  Thus every initially alive pair is outside both the
  absorber graph and the flexible-set pair graph and receives the verified
  lower bound above.
- The numerics exposed that the old single two-away threshold served two
  incompatible roles.  The formal development now separates a global
  `Kglobal` (total deletion and availability-schedule loss) from a pair-local
  `Kpair` (surviving pair-star jumps).  The variance envelope is exactly
  `(3+Kpair)(3Δ+Kglobal)` and the survival condition uses only `Kpair`.
- Pair-local two-away targets now exclude triangles already sharing a pair
  with the selector; those are charged to the proved three-target collision
  term.  The local cutoff is required only when the selector does not cover
  the tracked pair, exactly matching alive-to-alive transitions.
- Separate-cutoff versions now type-check through `AlivePairJump`,
  `AlivePairVariance`, `SharpPairConcentration`, the simultaneous pair union,
  pair-band bootstrap, timed availability bootstrap, linear trajectories, and
  the three-error positive-probability extraction.
- The pair-local threat has an exact finite witness family and selected-count
  identity.  Its generic moment theorem, timed joint-inclusion specialization,
  Markov tail, and union bound over selectors and vertex pairs all type-check.
- Summing the exact deletion inclusion over every available selector gives an
  aggregate drift estimate whose exceptional term is the total two-away
  incidence, so the global maximum cutoff no longer controls expected total
  availability loss.
- A2 supplies a first-moment envelope and one-event Markov tail for that total
  incidence.  The resulting centered availability deficit satisfies a stopped
  exponential concentration inequality on the same law used for all alive
  pair-star trajectories.
- A five-event union bound and support extraction now returns a genuine
  full-length absorber-greedy state with pair cutoff/floor, both two-away
  cutoffs, aggregate-incidence cutoff, total-availability floor, and exact
  chosen cardinality.
- The abstract trajectory hypotheses of the five-event phase reduce to the
  existing explicit linear upper/lower rates with a constant availability
  floor; the padded absorber wrapper exposes only scalar inequalities.
- The corrected pair-star lower drift is now transposed to an additive
  aggregate incidence statistic.  Exact-bank quadratic extension weights,
  stopped moments, a fixed-pair lower concentration theorem, and the
  simultaneous upper/lower pair union bound all type-check.
- A common six-event stopped law now includes the aggregate pair-star
  incidence cutoff.  Its support, availability martingale, pair martingales,
  outside-pair survival, positive-probability extraction, absorber
  specialization, explicit linear rate/variance budgets, scalar coefficient
  bound, and padded construction boundary all type-check.
- If a later terminal/vortex process reaches exhaustion while retaining the
  outside-pair survival invariant, the graph-support conclusion and hence the
  exact outside packing follow without any further counting estimate.
- Exact W1 and W4 vortex estimates now retain every phase-density factor
  instead of replacing it by one.  Their indexed absorber specializations
  and the rooted-threat coding give density-sensitive extension bounds for
  every planted root.
- The fixed-level stopped vortex kernel reaches its requested threshold in a
  quadratic packing horizon while preserving arbitrary invariants and global
  availability monotonicity.
- Iterating that kernel over all vortex levels yields a finite supported sweep:
  every listed level reaches its threshold, the invariant survives, and the
  final residual availability is bounded by the sum of the level thresholds.
- Ordinary project builds pass for the sharp forbidden-family bounds,
  density-sensitive rooted threats, and the complete vortex sweep
  (`1760/1760` jobs).  The next layer is the W2 equal-remainder collision
  estimate needed for probabilistic preservation during the sweep.
- W2 now has a level-weighted equal-remainder collision sum retaining the
  full `c^(r-3)` density saving.  On profiles with a terminal remainder, the
  direct absorber-induced W2 coefficient loses its terminal-size factor
  exactly, leaving an ambient-size-free coefficient.
- The factorial joint-inclusion theorem has been generalized to genuinely
  time-inhomogeneous point hazards.  The output is the product of each
  triangle's cumulative hazard, rather than a worst-case scalar hazard.
- A scheduled multi-level vortex kernel instantiates this theorem.  Its
  cyclic schedule visits every level once per cycle and has exact cumulative
  hazard `cycles / D(level(T))` for each triangle `T`.
- The same cyclic law now has a support theorem: after the quadratic packing
  number of cycles it preserves the exact absorber invariant, places every
  level below its threshold, and hence bounds total residual availability by
  the sum of the thresholds.  Thus structural saturation and weighted joint
  inclusion are finally available for one common finite law.

## Most recent checks

- Source checks passed through `GreedyDeletionStatistics.lean`,
  `GreedyDeletionObstruction.lean`, `TwoAwayThreatWeight.lean`,
  `FamilyTwoAwayWeight.lean`, `GreedyDeletionBound.lean`,
  `InhomogeneousJointInclusion.lean`, `EnvelopeStoppedGreedy.lean`,
  `TwoAwayAbsorberBound.lean`, `EnvelopeStoppedTwoAway.lean`,
  `AvailablePairDegree.lean`, `AvailablePairDegreeTrajectory.lean`,
  `PairEnvelopeStoppedGreedy.lean`, and
  `PairEnvelopeStoppedTwoAway.lean`.
- Module builds passed for `EnvelopeStoppedTwoAway.lean`,
  `AvailablePairDegree.lean`, `AvailablePairDegreeTrajectory.lean`, and the
  initial version of `PairEnvelopeStoppedGreedy.lean`.
- One ordinary Lake invocation built `PairEnvelopeStoppedTwoAway`,
  `StoppedGreedyVertexStarConcentration`, and `PairExtensionDeletionDrift`
  successfully, including all changed transitive dependencies (1753 jobs).
- Ordinary Lake builds passed for `PairExtensionTrajectory`,
  `StoppedPairExtensionConcentration`, and
  `SimultaneousPairExtensionConcentration` (latest build: 1736 jobs).
- An ordinary Lake build passed for `TimedPairBandPhase` and all changed
  transitive dependencies, including `PairAliveStoppedProcess`,
  `SimultaneousPairExtensionConcentration`, `PairExtensionBootstrap`, and
  `TimedPairBandBootstrap` (1758 jobs).
- Direct Lean source checks passed for the survival-weighted finite-kernel
  concentration layer and for `AlivePairJump`.  Direct compiled checks then
  passed successively through `SimultaneousPairExtensionConcentration`,
  `PairExtensionBootstrap`, `TimedPairBandBootstrap`, and
  `TimedPairBandPhase` with the hard-wired `3+K` lower jump.
- An ordinary Lake build passed for `LinearPairTrajectories` and every changed
  transitive dependency (1760 jobs).
- Direct Lean source checks passed for `AbsorberPadding`,
  `RestrictedAbsorberBank`, and `InitialPairAvailability`.
- An ordinary Lake build passed for `RestrictedAbsorberBank` and all changed
  transitive dependencies (1399 jobs).
- Ordinary builds passed for the new `PairTwoAwayCutoff`, `AlivePairJump`,
  `AlivePairVariance`, `SharpPairConcentration`,
  `SimultaneousPairExtensionConcentration`, `PairExtensionBootstrap`,
  `TimedPairBandBootstrap`, `TimedPairBandTwoCutoffs`, and
  `PairTwoAwayThreatWeight` dependency stacks.
- Direct source checks passed for `TimedPairBandTwoCutoffs`, the two-cutoff
  additions in `LinearPairTrajectories` and `TimedPairBandPhase`, and
  `TimedStoppedPairTwoAway`.
- Direct source checks and ordinary builds passed for
  `GreedyDeletionIncidence`, `TimedStoppedTotalTwoAway`,
  `AverageAvailabilityConcentration`, `TimedAveragePairBand`,
  `TimedAveragePairBandSuccess`, and `AverageAbsorberPhase`.
- Direct checks passed for `AverageOutsidePairSurvival`,
  `LinearAverageAbsorberPhase`, `AverageAbsorberCoefficientBounds`, and
  `OutsideAliveExtraction`; ordinary builds passed through
  `PaddedAveragePhaseConstruction`.
- Direct source checks and ordinary builds passed for
  `PairAggregateDeletionDrift`, `PairAggregateTwoAwayWeight`,
  `PairAggregateTwoAwayAbsorberBound`, `PairAggregateTwoAwayThreatWeight`,
  `TimedStoppedPairAggregateTwoAway`, `SharpPairAggregateConcentration`, and
  `SimultaneousPairAggregateConcentration`.
- Direct source checks passed for `TimedAggregateAveragePairBand`,
  `TimedAggregateAveragePairBandSuccess`, `AggregateAverageAbsorberPhase`,
  `LinearAggregateAverageAbsorberPhase`,
  `AggregateAverageAbsorberCoefficientBounds`, and
  `PaddedAggregateAveragePhaseConstruction`; ordinary builds passed through
  `AggregateAverageAbsorberCoefficientBounds` and its dependencies.

## Resolved failures

- The stopped-law extraction now retains positive mass, so support invariants
  are available on the chosen outcome.
- Vertex-star losses are converted to covered degrees by an exact packing
  identity, not an asymptotic estimate.
- The complement-graph component of `graphDifference` is explicitly reduced
  to nonadjacency before applying the initial candidate count.

## Next step

Select an explicit eventual parameter hierarchy for the corrected scalar
six-event phase, iterate it through the vortex, and construct the terminal
process which reaches exhaustion while retaining outside-pair survival. Feed
the resulting outside packing into
`ksssCoverDownCertificate_of_outsidePacking`, and export the main theorem.

## 2026-08-18 — exact vortex profile counting

- `VortexVertex.lean` now gives the exact partition of vertices by deepest
  vortex level and bounds realizations of a fixed vertex profile by the
  corresponding product of vortex-set powers.
- `VortexMonomial.lean` proves the finite majorization inequality used in
  KSSS Lemma 7.2 and its terminal-padding/profile-scale corollary.
- `VortexPrefix.lean` identifies prefix sums with early-level vertices and
  triangles; `ErdosTouching.lean` supplies both dual forms of KSSS Lemma 3.2.
- `VortexExactBank.lean` proves the sharp extra-vertex exponent and every
  cumulative profile inequality for an exact bank class.
- `VortexExactBankCount.lean` encodes a profiled extension by its vertex
  profile, extra vertex set, and bounded triple system, yielding the precise
  terminal-power/profile-scale count.
- `VortexInducedCount.lean` sums those estimates over all minimal orders and
  exact bank parts. `VortexInducedWellSpread.lean` establishes all W1--W4
  conditions for each indexed absorber-induced family, with an explicit
  finite coefficient.
- Direct source checks passed for every new module above; ordinary Lake
  builds passed through `VortexInducedWellSpread` and all of its dependencies
  (`1422/1422` jobs on 2026-08-18).

The remaining proof obligation is the master cover-down iteration and its
eventual parameter instantiation; no exported theorem is present yet.

## 2026-08-18 — indexed vortex weights and level process

- `VortexIndexedWeight.lean` and `VortexForbiddenWeight.lean` aggregate the
  exact absorber-induced W1/W4 estimates over every high-order indexed
  forbidden family.
- `WeightedKernelJointInclusion.lean` proves factorial joint inclusion for a
  monotone single-insertion kernel with a point-dependent hazard.
- `VortexLevelGreedy.lean` defines the threshold-stopped level process and
  bounds its joint inclusion probabilities by the KSSS vortex triangle
  weight.  Ordinary builds pass through this module and the indexed aggregate
  (`1429/1429` jobs).
- `VortexSharpWeight.lean` and `VortexIndexedSharpWeight.lean` retain the
  exact phase-density factor `c^(r-3)` in W4 instead of discarding it via
  `c <= 1`; their ordinary project builds pass.
- `VortexRootedThreatWeight.lean` combines the sharp W4 estimate with the
  injective rooted-threat code.  Its direct source check passes and gives the
  expected linear third-vertex factor times the density-sensitive indexed
  coefficient.

## Completion status

The exported theorem `erdos_207` is not yet present.  The final main-file
source/build check, forbidden-placeholder scan, and `#print axioms` audit are
still pending.

## 2026-08-18 — common-law terminal moment closure

- `VertexStarWeight.lean` now contains the arbitrary point-weight version of
  the singleton-star extension bound.
- `VortexVertexStarMoment.lean` gives a cyclic-law moment, Markov tail, and
  all-vertices extraction for selected vertex stars.
- `VortexPairWeight.lean` proves that a fixed pair-star has vortex weight at
  most one density factor per vortex level, and that all triples sharing a
  pair with a fixed triangle have total weight at most
  `3 * (ell + 1) * c`.
- `VortexRootedThreatFourWeight.lean` upgrades the order-four rooted-threat
  code to arbitrary point weights and obtains its ambient-linear vortex
  extension bound.
- `VortexFullTerminalMoment.lean` recombines indexed and order-four rooted
  witnesses, controls the actual rooted active forbidden-configuration
  count, and extracts one cyclic outcome with the structural saturation
  certificate, every vertex-star cutoff, and every ordered-pair rooted
  cutoff simultaneously.
- Direct source checks passed for all five modules.  Ordinary builds passed
  through `VortexRootedThreatFourWeight`, `VortexRootedThreatMoment`, and
  `VortexVertexStarMoment` and all changed transitive dependencies
  (`1769/1769` jobs).

The next unresolved bridge is dynamic: the terminal continuation can add
triangles after the cyclic stopped state, so its star/root controls must be
transported through that continuation, or the master vortex iteration must
produce an exhausted state while preserving `OutsideLeavePairsAlive`.

## 2026-08-18 — deterministic continuation and terminal certificate

- `GreedyContinuation.lean` now proves that a continuation of fuel `t` adds
  at most `t` new selected triangles, and consequently raises every selected
  vertex-star count by at most `t`.
- `TerminalControlCertificate.lean` packages the exact deterministic end of
  the count method: exhaustion together with the uniform star/root cutoffs
  and the fixed loss budget rules out every `KSSSCountFailureAt`, hence gives
  `HasKSSSOutsidePacking`.
- Direct Lean source checks passed for both changed modules.

The remaining master-iteration obligation is now isolated sharply.  The
star cutoff transports through a short terminal continuation by the proved
fuel bound, but the rooted active-threat cutoff is not monotone with a small
additive increment.  It must be re-estimated under the continuation law, or
outside-pair survival must be retained all the way to an exhausted state.

## 2026-08-18 — exact master-iteration data

- `IterationTypical.lean` formalizes KSSS Definition 10.1, including both
  consecutive-level degree windows and every bounded rooted graph-pattern
  extension count.
- `StrongWellDistributed.lean` formalizes Definition 10.2 as a finite-law
  joint bound for initial triangles, later triangles, and pairs uncovered by
  the initial family.
- `MasterIterationData.lean` formalizes the pointwise and law-level clauses
  of Definition 10.4 and the exact graph/availability update of Definition
  10.5.  Its direct Lean source check now passes.
- `tex/207.tex` now records the complete three-part proof of Proposition
  10.6: properties A1--A4, B1--B4, C1--C4, the joint bound incorporating the
  reserve graph, and the final strong-distribution/typicality verification.

The next missing result is the finite master step itself.  Its first
subproblem is the reserve-edge/triangle regularization step producing A1--A4
from the newly formalized iteration-good input.

## 2026-08-18 — conditioning, reserve sampling, and update verification

- `StructuredInitialData.lean` now gives the rounded power-law vortex
  recurrence and the exact well-spread hypotheses on every truncated vortex
  from KSSS Definition 10.3.
- `FiniteConditioning.lean` constructs conditioning of a finite law, proves
  the intersection-over-normalizer identity, and proves that strong
  well-distributedness survives with the exact reciprocal loss in its
  multiplicative constant.
- `MasterIterationConditioning.lean` formalizes the reduction after
  Proposition 10.6 which conditions on IG2--IG4.
- `ReserveEdgeSampling.lean` constructs the independent crossing-edge
  reserve, proves exact joint inclusion/exclusion probabilities, finite
  binomial upper- and lower-tail union bounds, and that every reserve outcome
  is a subgraph of the input graph.
- `MasterIterationUpdate.lean` proves that the A/B/C structural output,
  together with new parity, strong distribution, and typicality, implies the
  updated iteration-good state.  It also proves the old graph is covered by
  the selected triangles plus the precise updated remainder.

All of these modules pass direct Lean checks.  The probabilistic missing
piece is now limited to constructing A1--A4, B1--B4, and C1--C4 with the
numeric bounds required by the support-level update theorem.

## 2026-08-21 — common-law preliminary mixed estimate

- `PreliminarySurvivalScalar.lean` proves the exact truncated natural-number
  Bernoulli inequality needed to turn a `3k` local edge supply into the
  survival factor `((M-k)/M)^|E|`.
- `SupportRestrictedSelectedUncovered.lean` proves the inhomogeneous mixed
  selection/survival recurrence using transition hypotheses only on the
  positive-mass support.  This removes the spurious obligation at unreachable
  terminal clock states.
- `TimedActiveGreedyJointLaw.lean` applies that recurrence to an arbitrary
  clocked active greedy process carrying an auxiliary invariant.
- `PreliminaryOutsideSupply.lean` shows that outside-pair survival and the
  pair floor supply every uncovered crossing edge of a graph disjoint from
  the absorber graph.
- `AggregatePreliminaryGreedyJointLaw.lean` combines these facts for the same
  aggregate pair-band law used by all availability and pair concentration
  estimates.  It proves the exact `(8.7)` product bound plus the probability
  of terminal inactivity.
- Direct Lean checks pass for all five modules.  Ordinary Lake builds pass
  through `SupportRestrictedSelectedUncovered`, `TimedActiveGreedyJointLaw`,
  `PreliminaryOutsideSupply`, and
  `SupplyStoppedPreliminaryGreedyJointLaw` and their transitive dependencies.

The next obligation is to insert this concrete preliminary bound into
`jointBind_preliminaryAugmentedReserve`, discharge its scalar partition
inequality, and connect the resulting reserve-aware state to the master
iteration.

## 2026-08-21 — preliminary augmented-reserve numeric update

- `PreliminaryAugmentedReserveNumeric.lean` proves that every old
  per-triangle master weight is at most one on a nonempty vortex and combines
  old and newly surviving reserve-edge powers exactly.
- The two-powerset partition is now absorbed numerically: new preliminary
  triangles cost `alpha`, new residual crossing edges cost `eta`, and the
  uniform exceptional probability is charged to the next additive error via
  the explicit inequality `b + 2 * epsilon ≤ b'`.
- The exported theorem
  `jointBind_preliminaryAugmentedReserve_of_numeric` turns the concrete mixed
  preliminary law directly into a reserve-aware strongly distributed law at
  the next index.  Its direct Lean check passes.

The next obligation is state composition: bind this preliminary kernel to
the conditioned reserve/internal-edge kernel, construct the canonical
residual-link family on its support, and apply the simultaneous link update
inside one vortex-step induction.

## 2026-08-21 — composed preliminary/internal/link master kernel

- `PreliminaryInternalComposition.lean` composes the exact preliminary
  product-plus-exception law with the sharp internal-edge kernel while
  preserving the augmented crossing reserve.
- `PreliminaryInternalResidualLinks.lean` converts supported internal-cover
  outcomes into the canonical simultaneous residual links, including every
  center, side, and reserve-spoke certificate.
- `SupportedLinkCoverKernel.lean` totalizes the robust simultaneous-cover law
  by the empty law away from the old law's support.  It proves global C4 and
  structural support, joint cover support on occurring states, and now
  derives its readiness proposition directly from
  `exists_simultaneousRobustLinkCoverFamilyLaw` with the exact conditioning
  normalizer.
- `SupportedReserveAwareMasterIteration.lean` proves the support-sensitive
  probability, cap, and strong-rooted-cap master updates.  Cover validity is
  required only on the support of the joint law; reserve accounting and C4
  remain valid on every fiber.  Its direct source check and ordinary Lake
  build both pass (`2047/2047` jobs).
- `MasterCoverDownExtraction.lean` proves the deterministic terminal bridge:
  the final master cover step plus the accumulated coverage invariant is
  already a `HasKSSSOutsidePacking` certificate.  Its direct source check
  passes.

The remaining obligation is to instantiate these one-step interfaces from
the finite parameter hierarchy, start the master law, iterate over the
vortex, and invoke the terminal extraction theorem.

## 2026-08-21 — bounded flexible-root incidence in the explicit absorber

- `AbsorberRootTriples.lean` proves that the three roots of every attached
  sphere are absent from the universal sphere bank, including after mapping.
- `AbsorberRootAvailability.lean` localizes every singleton forbidden
  completion involving a mapped sphere root to the three roots of a sphere
  fiber, and packages the corresponding pair candidate set of size at most
  six.
- `AbsorberCoreRootCandidates.lean` exposes the constant-size root incidence
  hidden inside the universal cycle-cover bank.  A private `C4 ∪ C5` copy
  can see only its nine quotient images and a private `3C4` copy only its
  twelve quotient images.  Adding the path-cover part gives at most fourteen
  original roots adjacent to any core vertex.
- The same file lifts this statement through the sphere transform: every
  vertex of `highGirthCycleCoverGraph` is adjacent to at most fourteen of the
  distinguished original roots (and every sphere-interior vertex has at most
  three candidates).  Direct Lean checks pass for all three modules.

The next obligation is to combine these endpoint and forbidden-completion
candidate sets into the lower extension-count clause of initial iteration
typicality.  The global-layer upper bounds will use the already proved
absorber-support estimates; the small-layer lower bounds now lose only a
fixed number of roots per bounded pattern.

## 2026-08-21 — complete initial two-level typicality

- `InitialRootTypicality.lean` now bounds every unavailable root for one
  tested pair by an explicit set of size at most `36`, and every unavailable
  ambient vertex by absorber-edge and bank-support losses.
- Unioning over a graph pattern of support at most `h` gives the exact finite
  losses `h + 36 h^2` on the flexible root set and `h + 3 C h^2` on the
  ambient set.
- The same file proves the ambient degree loss is at most `C + 1` and the
  root degree loss is at most `15`.
- `oneStageVortex X` is the exact vortex `univ ⊇ X`, and
  `initial_oneStage_isIterationTypical` packages all degree and extension
  clauses at density `p = eta = 1` from four explicit scalar inequalities.
- A direct Lean source check of `InitialRootTypicality.lean` passes.

The next obligation is the finite parameter hierarchy: instantiate the
shortest existing preliminary/internal/terminal route (or the compressed
one-step master route) at the two-level vortex, obtain
`HasKSSSOutsidePacking`, and then invoke the already proved absorber assembly.

## 2026-08-21 — outer-residual preliminary product law

- `PreliminaryOuterResidual.lean` strengthens the preliminary mixed law from
  crossing edges to every stage edge not wholly contained in the next vortex
  set.  The outside-pair survival invariant supplies these edges without any
  new probabilistic hypothesis.
- The same file proves the active-event and conditioned pure product forms,
  together with finite witness-union tails for residual outer incidence.
- A direct Lean source check of `PreliminaryOuterResidual.lean` passes.

The next obligation is to use the conditioned outer product law for the
simultaneous residual-spoke and rooted-threat caps which imply internal-kernel
readiness.

## 2026-08-21 — retrospective success for arbitrary residual schedules

- `InternalEdgeResidualSchedule.lean` runs the internal greedy law on an
  arbitrary residual family of scheduled outer edges, preserves exact
  scheduled-edge provenance, and retains the sharp `D⁻¹` joint-inclusion
  estimate.
- `InternalEdgeTerminalRootSuccess.lean` records the first low-candidate
  failure as an exact certificate and proves that the process preserves this
  certificate, ambient containment, and its ordinary packing/avoidance
  invariant even after it freezes.
- A terminal uniform rooted cap, together with bounded scheduled incidence
  and reserve surplus, contradicts every such certificate.  Thus terminal
  rooted-cap extraction retrospectively implies `failed = false` and coverage
  of every scheduled residual edge; no rooted-cap assumption on hypothetical
  intermediate prefixes is needed.
- Direct source checks pass for both modules.  An ordinary Lake build of
  `ErdosProblems.Erdos207.InternalEdgeTerminalRootSuccess` passes (`1740/1740`
  jobs).

The next obligation is to condition the preliminary outer-product law on the
bounded residual-incidence event, bind the raw state-dependent internal law,
and use strong rooted-threat concentration to extract a successful terminal
outcome.
## 2026-08-21 — complete reserve-protected preliminary/internal stage

- `ReserveProtectedPairAlive.lean` and `ReserveProtectedStageGood.lean`
  construct the common reserve event: every internal outer edge has the
  required active two-spoke supply and every protected preliminary pair is
  live.  The uniform failure probability is the sum of the two explicit
  exponential bounds.
- `ReserveProtectedPreliminaryKernel.lean` totalizes the twice-conditioned
  preliminary law and records its trajectory, protected-availability,
  selected/residual product, and residual-incidence conclusions.
- `ReserveProtectedPreliminaryInternalStage.lean` packages the entire
  reserve-protected preliminary law followed by the fixed-reserve raw
  internal kernel.  Its direct source check and ordinary Lake build pass
  under the default computational limits (`2003/2003` jobs).

The next bridge is rooted-success conditioning of this raw internal law,
followed by `rawPreliminaryInternalResidualLinks` and the supported terminal
typical-link pipeline.

## 2026-08-21 — rooted residual law and terminal extraction wrapper

- `ReserveProtectedRootedConditioning.lean` conditions the composed
  preliminary/internal law on simultaneous rooted success while retaining
  the reserve-distribution and structural invariants.
- `ReserveProtectedRootedResidualLinks.lean` exposes the canonical residual
  bipartite links at every outside center, including center identities, side
  containment, reserve-spoke support, packing, and forbidden-family
  avoidance. Its direct check and ordinary Lake build pass (`2054` jobs).
- `ReserveProtectedRootedTerminal.lean` removes the remaining dependent-law
  bookkeeping: the rooted residual result plus the explicit terminal
  bisection, mixing, moment, deletion, and normalizer inequalities implies
  the exact `HasKSSSOutsidePacking` conclusion. Its direct check and ordinary
  Lake build pass under the default limits (`2098/2098` jobs).

The remaining proof obligation is quantitative rather than structural:
construct the gradual vortex and finite parameter hierarchy, discharge the
stagewise scalar inequalities throughout the compressed master induction,
and feed its terminal law to the outside-packing and absorber assembly
theorems.

## 2026-08-21 — supported typical transition closes the induction interface

- `SupportedCompressedTypicalTransition.lean` proves the full nonterminal
  bridge. It rechooses every residual bipartition from iteration typicality,
  derives supportwise robust simultaneous-link readiness, performs the
  reserve-aware update, and compresses the dependent output law to the fixed
  `MasterStateOn` sample space.
- Both its direct source check and ordinary Lake build pass under default
  limits (`2067/2067` jobs).

The next obligation is to instantiate this theorem uniformly over a gradual
vortex: choose the integer cutoffs and NNReal error budgets, prove the
preliminary/internal hypotheses and robust-link scalar inequalities from the
stage cardinalities, and apply `CompressedMasterInduction`.

## 2026-08-21 — localized residual-link loss

- `InitialVortexTypicality.lean` lifts the initial absorber-complement
  typicality theorem from the diagnostic two-level vortex to every level of
  an arbitrary finite vortex under uniform ambient loss bounds. Its direct
  check and ordinary Lake build pass (`1796/1796` jobs).
- `ResidualLinkTypicality.lean`, `IterationChosenLink.lean`, and
  `SupportedTypicalResidualLinks.lean` now expose localized variants in which
  only covered neighbors lying in the next vortex level are charged against
  the residual-link degree. The previous full-degree interfaces remain as
  proved corollaries.
- `LocalizedInternalStageLoss.lean` proves that outside-only preliminary
  triangles contribute no localized loss and injects every remaining covered
  next-level neighbor into the scheduled internal star. Thus the exact loss is
  bounded by the residual scheduled-incidence cutoff. Its direct check and
  ordinary Lake build pass (`1900/1900` jobs); the totalized supported link
  layer builds through `2030/2030` jobs.

The next obligation is to use this localized support theorem in the terminal
extraction interface, then instantiate the remaining finite probability and
scalar inequalities.

## 2026-08-21 — outer-only localized terminal closure

- `OuterOnlyPreliminaryInternalStage.lean` now retains, on the final raw-law
  support, the preliminary selected-family inclusion, packing, forbidden-
  avoidance, outer-only geometry, and exact scheduled-incidence cap.
- `OuterOnlyRawTerminal.lean` conditions that raw law on rooted success,
  reconstructs the canonical residual links, proves that covered neighbours
  in the terminal vortex inject into scheduled internal triangles, and applies
  the localized typical-link rechoice.
- The resulting theorem reaches the exact `HasKSSSOutsidePacking` conclusion
  through the supported robust-Hall/deletion pipeline.  Its direct Lean check
  and ordinary Lake build pass under the default limits (`2089/2089` jobs).

The remaining obligation is the finite parameter hierarchy: instantiate the
outer-only one-stage theorem at a power-law absorber root set, prove the
averaged preliminary phase succeeds, and discharge the rooted/Hall scalar
tails for all sufficiently large admissible orders.

## 2026-08-21 — correlated preliminary/internal master scale

- `InternalEdgeResidualProduct.lean` identifies the unique outside--outside
  scheduled edge of every internal triangle and proves the fixed-part and
  powerset-union estimates.  An internal triangle now costs the sharp joint
  factor `eta * D⁻¹`, not the quantitatively false standalone `D⁻¹` factor.
- `ReserveProtectedPreliminaryKernel.lean` exports the protected outer-edge
  product law after both conditioning steps; this is the same total kernel
  used by the stage construction.
- `ReserveProtectedCorrelatedComposition.lean` performs the preliminary and
  raw internal samplers inside one augmented-reserve update, with triangle
  scale `alpha + eta * D⁻¹`, and retains the raw internal support certificate.
- Direct Lean checks pass for all three modules.  This removes the previously
  impossible `D⁻¹ ≤ p/|U_i|` hypothesis; the next step is rooted conditioning
  and residual-link construction for the right-associated correlated law,
  followed by the finite gradual-vortex parameter hierarchy.

## 2026-08-21 — sharp retrospective initial-sparsification recurrence

- `InitialSparsificationReserveLaw.lean` introduces the correct initial-stage
  classification: triangles selected by the long sparsification phase are
  initial triangles at ambient scale `|V|⁻¹`, not later-stage triangles.
- `InhomogeneousSelectedUncoveredProduct.lean` and
  `SelectedAvailableUncoveredTransfer.lean` retain the exact time-dependent
  survival product and the essential status of a prescribed triangle before
  it is selected: it must still be available.
- `SharpGreedyCoveringChoiceCount.lean` proves the Bonferroni estimate
  `sum pair-stars ≤ union + choose(|B|,2)`, eliminating the false factor
  three in the earlier coarse covering bound.
- `SharpGreedySurvival.lean`, `GreedyTransferStructure.lean`, and
  `PendingGreedySurvival.lean` connect that count to one uniform greedy step,
  package the three edges of every pending prescribed triangle with the
  residual edge set, and discharge all four structural premises of the
  selected/available/uncovered transfer recurrence.
- `SelectedAvailableEnvelopeProduct.lean` solves the scalar recurrence.  If
  `delta_i ≤ theta_i^(3|Q|+b) rho_i`, the terminal bound is the full residual
  survival product times the product of retrospective point weights
  `sum_i rho_i (prod_{j<i} theta_j)^3`.  This is the formal counterpart of
  the cancellation behind KSSS (7.8)–(7.9).
- Direct Lean checks pass for all of these modules; ordinary Lake builds pass
  for the sharp covering and sharp one-step survival layers.

The next obligation is to instantiate the recurrence on the synchronized
good-state support of the long initial process and prove the discrete
trajectory/harmonic-sum estimates which make the retrospective point weight
`O(|V|⁻¹)` and the residual product `O(p)`.

## 2026-08-21 — synchronized timed transfer verified

- `TimedActiveAvailableTransfer.lean` packages the good-state support as
  `TimedGreedySynchronized`, proves that active transitions advance the
  external and internal clocks together, and derives the sharp one-step
  selected/available/uncovered recurrence with time-dependent availability
  and pair-star floors.
- Its terminal theorem combines this recurrence with the retrospective
  envelope calculation, giving exactly the product of the residual survival
  factor and one prefix-survival-cubed point weight for every prescribed
  selected triangle.
- The direct Lean check passes, and the ordinary default-limit Lake build
  `lake build ErdosProblems.Erdos207.TimedActiveAvailableTransfer` succeeds
  (`1910/1910` jobs).

The next obligation is the law-level conversion to initial strong
well-distributedness: dispose of nonpacking or edge-overlapping prescribed
families, compare terminal tracked-uncoveredness with the strong-distribution
event, charge early stopping to the failure tail, and discharge the discrete
survival and point-weight estimates.

## 2026-08-21 — tracked bounded initial law verified

- Split arbitrary prescribed symmetric pairs into the genuine outside leave
  edges tracked by the long greedy process and the deterministic absorber,
  flexible-square, and diagonal pairs.  The latter are paid by the condition
  `1 ≤ C p`; no live-star assertion is made for them.
- Proved that outside-pair survival and a time-dependent pair floor supply
  every edge of every pending prescribed triangle together with every
  tracked residual edge.
- Combined the sharp Bonferroni estimate with a bounded-pattern cutoff.  A
  prescription of total size at most `K` uses the exact retrospective
  survival and point-transfer products; a larger prescription is dominated
  by the amplified additive error.
- `TrackedInitialSparsification.lean`, `OutsideTrackableSupply.lean`,
  `BoundedSharpSurvivalScalar.lean`, and `BoundedSharpInitialLaw.lean` pass
  direct checks.  Ordinary Lake builds pass through the first three; the
  final module now also passes its direct source check under default limits.

The next obligation is to construct the synchronized active predicate from
the aggregate pair and availability deviation trajectories, bound its
first-passage failure probability, and prove the two discrete schedule
estimates `cumulativeSurvival = O(p)` and
`transferPointWeight = O(|V|⁻¹)`.

## 2026-08-21 — scheduled sharp-law bridge and cubic cancellation

- `TimedScheduledAggregatePairBand.lean` now exports support of the exact
  chosen-cardinality clock and of outside-pair survival for the scheduled
  process.
- `TimedScheduledAggregatePairBandSuccess.lean`,
  `ScheduledAggregateAverageAbsorberPhase.lean`,
  `RealFloorSchedules.lean`, and
  `LinearScheduledAggregateAverageAbsorberPhase.lean` construct the common
  scheduled six-event law and its positive terminal outcomes.
- `BoundedSharpScheduleEstimates.lean` proves the basic survival estimates
  and, crucially, the time-dependent cubic cancellation bound for the
  retrospective point weight.  The latter does not replace all availability
  denominators by their terminal minimum.
- `ScheduledBoundedSharpInitialLawGeneral.lean` connects arbitrary lower,
  upper, and pair-star schedules on the synchronized aggregate process to the
  exact initial product law.  Its direct Lean source check passes.
- `InitialProductReserveOne.lean` shows that the product law may record any
  canonical state-dependent reserve at reserve density one, and hence gives
  the reserve-aware strong law needed by the internal and terminal stages.
  Its direct Lean source check passes.

The remaining initial-phase scalar obligation is now precise: derive the
time-dependent upper availability schedule from the pair upper trajectory
and the deterministic uncovered-pair count, then prove that its lower
availability schedule satisfies the cubic normalized inequality used by the
new transfer lemma.  After that law is conditioned on bounded residual
incidence, it can be fed directly to the already verified raw-internal and
terminal pipelines.

## 2026-08-21 — power-vortex base state and sharp empty rooted endpoint

- `InitialPowerTransitionData.lean` turns the level-zero typicality stored in
  `InitialPowerVortexPackage` into the exact outer-only greedy invariant,
  outside-pair survival, and empty-chosen state needed by the first
  transition.  Its direct Lean check passes.
- The generic localized rooted-threat coefficient was audited and found too
  coarse for the power hierarchy: its unrestricted bank powerset factor can
  grow faster than every root-level cap available in the construction.
- `SeparatedLocalizedRootedThreat.lean` isolates the endpoint that caused
  this loss.  At an absorber-separated level, every empty-remainder witness
  is determined by its missing third vertex, and that vertex injects into
  `absorberRootPairObstructionSet`; `HasPaddedAbsorberRootBounds` therefore
  gives the uniform bound six.  The direct Lean check passes.

The next obligation is the nonempty-remainder part of the same extension
bound.  It will retain the refined A2 local/support decomposition and its
inverse ambient factors, rather than replacing the bank part by an
unweighted unrestricted powerset count.

## 2026-08-21 — exact long-phase hazard and rational barrier repair

- `OuterOnlyExactAvailability.lean` identifies the live internal-outer edge
  clock exactly, so both scheduled availability bounds use the same eligible
  pair count.
- `ScaledExtensionWeight.lean` and
  `ScaledTimedStoppedAbsorberTails.lean` lift all four stopped absorber tails
  from ambient inverse hazard to an arbitrary hazard bounded by
  `scale / (|V|+1)`, with the required `scale^q` extension loss.  This removes
  the quantitatively false requirement `fuel / Dcut <= 1 / (|V|+1)`.
- The scaled interface has been threaded through
  `SharpScheduledAbsorberFailure.lean`,
  `SharpScheduledOuterOnlyAbsorberLaw.lean`, and
  `OuterSharpRecursiveProductLaw.lean`; direct checks pass.
- The upper quadratic barrier and cubic cancellation now use the exact
  eligible-pair clock instead of all ambient pairs.  The lower drift
  comparison now accepts a natural numerator/denominator coefficient, which
  permits the necessary `6 + O(1/t)` certificate without integer rounding.

The current obligation is to instantiate the rounded perturbed quadratic
corridor at the fine power-vortex scale, then feed the resulting initial
product law into the already verified compressed transition chain.
