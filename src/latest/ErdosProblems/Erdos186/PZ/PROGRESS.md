# Pham--Zakharov upper proof progress

- Phase: Lean formalization, post-CFP upper-bound integration.
- Verified aggregate builds (Lean 4.33): `PZ.Reduction`,
  `PZ.Intersection`, `PZ.ConvexDensity`, `PZ.FinalIteration`, and `PZ.Main`.
  The last fully completed aggregate `PZ.Main` build had 8836 jobs.  The
  current source has additional reduction, convex-density, intersection,
  unconditional discrete-John, and finite-hull determinant modules; a fresh
  aggregate validation is pending because the shared host load exceeded 300.
  `PZ.Main` exports the conditional implication chain
  `pzBoxBound_of_components`; `PZ.FinalIteration` proves
  `pzBoxBound_of_oneStep : OneStepPackageStatement -> PZBoxBound`.
- Convex-density (PZ Lemma 1): the exact all-dimensional proposition is
  `ConvexDensity.PZLemmaOneStatement`.  Dimension one, the dimension-two
  occupied graph slab, normalization, cap selection, boundary graphs,
  thickening bounds, and the reduction to dimensions at least two with small
  epsilon are proved and type-check in the aggregate, including the
  subgradient, affine-normalization, Householder-cap, ambient graph-slab, and
  retained-fibre modules.  The exact remaining theorem
  is `PZNormalizedFiniteHullCore` (and hence `PZFullSpanHullCore`): the
  all-dimensional normalized full-affine-span random-rotation/occupied-cell/
  slab assembly.  The proved theorems
  `pzLemmaOneSmallEpsilon_of_fullSpanHullCore` and
  `pzLemmaOneStatement_of_smallEpsilon` reduce the literal public statement to
  this core.  The Householder graph-chart conversion for cap-selected
  common-frontier witnesses is now proved.  The remaining step is the
  normalized low/high branch assembly from the already proved
  relative shells, graph slab, thickening, and numerical estimates.  The
  Householder graph-window normalization, initial boundary regularization,
  and label-preserving second-grid slab theorem are now also proved.  The
  second-grid clamped-floor assignment and relative occupancy shell are now
  proved in `UnitGraphGrid.lean`; the affine graph-window transport,
  normalized cube/ball volume constants, and generic branch-output
  constructor are also proved.  The exact remaining construction is the
  large-hull branch joining cap selection, the relative shell, the low/high
  slab split, thickening, and `BranchNumerics`, followed by the wrapper to
  `PZNormalizedFiniteHullCore`.  The natural and planar no-discard grid
  assignments and high-oscillation graph slabs are now present; the remaining
  join is the explicit low/high numerical package and final output constructor.
- CFP structure input (CFP Theorem 1.5 / PZ Theorem 3 and Corollary 5):
  both `CFP.IntegerTheorem15` and the exact all-dimensional target
  `CFP.HigherDimensionalCorollary5` are defined propositions, not proved
  theorems.  The deepest
  upstream obstruction remains the unformalized Bilu--Freiman inverse
  theorem needed by the CFP existence proof.  The no-carry layer itself now
  type-checks; its precise remaining transport obligation is a proper
  projected GAP presentation (`HasProperProjectedPresentation`).
- Irreducible replacement (PZ Lemmas 6--10): the bounded eligibility context,
  coordinate Definition 9, failure-generated replacement relation, exact
  Lemma 6/7/8 estimates, concrete reachability, and finite-chain termination
  are proved.  The corrected composition target is
  `Reduction.IrreducibleReplacementStatement`; it requires the source scale
  lower bound before deriving the `|A|^{-(1-epsilon) Delta d}` high-rank
  estimate and returns a reachable terminal result.  The context now uses the
  source-required exponent slack `2 * (beta + 1)`, and the large-cardinality
  threshold is correctly chosen after `delta`, `gamma`, and `K`, and the
  source condition `delta < 1` is explicit.  The guarded quantitative trace,
  uniform upward-jump/rank bound, finite guarded terminal, proof that the
  terminal cannot stop at the population cutoff, terminal closure,
  canonical-scale, population absorption, and candidate-eligibility layers
  are now proved.  The three source rank-case terminal volume inequalities,
  uniform initial bounds, and terminal gap absorption are also present.  The
  remaining composition is the final existential wrapper proving
  `IrreducibleReplacementStatement` from those layers.  Their output is strong
  enough to obtain the local
  `CandidateClosedAt` inequality
  `2^rank * volume <= |X|^(2*(beta+1))` for every dense candidate.
- Intersection (PZ Theorem 4, Lemmas 11--14): equation (15), subset-sum
  conversion, lattice-cube extraction, and the final contradiction are
  proved in `PZ/Intersection/Main.lean`.  The exact remaining construction is
  presently named `ProducesTheorem4PostCFPData`.  It is now stated on the
  selected core in its own coefficient dimension and explicitly requires
  local `CandidateClosedAt`, so coordinate irreducibility cannot be vacuous.
  It must be proved by completing the source hierarchies and side geometry.
  `Theorem4Parameters` now records positivity, subunit ranges,
  the two power hierarchies, logarithmic lower bound, box control, and the
  large-cardinality threshold.  The public `Theorem4PostCFPStatement` now
  type-checks with the bounded eligible selector, a positive ambient
  dimension, and a fixed rank ceiling; the earlier all-real/all-dimensional
  interface has been removed.  On the full-rank branch,
  `stepLattice_fullRank_and_covolume_le` and the common-covering-radius theorem
  are proved once the side step matrices have nonzero determinant.  The next
  eligibility part, simultaneous side selection from an explicit
  core-retention inequality, direct selected-progression containment in a
  canonical control box, projection-cardinality estimates, and the
  determinant/non-singularity criterion are proved.  A singular side is
  handled quantitatively and does not require a minimal-dimension selector.
  Side-two orientation is closed by an explicit reversed witness.  The
  remaining composition must prove the loss/core hierarchy, instantiate the
  determinant criterion from the scale hierarchy, and close the scalar
  adjugate/margin bounds and centered-zonotope thickness.  Canonical rounding
  cores, actual-step inverse-coordinate reduction, oriented side witnesses,
  common covering radii, and canonical targets are now constructed.
  `GAPErrorBox.lean` already proves
  equation (15) and Lemma 13 absorption, so residual absorption is not an
  independent abstract assumption.
- Final iteration (PZ Observation 15 and Theorem 2): the exponent numerics
  and finite contradiction are proved.  `StepOutput` keeps the structural
  ratio and convex scale separate; the same-run `U,V -> sigma` estimate and
  global trace architecture are proved.  The remaining glue theorem is
  exactly `PZ.OneStepAssemblyStatement`, which must construct
  `FinalIteration.OneStepPackageStatement` from the four source statements
  and discharge dimension/population persistence using (20), (24), and (25).
  `PZ/OneStepAssembly.lean` proves the finite restriction, coordinate GAP,
  nonaveraging, cardinality, and trace bridges.  Its first missing geometric
  input is the genuine PZ Lemma 7 discrete-John theorem: a rank dichotomy and,
  in full rank, an outer-GAP volume bound by the relative convex volume.  The
  finite `DiscreteJohn.Certificate.card_outer_le` alone only bounds by the
  number of lattice points and is insufficient.  `DiscreteJohnRank.lean`
  defines the canonical effective lattice-section rank, eliminating fake
  full-rank branches produced by zero-radius padding.  The checked adapter
  `DiscreteJohnSection.lean` proves the intrinsic-coordinate symmetric-body
  theorem and the effective-rank upgrade.  Consequently
  `activeDiscreteJohnUpgrade_of_discreteJohnSection` is proved, and
  `DiscreteJohnMahler.lean` proves the ambient discrete-John statement
  unconditionally.  The finite lattice hull, symmetric hull, exact lattice
  filter, and
  dimension-only cardinal bound are also constructed.  Thus
  `PZ/FiniteHullDeterminant.lean` proves
  `FiniteHullDeterminantCancellationStatement` by maximal-simplex
  normalization.  Its downstream adapter
  `pzLemmaSeven_of_fullRankVolumeBridge` reduces the source theorem to the
  single active-rank input `FullRankVolumeBridgeStatement`.  This statement
  requires the certificate rank to equal the canonical lattice-section rank,
  excluding padded zero-radius counterexamples; it retains the necessary
  additive-one lattice-rounding term, which the application threshold
  absorbs.  After
  Lemma 7, the remaining assembly task is to construct the concrete
  branchwise `OneStepPackageStatement` and its global dimension/population
  persistence witnesses from the four source components.
- Configuration ownership: no PZ subtree agent edited `lakefile.toml` or
  `lake-manifest.json`; unrelated `tablet32` and `APAP` changes are therefore
  left untouched.
