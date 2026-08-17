# Erdős 622 formalization: complete

- Current phase: complete.  The detailed mathematical proof is in
  `tex/622.tex`, and the public Lean theorem is
  `Erdos622.erdos_622 : Resolution` in `ErdosProblems/Erdos622.lean`.
- Verified foundations: the exact cyclic-subset predicate and count, finite
  counting algebra, cut/degree identities, cover and matching lemmas,
  concentration estimates, the binomial CLT bridge, Gaussian-window bounds,
  weak regularity, linear-forest bookkeeping, and the full cleaned structural
  trichotomy all type-check under Lean 4.33.0.  Prescribed-endpoint balanced
  bipartite Hamilton paths and the full Petersen factorisation now check as
  well.  The bounded weak-regularity theorem now includes uniform bounds on
  every rectangle coefficient and on total coefficient mass.  The
  Chvátal--Erdős Hamiltonicity theorem (vertex-connectivity at least `k` and
  independence number below `k`) is fully formalized and rechecked.  The
  almost-two-cliques lane has a checked deterministic Hamilton-cycle theorem
  from two sparse-complement parts and two disjoint crossing edges.  The Alon
  lane also has checked regular completion, color pairing,
  cycle breaking, the independent-transversal local-lemma argument, and a
  greedy low-degree-remainder decomposition.  These pieces are now assembled
  into an unconditional high-girth bound: maximum degree at most `2*k` and
  girth at least `100*k` give a decomposition into `k+1` linear forests.  A
  checked grouped version partitions the Petersen factors into blocks of
  size `q` and produces `(k/q+1)*(q+1)` forests under extended girth
  `100*q`, which is the quantitative input for Alon's induction.  The
  minimum-cover random-matching lemma used in the almost-bipartite case is
  also unconditional and checked, including its uniform exponentially small
  failure bound.  Alon's induction has now been connected to the grouped
  high-girth theorem, including all floor/ceiling and normalized cost limits.
  The asymmetric-local-lemma sparse extractor and its eventual logarithmic
  scalar estimates are now also complete, so
  `AlonInduction.alon_asymptoticLinearArboricity` is unconditional, builds,
  and has only the standard Lean axioms.
- Verified failures/repairs: complement pairing, direct Dirac/Ore inheritance,
  and a proposed exact large-linear-forest shortcut are insufficient.  The
  last shortcut is an open path-partition conjecture, so the development uses
  the source's genuine Alon linear-arboricity input.
- The full almost-two-cliques random-subset case is now proved: its exported
  `UniformCaseDensityBound` is accepted after combining the deterministic
  sparse-complement Hamiltonicity theorem, a fixed crossing matching, and
  the two concentration estimates.
- The bi-dense lane is complete.  The full Nash--Williams--Bondy
  dominating-cycle theorem, the fixed-loss KSS stability statement, and
  `uniformCaseDensityBound_biDense` all pass direct checks and module builds.
  All weak-regularity coefficient bounds, sampled-profile transfer, degree
  inheritance, eventual arithmetic, and powerset bad-event counting are
  therefore part of one unconditional checked chain.
- The almost-bipartite lane now includes induced minimum-cover transport,
  the unconditional random-cover matching estimate at the required growing
  cover scale, matching-to-linear-forest conversion, the compact-uniform
  two-block Gaussian window, and exact finite counting assembly.
- The deterministic good-cut absorber is now complete through its oriented
  public theorem.  It constructs Hall attachments, maximizes an admissible
  linear forest, joins its components with one- and two-vertex connectors,
  extracts a spanning path, proves the exact imbalance identity, handles
  same-side endpoints by a fresh crossing extension, and closes the residual
  balanced bipartite graph.  The oriented theorem, its symmetric cut form,
  and the sampled-cycle wrapper all pass direct checks and module builds
  under the default limits.  `SuitableCertificate` now turns the uniform
  sample-concentration event plus an `IsKGoodSample` witness directly into a
  cycle spanning the sampled vertex set.
- A quantitative audit of the fully explicit absorber showed that the first
  provisional structural constants were too coarse.  The canonical values
  are therefore now `epsilon0 = 1/1048576` and `gamma0 = 1/256`.
  `TailoredTrichotomy`, `Regimes`, `AlmostCliques`, and `BiDenseCase` all
  pass direct checks and module builds with these stronger constants.  The
  sampled Hamiltonicity constants have been retuned simultaneously
  (`samplingRho = 2^-24`, protected budget `n/2048`, and low-set-union budget
  `n/6000`).
- The almost-bipartite count is complete in every cover regime.  Checked
  inputs include the exact
  balanced-cut powerset transport, both one-small-cover orientations over
  the full square-root imbalance range, the original-side sampled Alon
  forest of size `20d`, the bounded-internal sampled forest, balancing-set
  concentration, and the compact shifted Gaussian window.  The exact
  three-forest transfer uses the union window
  `2t - max LA L0 <= z <= max (2t) RB`; its normalized endpoints have product
  at least `15/32`, giving a uniform margin above one half on compact cover
  ranges.  The original tailored cut is kept distinct from the auxiliary
  balanced cover cut throughout.
- The unconditional two-large-cover count, the almost-bipartite case bound,
  and the final three-case assembly are all checked.  The public theorem's
  dependency report contains only `propext`, `Classical.choice`, and
  `Quot.sound`.
