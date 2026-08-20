# Erdős 446 progress log

- Phase 1 — complete. `tex/446.tex` reconstructs Ford's dyadic estimate,
  fixed-multiplicity corollary, endpoint transfer, and detailed Leanization
  dependency plan. The cited Ford sources were checked against both the short
  dyadic paper and the Annals paper. The corrected 17-page document passes
  `pdflatex -interaction=nonstopmode -halt-on-error -output-directory=/tmp tex/446.tex`.
- Phase 2 — active. More than one hundred sixty substantive arithmetic, density,
  sieve, cluster, prime-block,
  ordered-slot, and close-pair modules have passed Lean checks. In particular:
  the literal open-interval densities exist; the endpoint error is `1/(2n)`;
  the Ford scale and endpoint little-oh transfer compile; the finite CRT/sieve
  lower reduction compiles; and the full largest-differing-slot bound has been
  translated back to `sum_a W(a)/a` with exact factorial and block-mass factors.
- Latest verified milestones: the complete thirty-two-module chain has been
  recompiled with Lean 4.33.0 in an isolated coherent package cache; sharp
  without-replacement elementary mass;
  exact reciprocal-block-mass close-pair bound; geometric `O(2^{-j})` Mertens
  error for the doubly exponential prime blocks; finite product perturbation
  bounds; the exact unrestricted cyclic-composition identity
  `sum_b 1/(b! F(b)) = k^(k-1)/k!`; and Ford's arbitrary-positive-list
  rotation inequality for total product at most one.
- Latest verified cap milestone: `CappedCompositions.lean` proves, with no
  placeholders, that Ford's one-sided constraints
  `b i ≤ M * (M + i)` retain at least one half of the exact unrestricted mass
  `K^(K-1)/K!` whenever `M ≥ 3` and `K > 0`.  The proof formalizes coordinate
  deletion, cyclic averaging of the tail, reciprocal-factorial convolution,
  and the summable dyadic cap loss.
- Latest verified lower-bound milestone: `PartitionedLower.lean`,
  `BlockPartition.lean`, `BlockMassBounds.lean`, `BlockCloseBounds.lean`, and
  `DyadicLowerCore.lean` compile.  Together they preserve the sum of the
  per-block Cauchy quotients through exact-support partitioning, prove the
  sharp divisor and close-pair products, and assemble the explicit finite
  dyadic lower theorem under fixed parameter, scale, and size hypotheses.
- Latest verified size-closure milestone: `SizedCompositions.lean` proves a
  decrement-and-rotation first-moment bound and retains at least half of the
  full cyclic mass after imposing the logarithmic size cutoff.
  `SizedBlockBounds.lean` converts that cutoff to the sharp product bound and
  all divisor-scale inequalities, and `SizedDyadicLowerCore.lean` compiles the
  resulting size-closed finite lower theorem. `DyadicParameters.lean` chooses
  one fixed initial block satisfying every Mertens, selection, atom-loss, and
  close-pair budget through polynomial-over-exponential limits.
- Latest verified uniformity milestone: the size-closed theorem now works at
  every ambient endpoint beyond its construction scale, not only at an exact
  scale value. `FixedDyadicLower.lean` specializes all analytic hypotheses to
  one fixed triple `N,M,C` and gives the explicit finite lower bound uniformly
  for every depth `K > 0` and every such endpoint.
- Latest verified asymptotic milestone: `ScaleSelection.lean`,
  `ScaleAsymptotics.lean`, `LowerCoefficient.lean`,
  `LowerModelAsymptotic.lean`, and `LowerBound.lean` compile. They select the
  maximal admissible depth, identify the exact exponential base, apply
  Stirling, supply the Euler/Mertens factor, and prove the lower half
  `growth446 =O[atTop] (fun y => epsilon y (2*y))`.
- Latest verified upper/multiplicity milestone: `ClusterUpper.lean` proves
  Ford's global interval cover, product envelope, and the exact minimum over
  all squarefree prime prefixes. `IsolatedDivisors.lean` proves the finite
  close-pair inequality and Ford's power lower bound for isolated divisors.
  `UpperElementaryMass.lean` proves the factorial/power upper estimate for
  elementary reciprocal mass and its block-family corollary.
- Latest verified Abel milestone: `AbelPolynomial.lean` proves the exact Abel
  binomial convolution as a polynomial identity, and `AbelConvolution.lean`
  converts it into the nonnegative interior-sum comparison required by Ford's
  simplex recursion. Both compile with Lean 4.33.0 and contain no placeholders.
- Latest verified Smirnov milestone: `SmirnovOccupancy.lean`,
  `SmirnovNumerics.lean`, `RaneyRotation.lean`, and `RaneyOccupancy.lean`
  compile.  They define the exact multinomial occupancy probability, prove
  Raney's cycle lemma from last occurrences of consecutive prefix levels,
  translate it to cyclic occupancy vectors, perform the reciprocal-factorial
  double count, and derive the exact uniform identity
  `M(k,0,w+k) = w * abelKernel w k / k!`, including `k = 0`.
- Latest verified Pyke milestone: `SmirnovLastFailure.lean`,
  `SmirnovSplitMass.lean`, and `SmirnovPyke.lean` compile.  They partition
  failed occupancy vectors at their last failed prefix, identify every fiber
  with an exact prefix/tail product, evaluate the tail by the Raney identity,
  and prove Pyke's complete finite last-failure formula for
  `k! * smirnovOccupancyMass k u v`.
- Latest verified quantitative Smirnov milestone: the labelled-word
  multinomial bridge, first-crossing code fibers, fiber preservation,
  truncated/full exponential comparison, and disjoint fiber summation all
  compile. `SmirnovQuantitative.lean` now proves Ford's constant-24 finite
  Smirnov upper bound without an analytic hypothesis.
- Latest verified variable-denominator milestone: `ClusterProductSharp.lean`,
  `PrimeLogMoments.lean`, `FordPowersetMoments.lean`,
  `FordClusterLogMoments.lean`, `FordLargestPrimeSummation.lean`, and
  `FordVariableDenominator.lean` compile.  They prove the full finite
  Ford--Koukoulopoulos variable-logarithm reduction with only the standard
  Mathlib axioms.  The exceptional event in the writeup has also been
  corrected to Ford's literal linear cutoff `l - γ - 2m`.
- Latest verified fixed-multiplicity milestone: `FixedLowerEnergyMoment.lean`
  gives the unconditional prefix-energy moment bound;
  `FixedMultiplicityDensityLower.lean` assembles the size-truncated positive
  family, isolated-prime selection, exact-valuation CRT cells, rough sieve,
  Euler factor, and depth asymptotics.  Its theorem
  `exists_fixedMultiplicityModelDensityLower` proves the required positive
  comparison for every fixed `r ≥ 1`, with only standard Mathlib axioms.
- Latest verified exceptional-cover milestone: the source-accurate discrete
  cover with Ford's literal cutoff `l - γ - 2m`, its crowding translation,
  the four-factor reciprocal-mass split, and the strengthened factorial
  suppression by `2^(2^(m+3))` all compile. `UpperFinalAssembly.lean` also
  compiles the constant-removal bridge from the two finite upper estimates to
  the exact half-open Big-O statement used by the final public theorem.
- Latest verified upper-integration milestone:
  `UpperWeightedExceptionalSumFinal.lean` gives unconditional high- and
  low-depth estimates for the complete exceptional occupancy family while
  retaining the crucial `(k+1)!` denominator.  The complementary-largest-
  prime shell and an unconditional endpoint-free rough-interval estimate also
  compile.  `WeightedWordMassBridge.lean` proves the exact factorial-scaled
  identity between categorical word events and weighted composition mass,
  avoiding any accumulated pointwise prime-block error.
- Latest verified trimming/sieve milestone: `UpperTrimmedPrimeBlocks.lean`
  constructs a maximal retained subset in every prime block with reciprocal
  mass at most `log 2`, proves the discarded mass is geometrically summable,
  and therefore preserves the exact exponential base needed in the exceptional
  occupancy sum. `UpperComplementaryClusterReduction.lean` proves the
  source-faithful squarefree dyadic-shell bound in terms of
  `squarefreeClusterMass`, while `UpperPowerfulWeightedMass.lean` proves the
  convergent powerful-number divisor-weight needed to sum the squarefull
  fibers.
- Latest verified support-pooling milestone: `UpperTrimmedBlockPartition.lean`,
  `UpperRetainedBlockMass.lean`, and `UpperTrimmedLowSupportMass.lean` compile.
  They split every smooth support uniquely into auxiliary and retained parts,
  bound the auxiliary part by the single residual Euler factor, and sum the
  retained part through Ford's sharp exceptional-layer estimate without
  losing the `(k+1)!` denominator.
- Latest verified final-upper milestone: `UpperTrimmedFinalEndpoint.lean`
  combines the retained/residual low-cardinality support estimate with the
  high tail and proves the unconditional smooth squarefree cluster bound.
  `UpperPowerfulCutoffNumerics.lean` supplies the uniform squarefull cutoff,
  and `UpperSieveClusterReduction.lean` assembles Ford's Lemmas 3.2--3.3 into
  the unconditional `DyadicUpperSieveClusterReduction` required by the
  asymptotic bridge.
- Final assembly: `ErdosProblems/Erdos446.lean` now proves
  `epsilon_isBigO_growth446`, the complete theorem `erdos_446`, its sharp
  growth component, every-fixed-multiplicity comparison, and the literal
  disproof of `deltaR 1 = o(delta)`.  The direct Lean check passes at default
  limits and `#print axioms Erdos446.erdos_446` reports only `propext`,
  `Classical.choice`, and `Quot.sound`.  The final forbidden-token scan and
  `git diff --check` are clean, and `tex/446.tex` builds successfully to a
  19-page PDF.
