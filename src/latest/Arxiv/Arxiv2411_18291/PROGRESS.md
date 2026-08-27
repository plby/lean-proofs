# arXiv:2411.18291 formalization

Source: `tmp/arxiv-2411.18291/DesignsShort.tex`, Peter Keevash,
*A short proof of the existence of designs*.

## Objective and current status

The objective remains the paper's unconditional results, including Theorem 1.1:
for every `q > r ≥ 1`, all sufficiently large `K_q^r`-divisible complete
`r`-graphs have a true `K_q^r`-decomposition. The quantitative threshold in
the source is `(4*q)^(90*q*(2*q)^r*(6*choose(q,r))^2)`.

**Theorem 1.1 is proved unconditionally at the paper's original explicit
threshold.** `design_existence_paper_threshold` proves that every divisible
complete graph in the stated range has an actual decomposition for
n >= (4*q)^(90*q*(2*q)^r*(6*choose(q,r))^2).
`hasDecomposition_iff_binomial_divisibility_paper_threshold` gives the
same result using the numerical binomial divisibility conditions. The
reserve, absorber, regular family, nibble, and cover are all constructed;
rank one uses a partition. No auxiliary existence assumption remains.

`exists_sparse_absorber_paper_threshold` now proves the full sparse
absorber lemma at n0 in every positive rank. It avoids the old flattening
cost by retaining growing edge caps through integral generation, weighted
decoding, variable splitting, and both cancellation stages. The first
stage has raw coefficient C1*n^(-17alpha/45); the sharper further-pair
count keeps the second stage at n^(-5alpha/18), stronger than the required
n^(-alpha/4). The final fixed negative family is a true decomposition,
and its host absorbs every admissible leave. In rank one the empty host
suffices.

The earlier `design_existence`, `design_existence_explicit`, and
`correctedDesignThreshold` APIs remain valid. The corrected bound includes
a conservative flattening cost and is strictly larger than n0 for
triangles. The new theorem does not use that cost.

The formalization is complete with documented corrections to false source
statements. Every labelled result has a proof or a formal counterexample
with a proved repair. The final build, full public-theorem assumption audit,
and source-label review all pass. The main theorem, sparse absorber, and
quantitative nibble retain the original n0; the nibble retains constant 3.

**The user has authorized repairing the false concentration statement.**
`ConcentrationCounterexample` proves that Lemma 5.1(1), `lem:pseudobin`, fails
for independent signed summands, even with positive parameters and `0 < c ≤ 1`.
The working correction is to require nonnegative summands in part 1 and check
that hypothesis at its applications. The original source and counterexample
are retained; this correction does not weaken the main existence theorem.

The printed definition of `whp` is also false for Lemma 5.3: an explicit
isolated-vertex event has failure probability greater than `exp(-n/10)`.
This is proved for ordinary graphs with p=1/100 and every n >= 1000000.
A corrected statement, with failure below `exp(-n^(1/10))`, is now proved at
the paper's density and typicality-error scales and its original local
threshold n>=2^(9*R*h), in every positive edge rank R. The earlier explicit
threshold also remains available and fits below n0 through the full exchange
configuration. The main theorem uses actual probability bounds and is
unaffected by the refuted printed rate.

No declarations use `sorry`, added axioms, `native_decide`, or increased
heartbeats, recursion depth, or other computational limits.

## Checked infrastructure

| Module | Result |
| --- | --- |
| `Basic` | Uniform hypergraphs, clique edges, integer characteristic vectors, incidence operator, true and integral decompositions, closure under disjoint union and subtraction |
| `Incidence` | Counts of subsets between two fixed sets; the degree/incidence double-counting identity; necessary binomial divisibility conditions |
| `Decomposition` | Exact edge coverage and uniqueness; conversion from nonnegative integral coefficients to true decompositions; disjoint union and signed absorption |
| `Absorption` | Divisibility of the leave and the deterministic completion step from an absorber and a suitable partial decomposition |
| `LocalDecoder` | Explicit inclusion–exclusion decoder and its exact boundary |
| `DecoderBound` | The full `lem:decode`, including multiplier `r! * choose q r` and coefficient bound `2^q * r!` |
| `LocalDecoderOn` | The same decoder supported on a chosen `(q+r)`-set in an arbitrary larger graph, with zero boundary outside it |
| `IntegralSpan` | Integral generation by a prescribed family; correction of a representation modulo `N` using local decoders |
| `RationalIncidence` | Rational surjectivity on `q+r` vertices, with an explicit right inverse; inclusion–exclusion reconstruction of clique coefficients |
| `Divisibility` | Necessity and sufficiency of degree divisibility for integral decomposability on exactly `q+r` vertices |
| `Partite` | Complete partite hypergraphs, cliques as graphs of functions, and the unique-coverage characterization of decompositions |
| `PolynomialDecomposition` | Shifted polynomial families are true decompositions; exact counts of cliques and edges |
| `ExchangeSeed` | Constructs the prime-field seed, both disjoint decompositions, distinguished cliques and common edge, and the bound `(2q)^r * choose(q,r)` |
| `DecompositionGluing` | Exact clique-family gluing, erasing the shared clique, and preservation of disjointness between the two families |
| `Relabeling` | Injective relabeling preserves cliques, hypergraphs, and actual decompositions |
| `VertexGluing` | Constructs the glued vertex type and embeddings; proves exact graph intersection, both decompositions, edge accounting, and the two-glue separation calculation |
| `AlignedGluing` | Constructs the clique bijection identifying any specified pair of contained `r`-edges |
| `PreparedFamily` | The separation and locality invariant for previously prepared edges, its admissibility consequence, and injective relabeling |
| `PreparedGluing` | Preserves the invariant when attaching a copy along an interface avoiding all prepared private vertices |
| `PreparedInsert` | Extends the invariant with a new distinguished clique and its last-copy region |
| `ExchangeSystem` | Bundles actual pairs of disjoint decompositions and constructs the glued system, with edge accounting |
| `AttachmentGeometry` | Exact intersections and locality of the two attached copies |
| `PrepareEdge` | Constructs two aligned attachments for one new base edge, proves all invariant fields, and bounds added vertices by twice the seed carrier |
| `ExchangeIteration` | Finite induction preparing every base edge, bounding both edges and vertices by `(2*s.card+1)` times the corresponding seed count |
| `ExchangeConfiguration` | Full `lem:OO`, including frame locality, cross simplicity, the paper's edge bound, and the carrier bound `6*q^2*choose(q,r)` |
| `CoefficientRelabeling` | Transport of signed vectors under vertex equivalences and coefficient pushforward, including degree and boundary identities |
| `VertexDeletion` | Links, zero extension, coning, and preservation of degree divisibility when deleting a vertex with zero link |
| `GlobalDivisibility` | Full `rem:div` for every `n ≥ q+r`, by induction; numerical binomial characterization of divisibility for complete hypergraphs |
| `ConcentrationCounterexample` | An independent, bounded, measurable, integrable finite counterexample to part 1 of the signed concentration lemma as printed |
| `ExponentialBound` | A scalar linear upper bound for `exp(t*x)` on `0 ≤ x ≤ C`, and the exact choice of concentration parameters |
| `ConditionalExponential` | Conditional exponential bound and one-step compensation by the conditional mean, with all integrability obligations proved |
| `ExponentialProcess` | Measurability, integrability, bounds, and expectation at most one for the finite compensated exponential process |
| `AdaptiveConcentration` | Full part 2 of `lem:pseudobin`, both for a general filtration and the sigma-algebra generated by preceding variables; a stronger bound with denominator `(2+c)*C` is also proved |
| `IndependentConcentration` | Corrected part 1 of Lemma 5.1 for `0 ≤ X_i ≤ C`, with the printed constants; stronger separate upper and lower tail bounds are also proved |
| `BernoulliSubset` | Independent random subsets; occurrence probabilities and expectations; mutual independence for disjoint configurations; concentration of their counts |
| `Neighborhood` | Common neighborhoods, the typicality definition, and the disjoint edge sets used by distinct candidate vertices |
| `RandomHypergraph` | Exact edge-count and common-neighborhood expectations and concentration, with the finite-size correction `(n - |⋃ A|) * p^|A|` |
| `RandomTypicality` | Explicit simultaneous failure bound over all families of at most `h` faces, including the exact number of tests |
| `TypicalityDensity` | Conversion from reference density to observed density, with an explicit error constant |
| `TypicalGraphExistence` | Simultaneous density/typicality failure bound and a finite graph-existence criterion with numerical hypotheses only |
| `TypicalityBounds` | Failure bound at most `2*(h+2)*n^(r*h)*exp(-n*p^h*c^2/12)`, where the graph uniformity is `r+1` |
| `AsymptoticTypicality` | Typical sparse graphs exist for all sufficiently large `n` when `ρ*h + 2*δ < 1`; also the paper's `p ≥ n^(-1/(2*h))` and error `n^(-1/10)` scales |
| `PuncturedClique` | Exact one-vertex extension criterion for cliques with one specified edge exempted; typicality lower bounds after removing old vertices |
| `CliqueExtensionCount` | Bijection between new vertices and larger cliques; exact double count of predecessors |
| `TypicalCliqueCount` | Full iteration of the clique count, with density exponent `choose q r - 1` and divisor `(q-r)!` |
| `GraphBoundedness` | Strict face-degree boundedness, its equivalence to neighbor counting, and its consequence from typicality |
| `ReserveCriterion` | Numerical criterion yielding strict boundedness and the required number of clique extensions |
| `ReserveExistence` | Eventual sparse reserve existence, including the paper's exponent `ρ = (6*choose q r)^(-2)` and the stronger `n^(-ρ)` degree bound needed by the absorber |
| `EmbeddingExtensions` | Explicit equivalence between root-preserving embeddings and embeddings of free vertices into unused vertices; exact falling-factorial count |
| `EmbeddingCountBounds` | Upper bound `n^m` and lower bound `(3/4)*n^m` on the initial extension count when `n ≥ 4*v_H^2` |
| `ForbiddenEmbeddingCount` | A single new edge excludes at most `θ*n^m` root-preserving embeddings, by fixing every other free vertex and using the forbidden graph's degree bound |
| `TargetEmbeddingCount` | At most `k!*n^(m-k)` extensions send a specified edge with `k` free vertices to a fixed target edge |
| `LegalEmbeddingCount` | At least `(1/2)*n^m` legal extensions remain when the forbidden graph is `θ`-bounded and `|H|*θ ≤ 1/4` |
| `UniformExtensionProbability` | Actual uniform transition probabilities, with target-edge probability at most `2*k!/n^k` |
| `EdgeFamilyBoundedness` | Degrees of edge families with repetitions, lower-dimensional degree bounds, and counts of large intersections with a target edge |
| `GreedyRootCompatibility` | Admissibility and root images; incompatible targets have probability zero; the cumulative target budget is at most `2*r!*θ` |
| `GreedyProbabilityBudget` | The deterministic cumulative face budget is at most `2*r!*θ*n`, including repeated prescribed root images |
| `FiniteHistoryProcess` | Constructs the trajectory measure from finite history-dependent transition laws; proves its conditional-expectation formula and almost-sure transition support |
| `FiniteHistoryConcentration` | Adaptive concentration for the constructed process, including the closed threshold event needed for strict degree boundedness |
| `PartialEdgeFamily` | Graph degrees are bounded by sums of partial edge incidences; explicit bounds for unions of previously used edges |
| `GreedyEmbeddingProcess` | Actual stopped random greedy process, with an absorbing abort marker, avoidance of every previously used new edge, and a quantitative legal-choice bound |
| `GreedyStepExpectation` | Every history satisfies the root-dependent face expectation bound; stopped steps contribute zero |
| `GreedyDegreeConcentration` | Simultaneous degree-failure bound over every new pattern edge and ambient face, using the proved adaptive inequality |
| `GreedySuccess` | Monotonicity of prefix degrees and proof that a trajectory below all final degree caps cannot abort |
| `GreedyEmbeddingExistence` | Extracts actual root-preserving embeddings with disjoint new edge sets, forbidden-edge avoidance, and boundedness; proves a finite numerical existence criterion |
| `AsymptoticGreedyEmbedding` | Discharges the finite numerical criterion for every fixed admissible pattern at `θ = n^(-ρ)`, `0 < ρ < 1`, uniformly over the length and values of the root sequence |
| `PrescribedEmbeddingCount` | At least `(η/2)*n^m` legal candidates remain from `η*n^m` prescribed choices under the separate forbidden-density budget |
| `PrescribedExtensionProbability` | Target and face probability bounds divided by candidate density `η`, with cumulative conditional-mean budgets |
| `PrescribedGreedyProcess` | Constructs the stopped process with history-dependent candidate sets and separate root and forbidden densities |
| `PrescribedGreedySuccess` | A supported trajectory below the final degree caps cannot abort and yields embeddings in every prescribed candidate set |
| `PrescribedGreedyConcentration` | Actual process degree tails and simultaneous failure probability at output scale `4*r!*θ/η` |
| `PrescribedGreedyExistence` | Finite numerical existence criteria for dynamic and static prescribed candidate families |
| `AsymptoticPrescribedGreedy` | Eventual construction for `η=n^(-a)`, root density `n^(-b)`, and forbidden density `n^(-c)` when `2*a<b`, `a<c`, and `b-a<1` |
| `EmbeddingCliqueImages` | Punctured-clique counts give candidate-embedding lower bounds; new edges are precisely the image clique minus its root edge |
| `RootedCliquePattern` | Explicit root bijections, admissibility of complete clique patterns, and boundedness of an injective enumeration of a bounded leave |
| `CliqueCover` | Converts disjoint new-edge families into edge-disjoint full cliques; constructs a true decomposition of their union with exactly one clique per leave edge |
| `CoverExistence` | Eventual Cover lemma for candidate scale `n^(-a)` and leave scale `n^(-3*a)`, `0<a<1/2`, uniformly over all leaves and reserves |
| `ReserveCover` | Cover at the paper's parameters; constructs an actual sparse reserve that covers every suitably bounded disjoint leave |
| `GreedyFamilyBounds` | Bounds the union by thetaB plus the exact new-edge count times L; the same embeddings retain their bounds after restricting to any subpattern |
| `RootedCliquePlacement` | Extends every edge of a sparse graph to an edge-disjoint larger clique whose other edges avoid the original graph, with an explicit bound on the union |
| `CliqueRefinement` | Replacing a decomposition into `k`-cliques by all their `q`-subcliques gives exact edge multiplicity `choose(k-r,q-r)` |
| `CliqueFamilyBoundedness` | The paper's strict boundedness for boundary multigraphs; support and multiplicity bounds imply it, and unions obey the sum of the bounds |
| `SparseLocalDecoders` | Constructs all local decoder regions simultaneously; the decoder clique family has sparse support, bounded boundary, multiplicity at most `choose(q,r)`, and the exact decoder multiplier and coefficient bound |
| `CoefficientReduction` | Reducing coefficients modulo `N` to `[0,N-1]` gives boundary correction quotients in `{-1,0}` for a represented graph and a family of edge multiplicity at most two |
| `DecoderCorrection` | The local correction retains the individual coefficient bound, has the required boundary, and is supported on a family disjoint from the original cliques |
| `BoundedRepresentation` | Uniformly for all represented leaves, constructs a representation on the original and decoder families with every coefficient at most `2^q*r!` in absolute value |
| `RepeatedCliqueRoots` | Bounded clique boundaries control selected root-edge families with repetitions; bounded edge multiplicity gives a uniform bound on conflicting roots |
| `VertexAvoidingExtensions` | Avoiding `u` specified vertices excludes at most `m*u*n^(m-1)` extensions; at least half the candidates remain under explicit size conditions |
| `SeparatedGreedyCandidates` | History-dependent exclusion of earlier related free vertices, with candidate counts on every history and separation of the extracted embeddings |
| `SeparatedGreedyExistence` | Finite construction of disjoint new-edge families with the required free-vertex separation and output constant `8*r!` |
| `AsymptoticSeparatedGreedy` | Discharges the separated construction's numerical conditions for any fixed conflict bound and density `C*n^(-ρ)`, `C≥1`, `0<ρ<1`, without weakening the exponent |
| `CliqueRootInputs` | Admissibility of any complete clique root, root-image containment, and the finite prefix bound on conflicting clique roots |
| `SplittingPlacements` | Places actual exchange configurations on repeated clique roots, with disjoint new edges, forbidden-edge avoidance, free-vertex separation, and a bound on the full union |
| `ExchangeReplacement` | The exchange replacement has exactly the base clique's boundary, unit signed coefficients, and a new edge in every replacement clique |
| `SplittingDisjointness` | Replacement clique families from distinct copies are disjoint, and they avoid the original clique family |
| `SplittingAlgebra` | Selected signed replacements preserve the sum of base boundaries and give a difference of disjoint sets of cliques with coefficients in `{-1,0,1}` |
| `SignedCliqueSlots` | Fixed `C` positive and `C` negative slots per clique represent every coefficient in `[-C,C]`, respect the slot signs, and repeat each root at most `2*C` times |
| `SplittingFamily` | Constructs one sparse separated splitting family uniformly for every bounded representation on the input cliques |
| `SplittingSigns` | Fixed disjoint positive and negative replacement families support every resulting signed representation, with the correct orientation for each slot |
| `CliqueIntersections` | Singleton edge intersections are equivalent to exact vertex intersections; distinct cliques of a decomposition are edge-disjoint |
| `ExchangeNearFar` | Every near replacement is a distinguished negative clique and meets the base in exactly one edge |
| `SplittingCopyGeometry` | Different exchange copies share edges only in the original graph; near images meet it in one edge and far images avoid it |
| `SplittingNearFar` | Intrinsic near/far classification, inherited root signs, and edge-disjointness of negative far cliques from every other negative splitting clique |
| `SplittingNearIntersections` | Distinct negative near cliques and opposite-sign near pairs sharing an edge intersect in exactly that edge's vertices |
| `SplittingPartners` | Every edge outside the original graph in a negative near clique has a unique positive splitting partner, which is far |
| `ExchangeSeedIntersections` | The printed seed has an opposite-clique intersection of `q-r` vertices, exposing the extra condition needed by elimination when `q>2r` |
| `PolynomialExchangeSeed` | A degree-`r` translation constructs a stronger seed with all opposite-clique intersections at most `r`, with unchanged prime range and edge bound |
| `CrossSimpleGluing` | Gluing preserves the stronger opposite-clique intersection bound; the complete exchange construction inherits it |
| `ExchangeElimination` | Exact signed cancellation identity, avoidance of the common edge, negative-clique disjointness, intersection bounds, and pair-root admissibility |
| `PairRootEmbedding` | Constructs an injective map prescribing both root cliques of any target pair with the required vertex intersection |
| `EliminationPattern` | Unconditionally constructs the finite admissible cancellation pattern with the paper's size bound and no extra induced root edges |
| `SplittingMultiplicity` | At most two splitting cliques per outside edge, at most `2*C*M` per original edge, and a boundary bound with multiplier `2*C*M+2` |
| `CliquePairBounds` | Distinct ordered pairs sharing an edge repeat each coordinate at most `choose(q,r)*M` times; their root-edge families are bounded |
| `EliminationRootInputs` | Every induced root edge lies on one fixed side of the pair, giving the exact input bound for all prescribed root maps |
| `EliminationPlacements` | Constructs simultaneous sparse exchange placements on any prescribed distinct clique pairs with the required intersections, uniformly for all sufficiently large sizes |
| `EliminationFamily` | Packages actual placements for arbitrary finite index types, with both roots, root support, forbidden-edge avoidance, disjoint new edges, and the sparse graph bound |
| `EliminationCopyGeometry` | A negative replacement meets the previous graph only inside its negative root; any such old edge is unique |
| `EliminationNegativeGeometry` | Good negative cliques are edge-disjoint from all other negatives; bad cliques have singleton old intersections; a root-intersection criterion gives full negative edge disjointness |
| `NearCancellationPairs` | The finite set of all opposite-sign near pairs has no repeated pair and has the required exact intersections and original-edge containment |
| `FirstElimination` | Constructs the first elimination stage, proves its negative cliques avoid the original graph, and supplies each bad clique's unique positive far partner with exact vertex intersection |
| `EliminationSupport` | Both signs lie in the sparse extension graph; outside edges belong to one copy and have multiplicity at most two |
| `EliminationMultiplicity` | Old-edge multiplicity is at most `4*choose(q,r)*M^2`; the entire family and its union with the input family have explicit boundary bounds |
| `FurtherEliminationPairs` | Constructs the second-stage pairs and proves their negative-root overlaps lie in their positive partners, including intersections with retained negative cliques |
| `SecondElimination` | Constructs all second-stage exchanges at the same density exponent, using proved combined multiplicity and support bounds |
| `FinalNegativeFamily` | The retained and second-stage negative cliques are edge-disjoint, truly decompose their union, avoid the original graph, and satisfy the sparse graph bound |
| `TwoStageElimination` | Combines both stage-existence theorems into one uniform construction with explicit constant factors and the verified negative-host decomposition |
| `EliminationDisjointness` | Every elimination clique has a new edge; replacement copies have disjoint clique sets, avoid all previous cliques, and have disjoint signs |
| `FiniteFiberMatching` | Fiber cardinality inequalities give an actual color-preserving injection between finite families |
| `NearMatching` | Nonnegative old-edge boundary matches every selected negative near clique to a distinct selected positive near clique; the selected pair indices repeat neither root |
| `SelectedElimination` | Selected replacements have the boundary of the removed root pairs; replacing them in signed sets preserves the boundary and disjoint signs |
| `FirstCancellation` | Every bounded representation can undergo the first cancellation stage; all negative near cliques disappear and the negative far cliques are retained |
| `PreparedProtection` | Positive-clique locality survives both gluing attachments and insertion, including uniformity one; the exchange construction now carries this invariant |
| `FarPartnerIntersections` | Each positive far splitting clique shares at most one edge with the entire negative near family |
| `SignedEdgeForcing` | A nonnegative signed boundary forces a unique available positive partner and forbids a second negative clique at that edge |
| `FurtherPartnerSelection` | Every selected bad negative clique has an available positive far partner, and these partners are distinct |
| `FurtherCancellation` | The second selected cancellation preserves the boundary and places all negative cliques inside the fixed decomposed host |
| `SignedAbsorption` | The same fixed host absorbs every bounded represented leave, producing a true decomposition after adding its unused cliques |
| `SparseSignedAbsorber` | Unconditionally constructs sparse hosts for all bounded representations on any given sparse bounded-multiplicity family, at every exponent `0<ρ<1` |
| `AbsorberFromGenerators` | Local decoder normalization removes the coefficient restriction: one sparse host absorbs every leave generated by a given sparse family with any fixed edge multiplicity bound |
| `FiniteGroupGrowth` | Adding a generator outside a finite subgroup at least doubles its cardinality |
| `BoundedGenerators` | Chooses a generating subfamily respecting incidence-load caps, generating every unsaturated element, with size at most the logarithm of the group order |
| `ModularCliqueGenerators` | At most `N*|K|` modular clique generators with bounded face loads generate every unsaturated clique; vectors live on all ambient edges |
| `SaturationCounts` | Double counts bound saturated faces, saturated cliques, and heavy edges; combines modular generation with the saturated-face bound |
| `RootedCliqueExtensions` | Cliques with all edges inside an arbitrary root exempted, and their exact one-vertex extension criterion |
| `RootedCliqueCount` | Exact extension and predecessor counts, with the rooted-clique double count |
| `RootedCliqueBounds` | Iterates upper and lower extension counts with the exact factorial and density exponent |
| `PreciseTypicalCliqueCount` | Two-sided rooted-clique counts in typical graphs with explicit relative error |
| `CliqueCountEstimates` | Normalized clique main terms and relative estimates for total cliques, face roots, and edge roots |
| `GoodCliqueEdges` | Bounds saturated cliques and deleted edges; retains accurate unsaturated-clique counts on good edges |
| `ModularGeneratingData` | Constructs generators, saturated cliques, and a good subgraph with explicit finite bounds |
| `TypicalModularGenerators` | Applies the construction using the precise typical-graph clique counts |
| `AsymptoticCliqueCount` | Discharges collision and counting-error conditions at polynomial density scales |
| `CliqueMeanComparisons` | Relates face and edge main terms and double-counts clique incidence over the host |
| `GoodGeneratorCriterion` | One numerical condition bounds both saturation and edge-deletion fractions and preserves good-edge clique counts |
| `GeneratorCapNumerics` | Controls the integer face cap, its rounding error, and the polynomial parameter inequalities |
| `AsymptoticModularGenerators` | Uniform eventual generator construction for typical graphs with density comparable to a fixed power of `n` |
| `TypicalDensityScales` | Constructs graphs at a prescribed density scale with the exact desired typicality-error exponent |
| `SparseModularGenerators` | Constructs the graph and all modular generating data together, including the Section 6 exponents |
| `CliqueFamilyRelabeling` | Permutations preserve clique counts and boundary bounds; finite nonempty unions satisfy the sum bound |
| `ModularRelabeling` | Transports modular vectors, generated subgroups, and generating data under vertex equivalences |
| `ColouredGenerators` | The permuted union of generators spans all monochromatic unsaturated cliques with a linear bound in the colour count |
| `UniformFiniteFibers` | Exact uniform-input probabilities for finite maps whose fibers have equal size |
| `PermutationBlocks` | Transitivity on blocks and exact probabilities for membership in a uniformly permuted family |
| `GoodSubgraphDensity` | Bounds the density and permutation-probability error caused by deleting a small edge fraction |
| `DisjointFamilyPermutation` | Matches finite disjoint families by a permutation; applies to pairs of sets with matching sizes and intersection |
| `BlockPairOrbits` | Relabeling and transitivity for ordered block pairs with a prescribed intersection, with equal permutation fibers |
| `PermutationPairProbability` | The exact joint law under one permutation is uniform over the appropriate block-pair orbit |
| `BlockPairCounts` | Counts the orbit by choosing the first block, its intersection, and the remaining vertices outside it |
| `BlockPairFamilyBounds` | Bounds a pair family using rooted counts for the second block |
| `PairProbabilityBounds` | Converts the pair-family bound and exact orbit count into a normalized joint-probability estimate |
| `ShiftedChooseBounds` | Explicit relative lower bounds and upper bounds for binomial counts after excluding fixed vertices |
| `TypicalPermutationPairs` | Typicality gives joint clique probability at most `(1+16*ε)*d^(2*choose(q,r))` for intersections smaller than the edge size |
| `AsymptoticPermutationPairs` | Discharges the finite joint-probability conditions uniformly at polynomial density and error scales |
| `IndependentPermutationEvents` | Constructs independent colour permutations and proves exact probabilities of simultaneous coordinate constraints |
| `PermutationEventMoments` | Actual integrable indicator counts, with exact first and second moments; no independence between candidates is assumed |
| `PermutationMomentBounds` | Uniform marginal and joint bounds control the moments, with an additive contribution from exceptional ordered pairs |
| `PermutationCountSuccess` | Chebyshev bounds the lower tail by four times the relative variance bound and yields an actual successful colour assignment |
| `EmbeddingCollisionCounts` | At most `m^2*|T|*n^(m-1)` ordered pairs of extensions collide outside their fixed roots |
| `EmbeddingCollisionGeometry` | Noncolliding extensions intersect exactly in their shared root vertices, including the corresponding block-pair orbit |
| `ExtensionColourMoments` | Exact coloured-extension counts and means, with a second-moment bound from geometric collisions |
| `ExtensionColourCriterion` | A relative second-moment criterion gives failure probability at most `8*ε` |
| `ColourProbabilityNumerics` | Converts marginal and joint errors into powered relative errors uniformly at polynomial scales |
| `ColourCollisionNumerics` | Discharges the collision budget for candidate density `c*n^(-a)` and marginal probability at least `b*n^(-β)` |
| `AsymptoticColouredExtensions` | Uniform polynomial lower-tail bounds and successful assignments for each prescribed root and candidate family |
| `IndependentTrials` | Independent repetitions multiply failure probabilities; a finite union bound supplies a successful trial for every test |
| `AmplificationNumerics` | A fixed trial number defeats any prescribed polynomial number of tests |
| `UniformColouredExtensions` | One fixed finite collection of colour groups works for every injective root map simultaneously |
| `TypicalGoodEdgeColours` | Typicality and a small deleted-edge fraction imply the marginal and joint estimates for permuted good subgraphs |
| `RainbowExtensions` | Rainbow means an injective colour assignment; successful colour groups give actual rainbow embeddings |
| `TypicalRainbowExtensions` | At least `(3/8)*p^M*n^m` rainbow extensions of every root in one finite family of permuted good subgraphs |
| `SparseRainbowGenerators` | Constructs the host, sparse modular generators, good edges, and colours with the simultaneous pattern-extension property |
| `RainbowCliqueCounts` | Bounds the number of embeddings per image by `(q-r)!` and converts embedding counts into distinct punctured-clique counts |
| `RainbowCliqueExistence` | Simultaneous rainbow punctured cliques with conservative constants and the correct factorial divisor |
| `RainbowExchangePlacements` | Actual rainbow copies with a prescribed clique or prescribed pair of cliques; eventual sparse-host constructions for each property |
| `RainbowColourRelabeling` | Adding or injectively renaming colours preserves rainbow witnesses and the corresponding count lower bounds |
| `CombinedRainbowExtensions` | One fixed number of colours supplies all three extension properties, simultaneously over every root |
| `ModularExchangeGeneration` | The exchange identity generates the base modulo any integer when all replacement cliques are generated, including after relabelling |
| `ExchangeFrameStructure` | Near cliques correspond bijectively to base edges, with disjoint private sets and exact frame size; far cliques meet only the base in fewer than `r` vertices |
| `FiniteChoiceSequences` | Exact branch counts for history-dependent finite choices and a product lower bound without independence assumptions |
| `RootedCliqueAvoidance` | A forbidden vertex removes at most `n^(q-r-1)` rooted cliques; a finite union bound preserves half the choices |
| `FrameChoiceSequences` | At least `(L/2)^k` compatible near-clique histories, with prescribed root intersections and disjoint private vertices |
| `ChoiceSequenceAssignments` | Injectively converts histories into indexed assignments while preserving stage properties |
| `FrameAssignments` | The product lower bound counts distinct indexed assignments of cliques from the prescribed rooted families |
| `DisjointPieceEmbeddings` | Glues specified bijections on disjoint pieces into an embedding of their union |
| `RootedPieceEmbeddings` | Preserves the given base injection while matching disjoint private pieces and compatible root images |
| `FrameEmbeddings` | Constructs actual frame embeddings with the prescribed clique images; all full completions preserve them |
| `FrameEmbeddingCount` | Distinct assignments have disjoint completion families, giving `(3/4)*(L/2)^k*n^(v-frameSize)` full embeddings |
| `FrameCountNumerics` | The forbidden-vertex budget is eventually negligible at density exponent below one; verifies the polynomial product identity |
| `AsymptoticFrameCount` | Rooted families of density `c*n^(-γ)` give full pattern candidates of density `(3/4)*(c/2)^k*n^(-γ*k)` |
| `GoodEdgeFrameCounts` | Good-edge relative counts give the needed polynomial lower bound, unchanged by vertex permutations |
| `IndexedNearFrame` | Enumerates the actual near cliques, transports their private-set geometry, and proves the prescribed root-image conditions |
| `NearFrameCandidates` | Constructs polynomially many full exchange embeddings with monochromatic near cliques while fixing only the base |
| `CliqueSubfamilyDensity` | Normalizes total clique counts and controls the marginal loss from deleting a small clique fraction |
| `TypicalCliqueColours` | Polynomial marginal and joint colour estimates for every almost complete clique subfamily of a typical host |
| `ExchangeCliqueCounts` | Bounds the combined candidate and collision exponent by five times the exchange edge count |
| `RainbowNearCandidates` | A uniform candidate family for every base map, with monochromatic near cliques whenever the base is originally rainbow |
| `RainbowExchangeReplacements` | One added finite colour family supplies monochromatic exchange replacements for every original rainbow base |
| `SparseRainbowReplacements` | Discharges the colour experiment at the paper's sparse scale under `α*h ≤ 1/12` |
| `RainbowModularGeneration` | The original and added permuted generators span every originally rainbow clique modulo `N` |
| `SparseRainbowGeneration` | Constructs the host and a sparse enlarged generating family for any prescribed initial palette |
| `RainbowGeneratingSystem` | Combines all three rainbow extension properties with generation of every original rainbow clique |
| `RainbowColourAvoidance` | Repeated colour labels allow every rainbow witness to avoid a bounded set of forbidden labels |
| `RainbowAvoidingExtensions` | All three extension properties persist while avoiding any prescribed bounded set of root colours |
| `AvoidingRainbowGeneratingSystem` | Constructs the sparse generators after duplicating the initial palette, so generation covers its additional rainbow cliques too |
| `Focusing` | Subtracts a supported clique vector to focus every signed input vector on the target graph, preserving integral decomposability |
| `SparseCliqueCover` | Constructs sparse clique covers with separate candidate and input exponents whenever `2*a < b` and `b-a < 1` |
| `SparseFocusingFamily` | One sparse family focuses every integral signed vector supported on the input graph |
| `ColouredFocusingCounts` | Converts the factorial-corrected rainbow count into the polynomial candidate bound needed for focusing |
| `ColouredFocusingFamily` | Constructs a sparse focusing family inside the union of the colour graphs |
| `SparseColouredFocusing` | Proves good-subgraph density and the `n^(-0.7*α)` focusing bound when `ρ ≥ 2*α*choose(q,r)` |
| `CliqueSupportBounds` | A bounded clique boundary bounds its support graph, with no multiplicity assumption |
| `DecoderAugmentation` | Enlarges any sparse family with local decoders, absorbing constants by any fixed loss in the density exponent |
| `DecoderFocusingAssembly` | Joins generators, focusing cliques, and local decoders into one sparse family with uniform signed-vector properties |
| `CliqueResidualGeneration` | Outside-edge reference vectors cancel by incidence double counting, reducing supported generation to clique residual identities |
| `IntegralExchangeGeneration` | Actual integer generation witnesses for replacement and elimination exchanges, including embedded copies |
| `ModularIntegralLift` | Converts modular subgroup membership to an integer boundary and corrects it with local decoders; transports generated integer vectors into modular spans |
| `RainbowPaletteUnion` | Joins rainbow edge families with disjoint colour assignments and inserts an avoided root colour |
| `RootedCliqueBridge` | Finds a clique through a fixed edge whose intersections with two prescribed cliques are exactly that edge |
| `RainbowBridgeExistence` | Constructs a punctured rainbow bridge avoiding both root palettes at polynomial density |
| `RainbowEliminationGeneration` | Elimination exchanges with a rainbow punctured graph generate the difference of their root cliques |
| `RainbowPairGeneration` | Generates differences when the two roots intersect exactly in one edge and are jointly rainbow off it |
| `RainbowPuncturedPairGeneration` | A bridge cancels differences of arbitrary punctured rainbow cliques through the same edge |
| `RainbowReplacementGeometry` | Near cliques have only their designated root edge in the base; far cliques avoid the base |
| `ExchangeNearResidual` | The base boundary minus its near-clique boundaries is generated by far cliques; near roots reindex the base edges exactly |
| `RootColourPalette` | Chooses at most one label per coloured root edge, without an injectivity assumption |
| `RainbowReplacementWitnesses` | Places an exchange with punctured rainbow near cliques, rainbow far cliques, and fully rainbow near cliques at coloured roots |
| `RainbowCliqueResidual` | Proves the generated residual identity for every clique using fixed punctured rainbow references |
| `RainbowIntegralGeneration` | Every integrally decomposable vector supported on the colour graph is generated by rainbow cliques |
| `ModularSupport` | Modular combinations vanish outside their generators; a generated clique over nontrivial coefficients lies in their support |
| `RainbowGeneratorSupport` | Every edge of the colour graph extends to a rainbow clique and lies in the modular generator support |
| `RainbowIntegralLift` | Local decoders convert rainbow generation into exact generation by the sparse enlarged family |
| `SparseIntegralGenerators` | Combines the exchange, rainbow, focusing, and decoding constructions to generate all integral vectors supported on a sparse reserve |
| `IntegralGeneratorExistence` | Constructs the finite pattern and obtains unconditional sparse generation, including all degree-divisible signed vectors |
| `IntegralGeneratorParameters` | Verifies the paper's density scales and constructs an `n^(-0.6*α)`-bounded integral generating family |
| `IntegralGenerationTransitivity` | Substitution of integer clique generators preserves all generated vectors, without coefficient bounds |
| `GeneratorSplitting` | Defines one exchange per generator and proves support, intersection, and integer-span preservation |
| `GeneratorSplittingMultiplicity` | Old-edge multiplicities do not increase; outside edges have multiplicity at most two; each replacement clique meets the old support in at most one edge |
| `GeneratorSplittingBounds` | Bounds the split boundary by the original boundary plus twice the constructed support, without an initial multiplicity bound |
| `GeneratorSplittingExistence` | The ordinary greedy process constructs all splitting copies uniformly for arbitrary sparse input families |
| `SparseGeneratorSplitting` | The initial flattening step preserves the span and all geometric properties, absorbing fixed losses in any density-exponent gap |
| `BoundedMultiplicityCorrection` | Modulus-reduction quotients are bounded by the edge multiplicity; separated local decoders preserve the corresponding coefficient bound |
| `BoundedMultiplicityRepresentation` | Any fixed multiplicity `M` gives uniform representations with coefficient bound `(M+1)*2^q*r!` |
| `GeneratorSplittingIntersections` | Distinct split cliques through the same original edge intersect precisely in that edge |
| `BoundedCliqueGrouping` | Partitions a set of size at most `a*b` into at most `a` nonempty groups of size at most `b`, including corrected square-root grouping |
| `FlatteningRecurrence` | The numerical map `x ↦ max 16 (2*sqrt(x)+4)` reaches 16 under an explicit doubly exponential capacity bound; it does not assert existence of elimination rounds |
| `CliqueMultiplicityBound` | Boundary degree boundedness bounds each edge multiplicity by the same `θ*n` scale |
| `IndependentMeanBound` | Nonnegative independent upper-tail bound with only an upper bound on the mean |
| `IndependentFiniteChoices` | Independent uniform choices from different finite types, with exact coordinate laws and weighted-indicator means |
| `BalancedFiniteChoices` | Simultaneously balanced choices from finite groups by concentration and a union bound |
| `GroupedCliqueCounts` | Disjoint group incidence counts are bounded by the original clique family |
| `BalancedCliqueRepresentatives` | Existing group members can be chosen with weighted face degrees at most twice the original degree scale |
| `AsymptoticBalancedRepresentatives` | The balanced-choice criterion holds uniformly for densities at least n^(-ρ), ρ < 1/2, and groups of size at most sqrt(n)+1 |
| `RootedCliqueGrouping` | Nonempty disjoint groups labelled by unique root edges, with bounded sizes and counts per root |
| `UniformGreedyEmbedding` | Greedy placements uniformly over every density in a fixed polynomial interval |
| `UniformGeneratorSplitting` | Generator splitting uniformly over a polynomial density interval |
| `GroupEliminationIndices` | Each nonrepresentative is indexed exactly once; repeated representative degrees are bounded by weighted choice degrees |
| `GroupEliminationGeneration` | Retaining representatives and eliminating other group members preserves the integer span |
| `CliquePairRootDegrees` | Indexed degree bounds give all prescribed edge-family bounds for elimination roots |
| `UniformEliminationFamily` | Sparse elimination placements from indexed root degrees, without a repetition cap |
| `SharpEliminationCounts` | Root edges occur at most once in a remaining exchange; common root edges disappear |
| `IndexedCliqueDegrees` | Exact boundary-degree identities for indexed clique families, including repetitions |
| `EliminationBoundaryBounds` | A general indexed-root boundary estimate, used for both full and active elimination families with constant loss independent of group size |
| `GroupEliminationCounts` | Removed-clique incidences and retained incidences exactly recover the original count; representative weights cost at most the group size |
| `RootedEliminationMultiplicity` | Grouped elimination adds no old-root edges and yields multiplicity at most max(K, 2m+2) |
| `RootedEliminationReduction` | The grouped replacement family preserves the integer span and has a constant boundary-degree loss |
| `UniformFlatteningRound` | Constructs a full sparse reduction round with multiplicity bound max(16, 2*sqrt(x)+4), uniformly in density |
| `FlatteningIterationCost` | Repeated reduction reaches 16, while every fixed per-round degree cost has subpolynomial total growth |
| `SparseFlattening` | Unconditional sparse flattening to multiplicity 16 with any fixed exponent loss, preserving the integer span |
| `BoundedIntegralGenerators` | Constructs n^(-α/2)-bounded integral generators with multiplicity 16, above a uniform explicit threshold combining the closed generator coefficient and finite flattening |
| `SparseAbsorberExistence` | Unconditional Absorber lemma at a uniform explicit threshold, with the paper’s n^(-α/4) bound and absorption of every divisible reserve subgraph |
| `RealLocalDecoder` | Normalized real decoders with unit boundary, support inside the decoding set, and explicit coefficient bounds |
| `AveragedLocalDecoders` | Averaging preserves the exact decoded edge and dilutes each coefficient by the proportion of decoding sets containing its clique |
| `FractionalDecoderCorrection` | Averaged decoders correct any real edge error exactly and stay inside graph cliques |
| `DecoderAssignmentCounts` | Double counting bounds all decoding assignments affecting a fixed clique |
| `FractionalCorrectionBounds` | Uniform real correction bound from the edge error and the number of decoding sets |
| `NearCompleteCliqueExtensions` | A bounded complement gives a uniform lower bound on every next-vertex clique extension count |
| `NearCompleteCliqueCounts` | Finite rooted-clique count bounds with exact factorial normalization and a numerical relative-error criterion |
| `AsymptoticNearCompleteCliques` | Polynomially sparse complements give uniformly accurate rooted-clique and decoding-set counts |
| `FiniteFractionalBoost` | An explicit finite criterion yields valid clique probabilities with exactly equal edge means |
| `FractionalBoostNumerics` | All ambient-size factors cancel in the coefficient error, leaving a fixed constant times the relative counting error |
| `FractionalBoostExistence` | Constructs valid fractional regularization for every sufficiently large graph with polynomially sparse complement |
| `IndependentBernoulliChoices` | Independent indicators with distinct probabilities, exact means, and finite count identities |
| `FiniteCountSampling` | A union bound produces an actual finite subset satisfying all prescribed count estimates |
| `FractionalCliqueSampling` | Samples only graph cliques and converts the fractional boundary to simultaneous actual edge counts |
| `CliqueSamplingNumerics` | The sampling failure bound tends to zero at every relative exponent below one half |
| `RegularCliqueFamily` | Constructs the actual regular clique family with the power-scale edge count |
| `RegularityBoost` | The boost needed for eventual existence: binomial edge counts with n^(-1/3) relative error, for polynomially sparse complements |
| `VarianceExponentialBound` | Quadratic exponential bound for signed increments and the exact variance-sensitive Chernoff parameters |
| `ConditionalVarianceExponential` | Conditional exponential estimates compensated by second moments, including all integrability requirements |
| `ConditionalVarianceCompensation` | Conditional one-step supermartingale bound with a bounded predictable nonnegative weight |
| `VarianceExponentialProcess` | Strong adaptation, integrability, uniform bounds, and the exponential supermartingale |
| `SupermartingaleMaximal` | Finite-horizon Ville inequality from bounded optional stopping |
| `FreedmanSecondMoment` | Uniform tail bound with predictable second moments and stronger denominator 2v+ab |
| `ConditionalCentering` | Correct centered-increment bound 2b and invariance of conditional variance under predictable translations |
| `FreedmanConditionalVariance` | Conditional-variance concentration with denominator 2(v+ab), including nonpositive conditional means |
| `FreedmanFiniteIncrements` | The same concentration theorem with assumptions only before the finite horizon |
| `Freedman` | The paper's finite martingale lemma and its supermartingale extension with the printed constants |
| `PredictableIndicatorVariance` | Predictable switching preserves conditional moments on the active event and cannot increase conditional variance |
| `StoppedIncrementConcentration` | Freedman with drift assumed only where an increment is retained |
| `CriticalWindowProcess` | Measurable interval-stopping events and exact telescoping along a surviving trajectory |
| `CriticalWindowEntrance` | The last entrance before a crossing, including the one-step overshoot bound |
| `CriticalWindowAttempt` | The explicit concentration bound for one attempted interval crossing |
| `CriticalWindowConcentration` | Local-drift crossing bound with the finite union over start times |
| `SimultaneousCriticalWindows` | First-failure argument, simultaneous probability bound, and existence criterion for good trajectories |
| `ConditionalVarianceBounds` | Conditional variance bounded by b times the conditional absolute mean, and by b squared |
| `FiniteUnionOverlap` | Explicit multiple-counting error for a finite union with bounded pair intersections |
| `CliqueCodegree` | Common clique degree of distinct r-edges is at most n^(q-r-1) |
| `CliqueRemovalCounts` | Exact one-step removal, union-of-neighborhoods identity, and explicit overlap error |
| `CliqueRemovalDrift` | Double counting and bounds for average total clique loss in terms of squared edge degrees |
| `CliqueEdgeRemoval` | Exact edge-degree partition and the small change bound when the tracked edge survives |
| `FiniteHistoryStep` | Fixed initial history, integrability, and conditional transition means for functions of the whole history |
| `RemainingCliques` | Available clique family, exact update, and identification with cliques in the remaining graph |
| `CliqueRemovalProcess` | Actual uniform random removal process and exact support of legal choices |
| `UniformCliqueStep` | Exact finite uniform averages and conditional means of history-dependent clique increments |
| `CliqueRemovalPacking` | Supported trajectories are true packings; exact clique and edge counts whenever choices remain available |
| `FrozenEdgeLoss` | Exact loss of a frozen edge degree, small step bound, and double counting |
| `ExcludedEdgeNeighborhood` | Root exclusion, degree partition, and overlap error for cliques avoiding the tracked edge |
| `FrozenEdgeDrift` | Total and average frozen edge loss with explicit overlap error |
| `FrozenEdgeDegreeBounds` | Frozen edge loss under upper and lower bounds for all covered edge degrees |
| `FrozenTrackingIncrement` | Frozen comparison increments, exact survival factor, and absolute moment bounds |
| `FiniteHistoryMeasurability` | Measurability and integrability for arbitrary functions of finite histories |
| `FrozenEdgeProcess` | Actual adapted frozen edge process with bounded increments and permanent freezing |
| `FrozenEdgeConditionalDrift` | Exact conditional drift and absolute first moments for the frozen edge process |
| `FrozenEdgeConditionalVariance` | Conditional variance bounds for the actual frozen process |
| `FrozenEdgeValue` | Exact tracked degree while alive and freezing on the removal step itself |
| `FrozenEdgeControlledMoments` | Conditional drift and variance estimates under current edge-degree bounds |
| `FiniteSquaredDeviation` | Finite variance about the actual mean is bounded by squared deviations from any comparison value |
| `CliqueSquaredDegrees` | Exact sum of clique degrees and squared-degree bounds on a graph containing the clique family |
| `CliqueCountLossBounds` | Explicit total clique loss bounds from current degree errors and initial maximum degrees |
| `CliqueCountProcess` | Actual adapted clique-count process, exact updates on every trajectory, and bounded increments |
| `CliqueCountConditionalDrift` | Exact conditional clique-count drift and its bounds from current degree control |
| `CliqueCountVariance` | Conditional variance and finite-horizon variance budget for clique-count increments |
| `CliqueFaceLoss` | Exact face loss, small change bound, and double counting over a clique family |
| `FaceLossDrift` | Average face-degree loss from bounds on current clique degrees |
| `FaceCountProcess` | Actual adapted face-degree process with exact graph update and bounded increments |
| `FaceCountConditionalDrift` | Exact conditional face-degree drift and bounds from current clique degrees |
| `PredictableLossVariance` | Predictable comparison terms do not affect variance; bounded nonnegative losses give sharper bounds |
| `FaceCountVariance` | Face-degree variance bounded by the average actual loss, without a comparison-error term |
| `DiscretePowerBounds` | Explicit first-order power differences and a finite-step quadratic remainder |
| `DiscreteReciprocalBounds` | Explicit reciprocal and reciprocal-square differences when consecutive densities are comparable |
| `RemovalDensity` | Deterministic remaining density, monotonicity, horizon lower bounds, and exact edge scaling |
| `ComparisonIncrementBounds` | Upper and lower increments for power main terms with reciprocal comparison errors |
| `RatioPerturbation` | Explicit quotient errors when a positive denominator stays within half its main term |
| `EdgeNumeratorBounds` | Cancellation of first-order degree errors in the two edge critical intervals |
| `QuadraticRatioBound` | Quadratic drift main terms with explicit numerator and denominator errors |
| `EdgeCriticalDrift` | Numerical upper and lower frozen-edge drift criteria retaining the survival correction |
| `FrozenEdgeCriticalTrend` | Critical-interval drift criteria applied to the actual frozen edge process |
| `CliqueRemovalAvailability` | Current availability implies no previous abort on supported paths, exact density, and live tracked values |
| `NibbleComparisons` | Concrete reciprocal comparison functions and their main-term ratio identities |
| `NibbleDegreeScaleBounds` | Degree-error and critical-width bounds from the scalar smallness conditions |
| `NibbleCliqueScaleBounds` | Clique-count error bounds and positivity of the lower comparison |
| `NibbleEdgeIncrements` | Explicit finite increments of the concrete upper and lower edge comparisons |
| `NibbleEdgeRemainders` | Uniform bounds on the Taylor remainder and comparison-error growth |
| `NibbleSurvivalError` | Explicit control of the survival correction for the lower edge comparison |
| `NibbleEdgeStepControl` | Concrete edge comparison increments meet both critical-interval drift requirements |
| `NibbleComparisonParameters` | Uniform scalar parameter conditions above a fixed stopping density |
| `AsymptoticNibbleParameters` | Eventual construction of the scalar conditions from polynomial graph and degree lower bounds |
| `NibbleBinomialScales` | Polynomial lower bounds for binomial density scales and clique size at least three |
| `NibblePaperComparisonParameters` | Eventual comparison parameters at the paper’s binomial density, degree, and stopping scales |
| `CliqueCountCriticalDrift` | Numerical upper and lower count drift criteria, including the degree-variance error |
| `NibbleCliqueIncrements` | First-order, remainder, and reciprocal-square increments of count comparisons |
| `NibbleCountConditions` | Additional count overlap, variance, and step conditions with proved critical margins |
| `NibbleCliqueRemainders` | Count Taylor remainders and uniform slope and error bounds |
| `NibbleCliqueStepControl` | Count comparison drift directions and absolute step bounds |
| `AsymptoticNibbleCountConditions` | Eventual count conditions from polynomial lower bounds |
| `NibblePaperCountConditions` | Joint edge and count conditions at the paper’s density scales for epsilon below 2/3 |
| `NibbleCliqueDrift` | Concrete upper and lower clique-count drift inequalities |
| `NibbleComparisonSequences` | Deterministic comparisons at successive removal times |
| `NibbleCliqueCountTrend` | Both count drift signs under the actual trajectory law |
| `FaceCriticalDrift` | Face critical-interval margin absorbs relative degree and count errors |
| `NibbleFaceComparisons` | Linear face comparison, constant error envelope, and concrete drift |
| `NibbleFaceTrend` | Upper face drift for the actual removal process |
| `NibbleFaceLossBound` | Uniform average face loss before a comparison fails |
| `NibbleFaceVariance` | Concrete face variance and global absolute increment bounds |
| `NibbleEdgeSequenceSteps` | Concrete frozen-edge step criteria along the removal clock |
| `NibbleEdgeTrend` | Both frozen-edge drift signs, including already removed edges |
| `NibbleTrackedProcess` | One adapted finite family of count, edge, and face tracks and a measurable good event |
| `NibbleGoodState` | The common good event implies current availability and actual degree bounds |
| `NibbleGoodTrend` | Every track has nonpositive critical drift under the common good event |
| `NibbleEdgeLossBound` | Uniform edge slope, average loss, and increment scales |
| `NibbleEdgeVariance` | Frozen-edge increment and conditional variance bounds under the common good event |
| `NibbleControlScales` | Positive global step scales and nonnegative variance rates for every track |
| `NibbleTrackedBoundedness` | Global increment bounds for all tracks and exact process differences |
| `NibbleVarianceBudget` | Uniform conditional variance rates and budgets before the first good-event failure |
| `NibbleCriticalControl` | Actual critical-window controller and explicit simultaneous failure probability |
| `NibblePackingCriterion` | Supported good paths and genuine bounded-leave packings under explicit numerical conditions |
| `InitialCliqueCount` | Initial clique-count accuracy from degree accuracy by double counting |
| `NibbleInitialBounds` | The initial regularity assumption puts every track below its critical interval |
| `RegularNibbleCriterion` | Numerical packing criterion using only the paper's initial degree regularity |
| `NibbleHorizon` | Rounded stopping time, density interval, run-length bound, and final face density |
| `NibbleHalfWidths` | Count, edge, and face increments fit inside half their critical widths |
| `NibbleEndConditions` | Scalar end conditions discharge every gap and final-density condition |
| `AsymptoticNibbleEndConditions` | End conditions hold eventually under polynomial graph density |
| `NibblePaperEndConditions` | All comparison and end conditions at the paper's binomial density scales |
| `CriticalExponentLowerBound` | Critical-window exponent bound from a half-width gap and variance budget |
| `NibbleExponentScales` | Explicit count, edge, and face concentration exponent scales |
| `NibbleTrackExponents` | Exponent lower bounds for the actual tracked processes |
| `NibbleFailurePrefactor` | Polynomial bounds on the number of tracks and steps |
| `NibbleExponentConditions` | Scalar margins imply one common concentration exponent |
| `AsymptoticNibbleExponents` | Those exponent margins hold eventually from polynomial density bounds |
| `NibbleUniformExponent` | A single lower exponent controls the whole failure estimate |
| `NibblePaperExponents` | Common exponent n^(1/3-2*epsilon/3) at the paper's density scales |
| `NibbleTailDecay` | The polynomial union bound times the negative exponential is eventually below one |
| `AsymptoticNibble` | Unconditional eventual packing with 3*n^(-epsilon/(3*k))-bounded leave |
| `NibblePaperParameters` | Unconditional eventual nibble with the paper's n^(-3*k*rho)-bounded leave |
| `NearCompleteDensity` | A polynomially bounded complement eventually leaves more than half the edges |
| `DesignCompletion` | Exact assembly of a packing, reserve cover, and absorber into a design |
| `HigherRankDesignExistence` | Complete designs in rank at least two above the uniform explicit generator/flattening threshold |
| `RankOneDesign` | Explicit partition construction for rank-one designs and transport by equivalences |
| `DesignExistence` | Full Theorem 1.1 with a uniform explicit corrected threshold for every q > r ≥ 1, also in the numerical divisibility formulation |
| `ConstantComplementCliqueCounts` | Uniform rooted clique counts for a fixed complement bound and relative error |
| `FractionalBoostFromCounts` | Shared finite fractional-boost criterion from relative clique and decoder counts |
| `ConstantComplementFractionalBoost` | A fixed positive complement bound suffices for valid regularizing probabilities |
| `ConstantComplementBoost` | Boost at the printed complement constant 2^(-3q), with binomial normalization and relative n^(-1/3) error |
| `DenseNibbleScalars` | All four scalar nibble records at graph-size exponent at least one |
| `DenseNibbleParameters` | Constant-density binomial parameters, including rank one when k ≥ 3 |
| `DenseNibble` | Actual eventual packing at constant graph density in every positive rank with k ≥ 3 |
| `MaximumVertexPacking` | Maximum vertex-disjoint block families, support counts, and rank-one decompositions |
| `PairPackingAugmentation` | A maximum matching admits no one-to-two replacement or crossing augmenting pairs |
| `PairNeighbors` | Pair neighbor sets, exact incident-edge counts, and decomposition over matched pairs |
| `PairMatchingCounts` | Minimum degree delta implies a matching leaving at most max(1, |S|-2*delta) vertices |
| `RankOneVertices` | Rank-one graphs identified with vertex sets, preserving differences, cardinality, and boundedness |
| `RankOnePairPacking` | The finite matching bound in the paper's hypergraph decomposition notation |
| `RankOnePairNibble` | Pair-case nibble with every fixed leave exponent beta < 1/3 |
| `NormalizedChooseMonotonicity` | Binomial coefficients divided by n^alpha are monotone for alpha ≤ 1 and positive rank |
| `GraphEmbeddingPullback` | Exact pullback of supported clique families and preservation of clique supports |
| `RankOneRestriction` | A rank-one graph is the embedded complete graph on its own vertices; supported clique families restrict exactly |
| `RankOneRestrictionScales` | Restriction preserves the lower clique-degree scale, relative error, and leave bound |
| `SparseRankOneNibble` | General sparse rank-one nibble for q ≥ 3 via restriction to the actual vertices |
| `NibbleNonPairRanks` | General eventual nibble in every positive rank whenever q ≥ 3 |
| `PartialHall` | Hall's theorem with an allowed number of unmatched indices, using dummy targets |
| `VariableCountSampling` | Simultaneous Bernoulli count concentration with different means for each test |
| `DegreeHallBounds` | Minimum and maximum degrees give a quantitative partial transversal |
| `BalancedSubsetCounts` | A subset balances all specified counts around one half of their sizes |
| `BalancedPairPartition` | A random bipartition balances the vertex set and every pair neighborhood |
| `PairFamilyFromInjections` | Two disjoint injective vertex maps give a vertex-disjoint pair family |
| `BipartitePairMatching` | Degree bounds across a partition give a packing with an explicit uncovered count |
| `BalancedDegreeBounds` | Balanced subset and complement counts inherit nearly equal degree bounds |
| `NearRegularPairPacking` | Near-regular pair families have a packing leaving at most 9*c*|S|+2 vertices |
| `PairNibbleNumerics` | The source's pair-degree and error scales satisfy the matching criterion |
| `GeneralPairNibble` | The general pair nibble, including clique degrees at the minimum n^(2/3) scale |
| `AllRanksNibble` | General eventual nibble in every positive rank for all epsilon < 1/2 |
| `DecoderCoefficient` | Closed form for the alternating coefficient sum in Wilson's local decoder |
| `ExactLocalDecoder` | Decoder coefficients and their absolute values as functions of the root-clique intersection |
| `ContainedBlockIntersections` | Exact count of contained blocks with a prescribed number of vertices outside a subset |
| `DecoderMassBound` | Total absolute integer decoder mass at most 2^r times the decoder multiplier |
| `RealDecoderMass` | Normalized decoder mass at most 2^r, including the assignment double count |
| `SharpFractionalCorrection` | Correction bounds and valid sampling probabilities from total decoder mass |
| `RootedCliqueAdditiveLoss` | Clique-count iteration with additive extension losses and their binomial sum |
| `SharpComplementCliques` | Complement loss depends on choose(q,r), rather than a repeated worst-step bound |
| `FractionalBoostMassNumerics` | Size-independent correction cost 2^r*choose(q,r) times the relative count error |
| `FractionalBoostCountBounds` | Shared construction of decoding families from relative clique counts |
| `PaperBoostParameters` | All numerical margins at the printed complement constant 2^(-3q) |
| `SharpFractionalBoostFromCounts` | Fractional regularization under the improved correction budget |
| `PaperFractionalBoost` | Exact common fractional edge means with complement bounded by 2^(-3q) |
| `BernoulliPatterns` | Exact probabilities for arbitrary prescribed present and absent coordinates |
| `IsolatedVertexTypicality` | A nonempty graph with an isolated vertex is not typical with error below one |
| `TypicalityFailureLower` | Typicality failure has probability at least p*(1-p)^(n-1) |
| `TypicalityCounterexampleNumerics` | Explicit parameters meet Lemma 5.3 while violating the printed exponential rate |
| `PrintedWhpCounterexample` | For all n >= 1000000, p=1/100 refutes the printed whp conclusion of Lemma 5.3 |
| `TypicalityHighProbability` | Corrected eventual typicality with failure probability below exp(-n^(1/10)) |
| `TwoTermCancellation` | Odd transformations preserve zero sums of at most two integers; signed magnitude-level reconstruction |
| `MagnitudeLevelBoundary` | Multiplicity-two boundaries preserve their support under signed magnitude levels |
| `MultiplicityTwoObstruction` | A multiplicity-two family cannot generate a nonzero single-edge vector when choose(q,r)>2 |
| `MultiplicityTwoCounterexample` | Nonempty reserves and all cliques on q+r vertices obstruct multiplicity-two generation |
| `SmallSupportBoundedness` | Singleton graph and finite clique-family degree bounds |
| `SmallSupportAsymptotics` | Every fixed support meets all sublinear power boundedness scales eventually |
| `SparseMultiplicityTwoCounterexamples` | Sparse reserves and sparse clique families refute multiplicity two at arbitrarily large sizes |
| `PrintedMultiplicityTwoCounterexamples` | Counterexamples to Lemmas 6.1 and 6.5 at their printed input density parameters |
| `GreedySuccessProbability` | Measurable events for actual bounded greedy families and explicit finite success probabilities |
| `StretchedExponentialTail` | Polynomial prefactors are absorbed by every smaller stretched-exponential exponent |
| `PrescribedGreedySuccessProbability` | Finite success probabilities include actual history-dependent candidate membership |
| `GreedyHighProbabilityNumerics` | Explicit conservative density bound and uniform stretched-exponential failure estimates |
| `GreedyHighProbability` | Uniform high-probability construction when theta is at least n^(-rho) |
| `PrescribedGreedyHighProbability` | High-probability construction at separate candidate, root, and forbidden density scales |
| `FiniteHistoryProbability` | Exact finite-history probabilities and agreement when transitions agree along an event |
| `FiniteHistoryAgreement` | Transfer of event probabilities between processes agreeing along all relevant finite prefixes |
| `UnstoppedGreedyProcess` | Removes degree stopping exactly and proves corrected Lemma 5.5 for the ordinary greedy algorithm |
| `UnstoppedPrescribedGreedyProcess` | The same exact transfer and success probability for ordinary history-dependent candidate sampling |
| `PaperSizeParameters` | The printed integer threshold, exact alpha normalization, and basic parameter bounds |
| `PaperParameterMargins` | Configuration cost at most 1/12, colour-count bound, and the strict higher-rank density margin |
| `PaperFlatteningThreshold` | The explicit Section 10 inequality n0>(2^(5q)*(4q)^r*u)^(10/alpha) |
| `PaperThresholdDensity` | Finite polynomial density bounds above n0, including the combined reserve and absorber budget |
| `FiniteComplementDensity` | Double-counted face degrees give finite edge density bounds without asymptotic clique estimates |
| `PaperThresholdAssembly` | Above n0, the remaining host meets the printed boost complement bound and has density above one half |
| `PaperThresholdLog` | Exact log(n0), explicit rank-dependent bound, and the fixed-rank big-O statement |
| `ExplicitBoostSize` | The smaller Boost threshold (4q)^(90q), power lower bounds, and factorial domination |
| `ExplicitBoostParameters` | Finite rooted-clique count margins, including decoding loss at most one quarter |
| `ExplicitFractionalBoost` | Exact fractional regularization above the explicit Boost threshold |
| `ExplicitBoostTail` | The finite bound 6*n^r*exp(-n^(1/10)/12)<1 at the Boost threshold |
| `FiniteCliqueSamplingNumerics` | Shared finite concentration criterion used by explicit and eventual clique sampling |
| `ExplicitCliqueSampling` | The actual sampling criterion holds above (4q)^(90q) |
| `ExplicitBoostBinomial` | Finite binomial approximation and conversion from n^(-2/5) to n^(-1/3) error |
| `ExplicitRegularityBoost` | Full Lemma 2.3 at the printed threshold, already valid at the smaller (4q)^(90q) bound |
| `PaperReserveGrowth` | Exact n0^rho normalization, large reciprocal reserve density, and rho*choose(q,r) <= 1/36 |
| `ReserveThresholdConstants` | Fixed normalization, extension-count, size, and probability losses dominated by the printed threshold |
| `ExplicitReserveNumerics` | Finite typicality normalization and punctured-clique counting conditions at n0 |
| `ExplicitReserveTail` | The simultaneous reserve sampling tail is strictly below one at n0 |
| `ExplicitReserveTypicality` | Constructs a typical graph at the reserve's finite density and error scales |
| `ExplicitReserve` | Full Lemma 2.1 at n0, with strict n^(-rho) boundedness and extension counts at every edge |
| `ExplicitCoverSmallness` | The prescribed greedy cover's density condition holds at n0 |
| `ExplicitCoverTail` | The prescribed greedy cover's simultaneous failure bound is below one at n0 |
| `ExplicitCliqueCover` | Full Lemma 2.5 at n0, with actual disjoint covering cliques and only the necessary extension counts |
| `ExplicitReserveCover` | Constructs one sparse reserve covering every sufficiently bounded disjoint leave at n0 |
| `ExplicitNibbleGrowth` | A common explicit constant bound for all nibble comparison and concentration conditions |
| `ExplicitNibbleMargins` | Converts finite coefficient bounds and density lower bounds into power margins; proves the stopping-exponent gaps |
| `ExplicitNibbleComparison` | Every comparison condition holds at n0 for a=n^(-1/9) and the paper's stopping density |
| `ExplicitNibbleEnd` | All clique-count and stopping conditions hold at n0 |
| `ExplicitNibbleFaceMargin` | Explicit face-concentration coefficient bound, including the reciprocal graph-density constant |
| `ExplicitNibbleExponents` | Every tracked concentration exponent is at least n^(1/6) at n0 |
| `ExplicitNibbleBinomial` | Finite binomial lower bounds and absorption of the factor three in the leave bound |
| `ExplicitNibbleTail` | The finite simultaneous tail 5*n^(2*r)*exp(-n^(1/6)) is below one at n0 |
| `ExplicitNibbleParameters` | Constructs all four numerical records from the paper's initial density and degree scale |
| `ExplicitNibble` | Actual finite nibble packing at n0 whenever a clique has at least three edges |
| `ExplicitPairNibble` | Finite maximum-matching proof of the q=2, r=1 case at n0 |
| `ExplicitAllRanksNibble` | Full Lemma 2.4 at the printed threshold in every positive rank |
| `PaperAlphaGrowth` | Finite growth at arbitrary nonnegative multiples of alpha; in particular (4q)^(30q) <= n^(alpha/3) |
| `ExplicitAbsorberGreedyTail` | Finite greedy failure probability below one whenever the pattern has at most n edges and density is at least n^(-1/2) |
| `ExplicitAbsorberGreedyNumerics` | All finite placement conditions at density A*n^(-alpha/3), for pattern sizes and A at most (4q)^(8q) |
| `ExplicitAbsorberGreedy` | Actual disjoint bounded greedy embeddings at n0 under those explicit pattern bounds |
| `ExplicitDecoderPlacement` | All clique patterns on at most 2q vertices satisfy the finite bounds; constructs disjoint rooted placements at n0 |
| `ExplicitLocalDecoders` | Finite sparse local decoder families, with exact decoder multipliers and bounded edge multiplicity |
| `ExplicitBoundedRepresentation` | One finite decoder family gives uniformly bounded integer representations for every generated leave |
| `ExplicitSeparatedGreedyNumerics` | Finite candidate, smallness, and probability conditions with prescribed free-vertex separation |
| `ExplicitSeparatedGreedy` | Actual bounded placements with disjoint free vertices for related roots, at n0 |
| `ExplicitSplittingPlacements` | Finite placements on repeated clique roots, including all required free-vertex separation |
| `ExplicitSplittingFamily` | Finite signed-slot splitting families under explicit pattern, conflict, and density bounds |
| `AbsorberWorkingParameters` | Coefficient cap, multiplicity, normalized density, and conflict bounds for multiplicity-16 generators |
| `NormalizedSplitting` | All splitting constants fit n0 at the normalized parameters; the exchange carrier size is still an explicit hypothesis |
| `FiniteDecoderSplitting` | Connects finite decoders and bounded representations to splitting; also constructs the exchange carrier with its proved size bound |
| `SmallCarrierExchange` | Actual exchange and cancellation patterns with at most `(4*q)^(2*q)` vertices |
| `SmallPatternGreedyNumerics` | Finite separated placement numerics for patterns of size `(4*q)^(2*q)` and density constants up to `(4*q)^(24*q)` |
| `SmallPatternGreedy` | Actual ordinary and separated embeddings for every working exponent between alpha/3 and 1/2 |
| `ExplicitEliminationPlacements` | Actual cancellation placements on prescribed clique pairs at n0, under explicit density constants |
| `ExplicitEliminationFamily` | Finite cancellation families on arbitrary finite index types |
| `ExplicitEliminationStages` | Both finite cancellation stages and the decomposable negative host under two explicit scalar bounds |
| `AbsorberCoefficientBounds` | Accumulated multiplicity-16 absorber coefficient at most `(4*q)^(22*q)`; both cancellation densities fit even after doubling |
| `AbsorberFactorBounds` | Transfers the integer coefficient bounds to actual exchange configurations and proves the final n^(-alpha/4) density at n0 |
| `NormalizedElimination` | Discharges both cancellation constants and constructs the finite negative host from splitting at exponent alpha/2 |
| `FlexibleDecoderPlacement` | Finite disjoint decoder regions at every exponent from alpha/3 to 1/2, retaining the 4*R! constant |
| `FlexibleLocalDecoders` | Local decoder families and bounded representations at flexible exponents and density coefficients |
| `FlexibleSplittingPlacements` | Actual separated placements of repeated splitting roots at flexible exponents |
| `FlexibleSplittingFamily` | Finite signed-slot splitting families with the sharper small-pattern numerical bounds |
| `HalfAlphaSplitting` | Normalized splitting at alpha/2, including the initial factor two and all multiplicity-16 constants |
| `HalfAlphaDecoderFamily` | Actual decoder augmentation, normalized support and clique degrees, bounded multiplicity, and uniform representations at alpha/2 |
| `HalfAlphaSignedAbsorber` | Constructs all patterns and placements for a finite host absorbing every normalized bounded representation |
| `FiniteAbsorberFromGenerators` | Full finite absorber from a supplied sparse multiplicity-16 integral generating family, with the final n^(-alpha/4) bound |
| `FlatteningCostObstruction` | For triangles at n0, every stopping iteration costs more than the available n^(alpha/10) budget under the current uniform round estimate |
| `FiniteFlatteningIterations` | A finite logarithmic cost criterion and a conservative explicit threshold for all multiplicity-reduction iterations |
| `FiniteUniformGreedy` | Actual finite embeddings uniformly for densities between n^(-1/2) and (4q)^(24q)*n^(-alpha/3) |
| `FiniteGeneratorSplitting` | Actual generator splitting at n0 throughout that uniform density range |
| `FiniteUniformElimination` | Actual finite elimination families from indexed root degrees; the same placements simultaneously bound every subpattern by its new-edge count |
| `ExplicitBalancedRepresentatives` | Actual balanced representatives for groups of size at most sqrt(n)+1 at n0 |
| `FlatteningRoundConstants` | Explicit universal round coefficient and the required bound on intermediate placement densities |
| `FiniteFlatteningRound` | One complete multiplicity-reduction round at n0, preserving the full integer span |
| `FiniteSparseFlattening` | Actual multiplicity-16 flattening from n^(-3alpha/5) to n^(-alpha/2) above an explicit valid threshold |
| `FinitePaperFlattening` | The full printed input coefficient is accepted by the corrected finite construction; its chosen threshold is provably larger than n0 for triangles |

| `FiniteGoodDensity` | At n0, every good-density power through choose(q,R) is at least half its reference power; the loss is not exponential in choose(q,R) |
| `FocusingParameters` | Explicit focusing exponent margins and factorial domination at n0, including rank one |
| `FiniteFocusingCounts` | The observed-density rainbow count supplies the required polynomial number of focusing candidates at n0 |
| `FiniteFocusingNumerics` | Finite prescribed-greedy smallness, failure probability below one, and the final n^(-7alpha/10) focusing bound |
| `FiniteFocusingFamily` | Constructs actual sparse clique covers and one focusing family for all supported integral vectors at n0 |
| `FiniteDecoderAugmentation` | Actual decoder augmentation at flexible exponents; an input coefficient at most (4q)^(6q) fits half the n^(-3alpha/5) output budget at n0 |
| `FiniteGeneratorAssemblyThreshold` | An explicit threshold absorbs any fixed input coefficient while leaving enough density margin for decoders |
| `FiniteDecoderFocusing` | Combines focusing and decoding at n0 under a coefficient cap, or above an explicit threshold for arbitrary coefficients |
| `FiniteRainbowIntegralGeneration` | Actual bridges avoiding two prescribed cliques, pair differences, and integral generation on the colour graph at n0 |
| `FiniteIntegralGeneratorsFromSystem` | Finite integral generators from an actual coloured modular system; constructs all focusing, decoder, bridge, and lifting steps |
| `PaperIntegralGeneratorExistence` | Constructs the full colour system at n0 and the integral generating family at an explicit coefficient-dependent threshold, subsequently bounded uniformly in q and r |

| `FiniteGeneratorCap` | At n0 the actual decoder modulus satisfies the rounded face-cap, strict generator-degree, and saturation budgets |
| `FiniteModularHostNumerics` | Observed-density bounds and the rooted-clique collision budget hold at n0 without an exponential density-power loss |
| `FiniteModularGenerators` | Constructs sparse modular generators in a supplied typical host at n0, including small saturation/deletion fractions and accurate good-edge clique counts |
| `FiniteTypicalHostNumerics` | The full exchange-size typicality factor and simultaneous sampling tail fit n0 |
| `FiniteTypicalHost` | Constructs a typical host through any h up to the exchange edge bound, with the paper's n^(-1/10) typicality and density error |
| `FiniteSparseModularGenerators` | Constructs both the typical host and the full sparse modular generating data at n0 for the decoder modulus |
| `PaperRainbowGeneratingSystem` | Constructs the complete modular colour system at n0, including extension and replacement palettes and prescribed-colour avoidance |

| `LinearColourPowers` | Small joint-probability errors accumulate linearly in the pattern edge count; the finite powered estimate fits n0 |
| `FiniteColourTrials` | Explicit trial count 48*(rootSize+1)*inverseAlpha, with failure at most n^(-1) for all root maps and at most n^(-2) for nonempty roots at n0 |
| `FinitePermutationPairNumerics` | Finite shifted-binomial lower bounds and clique-count error margins for joint permutation probabilities |
| `FinitePermutationPairs` | Joint probabilities for any two permuted clique subfamilies of size at most q, with error 16*n^(-alpha/6), at n0 |
| `FiniteGoodEdgeColours` | Good-edge marginal probabilities and joint probabilities with relative error n^(-alpha/12) at n0 |
| `FiniteColourCollisions` | Geometric collision contribution is at most n^(-alpha/24) of the squared mean at the exchange size bounds |
| `FiniteColouredExtensions` | Finite lower-tail probability and actual independent colour trials succeeding for every root simultaneously |
| `FiniteRainbowExtensions` | Constructs one explicit-size palette with the required number of rainbow embeddings for every root at n0 |

| `FiniteRainbowRootPatterns` | Actual finite palettes for punctured cliques and the one- and two-clique exchange roots at n0 |
| `FiniteCombinedRainbowExtensions` | Combines the three root-pattern palettes with an explicit total colour count at n0 |
| `FiniteCliqueColours` | Finite total clique count, unsaturated-clique marginal density, and joint clique-colour probabilities at n0 |
| `FiniteNearFrameNumerics` | Bounds the near-frame factorial and collision costs, absorbing its density coefficient into n^(-1/40) |
| `FiniteNearFrameCandidates` | Actual near-frame candidates for every rainbow base at n0, including all compatible completions |
| `FiniteRainbowReplacements` | Far-clique trials give exchange replacements and modular generation for every original rainbow clique, uniformly with failure at most n^(-2) at n0 |

| `FiniteGeneratorCoefficient` | Bounds the combined palette and complete generator coefficient uniformly in q and r; supplies a closed integral-assembly threshold |
| `FiniteIntegralGeneratorExistence` | Preserves the earlier uniform-threshold interface using the stronger unconditional construction at n0 |

| `FiniteSparseNibbleMargins` | Exact ε cutoff and finite binomial lower bounds for the polynomially sparse densities in Section 9 |
| `FiniteSparseNibbleComparison` | Finite comparison parameters with variable ε, sparse clique density, and graph size at least n^(19/20)/(4r!) |
| `FiniteSparseNibbleEnd` | Finite clique-count and stopping conditions over the same variable-error range |
| `FiniteSparseNibbleExponents` | Common n^(1/10) concentration exponent with a graph coefficient allowed to depend on n |
| `FiniteSparsePairNibble` | Finite sampling and leave bounds for the general near-regular pair construction |
| `FiniteSparseNibble` | Finite packing from separate floor and density conditions; every ε ≤ 2/5 for pairs, and 1/(12k) ≤ ε ≤ 2/5 in all ranks |
| `FiniteNibbleFloors` | Five floor conditions from polynomial-versus-power bounds; p ≤ 1/3 for k ≥ 15, and p ≤ 1/432 for every k ≥ 3 |
| `FiniteGeneralNibble` | Lemma 9.1 at n0 for every ε ≤ 2/5 with constant 432; original constant 3 in the pair, large-clique, nonpositive-error, and previous cutoff ranges |
| `FiniteTypicalityThreshold` | Closed corrected typicality threshold; it lies below n0 through the exchange size, and absorbs the full probability prefactor |
| `FiniteTypicalityProbability` | Corrected Lemma 5.3 with explicit threshold and failure below exp(-n^(1/10)); density and typicality hold simultaneously, including at n0 through the exchange size |
| `ModularGeneratorsProbability` | Both observed-density and exact reference-density KSG bounds hold with probability greater than 1-exp(-n^(1/10)) at n0, for the decoder-modulus range |
| `FiniteModularErrorBudget` | Finite cap and clique-count conditions with one quarter of the final relative-error allowance, without increasing n0 |
| `FiniteModularQuarterGenerators` | Sparse modular generators with quarter-sized saturation, deletion, and observed clique-count errors |
| `FiniteReferenceCliqueCounts` | Finite conversion of observed-density factorial main terms to reference-density binomial main terms |
| `FiniteReferenceModularGenerators` | Exact KSG reference-density clique counts and strict source saturation/deletion bounds at n0 |
| `PermutationColourConditioning` | Exact restriction and product laws for disjoint permutation colours; uniform section bounds transfer to the original family |
| `FiniteColourPaletteBudget` | Enough unused colours for every base palette; the printed count works for q>=3, a doubled count for q=2, and the base-palette union bound fits n0 |
| `FiniteSameFamilyGeneration` | Every rainbow clique is generated in the same family, now with failure at most n^(-5/3) at n0; printed palette for q>=3 and doubled palette for q=2 |
| `FiniteRainbowProbability` | Many rainbow embeddings for all roots of size at most 2q-1 in a prescribed palette, with failure at most n^(-5/3) at n0 for q>=3 |
| `FiniteRootPatternProbability` | Separate n^(-5/3) failure bounds for punctured-clique counts and the one-base and two-base exchange properties in the same palette |
| `FiniteJointColourProbability` | All three extension properties and same-family generation hold jointly with failure at most n^(-1), using the printed palette for q>=3; constructs the typical host and sparse generator union, retaining the factorial punctured-count correction |
| `ExclusiveRainbowEmbeddings` | Exclusive colours determine a rooted embedding from its clique image, removing the factorial divisor |
| `ColourCollisionCounts` | Marked wrong-colour incidences bound the difference between successful and exclusive embeddings |
| `ColourCollisionMoments` | First moment and Markov bounds for colour collisions, retaining the full density power |
| `ExclusiveColourNumerics` | Good-subgraph density powers retain 15/16 of the reference term; collision coefficients fit n0 |
| `FiniteExclusiveColourCounts` | Exclusive embeddings exceed 35/64 of the observed-density scale, with failure at most 33*n^(-alpha/24) |
| `ExclusiveColourTrials` | Independent amplification of exclusive-colour success in the printed palette for q>=3 |
| `PrintedPuncturedColourCount` | Exact source punctured-clique count with constant 1/2 and no factorial loss; failure at most n^(-5/3) at n0 for q>=3 |
| `PrintedJointColourProbability` | All four exact source colour conclusions jointly hold in the printed palette with failure at most n^(-1), for q>=3; also constructs the host and sparse generator union |
| `AllRanksColourTrials` | Eighty q/alpha independent trials fit twice the printed palette and give n^(-5/3) failure for all roots, including q=2 |
| `AllRanksColourProbability` | All three extension assertions at n0 in every positive rank, with the original punctured-clique count and a doubled palette |
| `AllRanksJointColourProbability` | All four joint colour conclusions and sparse host assembly in every positive rank with twice the printed palette and failure at most n^(-1) |
| `ScaledNibbleFloors` | A stopping density 16/3 times the target scale satisfies all five floor conditions whenever the target is at most 1/16 |
| `ScaledSparseNibble` | Lemma 9.1 at n0 in every positive rank and every epsilon ≤ 2/5 with leave constant 16, improving the previous 432 |
| `FiniteGreedyProbability` | Actual ordinary and history-dependent prescribed greedy algorithms succeed with failure below exp(-n^(2/5)) at n0 under explicit finite conditions |
| `SeparatedGreedyProbability` | High-probability output retains disjoint free vertices for related roots; the event records the actual sampled embeddings |
| `DecoderPlacementProbability` | Decoder-region clique placements, punctured disjointness, and support bounds hold with finite high probability, at flexible working exponents |
| `SplittingPlacementProbability` | Actual repeated-root splitting placements have disjoint new edges, free-vertex separation, and bounded union with failure below exp(-n^(2/5)) at n0 |
| `DecoderFamilyProbability` | The actual decoder stage produces every bounded local decoder and its sparse supporting family with failure below exp(-n^(2/5)) at n0 |
| `AbsorberJointFailure` | Four errors exp(-n^(2/5)) fit below exp(-n^(1/10)) at n0, including arbitrary dependence of later stage laws |
| `CancellationOutputLaws` | Both cancellation-stage laws have uniform conditional failure bounds for every successful preceding output |
| `DecoderOutputLaw` | Certified finite decoder outputs and exact trajectory-derived laws, with the required enumeration change and scaled probability estimate |
| `EliminationFamilyProbability` | Finite cancellation-family output laws read the actual sampled embeddings, with exact failure mass and the prescribed pair enumeration |
| `EliminationPlacementProbability` | Actual two-root cancellation placements retain both root images, disjoint new edges, and graph bounds with failure below exp(-n^(2/5)) at n0 |
| `FailedOutputComposition` | Dependent composition preserves earlier outputs, stops on failure, and bounds total failure by the sum of conditional stage bounds |
| `FiniteObservedOutput` | Finite probability laws of outputs read from trajectory prefixes; failure mass equals the complement of the matching-output event |
| `NormalizedDecoderOutput` | Every sampled decoder supplies the normalized input, multiplicity and representation bounds for splitting at alpha/2 |
| `NormalizedSplittingOutput` | The actual signed splitting law has failure below exp(-n^(2/5)) at the normalized alpha/2 parameters |
| `SampledAbsorberProcess` | The composed actual sampler fails with probability below exp(-n^(1/10)) at n0; all successful outputs are sparse absorbers for generated leaves |
| `SampledAbsorberProcessData` | Explicit dependent four-stage sampler specification, retaining its root choices, intermediate families and final graph properties |
| `SplittingFamilyProbability` | Actual signed splitting-family output laws, including separation and support, with the finite exp(-n^(2/5)) failure bound |
| `UnconditionalSampledAbsorber` | Constructs all exchange patterns and initial roots for the sampled absorber from the supplied multiplicity-16 generating family |
| `ModulusDependentThreshold` | Closed modulus-dependent generator threshold, with equality to n0 throughout the decoder-modulus range |
| `ArbitraryModulusGenerators` | All three exact reference-density generator conclusions and the corrected random-host probability for every positive modulus |
| `AllRanksPrintedColourPattern` | Constructs a legal exchange and elimination pattern in every positive rank whose printed-palette experiment satisfies all four probability conclusions |
| `AllRanksPrintedColourSystem` | Constructs the pattern, typical host, sparse generators and successful printed-palette colouring in every positive rank at n0 |
| `PairColourExchange` | Explicit four-vertex pair exchange and exact fresh-colour and far-clique counts, fitting all printed-palette budgets |
| `PairPrintedColourProbability` | All four source colour conclusions jointly hold in the printed palette for q=2 and edge rank one, with failure at most n^(-1) |
| `LinearTypicalityDensity` | Observed-density typicality loses only a linear factor in the neighborhood size, with the actual simultaneous failure bound |
| `LocalTypicalityNumerics` | The source's local threshold absorbs all concentration and union-bound costs when edge rank times neighborhood size is at least fifteen |
| `LocalTypicalityProbability` | Corrected random typicality and density concentration at the source's local threshold in that range, with an actual graph-existence conclusion |
| `LocalTypicality` | Every rank-one graph is exactly typical; the initial combined local-threshold range is superseded by the full theorem |
| `SharpRandomTypicality` | Separate density and neighborhood errors preserve almost the full typicality tolerance, with sharper actual concentration probabilities |
| `LocalTypicalityGrowth` | Rational finite growth and logarithmic estimates at the printed local threshold, including the smallest rank-size product |
| `LocalTypicalityTails` | Both the density tail and simultaneous neighborhood tail are strictly below half the corrected total failure allowance |
| `SharpTypicalityBounds` | Geometric test counting, binomial lower bounds and separate concentration exponents at the printed local threshold |
| `FullLocalTypicality` | Corrected Lemma 5.3 at its original local threshold, density range and error tolerance in every positive rank, without a small-parameter restriction |
| `EdgewiseCorrection` | Nonpositive correction quotients are bounded by each edge's actual multiplicity, preserving all face-degree bounds |
| `VariableCliqueSlots` | Separate signed capacities per clique, exact boundary and root-degree identities, and overlap bounds from capacity sums |
| `VariableDecoderRepresentation` | Every generated leave has an exact representation within capacities fixed by the generator and decoder regions, without a uniform multiplicity assumption |
| `VariableSplittingFamily` | Constructs actual separated exchange copies for variable capacities under explicit finite inequalities; signed representations use one fixed family |
| `VariableDecoderSplitting` | Composes edgewise correction and actual variable-capacity splitting uniformly for all generated leaves, with the weighted capacity and finite numerical inputs explicit |
| `WeightedFamilyDegrees` | Fixed natural weights, exact expanded-index counts and reindexing, with no probabilistic independence assertion |
| `WeightedDecoderDegrees` | Exact decoder capacity degrees from weighted region incidences, and the resulting capacity boundedness theorem |
| `WeightedDecoderRoots` | Positive decoder weights have root-degree budget equal to source plus generator bounds and increments below one plus the generator degree cap |
| `WeightedGreedyBudgets` | Weighted deterministic target and face expectation budgets from the actual weighted root degrees |
| `WeightedGreedyProcess` | Actual history-stopped weighted embedding law, control of ordinary forbidden degrees, and uniform transition mean bounds |
| `WeightedGreedyConcentration` | Nonnegative bounded weighted increments give simultaneous adaptive tails for every positive deviation factor |
| `WeightedGreedyExistence` | A finite tail criterion constructs actual legal, disjoint embeddings with weighted degree bounds |
| `WeightedCliquePlacement` | Actual punctured clique placement with weighted region degrees and an ordinary graph bound |
| `WeightedDecoderPlacement` | Constructs decoder regions and their variable capacity bounds from the sparse generator under explicit finite inequalities, without uniform constant multiplicity |
| `WeightedDecoderTail` | Sharper inverse-alpha bound and simultaneous weighted decoder tails at the printed threshold |
| `WeightedDecoderNumerics` | Deviation n^(alpha/10) discharges all finite decoder inequalities and yields graph and capacity density n^(-2alpha/5) |
| `WeightedDecoderAtThreshold` | Actual decoder regions and their capacity bounds at n0, including support for the augmented generator |
| `VariableSplittingNumerics` | A rounded conflict cap proportional to theta*n fits the free-vertex budget; all splitting conditions hold at n0 and the output is n^(-alpha/3) bounded |
| `VariableSplittingAtThreshold` | Constructs the exchange pattern, decoder regions and one fixed variable-capacity splitting family at n0, representing every generated leave from a supplied sparse generator |
| `VariableSplittingSigns` | Fixed disjoint positive and negative families support every representation within the individual root capacities |
| `VariableSplittingCopyGeometry` | Root-edge support, exact old-graph intersections, and near/far copy geometry without uniform multiplicity assumptions |
| `VariableSplittingNearFar` | Near cliques meet the old graph in one edge; far negative cliques avoid every other negative clique |
| `VariableSplittingNearIntersections` | Free-vertex separation gives exact vertex intersections of near cliques sharing an edge |
| `VariableSplittingPartners` | Unique positive far partners for new edges of negative near cliques |
| `VariableSplittingMultiplicity` | Old-edge multiplicity is bounded by the actual sum of root capacities; new-edge multiplicity is at most two |
| `VariableSplittingDegrees` | Additive boundary-degree bound from root capacities and the simple output graph, with no maximum multiplicity factor |
| `VariableNearCancellationPairs` | Exact geometry of all opposite near cancellation pairs, without asserting a sparse bound for that whole index family |
| `VariableNearMatching` | Nonnegative old-graph boundary supplies selected near matchings that cover all chosen negative near cliques |
| `VariableSplittingOutput` | Actual fixed signed output at n0 with n^(-3alpha/10)-bounded clique boundary and selected near matchings for every generated leave |
| `SharpGeneratorCoefficient` | The full palette coefficient plus one is at most (4q)^(6q), without a coefficient-dependent threshold |
| `PaperIntegralGeneratorsAtThreshold` | Constructs the full colour system and integral generators at n0 with half the n^(-3alpha/5) degree budget |
| `IntegralGeneratorSupportAtThreshold` | The sparse source graph and generator support together fit the n^(-3alpha/5) input budget |
| `UnconditionalVariableSplitting` | Constructs fixed variable-capacity splitting at n0 from the source graph alone, representing all integrally decomposable leaves with selected near matchings |
| `EliminationNearCounts` | At most 2*(k-1) replacement cliques touch the roots of an elimination copy; their new support has at most 2*(k-1)^2 edges |
| `EliminationActiveFamily` | Exact image of the near subpattern; every high-multiplicity edge is covered only by this active family, and the other replacements have multiplicity at most two |
| `ActiveEliminationBounds` | The active boundary degree is controlled by indexed roots and the small active graph instead of the full exchange graph |
| `FiniteActiveElimination` | Actual elimination at n0 with active-family density cost 2*(q-R+1)+2+16*R!*(k-1)^2, independent of the full exchange size |
| `EdgeCappedModularGenerators` | Simultaneous face and edge caps, modular generation outside their union of saturated cliques, and the additive saturation bound |
| `EdgeCappedGeneratingData` | Constructs the good host with both caps and explicit saturation, deleted-edge, and remaining clique-count bounds |
| `RelativeEdgeCappedGenerators` | Quantitative cap budgets give relative error delta and deleted-edge fraction at most delta |
| `TypicalEdgeCappedGenerators` | Actual capped generators in a typical host, retaining face boundedness and saturated-clique fraction at most delta squared |
| `EdgeCapNumerics` | The ceiling edge cap is at most n^(alpha/20) at n0 with relative error n^(-alpha/60), for every modulus through the decoder modulus |
| `EdgeCappedAtThreshold` | Constructs the typical host and capped modular generators at n0, with no supplied host assumption |
| `RelaxedColourNumerics` | Sharper joint moments and (8H)^2 <= (4q)^(3q) give powered joint probabilities at most twice the squared marginal product at n0 |
| `OneSidedSecondMoment` | A second moment at most three times the squared mean gives lower-tail failure at most 8/9 by shifted-square Markov |
| `LogarithmicColourTrials` | ceil(9*(f+2)*log n) independent trials with failure at most 8/9 give total failure at most n^(-2) over n^f roots |
| `RelaxedColourExtensions` | Actual good-edge colour moments and simultaneous extension probabilities at n0 under the capped generators' relaxed error |
| `RelaxedRainbowExtensions` | Constructs a typical host, capped generators, and one successful rainbow palette for all roots, retaining both caps with the exact palette factor |
| `RelaxedCliqueColours` | Squared saturation error gives the marginal and pair bounds needed for the capped family's unsaturated clique colours |
| `RelaxedRainbowGeneration` | Actual far-colour replacements and modular generation of all initial rainbow cliques at n0, with simultaneous failure at most n^(-2) |
| `CappedRainbowGeneratingFamily` | Constructs the host before any initial palette, then adds colours generating all its rainbow cliques while retaining both caps and every original generator copy |
| `RelaxedRainbowRootPatterns` | Logarithmic palettes for punctured cliques, prescribed clique roots, and prescribed intersecting pairs under the capped host's deletion error |
| `RelaxedCombinedRainbowExtensions` | One explicitly sized palette simultaneously supplies all three relaxed rainbow extension properties |
| `RelaxedGoodDensity` | Every good-host density power through the full exchange size is at least half its reference value at n0 |
| `CappedRainbowGeneratingSystem` | Constructs one host with combined extensions, avoidance, modular generation, and density-power bounds; both caps are independent of the number of avoiding copies |
| `RepeatedColourBounds` | Surjective repetition of colour labels preserves the generator union, including the augmented palette used for avoidance |
| `RelaxedFocusingCounts` | Retains the original punctured-clique lower count and factorial normalization under good-edge loss n^(-alpha/60) |
| `CappedFocusing` | Constructs focusing cliques of edge multiplicity at most one, including the relaxed coloured host at n0 |
| `CappedDecoderAugmentation` | Actual local decoders add at most choose(q,R) to the edge cap, with the original flexible degree bound |
| `CappedDecoderFocusing` | Focusing plus decoding adds at most 1+choose(q,R) to the edge cap and retains half the final degree budget |
| `RelaxedRainbowIntegralGeneration` | Constructs avoiding bridges and proves integral rainbow generation with the relaxed good-edge loss |
| `CappedIntegralGeneratorsFromSystem` | Integral lifting of the actual modular system retains the input cap up to 1+choose(q,R) |
| `LogarithmicPaletteBudget` | Bounds the full palette by four maximal-root palettes and proves its numerical coefficient bound for q at least three |
| `LogarithmicPaletteGrowth` | The full logarithmic palette coefficient plus one is at most n^(alpha/20) at n0 for q at least three |
| `CappedIntegralGeneratorsAtThreshold` | Constructs integral generators at n0 for q at least three, with half the n^(-3alpha/5) degree budget and edge multiplicity at most n^(alpha/10) |
| `CappedDecoderCapacity` | Edge-disjoint decoder regions give a weighted edge-capacity bound linear in the original cap, retained by the splitting family |
| `CappedSplittingNumerics` | The fixed decoder coefficient is at most (4q)^(q+1), so splitting turns edge cap n^(alpha/10) into n^(7alpha/60) at n0 |
| `VariableNearPairCounts` | Each near clique has at most M opposite-sign partners under edge cap M; real indexed root-degree bounds avoid the choose(q,R) factor |
| `CappedVariableSplitting` | Constructs one fixed signed splitting family at n0 for q at least three, with edge cap n^(7alpha/60), representing every integrally decomposable leave |
| `SharpWeightedDecoderCoefficient` | Combines factorial and binomial factors to bound the weighted decoder coefficient by (4q)^(3q), giving density n^(-17alpha/30) |
| `CappedWeightedDecoderNumerics` | The small increment cap permits deviation one at n0, with verified legal-choice, polynomial-tail, graph, and capacity budgets |
| `CappedWeightedDecoderAtThreshold` | Constructs weighted decoder regions with graph and capacity density n^(-17alpha/30) from input edge cap n^(alpha/10) |
| `SharpVariableSplittingNumerics` | Finite splitting for stronger input exponents, graph density n^(-alpha/2), and clique-boundary density n^(-89alpha/180) |
| `SharpVariableSplittingAtThreshold` | Constructs the stronger fixed splitting family for every leave while retaining edge cap n^(7alpha/60) |
| `CappedFirstElimination` | Constructs elimination copies for all opposite near pairs at n0 with graph density n^(-alpha/3), retaining the exact coefficient |
| `VariableFirstElimination` | Negative elimination cliques avoid the original graph; every bad negative clique has a unique positive far splitting partner |
| `VariableFirstCancellation` | A selected near matching preserves boundary and disjoint signs and removes every negative near splitting clique |
| `UnconditionalFirstElimination` | Constructs generators, decoders, splitting and universal first elimination from the source alone, with checked signed cancellation for every admissible leave |

Both assertions of `rem:div` are checked, including the general ambient size
induction.
| `VariableFurtherEliminationPairs` | Constructs every bad negative clique's unique positive far partner and proves the root-intersection and overlap conditions for the further stage |
| `VariableFarPartnerIntersections` | Frame locality gives each variable-splitting positive far clique at most one edge meeting the negative near family |
| `VariableFurtherPartnerSelection` | Nonnegative boundary forces each selected far partner; selected partners are distinct and preserve the exact selected negative set |
| `VariableFurtherPairCounts` | Far partners repeat at most 4*choose(q,R)*M times, giving sharp real-cap indexed degrees without a squared multiplicity loss |
| `VariableFinalNegativeFamily` | The retained and further negative cliques form a true decomposition, avoid the original graph, and have support bounded by the second elimination graph |
| `VariableFurtherCancellation` | The selected second replacements preserve boundary and disjoint signs and place all negative cliques inside the fixed final family |
| `CappedFurtherNumerics` | The further input coefficient is at most (4q)^(5q); both placement interval bounds and the final n^(-5alpha/18) density hold at n0 |
| `CappedFurtherElimination` | Constructs all further universal cancellation copies at n0 from the actual capped splitting and first elimination families |
| `VariableSignedAbsorption` | Both selected stages convert every matched signed leave into a true decomposition of the fixed negative host together with that leave |
| `RankOneAbsorber` | Every divisible rank-one hypergraph decomposes, by embedding a partition on its edges; the empty host absorbs every such leave |
| `CappedSparseAbsorber` | Full unconditional n^(-alpha/4)-bounded sparse absorber at n0 in every positive rank, without a supplied generator or flattening threshold |
| `PaperDesignExistence` | Full unconditional design existence and the equivalent numerical binomial divisibility criterion at the paper's original explicit threshold |
| `SharpNibbleEndpoint` | Rounding costs at most a rather than the stopping density, yielding the precise finite leave p0+(128*k+1)*a |
| `TwiceNibbleFloor` | For k>=10, a=p^k and p<=1/3 satisfy the finite floor conditions at 2p, and the precise leave is at most 3p |
| `SharpFiniteNibble` | Actual finite clique-removal packings retain the precise endpoint bound for sparse graphs and rank-one inputs |
| `TenCliqueNibble` | Extends the exact constant-3 Section 9 theorem at n0 from k>=15 to k>=10, and combines it with the other previously verified ranges |
| `FlexibleNibbleInitial` | Separate regularity and tracking errors satisfy the exact initial critical margins and yield actual finite packings |
| `ScaledInitialNibbleFloors` | The tracking scale a=2*p^k/(5*k) meets all finite floor conditions at stopping density 2p for k>=6, with endpoint at most 3p |
| `ScaledNibbleInitialMargins` | The original degree error p^(3k) fits both strict initial margins at the reduced tracking scale |
| `ScaledNibbleExponent` | A logarithmic adjustment expresses the scaled tracking error as n^(-eta/3), with epsilon<=eta<=2/5 proved at n0 |
| `FlexibleFiniteNibble` | The finite sparse construction retains a separately bounded original input error, including every positive rank and small rank-one graphs |
| `SixCliqueNibble` | Extends the exact constant-3 Section 9 bound at n0 to every k>=6 and combines all verified parameter ranges |
| `SmallLeaveNibbleFloors` | Base-15 coefficient bounds verify all scaled tracking and strict initial conditions for every k>=3 and p<=1/15 |
| `SmallLeaveNibble` | The exact constant-3 finite Section 9 conclusion holds at n0 for every positive rank when the target density p is at most 1/15 |
| `ExactNibbleThreshold` | The exact constant 3 holds for all allowed parameters at the explicit sufficient threshold max(n0,ceil(15^(3*k/epsilon))) |
| `LogNibbleComparisons` | Logarithmic error functions, the uniform bound (1-k*log(p))^2*p^(k-1)<=3, derivative, and weighted-power bounds |
| `SmallRelativeRatio` | Ratio perturbation retains the actual positive denominator factor instead of replacing it by two |
| `SmallErrorEdgeDrift` | Sharper upper and lower numerical edge drift, including the survival correction, with count error at most 1/64 |
| `SmallErrorFrozenEdgeTrend` | The sharpened numerical bounds apply to conditional expectations of the actual frozen edge process |
| `LogNibbleScalars` | All six relative error margins hold for k=3,4,5 when a<=((2/5)*p)^k |
| `LogNibbleScaleBounds` | Lifts the scalar margins to degree and clique-count errors and proves the scalar face drift with face error 2a |
| `LogNibbleIncrements` | Exact finite-step logarithmic degree and count error bounds, with both signs controlled |
| `LogNibbleEdgeSteps` | Finite logarithmic comparison increments, Taylor remainder, absolute increment bounds, and survival allowance |
| `LogNibbleEdgeTrend` | Both logarithmic critical drift bounds hold on the actual removal trajectory, including already removed edges |
| `LogNibbleCountConditions` | Logarithmic count errors dominate both clique-overlap losses and the quadratic degree-variance term |
| `LogNibbleCliqueSteps` | Count comparisons have the required finite drift directions and absolute increments at most 9*k^3*D |
| `LogNibbleCliqueCountTrend` | Both logarithmic count critical trends hold under the actual trajectory law |
| `LogNibbleParameters` | One explicit set of scalar hypotheses controls every density above the chosen stopping floor |
| `LogNibbleFaceComparisons` | Constant face error 2*a*n has the required drift and average loss at most 12*k*n/g |
| `LogNibbleFaceTrend` | Actual face drift, conditional variance, and absolute increment bounds for the logarithmic route |
| `LogNibbleTrackedProcess` | One measurable finite family tracks both count signs, both frozen-edge signs, and every face |
| `LogNibbleGoodState` | The common logarithmic good event guarantees availability, actual remaining-edge degree bounds, and face bounds |
| `LogNibbleGoodTrend` | Every track has the required critical drift on the common logarithmic good event |
| `LogNibbleEdgeLossBound` | Logarithmic edge comparisons fit the existing fixed increment and average-loss scales |
| `LogNibbleEdgeVariance` | Actual frozen-edge variance and absolute increment bounds on the logarithmic good event |
| `LogNibbleTrackedBoundedness` | Global increment bounds for all logarithmic tracks, using the existing explicit step scales |
| `LogNibbleVarianceBudget` | Conditional variance rates and cumulative budgets hold before the first logarithmic tracking failure |
| `LogNibbleCriticalControl` | The logarithmic processes satisfy simultaneous critical-window control and the existing explicit failure bound |
| `LogNibblePackingCriterion` | A supported good trajectory gives an actual clique packing with bounded leave density p+2a |
| `LogNibbleInitialBounds` | The paper's original degree regularity starts every logarithmic track strictly below its critical interval |
| `RegularLogNibbleCriterion` | Full logarithmic packing construction from original regularity and explicit numerical hypotheses, without a supplied good trajectory |
| `LogNibbleHalfWidths` | All step half-width estimates and the rounded-density error bound for logarithmic parameters |
| `LogNibbleEndConditions` | Uniform critical-window gaps and an actual packing at the logarithmic horizon, with leave p0+3a |
| `LogNibbleTrackExponents` | Count, edge, and face concentration exponents for the logarithmic construction |
| `LogNibbleUniformExponent` | A common exponent and the explicit simultaneous failure bound for every logarithmic track |
| `FiniteLogNibbleEnd` | The logarithmic endpoint conditions at the original n0 for every epsilon at most 2/5 |
| `FiniteLogNibbleParameters` | All logarithmic scalar parameters at n0 without a lower cutoff on epsilon |
| `FiniteLogNibble` | Actual sparse logarithmic packings at n0, including the separate rank-one small-graph case |
| `SmallCliqueNibble` | The exact constant-3 leave bound at n0 for clique sizes three through five |
| `ExactPaperNibble` | Full Lemma 9.1 at the original n0 and printed constant 3 for all positive ranks and epsilon at most 2/5 |
| `CliqueFamilyLowerDegrees` | Lower degrees retain the q-r factor from the input boundary bound |
| `UniformCliqueEnlargement` | Exact superset counts and fixed-face probabilities for a uniformly enlarged input clique |
| `CliqueEnlargementBudget` | Simultaneous face expectation budgets using all intersections with the input clique |
| `FiniteChoiceConcentration` | Actual finite random choices with bounded sums for every test and supported outputs |
| `CliqueEnlargementExistence` | Constructs one shared enlarged region per input clique with simultaneous face bounds |
| `CliqueRefinementDegrees` | Boundary bounds for all refined cliques, allowing overlaps and repeated regions |
| `SharedCliqueDecoders` | Actual local decoder regions with coefficient 2*(4q)^R under finite sampling inequalities |
| `SharedDecoderNumerics` | Shared decoder size and failure estimates at n0 for every input coefficient at least one |
| `SharedDecodersAtThreshold` | Local decoder augmentation at n0 with half the final printed coefficient and no input coefficient cap |
| `PrescribedCliqueEnlargement` | Face probabilities for arbitrary prescribed candidate families, including impossible intersections |
| `PrescribedCliqueSelection` | Actual prescribed clique choices with simultaneous bounds and no disjointness assumptions |
| `PrescribedCliqueFamily` | A bounded clique family through every prescribed root edge |
| `AllEdgeFocusing` | Geometric focusing at n0 for every reserve edge, including edges already in the coloured host |
| `ExactDecoderFocusing` | Full standalone decoder/focusing lemma with the exact printed coefficient and all geometric conclusions at n0 |
| `PaperModularGenerators` | KSG probability and existence at n0 for the paper's fixed decoder modulus, without an extra modulus hypothesis |
| `LiteralGreedyCounterexample` | The printed process definition has no legal first step on a nontrivial rank-one example satisfying its numerical assumptions for every n at least 1025; the corrected process has legal choices |
| `RankOneLegalExtensions` | Root-preserving embeddings avoiding a vertex set, and deterministic availability of rank-one legal extensions |
| `RankOneGreedyBounds` | Rank-one root bounds control the entire run length; all histories satisfy degree caps and retain legal choices under a linear smallness condition |
| `GreedyCertainSuccess` | Actual ordinary-process success with probability one from deterministic degree and availability bounds |
| `RankOneGreedy` | The full printed greedy smallness bound in rank one, with success probability one and the stronger input degree bound |

| `IntersectingGreedyStars` | Pairwise-intersecting root sets force distinct free centres in every disjoint star family |
| `IncidentRootEmbeddings` | Incident-pair root embeddings and cyclic rotations; every vertex fibre has size at most 2L |
| `DoubleStarPattern` | Admissible double-star pattern with at most twice as many edges as roots |
| `RootFiberBounds` | Vertex-fibre bounds imply rank-two edge-degree bounds and survive embedding and reindexing |
| `BalancedStarRoots` | Balanced, pairwise-intersecting root embeddings in a finite ambient set and their natural-number sequence |
| `DoubleStarNumerics` | The fixed 257-vertex pattern satisfies every printed numerical hypothesis for n=65600L and L>=4096 |
| `StarGreedyFailure` | The success event is empty for 65792L prescribed roots in 65600L ambient vertices |
| `GreedySmallnessCounterexample` | Arbitrarily large counterexamples to the intended Lemma 5.5 under its printed linear smallness condition; success probability zero for every output bound |

## Paper coverage

The labels below are the source's LaTeX labels. A proved supporting identity
does not establish the corresponding construction lemma.

| Source label / result | Status |
| --- | --- |
| `thm:steiner` — eventual unconditional design existence | Proved in full, including rank one; also proved with the equivalent numerical binomial divisibility conditions |
| `param` and Section 10 — explicit quantitative threshold | Proved at the exact printed n0 in every positive rank, including the equivalent numerical divisibility criterion. Parameter identities, exact logarithm, and fixed-rank big-O estimate are also proved. The larger corrected bound remains valid but is no longer needed |
| `lem:R` — sparse reserve | Proved at the printed threshold, with the required clique count at every edge and stronger strict `n^(-ρ)`-boundedness |
| `lem:A` — sparse absorber | Proved unconditionally at n0 with the paper’s n^(-α/4) bound in every positive rank. Growing caps and weighted decoding replace the expensive fixed-multiplicity flattening route |
| `lem:reg` — regularity boosting | Proved in full at the printed threshold, complement constant 2^(-3q), and binomial normalization, with stronger relative n^(-1/3) error. The construction already works for n >= (4q)^(90q) |
| `lem:nibble` — approximate clique decomposition with bounded leave | Proved at the printed threshold in every positive rank, including q = 2, r = 1, with the paper's initial relative error and n^(-3*k*rho)-bounded leave |
| `lem:cover` — cover the leave using reserve edges | Proved at the printed threshold and the paper's parameters, including the actual clique family and its decomposition |
| `lem:OO` — clique exchange configuration | Proved, including the explicit bound and admissibility; a stronger version using the corrected seed also supplies opposite-clique intersections and positive frame locality |
| `lem:decode` — bounded integral local decoder | Proved |
| `lem:pseudobin` — concentration inequalities | Part 1 is proved with the authorized nonnegativity hypothesis; the original signed statement is refuted; part 2 is proved as stated |
| `def:typ`, `lem:randomtyp` — typical random hypergraphs | Proved in every positive rank at the source's original local threshold n>=2^(9Rh), density range and typicality error, with failure below exp(-n^(1/10)). Rank one is exactly typical with probability one; higher ranks have simultaneous density control. No small-parameter cases remain. The earlier explicit threshold through the exchange size is preserved. The printed exp(-n/10) rate is refuted |
| `def:process`, `lem:process` — random greedy embeddings | The literal forbidden-root rule is formally refuted. The corrected ordinary and degree-stopped processes are constructed, with exact equality of bounded-success probabilities. In rank one the full printed smallness bound gives success with probability one and the stronger input degree bound for n>=2*v_H. In higher ranks, corrected finite failure below exp(-n^(2/5)) holds under explicit size and conservative smallness conditions; all paper applications and the general eventual bound are proved. The printed general linear smallness condition is formally refuted by a fixed rank-two pattern at arbitrarily large n: the success event is empty for every output degree bound. The proved quadratic smallness repair suffices for every paper application |
| `rem:process` — separate forbidden density and prescribed candidate families | The same printed linear smallness condition is refuted by the ordinary-process special case. Under the corrected smallness condition, actual ordinary-process probabilities include history-dependent candidates and separate density scales. At n0, failure is below exp(-n^(2/5)) under the finite smallness condition and theta/eta≥n^(-1/2). The general eventual rate exp(-n^beta), beta<1-(b-a), also remains proved |
| `cor:A` — successful bounded absorber construction | Proved at n0 for the corrected multiplicity-16 construction after Step 1, with joint failure below exp(-n^(1/10)). All patterns and the four actual trajectory-derived laws are constructed, later stages may depend on earlier outputs, and every successful output is n^(-alpha/4)-bounded and absorbs all generated leaves. The printed exp(-n/10) convention is refuted; this probability theorem has a supplied multiplicity-16 Step-1 family. The capped route separately proves unconditional absorber existence at n0 |
| `lem:Aint` — integral absorber | Sparse generation at n^(-α/2) is proved above a uniform explicit threshold with multiplicity 16, sufficient for the absorber. The printed multiplicity-two conclusion is refuted when choose(q,r)>2, even for a singleton reserve at arbitrarily large sizes |
| `lem:KSG` — sparse generating cliques | Fully proved at n0 for the paper's fixed N=R!*choose(q,R), with exact reference-density binomial counts, strict saturation/deletion bounds, and corrected probability greater than 1-exp(-n^(1/10)). This N is defined in the local-decoder lemma and reused in the integral lift; KSG does not quantify a new arbitrary modulus. The extension to every positive N holds at the documented modulus-dependent threshold. The printed probability rate is refuted |
| `lem:extcol` — rainbow extension and generation | All four source conclusions hold jointly at n0 in every positive rank with a constructed pattern, the printed palette, and failure at most n^(-1), including the reference-density count with constant 1/2 and no factorial loss. The pair case uses an explicit four-vertex exchange. The typical host and sparse generator union are constructed. The doubled-palette theorem remains available for arbitrary supplied patterns |
| `lem:Q0'` — locally decoding and focusing cliques | Fully proved at n0 with the exact printed coefficient 2^(q+2)*(4q)^R*u*n^(-7alpha/10), complete local decoder regions for every input edge, and focusing cliques for every reserve edge. The proof shares a region across each input clique and does not require disjointness between the reserve and coloured host. The earlier integrated construction and its coefficient bounds remain valid |
| `lem:flat` — flattening to multiplicity two | The printed multiplicity-two conclusion is refuted on sparse inputs. A multiplicity-16 replacement is proved with an explicit larger threshold, including the full printed input coefficient. The current uniform round-cost estimate is formally incompatible with n0 for triangles; the completed design theorem at n0 bypasses this flattening cost |
| `rem:div` — degree divisibility characterizes integral decomposability | Proved for all `n ≥ q+r` |
| `freed`, `rem:doob` — martingale and supermartingale concentration | Proved for finite processes with the printed conditional-variance constant; the centering bound is correctly 2b |
| `lem:nibble+` — quantitative clique removal | Fully proved with the exact printed constant 3 at the original n0 for every epsilon ≤ 2/5 in all positive ranks, from the original degree regularity and density assumptions. No exceptional range or extra threshold remains. The eventual constant-3 bound also holds for every epsilon<1/2 |

## Verification

Run from `src/latest`:

```sh
lake build Arxiv.Arxiv2411_18291
lake env lean Arxiv/Arxiv2411_18291/Audit.lean
```

Both commands passed on 2026-08-27. The entry point imports all 844
supporting modules in the inventory above; the full build completed
4440 jobs. All 2959 assumption checks match their exact names and order
and use only `propext`, `Classical.choice`, and `Quot.sound`. The audit
explicitly covers every one of the 2956 public theorems and lemmas,
plus three proof-bearing definitions.

This includes Theorem 1.1 and the numerical divisibility criterion at the
original explicit threshold, the full sparse absorber in every positive
rank, Lemma 9.1 with constant 3, and the standalone decoder/focusing lemma
with its exact printed coefficient. KSG uses the fixed paper modulus.
The greedy results include probability-one success at the printed rank-one
smallness bound and an arbitrarily large rank-two counterexample to the
printed general bound, with success probability zero.

The inventory agrees exactly with the reachable, acyclic import graph.
All Lean sources are free of proof placeholders, added axioms, unsafe
evaluation, and computational limit overrides. Changed proof files have
no long lines, trailing whitespace, or tabs. The only build warnings are
the pre-existing dirty BoundedGaps and AINTLIB dependency notices.

Logs: `tmp/arxiv-2411.18291/build-844.log` and
`tmp/arxiv-2411.18291/audit-844.log`.

## Final source audit

The last mathematical obligation is resolved by
`arbitrarily_large_greedy_linear_counterexamples`. For a fixed rank-two
pattern on 257 vertices, all printed Lemma 5.5 input bounds hold at
arbitrarily large n, but the ordinary-process success event is empty.
Increasing the output degree constant or weakening the failure rate cannot
repair this statement. The proved quadratic smallness hypothesis suffices
for every application and leaves the main threshold unchanged.

KSG uses the fixed N=r!*choose(q,r) defined in `lem:decode` (source line 696),
reused in Gamma=Z/NZ (line 1089) and the integral lift (lines 1452-1458).
It does not quantify a fresh arbitrary modulus. The stronger
arbitrary-modulus theorem remains available at its documented threshold.

The signed concentration claim, printed exp(-n/10) convention,
multiplicity-two conclusions, literal process definition, and general
linear greedy smallness condition have explicit counterexamples. Their
proved repairs are source corrections, not obligations to prove false
claims. The multiplicity-16 flattening repair needs a larger threshold;
the main theorem at n0 uses a different, capped construction.

All 24 labelled theorem, lemma, corollary, definition, and remark results
in the LaTeX source occur in the coverage table above. Their hypotheses,
conclusions, constants, and source corrections have been reviewed against
the formal statements. The parameter display and Section 10 threshold
are also covered. The unlabelled Section 8 definitions use Mathlib's
measurable spaces, filtrations, martingales, and supermartingales; the
finite-process Freedman theorem is proved with the printed denominator.
Section 9 contains the quantitative nibble (Lemma 9.1); earlier references
to that result as Section 8 / Lemma 8.1 have been corrected.

There are no remaining mathematical formalization obligations under these
corrections. No claim is made that the refuted statements hold as printed,
or that all intermediate constructions follow the paper's original proof.

## Historical implementation notes

The sections below record earlier milestones and their then-current open
obligations. Statements there that a construction or threshold was not yet
proved are historical; the overview, coverage table, and final source audit
above describe the current status. The latest milestone is at the end.

## Random greedy constants and source corrections

In the paper's notation, let `r` be the edge size, `w = v_H`, and `M = |H|`.
The finite construction currently proves the following sufficient conditions:

- `n > 0` and `n ≥ 4*w^2`;
- the forbidden graph and each prescribed root-edge family are `θ`-bounded;
- `θ ≥ 0` and `M*(θ + M*(4*r!*θ)) ≤ 1/4`;
- `M*choose(n,r-1)*exp(-2*r!*θ*n/3) < 1`.

Under these numerical conditions and admissibility, actual extensions exist
whose new edge sets avoid the forbidden graph, are pairwise disjoint, and
whose new-edge families are strictly `4*r!*θ`-bounded. The root-edge families
retain their input bound; `IsGreedyFamily.all_edges_bounded` combines both.
`eventually_exists_greedy_family` discharges the size and numerical conditions
for every fixed `θ = n^(-ρ)` with `0 < ρ < 1`.

The proof accounts for the union of **all** previous new-edge families when
forming the forbidden graph. Its sufficient smallness condition is more
conservative than the printed `θ < (8*r!^2*|H|)^(-1)`; that printed constant
has not been certified.

For prescribed candidates with at least `η*n^(w-|F|)` embeddings, the
generalized finite criterion instead uses `η>0`, `n>0`, root bound `θ`,
forbidden bound `θB`, and output bound `L=4*r!*θ/η`, with
`M*(θB+M*L)≤η/2` and
`M*choose(n,r-1)*exp(-(2*r!*θ*n/η)/3)<1`.
Candidate sets may depend on previous choices, and their lower bound is
needed only on successful histories below the degree caps. Static candidates
are a special case. These numerical conditions hold eventually at
`η=n^(-a)`, `θ=n^(-b)`, `θB=n^(-c)` when `2*a<b`, `a<c`, and `b-a<1`.
No independent-domination assumption is used.

The source's definition of `C_i` names previous root edges, although its
applications require excluding previously used new edges. The formal process
excludes the new edges and leaves the prescribed root edges fixed. Prefix
degrees also use only the preceding steps, correcting the displayed sum over
all `[t]`. The final concentration argument uses conditional means under the
actual trajectory measure, not the source's unsupported independent-domination
claim. The bound above is retained explicitly instead of the source's stronger
`whp` convention.

## Source correction: signed concentration

The source at `DesignsShort.tex:773–781` assumes only `|X_i| ≤ C` and
independence in part 1, with `E X = μ`, and claims

`P(|X - μ| > c*μ) ≤ 2*exp(-μ*c²/(2*(1+2*c)*C))`.

Lean checks the following counterexample in `ConcentrationCounterexample.lean`:

- Take 400 independent fair coins, and let each `X_i` be `28/25` or `-22/25`.
- Every `|X_i| ≤ C = 28/25`, every summand is measurable and integrable,
  and the total mean is `μ = 48`.
- Set `c = 1`. Exactly 225 positive outcomes give `X = 98`, hence
  `|X - μ| = 50 > 48`.
- That single count has probability `choose(400,225)/2^400 > 1/600`.
- The claimed bound is `2*exp(-50/7) < 1/600`.

`SignedConcentration.signed_pseudobin_counterexample` packages the hypotheses
and strict violation. Its axiom audit uses only Lean's standard axioms. The
large binomial comparison uses the proved binary factorial identities at the
default computational limits, without native evaluation or extra axioms.

This does not refute the main design-existence theorem. It prevents proving
**all results exactly as printed**. Adding nonnegativity to part 1 is the
authorized correction; the source proof at lines 1634–1636 invokes a
variance estimate controlled by the mean that does not hold for arbitrary
signed summands. The user has explicitly authorized proceeding with this
correction or resolving the issue at the lemma's applications.

## Random typicality and explicit failure probabilities

The typicality proof now retains an explicit failure probability instead of
assuming the source's shorthand `whp = probability > 1 - exp(-n/10)`.
The simultaneous bound is a polynomial in `n` times
`exp(-n*p^h*c^2/12)`. It tends to zero for `p ≥ n^(-ρ)` and
`c = n^(-δ)` when `ρ*h + 2*δ < 1`.

The graph obtained has relative density error at most `n^(-δ)` and
typicality error at most `(4 + 2*h*2^h)*n^(-δ)`. Specializing to
`ρ = 1/(2*h)` and `δ = 1/5`, then enlarging the eventual size threshold,
gives the paper's `n^(-1/10)` error scale. This proves an eventual existence
statement without a probabilistic construction assumption. The stronger
probability result and counterexample to the printed `whp` convention are
proved below. The explicit threshold `n > 2^(9*r*h)` remains unverified.

## Reserve construction

`IsTypical.puncturedCliques_lower` proves the lower bound
`(n/2)^(q-r) * d^(choose q r - 1) / (q-r)!` for distinct cliques extending
any fixed edge, with all other edges in the graph. The proof uses an exact
bijection at each step and double counts predecessors; it does not count
ordered vertex sequences as distinct cliques.

`eventually_exists_reserve_paper_parameters` combines this count with sparse
typicality. Sampling at one quarter of `n^(-ρ)` gives actual density between
`n^(-ρ)/8` and `n^(-ρ)/2`, so typicality implies strict `n^(-ρ)`-boundedness.
For sufficiently large `n`, the spare factor `n^(-ρ)` in the required
clique-count exponent absorbs the fixed powers of two and the factorial.
The resulting count is at least `n^(-choose(q,r)*ρ) * n^(q-r)`.

This strengthens the printed reserve's `2*n^(-ρ)` degree bound to the
`n^(-ρ)` hypothesis of the absorber, resolving that constant mismatch.
The finite theorem `exists_reserve_paper_threshold` now verifies every
numerical condition for n>=n0; see the explicit construction below.

## Cover construction

`eventually_exists_clique_cover` applies the prescribed-choice process to a
complete clique pattern rooted at one edge. A punctured clique supplies at
least one root-preserving embedding, so the input count is a lower bound on
the number of actual candidates. Taking `b=c=3*a` gives a valid eventual
process for `0<a<1/2`. The forbidden graph starts empty.

Each output clique contains its assigned leave edge, and all remaining edges
lie in the reserve. The leave's roots are distinct and outside the reserve,
so disjoint new-edge families imply disjoint full clique edge sets. The
resulting family has exactly `|L|` cliques and is a true decomposition of a
graph `G` with `L ⊆ G ⊆ L ∪ R`.

`exists_clique_cover_paper_threshold` now checks the finite conditions at
`a=choose(q,r)*ρ`, `ρ=(6*choose(q,r))^(-2)`, and every n>=n0.
`ExplicitReserveCover` combines this with the finite reserve construction;
the eventual interfaces in `ReserveCover` are corollaries. The reserve's own degree
bound is not needed by the cover argument beyond its extension counts.
The source mentions an ambient `G \\ A` in the Cover lemma without introducing
those objects locally; the intrinsic containment above supplies the needed
ambient containment whenever `L ∪ R ⊆ G \\ A` in an application.

## Sparse local decoders and bounded representations

`eventually_exists_clique_placement` applies the base greedy construction to
the complete pattern on `q+r` vertices rooted at one edge. Given a
`θ=n^(-ρ)`-bounded graph `B`, `0<ρ<1`, it produces one region `Z_e` per edge
of `B`. Their full `r`-edge sets are pairwise disjoint and meet `B` only in
their assigned roots. Their union is strictly
`(1+4*r!*choose(q+r,r))*θ`-bounded.

The family `D₂` of all `q`-subsets of these regions has edge multiplicity
exactly `choose(q,r)` on their union and zero outside it. The sparse support
bound therefore also gives a boundary-multigraph bound, with the additional
factor `choose(q,r)`. Every root edge has a decoder supported on `D₂`, with
multiplier `N=r!*choose(q,r)` and coefficients bounded by `2^q*r!`.
This constructs Step 2; it does not assume its placements exist.

`bounded_representation_of_local_decoders` implements the first algebraic
part of the absorber proof. Suppose the original clique family `D₁` has
edge multiplicity at most two, all its edges lie in `B`, and it integrally
represents a leave `L ⊆ B`. Reducing its coefficients to `[0,N-1]` gives
a residual vector divisible by `N`, with every quotient in `{-1,0}`.
Summing the corresponding local decoders corrects the boundary exactly.

The decoder regions are edge-disjoint, so each decoder clique receives at
most one correction. Also `D₁` and `D₂` are disjoint when `q>r≥1`: each
region has only one edge in `B`, whereas an original clique has at least
two. Thus the resulting representation on `D₁ ∪ D₂` has every coefficient
bounded by `2^q*r!`, with the same constant as the paper. The one-sided
remainder choice simplifies the printed balanced-remainder argument without
weakening its conclusion. The chosen family `D₂` works for every represented
leave simultaneously. The signed absorber now absorbs all these normalized
representations. The sparse family `D₁` generating every divisible leave
is constructed in the later integral-generation and flattening sections.

## Separated splitting construction

`eventually_exists_splitting_family` constructs Step 3 uniformly for every
bounded clique family `D` of edge multiplicity at most `M`. It allocates `C`
positive and `C` negative slots for each clique, where the absorber uses
`C=2^q*r!`. Each slot receives an actual copy of the exchange configuration
with its base mapped to the prescribed clique.

New edge sets are pairwise disjoint and avoid the prescribed graph `B`,
which contains every edge of `D`. If two roots share an edge, their copies'
free vertex sets are disjoint. The root conflict count is at most
`choose(q,r)*(2*C)*M`. At a step with at most `d` earlier conflicting roots,
at most `d*w` vertices are excluded. The candidate count leaves at least
half the choices when `n≥4*w²` and `n≥4*d*w²`.

The separated process has output bound `8*r!*θ` and finite numerical
conditions `|H|*(θ+|H|*8*r!*θ)≤1/4` and
`|H|*choose(n,r-1)*exp(-4*r!*θ*n/3)<1`.
These hold eventually for every fixed `θ=C₀*n^(-ρ)`, `C₀≥1`, `0<ρ<1`.
Constant factors are retained; no density exponent is lost. The resulting
union has the explicit degree bound recorded in `SplittingFamily.bounded`.
The printed quantitative size threshold has not been certified.

`ExchangeSystem.boundary_replacement` proves the exact exchange identity.
Each replacement clique contains a new edge, so the greedy invariants and
the containment of the roots in `B` rule out a replacement clique appearing
in two copies. Thus selecting signed slots produces coefficients in
`{-1,0,1}`. `SplittingFamily.signed_representation_with_signs` proves that
every supported coefficient vector bounded by `C` has the same boundary
as a difference `P-N`, where `P` and `N` lie in fixed positive and negative
splitting families chosen before the coefficient vector.

These positive and negative families are disjoint **as sets of cliques**.
Their cliques are not claimed to be edge-disjoint: the two elimination stages
remove the negative overlaps and put selected negatives in a fixed decomposition.

The splitting geometry is now checked. Negative far cliques are edge-disjoint
from every other negative splitting clique. Two distinct negative near cliques
sharing an edge intersect precisely in that edge's vertices; the same holds
for an opposite-sign near pair. Every edge outside `B` in a negative near
clique belongs to a unique positive splitting clique, and that clique is far.
These statements use the actual separated copies, not additional geometric
assumptions about the placed family.

## Verified exchange construction

The finite-field construction is now implemented using polynomial evaluation
and Lagrange interpolation. `exists_prime_exchange_seed` supplies the seed.
`exists_glue_bijection` aligns its common edge with the selected edge of the
current negative clique. `vertex_glue_two_decompositions` and
`glue_families_disjoint` handle the two families. `two_glues_inter_old` gives
the required separation after the second attachment.

The implemented `PreparedFamily` invariant assigns each completed edge
`e` a last-copy region `R_e` and its distinguished negative clique `N_e`:

- `R_e` meets the base clique precisely in `e`, and `N_e` is contained in `R_e`.
- Each region avoids the private vertices of every other prepared clique.
- Every negative clique or host edge meeting the **private vertices of `N_e`**
  lies inside `R_e`.

It is the private vertices of `N_e`, not every vertex of `R_e` outside the
base, that must be protected. A negative clique containing a different base
edge cannot meet those private vertices, so subsequent gluing interfaces
avoid them. `exists_prepare_edge` preserves the invariant through both new
attachments; `exists_prepared_subfamily` iterates over the finite edge set.
`exists_clique_exchange` then establishes the full frame condition and bound.

## Additional seed correction for elimination

The source's later elimination argument uses a property stronger than the
stated exchange lemma: a surviving positive decomposition clique must meet
the designated negative clique in at most one edge. The printed seed's shift
is zero on the distinguished `r` parts and one elsewhere. Its all-one positive
clique meets the designated negative clique in `q-r` vertices. For example,
`q=5, r=2` gives three common vertices and three common edges.
`fieldExchangeSeed_large_opposite_inter` checks the obstruction for all
`0<r` and `2*r<q`. This does not refute the exchange existence lemma itself.

The repaired seed translates by
`w(X) = ∏ (X-y_i)`, over the distinguished `r` nodes. A positive clique and a
negative clique differ by a polynomial of degree exactly `r`, so they agree
at at most `r` nodes. The designated zero clique and translated zero clique
still meet exactly in the chosen edge. The graph and its two decomposition
sizes are unchanged. `exists_prime_crossSimple_exchange_seed` proves existence
with the same prime range and seed edge bound.

`ExchangeSystem.glue_crossSimple` proves that the extra intersection bound
survives gluing. The two-attachment induction carries it through the entire
construction. Thus `exists_crossSimple_clique_exchange` has all the previous
properties, the stronger intersection bound, and the same
`3*(2*q)^r*choose(q,r)^2` edge bound.

The local elimination identities and both crucial geometric properties are
proved for this stronger exchange. `exists_elimination_pattern` packages an
actual admissible pair, and `exists_pair_root_map` sends it to any prescribed
target pair with the correct intersection. The complete two-stage assembly,
final global negative-clique disjointness, and signed absorption are now proved.

## Simultaneous cancellation-pair placements

If the original clique family has edge multiplicity at most `M` and splitting
uses `C` slots of each sign per clique, then its full replacement family has
multiplicity at most `2*C*M` on the original graph and at most two elsewhere.
The uniform bound `2*C*M+2` converts the simple support bound into a boundary
multigraph bound. No independence of replacement cliques is assumed.

In a clique family of edge multiplicity at most `M`, a fixed clique has at
most `choose(q,r)*M` overlapping partners. Thus a sequence of distinct ordered
pairs repeats each coordinate at most that many times. Admissibility puts
every induced pattern root edge in one of the two prescribed root cliques,
so the input edge-family bound follows at the same density exponent.

For a fixed elimination pattern `S`, a clique boundary and forbidden graph
bounded by `A*n^(-ρ)`, and `0<ρ<1`,
`eventually_exists_elimination_placements` constructs placements for every
sequence of distinct pairs with the required vertex intersections. In the
paper's edge-rank notation, the output new-edge family bound is
`8*r!*choose(q,r)*M*A*n^(-ρ)`, and the whole graph is bounded by
`A*n^(-ρ) + |S|*8*r!*choose(q,r)*M*A*n^(-ρ)`.
The theorem constructs both root maps and all extensions, including empty
sequences. The explicit printed threshold is not yet certified.

`eventually_exists_first_elimination` now applies this construction to the
actual finite set of all opposite-sign near pairs. If splitting has graph
bound `A*n^(-ρ)` and its original family has multiplicity at most `M`, set
`K=2*C*M+2`. The first-stage family has graph bound
`K*A*n^(-ρ) + |T|*8*r!*choose(q,r)*K*(K*A)*n^(-ρ)`.

Every negative first-stage clique avoids the original graph `B`. Good cliques
avoid the whole splitting graph and are edge-disjoint from every other
negative first-stage clique. A bad clique meets the splitting graph in one
edge; that edge is outside `B` and belongs to its negative near root. The
proved splitting-partner theorem supplies a unique positive far clique
through it. Its vertex intersection with the bad clique is exactly that edge,
so the second-stage root condition is established without an extra assumption.

For a root family with multiplicity at most `M`, the full signed elimination
family has multiplicity at most `4*choose(q,r)*M^2+2`. Including the input family
gives the bound `M+4*choose(q,r)*M^2+2`. These conservative constants suffice
at the unchanged exponent `ρ` and are used in the second-stage construction.

`FurtherEliminationPairs` indexes the second stage by the actual bad cliques,
so its negative roots do not repeat. Their shared edges belong to their
positive far partners. The same containment holds for intersections with the
negative far splitting cliques and good first-stage negative cliques.
`eventually_exists_second_elimination` constructs this family using the proved
multiplicity and support bounds.

`finalNegative_decomposition` proves that the union of negative far splitting
cliques, good first-stage negatives, and all second-stage negatives is truly
decomposed by those cliques. The union is disjoint from the original graph and
inherits the second-stage sparse bound. `eventually_exists_two_stage_elimination`
combines both existence theorems with explicit factors `firstEliminationFactor`
and `secondEliminationFactor`. The signed-absorption argument described next
establishes that this fixed negative host works for every bounded representation.

## Universal signed absorption

`NearMatching` assigns each selected near clique its unique original edge.
The signed boundary is nonnegative there, so each negative color fiber has
size at most its positive fiber. The resulting injection selects cancelling
pairs without repeating either root. `SelectedElimination` proves the exact
replacement identity for any such selected family. `FirstCancellation`
eliminates all negative near cliques, retaining the negative far cliques.
This explicitly retains a family omitted in the paper's sentence saying
that all remaining splitting cliques are positive.

For the second stage, uniqueness of a partner at each edge is not by itself
enough to prevent one positive clique from being used at several edges.
`PreparedProtection` strengthens the actual exchange construction: every
positive clique touching a prepared private set lies in its protecting
region. This invariant survives both attachments and insertion, without any
new size cost. Thus `exists_local_crossSimple_clique_exchange` includes
positive frame locality, even when the edge size is one.

Positive frame locality and the corrected polynomial seed imply that a
positive far clique meets the entire negative near family in at most one
edge. No positive first-stage elimination clique can contain a bad old edge.
Nonnegative boundary therefore forces the corresponding far partner to be
present and permits only one negative clique at that edge. Hence the selected
far partners are distinct. The second replacements preserve the boundary and
leave every negative clique in `finalNegative`, which truly decomposes the
fixed host. Adding its unused cliques gives a true decomposition of host plus
leave. This proves `two_stage_absorbs_bounded_representations`.

`exists_sparse_absorber_for_bounded_representations` constructs all required
patterns and placements, uniformly for every coefficient vector bounded by
`C` on the supplied family `D`. For input graph and clique-boundary bounds
`A*n^(-ρ)` and edge multiplicity `M`, it gives a fixed host bounded by
`K*n^(-ρ)`, with `K` depending only on the fixed parameters. It is disjoint
from the input graph and has a true decomposition. No density exponent is lost.

Finally, `exists_sparse_absorber_for_generated_leaves` combines the local
decoders and coefficient normalization with that construction. For any
`n^(-ρ)`-bounded graph `B` and a clique family `D` supported there with edge
multiplicity at most two, one sparse host absorbs every leave `J ⊆ B` that
is integrally generated by `D`, with no restriction on the original integer
coefficients. This does not assume a universal generating family exists;
the later construction supplies one with the sufficient multiplicity bound 16.

## Integral absorber: modular generators and saturation

The deterministic selection in `lem:KSG` is now proved. A new generator
outside the previous subgroup at least doubles its cardinality, by Lagrange's
theorem. `exists_bounded_generating_subfamily` chooses a maximal finite family
whose incidence loads are at most the specified cap and whose subgroup size
is at least `2^|G|`. Any unsaturated element outside its subgroup could still
be added, contradicting maximality. Hence all unsaturated elements are generated,
and the chosen family has size at most the base-two logarithm of the group order.

`exists_modular_generating_cliques` applies this to clique vectors over
`ZMod N`. It counts in the space of vectors on the host edges, of cardinality
`N^|K|`, and transports the result by zero extension to vectors on all ambient
edges. Thus the resulting full modular generators satisfy `|G|≤N*|K|` and
the prescribed face-load caps. No probabilistic hypothesis is used in this step.

`SaturationCounts` proves the exact incidence identity and its consequences:
the cap times the number of saturated faces is at most `choose(q,r-1)*|G|`;
the number of saturated cliques is at most the sum of their face extension
counts; and the heavy-edge threshold times the number of heavy edges is at
most `choose(q,r)` times the number of saturated cliques. Here `r` denotes
the paper's edge size.

The typicality estimates and good-subgraph construction are now also proved.
Rooted-clique counts exempt every edge inside a prescribed root. Exact
extension/predecessor double counts give upper and lower bounds with the
correct factorial and density exponent. Under the explicit collision bound,
their relative error is at most `η*q*2^q`. This covers total cliques, cliques
through an `(r-1)`-face, and cliques through an edge.

Write `k=choose(q,r)`, `j=choose(q,r-1)`, and `d=density K`. The finite
generator criterion uses a positive integer face cap and target error `ε`.
The inequality `4*k*j*N*n*d ≤ cap*ε^2`, together with counting error at most
`ε/2`, ensures that at most an `ε` fraction of all cliques are saturated
and at most an `ε` fraction of host edges are deleted. Each retained edge
belongs to `μ ± ε*μ` unsaturated cliques, with
`μ=n^(q-r)*d^(k-1)/(q-r)!`. The generator boundary bound follows directly
from the cap.

`eventually_good_modular_generating_data` proves these numerical conditions
uniformly for typical graphs of density between fixed positive multiples of
`n^(-α)`. With `cap=floor(n^(1-s))` and `ε=n^(-t)`, it suffices that
`s<1`, `0<t<δ`, `s+2*t<α`, and `α*k+δ<1`. The floor is positive and at least
half its real argument for all sufficiently large sizes.

`eventually_exists_sparse_modular_generators` constructs the graph as well
as its generating data. For `α>0`, `α*h≤1/2`, and `h≥k`, it gives the
Section 6 scales `δ=1/10`, `s=7*α/10`, and `t=α/10`, including typicality
and density error `n^(-1/10)`. This is an eventual construction version of
`lem:KSG`, with observed-density clique main terms and a saturated fraction
relative to the actual clique family. The newer finite construction below
also proves the reference-density bounds at n0 for the decoder-modulus range,
with the corrected probability rate; the false printed rate is not used.

## Coloured copies and the frame-conditioning repair

`ModularGeneratingData.map` transports all modular generating relations
under a vertex permutation. `ModularGeneratingData.permuted_generates`
then shows that the union of the permuted generators spans every
monochromatic unsaturated clique. Its boundary is bounded by the number of
colours times the original bound, even if the copies overlap.

`uniform_permuted_family_probability` proves the exact probability
`|D|/choose(n,q)` that a fixed `q`-set belongs to a uniformly permuted family
`D`. The proof constructs equal-size permutation fibers and uses an actual
finite probability measure. Deleting at most an `ε` fraction of edges from
a graph of relative density error `δ` changes the resulting edge probability
by at most `(ε+δ+ε*δ)` times the reference density.

Joint estimates, simultaneous rainbow extensions, and generation of all
original rainbow cliques are now proved, as detailed below.
The printed proof of `lem:extcol`.4 needs
care with conditioning: after fixing the entire frame, the printed bound
`d^(2*(k-1))` for cliques sharing a frame edge does not by itself imply the
claimed vanishing relative variance compared with a squared mean of order
`d^(2*k)`. This is a gap in that variance argument, not a formal counterexample
to the existence statement. The formal construction repairs it by counting
all eligible frame embeddings while fixing only the base, and uses a separate
added palette to generate the cliques rainbow in the original palette.

## Joint permutation estimates and count moments

`exists_perm_map_finset_pair` proves transitivity on ordered pairs of sets
with the same component sizes and intersection size. It matches the three
disjoint regions of each pair and extends the resulting injection to a
permutation. Composition then gives equal permutation fibers for each pair.

For block sizes `a,b` and intersection size `s≤b`, the orbit has exactly
`choose(n,a)*choose(a,s)*choose(n-a,b-s)` elements. Consequently the joint
probability that two prescribed blocks belong to two permuted families
under the **same** permutation is the fraction of this orbit in the pair
family. No independence of these two events is assumed.

If all rooted counts of the second family are at most `L`, its pair-family
size is at most `|G|*choose(a,s)*L`. After division by the exact orbit count,
the factor `choose(a,s)` cancels. Explicit falling-factorial estimates give
`choose(n-a,b) ≥ (1-ε)*n^b/b!` whenever the finite size condition holds.
For fixed bounded `a,b`, this holds eventually with `ε=n^(-κ)` for every
`κ<1`.

`IsTypical.permuted_clique_pair_probability_le` combines these facts with
the proved rooted-clique estimates. In the paper's edge-rank notation,
two `q`-cliques intersecting in `s<r` vertices, and any two subfamilies of
the host clique family, have joint probability at most
`(1+16*ε)*d^(2*choose(q,r))`, provided both finite counting errors are at
most `ε≤1/2`. `eventually_permuted_clique_pair_probability_le` proves all
these conditions uniformly when `0<κ<min(δ,1)`, the density is bounded
below by a positive multiple of `n^(-α)`, and `α*choose(q,r)+δ<1`.

`RandomPermutation.probability` is an actual product probability measure
on colour-indexed vertex permutations. A candidate is a finite collection
of coordinate constraints. Its indicator is measurable and integrable,
and a finite candidate count has integrable square. The mean is the sum,
over candidates, of the products of marginal coordinate probabilities.
The second moment is the sum over ordered candidate pairs of products of
their joint probabilities in each colour.

With `m` colours, uniform marginal probability `p` gives mean `|T|*p^m`.
If every nonexceptional ordered pair has joint probability at most `t` in
each colour, the second moment is at most `|T|^2*t^m+|B|`, where `B` is the
specified exceptional-pair family. Finally, if the mean is `μ>0` and the
second moment is at most `(1+ε)*μ^2`, the probability of count at most
`μ/2` is at most `4*ε`. If `4*ε<1`, a colour assignment with count above
`μ/2` exists.

These moment criteria are now applied to actual root-preserving embeddings
and amplified over all root maps, as described next.

## Simultaneous rainbow extensions and source applications

For a root set `F`, let `m=|W|-|F|`. Among pairs of extensions from
candidate families `T,U`, at most `m^2*|T|*n^(m-1)` share a vertex outside
the fixed root. The linear dependence on `|T|` is useful when the candidate
family itself has only polynomial density. Every other pair intersects
exactly in its prescribed root vertices. A pattern block meeting the root
in fewer than `r` vertices therefore falls under the proved joint bound.

If `|T|≥c*n^(-a)*n^m`, marginal probability is at least `b*n^(-β)`, and
there are `M` constrained blocks, the collision contribution is a relative
`n^(-κ)` error whenever `a+2*β*M+κ<1`. A joint error of order `n^(-γ)`
with `0<κ<γ` contributes at most another `n^(-κ)`. The lower-tail failure
probability is then at most `8*n^(-κ)`.

The product-measure repetition theorem requires independence only between
trials, not between different roots. With `L` trials, failure for a fixed
root is at most `(8*n^(-κ))^L`. There are at most `n^|F|` injective root
maps, so any fixed `L` with `κ*L>|F|` makes their union bound less than one
for all sufficiently large sizes. This produces one collection of colour
groups that works for every root, rather than a separate choice per root.

`eventually_many_rainbow_extensions` applies this to all extensions into a
typical host's good subgraph. Their initial count is at least `(3/4)*n^m`,
so every root retains more than `(3/8)*p^M*n^m` rainbow embeddings, where
`p` is the actual good-subgraph density. `IsRainbow` includes an injective
assignment of edges to their colours. No independence is hidden in that
definition.

At the paper's density scales, `α*h≤1/4`, `M≤h`, and `h≥1` suffice; the
source's stronger parameter bound also fits this range.
`eventually_exists_sparse_rainbow_generators` constructs the host and its
modular data as well as these permutations. The union of the permuted
generators retains its boundary bound, multiplied by the fixed number of
colours, and generates every monochromatic unsaturated clique.

For the first colour property, a prescribed root edge has at most
`(q-r)!` extensions with any one image clique. The proved distinct-clique
bound is therefore
`(3/8)*p^(choose(q,r)-1)*n^(q-r)/(q-r)!`.
This initial bound explicitly accounts for vertex orderings. The stronger
exclusive-colour argument below now proves the printed larger count for q>=3.
For the second and third properties, the root-map theorems prescribe one
clique or a pair intersecting in exactly one edge. Exchange locality proves
that the uncoloured root edges are precisely the one or two removed cliques.

`eventually_combined_rainbow_extensions` now assembles all three properties
in one family indexed by `Fin u`, for a fixed `u` independent of `n`.
Injective colour relabelling preserves each rainbow witness and the clique
counts. The fourth property's frame-conditioning issue is repaired below.
The later joint colour theorem below proves the exact palette, count, failure
probability, and threshold for q>=3.

## Frame structure and the next generation step

`IsExchangeFamily.nearRootEquiv` identifies the near cliques with the
`choose(q,r)` base edges. Every near clique has exactly `q-r` private
vertices, these private sets are pairwise disjoint, and the frame has exactly
`q+choose(q,r)*(q-r)` vertices. Every far clique meets the base in fewer
than `r` vertices. These are checked facts, so the existing colour moment
theorem can be applied to far cliques while fixing only the base.

`ExchangeSystem.modular_image_base_mem` proves the algebraic conclusion:
if all replacement clique vectors of an embedded exchange belong to an
additive subgroup modulo `N`, then its base vector belongs to that subgroup.

The repair of the fourth colour property starts by fixing the
colour family used for rainbow extensions, then adds a separate finite
family of colours to generate its rainbow cliques. The integral absorber
needs generation of those original rainbow cliques; it need not make the
same claim for additional rainbow cliques created by the new colours.
For each original rainbow base, count every eligible near-frame embedding
as part of the candidate family, then apply the far-clique colour estimate
with only the base fixed. The candidate count, simultaneous far-clique
construction, and combination with the modular exchange identity are now
proved. The resulting theorem generates every original rainbow clique;
it makes no generation claim for new rainbow cliques formed by the added
palette.

## Counting all eligible near frames

`rooted_clique_vertex_count_le` bounds the number of `q`-cliques through an
`r`-vertex root and one additional fixed vertex by `n^(q-r-1)`. Consequently,
a previously used set `U` removes at most `|U|*n^(q-r-1)` choices. When the
rooted family has size at least `L` and this budget is at most `L/2`, at
least `L/2` choices remain.

`choiceSequences_card_lower` multiplies these lower bounds over a finite
history-dependent choice process. This is a direct cardinality argument,
with disjoint branches, not a claim of independent choices. In a frame
with `k` near cliques, the resulting sequences have pairwise disjoint
private vertices and exact intersections with the base. They inject into
indexed assignments, yielding at least `(L/2)^k` distinct assignments.

The prescribed base bijection and the bijections between private pieces
glue to an actual frame embedding. Every such embedding has at least
`(3/4)*n^(v-frameSize)` completions when `n≥4*v^2`. Different indexed
assignments cannot share a completion because a full embedding determines
every assigned clique image. `frameCandidateExtensions_card_lower` therefore
proves the product bound for actual full embeddings, preserving the original
base map.

For rooted-family size `L=c*n^(-γ)*n^(q-r)` with `γ<1`, the forbidden-vertex
budget holds eventually. The frame has `k*(q-r)` private vertices, so the
product bound simplifies exactly to candidate density
`(3/4)*(c/2)^k*n^(-γ*k)` relative to all `n^(v-q)` base-preserving assignments.

`eventually_good_edge_rooted_count_lower` obtains
`c=b^(k-1)/(2*(q-r)!)`, `γ=α*(k-1)` from the proved good-edge count, when
the host density is at least `b*n^(-α)`. Relabelling preserves the rooted
count exactly. Finally, `eventually_near_frame_candidates` applies these
bounds to the actual near cliques of an exchange. It fixes the base map and
the prescribed good-edge colours, and constructs a candidate family of size
at least

`(3/4)*(b^(k-1)/(4*(q-r)!))^k * n^(-α*k*(k-1)) * n^(v-q)`.

Every near clique in every candidate is monochromatic in its prescribed
clique family. The near frame itself varies throughout the count. This is
the candidate-density input needed to use the previously proved far-clique
intersection bound with only the base fixed.

## Completed rainbow generation with separate colour families

For `D` obtained by deleting a polynomially small fraction of the host's
`q`-cliques, `eventually_clique_colour_estimates` proves marginal lower
bound `(b^k/2)*n^(-α*k)` and relative lower bound
`(1-n^(-γ))*density(K)^k`. Its joint upper bound for two cliques
intersecting in fewer than `r` vertices is
`(1+n^(-γ))*density(K)^(2*k)`.

There are `k` near cliques. If there are `M` far cliques, the exact
decomposition counts give `k*M ≤ 2*|H|` and `k^2 ≤ |H|`. Thus the
near-candidate exponent plus the collision exponent is at most
`α*k*(k-1)+2*α*k*M ≤ 5*α*|H|`. Under `α*h≤1/12`, the existing uniform
colour experiment applies with positive polynomial error exponents.

`eventually_rainbow_exchange_replacements` fixes the initial permutations,
then constructs one finite extra palette working for every original rainbow
base. Near cliques use the original colours, while far cliques use the new
ones. The resulting actual exchange embeddings give modular generation by
the union of the two permuted generator families. Adding a dummy identity
colour makes the final palette nonempty even in degenerate index cases.
Its boundary bound is the old bound multiplied by the fixed palette size.

`eventually_exists_rainbow_generating_system` constructs the host, good
subgraph, generators, original palette, and added generating palette, while
retaining all three original rainbow extension properties. It is an eventual
construction theorem, not a proof of the printed probability bound, explicit
colour count, or numerical threshold.

The completion argument also needs extensions avoiding colours prescribed on
their roots. `t+1` distinctly labelled copies of a palette suffice to avoid
any set of at most `t` labels: some copy contains none of them. This is
deterministic and does not assume independence between identical permutations.
`eventually_exists_avoiding_rainbow_generating_system` performs this duplication
before applying generation. Therefore it generates all rainbow cliques in
the duplicated original palette, not merely those rainbow before duplication.

## Completed sparse focusing construction

`exists_focusing_vector` subtracts the weighted clique through each input
edge outside the target graph. Every other edge of such a clique is in the
target graph, so all remaining outside coordinates vanish exactly.
`exists_focused_integral_vector` also preserves integral decomposability.

`eventually_exists_sparse_clique_cover` uses candidate density `n^(-a)`
and root degree bound `n^(-b)`. If `0≤a`, `2*a<b`, and `b-a<1`, it
constructs an actual cover whose graph is bounded by
`n^(-b)+4*r!*choose(q,r)*n^(-(b-a))`. Applying it only to input edges
outside the target yields one fixed sparse focusing family for every signed
input vector. Its cliques may overlap the previously chosen generators;
no disjointness from that family is needed for the focusing lemma.

The factorial-corrected rainbow count supplies the candidate density at any
exponent strictly larger than `α*(k-1)`. Good-edge deletion and the host's
relative density error give good-subgraph density at least `n^(-α)/4`.
Taking `a=α*(k-1)+α/2`, the condition `ρ≥2*α*k` supplies all greedy gaps.
The fixed coefficients are eventually absorbed to obtain an
`n^(-0.7*α)`-bounded focusing family for every `n^(-ρ)`-bounded input graph.
This is `eventually_exists_sparse_coloured_focusing`.

The local decoder family is assembled with the focusing family and generators.
Integral vectors on the coloured graph are now generated by rainbow cliques,
as proved below. The later flattening construction reduces multiplicities
to a fixed bound, and the final assembly proves unconditional design existence.

## Decoder assembly and the remaining integral-generation reduction

The indicator of a clique family's support is bounded coordinatewise by its
boundary. Thus a boundary degree bound also bounds the simple support graph.
`eventually_augment_with_local_decoders` uses that fact and the earlier local
decoder construction. For any `0<t<s<1`, it enlarges a family bounded by
`C*n^(-s)` to an `n^(-t)`-bounded family decoding every modulus multiple
supported on the original family. All fixed coefficients are absorbed in
the exponent gap; the construction works uniformly for all later vectors.

`eventually_exists_decoder_focusing_augmentation` combines this with focusing.
The resulting family contains the generators, focuses every integral input
vector onto the colour graph, and decodes modulus multiples on the generator
support. Its bound is `n^(-η)` for any fixed `0<η<0.7*α`, with `0.7*α<1`.

`generatedBy_of_clique_residuals` supplies an algebraic alternative to pairing
signed copies. Assign a reference edge vector `w_e` to every edge outside
the coloured graph. If each clique boundary minus the sum of its outside-edge
references is generated by the chosen family, then every integral boundary
supported on the coloured graph is generated. Double counting shows that
the total coefficient of each `w_e` is the original boundary coordinate,
which is zero outside the graph. The geometric residual relations are now
proved by the bridge and exchange arguments below.

Replacement and elimination exchanges now have explicit `GeneratedBy`
witnesses over the integers, including after arbitrary vertex embeddings.
`GeneratedBy.modular_mem` transports an integer representation into the
modular span of another family when each supporting clique is generated
there. Conversely, `exists_integral_boundary_of_modular_generated` proves
by subgroup-closure induction that every modularly generated vector lifts
to an integer boundary on the same family. Finally,
`generatedBy_of_modular_membership` uses local decoders to correct the
modulus-divisible difference on a specified support graph. Its support and
decoder hypotheses are explicit; this is not an assertion that the complete
integral absorber has been constructed.

## Completed sparse integral generation

A punctured rainbow bridge avoids the palettes of two prescribed cliques
and intersects each exactly in their common root edge. Applying elimination
to both pairs and subtracting cancels the bridge. Thus any two punctured
rainbow cliques through one edge have a difference generated by full rainbow
cliques, even when their vertices or colour labels overlap elsewhere.

For an arbitrary base clique, choose a palette containing one label for each
coloured base edge. A replacement exchange avoiding this palette has rainbow
far cliques, punctured rainbow near cliques, and fully rainbow near cliques
at coloured roots. The near-root bijection gives one term per base edge.
Comparing each uncoloured near clique with a fixed punctured rainbow reference
proves the residual identity needed for incidence cancellation. This proves
`eventually_integral_coloured_generated_rainbow` over the integers.

Every coloured edge extends to a full rainbow clique by avoiding its own
label. Modular generation of that clique forces the edge into the generator
support, because the modulus is greater than one. Local decoders therefore
correct the complete modular difference, with no missing support assumption.
Focusing, rainbow generation, and modular lifting now construct one fixed
sparse family generating every integral vector supported on the reserve.

`eventually_exists_sparse_integral_generators` constructs the exchange system
as well, subject only to numerical exponent conditions. The global divisibility
criterion gives the version for all degree-divisible signed vectors.
`integral_generator_parameters` verifies those conditions for
`ρ=(6*choose(q,r))^(-2)` and `α=ρ/(2*q)^r`. Consequently
`eventually_exists_sparse_integral_generators_paper_parameters` constructs a
family whose boundary is `n^(-0.6*α)`-bounded. The subsequent sparse
flattening construction now supplies the fixed multiplicity needed by the absorber.

## Completed sparse flattening and unconditional absorption

The construction splits the family before every reduction round. Splitting
preserves its integer span and does not increase old-edge multiplicities.
New edges occur at most twice, every split clique has at most one old edge,
and distinct split cliques through one old edge intersect exactly there.
Only old edges used more than 16 times are grouped. Nonempty disjoint groups
have both size and count per root at most `floor(sqrt(x))+1`.

A product of independent uniform choices selects one existing member of
each group. For a face T, the weighted incidence of a representative from
a group of size s is s times its membership indicator; its expectation is
exactly the number of group members containing T. The proved nonnegative
upper-tail inequality and a union bound yield simultaneous weighted degrees
at most twice the input scale. This works uniformly when the density is at
least `n^(-ρ)`, with `ρ<1/2`, and group sizes are at most `sqrt(n)+1`.

Every nonrepresentative is eliminated exactly once against its representative.
The uniform greedy construction places all exchanges. Common root edges
vanish from the added cliques, and no other old edge can enter an exchange.
Counting retained and removed cliques together gives the recurrence
`x ↦ max 16 (2*floor(sqrt(x))+4)`. The integer span is preserved, and each
round increases the boundary-degree bound by only a fixed constant.

The capacity `16*4^(2^k)` bounds the number of rounds needed to reach 16.
For every fixed cost C and every ε>0, the total cost is eventually at most
`n^ε`. The theorem `eventually_exists_sparse_flattening` therefore preserves
the integer span while taking an `n^(-ρ)`-bounded family to an
`n^(-η)`-bounded family with multiplicity at most 16, for every fixed
`0<η<ρ<1/2`. All rounds and all degree bounds are constructed and checked.
This is a conservative substitute for the paper’s multiplicity-two lemma,
not a proof of that exact printed conclusion.

At the paper’s parameters, `BoundedIntegralGenerators` combines integral
generation and flattening to obtain one `n^(-α/2)`-bounded family generating
every integral vector on the reserve, with multiplicity at most 16.
The coefficient normalization works for any fixed multiplicity M: the
modulus-reduction quotient has absolute value at most M, and the coefficient
bound is `(M+1)*2^q*r!`. Thus the generalized universal absorber applies.

Enlarge the reserve by the generator support. Its degree bound fits below
`n^(-α/3)` for all sufficiently large n. Absorption supplies a disjoint host
with bound `K*n^(-α/3)`, which fits below `n^(-α/4)`. The theorem
`eventually_exists_sparse_absorber_paper_parameters` proves the eventual
Absorber lemma unconditionally: this one host absorbs every divisible
subgraph of the original reserve. Its own true decomposition and divisibility
follow by taking the empty leave. This construction is used in the completed
main existence theorem. The printed explicit threshold remains unverified.

## Completed regularity boost for polynomially sparse complements

Normalized real local decoders have unit boundary and the explicit
coefficient bound inherited from the integral decoder. Averaging over
many actual decoding cliques preserves the unit boundary and reduces
individual coefficients. Double counting bounds the total number of
decoding assignments that can affect any fixed target clique. Consequently,
`fractionalDecoderCorrection` corrects a real edge error exactly while
remaining supported on graph cliques, with a proved uniform error bound.

If the complement is `n^(-δ)`-bounded, missing clique-extension vertices lie
in the used set or in a missing-edge neighborhood of a current face.
The union bound and the existing rooted-clique recurrence give counts
`(1±n^(-κ))*n^(q-a)/(q-a)!` for every fixed `0<κ<min(δ,1)`, uniformly in
the graph and the root. The same estimate supplies many `(q+r)`-vertex
local decoding cliques through every graph edge.

Start each graph clique with probability one half. Use the averaged
decoders to correct its edge means to `n^(q-r)/(2*(q-r)!)`. The ambient
powers cancel in the coefficient bound, leaving a fixed multiple of the
counting error. For all sufficiently large n, every corrected coefficient
lies in `[0,1]`. The theorem `eventually_exists_fractional_boost` constructs
these probabilities; no fractional decomposition is assumed.

The independent product experiment allows different probabilities at
each clique. The corrected nonnegative concentration inequality and a
union bound yield one actual clique family satisfying every edge count.
Sampling at relative exponent `2/5`, then converting the power-scale main
term to `choose(n,q-r)`, proves `eventually_exists_regularity_boost`:
all graph-edge counts are `(1±n^(-1/3))*choose(n,q-r)/2`. This is the
stronger relative error required by the paper’s nibble input; the displayed
Boost lemma itself uses an absolute error twice as large.

The complement hypothesis in this theorem is polynomially small, with
`0<δ<1`, which suffices after removing the constructed absorber and reserve.
The printed constant condition `c<2^(-3q)` is established below by a
sharper estimate; the explicit size threshold remains open. The proof keeps sampling
probabilities distinct from normalized fractional weights: the expected
edge count is `n^(q-r)/(2*(q-r)!)`, not one half.

### Extension to a fixed complement bound

`exists_constant_complement_regularity_boost` now gives the same regularity
conclusion for a fixed positive complement bound depending only on the ranks.
To choose it, let R = r+1 be the graph rank, let
K = `fractionalBoostConstant q R`, and put

- epsilon = 1 / (4*(K+1));
- A = (q+1)*choose(q,r);
- B = (q+R+1)*choose(q+R,r);
- theta = epsilon / (2*(A+B+1)).

All these choices are independent of n, and theta is positive. The two
rooted clique estimates have relative error at most epsilon for all
sufficiently large n. The decoder correction has size at most one half,
so it gives valid sampling probabilities. Independent sampling and the
existing binomial conversion then yield relative n^(-1/3) error.
The earlier polynomial-complement theorem shares the same finite
fractional-boost proof. The construction below improves the complement
constant to the printed value 2^(-3q); the existential wrappers now use it.

## Variance-sensitive martingale concentration

The scalar estimate
`exp(t*x) ≤ 1+t*x+(t^2/(2-t*b))*x^2` holds for signed `x≤b`,
`b,t≥0`, and `t*b<2`. Conditional expectation produces an exponential
supermartingale compensated by conditional second moments. Bounded optional
stopping at its first threshold crossing gives a maximal inequality without
an extra factor for the number of times.

Choosing `t=a/(v+a*b)` gives the stronger second-moment tail
`exp(-a^2/(2*v+a*b))`. The source's supermartingale centering argument
incorrectly keeps the increment bound b; the valid immediate bound is 2b.
Using 2b in the stronger estimate recovers precisely the printed
`exp(-a^2/(2*(v+a*b)))` bound with conditional variance.
`freedman_finite_process_bound` assumes adaptation, integrability, bounded
increments, and the supermartingale condition only up to a finite horizon.
`freedman_martingale` and `freedman_supermartingale` give the paper's forms.
The critical-interval stopping argument is now proved as well. An attempted
crossing starts immediately after the last value below its lower boundary.
The overshoot is at most one increment bound; summing the Freedman bound
over at most n start times gives an explicit failure bound. Predictable
indicators stop an attempt when either its interval condition or a shared
good event fails, and cannot increase conditional variance. Taking the
first failure among a finite family justifies using drift and variance
estimates that are only valid before that failure. This supplies
`CriticalWindowControl.failure_probability_le` and
`CriticalWindowControl.exists_good_trajectory`, with all hypotheses explicit.

## Clique removal: constructed process and checked one-step counts

`CliqueRemovalProcess.probability` is the actual trajectory measure whose
steps choose uniformly from the available q-cliques, or return an empty
marker when there are no choices. `FiniteHistoryProcess.condExp_step` and
`CliqueRemovalProcess.condExp_chosen_step` compute conditional means of
increments depending on the entire history from those transition laws.
Supported trajectories give subsets of the original clique family whose
cliques are pairwise edge-disjoint. If a choice remains at each step,
`trajectory_card` gives exactly n chosen cliques after n steps and
`trajectory_leave_card` gives exact edge accounting. These implications
alone do not assert that choices remain until the nibble's target horizon;
the completed asymptotic control below now supplies that assertion.

The union of edge neighborhoods counts discarded cliques exactly. Distinct
r-edges have at most `|V|^(q-r-1)` common q-cliques, so the error from multiple
counting is at most `choose(q,r)^2*|V|^(q-r-1)` per step. Double counting gives
the average total clique loss in terms of the sum of squared edge degrees.
For an edge that survives a step, its clique-degree change is at most
`choose(q,r)*|V|^(q-r-1)`; this uses a conservative fixed constant.

The surviving-edge condition is essential: if the selected clique contains
the edge, its whole clique degree disappears. The constructed frozen
process freezes both the degree and its deterministic comparison at that
removal step. Before removal it equals the actual remaining degree minus
the comparison value. Its conditional drift is exactly the negative average
frozen loss minus the comparison increment times the survival probability.
The conditional absolute mean and variance are bounded, and upper and lower
drift estimates follow from the current covered-edge degree bounds.

The total clique-count process and the face-degree process also have exact
updates on every trajectory, including trajectories containing empty or
illegal choices. The face loss counts only currently remaining edges,
which gives a global small-change bound; the uniform transition law only
selects available cliques, so double counting gives the exact conditional
drift. Squared deviations of current clique degrees bound their variance
about the actual mean and supply both clique-count drift inequalities.
The total-count increments have a finite-horizon variance budget. Face
variance is at most the maximum face loss times its conditional mean;
subtracting the predictable comparison increment does not affect variance.

Finite differences of power main terms now have explicit first-order and
quadratic remainder bounds. Reciprocal and reciprocal-square error terms
have explicit increment bounds for both signs. Numerator cancellation and
quotient perturbation estimates give upper and lower critical-interval drift
criteria for the actual frozen edge process. The lower criterion includes
an explicit survival correction; the upper criterion can discard that term
when the comparison increment is nonpositive.

Available clique families decrease on every trajectory. On a supported
trajectory, nonempty current availability therefore rules out any earlier
abort. The current clique-count lower bound can thus justify the exact
density and the tracked degree of each live edge, without a separate
assumption of non-abort at every preceding step. Supported paths have full
measure under the constructed process.

The concrete edge-comparison parameter inequalities are now proved, including
the finite-step remainder and survival correction, and hold eventually at
the paper’s density scales. Clique-count and face comparison estimates now
also pass, with their critical drift verified under the same good event.
Finite-horizon variance budgets and simultaneous critical-interval control
are now assembled, and an explicit numerical criterion gives availability
through the horizon and a packing with bounded leave. Its scalar conditions
are now verified at the paper's scales, proving the eventual nibble.
No completed nibble or main theorem is claimed from the general concentration
criterion alone.

## Concrete reciprocal comparison bounds

Write `a = n^(-epsilon/3)`, `k = choose(q,r)`, and let g be the initial
edge count. The comparison main terms are `m = D*p^(k-1)` and
`h0 = D*g*p^k/k`. The conservative errors are now fixed as
`u = 16*k*a^2*D/p` and `v = 16*k^2*a^3*D*g/p^2`; the edge critical width
is `a^2*D`, and the auxiliary drift scale is `t = a^2*D/p`.

The record `NibbleComparisonParameters` gives explicit scalar conditions
at a stopping density p0. Its consequences hold uniformly for `p0 <= p <= 1`:
`u^2 <= t*m`, `u <= m`, `v <= h0/2`, `v*m <= t*h0`, and the required
codegree bound. The lower clique-count comparison is positive. Consecutive
densities differing by `k/g` are comparable, so the checked finite-step
bounds apply. Both edge comparison increments have absolute value at most
twice the main drift magnitude and satisfy their respective critical-interval
requirements. The lower requirement retains the explicit survival correction.

`eventually_nibble_comparison_parameters` constructs this record from
polynomial graph and degree lower bounds with explicit exponent gaps.
`eventually_nibble_parameters_from_densities` specializes it to
`g = phi*choose(n,r)`, `D = tau*choose(n,q-r)`,
`phi >= n^(-r/3)`, `tau >= n^(-1/3)`, and
`p0 = n^(-epsilon/(3*k))`, for `2 <= r < q` and `0 < epsilon < 1`.
The concentration argument will use the paper’s stricter epsilon range.
This parameter theorem is eventual; it does not certify the printed
explicit threshold or establish the bounded-leave nibble conclusion.

## Count and face comparisons and the common good event

The additional record `NibbleCountConditions` requires
`128*a <= k*p0^(k-2)`, `1 <= a^3*g`, and `L <= a^3*D`.
These assumptions and the edge parameter record hold eventually at the
paper's density scales for `0 < epsilon < 2/3`, which includes the source's
range. They supply both clique-count critical drift inequalities. Both
count comparison increments have absolute value at most `130*k^3*D`.

The face comparison is `p*F + 128*k*a*n`, where F is the initial face degree.
Its increment is exactly `-k*F/g`, its critical width is `a*n`, and its upper
critical drift is nonpositive. Under the good bounds the average face loss
is at most `4*(1+128*k)*k*n/g`. For graph rank r+1, its conditional variance
is at most `(q-r)` times that bound. The global increment bound is
`(q-r) + k*n/g`.

`nibbleTrackedProcess` combines the upper count, negative lower count,
upper frozen edges, negative lower frozen edges, and upper face processes
into one finite adapted family. `nibbleGood` means that all these tracks
are strictly negative. Its failure is pointwise detected by some track
reaching zero. On a supported trajectory the good event gives nonempty
current availability, hence no earlier abort, and the actual degree bounds
for all remaining and all covered edges. `nibbleGood_tracked_trend` proves
nonpositive conditional drift in each track's critical interval using only
this common good event.

For frozen edges in the initial graph write `B = k*L + 2*k^2*D/g`. Their global increments are
at most B in absolute value. Under the good event their conditional
variances are at most `B*(10*k^2*D/g)`, including zero variance for edges
already removed. Finite-horizon summation and the explicit critical-window
failure bound are now checked, as described below. Its eventual smallness
is also proved.

## Checked finite-horizon packing criterion

The index set includes all ambient edges for a simple fixed finite type.
Edges outside G are now constant tracks with value `-2*a^2*D` and zero
increments; requiring a positive lower clique degree for those edges would
make initialization impossible. Only edges in G use the frozen comparisons.
All adaptedness, drift, boundedness, and variance proofs respect this guard.

`nibbleCriticalControl` instantiates the proved critical-window theorem for
the actual trajectory law. For a horizon N its variance budgets are N times
the fixed per-step rates. `nibble_failure_probability_le` gives the explicit
finite sum `nibbleFailureBound`. A bound below one yields a trajectory in
every transition support on which all good events hold, rather than merely
an arbitrary path in the ambient sample space.

`nibble_initial_below_critical` proves initialization from
`|degree_H(e)-D| <= a^3*D` for every edge e in G. Double counting controls the
initial total clique count, and nonedges have zero actual clique degree.
Consequently `exists_regular_nibble_packing` requires no unproved process
or initialization assumption. Its numerical inputs, besides the proved
scalar records P and Q and initial regularity, are:

- `p0 <= removalDensity(k,g,N)`;
- every fixed increment bound is smaller than its critical width;
- `nibbleFailureBound(q,G,a,D,N) < 1`;
- `removalDensity(k,g,N) + 128*k*a <= theta`.

Under these explicit numerical conditions it constructs `C ⊆ H`, with
`C.card = N`, a genuine decomposition of its clique support, and a strictly
theta-bounded leave. The following asymptotic estimates now discharge these
conditions. The finite criterion itself is not being claimed as the main
existence theorem.

### Checked numerical estimates

The horizon is `floor((1-p0)*g/k)`. The proved rounding bounds give
`p0 <= p_N < p0+k/g` and `N <= g`. Eventual `128*k*a <= p0`, together
with the already proved `k/g <= p0`, then gives the desired `theta=3*p0`.

For a comfortable half-width gap, the additional sufficient scalar bounds
are `264*k^3 <= a^3*g` for the count track and `4*(q-r) <= a*n` for face
tracks (here the graph rank is r+1). The existing edge parameter record
implies the edge half-width gap. All these deductions and their eventual
forms are now checked.

With half-width gaps and `N <= g`, the three Freedman exponents are
bounded below by positive constants times
`a^6*g`, `a^4*D/(k*L+2*k^2*D/g)`, and `a^2*n`, respectively. The paper's
density bounds give `g >= c_g*n^(2*R/3)` and `D/L >= c_D*n^(2/3)` for
graph rank `R >= 2`. The common lower exponent is
`n^(1/3-2*epsilon/3)` when `0 < epsilon < 1/2`.
There are at most `5*n^R` tracks and at most `n^R` steps, giving the checked
failure bound `5*n^(2*R)*exp(-n^(1/3-2*epsilon/3))`, which is eventually below one.

## Unconditional eventual nibble

`eventually_exists_nibble` constructs the actual clique packing on `Fin n`
under the initial regularity and density hypotheses, with no unproved
process, concentration, or existence assumption. It proves the eventual
version for graph rank at least two and `0 < epsilon < 1/2`, giving the
strictly `3*n^(-epsilon/(3*k))`-bounded leave.

`exists_nibble_paper_threshold` specializes to initial density
above one half and degree main term `choose(n,q-R)/2`, with relative
`n^(-1/3)` error. Since `1/(12*k) < 1/(9*k)`, the factor three in the general
leave estimate is absorbed at n>=n0, giving exactly the paper's
`n^(-3*k*rho)` boundedness with `rho=(6*k)^(-2)`. All its finite conditions
are now proved, including the pair case. The eventual interfaces in
`NibblePaperParameters` are corollaries of this finite construction.

## Unconditional design existence

The main assembly now uses `paper_threshold_regular_host`. At or above the
printed n0, the union of the n^(-rho)-bounded reserve and n^(-alpha/4)-bounded
absorber is 2^(-3q)-bounded. Finite double counting then shows that the
remaining graph has more than half of all edges. These are exactly the input
bounds for regularity boosting at the printed complement constant and for
the nibble. The older eventual density theorem remains available but is no
longer needed in this assembly. The main theorem also uses the finite reserve,
cover, Boost, and nibble constructions directly. The absorber now uses finite
colour construction and explicit assembly and flattening bounds. These are
not all certified at n0, so the printed overall size bound is still not proved.

The nibble packing and reserve cover are edge-disjoint. Together they
cover every edge outside the absorber except for a subset of the reserve.
Divisibility of that final leave follows by subtracting the absorber and
the two decomposed graphs from the complete graph. The absorber finishes
the decomposition. This proves `eventually_hasDecomposition_complete_succ`
with no unproved construction assumptions.

For rank one, `rankOneFamily` partitions `Fin q × Fin m` into the constant
function cliques. A vertex equivalence transports the partition to any
finite vertex set whose cardinality is divisible by q. Divisibility of the
complete rank-one graph implies this arithmetic condition.

`design_existence` combines both cases and extracts a natural threshold.
`design_existence_iff_binomial_divisibility` combines it with the already
proved integral divisibility criterion. These are the full qualitative
Theorem 1.1 and its standard arithmetic formulation. The printed explicit
value of the threshold remains unverified.

## Nibble at the paper parameters in every positive rank

The constant-density hypothesis gives graph-size exponent R for graph rank
R, rather than the weaker exponent 2R/3 used in the general nibble. The
new scalar estimate uses the common concentration exponent n^(1/2-epsilon).
It is positive for 0 < epsilon < 1/2. Thus `eventually_exists_dense_nibble`
includes R = 1 whenever k = choose(q,R) is at least three. Specializing
to epsilon = 1/3 and tau = 1/2 gives the paper's exact bounded-leave
exponent also in rank one with q >= 3.

For q = 2 and R = 1, a maximum matching has the following elementary
property: for two uncovered vertices u and v, their total degree is at
most twice the number of matched pairs. Otherwise two incident edges
would replace one matched pair and increase the matching. The formalized
argument counts neighbors over the disjoint matched pairs and verifies
the one-to-two augmentation directly.

Consequently minimum degree delta gives a matching with at most
max(1, |G|-2*delta) uncovered vertices. The paper's degrees near n/2 give
delta = (1-n^(-1/3))*n/2 and hence at most max(1,n^(2/3)) uncovered vertices.
Every fixed boundedness exponent beta < 1/3 follows for sufficiently
large n, in particular beta = 1/24 = 3*k*rho for k = 2.

`eventually_exists_nibble_paper_parameters_all_ranks` therefore proves the
eventual Nibble lemma for every q > R >= 1 with the printed leave exponent.
At this stage the more general `lem:nibble+` still required its q = 2 case
when the initial clique-degree scale tau may shrink with n.

## General sparse rank-one nibble for q at least three

Restrict a rank-one graph G to its m = |G| actual vertices. The restricted
host is the complete rank-one graph. All cliques of H restrict along the
same vertex embedding, preserving their degrees, decompositions, and
the cardinality of every leave.

For d >= 1, the function choose(n,d)/n^alpha is monotone for alpha <= 1.
This follows from choose(n,d) = n*choose(n-1,d-1)/d. Consequently the
original lower mean n^(-1/3)*choose(n,q-1) is at least
m^(-1/3)*choose(m,q-1), so the restricted clique-degree parameter is
admissible for the dense nibble. Relative error n^(-epsilon) is no larger
than m^(-epsilon), and the output leave scale m^(1-epsilon/(3*q)) is
no larger than n^(1-epsilon/(3*q)).

The density assumption gives m >= n^(2/3), hence m tends to infinity
uniformly over the inputs. Applying the already proved dense nibble on
Fin m yields `eventually_exists_sparse_rankOne_nibble`.
`eventually_exists_nibble_of_three_le_q` combines it with the earlier
higher-rank theorem and has the paper's general density hypotheses for
every q >= 3 and every positive graph rank below q.

## General pair nibble and the complete eventual nibble range

`exists_partial_transversal` proves Hall's theorem allowing d unmatched
indices by adjoining d dummy targets. Double counting translates lower
left degrees delta and upper right degrees Delta into this hypothesis
whenever `(Delta-delta)*|A| <= Delta*d`.

Independent vertex indicators simultaneously balance the size of one
partition class A and every neighborhood around half of their totals.
The two sides then have degrees between `(1-c)^2*D/2` and `(1+c)^2*D/2`.
Taking `d=ceil(4*c*|S|)` supplies a matching that leaves at most
`9*c*|S|+2` vertices uncovered. All statements use actual finite vertex
sets and pairs; the resulting family is a true rank-one decomposition.

For the source parameters, `D >= n^(2/3)` and `c=n^(-epsilon/2)` satisfy
the simultaneous concentration criterion. The failure bound is below one
for all sufficiently large n, uniformly over the input graph. The leave
bound is strictly below `3*n^(-epsilon/6)*n` when `0<epsilon<1/2`.
Thus `eventually_exists_general_pair_nibble` covers the formerly missing
case even when tau tends to zero at its allowed rate.

`eventually_exists_nibble_all_ranks` combines this with the previous
higher-q cases. It also treats epsilon <= 0 by taking the empty packing,
since every face degree is at most n and the requested bound is at least
3*n. The resulting statement covers every positive rank below q and all
epsilon < 1/2, hence the entire printed epsilon range. Only the explicit
size threshold remains open for the conclusion of `lem:nibble+`.

## Regularity boost at the printed complement constant

The local decoder coefficient at a clique Q depends only on
`t=|e\\Q|`. Its exact value is
`(-1)^t * (q-r).ascFactorial(t) * (r-t)!`.
The recurrence is proved directly from Pascal's identity for the
inclusion-exclusion sum. There are `choose(q,r-t)*choose(r,t)` root edges
with this value inside a decoding set of size q+r.

For each t, multiplying the absolute coefficient by `choose(q,r-t)`
gives at most the decoder multiplier `(q)_r`. Summing over t shows that
the normalized real decoders through a fixed clique have total absolute
mass at most `2^r`. Double counting the decoding assignments therefore
improves the correction budget to `2^r*choose(q,r)*epsilon`. This replaces
the old maximum-coefficient bound without changing any boundary identity.

The clique-count proof is also sharpened. Summing the successive extension
losses gives `choose(q,r)*theta` plus a finite-size term at most `q^2/n`.
The earlier bound repeated the largest step loss at every extension.
Thus every fixed relative error above `choose(q,r)*theta` is valid for all
sufficiently large n.

At `theta=2^(-3q)`, choose `epsilon=2*choose(q,r)*theta`.
The elementary bound `choose(q,r)<=2^(q-1)` makes the correction at most
one quarter, and the decoding-clique count has relative error at most
one half. All numerical margins are checked. The resulting probabilities
are in [0,1], supported on graph cliques, and have exact common edge means.
Independent sampling and binomial conversion prove
`eventually_regularity_boost_paper_constant`, with the paper's complement
constant and stronger relative n^(-1/3) output error. The explicit size
condition has now also been discharged by `regularity_boost_paper_threshold`;
the finite construction is described below.

## Source correction: the printed high-probability convention

The notation paragraph defines whp as probability greater than
`1-exp(-n/10)`. This is too strong for Lemma 5.3, not merely an estimate
missing from the formalization.

Take ordinary graphs, s=1, p=1/100, and any n >= 1000000. These parameters
satisfy `n > 2^(9*2*1)` and `p > n^(-1/2)`. Consider the event that vertex
0 is isolated and the edge {1,2} is present. Its exact probability is
`(1/100)*(99/100)^(n-1)`. The graph is nonempty, so its observed density is
positive. Its zero degree at vertex 0 contradicts typicality with any
relative error below one, including n^(-1/10).

The formal numerical comparison gives
`exp(-n/10) < (1/100)*(99/100)^(n-1)` already for n >= 2000.
For example, `exp(-100) <= 1/100` and `exp(-1/50) <= 99/100` imply the
lower bound `exp(-100-(n-1)/50)`, which exceeds exp(-n/10).
`PrintedWhpCounterexample.printed_typicality_whp_counterexample` proves
all source hypotheses and the opposite strict bound on success probability.
The counterexample does not rely on an asymptotic approximation or on
native evaluation of large finite sample spaces.

`typical_paper_whp_corrected_explicit` gives a repaired probability claim.
At p >= n^(-1/(2*h)), choose the intermediate relative error n^(-1/8).
The actual simultaneous density and neighborhood failure bound is at most
`2*(h+2)*n^(r*h)*exp(-n^(1/4)/12)`, where r is the face size. The fixed
normalization factor and polynomial probability prefactor are absorbed at
the closed threshold given below, yielding failure strictly below
exp(-n^(1/10)). The eventual interfaces now use this finite theorem.
The separate printed local size bound n>2^(9*(r+1)*h) is not asserted,
but the corrected threshold is at most the global n0 in the configuration
range needed by the paper.

The existing design-existence proof is unaffected: it used the explicit
finite probability bounds throughout, rather than the printed whp convention.
Other auxiliary probability formulations still need to be checked at their
own parameters, using valid rates instead of this false global convention.

## Source correction: multiplicity two is impossible

Lemma 6.1 (`lem:Aint`) claims a clique family of edge multiplicity at most
two that generates every integrally decomposable vector supported on a
given sparse reserve. Lemma 6.5 (`lem:flat`) claims that every sufficiently
sparse clique family has its integer span contained in such a family.
Both conclusions are false whenever `k=choose(q,r)>2`.

Here is the algebraic obstruction. Suppose a clique vector Phi supported
on a multiplicity-two family has boundary supported on just one edge e.
At every other edge, the zero boundary equation has at most two terms.
The nonzero coefficients in such an equation are an opposite pair.
For each positive magnitude t, replace coefficients of magnitude t by
their signs and all other coefficients by zero. This preserves every
zero boundary equation. Each resulting boundary is still supported on e,
and its value there has absolute value at most two. But the total boundary
of every integer clique vector is divisible by k. Since k>2, each level
has zero boundary. Reconstructing Phi from its magnitude levels shows
that its boundary was zero too.

A local decoder on q+r vertices generates `r!*choose(q,r)` copies of a
single edge. Thus no multiplicity-two family can generate all integral
vectors supported on any nonempty reserve, and no such family can contain
the integer span of all q-cliques on those q+r vertices.

For a concrete triangle example, take R={{0,1}} and J=6*1_{{0,1}}.
It is integrally decomposable using the ten triangles on {0,1,2,3,4}:
assign coefficient 2 to triangles containing both or neither of 0,1,
and coefficient -1 to triangles containing exactly one. Their boundary
is J. No family using each edge at most twice can generate J.

Adding isolated vertices preserves these obstructions. A singleton reserve
is n^(-rho)-bounded for all sufficiently large n whenever rho<1. A fixed
clique family is C*n^(-eta)-bounded eventually for every C>0 and eta<1.
`eventually_integral_absorber_paper_counterexample` and
`eventually_flattening_paper_counterexample` verify this at the printed
rho and 0.7*alpha input scales. They exclude even a multiplicity-two output
with no boundedness restriction, so changing only the output constant or
the size threshold cannot repair the claims.

The formalized main theorem is unaffected. It uses the already proved
multiplicity-16 flattening and an absorber accepting any fixed multiplicity.
No assertion of multiplicity two is assumed in that proof.

## Probability of the ordinary greedy algorithms

The success event now records the embeddings actually chosen by the process.
It requires root-preserving embeddings, pairwise disjoint new edge sets,
avoidance of the forbidden graph, and bounded edge families. In the prescribed
version it also records membership in the candidate family available at that
exact earlier history. These are measurable events, not assertions that some
unrelated successful family exists.

Write R for the graph rank, M for the number of pattern edges, and w for its
vertex count. Under n>=4*w^2, n>0, admissibility, bounded roots and forbidden
graph, and `M*(theta+M*(4*R!*theta))<=1/4`, the finite success probability is
at least
`1-M*choose(n,R-1)*exp(-2*R!*theta*n/3)`.
The new edge families are strictly `4*R!*theta`-bounded.
For prescribed candidate density eta, the corresponding failure bound is
`M*choose(n,R-1)*exp(-2*R!*theta*n/(3*eta))`, the output bound is
`4*R!*theta/eta`, and the smallness condition is
`M*(thetaB+M*(4*R!*theta/eta))<=eta/2`.

These estimates first follow from the degree-stopped trajectory laws. To
remove stopping, the formalization derives the exact probability of each
finite history from its previous-history probability and next transition
mass. If two transition systems agree along every history in an event,
they give that event the same probability. Every bounded successful family
stays below the degree cap at all earlier times, so the ordinary and stopped
greedy algorithms agree along it. This proves exact equality of their success
probabilities, also for candidates depending on earlier history.

For an explicit conservative upper density bound, set m=max(1,M) and require
`theta <= 1/(4*m*(1+4*R!*m))`. If `theta >= n^(-rho)` with rho<1, the
failure probability is eventually below exp(-n^beta) for every beta<1-rho.
At rho=1/2 and beta=1/10, `eventually_greedy_paper_probability_corrected`
therefore gives the paper's lower density range, its `2^(R+1)*R!*theta`
output bound, and probability greater than `1-exp(-n^(1/10))` for the
ordinary algorithm. It explicitly includes the bounds for the fixed root
edge families. The printed upper density constant is still not certified.

For candidate density n^(-a), root density n^(-b), and forbidden density
n^(-c), the checked conditions are `2*a<b`, `a<c`, and `b-a<1`. The ordinary
prescribed process succeeds with failure below exp(-n^beta) for every
beta<1-(b-a), uniformly in the number and values of the root embeddings and
all history-dependent candidate choices satisfying the lower bound.
This strengthens the previous eventual existence theorem to a statement
about the actual randomized construction; no explicit size threshold is claimed.

## Checked components of the explicit threshold

Write `A=(2*q)^r*(6*choose(q,r))^2` and `n0=(4*q)^(90*q*A)`.
The formal definitions are `paperInverseAlpha` and `paperSizeThreshold`.
`paperAlpha` and `paperRho` agree exactly with the parameters in the source,
with `alpha*A=1` and `n0^alpha=(4*q)^(90*q)`.
The basic estimates include `0<alpha<=rho<=1/36` and `n0>1`.

If the exchange has M edges with `M<=3*(2*q)^r*choose(q,r)^2`, then
`12*M<=A`, so `M<A` and `alpha*M<=1/12`. Setting `u=20*q^2*A*M` gives
`u<=2160*q^2*(2*q)^(2*r)*choose(q,r)^4`. For q>r>=1, elementary power and
binomial bounds give
`2^(5*q)*(4*q)^r*u <= (4*q)^(6*q+5) < (4*q)^(9*q)`.
Raising to `10*A=10/alpha` proves exactly the strict inequality highlighted
in Section 10:
`(2^(5*q)*(4*q)^r*u)^(10/alpha) < n0`.
This verifies the numerical assertion, not the false multiplicity-two lemma.

The source's strict margin `choose(q,r)*alpha<rho/2` holds for r>=2.
For r=1 it is instead exactly `choose(q,1)*alpha=rho/2`; both facts are
proved. The separate rank-one construction avoids any need for strictness
in that case.

For every n>=n0 and t>=0, the exact normalization gives
`n^(-alpha*t) <= (4*q)^(-90*q*t)`. In particular,
`n^(-alpha/4) <= 2^(-3*q)/2`, and
`n^(-rho)+n^(-alpha/4) <= 2^(-3*q)`.
The usual greedy lower density requirement also holds for every exponent
gamma<=rho whenever n>1: `n^(-1/2)<n^(-gamma)`.

Independently of any asymptotic estimate, a theta-bounded rank-R graph on
n>=2*R vertices has at most `2*theta*choose(n,R)` edges. This is proved by
summing its face degrees and using the exact adjacent-binomial identity.
Thus a complement bounded by theta<1/4 leaves more than half the edges.
Since n0>=(4*q)^2>=2*r, `paper_threshold_regular_host` supplies both the
boost complement bound and the nibble density after removing the reserve
and absorber. `eventually_hasDecomposition_complete_succ` now uses this
finite lemma and regularity boosting at the printed complement constant.

Finally, the exact logarithm is
`log(n0)=3240*2^r*q^(r+1)*choose(q,r)^2*log(4*q)`.
For q>=2, `log(4*q)<=3*log(q)`, yielding the explicit coefficient
`9720*2^r` in the claimed big-O scale. The formal big-O statement varies q
with r fixed; it does not hide an assertion that the constant is uniform in r.

The remaining quantitative task is to verify every finite construction
criterion at n>=n0 (or state and prove a corrected explicit overall bound).
The scalar inequalities above alone do not certify all construction thresholds.
The full Boost, reserve, and Cover thresholds have now been discharged as
described below, as has the full Lemma 2.4 nibble. Absorber, colouring,
flattening, and the broader Lemma 9.1 thresholds remain.

## Full explicit regularity boost

`regularity_boost_paper_threshold` proves Lemma 2.3 with the printed n0.
The stronger theorem `regularity_boost_explicit` works already for
`n >= (4*q)^(90*q)`, independently of the large inverse-alpha factor in n0.
It uses the printed complement bound 2^(-3q), produces an actual clique
family contained in the graph, and gives error at most
`n^(-1/3)*choose(n,q-r)/2` around `choose(n,q-r)/2`.
The source allows twice this error.

The two rooted-count conditions are now finite. The host-size bound gives
`q^2*2^(3*q)<=n` and `8*q^2<=n`. These dominate the finite-size losses for
the initial q-clique count and the decoding (q+r)-clique count. The latter
has complement loss at most one quarter. Combined with the exact decoder
mass bounds, this produces valid fractional coefficients and exact common
edge means, with no eventual hypothesis.

For the sampling step, write `d=q-r` and use relative error n^(-2/5).
The same host-size bound gives `d!<=n^(1/10)`. The finite concentration
exponent is therefore at least n^(1/10)/12. The proved inequality
`6*n^r*exp(-n^(1/10)/12)<1` discharges the simultaneous sampling criterion.
Its proof is fully numerical: with x=n^(1/20), one has `x>240*r+60`,
`log(n)<=20*x`, and `log(6)<=5`. Consequently the logarithm of the
polynomial prefactor is strictly smaller than x^2/12.

The binomial conversion is also finite: the size condition gives
`(1-n^(-2/5))*n^d/d! <= choose(n,d)`, `n^(-2/5)<=1/2`, and
`4*n^(-2/5)<=n^(-1/3)`. These imply the stated normalized output error.
The previous eventual Boost theorem is now a corollary of this finite result.

The main existence proof calls `regularity_boost_paper_threshold` directly.
It no longer invokes an additional eventual threshold for boosting, nor the
former eventual density and exponent-loss estimates for its input graph.
The reserve, Cover, and Lemma 2.4 nibble thresholds are now also discharged
below. The absorber threshold still needs to be made explicit for the
quantitative main theorem.

## Full explicit reserve and Cover

`exists_reserve_paper_threshold` proves Lemma 2.1 for every n>=n0.
It constructs a reserve with strict n^(-rho) boundedness and at least
`n^(-K*rho)*n^(q-R)` punctured q-cliques at every rank-R edge, including
edges inside the reserve. Thus it strengthens both the printed factor-two
degree bound and the domain of the extension-count conclusion.

The exact identity `n0^rho=(4*q)^(90*q*(2*q)^R)` gives
`(4*q)^(10*(q+K)) <= n^rho`, where K=choose(q,R). This dominates all fixed
normalization, size, factorial, and clique-count losses. Sampling at
`p=n^(-rho)/4` with relative error `c=n^(-1/8)` gives density between
`n^(-rho)/8` and `n^(-rho)/2`. Its typicality error is
`(4+2*K*2^K)*c <= 1/4`.

The simultaneous failure estimate is bounded by
`2*(K+2)*n^((R-1)*K)*exp(-n^(1/2)/12)`, which is strictly below one
at n0. With x=n^(1/4), the proved inequalities are
`x>48*(R-1)*K+24*K+36`, `log(n)<=4*x`, and
`log(2*(K+2))<=2*K+3`. These give the finite probability margin without
assuming the paper's false global whp convention.

`exists_clique_cover_paper_threshold` proves Lemma 2.5 for every n>=n0.
Write a=K*rho. The prescribed greedy construction uses candidate density
n^(-a), root density n^(-3*a), and an empty forbidden graph. The inequality
`2*(K+4*K^2*R!) <= n^a` verifies its finite smallness condition. Since
a<=1/36, its simultaneous failure estimate is bounded by the same finite
tail as reserve sampling. The resulting cliques are actual candidates,
contain their assigned leave edges, and are pairwise edge-disjoint. Their
union is a graph G with L contained in G contained in L union R, and they
form a true decomposition of G with exactly |L| cliques.

`exists_reserve_cover_decompositions_paper_threshold` combines the two
constructions. The main theorem now calls it directly. The finite nibble
below is also integrated. The absorber uses separate explicit assembly and
flattening thresholds; all other stages in the main assembly hold at the
printed n0.

## Full explicit Lemma 2.4 nibble

`exists_nibble_paper_threshold` proves Lemma 2.4 for every n>=n0 and every
q>R>=1, including the pair case. The assumptions match the printed lemma:
G has more than half the complete graph's edges, H consists of q-cliques
in G, and every graph edge has H-degree within relative n^(-1/3) of
`choose(n,q-R)/2`. The conclusion is an actual packing contained in H,
with a strictly n^(-3*K*rho)-bounded leave.

For K=choose(q,R)>=3, put a=n^(-1/9), p0=n^(-1/(9*K)), and
D=choose(n,q-R)/2. The finite binomial bounds give
`|G| >= n^R/(4*R!)` and `D >= n^(q-R)/(4*(q-R)!)`.
The common constant `2^24*q^2*K^6*q!` is at most n^rho at n>=n0.
It dominates every fixed coefficient in the comparison, clique-count,
stopping, and concentration records. The stopping-exponent inequalities
are verified separately, including `rho+2/(9*K)<=1/9` and
`rho<=2/(9*K)`.

All three concentration exponents are therefore at least n^(1/6). The
simultaneous failure bound `5*n^(2*R)*exp(-n^(1/6))` is strictly below one:
with x=n^(1/12), one has x>24*R+4, log(n)<=12*x, and log(5)<=4.
The proved finite process criterion constructs the actual supported packing;
no eventual probability estimate or assumed random outcome is used.
Finally, `1/(9*K)=4*K*rho` and the same threshold absorb the factor three
in the output `3*p0`, giving exactly the required n^(-3*K*rho) bound.

When q=2 and R=1, the finite maximum-matching estimate leaves at most
max(1,n^(2/3)) vertices. At n>=n0 this is strictly smaller than n^(23/24),
which is the required bound because 3*K*rho=1/24. Thus every positive
rank is included in the finite theorem.

The main proof uses this finite packing construction directly and no longer
invokes an eventual nibble threshold. This closes Lemma 2.4, not the broader
Lemma 9.1 with variable epsilon and polynomially small graph and degree
densities; its printed threshold remains a separate obligation.

## Finite greedy placements for the absorber

`exists_absorber_greedy_family_paper_threshold` constructs actual embeddings
at density `theta=A*n^(-alpha/3)` for every n>=n0. The admissible pattern's
vertex and edge counts, and A, may each be as large as `(4*q)^(8*q)`;
the only lower bound on A is A>=1. The forbidden graph and root families
must have the stated theta bound. The output avoids the forbidden graph,
has pairwise disjoint new-edge images, and bounds each new-edge family by
`4*R!*theta`. The number and values of the roots are unrestricted.

The exact alpha normalization gives `(4*q)^(30*q)<=n^(alpha/3)`.
For a pattern with M edges,
`4*M*(1+4*M*R!) <= (4*q)^(17*q+2)`. Multiplying by A still leaves an
exponent at most 25*q+2<=30*q, so the finite smallness condition holds.
The vertex condition `4*|W|^2<=n` follows from the same printed threshold.
Also theta>=n^(-1/2), and M<=n, so the simultaneous failure estimate is
bounded by the already checked finite Boost tail.

This is an actual finite construction with explicit input bounds, not merely
an eventual numerical estimate. The exchange carrier, cancellation constants,
and decoder/splitting interface at alpha/2 are now checked below. The sparse
initial integral-generator threshold remains open. Multiplicity-16 flattening
now has an explicit larger threshold; its current cost estimate cannot fit n0.

## Finite decoder placements and bounded representations

`exists_clique_placement_paper_threshold` instantiates the uniform finite
greedy theorem for a complete rank-R pattern on any s vertices with
R<=s<=2*q. For a graph B bounded by n^(-alpha/3), it constructs one s-clique
through each edge of B, with that edge as its only edge in B. The placed
cliques are pairwise edge-disjoint, and their union is bounded by
`(1+4*R!*choose(s,R))*n^(-alpha/3)`. These are actual placements for every
n>=n0, including the empty input case.

Taking s=q+R gives `exists_sparse_local_decoders_paper_threshold`.
All q-subsets of the placed regions form a family D with edge multiplicity
at most choose(q,R). Each edge of B has an integral decoder on D, with
multiplier `R!*choose(q,R)` and coefficient bound `2^q*R!`. The support
graph and clique-family degree bounds are proved at this same finite size.

`exists_bounded_multiplicity_representation_family_paper_threshold` augments
any supplied generating family D1 of edge multiplicity at most M by one
such decoder family D2. Simultaneously for every leave L contained in B
and generated by D1, it gives an exact integer representation supported on
D1 union D2 with every coefficient bounded in absolute value by
`(M+1)*2^q*R!`. In particular the proved multiplicity-16 generators require
coefficient bound `17*2^q*R!`. No bound on their original integer
representations is assumed. The exchange carrier, finite cancellation stages,
and decoder/splitting interface at alpha/2 are now checked below. Constructing
the sparse multiplicity-16 generating family at n0 remains open.

## Finite separated splitting

`exists_absorber_separated_greedy_family_paper_threshold` adds disjoint free
vertices for every related pair of roots. At theta=A*n^(-alpha/3), it permits
pattern vertex count, edge count, and prior-conflict count at most
`(4*q)^(8*q)`, with `2*A <= (4*q)^(8*q)`. The extra finite size condition
`4*|W|*(d*|W|)<=n` is proved at n0. Candidate density one half gives the
output constant `8*R!*theta`.

`exists_splitting_family_paper_threshold` applies this construction to all
positive and negative coefficient slots. Each root occurs at most 2*C times,
and each root conflicts with at most K*(2*C*M) prior roots, where M bounds
the input edge multiplicity. The resulting family has all properties needed
by the existing signed-representation and elimination proofs, including
disjoint free vertices whenever two roots share an edge.

For the multiplicity-16 generators, the decoder normalization parameters are
`C=17*2^q*R!`, `M=16+K`, and `A=M*(2+4*R!*choose(q+R,R))`.
`AbsorberWorkingParameters` proves both required inequalities
`4*C*A <= (4*q)^(8*q)` and `K*(2*C*M) <= (4*q)^(8*q)`.
It also bounds the paper's exchange edge count by `(4*q)^(2*q)`.
Thus no further smallness or probability hypothesis remains for these parameters.

`exists_decoder_splitting_paper_threshold` connects the stages: starting from
a supplied multiplicity-16 family supported on a graph bounded by
n^(-alpha/3), it constructs the augmented graph and clique family, all
bounded integer representations, and a splitting family at the verified
constant factor. `exists_exchange_decoder_splitting_paper_threshold` now
constructs the exchange system too; no carrier size hypothesis is needed.
The entire gluing construction preserves the stronger bound
`|W| <= 6*q^2*choose(q,R) <= (4*q)^(2*q)`. Choosing a distinguished negative
clique also gives a cancellation pattern with the same vertex bound.

## Finite cancellation and the accumulated absorber coefficient

Small exchange patterns permit stronger finite greedy estimates. With at most
`(4*q)^(2*q)` vertices and edges, and at most `(4*q)^(8*q)` prior conflicts,
the density coefficient may be as large as `(4*q)^(24*q)`. The working
exponent can be any rho with alpha/3<=rho<=1/2. In the smallness estimate,
`4*M*(1+8*M*R!) <= (4*q)^(5*q+2)`, so the product exponent is at most
29*q+2<=30*q. The same finite tail estimate constructs actual embeddings.

`exists_two_stage_elimination_paper_threshold` constructs both cancellation
families from the splitting family. Its final negative host has a true
decomposition, avoids the original graph, and has the exact accumulated
density bound. Both input densities are explicit scalar expressions.

`AbsorberCoefficientBounds` checks those expressions at C=17*2^q*R!,
M=16+choose(q,R), the decoder normalization A, and the paper's exchange
edge bound. With K0=2*C*M+2 and K1=K0+4*choose(q,R)*K0^2+2, it bounds the
whole splitting-plus-two-cancellation coefficient by `(4*q)^(22*q)`.
The proof groups all factors into one monomial; the q=2 case is checked
exactly, and q>=3 has a uniform power bound. Doubling the initial density
still leaves both cancellation inputs below `(4*q)^(24*q)`.

The final factor two accommodates a union of the reserve and generator
support. It satisfies
`2*Kfinal*n^(-alpha/2) <= n^(-alpha/4)` at every n>=n0, since
`2*Kfinal <= (4*q)^(22*q+1) <= n^(alpha/4)`.
`exists_normalized_two_stage_elimination_paper_threshold` applies these
bounds to actual patterns and constructs the required negative host from
splitting at density `2*splittingFactor*n^(-alpha/2)`.

The decoder/splitting interface at alpha/2 is now checked below. The finite
absorber still requires its sparse generating family. Initial generation
now uses the finite colour system and explicit assembly bound described below;
the explicit flattening threshold is larger than n0; the full printed design threshold is not asserted.

## The finite absorber from supplied generators

The ordinary greedy construction now works for alpha/3<=rho<=1/2 with the
same 4*R! output constant; imposing free-vertex separation uses 8*R!.
These estimates construct decoder regions, their local integer decoders,
and bounded representations at rho=alpha/2. An input graph bounded by
`2*n^(-alpha/2)` yields normalized graph and clique-family bounds
`2*A*n^(-alpha/2)`, where A is the previously checked decoder factor.
The augmented family has multiplicity at most 16+choose(q,R), and every
represented leave has coefficients at most 17*2^q*R!.

`exists_normalized_splitting_family_half_alpha` constructs all signed slots,
with the required private-vertex separation, at density
`2*splittingFactor*n^(-alpha/2)`. Both cancellation stages then give the
fixed decomposable negative host with density n^(-alpha/4). This host absorbs
every bounded representation on the augmented family simultaneously.

`exists_absorber_for_generated_leaves_paper_threshold` combines these steps.
For every n>=n0, a multiplicity-16 family supported on a graph bounded by
`2*n^(-alpha/2)` has one disjoint n^(-alpha/4)-bounded host absorbing all
its generated leaves. There are no assumed decoder, exchange, placement,
or cancellation constructions.

`exists_sparse_absorber_paper_threshold_of_generators` specializes this to
the paper's reserve bound n^(-rho), adjoining the support of a supplied
n^(-alpha/2)-bounded generating family. It gives the full absorber property
for every divisible leave. The main eventual absorber theorem now calls
this finite construction directly. The sparse multiplicity-16 generating
family now uses finite colour construction and the explicit integral-assembly
and flattening thresholds described below.

## Finite flattening and its cost obstruction

Each multiplicity-reduction round is now constructed at n0, uniformly while
the density lies between n^(-3alpha/5) and n^(-alpha/2). This includes generator
splitting, actual balanced representatives for groups of size at most sqrt(n)+1,
and indexed elimination placements. The round preserves every generated
integer vector and reduces multiplicity by x -> max(16,2*floor(sqrt(x))+4).
Its uniform degree multiplier is the explicit integer

`C=(7+4*(q-r)+24*(r+1)!*E)*(3+8*(r+1)!*E)`,

where r is the face rank and E=3*(2q)^(r+1)*choose(q,r+1)^2.

The accumulated C^k cost cannot simply be assumed to fit n0.
`uniform_flattening_round_cost_obstruction` proves this for q=3 and edge
rank 2, for any actual exchange patterns. At n0, the recurrence needs at
least 11 rounds; the per-round uniform coefficient is at least 8109; and
`8109^11 > 12^27 = n0^(alpha/10)`. This disproves the current iteration-cost
certificate at n0, not the existence of a better flattening construction or
the existence of designs at that size.

`exists_flattening_iterations_of_log_bound` supplies a finite alternative.
If `(K+3)*log(C) <= epsilon*2^K*log(4)` and n>16*4^(2^K), it constructs
enough rounds with C^k<=n^epsilon. A fully explicit conservative choice is
`K=max(4,ceil(2*log(C)/(epsilon*log(4))))`.

With epsilon=alpha/10, `finiteFlatteningThreshold` is the maximum of n0
and this explicit iteration threshold. Above it,
`exists_sparse_flattening_explicit` constructs an n^(-alpha/2)-bounded family
of multiplicity at most 16 containing the entire integer span of any
n^(-3alpha/5)-bounded input. `exists_flattened_paper_input_explicit` includes
the paper's full coefficient `2^(q+2)*(4q)^R*u*n^(-7alpha/10)`.
The chosen corrected threshold is proved strictly larger than n0 for triangles.

The main bounded-generator theorem now calls this finite flattening result.
The initial sparse integral-generator construction now works at n0 by the
sharper coefficient bound below. The printed global size bound
remains unverified, as do
the other auxiliary quantitative statements listed above.


## Finite focusing, decoding, and integral generation from the colour system

At the printed n0, the good graph satisfies
`density(G)^s >= (1/2)*(n^(-alpha))^s` for every s<=choose(q,R).
The proof keeps the small relative density error before taking powers.
Using only density(G)>=n^(-alpha)/4 would instead lose 4^s, which is
unnecessarily expensive at the paper's parameters.

Set a=alpha*(choose(q,R)-1)+alpha/2. The proof checks both exponent margins
rho-2a>=alpha and rho-a>=alpha, as well as the factorial, prescribed-greedy
smallness, and finite failure bounds. Consequently the actual focusing
cliques form an n^(-7alpha/10)-bounded family at n0. This single family
focuses every supported integral vector and preserves integral decomposability.
The existing general cover proof now exposes its finite numerical criterion;
the older asymptotic theorem uses that same construction.

The decoder augmentation factor is at most `(4q)^(2q+1)`.
If the input generator coefficient C satisfies C+1<=(4q)^(6q), focusing and
decoding now produce an (n^(-3alpha/5)/2)-bounded family at n0. The full
constructed palette coefficient meets this cap, as proved below. For an
arbitrary larger colour-system coefficient,
`finiteGeneratorAssemblyThreshold q r C` supplies the explicit bound

`max(n0, ceil(max(1,C))^(20*paperInverseAlpha(q,R)))`,

where r=R-1. Above this threshold the original C*n^(-7alpha/10) input is
n^(-13alpha/20)-bounded, and the remaining alpha/20 margin pays for the
combined decoder cost. The resulting family has the same n^(-3alpha/5)
bound needed by finite flattening.

The bridge argument is also finite at n0. Its candidate count survives
excluding both prescribed cliques, and its colour avoidance gives the
integer pair-difference identities. The clique-residual argument then
generates every integrally decomposable vector supported on the colour graph.
Modular generation and the constructed decoders lift this to exact integral
generation of every supported reserve vector.

`exists_integral_generators_from_system_explicit` implements all these
steps from an actual coloured modular system, its observed-density and
deletion bounds, extension properties, and modular span. It assumes no
integral-generation conclusion. The main bounded-generator proof now uses
the sharper n0 assembly proved below and the previously verified finite flattening.
The colour system is now constructed at n0 with explicit palette sizes, as
described below. No additional eventual colour-construction input remains.
The printed global threshold and broader auxiliary claims remain unverified.


## Finite typical host and sparse modular generators

The typical host and modular selection no longer require unspecified
largeness in the main proof. `exists_sparse_modular_generators_paper_threshold`
constructs both at every n>=n0, for every h between choose(q,R) and the
exchange edge bound `3*(2q)^R*choose(q,R)^2`, and every positive modulus
N<=R!*choose(q,R). In particular it applies to the actual decoder modulus.

The host is `(n^(-1/10),h)`-typical and has relative density error n^(-1/10)
around n^(-alpha). Sampling with error n^(-1/8) leaves an n^(1/40) margin
for the full factor 4+2*h*2^h. The relation 12*h<=paperInverseAlpha makes
that margin available at n0. An explicit simultaneous failure bound below
one constructs the host. The new finite corrected probability theorem also
gives failure below exp(-n^(1/10)) at n0, and applies to the larger density
range p>=n^(-1/(2*h)). It does not assert the source's refuted exp(-n/10) rate.

For modular selection the cap is floor(n^(1-7alpha/10)). Its rounding costs
at most a factor two, and

`16*choose(q,R)*choose(q,R-1)*N <= (4q)^(2q+2) <= n^(alpha/10)`.

This supplies both the saturation and deletion budgets. The constructed
generators are 2^q*n^(-7alpha/10)-bounded and number at most N*|K|.
At most an n^(-alpha/10) fraction of cliques is saturated, and at most that
fraction of host edges is removed. Every good edge has the expected number
of unsaturated cliques, with relative error strictly below n^(-alpha/10).
The compatibility interface uses the observed host density. The stronger
reference-density binomial counts and strict source saturation/deletion
bounds are now proved at n0 as described below, without changing the generator
bound or the modulus range.

`PaperRainbowGeneratingSystem` now supplies this finite host to the actual
rainbow experiments. `PaperIntegralGeneratorExistence` and the main design
proof use this revised construction. The two colour experiments now also
have finite proofs at n0, including repetition counts and probability estimates.
Assembly uses an explicit palette-dependent coefficient; flattening uses
an explicit larger threshold. All subsequent absorber/nibble/cover stages
are finite at n0.
The printed full design threshold, sharper probability claims, and other
auxiliary statements remain open as listed above.


## Finite simultaneous rainbow extensions

`exists_many_rainbow_extensions_paper_threshold` constructs an actual
palette at every n>=n0 for any pattern with at most h edges and at most
(4q)^(2q) vertices, where h<=3*(2q)^R*choose(q,R)^2. No pattern edge may
lie wholly in the prescribed root. The supplied host is typical through h,
with the verified reference-density and good-edge deletion bounds.
For every root embedding, the palette provides more than
`(3/8)*density(G)^|E|*n^(|W|-|F|)` rainbow extensions simultaneously.

The proof now uses a linear error estimate instead of the earlier H*2^H
loss. If 24*H*epsilon<=1, the powered joint probability is at most
`(1+24*H*epsilon)*p^(2*M)` for M<=H. Joint permutation probabilities at
error n^(-alpha/6), and the good-graph deletion estimate, give the needed
marginal/joint error n^(-alpha/12). The resulting moment error is
n^(-alpha/24), as is the geometric collision contribution. The per-root
failure probability is at most 8*n^(-alpha/24).

The explicit independent-trial count is
`paperColourTrialCount(q,R,f)=48*(f+1)*paperInverseAlpha(q,R)`.
At n0, the union bound for all at most n^f root maps is at most n^(-1)<1.
Thus one family of trials works for all roots, and grouping their colours
constructs the actual rainbow palette. The count does not depend on n.

Joint-permutation bounds also apply to clique subfamilies of every size
k<=q, not just edges. The next section records their use in the far-clique
generation experiment and the integration of all finite palettes into the
main generator proof. Other printed quantitative claims remain open.


## Finite root palettes and far-clique generation

The three prescribed-root patterns are now instantiated at n0: punctured
cliques, a single exchange base, and a pair of roots meeting in one edge.
`paperExtensionPaletteSize` records their exact combined palette cardinality.
The actual small-carrier exchange supplies the vertex-size hypothesis; it
is not an additional assumption on the unconditional main theorem.

For the unsaturated clique family D, finite relative counting and deletion
bounds give

`density(D) >= (1/4)*n^(-alpha*K)`, where `K=choose(q,R)`,

and marginal/joint errors n^(-alpha/12) relative to density(host)^K.
Keeping the host density power before estimating it avoids an exponential
loss in this marginal coefficient.

The near-frame construction counts all compatible frames and all their
completions. Its factorial coefficient is bounded using K^2<=h, q<=K, and
`(4q)^(10*(q+h)) <= n^(1/40)`. The resulting candidate family has size at least

`(3/4)*n^(-(alpha*(K-1)*K+1/40))*n^(|W|-q)`.

The same bound holds for every root map, using all extensions as dummy
candidates when the base is not rainbow. For far cliques,
`alpha*(K-1)*K+2*alpha*K*|far| <= 5*alpha*h <= 5/12`.
This leaves ample room for both the extra 1/40 loss and the n^(-alpha/24)
collision and second-moment errors. The generalized finite colour theorem
therefore gives per-root failure at most 8*n^(-alpha/24), and exactly
`48*(q+1)*paperInverseAlpha(q,R)` independent trials suffice for all base maps.
Successful counts yield actual exchange embeddings whose near and far
replacement cliques are generated by the two corresponding colour families.

`exists_paper_rainbow_generating_family_threshold` and
`exists_paper_avoiding_rainbow_generating_system_threshold` construct the
full modular colour system at n0. The main proof now uses these results.
For a supplied exchange and elimination pair,
`exists_paper_integral_generators_with_exchange_explicit` constructs the
n^(-3alpha/5)-bounded integral generating family above
`finiteGeneratorAssemblyThreshold` with the explicit
`paperIntegralGeneratorCoefficient`. Its eventual wrapper uses only this
stated threshold, with no additional asymptotic construction lemma.

The coefficient is now bounded uniformly and all stages are combined in
the closed corrected threshold below. The printed n0 is still not certified: the present flattening cost already requires a
strictly larger bound for triangles. Stronger source probability claims
and the remaining small-clique, small-positive-error cases for the original constant
of Lemma 9.1 remain separate obligations; a uniform replacement, now improved from constant 432 to 16, is proved below.


## A uniform explicit corrected design threshold

The generator coefficient no longer depends on a choice of exchange or
palette. Write R for the edge size and set

- K=choose(q,R), A=paperInverseAlpha(q,R), H=3*(2q)^R*K^2;
- L=48*(2q+1)*A and U=3*(L*H+1);
- C=((2*K+1)*U+L*H+1)*2^q.

All root sizes are at most 2q, all relevant new-edge sets have at most H
edges, and the number of far cliques is at most H. These inequalities bound
the full generator coefficient by C. The natural ceiling in the assembly
threshold is therefore also at most C.

`integralGeneratorThreshold q (R-1)` is exactly `max(n0,C^(20*A))`.
`exists_paper_integral_generators_explicit` constructs the initial
n^(-3alpha/5)-bounded family above this threshold, choosing its actual small
exchange and elimination pair internally. No exchange, palette, modular span,
or eventual existence assumption is supplied by the caller.

`boundedIntegralGeneratorThreshold` takes the maximum of that threshold and
the previously proved `finiteFlatteningThreshold`. It yields the complete
multiplicity-16 integral generating family and the sparse absorber.
Combining the absorber with finite reserve, Boost, nibble, and Cover gives
`hasDecomposition_complete_succ_explicit` in rank at least two.

Finally, `correctedDesignThreshold q R` is zero for R=1 and otherwise this
combined threshold. `design_existence_explicit` proves design existence above
it for every q>R>=1. The original qualitative theorem now uses this explicit
witness. The numerical binomial-divisibility equivalence is also proved
above `max(correctedDesignThreshold(q,R),q+R)`.

`correctedDesignThreshold_triangle_gt_printed` proves that the corrected
bound is strictly larger than the paper's n0 for triangles. This is a
comparison of sufficient bounds, not a counterexample to designs existing
at the smaller bound. The original printed n0, stronger auxiliary probability
claims, and the constant-3 bound in the small-clique, small-positive-error cases
of Lemma 9.1 remain unverified. The uniform replacement is proved below, and subsequently improved from 432 to 16.


## Finite Section 9 nibble at sparse densities and variable error

`exists_sparse_nibble_all_ranks_paper_threshold` proves the full packing
conclusion and polynomial density assumptions of Lemma 9.1 at the printed
n0, in every positive rank, throughout

`1/(12*choose(q,R)) <= epsilon <= 2/5`.

Here R is the edge rank and K=choose(q,R). The exact identity
`3*K*paperRho(q,R)=1/(12*K)` is proved. Above this error cutoff,
with a=n^(-epsilon/3) and p0=n^(-epsilon/(3*K)), the paper's rho margin
pays for all finite comparison coefficients. The construction has no
assumed typical graph, random outcome, or eventual parameter estimate.
The allowed input densities are exactly phi>=n^(-R/3) and tau>=n^(-1/3).
The resulting leave is 3*n^(-epsilon/(3*K))-bounded.

A common numerical criterion only requires |G|>=n^(19/20)/(4*R!).
For R>=2 the input density and finite binomial estimate imply this bound.
The concentration parameter uses cg=n^(-1/20)/(4*R!), so a uniform linear
lower bound cg*n with constant cg is not silently assumed. The additional
n^(1/20) in the face coefficient is absorbed explicitly. All count, edge,
and face tracks have concentration exponent at least n^(1/10), and the
finite simultaneous failure estimate is less than one at n0.

For R=1 and q>=3, graphs below the size criterion already satisfy the
stated leave bound with the empty packing. Larger graphs use the same
finite clique-removal criterion in the original vertex set; no change
of ambient size and no additional threshold is needed. For q=2, finite
sampling estimates give the near-regular pair packing. The older eventual
pair theorem now reuses its extracted finite numerical criterion.

`exists_nibble_of_nonpositive_error` handles epsilon<=0 at every n>=1.
The general eventual all-ranks theorem selects the finite n0 proof whenever
its parameters lie in a verified constant-3 range, and retains the previous
eventual argument otherwise.

## Finite Section 9 without an error cutoff

`exists_sparse_nibble_paper_threshold_weaker` proves a corrected version of
Lemma 9.1 at exactly n0, for every epsilon<=2/5 in every positive rank, with
leave bound

`432 * n^(-epsilon/(3*K))`.

All the source's polynomial density assumptions and clique-degree hypotheses
are unchanged. The proof constructs an actual packing and does not assume
any numerical comparison, random outcome, or eventual estimate. The constant
432 is a sufficient bound from the existing process estimates; it is not
asserted to be optimal. This implements the authorized option of weakening
constants to handle the full error range.

The five floor comparisons are now separated from the density estimates in
`NibbleFloorConditions`. For K>=3, polynomial-versus-power induction proves

- 256*K^2 <= 432^K;
- 16*K^3 <= 432^(K-2);
- 128*K <= 432^(K-1).

If p0=n^(-epsilon/(3*K))<=1/432, these bounds and a=p0^K imply all five
floor conditions. The previously checked density and concentration estimates
then give the stronger 3*p0 leave. If p0>1/432, the empty packing suffices
for 432*p0. Equality belongs to the process branch, preserving strict graph
boundedness. The pair case is handled separately as described next.

The original constant 3 also holds without an error cutoff in two regimes.
`exists_pair_nibble_paper_threshold` covers q=2, R=1: for p0<=1/3 the sampling
parameter is c=p0^3, so c<=1/4 and 9*c<=p0 without a lower bound on epsilon.
For p0>1/3 the empty packing suffices. Nonpositive epsilon is included.

`exists_sparse_nibble_of_large_clique_paper_threshold` covers every K>=15.
For p0<=1/3, induction gives 256*K^2<=3^K, 16*K^3<=3^(K-2), and
128*K<=3^(K-1). The variance comparison follows from 128/9<=K. Again,
p0>1/3 is the trivial leave case. The construction covers every positive
edge rank, including rank-one graphs below the general size criterion.

`exists_sparse_nibble_paper_threshold_of_covered_parameters` combines the
exact constant-3 ranges: epsilon<=0, epsilon>=1/(12*K), pairs, or K>=15,
always assuming epsilon<=2/5. The remaining finite case for the original
constant is precisely 3<=K<=14 and 0<epsilon<1/(12*K); the corrected constant
432 covers it; the scaled-stopping argument below improves this to 16.
No counterexample to the original lemma is asserted.

## Finite corrected high-probability typicality

Let r be the face rank and h>=1 the number of neighborhood tests allowed.
The sampled graph has edge rank r+1. Set

`M = max(4+2*h*2^h, 48*r*h+24*h+37)`,
`T = correctedTypicalityThreshold(r,h) = M^40`.

For every n>=T and every p>=n^(-1/(2*h)),
`typical_paper_whp_corrected_explicit` proves that, with probability greater
than 1-exp(-n^(1/10)), the p-random graph simultaneously has relative density
error at most n^(-1/10) and is (n^(-1/10),h)-typical. The actual failure
probability and the corresponding existence theorem are also proved. No
size, normalization, or probability condition is left to a caller beyond
this explicit threshold.

The proof uses c=n^(-1/8). The growth M<=n^(1/40) absorbs the density-to-
observed-typicality factor 4+2*h*2^h. The scalar tail proof bounds the logarithm
of the polynomial prefactor by x^2, where x=n^(1/40), and compares this with
n^(1/4)/12-n^(1/10). This gives a strict finite probability bound rather
than invoking an asymptotic limit.

`correctedTypicalityThreshold_le_paperThreshold` proves T<=n0 whenever
q>r+1 and h<=3*(2*q)^(r+1)*choose(q,r+1)^2. Consequently
`typical_paper_whp_corrected_paper_threshold` proves the corrected probability
claim at n0 through the full exchange size, at the full source density range.
`exists_typicalGraph_paper_density_threshold` supplies the corresponding
actual graph. All four pre-existing eventual probability interfaces now
use the explicit threshold instead of separate eventual estimates.

The rate exp(-n/10) remains refuted. The full local-threshold result below now
certifies 2^(9*(r+1)*h) in every positive edge rank, including all smaller
products. The later joint colour results
also settle all four colour assertions with a corrected finite probability.
For KSG, both the observed-density construction and the source's
reference-density bounds now have corrected finite probability proofs
in the modulus range used by the main construction.

## Corrected probability of the modular-generator construction

`modular_generators_paper_whp_corrected` strengthens the existing finite KSG
construction from existence of one host to a statement about the sampled
host itself. At n>=n0, with p=n^(-alpha), probability greater than
1-exp(-n^(1/10)) is assigned to graphs that are typical through the supplied
configuration size, have the required density, and admit the complete
`ModularGeneratingData` with its proved sparse generator, saturation,
deleted-edge, and accurate unsaturated-clique bounds.

This holds for every 0<N<=R!*choose(q,R) and
choose(q,R)<=h<=3*(2*q)^R*choose(q,R)^2. The proof discharges
p>=n^(-1/(2*h)) using alpha*h<=1/12, then applies the deterministic
modular-selection theorem to every graph in the finite typicality event.
No randomized generator-selection outcome is assumed. The existing
`exists_sparse_modular_generators_paper_threshold`, used by the main
construction, now extracts its witness from this positive-probability event.

The original probability interface retains its observed-density factorial
main term for compatibility. The following stronger interface now proves
the source's reference-density binomial main term and strict absolute
saturation bound. Neither theorem reinstates the false exp(-n/10) convention.

## Reference-density KSG bounds at the paper threshold

Write R for the edge rank, K=choose(q,R), p=n^(-alpha), and
epsilon=n^(-alpha/10). `exists_reference_modular_generators_paper_threshold`
constructs the same type of modular-generating data but now proves exactly:

- fewer than epsilon*|G| deleted host edges;
- fewer than n^(-alpha/10-K*alpha)*choose(n,q) saturated cliques;
- for every good edge, unsaturated clique count with relative error strictly
  below epsilon around n^(alpha-K*alpha)*choose(n,q-R);
- the original 2^q*n^(-7alpha/10) generator bound, and generator cardinality
  at most N*|G|.

The input is any supplied (n^(-1/10),h)-typical host with the proved relative
density error, n>=n0, h>=K, and 0<N<=R!*K. The subset and modular-generation
properties are fields of `ModularGeneratingData`, not additional assumptions.

The finite selector first uses epsilon/4 for its three relative errors.
The cap condition needs a factor 16 more than before; this coefficient is
at most (4q)^(2q+4), still absorbed by n^(alpha/10). The clique counting
error uses the stronger exponent alpha/5 and costs no larger threshold.
The former finite generator theorem is now a wrapper around this stronger
quarter-error construction, preserving all existing callers.

For density powers up to K, the relative error is at most epsilon/8.
The factorial-to-binomial error is also at most epsilon/8, giving a combined
main-term error at most epsilon/2 relative to the reference binomial term.
Together with the quarter-error selection bound and epsilon<=1, this gives
strict final relative error below epsilon. The total host clique count is
at most twice the reference term, so the quarter saturation bound also
implies the source's strict absolute bound.

`reference_modular_generators_paper_whp_corrected` applies these deterministic
bounds to the sampled host itself. At n>=n0, for p=n^(-alpha) and every
K<=h<=3*(2q)^R*K^2, the full reference-normalized construction succeeds with
probability greater than 1-exp(-n^(1/10)). The direct existence interface is
`exists_sparse_reference_modular_generators_paper_threshold`.

These conclusions include the actual decoder modulus N=R!*K. A version
allowing arbitrary larger N at the same printed n0 is not claimed; the
source proof itself uses a bound involving N. The later arbitrary-modulus
extension gives an explicit threshold, and the four-vertex colour pattern
below recovers the smaller printed palette for q=2. The original global
design threshold and the other separately listed obligations remain open.


## Same-family rainbow generation and finite failure probability

`FiniteSameFamilyGeneration` proves the fourth assertion of `lem:extcol`
for one fixed family of random permutations, including rainbow cliques that
use any of its colours. This strengthens the separate-family construction
used by the main design proof; no closure assumption about newly introduced
rainbow cliques is made.

Write K=choose(q,R), A=paperInverseAlpha(q,R), and M=|S.graph|. The finite
host and unsaturated-clique hypotheses are the established observed-density
KSG estimates. For q>=3, the colour family has exactly the source's
u=20*q^2*A*M colours. At n>=n0, the probability that some rainbow clique
fails to be generated by that same family's permuted modular generators is
at most n^(-1). The theorem is
`paper_same_family_rainbow_generation_failure_paper_threshold`; an actual
family is extracted by `exists_paper_same_family_rainbow_generators`.
For q=2, R=1, this argument proves the same statement with
40*q^2*A*M colours. The later all-rank joint theorem also has all three
extension assertions in this doubled palette. This is not a counterexample
to the printed smaller count.

The proof fixes the K colours used by a base, but leaves every unused
permutation independent. The single-trial estimate 8*n^(-alpha/24) is at
most n^(-alpha/32) at n0. Thus 48*(q+1)*A trials fail for some base embedding
with probability at most n^(-2), uniformly in every value of the fixed
permutations. Product-measure restriction, splitting, and finite sections
transfer this conditional estimate to the original random family.

There are exactly choose(u,K) possible base palettes. Every rainbow clique
has one such palette. The available colours contain all required far-clique
trials: K*|far|<=2*M and q<=K give a total cost at most 145*A*M. This fits
20*q^2*A*M for q>=3 and 40*q^2*A*M for all q>=2. The numerical bound
u^K<=n0 then gives a total failure probability at most n^(-1).

The same-family bound is now strengthened to n^(-5/3), using u^K<=n^(1/3).
It is combined with the three extension properties in the following result.
The existing unconditional main proof and its corrected explicit threshold
remain unchanged.


## Joint colour probability in the printed palette

For q>=3, `joint_rainbow_generation_failure_paper_threshold` proves total
failure at most n^(-1) for `RainbowExtensionProperties` together with
modular generation of every rainbow clique by the same family's generators.
The family has exactly u=20*q^2*A*M colours, where A=paperInverseAlpha(q,R)
and M=|S.graph|, and the ambient size is only required to satisfy n>=n0.

The new common trial count is 60*q*A. At n0, q>=3 implies
8*n^(-alpha/24)<=n^(-alpha/27). For any root of size f<=2*q-1, the union
bound over root embeddings is therefore at most n^(-5/3). This applies to
a punctured clique, a single exchange base, and two bases meeting in an
R-edge. Each experiment uses at most M colours per trial, so all three can
be tested within the same printed palette. Independence between these
three experiments is not assumed or needed.

Generation has the same n^(-5/3) bound: after conditioning on the K colours
of a base, the conditional failure is at most n^(-2), and the number of
possible base palettes is at most u^K<=n^(1/3). A union bound over these
four failures gives 4*n^(-5/3)<=n^(-1) at n0.

`exists_joint_rainbow_generating_family_paper_threshold` extracts a common
family. `exists_sparse_joint_rainbow_system_paper_threshold` also constructs
the typical host and its modular data, and proves the source's
u*2^q*n^(-7alpha/10) bound for the union of permuted generators. Its modulus
range is the established 0<N<=R!*choose(q,R); no host-existence input or
probabilistic construction outcome is assumed.

This initial joint theorem uses the count
(3/8)*density(G)^(K-1)*n^(q-R)/(q-R)!. The next theorem removes that loss
and proves the source's count. The joint q=2 case initially remained separate;
it is now proved by the four-vertex colour pattern described below.


## The printed punctured-clique count and all four colour assertions

`PaperRainbowExtensionProperties.punctured` has the source's count
(1/2)*(n^(-alpha))^(K-1)*n^(q-R), with a strict lower bound, where
K=choose(q,R). For q>=3, `printed_joint_rainbow_generation_failure_paper_threshold`
proves all four assertions of `lem:extcol` jointly at n>=n0, in exactly
u=20*q^2*A*M colours, with total failure at most n^(-1). The direct existence
and sparse-host assembly interfaces are
`exists_printed_joint_rainbow_generating_family_paper_threshold` and
`exists_sparse_printed_joint_rainbow_system_paper_threshold`. The constructed
host uses the established modulus range 0<N<=R!*K. The other three assertions,
the palette size, and the source's sparse generator-union bound are unchanged.

The new proof controls ambiguities between labelled embeddings rather than
dividing their count by (q-R)!. An embedding is exclusive when each prescribed
colour contains its own edge and no other edge of the punctured pattern.
If two exclusive embeddings have the same image clique, their coloured edge
images agree. Every non-root vertex is determined by those edges, and the
root map is fixed, so the embeddings are equal.

For each successful embedding, mark a pair of distinct pattern edges when
one edge also receives the other's colour. Their total count bounds all
nonexclusive successes. For s pattern edges and T candidates, its mean is
at most 2*s^2*|T|*density(G)^(s+1). The extra density factor comes from the
joint probability of two distinct edges in one uniformly rotated colour;
all other colour marginals retain their exact density factors.

The three-quarter-mean lower tail has probability at most
32*n^(-alpha/24). The collision count exceeds
(1/64)*density(G)^s*n^(q-R) with probability at most n^(-alpha/24).
Since there are at least (3/4)*n^(q-R) candidate embeddings, their difference
exceeds (35/64)*density(G)^s*n^(q-R), with failure at most
33*n^(-alpha/24). At n0, density(G)^s is at least
(15/16)*(n^(-alpha))^s. Thus the resulting coefficient is 525/1024>1/2.

For q>=3, the single-trial failure is at most n^(-alpha/30). Repeating
60*q*A times and taking a union bound over all R-root maps gives failure
at most n^(-5/3). The other two extension assertions and generation each
have the same bound. Their sum is at most n^(-1). No independence between
the four final assertions is required. The unconditional main design theorem
and its corrected explicit threshold still use the existing avoiding-colour
construction; this stronger non-avoiding theorem does not replace it silently.


## A doubled palette covers the joint q=2 case

`corrected_joint_rainbow_generation_failure_paper_threshold` proves all four
colour conclusions jointly for every q>R>=1 at n>=n0, with failure at most
n^(-1), using 40*q^2*A*M colours. The punctured-clique count retains the
source's coefficient 1/2 and reference density. The direct existence and
sparse-host versions are
`exists_corrected_joint_rainbow_generating_family_paper_threshold` and
`exists_sparse_corrected_joint_rainbow_system_paper_threshold`. The host and
modulus assumptions are exactly those in the previously verified finite
construction. For q>=3 the smaller printed palette remains proved separately.

The repetition arguments are now factored through a supplied numerical
failure bound, so both palette sizes reuse the same finite probability and
root-to-clique proofs. The doubled palette contains 80*q*A trials of every
pattern of at most M edges. Ordinary extension failures obey
8*n^(-alpha/24)<=n^(-alpha/32); the resulting exponent absorbs all roots
of size at most 2*q-1, even for q=2. Exclusive punctured extensions use
33*n^(-alpha/24)<=n^(-alpha/36), which absorbs their smaller R-root set.
Each failure is at most n^(-5/3), as is same-family generation in this
palette. The usual four-event union bound gives n^(-1).

This established the q=2 joint result with the permitted change of constants.
The smaller printed palette is now recovered by the four-vertex colour
pattern below. The independent global threshold and probability-rate
corrections remain unchanged.


## Improving the uniform Section 9 leave from 432 to 16

`exists_sparse_nibble_paper_threshold_sixteen` proves the full finite
hypotheses of Lemma 9.1, in every positive edge rank and every epsilon<=2/5,
with leave bounded by 16*n^(-epsilon/(3*K)), where K=choose(q,R).
The ambient threshold remains n>=n0, and both polynomial density assumptions
and the initial degree error are unchanged. Existing interfaces with
constant three remain available in their previously verified ranges.

Put p=n^(-epsilon/(3*K)) and a=p^K. When p<=1/16, the process now stops
at density p0=(16/3)*p instead of p. Its final bound 3*p0 is exactly 16*p.
The finite comparison, count, and terminal estimates have been generalized
to any larger stopping density satisfying the five floor conditions; the
previous fixed-density versions are wrappers with identical statements.
The graph-size, higher-rank, and rank-one packing constructions all use
these generalized estimates. The horizon and concentration argument are
unchanged, and no asymptotic largeness assumption is introduced.

The numerical inequalities are proved by induction from K=3:
256*K^2<=16^K, 144*K^3<=16^K, and 384*K<=16^K. Together with p<=1/16,
they imply the small-error, denominator, and face-error bounds at the new
stopping density. The variance bound also holds, and p0<=1/3. When p>1/16,
the empty packing already gives the strict 16*p bound. Equality is assigned
to the process branch. Pair cliques and the previously covered error ranges
reuse their stronger constant-three results.

The remaining interval for the original constant three is unchanged:
3<=K<=14 and 0<epsilon<1/(12*K). The permitted uniform replacement now
has constant sixteen rather than 432. The original global design threshold
and the other separately listed auxiliary quantitative claims remain open.


## Finite probabilities for the actual absorber placement algorithms

`absorber_greedy_failure_lt_stretched_exp` improves the finite tail used
previously only to prove existence. For n>=n0, M<=n, and theta>=n^(-1/2),
the entire union bound M*choose(n,R-1)*exp(-2*R!*theta*n/3) is strictly
less than exp(-n^(2/5)). Its polynomial prefactor is paid for by the existing
finite Boost tail; the remaining square-root exponent pays for the new
stretched-exponential rate. The earlier less-than-one theorem is a wrapper.

`unstopped_greedy_probability_paper_threshold` transfers this estimate to
the actual ordinary greedy process. Its assumptions are the explicit
completion-size and density smallness conditions, not an informal largeness
claim. The prescribed-candidate counterpart allows arbitrary history-dependent
candidate families, separate forbidden density, and theta/eta>=n^(-1/2).
Neither process contains an artificial degree stop. The existing exact
agreement with the stopped process supplies their probability estimates.

For patterns with at most (4q)^(2q) vertices and edges, the interval
n^(-1/2)<=theta<=(4q)^(24q)*n^(-alpha/3) is verified at n0. The
`small_pattern_uniform_greedy_paper_probability` interface gives the paper's
all-edge output coefficient 2^(R+1)*R!, with the stronger finite failure
rate exp(-n^(2/5)). The printed, less conservative upper density constant
is still not claimed.

`SeparatedGreedyProbability` applies the prescribed process to the actual
free-vertex restrictions on earlier related placements. It records both
the bounded greedy family and separation for every related pair, together
with equality to every selected embedding in the trajectory. The allowed
working exponents include alpha/2. `splitting_placements_probability_at_exponent`
then verifies the repeated-clique root degrees, the conflict count, separation,
and the bounded union used in the splitting stage.

`local_decoder_output_probability_at_exponent` proves a probability statement
about the decoder family's actual output, not the existence of some unrelated
decoder family. It enumerates all edges of the forbidden graph, records the
selected embeddings at their exact time indices, and refines their disjoint
(q+R)-cliques into q-cliques. The output has the local decoder coefficient
and multiplicity bounds and the proved sparse support bound. The theorem
works for every exponent between alpha/3 and 1/2 at n0, so includes the
alpha/2 construction used by the main proof. The arbitrary default root
edge is used only after the finite enumeration has ended.

These individual placement estimates now feed into the dependent sampled
absorber below. The unconditional design existence theorem and its corrected
explicit threshold remain unchanged.


## The four-stage sampled absorber and its joint probability

`exists_sampled_absorber_process_paper_threshold` proves the corrected
probabilistic assertion of Corollary A after the integral generating family
has been supplied. It uses all four actual placement laws: local decoding,
signed splitting with the private-vertex restrictions, first cancellation,
and second cancellation. The joint failure probability is strictly below
exp(-n^(1/10)) for n>=n0. Every successful output has a decomposition,
is disjoint from the original input graph, is n^(-alpha/4)-bounded, and
absorbs every leave generated by the supplied family.

A stage's finite output is read from its sampled trajectory prefix. The
failure mass is exactly the probability that no certified output matches
that prefix. The decoder index conversion is explicit; the splitting and
cancellation events also record every sampled embedding at its actual
index. Thus the construction does not replace the random experiment with
a deterministic choice of a successful family.

The distribution for each later stage may depend on every earlier output.
The first cancellation roots are chosen from the sampled splitting family;
the further cancellation pairs and second roots are chosen from the sampled
first cancellation family. None records failure and prevents later stages
from running. The dependent composition preserves earlier outputs and has
failure at most the sum of the four uniform conditional bounds. At n0,
4*exp(-n^(2/5))<exp(-n^(1/10)), so the union bound fits the stated rate
without independence or an asymptotic size assumption.

`exists_sampled_absorber_for_generated_leaves` constructs both exchange
patterns and all initial roots. Its inputs are just the sparse graph and
the supplied multiplicity-16 generating family. Decoder and splitting
parameters are verified at alpha/2, including the factor two for the
original graph and generator support. All intermediate constants and the
final n^(-alpha/4) bound use the existing normalized finite estimates.

This closes the compound-probability gap listed previously for Corollary A
with the authorized corrections. It does not restore the printed whp rate
exp(-n/10), the false multiplicity-two claim, or the unverified construction
of the Step-1 generators at the printed global threshold. Those distinctions
and the corrected explicit threshold for the main design theorem remain.

Verification of this extension passed on 2026-08-27: the full build completed
4259 jobs across all 663 supporting modules, and all 1706 audited results
use only propext, Classical.choice, and Quot.sound. The logs are
`tmp/arxiv-2411.18291/build-663.log` and `tmp/arxiv-2411.18291/audit-663.log`.
No computational limits were increased. The final process specification is
kept separate from its proof so dependent type expansion stays within the
existing heartbeat limit.


## Every positive modulus in the sparse-generator lemma

`reference_modular_generators_whp_modulus_threshold` proves all three
conclusions of the sparse modular-generator lemma for every positive N.
The probability concerns the actual random host and is greater than
1-exp(-n^(1/10)). Saturation and deletion are strictly below the source's
bounds; unsaturated clique counts have the original reference-density
binomial normalization. A companion theorem constructs such a host.

Writing R for the edge rank and A=alpha^(-1), the sufficient threshold is

    max(n0, max(1, 256*choose(q,R)*choose(q,R-1)*N)^(10*A)).

The new numerical interface isolates precisely the modulus requirement:
256*choose(q,R)*choose(q,R-1)*N <= n^(alpha/10). It supplies the same
integer face cap and quarter-error budget as before. The construction,
reference-count comparison, and random-host probability then reuse the
existing finite arguments. No upper bound on N or implicit asymptotic
threshold remains in this corrected version.

`modularGeneratorThreshold_eq_paperThreshold` proves that the displayed
threshold is exactly n0 whenever N<=R!*choose(q,R). Existing finite
statements and their downstream users are preserved as wrappers with
identical assumptions and conclusions. This does not assert that the
unchanged n0 suffices for arbitrarily large moduli.

Verification of the arbitrary-modulus extension passed on 2026-08-27:
all 665 supporting modules build in 4261 jobs, and all 1717 axiom checks
match their declarations and use only propext, Classical.choice, and
Quot.sound. Logs: `tmp/arxiv-2411.18291/build-665.log` and
`tmp/arxiv-2411.18291/audit-665.log`. All imports are acyclic and every module
is reachable from the entry point; no computational limits were changed.


## The printed colour palette in every positive rank

The pair case q=2, R=1 is now proved with the original palette rather
than twice that palette. `pairColourExchange` is a four-vertex exchange:
its positive pairs are 01 and 23, its negative pairs are 02 and 13,
and its base is 01. Lean checks its two decompositions, exchange-family
properties and designated elimination pair directly on this finite type.
It is used for the colour argument; positive frame locality is neither
claimed for this pattern nor needed by the colour theorem.

The colour estimates now charge only the edges needing fresh colours,
not all edges of the pattern. There are exactly two over the base pair
and one over the union of the opposite roots. The punctured-clique pattern
also needs one fresh colour. The existing 160*alpha^(-1) repetitions
therefore fit the printed palette of 320*alpha^(-1) colours. Generation
uses just one far clique, so its separate requirement
2+144*alpha^(-1)<=320*alpha^(-1) also holds. These are exact finite
identities; the ambient threshold and the probability estimates are unchanged.

`pair_printed_joint_colour_failure_paper_threshold` combines all four
conclusions, including the original punctured-clique coefficient one half
and the same-family modular generation statement. Joint failure is at most
n^(-1). `exists_printed_colour_pattern_all_ranks` then constructs the
appropriate exchange for every q>R>=1, using the general construction for
q>=3 and the four-vertex pattern for pairs.

`exists_sparse_printed_colour_system_all_ranks` additionally constructs
the typical host, the sparse modular generating family, and a successful
colouring in the printed palette at n0. It retains the actual random
experiment's failure bound and the sparse bound for the permuted generator
union. The existing arbitrary-pattern doubled-palette theorem and all
previous interfaces remain available. This closes the previously listed
pair-palette gap; no claim is made that every arbitrary pair exchange has
the same colour budget. The main design proof's separate colour-system
interface is unchanged.

Verification of this extension passed on 2026-08-27: the full build completed
4265 jobs across all 669 supporting modules. All 1733 axiom checks match
their declarations and use only propext, Classical.choice, and Quot.sound.
Logs are `tmp/arxiv-2411.18291/build-669.log` and
`tmp/arxiv-2411.18291/audit-669.log`. Every module is inventoried exactly
once and reachable through acyclic imports. No computational limits were
increased and no new warnings remain.

## The source's local typicality threshold in a uniform range

`typical_local_threshold_of_covered_parameters` proves corrected Lemma 5.3
at the source's local threshold n>=2^(9*R*h), whenever R=1 or R*h>=15.
The edge rank is R=r+1 in the Lean declarations. The full source density
range p>=n^(-1/(2*h)) is retained, and the success probability is strictly
greater than 1-exp(-n^(1/10)). For R>=2 and R*h>=15 the same event also
controls the observed density to relative error n^(-1/10).

The key improvement is `relative_pow_error_linear`: if |a-b|<=c*b and
c*h<=1/2, then |a^k-b^k|<=2*c*h*b^k for k<=h. Consequently conversion
to observed-density typicality costs (4+4*h)*c, replacing the previous
exponential coefficient. Taking c=n^(-1/10)/(4*(h+1)) gives failure at most

`2*(h+2)*n^(r*h)*exp(-n^(3/10)/(192*(h+1)^2))`.

At k=R*h>=15, the proved inequality 3072*k^3<=3^k and the source threshold
absorb the polynomial prefactor, with strict room for exp(-n^(1/10)).
All estimates apply to the actual independent-edge probability measure.

Rank one needs no probabilistic approximation: `rankOne_isTypical` proves
zero-error typicality for every graph and every neighborhood size, including
the empty ambient type. Its typicality probability is exactly one.

This first step narrowed the local-threshold cases to R>=2 and 2<=R*h<=14.
The separate-error argument below now settles these cases too. Neither
argument restores the refuted exp(-n/10) rate or changes the separate global
design-threshold obligation. The prior general explicit-threshold theorem
and all its applications are unchanged.

Verification on 2026-08-27: the full entry-point build completed 4269 jobs
across 673 supporting modules. All 1748 audit entries match their requested
declarations and use only `propext`, `Classical.choice`, and `Quot.sound`.
The logs are `tmp/arxiv-2411.18291/build-673.log` and
`tmp/arxiv-2411.18291/audit-673.log`. The import graph is reachable and
acyclic, every supporting module is inventoried once, and no new warnings,
proof placeholders, or computational-limit changes were introduced.

## The full local typicality lemma, including every small case

`typical_paper_whp_corrected_local_all_ranks` proves corrected Lemma 5.3 for
every positive edge rank R, every h>=1, n>=2^(9*R*h), and every
p>=n^(-1/(2*h)). Its conclusion is actual typicality success probability
strictly greater than 1-exp(-n^(1/10)), with error exactly n^(-1/10).
No rank-size cutoff remains. In rank at least two,
`typical_density_whp_full_local_threshold` also gives simultaneous relative
density error n^(-1/10), and `exists_typicalGraph_density_full_local_threshold`
extracts a graph with both properties. Rank one is exactly typical for every
outcome by the deterministic theorem above.

The two error budgets are now separate. With delta=n^(-1/10), the density
uses relative error delta/(512*h), while each common neighborhood uses
(63/64)*delta around its exact mean. Excluded face vertices cost at most
delta/128. The sharper independent concentration bound has denominator
2+c rather than 2*(1+2*c); its nonnegativity assumptions are proved for
the indicator summands. A geometric count bounds all neighborhood tests
by (9/8)*n^((R-1)*h), avoiding an unnecessary factor h+1.

The density and neighborhood exponents are at least, respectively,

`n^(13/10)/(1769472*h^2)` and `(504063/1212416)*n^(3/10)`.

Each complete failure contribution is strictly less than half of
exp(-n^(1/10)) at the source threshold. The finite logarithmic estimates
use the rational lower base 373/200 for n^(1/(10*R*h)); all numerical
comparisons, including the narrow smallest case R=2,h=1, are proved in
Lean using exact rational arithmetic and exponential-series bounds.

This closes the standalone local-threshold obligation. The original
exp(-n/10) convention stays refuted. The global design threshold,
general greedy smallness constant, and previously listed constant-three
nibble interval are separate remaining obligations; the unconditional main
theorem and the uniform constant-sixteen nibble remain proved.

Verification on 2026-08-27: the full build completed 4274 jobs across all
678 supporting modules, including every downstream consumer of the stronger
concentration helper. All 1778 audit entries match their requested names
and use only `propext`, `Classical.choice`, and `Quot.sound`. Logs are
`tmp/arxiv-2411.18291/build-678.log` and
`tmp/arxiv-2411.18291/audit-678.log`. The import graph is reachable and
acyclic, the inventory has one entry per supporting module, and no new
warnings, proof placeholders, or computational-limit overrides were added.

## Edgewise capacities for an alternative to flattening

`reduced_boundary_correction_range` retains the actual edge multiplicity
m_e of the input generator. Reducing coefficients modulo the decoder modulus
N gives a correction quotient in [-m_e,0]. Its absolute-value degree at
every face is at most the original generator's boundary degree. This bound
does not replace all m_e by their maximum.

For fixed decoder regions Z_e, `edgewiseDecoderCapacity` assigns each clique
Q the capacity

`2^q*R! * (1_{Q in D} + sum_{e: Q subset Z_e} m_e)`.

`edgewise_representation_of_local_decoders` proves that every generated
leave has an exact representation within these capacities. The capacity
function and support are chosen before the leave; no uniform edge-multiplicity
bound is assumed.

`VariableCliqueSlots` allocates the corresponding positive and negative
slots. Their face degree is exactly twice the sum of capacities on cliques
containing that face. If these sums are theta*n bounded, every chosen root
edge family is 2*theta bounded, and the number of slots sharing an edge
with any root is at most choose(q,R-1)*2*theta*n. The overlap estimate uses
the actual capacity sums rather than a maximum capacity times a maximum
multiplicity.

`exists_variable_splitting_family` constructs actual root-preserving exchange
embeddings, disjoint new edges, and the required free-vertex separation
under explicit finite size, conflict, smallness and failure inequalities.
The full union is bounded by theta+16*R!*|S.graph|*theta. The composed theorem
`exists_variable_decoder_splitting` constructs one such family supporting
signed set representations of every generated leave.

The splitting interface takes the weighted decoder capacity bound as an
input. The construction of suitable regions and all decoder and splitting
conditions at n0 are now supplied below. The input generator and source
graph must be n^(-3alpha/5) bounded. Constructing that input at n0 and
controlling the later cancellation stages remain required before this route
could replace flattening in the main proof. No new global-threshold claim
is made. Existing main-theorem and multiplicity-16 interfaces are unchanged.

Verification on 2026-08-27: the entry-point build completed 4279 jobs across
683 supporting modules. All 1794 audit entries match their requested
declarations and use only `propext`, `Classical.choice`, and `Quot.sound`.
Logs are `tmp/arxiv-2411.18291/build-683.log` and
`tmp/arxiv-2411.18291/audit-683.log`. All imports are reachable and acyclic,
the inventory lists each module once, and no new warnings or proof escapes
remain. No computational limits were increased.


## Constructed weighted decoder placement

`edgewiseDecoderCapacity_degree` gives the exact capacity sum at each
face S. In edge rank R, it is

`2^q*R! * (# {Q in D : S subset Q} + choose(q+1,q-R+1) * sum_{e: S subset Z_e} m_e)`.

`decoderRootWeight` assigns each root the positive weight w_e=1+m_e.
The weighted root degree is at most the source graph degree plus the
original generator's boundary degree. If these two inputs are respectively
theta_B and theta_D bounded, the weighted root budget is theta_B+theta_D,
and each increment weight is strictly below C=1+theta_D*n.

`weightedGreedyProbability` is an actual finite-history embedding process.
Each root is sampled once; its weight multiplies its incidence indicator.
The weighted stop is determined by the previous history. Since all weights
are at least one, its degree cap also controls the ordinary forbidden graph.
Every transition, including aborts, has the required conditional-mean bound.
The expanded weighted index set is used only for deterministic sums, never
as a collection of independent random samples.

For any c>0, the total mean budget at a face is
mu=2*R!*(theta_B+theta_D)*n. The probability of reaching (1+c)*mu is at most
exp(-mu*c^2/((2+c)*C)). The simultaneous bound multiplies this by the number
of pattern edges and ambient faces. All increments are proved nonnegative
and bounded by C, as required by the corrected concentration theorem.

`exists_weighted_greedy_family` extracts actual legal disjoint embeddings
when this failure bound is below one. `exists_weighted_decoder_placement`
then constructs the decoder regions Z_e, their weighted degree bound,
their ordinary graph bound, and the resulting variable clique capacities.
Writing K=choose(q+R,R) and L=(1+c)*2*R!*(theta_B+theta_D), its explicit
conditions are n>=4*(q+R)^2, n>0, K*(theta_B+K*L)<=1/4, and the simultaneous
tail bound below one. The regions are weighted K*L bounded, their union
graph is theta_B+K*L bounded, and their capacity parameter is

`2^q*R! * (theta_D + choose(q+1,q-R+1)*K*L)`.

These are constructed outputs, not assumed placement or capacity bounds.
The result also handles an empty source graph without adding a nonemptiness
assumption. This general finite interface retains its explicit inequalities;
the specialization below discharges them at n0 and composes with variable
splitting. Bounds for the later cancellation stages remain. In particular,
the existing first elimination enumerates all opposite-sign near pairs;
its degree estimates cannot simply reuse a uniform multiplicity constant.
No new claim about n0 or the complete variable-capacity absorber is made.

Verification on 2026-08-27: the full entry-point build completed 4288 jobs
across 692 supporting modules. All 1831 audit entries, including the 37 new
theorems, match the requested declarations and use only `propext`,
`Classical.choice`, and `Quot.sound`. Logs are
`tmp/arxiv-2411.18291/build-692.log` and
`tmp/arxiv-2411.18291/audit-692.log`. Every supporting module is inventoried
once, reachable from the entry point, and part of an acyclic import graph.
There are no new warnings, proof placeholders, or computational-limit changes.


## Weighted decoder and splitting stages at n0

The finite conditions for the weighted route are now discharged at the
printed threshold. For edge rank R and alpha=paperAlpha(q,R), assume the
supplied generator D and its source graph B are n^(-3alpha/5) bounded and
cliqueSupport(D) is contained in B. No constant edge-multiplicity bound is
required.

`paperInverseAlpha_le_two_q_power` proves 1/alpha <= (4q)^(2q+2).
With c=n^(alpha/10), theta=n^(-3alpha/5), and C=1+theta*n, the weighted
concentration exponent is at least (2/3)*c. The logarithmic union bound
retains the inverse-alpha factor: 30*R/alpha < n^(alpha/20) at n0.
This proves the simultaneous failure probability is below one. The result
is an existence statement; it does not assert the earlier constant-weight
failure rate for this weighted process.

`weighted_decoder_finite_conditions` checks the legal-choice smallness
and ambient size inequalities. `weighted_decoder_output_density` bounds
both the decoder graph and the clique capacities by n^(-2alpha/5).
Consequently `exists_weighted_decoder_paper_threshold` constructs the actual
regions and both bounds, with no extra finite numerical assumptions.

For splitting at theta'=n^(-2alpha/5), choose the integer conflict cap

`d = ceil(choose(q,R-1) * 2*theta'*n)`.

The cap can grow with n. `variable_splitting_conflict_size` proves the
required free-vertex restriction 4*w*(d*w)<=n, including its rounding
error. It uses 16*w^2*choose(q,R-1)*theta'<=1 and 8*w^2<=n rather than a
constant cap. The remaining smallness and tail inequalities also hold
at n0, and the entire splitting graph is n^(-alpha/3) bounded.

`exists_weighted_decoder_splitting_paper_threshold` composes the two actual
constructions. `exists_constructed_weighted_splitting_paper_threshold`
also constructs the exchange pattern, with its cross-simplicity and local
frame properties. One fixed family then supports disjoint signed clique
sets P and N with boundary(P-N)=indicator(L) for every generated L subset B.
Neither the pattern, decoder regions, splitting family, nor finite
placement inequalities are assumed in this last theorem.

This closes the weighted decoder and splitting conditions at n0. It does
not finish absorption: the negative cliques still need cancellation. The
existing first-elimination family enumerates all opposite-sign near pairs,
so its old multiplicity-based bounds cannot be reused directly. The required
input generator at n0 with the full source coefficient was also outstanding;
the sharper construction below now supplies it, including
its support graph. The unconditional eventual main theorem and corrected
explicit main threshold are unchanged; no printed global threshold is
asserted by these new stage results.

Verification on 2026-08-27: all 697 supporting modules build in 4293 jobs.
The 1849 requested axiom checks, including 18 new results, match exactly
and use only `propext`, `Classical.choice`, and `Quot.sound`. Logs are
`tmp/arxiv-2411.18291/build-697.log` and
`tmp/arxiv-2411.18291/audit-697.log`. The inventory and acyclic import
coverage are complete. There are no new warnings or proof escapes, and
no computational limits were increased.


## Variable-capacity signs, geometry, and boundary degrees

The splitting geometry now uses the individual capacities C(Q) throughout.
The fixed positive and negative clique families are chosen before a leave,
are disjoint as sets, and contain the corresponding signed representation
of every vector whose coefficient at Q is bounded by C(Q).

The placed-copy proofs establish exact intersections with the original
graph. Near cliques meet it in one edge, far cliques avoid it, and every
negative far clique is edge-disjoint from every other negative clique.
Near cliques sharing an edge intersect in precisely its vertices. Each
new edge of a negative near clique has a unique positive far partner.
None of these results uses a uniform capacity or edge-multiplicity bound.

For the full replacement family, an old edge e has multiplicity at most
2*sum_{Q containing e} C(Q). Every edge outside the old graph has
multiplicity at most two. Summing these contributions gives the bound

`degree(boundary(F.cliques), T) <= 2*(q-R+1)*capacityDegree(D,C,T) + 2*degree(F.graph,T)`.

Thus a capacity density theta_C and graph density theta give clique-boundary
density 2*(q-R+1)*theta_C+2*theta. The two contributions add; there is no
maximum-multiplicity factor multiplying the graph density. At n0, the
already constructed densities n^(-2alpha/5) and n^(-alpha/3) yield
n^(-3alpha/10) boundedness for the full clique boundary.

`VariableNearMatching` matches every selected negative near clique to a
distinct selected positive near clique. Its proof uses the nonnegative
boundary on the old graph, not a multiplicity bound.
`exists_constructed_variable_splitting_output` combines the constructed
exchange, decoder regions, and splitting family at n0 with the new boundary
bound and fixed signs. Every generated leave has signed sets within these
families and a matching of the selected near cancellations.

This does not construct a sparse elimination family covering all potential
near pairs simultaneously. The matching may depend on the leave; replacing
the fixed absorber by an elimination family chosen afterwards would not
prove the required universal absorption statement. The all-pairs placement
cost and later cancellation remain open. The full-coefficient input
generation and support budget at n0 are now supplied below.
The main design theorem continues to use the previously
verified corrected threshold.

Verification on 2026-08-27: all 707 supporting modules build in 4303 jobs.
All 1894 exact audit requests, including 45 new results, match the output
and use only `propext`, `Classical.choice`, and `Quot.sound`. Logs are
`tmp/arxiv-2411.18291/build-707.log` and
`tmp/arxiv-2411.18291/audit-707.log`. The import graph is reachable and
acyclic, the inventory lists each module once, and the new source files
have no long lines, trailing whitespace, warnings, or proof escapes.
No computational limits were increased.


## Full generator coefficient and unconditional variable splitting at n0

The complete palette coefficient now fits the direct assembly theorem's
budget. Write R=r+1, k=choose(q,R), a=(2q)^R, and H=3*a*k^2. The uniform
coefficient factors exactly as

`C_upper = (6*k+4)*(48*(2q+1)*paperInverseAlpha(q,R)*H+1)*2^q`.

Its product bound is

`C_upper+1 <= 207360*(2q+1)*a^2*k^5*2^q <= (4q)^(6q)`.

The proof retains k<=2^q alongside a: for q>=4 their combined contribution
is at most (4q)^(3q), and the remaining factor is at most (4q)^6.
The cases q=2 and q=3 are checked exactly. This avoids the extra threshold
that resulted from normalizing the coefficient by n^(alpha/20).

The direct decoder augmentation also has spare room: twice its coefficient
is at most (4q)^(8q+2), which is at most n^(alpha/10) at n0.
`decoder_augmentation_half_density_paper_threshold` therefore gives the
stronger output density n^(-3alpha/5)/2. The existing direct focusing and
integral-lifting theorems now retain this half-budget bound.

`exists_paper_integral_generators_paper_threshold` constructs the entire
colour system, its exchange pattern and carrier, focusing cliques, local
decoders, and integral lift at n0. The input is only an n^(-rho)-bounded
source graph B. The same D generates every integrally decomposable integer
vector supported on B, with boundary density at most n^(-3alpha/5)/2.
The main design proof's earlier explicit generator interface now calls
this stronger construction; its corrected overall threshold is preserved.

The original graph also fits half the budget:
`n^(-rho) <= n^(-3alpha/5)/2` at n0. Thus B union cliqueSupport(D)
is n^(-3alpha/5) bounded. This support enlargement is included explicitly
in `exists_paper_integral_generators_with_support`; no unsupported assumption
that every generator lies inside B is made.

`exists_unconditional_variable_splitting_paper_threshold` now composes this
input with the actual weighted decoder and splitting constructions. From
B alone, it chooses D, its support graph, the exchange pattern, decoder
regions, and one fixed splitting family at n0. Its full clique boundary
is n^(-3alpha/10) bounded. Every integrally decomposable leave L subset B
has disjoint signed sets in the fixed positive and negative families and
a selected near matching.

The all-pairs cancellation cost and the later universal cancellation
construction remain open. The matching may depend on L; the construction
does not yet yield a single sparse absorber for all L at n0. The standalone
focusing/decoder lemma's exact printed output coefficient is also not
asserted by this improved generator density. No claim about the printed
global design threshold has been added.

Verification on 2026-08-27: all 711 supporting modules build in 4307 jobs.
The 1904 requested axiom checks, including 10 new results and the stronger
direct assembly statements, match exactly in name and order and use only
`propext`, `Classical.choice`, and `Quot.sound`. Logs are
`tmp/arxiv-2411.18291/build-711.log` and
`tmp/arxiv-2411.18291/audit-711.log`. The inventory is exact and the import
graph is reachable and acyclic. The new and changed proof modules have
no new warnings, long lines, trailing whitespace, or proof escapes.
No computational limits were increased.


## Separating the active part of an elimination placement

The current flattening construction repeatedly splits the whole input
family. A more selective analysis now has a verified bound for the part
of each elimination copy that touches its old roots.

For an elimination pattern with roots P and N, define its near family to
be the replacement cliques sharing an edge with either root. Write
R for the edge rank and k=choose(q,R). Distinct near cliques can be
assigned distinct root edges: an old root edge appears in at most one
replacement, and the common root edge disappears completely. Therefore
there are at most 2*(k-1) near replacement cliques, independent of the
full exchange size. Each has at least one old edge, so the new part of
their combined support has at most 2*(k-1)^2 edges.

For an actual placed elimination family E, `E.activeCliques` consists
exactly of the images of this near subpattern. These are the replacements
that meet the previously constructed graph. Every edge of multiplicity
above two in E.cliques is covered only by E.activeCliques. The remaining
replacement family avoids the old graph and has multiplicity at most two
at every edge.

The actual finite placement has been strengthened, not replaced by an
assumption. `exists_uniform_elimination_family_with_bounds_paper_threshold`
constructs one family whose embeddings simultaneously control every
subgraph of the exchange pattern. The graph bound charges only the new
edges of that subpattern. The earlier placement theorem is a wrapper of
this stronger construction.

Consequently, for indexed root degrees and old-graph density bounded by
theta, `exists_elimination_family_with_active_bound_paper_threshold`
constructs a family at n0 with active graph density at most

`(1 + 8*R!*(k-1)^2)*theta`,

and active clique-boundary density at most

`(2*(q-R+1) + 2 + 16*R!*(k-1)^2)*theta`.

The latter factor is 134 for triangles. It is independent of the full
exchange's number of edges, unlike the older full-family round estimate.
All root support, pair intersections, finite size and density conditions
remain explicit in this placement theorem.

This is not yet a complete improved flattening round or iteration.
Retained representatives and interactions with previously retained cliques
still need to be included in a preserved invariant. In particular, the
inactive replacements cannot simply be declared unaffected by all later
root choices. The new active-family factor is not asserted as a bound
for an entire round. The all-pairs cost in the variable-capacity route
and the printed global threshold remain open.

Verification on 2026-08-27: the full build passes with 715 supporting
modules and 4311 jobs. All 1924 requested axiom checks, including 20 new
results, match exactly in name and order and use only `propext`,
`Classical.choice`, and `Quot.sound`. Logs are
`tmp/arxiv-2411.18291/build-715.log` and
`tmp/arxiv-2411.18291/audit-715.log`. The inventory and reachable, acyclic
import graph are exact. The changed proof modules have no new warnings,
long lines, trailing whitespace, or proof escapes. No computational limits
were increased.

## Simultaneous face and edge caps at the printed threshold

The bounded-generation argument now accepts a separate integer cap for each
incidence test. Its original constant-cap API remains a specialization. Applied
to the disjoint union of faces and edges, this constructs a modular generating
family subject to both caps. Every clique whose incident faces and edges are
unsaturated belongs to the generated subgroup.

Write R=r+1, k=choose(q,R), f=choose(q,r), and let M bound the number of
generators. If the original clique counts at faces and edges are at most
L_F and L_E, respectively, the number of saturated cliques is at most

`f*M*L_F/faceCap + k*M*L_E/edgeCap`.

This estimate is proved for the actual union of the two saturation sets.
The existing good-edge construction then deletes edges having too many
saturated extensions. If the original edge-clique count has relative error
at most delta/2, two explicit cap budgets give deleted-edge fraction at
most delta and remaining edge-clique relative error strictly below delta.
For a typical host, double counting improves the saturated-clique fraction
to at most delta squared.

`exists_edge_capped_modular_generators_paper_threshold` discharges these
budgets at n0 for every positive N through the decoder modulus R!*k. It uses

- `delta = n^(-alpha/60)`;
- `faceCap = floor(n^(1-7*alpha/10))`;
- `edgeCap = ceil(8*k^2*N/delta^2)`.

The original face-density estimate `2^q*n^(-7*alpha/10)` is retained.
`edge_cap_coefficient_bound` proves `16*k^2*N <= (4*q)^(q+1)`, including
q=2 and q=3 directly. This absorbs rounding and the coefficient to prove
`edgeCap <= n^(alpha/20)` at n0. The face budget follows from the previously
reserved quarter-error margin; no stronger size hypothesis is introduced.

`exists_sparse_edge_capped_modular_generators_paper_threshold` also constructs
the typical host. Thus this statement has no supplied host or generator
assumption. Its generator family has cardinality at most N times the host's
edge count, generates all unsaturated clique vectors, and retains both caps.

In `ColouredGenerators`, `containing_permutedUnion_le_sum` bounds the count
at an edge by the sum of counts at its inverse images. Consequently,
`containing_permutedUnion_le` preserves any real edge cap under arbitrary
permuted unions, with a factor equal to the number of copies. No disjointness
or independence of these copies is assumed.

This does not yet complete the alternative absorber construction. The old
colour success theorems require the smaller error n^(-alpha/10), so they
cannot be invoked unchanged for this new family. Their probability budgets,
the palette size, focusing, and decoder augmentation must all be reconciled
with the new error and edge cap before using it in universal cancellation.

Verification on 2026-08-27: all 721 supporting modules build in 4317 jobs.
All 1943 requested axiom checks, including 19 new results, match their
requested names and order and use only `propext`, `Classical.choice`, and
`Quot.sound`. No proof escapes, raised limits, or new warnings were found.
The inventory and the reachable, acyclic import graph agree exactly.
Logs: `tmp/arxiv-2411.18291/build-721.log` and
`tmp/arxiv-2411.18291/audit-721.log`.

## Rainbow extensions with the relaxed capped-generator error

The good-edge colour experiment now accepts the new error
`delta = n^(-alpha/60)` at n0. It does not reuse the old small-loss
hypothesis. `good_edge_colour_estimates_relaxed_paper_threshold` proves
that the actual good graph has density at least one quarter of the
reference density and at least `(1-delta)*density K`. Its pair probability
is at most `(1+delta)*(density K)^2`.

Two sharper estimates make this usable over the full exchange size H.
For delta at most 1/8, the joint-to-marginal factor is at most `1+4*delta`.
`exchange_eight_square_bound` proves `(8*H)^2 <= (4*q)^(3*q)` whenever
`H <= 3*(2*q)^R*choose(q,R)^2`. For q>=3, the proof uses the descending
exponent bound, `choose(q,R)^4 <= 16^q`, and `144 <= q^(q+2)`; q=2 is
checked directly. Consequently `8*H*delta <= 1` at n0, and every powered
joint probability through H colours is at most twice the squared product
of marginal probabilities.

The existing geometric collision estimate contributes at most one more
squared mean. The actual extension count therefore has second moment at
most three times its squared mean. `lower_tail_le_eight_ninths_of_second_moment`
converts this to failure at most 8/9 for exceeding half the mean. The proof
applies Markov to `(X-5*mean)^2`: its expectation is at most 18 times the
squared mean, while failure makes it at least 81/4 times that squared mean.
No nonnegativity assumption on X is needed for this one-sided estimate.

`logarithmicColourTrialCount n f` is `ceil(9*(f+2)*log n)`. The elementary
bound `8/9 <= exp(-1/9)` proves

`n^f * (8/9)^(logarithmicColourTrialCount n f) <= n^(-2)`.

Thus `uniform_coloured_extensions_relaxed_failure_paper_threshold` gives
simultaneous failure at most n^(-2) over every prescribed f-vertex root.
`exists_many_rainbow_extensions_relaxed_paper_threshold` constructs one
successful palette and obtains more than
`(3/8)*(density G)^|E|*n^(|W|-|F|)` rainbow extensions for every root.

`exists_edge_capped_rainbow_host_paper_threshold` composes this with the
actual typical host and capped modular generators. All the original cap,
cardinality, saturation, deleted-edge, and extension-count conclusions are
retained. The palette has exactly `L*|E|+1` colours, where
`L=logarithmicColourTrialCount n |F|`; its generator union has face bound
`(L*|E|+1)*2^q*n^(-7*alpha/10)` and edge cap
`(L*|E|+1)*n^(alpha/20)`.

The palette factor remains explicit and has not yet been absorbed into the
later assembly budget. The unsaturated-clique colour experiment, near-frame
generation, focusing, decoder augmentation with caps, and universal
cancellation still require work. This extension is not a claim of the
printed fixed palette, the source's exact reference-density coefficient,
or a completed absorber at n0.

Verification on 2026-08-27: all 726 supporting modules build in 4322 jobs.
All 1958 requested axiom checks, including 15 new results, match their names
and order and use only `propext`, `Classical.choice`, and `Quot.sound`.
There are no proof escapes, increased computational limits, or new warnings.
The inventory and reachable, acyclic import graph agree exactly.
Logs: `tmp/arxiv-2411.18291/build-726.log` and
`tmp/arxiv-2411.18291/audit-726.log`.

## Far colours and modular rainbow generation with retained caps

The second colour experiment now works with the capped generating data.
The near-frame argument has been generalized to require only relative
edge-clique error at most one half. Its original APIs are preserved as
specializations, with the original numerical bounds. The new error
`delta=n^(-alpha/60)` is at most 1/8, so it meets this requirement without
changing the near-frame count or its collision and completion budgets.

`clique_colour_estimates_relaxed_paper_threshold` handles the unsaturated
family. Both the host's total clique-count error and its removed-clique
fraction are at most delta squared. Their combined marginal loss is at
most `2*delta^2 <= delta`. Pair probabilities are bounded by those of the
full host clique family. Consequently the same powered-moment estimate
used for good-edge colours applies to the far cliques, with marginal
reference density `(density K)^choose(q,R)`.

`coloured_extension_lower_tail_of_estimates_relaxed_paper_threshold` extends
the constant-success criterion to sparse candidate families of size at
least `(3/4)*n^(-a)*n^(|W|-|F|)`, with explicit exponent and density inputs.
This includes the actual near-frame candidates. The exchange's exponent
identity verifies the collision condition; no extra size threshold is used.

`rainbow_exchange_replacements_relaxed_failure_paper_threshold` proves
failure at most n^(-2) for the actual far-colour experiment with
`L=ceil(9*(q+2)*log n)` trials. Every initial rainbow clique then has an
exchange whose near and far replacement cliques lie in the appropriate
permuted unsaturated families. The existence theorem chooses one such
assignment of far colours.

`sparse_host_rainbow_generation_relaxed_failure_paper_threshold` applies
the exchange identity to these replacements and proves the same failure
bound for modular generation of every initial rainbow clique. Its
existence form constructs the additional permutations; this is not a
hypothesis that the replacements or their modular span already exist.

Finally, `exists_capped_rainbow_generating_family_paper_threshold` constructs
the typical host and capped generators before the initial palette is
chosen. For every initial palette J, it supplies an augmented palette of
size `|J|+L*|farCliques|+1` that retains all original generator copies and
generates all original rainbow cliques. The augmented family retains the
face bound and edge cap multiplied by exactly this palette size.

Thus the relaxed good-edge and far-clique experiments, near-frame
selection, and modular rainbow generation are now connected at n0. Still
required for the alternative final construction are the combined extension
palettes, numerical palette/degree budget, focusing and local decoding with
retained caps, and universal cancellation. The final printed design threshold
is not asserted by these results.

Verification on 2026-08-27: all 729 supporting modules build in 4325 jobs.
All 1969 requested axiom checks, including 11 new results and the preserved
near-frame APIs, match their names and order and use only `propext`,
`Classical.choice`, and `Quot.sound`. No proof escapes, increased limits,
or new warnings were found. The inventory and reachable, acyclic import
graph agree exactly.
Logs: `tmp/arxiv-2411.18291/build-729.log` and
`tmp/arxiv-2411.18291/audit-729.log`.

## Full avoiding colour system and removal of repeated-label costs

All three extension patterns now accept the capped host's relaxed deletion
error: punctured cliques, one prescribed clique root, and two prescribed
clique roots intersecting in an R-edge. The actual extension families use
`logarithmicColourTrialCount n f` trials for their respective root sizes f.
The punctured-clique count retains the `(3/8)*(density G)^(k-1)` coefficient
with its factorial denominator.

`relaxedExtensionPaletteSize n S P` is the sum of these three palette
sizes. `combined_rainbow_extensions_relaxed_paper_threshold` places their
colour sets in a disjoint sum and then reindexes by a finite interval.
The resulting one palette simultaneously satisfies all three extension
properties; these properties are constructed, not assumed.

`good_reference_density_power_relaxed_paper_threshold` proves that every
power s through the full exchange size H satisfies

`(1/2)*(n^(-alpha))^s <= (density G)^s`.

It uses `8*H*delta<=1` with delta=n^(-alpha/60), the original density
accuracy, and the general Bernoulli estimate for a good subgraph. There is
no factor exponential in H, and the result is no longer restricted to
powers through choose(q,R). The case s=1 also gives good-host density at
least half the reference density.

`exists_capped_avoiding_rainbow_generating_system_paper_threshold` now
constructs the host, capped modular generators, one combined extension
palette, t+1 copies of its colour labels, and the far-clique generation
palette. It supplies `RainbowAvoidingExtensionProperties`, modular
spanning for every initial rainbow clique, the full density-power bounds,
and both generator caps.

The cap estimate is stronger than counting all colour labels. Repeated
labels use exactly the same permutations, so they do not add generator
cliques. `permutedUnion_comp_surjective` proves invariance under arbitrary
surjective repetition, and `permutedUnion_augmented_repeated` proves it
for the augmented palette used here. Writing u for the combined extension
palette and L for the far-clique trial count, the resulting cap factor is

`u + L*|farCliques| + 1`,

independent of t. Both the face bound and the edge cap use this factor,
even though the full index type has `(t+1)*u+L*|farCliques|+1` labels.
The modular spanning statement still covers rainbow cliques for the full
repeated-label palette; only the generator union is identified with the
smaller union. This does not weaken the colour-avoidance conclusion.

The remaining factor is explicit and still needs a numerical power bound.
Focusing and local decoding must retain edge multiplicity before the new
system can give bounded integral generators for universal cancellation.
The final printed design threshold remains unclaimed.

Verification on 2026-08-27: all 734 supporting modules build in 4330 jobs.
All 1978 requested axiom checks, including nine new results and the
strengthened system cap, match their names and order and use only
`propext`, `Classical.choice`, and `Quot.sound`. No proof escapes,
increased computational limits, or new warnings were found. The inventory
and reachable, acyclic import graph agree exactly.
Logs: `tmp/arxiv-2411.18291/build-734.log` and
`tmp/arxiv-2411.18291/audit-734.log`.


## Capped integral generators at the original threshold

For q>=3 and edge rank R=r+1<q,
`exists_capped_integral_generators_paper_threshold` now constructs the
complete integral generator family at n0. Given any n^(-rho)-bounded
source graph B, it produces D with

- face boundedness at most `(1/2)*n^(-3*alpha/5)`;
- at most `n^(alpha/10)` cliques through each R-edge;
- integral generation of every integrally decomposable integer vector
  supported on B.

The exchange configuration, typical host, modular generators, extension
palettes, avoiding copies, focusing cliques, and local decoders are all
constructed. The final theorem has no supplied generating-system,
modular-spanning, integral-generation, or numerical growth hypothesis.
The q>=3 restriction is explicit; this strengthened cap theorem does not
claim the q=2 case. The previously verified integral generation theorem
without this cap still covers q=2.

The original focusing construction already used an edge-disjoint clique
cover. `exists_focusing_family_of_clique_cover_with_cap` retains this
information, proving edge multiplicity at most one. Its previous API is
preserved by dropping the extra conjunct. The punctured-clique count and
bridge arguments now accept the relaxed good-edge loss n^(-alpha/60),
using the full good-density power estimate and retaining the original
factorial normalization.

`augment_with_local_decoders_and_cap_at_exponent` uses the actual local
decoder family's multiplicity bound choose(q,R). Thus focusing followed
by decoding increases any incoming edge cap M by at most 1+choose(q,R).
`exists_integral_generators_from_system_with_cap_paper_threshold` performs
integral lifting while preserving precisely that additive bound.

The full generator palette has size

`p = relaxedExtensionPaletteSize n S P + L*|farCliques| + 1`,

where L=ceil(9*(q+2)*log n). Repeated colour labels still cost no extra
generator copies. `relaxedGeneratorPaletteSize_le` bounds p by four
maximal-root palettes. The coefficient estimate is

`p*2^q + 1 <= 81*(q+1)*H*2^q*(log n+1)`.

The proof bounds log n+1 by
`181*paperInverseAlpha*n^(alpha/180)`. For q>=3 the accompanying coefficient
is at most `(4q)^(4q)`; the finite cases q=3,4,5 are checked exactly, and a
uniform power bound handles q>=6. Since n>=n0 gives
`(4q)^(4q)<=n^(2*alpha/45)`, the full coefficient plus one is at most
`n^(alpha/20)`. This discharges the growth condition in the focusing and
decoder assembly without increasing the threshold.

Finally the raw edge cap n^(alpha/20), multiplied by p and increased by
1+choose(q,R), is at most n^(alpha/10). This supplies a substantially smaller
initial multiplicity for the remaining universal cancellation analysis.
It does not by itself construct multiplicity-16 generators or certify the
printed final design threshold; those claims remain open for this route.

Verification on 2026-08-27: all 743 supporting modules build in 4339 jobs.
All 1999 requested axiom checks, including 21 new results and the preserved
focusing API, match their names and order and use only `propext`,
`Classical.choice`, and `Quot.sound`. No proof escapes, increased
computational limits, or new warnings were found. The module inventory and
reachable, acyclic import graph agree exactly. Changed proof files have no
long lines, trailing whitespace, or tabs.
Logs: `tmp/arxiv-2411.18291/build-743.log` and
`tmp/arxiv-2411.18291/audit-743.log`.


## Linear decoder capacities and capped variable splitting

The small generator cap now survives the actual weighted decoder and
splitting stages. `exists_unconditional_capped_variable_splitting_paper_threshold`
constructs, for q>=3 and n>=n0, one fixed splitting family whose graph is
n^(-alpha/3)-bounded, whose clique boundary is n^(-3alpha/10)-bounded, and
whose edge multiplicity is at most n^(7alpha/60). It starts only from the
n^(-rho)-bounded source graph. Every integrally decomposable leave in that
source has a signed representation in the fixed positive and negative
families and a near matching. No family is chosen after the leave.

The key improvement avoids multiplying two unrelated maximum bounds.
Write R=r+1, k=choose(q,R), a=2^q*R!, and let M bound the original
family's edge multiplicities. The weighted capacity identity now applies
to every subset of size at most q. At an R-edge e it says that the sum of
capacities is exactly

`a * (multiplicity_D(e) + k * weightedRegionDegree(e))`.

The decoder regions are edge-disjoint, so at most one contains e. Its
weight is the original multiplicity at its assigned root, hence at most
M. Thus the capacity at e is at most `a*(1+k)*M`, linear in M. The original
face-degree identity is retained as a specialization of the generalized
identity.

`VariableSplittingFamily.decoder_clique_multiplicity` consequently bounds
the fixed replacement family by `2*a*(1+k)*M+2` at every edge. The factor
two accounts for the signed slots; edges outside the original splitting
graph still occur at most twice. The numerical estimate

`2*a*(1+k)+2 <= (4q)^(q+1) <= n^(alpha/60)`

holds at n0. Applied to the constructed generator cap n^(alpha/10), it
gives the new splitting cap n^(7alpha/60).

The near-pair counts are also sharper. Every near clique meets the old
graph in exactly one edge, and every common edge of opposite-sign near
cliques lies in that graph. All opposite partners of a fixed near clique
therefore use its single old edge. Under a splitting cap M there are at
most M such partners in either coordinate, rather than choose(q,R)*M.
The proofs bound the actual finite index fibres by injections into the
cliques containing that edge.

`VariableSplittingFamily.near_pair_degree_bounds` combines these fibre
counts with the boundary degree: if the splitting family is delta-bounded,
each indexed root family has face degrees strictly below M*delta*n.
Its real-valued bound keeps the exact power cap without rounding.

These results construct and bound the fixed splitting family and all
potential near-pair inputs. They do not yet construct both universal
elimination families within the final degree budget. The next quantitative
step is to use the small edge cap in weighted decoder concentration,
rather than the older bound derived only from the face degree; the
constant-deviation version and sharper resulting degrees are not yet
proved. The printed final design threshold remains unclaimed.

Verification on 2026-08-27: all 747 supporting modules build in 4343 jobs.
All 2012 requested axiom checks, including thirteen new results and the
preserved weighted face-degree API, match their names and order and use
only `propext`, `Classical.choice`, and `Quot.sound`. No proof escapes,
increased computational limits, or new warnings were found. The inventory
and reachable, acyclic import graph agree exactly. Changed proof files
have no long lines, trailing whitespace, or tabs.
Logs: `tmp/arxiv-2411.18291/build-747.log` and
`tmp/arxiv-2411.18291/audit-747.log`.


## Constant-deviation decoding and the first universal cancellation

`exists_unconditional_first_elimination_paper_threshold` now constructs
the generators, decoder regions, fixed splitting family, and elimination
copies for every opposite near pair, starting from the sparse source graph
alone. This holds for q>=3 and n>=n0. For every integrally decomposable
leave, its chosen matching selects copies from that same fixed family;
the resulting signed replacement preserves the leave boundary and disjoint
signs and removes every negative near splitting clique. The further
cancellation stage is not yet included.

The decoder concentration proof now uses the actual increment cap. The
general theorem `exists_weighted_decoder_placement_of_weight_bound`
accepts any proved bound C on the decoder root weights; the previous API
is preserved as a wrapper using its original face-degree bound. For capped
generators, C=1+n^(alpha/10). Setting the deviation parameter equal to one
then gives a concentration exponent at least `(2/3)*n^(alpha/10)`, enough
for the already verified polynomial union bound. The legal-choice budget
also holds, since its output load is no larger than with the former
n^(alpha/10) deviation. Actual weighted decoder regions are constructed.

Combining the factorial and binomial factors gives the sharper bound

`weightedDecoderCoefficient <= (4q)^(3q)`.

At n0 this costs only alpha/30 in the exponent. Both the decoder graph
and its capacity function therefore have density n^(-17alpha/30), rather
than n^(-2alpha/5). The finite variable-splitting criterion now works at
any exponent between 2alpha/5 and 1/2, retaining the rounded conflict
budget. Its output coefficient costs alpha/15, so these decoders produce
splitting graph density n^(-alpha/2).

The clique-boundary degree is controlled separately by the root capacity
and graph degree. The remaining coefficient 2(q-r)+2 is at most 4q, and
at n0 this is at most n^(alpha/180). Thus the constructed fixed splitting
family has clique-boundary density n^(-89alpha/180), while retaining the
previous edge cap n^(7alpha/60). Its signed representation and near
matching conclusions still hold for every admissible leave.

The sharper near-pair repetition theorem now supplies indexed root-face
degrees below `n^(-17alpha/45)*n`. These are in the verified finite greedy
interval. Consequently elimination configurations can be placed for all
potential opposite near pairs at once. The first elimination coefficient

`C1 = 1 + 4*R!*H`

is at most `(4q)^(4q)`, so the first elimination graph has density at most
n^(-alpha/3). The constructed theorem retains the stronger raw bound
`C1*n^(-17alpha/45)` as well as the absorbed power bound. It also retains
the elimination pattern's graph and vertex size bounds, which are needed
for the further stage.

The first-stage geometry and signed algebra now accept variable capacities.
Negative elimination cliques avoid the original splitting graph, good
negative cliques avoid all splitting cliques, and every bad negative
clique has a unique positive far splitting partner through its single old
edge. For a selected matching, cancellation preserves the exact boundary
and disjoint signs, and its negative family is contained in the union of
the negative far splitting cliques and the negative elimination cliques.

Still required are the sparse further-elimination family for all bad
negative cliques, the final negative packing, and the complete variable
absorber. In particular, this milestone does not yet certify the printed
final design threshold. The raw first-stage coefficient has deliberately
been retained for that remaining degree calculation.

Verification on 2026-08-27: all 756 supporting modules build in 4352 jobs.
All 2044 requested axiom checks, including 32 new results and the preserved
weighted placement API, match their names and order and use only `propext`,
`Classical.choice`, and `Quot.sound`. No proof escapes, increased
computational limits, or new warnings were found. The inventory and
reachable, acyclic import graph agree exactly. Changed proof files have
no long lines, trailing whitespace, or tabs.
Logs: `tmp/arxiv-2411.18291/build-756.log` and
`tmp/arxiv-2411.18291/audit-756.log`.


## Both cancellation stages and design existence at the original threshold

`design_existence_paper_threshold` completes the main quantitative result:
for every q>r>=1 and n>=paperSizeThreshold q r, divisibility of the complete
r-graph implies an actual clique decomposition. The threshold is exactly
the paper's `(4q)^(90q/alpha)`. The equivalent numerical criterion is
`hasDecomposition_iff_binomial_divisibility_paper_threshold`.
The earlier qualitative and larger-threshold theorems are preserved.

The new route closes the remaining absorber step. With R the edge rank,
k=choose(q,R), m=n^(7alpha/60), and delta=n^(-89alpha/180), set

`theta = m*delta = n^(-17alpha/45)`.

The first elimination graph retains its unabsorbed coefficient
`C1*theta`, where `C1=1+4*R!*H` and H is the elimination pattern size.
A bad negative clique has a unique positive far splitting partner.
Every edge of that partner lies outside the original splitting graph,
where the splitting family has multiplicity at most two. Each coordinate
of the near-pair family repeats a clique at most m times. Hence at most
4m first elimination cliques contain such an edge, and at most 4*k*m bad
negative cliques can share one far positive partner. The proof counts the
actual finite index fibres by an injection into the union over its edges.
It does not use the older squared union-multiplicity estimate.

The second positive root degrees are therefore below 4*k*theta*n.
Each bad negative clique occurs once, so the second negative root degrees
are below `(2*(q-R+1)+2*C1)*theta*n`. The existing graph and both root
families fit the common density `A2*theta`, where

`A2 = 4*k + 2*(q-R+1) + 2*C1`.

The numerical proofs establish C1<=(4q)^(4q), A2<=(4q)^(5q), and both
finite greedy interval bounds. The constructed second family has density
at most `C1*A2*theta`. At n0, `(4q)^(9q)<=n^(alpha/10)`, so this is at
most n^(-5alpha/18), stronger than the required n^(-alpha/4).

All corresponding geometry and selected signed identities now accept
variable capacities. Frame locality makes selected far partners distinct;
nonnegative boundary forces their presence. The two replacements preserve
the exact boundary and disjoint signs. The retained negative far cliques,
good first-stage negative cliques, and second-stage negative cliques form
one fixed edge-disjoint family. It decomposes its support, avoids the
source graph, and is bounded by the second elimination graph. Adding back
unused host cliques absorbs every admissible leave.

`exists_sparse_absorber_paper_threshold` consequently constructs the
full sparse absorber at n0. The capped construction covers q>=3. For
rank one, `hasDecomposition_one_of_divisible` embeds a partition indexed
by the graph's edges, and `empty_isAbsorber_one` removes any need for a
nonempty host. Thus the absorber lemma covers every positive rank and
all allowed clique sizes. The finite reserve, boost, nibble, cover, and
completion theorems then yield the main design theorem without the older
flattening threshold.

Verification on 2026-08-27: 768 supporting modules, 4364 full-build jobs,
and 2094 requested assumption checks, including fifty new results. Every
check matches its requested name and order and uses only the three standard
axioms. The inventory, import graph, proof-escape scan, and changed-file
style checks pass, with no new warnings or raised computational limits.
Logs: `tmp/arxiv-2411.18291/build-768.log` and
`tmp/arxiv-2411.18291/audit-768.log`.

The remaining work is confined to the separate auxiliary formulations in
the current next-work list. Neither the sparse absorber nor the printed
main design threshold remains open.


## Sharper finite nibble endpoint and constant three for k at least ten

`exists_sparse_nibble_of_ten_le_clique_paper_threshold` now proves the
original Section 9 leave constant 3 at n0 whenever k=choose(q,R)>=10,
for all epsilon<=2/5. This extends the previous range k>=15 without
changing the input density assumptions or initial regularity. The combined
`exists_sparse_nibble_paper_threshold_of_extended_parameters` includes
the already proved nonpositive-error, pair, and epsilon>=1/(12k) cases.
The remaining exact constant-3 interval is 3<=k<=9 and
0<epsilon<1/(12k). The uniform constant 16 remains valid throughout.

The improvement retains the actual error at the stopping time. From the
existing comparison parameters, k/g<=a, so rounding the horizon costs
at most a. The final face degree is bounded by

`p0 + (128*k+1)*a`,

rather than replacing all three contributions by p0. The actual finite
packing theorem, the sparse graph specialization, and the rank-one
specialization now preserve this sharper endpoint.

For p=n^(-epsilon/(3k))<=1/3, put a=p^k and stop at p0=2p.
The elementary coefficient bounds

`256*k^2<=3^k`, `4*k^3<=3^(k-2)`, and `128*k+1<=3^(k-1)`

hold for every k>=10. They verify the five finite floor conditions at
2p, including the variance comparison. They also give
`2p+(128*k+1)*p^k<=3p`. When p>1/3 the empty packing already meets the
strict leave bound. Thus no error cutoff is needed in the k>=10 result.

Verification on 2026-08-27: all 772 supporting modules build in 4368 jobs.
All 2106 requested assumption checks, including twelve new results, match
their names and order and use only the three standard axioms. The inventory
and acyclic reachable import graph agree exactly. The proof-escape and
computational-limit scans pass, and all new proof files pass style checks.
There are no new warnings.
Logs: `tmp/arxiv-2411.18291/build-772.log` and
`tmp/arxiv-2411.18291/audit-772.log`.


## Separate initial errors and constant three for k at least six

`exists_sparse_nibble_of_six_le_clique_paper_threshold` now proves the
original finite Section 9 leave constant 3 for every k=choose(q,R)>=6,
all epsilon<=2/5, and the original density hypotheses at n0. The combined
`exists_sparse_nibble_paper_threshold_of_improved_parameters` also retains
the pair, nonpositive-error, and epsilon>=1/(12k) cases. The only remaining
constant-3 cases have k=3,4,5 and 0<epsilon<1/(12k).

The previous numerical interface unnecessarily tied the input relative
error b to the cube of the comparison scale a. The actual initial critical
intervals allow the sharper strict conditions

`b < k*(16*k^2-1)*a^3` and `b < (16*k-1)*a^2`.

The first follows from dividing the initial clique-count error by k;
the second keeps the edge error separate from its critical width.
`nibble_initial_below_critical_of_error` proves the initial inequalities
for every track, and `exists_packing_at_nibble_horizon_of_error` constructs
the actual packing with this more general input. The process, drift,
variance, and concentration results are unchanged. The finite sparse
frontends now keep the input error independent of the comparison exponent.

For p=n^(-epsilon/(3k))<=1/3, choose

`a = (2/(5*k))*p^k` and `p0=2p`.

The elementary inequalities `512*k<=5*3^k` and
`8*k^2<=5*3^(k-2)` hold for k>=6 and verify the smallness and denominator
conditions. The other floor conditions also hold, and the precise
endpoint `2p+(128*k+1)*a` is at most 3p. Both strict initial margins
contain the original input error b=(p^k)^3. In particular the count
coefficient is `128/125-8/(125*k^2)>1`.

To reuse all previously proved finite exponent estimates, define

`eta = epsilon + 3*log(5*k/2)/log(n)`.

At n0 the scale 5*k/2 is at most n^(1/20). For epsilon<=1/4, this gives
epsilon<=eta<=2/5 and the exact identity n^(-eta/3)=a. The existing
finite comparison and tail estimates therefore apply with eta, while
the new initial-error theorem retains the original regularity error.
For larger epsilon, the previous epsilon>=1/(12k) theorem applies;
for p>1/3 the empty packing suffices. No new threshold is introduced.

Verification on 2026-08-27: 778 supporting modules build in 4374 jobs.
All 2124 requested assumption checks, including eighteen new results,
match their exact names and order and use only the three standard axioms.
The module inventory, reachable acyclic imports, proof-escape scan,
computational-limit scan, and new-file style checks all pass. No new
warnings were introduced.
Logs: `tmp/arxiv-2411.18291/build-778.log` and
`tmp/arxiv-2411.18291/audit-778.log`.


## Every clique size in the small-leave regime and an explicit exact threshold

`exists_sparse_nibble_paper_threshold_of_small_leave` proves the exact
Section 9 leave constant 3 at n0 for every positive rank and clique size
whenever p=n^(-epsilon/(3k))<=1/15. This includes all k=3,4,5 in that
regime; the pair case is retained from its separate construction.
The remaining unchanged-n0 cases therefore have k=3,4,5,
0<epsilon<1/(12k), and 1/15<p<=1/3.

The scaled floor and initial-margin lemmas are now generalized with their
old APIs preserved. The coefficient induction accepts any natural base
and a checked starting index. The finite floor theorem accepts those
coefficients and the exact variance comparison separately. The initial
margin theorem only needs the actual small-power inequality, rather than
a fixed lower bound on k. These changes permit base 15 and starting
index 3: all three seed inequalities hold, including the limiting
8*3^2<=5*15 comparison. The same scaled tracking error and doubled
stopping density then construct the actual finite packing with leave 3p.

For every epsilon<=2/5, the new `exists_sparse_nibble_exact_explicit`
proves the exact constant at the closed sufficient bound

`nibbleExactLeaveThreshold q R epsilon = max(n0, ceil(15^(3*k/epsilon)))`.

For positive epsilon the second term forces p<=1/15 by the real-power
identity; for nonpositive epsilon the empty packing suffices. The result
retains all original density and degree-regularity hypotheses and has no
implicit largeness assumption. It is an additional explicit sufficient
threshold, not a claim that the extra term always lies below n0.

Verification on 2026-08-27: 781 supporting modules build in 4377 jobs.
All 2133 requested assumption checks, including nine new results and the
preserved scaled-error APIs, match their exact names and order and use
only the three standard axioms. The inventory and reachable acyclic
import graph agree exactly. No proof escapes, increased computational
limits, new warnings, or changed-proof style violations were found.
Logs: `tmp/arxiv-2411.18291/build-781.log` and
`tmp/arxiv-2411.18291/audit-781.log`.

## Logarithmic tracking and actual edge drift for small clique sizes

This extension adds nine modules and 34 checked theorems. It addresses
an obstruction in the reciprocal comparison functions, without changing
any earlier constant-3 result or the completed design theorem at n0.

Write L(p)=1-k*log(p), a=n^(-epsilon/3), and p for the current
removal density. The new degree and clique-count errors are
3*L(p)*a^2*D and 4*L(p)^2*a^3*D*g. The scalar proof first establishes
L(p)^2*p^(k-1)<=3 for every k>=3 and 0<p<=1, using a cubic lower
bound for the exponential. Weighted versions then give all needed
small-clique margins when a<=((2/5)*p)^k. This is the condition
obtained by stopping at five halves of the target leave density.

For k=3,4,5, put m=D*p^(k-1), h0=D*g*p^k/k, w=a^2*D, and
write u,v for the new degree and count errors. The proved bounds are:

- u<=m/8 and u^2<=w*m/8;
- v<=h0/64 and v*m<=(5/2)*w*h0;
- u<=(3/4)*a*m and v<=a*h0/4.

The last pair proves the scalar face drift with error 2*a*n and
critical width a*n. The earlier edge drift inequalities used only
h>=h0/2 and discarded too much of this margin. The new ratio bound
retains h>=63*h0/64. The sharpened numerator cancellation and denominator
estimate give an edge drift allowance (3*k-1/8)*w*m/h0. The lower
bound includes the survival correction; it is not silently omitted.

Finite logarithmic increments give error slope 3*k*w*m/h0. The Taylor
remainder is at most w*m/(8*h0) when 8*k^3<=a^2*g. Both comparison
increments have absolute value at most twice the main slope; that bound
is at most w/100 when 200*k^2<=a^2*g.

`CliqueRemovalProcess.logNibbleEdge_critical_trends` combines these
facts with the actual trajectory and conditional expectation. It proves
both upper and lower critical trends, also treating already removed
edges. Its explicit hypotheses include 200*k^3<=a^2*g, the codegree
allowance (k^2+k)*n^(q-r-1)<=a^2*D/100, positive next density, and the
consecutive-density half bound.

This is not yet the remaining constant-3 packing theorem. The next work
is logarithmic clique-count tracking, the moment and stopping estimates,
the simultaneous packing construction, and discharge of all numerical
inputs at n0. The open parameter range is still k=3,4,5,
0<epsilon<1/(12*k), and 1/15<target density<=1/3.

Verification on 2026-08-27: all 790 supporting modules build in 4386 jobs.
All 2167 requested axiom checks match their exact names and order and
use only propext, Classical.choice, and Quot.sound. The inventory and
reachable acyclic import graph agree exactly. No proof placeholders,
new axioms, unsafe evaluation, or limit overrides occur; the new proof
files pass the line-length and whitespace checks. Only the two existing
dirty-dependency warnings remain.

Logs: `tmp/arxiv-2411.18291/build-790.log` and
`tmp/arxiv-2411.18291/audit-790.log`.

## Full logarithmic packing construction from original regularity

This extension adds 17 modules, 60 theorems, and the checked
`logNibbleCriticalControl` construction. The logarithmic route now
constructs an actual packing; no supplied good trajectory or unproved
concentration assertion is used.

`CliqueRemovalProcess.exists_regular_log_nibble_packing` takes the
paper's original degree error a^3*D, a `LogNibbleParameters` bundle,
an explicit horizon N, the step/window gaps, and the existing explicit
`nibbleFailureBound < 1`. It returns a subfamily of H with exactly N
cliques, an actual decomposition of its support, and bounded leave at
any density at least removalDensity(N)+2*a.

The new components establishing this construction are:

- Both actual clique-count critical trends. The elementary bound
  9*a<=k*p^(k-2), valid above the logarithmic stopping floor, controls
  the quadratic degree variance by the count-error margin.
- Finite clique-count comparison increments bounded by 9*k^3*D.
  These fit the existing larger uniform step bound, so all previously
  defined failure exponents remain applicable without changing them.
- A constant face error 2*a*n, with actual drift and average loss
  at most 12*k*n/g. The face variance is at most
  12*(q-r+1)*k*n/g, also below the existing uniform variance rate.
- One measurable family of signed count, frozen-edge, and face processes,
  together with its common good event and actual availability and degree
  consequences. Already removed edges and nonedges are included.
- Joint critical drift, global absolute increments, conditional variances,
  and every finite-horizon variance budget before the first failure.
- Simultaneous critical-window concentration, a supported good path,
  extraction of the exact-size clique packing, and original-regularity
  initialization of all tracks below their critical windows.

The `LogNibbleParameters` inputs are explicit scalar inequalities:
3<=k<=5; positive a,g,D,p0; p0<=1; a<=((2/5)*p0)^k;
200*k^3<=a^2*g; k<=a^3*g; nonnegative codegree bound L;
(k^2+k)*L<=a^2*D/100; and L<=a^3*D. They imply the needed
consecutive-density bounds and all logarithmic pointwise margins.

The remaining Section 9 work is now the finite specialization at n0:
prove the parameter bundle, half-window/failure inequalities, and the
rounded endpoint when a=n^(-epsilon/3) and p0=(5/2)*n^(-epsilon/(3*k)).
The existing sparse exponent and polynomial tail estimates already use
the identical failure-bound expression. Their numerical use by the new
route has not yet been certified, so the unchanged-n0 constant-3 claim
in the remaining range stays open.

Verification on 2026-08-27: all 807 supporting modules build in 4403 jobs.
All 2228 requested axiom checks match their exact names and order and
use only propext, Classical.choice, and Quot.sound. The inventory and
reachable acyclic import graph agree exactly. All sources are free of
proof placeholders, added axioms, unsafe evaluation, and computational
limit overrides. New proof files pass line-length and whitespace checks;
only the two existing dirty-dependency warnings remain.

Logs: `tmp/arxiv-2411.18291/build-807.log` and
`tmp/arxiv-2411.18291/audit-807.log`.


## Full Section 9 constant three at the original threshold

The final small-clique parameter estimates close Lemma 9.1, `lem:nibble+`,
with the exact printed constant 3 at n0. The theorem
`exists_sparse_nibble_constant_three_all_positive_ranks` covers every
q > r >= 1 and epsilon <= 2/5, with the original lower bounds on graph
and clique densities and original relative degree error n^(-epsilon).
It returns an actual subfamily of the supplied cliques, decomposing its
support, whose leave has strict face degrees below
3*n^(-epsilon/(3*choose(q,r)))*n. No extra threshold or middle-density
exception remains. This adds nine supporting modules and 21 theorems.

For k=3,4,5, put a=n^(-epsilon/3) and target p=n^(-epsilon/(3*k)).
The logarithmic construction stops at p0=(5/2)*p. Its step half-widths,
window gaps, and all count, edge, and face failure exponents are now
proved at n0. The same finite polynomial tail bounds apply, without
changing concentration constants. The rounded horizon gives leave at
most p0+3*a. Since a=p^k and p<=1/3, this is at most 3*p. When p>1/3,
the empty packing already suffices. The rank-one small-graph case is
handled directly; every other rank meets the required graph-size bound.
The existing pair theorem and k>=6 scaled comparisons complete all cases.

The full-paper audit now leaves only the general greedy lemma's printed
smallness coefficient, the standalone decoder/focusing output coefficient,
and arbitrary larger KSG moduli at unchanged n0. None of these qualify
the already completed main design theorem or sparse absorber at n0.

Verification on 2026-08-27: all 816 supporting modules build in 4412 jobs.
All 2249 requested axiom checks match their exact names and order and
use only propext, Classical.choice, and Quot.sound. The inventory and
reachable acyclic import graph agree exactly. All sources are free of
proof placeholders, added axioms, unsafe evaluation, and computational
limit overrides. New proof files pass line-length and whitespace checks;
only the two existing dirty-dependency warnings remain.

Logs: `tmp/arxiv-2411.18291/build-816.log` and
`tmp/arxiv-2411.18291/audit-816.log`.


## Exact standalone decoder and focusing coefficient at n0

`exists_coloured_decoder_focusing_exact_coefficient` closes `lem:Q0'`
with all of its geometric conclusions and the exact coefficient
2^(q+2)*(4q)^R*u*n^(-7alpha/10), in every positive rank R at n0.
It uses the density, good-subgraph, and punctured rainbow-clique counts
already supplied by the earlier colour construction. The companion
`exists_decoder_focusing_exact_coefficient` exposes only the needed
punctured-clique lower bound. No upper cap on u is required.
This extension adds fourteen modules and 29 checked theorems.

The local decoder construction now enlarges each input q-clique Q to a
single (q+R)-set Z_Q and retains all q-subsets of Z_Q. Every edge of Q
shares the same decoder region. This replaces the excessive coefficient
from enlarging each edge separately; no disjointness of regions is needed.
Repeated refined cliques only reduce the final boundary.

For a face S of size R-1, the input boundary bound theta*n gives a
clique-count bound theta*n/(q-R+1). Lower-dimensional counts preserve
this divisor. A uniform enlargement contains S with probability at most
2*R!/n^|S\Q|. Summing over all possible intersections S intersect Q
bounds the mean face count by 2^R*R!*theta*n/(q-R+1). The corrected
nonnegative concentration theorem constructs choices simultaneously below
twice that budget. Refinement then costs at most 2*(4q)^R*theta,
which is half the final source coefficient when theta=u*2^q*n^(-7alpha/10).
All sampling-size and failure estimates are proved at the original n0.

The focusing half uses actual uniform choices among prescribed punctured
cliques. Its probability bounds also handle intersections too large for
the available free vertices: these have probability zero. The resulting
family has the required n^(-7alpha/10) boundary bound and provides a
focusing clique for every reserve edge, including edges already in the
coloured host. Thus no artificial disjointness hypothesis is added.
Taking the union with the shared decoder family proves the printed lemma.

Verification on 2026-08-27: all 830 supporting modules build in 4426 jobs.
All 2278 requested axiom checks match their exact names and order and
use only propext, Classical.choice, and Quot.sound. The inventory and
reachable acyclic import graph agree exactly. All sources are free of
proof placeholders, added axioms, unsafe evaluation, and computational
limit overrides. New proof files pass line-length and whitespace checks;
only the two existing dirty-dependency warnings remain.

Logs: `tmp/arxiv-2411.18291/build-830.log` and
`tmp/arxiv-2411.18291/audit-830.log`.


## KSG scope and the full rank-one greedy smallness bound

This extension adds six modules and 19 checked theorems. The only remaining
quantitative obligation is now the corrected general greedy process in
rank at least two at the printed smallness threshold.

The KSG scope audit is closed. The source defines N:=r!*choose(q,r) in
its local-decoder lemma, then uses Gamma=Z/NZ and later invokes that decoder
for the multiples of N arising in the integral lift. It does not introduce
or quantify a separate arbitrary modulus in KSG. `paperModulus` records
this value and its equality to the falling factorial (q)_r.
`paper_modular_generators_whp` and `exists_paper_modular_generators` give
all three KSG conclusions at n0 with no extra modulus input. The corrected
probability rate is retained. Earlier results for arbitrary positive moduli
at an explicit modulus-dependent threshold are unchanged.

`literal_greedy_counterexample` refutes the exact forbidden-root wording
of Definition 5.4 for every n>=1025. Take the rank-one graph consisting of
two singleton edges on two vertices, root one vertex at 0, take B to be
that root singleton, and use a one-step sequence with theta=1/32.
The extension is admissible and nontrivial; B and the prescribed root
families are theta-bounded; n^(-1/2)<theta<1/(8*1!^2*2). Nevertheless,
there is no extension avoiding B on every edge, because the root is fixed
in B. The same theorem verifies that the implemented corrected legal set,
which exempts root edges, is nonempty. This does not refute the intended
higher-rank smallness statement; that question remains separate.

For the corrected rank-one process, `rankOne_greedy_probability_one`
proves more than the printed conclusion. If n>=2*v_H, theta>0, and
 theta<1/(8*|H|), then the ordinary process succeeds with probability one
and every edge family retains the input theta bound. The companion
`rankOne_greedy_paper_probability_one` gives the printed 4*theta bound.
No lower density cutoff or asymptotic probability estimate is needed.

Admissibility and a nonempty pattern supply a root edge. Its rank-one
family bound forces the entire run length t<theta*n. Every history has
face degree at most its length. The forbidden graph therefore has fewer
than (theta+|H|*theta)*n vertices, and this is at most n/2 under the printed
smallness assumption. There are enough remaining vertices to extend every
root embedding. A direct finite embedding construction proves availability;
the actual transition supports, legal-family extraction, and equality of
ordinary and stopped success probabilities then establish probability one.

Verification on 2026-08-27: all 836 supporting modules build in 4432 jobs.
All 2297 requested axiom checks match their exact names and order and
use only propext, Classical.choice, and Quot.sound. The inventory and
reachable acyclic import graph agree exactly. All sources are free of
proof placeholders, added axioms, unsafe evaluation, and computational
limit overrides. New proof files pass line-length and whitespace checks;
only the two existing dirty-dependency warnings remain.

Logs: `tmp/arxiv-2411.18291/build-836.log` and
`tmp/arxiv-2411.18291/audit-836.log`.


## Final greedy counterexample and completed source audit

Eight new modules and 32 theorems resolve the last mathematical obligation.
`arbitrarily_large_greedy_linear_counterexamples` refutes Lemma 5.5 even
for the intended process, independently of the earlier Definition 5.4
forbidden-root defect. This is an impossibility of completion, not merely
a failure of the paper's probability estimate.

Take A=ZMod 256, with pattern vertices Option A. All 256 vertices `some a`
are roots; `none` is the free centre. The pattern contains every spoke
from the free centre and a root star centred at `some 0`. It is admissible,
nontrivial, and has at most 512 edges. The auxiliary root carrier is the
32896 unordered pairs of distinct vertices of Option A. For each of the
257 base points, cyclically rotate a bijection from root labels to its
256 incident pairs, and repeat each rotation L times.

All these root sets intersect. For a fixed label and carrier vertex,
only two base points are possible and each determines a unique shift.
Consequently vertex fibres have size at most 2L and every prescribed
root-edge family has degree at most 4L. Embed the carrier in Fin n,
where n=65600L, and set theta=1/16385 and B empty. For every L>=4096,
Lean verifies

- `4L < theta*n`;
- `n^(-1/2) < theta < 1/(8*(2!)^2*|H|)`;
- all prescribed root edges are theta-bounded;
- the number of required copies is t=65792L>n.

Any completed family with disjoint new edges would have distinct free
centres: if two centres coincide, a common root vertex gives a shared
new edge. Thus completion requires t<=n, a contradiction. The ordinary
process success event is empty for every output degree parameter and
its success probability is zero. L can grow beyond every proposed
threshold depending only on the fixed pattern's 257 vertices.

The correction already used throughout the formalization is the sufficient
condition theta<=1/(4*M*(1+4*R!*M)), with M=max(1,|H|) and positive edge
rank R. Its ordinary-process theorem retains the paper's output degree
constant and gives the corrected stretched-exponential success rate.
All applications, including the absorber and Theorem 1.1, meet this
condition at the original n0. Rank one separately admits the printed
linear condition with success probability one.

The final audit was expanded from selected results to all public theorems:
2956 theorem/lemma checks plus three proof-bearing definitions. The full
844-module build and all 2959 exact-name assumption checks pass, using
only the three standard axioms. All 24 labelled source results and the
quantitative parameter/threshold claims have been reviewed. This completes
the formalization with the source corrections stated above.
