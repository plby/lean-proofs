/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
This file formalizes Erdős Problem 387.

Mathematical source:
H. M. Bui, S. Naprienko, K. Pratt, A. Zaharescu,
"Binomial coefficients with divisors avoiding an interval",
arXiv:2605.21221v2 (2026).

Progress log (2026-08-15):
* Phase 1: the mathematical reconstruction and Leanization plan are in
  `tex/387.tex`.
* Phase 2, verified here so far: the exact logical reduction from a
  counterexample for every positive real endpoint; the Archimedean reduction
  from the qualitative fixed-B BNPZ theorem; and, in `CoverAlgebra.lean`, the
  CRT realization, binomial-product identity, divisor splitting, size bound,
  and pairwise-coprimality lemmas used at the algebraic/analytic interface.
  `AnalyticInputs.lean` also derives the exact fixed-modulus dyadic-interval
  PNT used by the public cover proof from the repository's `WeakPNT_AP`, then
  proves the public shifted lower bound for each fixed `(Q,a,h)` and uniformly
  over every fixed finite family.  `CoverLemma.lean` ports and verifies the
  public 1,900-line fixed-parameter covering lemma against that axiom-free PNT
  under the default computational limits.  `CoverBPZPrelude.lean` additionally
  ports the 8,600-line axiom-free public development through the exact point
  immediately preceding its first use of uniform Siegel--Walfisz, and
  `CoverBPZConditional.lean` verifies the remaining wide-cover construction
  with that analytic proposition passed explicitly as a theorem argument.
  `CoverAlgebra.lean` now also packages residual divisor choices as finite
  tuples and proves uniqueness of their product representation under the
  certified pairwise-coprimality hypothesis.  `DivisorStructure.lean`
  formalizes the elementary post-Proposition-6.4 case split: absence of a
  convenient factorization forces a `y ^ 3`-small factor times at most one
  large prime.  `Section6Counting.lean`, `ErrorClasses.lean`, and
  `ErrorCounting.lean` give literal finite sifted/error sets and the complete
  cardinality handoff.  `LocalDensity.lean` proves the exact `k` forbidden
  residue classes modulo every prime greater than `k`, combines them by CRT
  into exactly `k ^ ω(g)` classes for every squarefree modulus `g`, and
  counts their occurrences in finite initial intervals with an explicit
  remainder and in arbitrary half-open intervals.  `BrunSieve.lean` adds the
  lower-bound dual missing from Mathlib's Selberg-sieve API and proves that
  every odd Möbius truncation is a valid lower weight; it now also proves the
  matching upper-sieve theorem for every even truncation.  `BrunMainTerm.lean`
  identifies both main terms with finite subset sums, bounds their tails by a
  finite Euler product, and gives a uniform `[V/2, 3V/2]` comparison under an
  explicit tail hypothesis.  `SieveInstantiation.lean` constructs the literal
  binomial sieve, identifies its sifted sum and multiple sums with the named
  finite candidate sets, evaluates its squarefree local density, combines
  that density with the covering progression by CRT, and proves the uniform
  concrete remainder bound `|R_d| ≤ 4 k ^ ω(d)`, with both lower and upper
  Brun bounds.  Finally, `QualitativeCover.lean` extracts from the public,
  unconditional fixed-parameter cover a natural-number factorization of the
  binomial coefficient into positive, pairwise-coprime residuals whose product
  is exactly `Nat.choose` and whose individual sizes are at most `n / B`.
  `UniformAnalyticInputs.lean` now derives the growing-polylogarithmic shifted
  prime-count estimate from the axiom-free weighted Bombieri--Vinogradov
  theorem in the `BoundedGaps` dependency.  Consequently
  `UnconditionalCover.lean` discharges the public cover's last hypothesis and
  supplies its full wide Section 6 input unconditionally.
  `RefinedCover.lean` then performs the finite CRT refinement by all primes in
  `(k,2k)`, excludes every prime below `2k`, and preserves the certified
  pairwise-coprimality of the residual factors.  `RefinedSieve.lean` runs the
  exact local-density and finite Brun-sieve calculation on the resulting
  modulus `M`, and `RefinedErrorCounting.lean` gives the literal refined
  Section 6 error-class exhaustion and counterexample handoff.
  `DivisorTupleCRT.lean` additionally constructs the canonical residue
  `γ_d (mod d)` of every pairwise-coprime residual-divisor tuple and proves
  the source congruence `n ≡ γ_d (mod d)`.  `CongruenceCounting.lean` and
  `RefinedDivisorCongruence.lean` combine this class with the refined cover
  class and count it in an arbitrary half-open interval.  Finally,
  `TupleCertificateCounting.lean` reindexes every large-component error by
  a finite, candidate-independent tuple certificate and proves the exact
  reciprocal-modulus union bound required at the start of Proposition 6.2.
  `DivisorSwitching.lean` then replaces the exceptional component by its
  complementary residual divisor, proves `b < D` and
  `(large+1)D ≤ X`, and separates the resulting reciprocal main sum from its
  endpoint certificate count.
  `RoughReciprocal.lean` bounds the switched reciprocal sum by the `k`th
  power of a one-dimensional rough harmonic mass.  `RoughHarmonicEstimate.lean`
  identifies that mass with a primorial-coprime harmonic sum, proves the
  elementary density inequality `V(D) log(D+1) ≤ 1`, applies the existing
  all-endpoint Wirsing theorem, and obtains the uniform
  `log T / log z` envelope.  `RoughIntervalEstimate.lean` sharpens this by
  injecting every rough integer into its least-prime-factor fibre and using
  Mathlib's Chebyshev bound to gain the essential factor `1 / log z` on a
  bounded-ratio interval.  `LocalizedSwitchingEstimate.lean` proves the
  source localization `D < 3 gᵢ bᵢ` and `bᵢ gᵢ < 2 B D`, tensors that short
  interval estimate with the remaining coordinates, and also replaces the
  invalid coordinate-box endpoint count by the product-sensitive estimate
  `#certificates ≤ T^2 * ∑ 1 / certificate.value`.  Finally,
  `SwitchedClassSieve.lean` rebuilds the exact local-density and even-Brun
  upper sieve inside every switched CRT class, with uniform remainder
  `4 k^ω(d)`, and combines the classes into a fully explicit localized finite
  form of Proposition 6.2.  Its remaining large-error work is the eventual
  specialization of the displayed finite bound along the paper's parameter
  scale.  `AlmostPrimeExhaustion.lean` corrects the convenient-error set to
  require every component to be at most the medium threshold, proves the two
  finite exponent comparisons that force a second large prime, and splits
  the last error set into the exact comparable-prime and separated-prime
  alternatives of Propositions 6.5 and 6.6.
  `ParameterScale.lean` encodes every fractional power used in these five
  estimates as an exact power of one natural base and verifies both final
  almost-prime scale inequalities and the `X^.99` divisor-switch endpoint
  inequality by integer exponent arithmetic.
  `PrimeReciprocalBound.lean` and `RefinedLogarithmicSieve.lean` sharpen the
  Brun truncation to logarithmic depth, provide the adjacent even upper
  depth, and bound the reciprocal Euler product by a power of two at that
  same depth.  `SubpowerScale.lean` and `SubpowerAnalytic.lean` specialize
  the fixed-parameter route to `log X / log z = N^2`: both switched rough
  masses are `O(N^2)`, the localized reciprocal-certificate main term is
  `O(1/N)`, and the product-sensitive certificate count divided by `X`
  tends to zero.  `SubpowerLargeError.lean` combines these estimates with
  the adjacent even Brun depth and its CRT endpoint term to prove that the
  refined large-error cardinality, normalized by the sifted scale `X * V`,
  tends to zero.  `SubpowerSiftedLower.lean` proves the matching eventual
  lower bound `X * V / (16M)` for the refined sifted set and concludes that
  the large-error set is eventually strictly smaller.
  `ComparablePrimeCertificates.lean`, `ComparablePrimeEstimate.lean`, and
  `SubpowerComparable.lean` now give the exact two-prime CRT cover, prove the
  binary-shell reciprocal estimate, absorb the Brun endpoint, and show that
  the normalized comparable-prime error is eventually at most
  `18 * (2 * Cπ / log 2) ^ 2 / (M * k) + ε`, with the refined progression
  density `1 / M` retained.  It also packages the estimate into the final
  fixed budget `X * V / (32 * M)`.  `ReciprocalEnergy.lean`,
  `RoughDivisorBound.lean`, and `SubpowerReciprocalEnergy.lean` prove the
  cleared-denominator squarefull certificate from BNPZ Lemma 9.1, reindex
  reciprocal-energy solutions by their squarefull products, prove
  `τ(n) ≤ 2^Ω(n)` and `z^Ω(n) ≤ n` for rough `n`, and specialize the resulting
  `2ℓ`-variable energy bound to an explicit `2^{O_ℓ(N²)}` loss on the
  subpower scale.  `AdditiveCharacterOrthogonality.lean`,
  `ModularReciprocalEnergy.lean`, `ReciprocalMoment.lean`,
  `RoughDivisorFamily.lean`, `OffDiagonalMoment.lean`, and
  `ModularMomentFamily.lean` formalize the finite high-moment expansion from
  Lemma 9.2: additive-character fibres, cleared modular reciprocal
  numerators, the rational diagonal, and the reindexing of every nonzero
  numerator by its family of rough divisors.  Finally,
  `SubpowerOffDiagonalMoment.lean` and `SubpowerModularMoment.lean` absorb
  both divisor-code losses into the subpower base and prove the complete
  modulus-family moment bound.  `InversePhaseOrthogonality.lean` also proves
  the exact `T₂` cancellation: equality of the phases `ha/r₁` and
  `ha/r₂` modulo `q` forces congruence modulo `q / gcd(q,h)`, hence the
  literal diagonal when this reduced modulus exceeds the short box.
  `HighMomentExpansion.lean`, `BilinearMomentInequality.lean`, and
  `ConvenientMomentReduction.lean` now open the ordered high moment without
  losing its phase, prove finite Parseval with its required modulus factor,
  place the chosen unimodular coefficient into the short-variable weight,
  and complete the exact Hölder--Cauchy reduction to the two checked moments.
  `KloostermanOrthogonality.lean` proves the complete inverse-phase second
  moment exactly and its incomplete analogue by finite Fourier
  orthogonality.  `InverseWeylDifferencing.lean`,
  `FiniteWeylInequality.lean`, and `InverseRationalFunction.lean` provide an
  arbitrary-depth finite Weyl-differencing inequality for reciprocal phases
  together with the exact recursively cleared numerator/denominator formula.
  `InverseRationalPolynomial.lean` identifies these functions with literal
  prime-field polynomials: the denominator is monic of exact degree `2^j`,
  its full pole list has exactly `2^j` entries with multiplicity, and the
  numerator has degree at most `2^j`.
  `PoleTranslation.lean` formalizes the source's Artin--Schreier
  nondegeneracy preparation: a nonempty proper pole set cannot be invariant
  under a nonzero prime-field translation, paired translate-differences at
  most double its cardinality, and under `2^j < p` an iterated difference of
  one reciprocal pole still has a simple pole.
  `ArtinSchreierObstruction.lean` puts every such partial fraction over a
  common polynomial denominator, proves that its numerator is nonzero at
  every supported pole, and rules out every reduced representation
  `g^p - g + c` by exact cross-multiplication and cancellation.
  `InversePhasePartialFraction.lean` identifies that common fraction with
  the exact positive-shift phase used by `FiniteWeylInequality.lean` and
  transports both pole survival and the Artin--Schreier exclusion to the
  natural-number shift convention.  `RationalWeilWeight.lean`,
  `RationalWeilProbe.lean`, `RationalArtinCancellation.lean`, and
  `RationalArtinPolynomial.lean` construct the zero-extended multiplicative
  Euler weight, a derivative probe with one simple and all remaining double
  pole zeros, prove complete affine-character cancellation on every probe
  line, and deduce that the resulting rational Artin polynomial has degree
  strictly less than twice the number of surviving poles.
  `RationalMonicFactors.lean`, `RationalLocalEuler.lean`,
  `RationalEulerCoefficients.lean`, `RationalFiniteEuler.lean`, and
  `RationalReciprocalRoots.lean` now supply the unique-factorization Euler
  product and its division-free logarithmic derivative, factor the Artin
  polynomial into reciprocal linear factors, and identify the Euler
  logarithmic coefficients with reciprocal-root power sums.
  `RationalRootPhase.lean`, `RationalTraceBridge.lean`, and
  `RationalClosedPoints.lean` prove the minimal-polynomial trace formula and
  closed-point reindexing for arbitrary finite extensions.  Consequently the
  zero-extended rational trace sum over every finite extension is exactly the
  negative corresponding power sum of the fixed reciprocal roots.
  `RationalRootRadius.lean` applies the checked bounded-even-power-sum theorem
  to this identity: an extension-uniform `C * p^m` estimate places every
  reciprocal root in the radius-`sqrt p` disk and gives the literal
  prime-field zero-extended simple-pole bound with conductor factor
  `2 * #poles - 1`.  `RationalTracePolynomials.lean` maps the simple-pole
  numerator and denominator to every finite extension, clears the two halves
  of the Frobenius orbit, identifies the resulting rational fraction with the
  embedded trace away from its poles, and bounds the cleared degrees.
  `RationalStepanovParameters.lean` through
  `RationalStepanovNonvanishing.lean` construct the Stepanov auxiliary
  polynomial, obtain its coefficients from a strict dimension inequality,
  prove all prescribed Hasse-derivative vanishings, and prove nonvanishing by
  an exact mixed-radix computation of the local pole orders.
  `RationalStepanovDegree.lean`, `RationalStepanovFiberCount.lean`, and
  `RationalStepanovExtensionSum.lean` turn this into the uniform even-extension
  trace-fibre estimate required by `RationalRootRadius.lean`.  Consequently
  the prime-field zero-extended rational Weil bound is now unconditional.
  `PositiveShiftCompleteSum.lean` specializes it to the exact positive-shift
  phase produced by finite Weyl differencing and restores the finitely many
  pole values.  `CyclicWeylCompletion.lean` proves the exact finite cyclic
  autocorrelation identity and uses one difference to remove an arbitrary
  linear Fourier twist, giving a checked complete twisted reciprocal-sum
  bound from the two-pole rational estimate.  Finally,
  `ReciprocalIntervalCompletion.lean` combines that bound with the existing
  kernel-checked interval Fourier coefficients: it proves the exact
  completion identity and the resulting logarithmic-loss bound for every
  integer interval of length at most the prime modulus.  Its completion
  theorem is phase-generic.  `IteratedReciprocalCompletion.lean` applies it
  after an arbitrary list of positive reciprocal differences: the added
  linear Fourier twist disappears under one cyclic difference, the pole
  conductor grows by one factor of two, and the resulting completed and
  incomplete estimates are proved with explicit constants.
  `IteratedWeylBound.lean` then iterates the finite positive-shift inequality
  itself.  Its recursive nonnegative envelope applies to every intermediate
  interval length and inserts the completed rational bound at the selected
  bottom depth, yielding an unconditional explicit bound for the original
  short reciprocal phase.
  `ProgressionFourier.lean` supplies the exact complementary counting
  interface: the cardinality of one residue class on an arbitrary finite
  natural or integer set is expanded into its zero frequency and explicit
  nonzero additive-character frequencies.  On integer intervals its
  coefficient convention is transported to the checked Waring interval
  kernel and has total norm at most `q * (log q + 1)`.  Thus subsequent
  certificate summations can retain endpoint cancellation instead of paying
  an unsummable absolute `+2` per class.
  `BezoutAdditiveCharacter.lean` also proves the exact character-valued
  Bézout reciprocity identity of BNPZ Lemma 8.3 for coprime product moduli,
  using Mathlib's canonical `Nat.gcdA` and `Nat.gcdB` coefficients.  This is
  the CRT phase factorization needed to combine the progression formula with
  the reciprocal phases in the medium and separated-prime estimates.
  `SimultaneousFourier.lean` composes these results with the already-defined
  simultaneous natural-number class: it proves equality with the associated
  `ZMod (M*d)` fibre, expands its cardinality exactly, identifies both CRT
  coordinates of the canonical residue, and splits every resulting Fourier
  phase into its divisor-modulus and fixed-progression factors.
  `TupleCoordinateCRT.lean` then removes a distinguished coordinate from a
  full tuple certificate.  It constructs the complementary residue modulo
  the product of all other coordinates, proves its congruences, proves the
  two complementary moduli coprime, identifies the full canonical residue
  with their simultaneous residue, and supplies the corresponding split
  additive-character identity.  The source-shaped reciprocity corollary
  rewrites the nontrivial factor using `Nat.gcdB D dᵢ`, the canonical inverse
  of the varying coordinate modulo the complementary product.
  `MediumCertificates.lean` now places every medium error in the same
  independent tuple-certificate cover at the lower threshold and records
  the distinguished-coordinate inequalities
  `(medium+1)D ≤ X` and `X/2 < B*large*D` needed for the dyadic
  Proposition 6.3 summation.  `TupleCoordinateCRT.lean` also proves the
  source nondegeneracy `gcd(γ_D-i,D)=1` whenever the tuple factors are
  `z`-rough and `k ≤ z`.
  `CompositeKloostermanCompletion.lean` supplies the exact finite Fourier
  completion for the zero-extended unit reciprocal phase at every nonzero
  composite modulus and proves the logarithmic-loss incomplete estimate
  from an explicit uniform completed-sum bound.  `PrimeKloostermanBound.lean`
  derives the prime local estimate from the checked rational Weil theorem by
  the Möbius substitution `x=t/(t+1)`, including the one-pole and degenerate
  frequency cases.  `KloostermanMultiplicativity.lean` proves exact CRT
  factorization and verifies that both Bézout twists are units, and
  `SquarefreeKloostermanBound.lean` multiplies the local estimates to obtain
  `4^ω(q) * sqrt(q) * sqrt(gcd(b,q))` for every squarefree rough modulus.
  Thus the remaining content of BNPZ Lemma 8.2 is its prime-power local
  estimate and the assembly of arbitrary composite moduli.
  Thus the medium estimate, the remaining dyadic certificate/scale summation
  for the convenient error, and the separated Section 8--10 classes remain
  to be proved.
  An axiom audit of this
  composition reports only `propext`, `Classical.choice`, and
  `Quot.sound`.
* Remaining dependency: prove the fixed-parameter specializations of the
  Section 7--10 divisor-distribution bounds and use them to prove the
  fixed-`B` counterexample theorem.  The exact
  transported local density, both Brun inequalities, their Euler-product
  main terms, a powers-of-two moment criterion for the omitted Brun tail, an
  explicit cardinal lower bound with uniform CRT endpoint error, and
  arbitrary-large existence for every fixed threshold are now proved in
  `QualitativeSieve.lean`.  That file now also bounds the complete moment by
  a polynomial in the roughness threshold, chooses an explicit odd depth
  twice a base-two logarithm of this polynomial, and produces a sifted
  parameter in an explicit dyadic interval.  Thus the qualitative route no
  longer needs a separate beta-sieve fundamental lemma.  Freezing `B` and `k`
  also provides an independent elementary cover route.  It now
  also restricts to an explicit affine subprogression on which every
  `p ≤ k` residual valuation is constant, splits each residual into that
  fixed small-prime coefficient and its complementary large-prime part, and
  proves that the latter is `z`-rough at every sifted parameter.  The
  surviving work is the eventual specialization of the large bound and the
  Section 8--10 medium, convenient, comparable-prime, and separated-prime
  divisor-distribution estimates.
-/

import ErdosProblems.Erdos387.AdditiveCharacterOrthogonality
import ErdosProblems.Erdos387.AnalyticInputs
import ErdosProblems.Erdos387.AlmostPrimeExhaustion
import ErdosProblems.Erdos387.ArtinSchreierObstruction
import ErdosProblems.Erdos387.BrunSieve
import ErdosProblems.Erdos387.BrunMainTerm
import ErdosProblems.Erdos387.BezoutAdditiveCharacter
import ErdosProblems.Erdos387.BilinearMomentInequality
import ErdosProblems.Erdos387.CoverAlgebra
import ErdosProblems.Erdos387.CoverBPZConditional
import ErdosProblems.Erdos387.CoverBPZPrelude
import ErdosProblems.Erdos387.CoverLemma
import ErdosProblems.Erdos387.CyclicWeylCompletion
import ErdosProblems.Erdos387.CongruenceCounting
import ErdosProblems.Erdos387.ComparablePrimeCertificates
import ErdosProblems.Erdos387.ComparablePrimeEstimate
import ErdosProblems.Erdos387.CompositeKloostermanCompletion
import ErdosProblems.Erdos387.SquarefreeKloostermanBound
import ErdosProblems.Erdos387.ConvenientMomentReduction
import ErdosProblems.Erdos387.DivisorStructure
import ErdosProblems.Erdos387.DivisorSwitching
import ErdosProblems.Erdos387.DivisorTupleCRT
import ErdosProblems.Erdos387.ErrorClasses
import ErdosProblems.Erdos387.ErrorCounting
import ErdosProblems.Erdos387.FiniteWeylInequality
import ErdosProblems.Erdos387.LocalDensity
import ErdosProblems.Erdos387.LocalizedSwitchingEstimate
import ErdosProblems.Erdos387.InversePhaseOrthogonality
import ErdosProblems.Erdos387.InversePhasePartialFraction
import ErdosProblems.Erdos387.InverseRationalFunction
import ErdosProblems.Erdos387.InverseRationalPolynomial
import ErdosProblems.Erdos387.IteratedReciprocalCompletion
import ErdosProblems.Erdos387.IteratedWeylBound
import ErdosProblems.Erdos387.HighMomentExpansion
import ErdosProblems.Erdos387.KloostermanOrthogonality
import ErdosProblems.Erdos387.ModularMomentFamily
import ErdosProblems.Erdos387.ModularReciprocalEnergy
import ErdosProblems.Erdos387.MediumCertificates
import ErdosProblems.Erdos387.OffDiagonalMoment
import ErdosProblems.Erdos387.Endpoint
import ErdosProblems.Erdos387.PoleTranslation
import ErdosProblems.Erdos387.PositiveShiftCompleteSum
import ErdosProblems.Erdos387.ProgressionFourier
import ErdosProblems.Erdos387.QualitativeCover
import ErdosProblems.Erdos387.QualitativeCounting
import ErdosProblems.Erdos387.QualitativeDivisorStructure
import ErdosProblems.Erdos387.QualitativeRoughCounting
import ErdosProblems.Erdos387.QualitativeSieve
import ErdosProblems.Erdos387.RationalArtinPolynomial
import ErdosProblems.Erdos387.RationalClosedPoints
import ErdosProblems.Erdos387.RationalRootRadius
import ErdosProblems.Erdos387.RationalStepanovAuxiliary
import ErdosProblems.Erdos387.RationalStepanovDegree
import ErdosProblems.Erdos387.RationalStepanovExtensionSum
import ErdosProblems.Erdos387.RationalStepanovFiberCount
import ErdosProblems.Erdos387.RationalStepanovLinear
import ErdosProblems.Erdos387.RationalStepanovNonvanishing
import ErdosProblems.Erdos387.RationalStepanovParameters
import ErdosProblems.Erdos387.RationalTracePolynomials
import ErdosProblems.Erdos387.ReciprocalIntervalCompletion
import ErdosProblems.Erdos387.ParameterScale
import ErdosProblems.Erdos387.PrimeReciprocalBound
import ErdosProblems.Erdos387.RefinedCover
import ErdosProblems.Erdos387.RefinedErrorCounting
import ErdosProblems.Erdos387.RefinedDivisorCongruence
import ErdosProblems.Erdos387.RefinedSieve
import ErdosProblems.Erdos387.RefinedLogarithmicSieve
import ErdosProblems.Erdos387.RoughReciprocal
import ErdosProblems.Erdos387.RoughHarmonicEstimate
import ErdosProblems.Erdos387.RoughIntervalEstimate
import ErdosProblems.Erdos387.ReciprocalEnergy
import ErdosProblems.Erdos387.ReciprocalMoment
import ErdosProblems.Erdos387.RoughDivisorBound
import ErdosProblems.Erdos387.RoughDivisorFamily
import ErdosProblems.Erdos387.Section6Bridge
import ErdosProblems.Erdos387.Section6Counting
import ErdosProblems.Erdos387.SieveInstantiation
import ErdosProblems.Erdos387.SimultaneousFourier
import ErdosProblems.Erdos387.TupleCertificateCounting
import ErdosProblems.Erdos387.TupleCoordinateCRT
import ErdosProblems.Erdos387.SwitchedClassSieve
import ErdosProblems.Erdos387.SubpowerScale
import ErdosProblems.Erdos387.SubpowerAnalytic
import ErdosProblems.Erdos387.SubpowerComparable
import ErdosProblems.Erdos387.SubpowerLargeError
import ErdosProblems.Erdos387.SubpowerModularMoment
import ErdosProblems.Erdos387.SubpowerOffDiagonalMoment
import ErdosProblems.Erdos387.SubpowerReciprocalEnergy
import ErdosProblems.Erdos387.SubpowerSiftedLower
import ErdosProblems.Erdos387.UnconditionalCover

namespace Erdos387

/-- The positive answer proposed in Erdős Problem 387. -/
def UniversalNearDivisor (c : ℝ) : Prop :=
  0 < c ∧ ∀ n k : ℕ, 1 ≤ k → k < n →
    ∃ d : ℕ, (d : ℝ) ∈ Set.Ioc (c * n) n ∧ d ∣ n.choose k

/-- A counterexample at the real endpoint `c * n`. -/
def IsCounterexample (c : ℝ) (n k : ℕ) : Prop :=
  1 ≤ k ∧ k < n ∧
    ∀ d : ℕ, (d : ℝ) ∈ Set.Ioc (c * n) n → ¬d ∣ n.choose k

/-- A counterexample at the fixed-parameter endpoint `n / B`. -/
def IsFixedBCounterexample (B n k : ℕ) : Prop :=
  1 ≤ k ∧ k < n ∧
    ∀ d : ℕ, (d : ℝ) ∈ Set.Ioc ((n : ℝ) / B) n → ¬d ∣ n.choose k

/-- Exact interface to Sections 6--10 of BNPZ: after the covering factors
have been removed, it is enough to exclude every product formed from one
divisor of each residual factor. -/
theorem fixedBCounterexample_of_cover {B n k : ℕ} (hk : 1 ≤ k) (hkn : k < n)
    (D : CoverFactorization n k)
    (hexclude : ∀ e : ℕ → ℕ,
      (∀ i < k, e i ∣ (n - i) / D.g i) →
      ¬((∏ i ∈ Finset.range k, e i : ℕ) : ℝ) ∈ Set.Ioc ((n : ℝ) / B) n) :
    IsFixedBCounterexample B n k := by
  refine ⟨hk, hkn, ?_⟩
  intro d hd hdvd
  obtain ⟨e, he, hde⟩ := exists_coverDivisorFactors D hdvd
  apply hexclude e he
  simpa [hde] using hd

/-- The last logical step: counterexamples for every positive real `c`
give the exact negative answer in the formal-conjectures statement. -/
theorem erdos_387_of_counterexamples
    (h : ∀ c : ℝ, 0 < c → ∃ n k : ℕ, IsCounterexample c n k) :
    False ↔ ∃ c : ℝ, UniversalNearDivisor c := by
  constructor
  · exact False.elim
  · rintro ⟨c, hc, hall⟩
    obtain ⟨n, k, hk, hkn, hbad⟩ := h c hc
    obtain ⟨d, hd, hdvd⟩ := hall n k hk hkn
    exact hbad d hd hdvd

/-- The Archimedean reduction used in the qualitative BNPZ argument:
counterexamples for every integer weight `B ≥ 2` rule out every real
constant `c > 0`. -/
theorem counterexamples_of_fixedB
    (h : ∀ B : ℕ, 2 ≤ B → ∃ n k : ℕ, IsFixedBCounterexample B n k) :
    ∀ c : ℝ, 0 < c → ∃ n k : ℕ, IsCounterexample c n k := by
  intro c hc
  obtain ⟨B, hB⟩ := exists_nat_gt (max 2 (c⁻¹))
  have hBtwo : 2 ≤ B := by
    exact_mod_cast (le_trans (le_max_left 2 c⁻¹) (le_of_lt hB))
  obtain ⟨n, k, hk, hkn, hbad⟩ := h B hBtwo
  refine ⟨n, k, hk, hkn, ?_⟩
  intro d hd hdvd
  apply hbad d ?_ hdvd
  refine ⟨?_, hd.2⟩
  have hBinv : c⁻¹ < (B : ℝ) := lt_of_le_of_lt (le_max_right 2 c⁻¹) hB
  have hBpos : (0 : ℝ) < B := by positivity
  have hBc : 1 / (B : ℝ) < c := by
    exact (one_div_lt hBpos hc).2 (by simpa [one_div] using hBinv)
  calc
    (n : ℝ) / B = (n : ℝ) * (1 / B) := by ring
    _ ≤ (n : ℝ) * c := by gcongr
    _ < d := by simpa [mul_comm] using hd.1

/-- BNPZ only needs to supply the fixed-parameter construction beyond some
absolute threshold.  This is the quantifier form closest to the paper. -/
theorem counterexamples_of_eventually_fixedB
    (h : ∃ B₀ : ℕ, ∀ B : ℕ, B₀ ≤ B →
      ∃ n k : ℕ, IsFixedBCounterexample B n k) :
    ∀ c : ℝ, 0 < c → ∃ n k : ℕ, IsCounterexample c n k := by
  obtain ⟨B₀, hB₀⟩ := h
  intro c hc
  obtain ⟨B, hB⟩ :=
    exists_nat_gt (max ((max 2 B₀ : ℕ) : ℝ) (c⁻¹))
  have hB₀B : B₀ ≤ B := by
    have hB₀max : (B₀ : ℝ) ≤ (max 2 B₀ : ℕ) := by
      exact_mod_cast le_max_right 2 B₀
    exact_mod_cast (le_trans (le_trans hB₀max
      (le_max_left ((max 2 B₀ : ℕ) : ℝ) c⁻¹)) (le_of_lt hB))
  obtain ⟨n, k, hk, hkn, hbad⟩ := hB₀ B hB₀B
  refine ⟨n, k, hk, hkn, ?_⟩
  intro d hd hdvd
  apply hbad d ?_ hdvd
  refine ⟨?_, hd.2⟩
  have hBinv : c⁻¹ < (B : ℝ) :=
    lt_of_le_of_lt (le_max_right ((max 2 B₀ : ℕ) : ℝ) c⁻¹) hB
  have hBtwo : (2 : ℝ) < B :=
    lt_of_le_of_lt (le_trans (by exact_mod_cast le_max_left 2 B₀)
      (le_max_left ((max 2 B₀ : ℕ) : ℝ) c⁻¹)) hB
  have hBpos : (0 : ℝ) < B := lt_trans (by norm_num) hBtwo
  have hBc : 1 / (B : ℝ) < c := by
    exact (one_div_lt hBpos hc).2 (by simpa [one_div] using hBinv)
  calc
    (n : ℝ) / B = (n : ℝ) * (1 / B) := by ring
    _ ≤ (n : ℝ) * c := by gcongr
    _ < d := by simpa [mul_comm] using hd.1

/-- Direct reduction from the quantitative conclusion of BNPZ Theorem 1.4.
The paper supplies the hypothesis (indeed with additional control on `n` and
`k`); `tendsto_BNPZEndpoint` supplies the endpoint limit. -/
theorem counterexamples_of_eventually_BNPZ
    (h : ∀ᶠ k : ℕ in Filter.atTop,
      ∃ n : ℕ, 1 ≤ k ∧ k < n ∧
        ∀ d : ℕ,
          (d : ℝ) ∈ Set.Ioc (BNPZEndpoint k * n) n → ¬d ∣ n.choose k) :
    ∀ c : ℝ, 0 < c → ∃ n k : ℕ, IsCounterexample c n k := by
  intro c hc
  obtain ⟨k, ⟨n, hk, hkn, hbad⟩, hkc⟩ :=
    (h.and (eventually_BNPZEndpoint_lt hc)).exists
  refine ⟨n, k, hk, hkn, ?_⟩
  intro d hd hdvd
  apply hbad d ?_ hdvd
  refine ⟨?_, hd.2⟩
  exact lt_of_le_of_lt (by gcongr) hd.1

/-- Once the fixed-parameter BNPZ theorem is formalized, this is the exact
statement requested by the formal-conjectures specification. -/
theorem erdos_387_of_fixedB
    (h : ∀ B : ℕ, 2 ≤ B → ∃ n k : ℕ, IsFixedBCounterexample B n k) :
    False ↔ ∃ c : ℝ, 0 < c ∧ ∀ n k : ℕ, 1 ≤ k → k < n →
      ∃ d : ℕ, (d : ℝ) ∈ Set.Ioc (c * n) n ∧ d ∣ n.choose k := by
  apply erdos_387_of_counterexamples
  exact counterexamples_of_fixedB h

/-- Exact final reduction from the eventual fixed-`B` form proved by BNPZ. -/
theorem erdos_387_of_eventually_fixedB
    (h : ∃ B₀ : ℕ, ∀ B : ℕ, B₀ ≤ B →
      ∃ n k : ℕ, IsFixedBCounterexample B n k) :
    False ↔ ∃ c : ℝ, 0 < c ∧ ∀ n k : ℕ, 1 ≤ k → k < n →
      ∃ d : ℕ, (d : ℝ) ∈ Set.Ioc (c * n) n ∧ d ∣ n.choose k := by
  apply erdos_387_of_counterexamples
  exact counterexamples_of_eventually_fixedB h

/-- Exact final reduction from the quantitative interval in BNPZ Theorem 1.4. -/
theorem erdos_387_of_eventually_BNPZ
    (h : ∀ᶠ k : ℕ in Filter.atTop,
      ∃ n : ℕ, 1 ≤ k ∧ k < n ∧
        ∀ d : ℕ,
          (d : ℝ) ∈ Set.Ioc (BNPZEndpoint k * n) n → ¬d ∣ n.choose k) :
    False ↔ ∃ c : ℝ, 0 < c ∧ ∀ n k : ℕ, 1 ≤ k → k < n →
      ∃ d : ℕ, (d : ℝ) ∈ Set.Ioc (c * n) n ∧ d ∣ n.choose k := by
  apply erdos_387_of_counterexamples
  exact counterexamples_of_eventually_BNPZ h

/-- The exact remaining theorem obligation after all elementary reductions:
construct a cover for each `B` and prove the BNPZ residual-product exclusion. -/
theorem erdos_387_of_cover_certificates
    (h : ∀ B : ℕ, 2 ≤ B →
      ∃ n k : ℕ, ∃ D : CoverFactorization n k,
        1 ≤ k ∧ k < n ∧
        ∀ e : ℕ → ℕ,
          (∀ i < k, e i ∣ (n - i) / D.g i) →
          ¬((∏ i ∈ Finset.range k, e i : ℕ) : ℝ) ∈ Set.Ioc ((n : ℝ) / B) n) :
    False ↔ ∃ c : ℝ, 0 < c ∧ ∀ n k : ℕ, 1 ≤ k → k < n →
      ∃ d : ℕ, (d : ℝ) ∈ Set.Ioc (c * n) n ∧ d ∣ n.choose k := by
  apply erdos_387_of_fixedB
  intro B hB
  obtain ⟨n, k, D, hk, hkn, hexclude⟩ := h B hB
  exact ⟨n, k, fixedBCounterexample_of_cover hk hkn D hexclude⟩

/-- Exact remaining analytic interface for the unconditional absorber route:
it suffices to make the four explicit error classes smaller than the sifted
parameter set for one absorber at every fixed weight. -/
theorem erdos_387_of_absorber_error_bounds
    (h : ∀ m : ℕ, 3 ≤ m →
      ∃ k : ℕ, ∃ C : CoverBPZ.AbsorberCoverValid m k,
        ∃ T z y medium large : ℕ,
          3 ≤ k ∧ 2 ≤ y ∧
          (AbsorberLargeErrors C T z large).card +
              (AbsorberMediumErrors C T z medium large).card +
              (AbsorberConvenientErrors C T z y medium).card +
              (AbsorberAlmostPrimeErrors C T z y medium).card <
            (SiftedAbsorberParameterCandidates C T z).card) :
    False ↔ ∃ c : ℝ, 0 < c ∧ ∀ n k : ℕ, 1 ≤ k → k < n →
      ∃ d : ℕ, (d : ℝ) ∈ Set.Ioc (c * n) n ∧ d ∣ n.choose k := by
  apply erdos_387_of_fixedB
  intro B hB
  let m := max 3 B
  have hm3 : 3 ≤ m := le_max_left 3 B
  have hBm : B ≤ m := le_max_right 3 B
  obtain ⟨k, C, T, z, y, medium, large, hk3, hy, herrors⟩ := h m hm3
  obtain ⟨t, _htWindow, _hcop, hbad⟩ :=
    exists_absorberCounterexample_of_error_sum_lt C
      (by omega : 0 < m) (by omega : 0 < k) hy herrors
  refine ⟨C.nNat t, k, ?_, C.k_lt_nNat t, ?_⟩
  · omega
  · intro d hdB hdvd
    apply hbad d ?_ hdvd
    refine ⟨?_, hdB.2⟩
    have hBpos : (0 : ℝ) < B := by exact_mod_cast (lt_of_lt_of_le (by norm_num) hB)
    have hmpos : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
    exact lt_of_le_of_lt
      (div_le_div_of_nonneg_left (by positivity) hBpos (by exact_mod_cast hBm))
      hdB.1

/-- Equivalent frozen formulation of the remaining analytic obligation: it
suffices to make the single rough-product error set smaller than the sifted
set.  All small-prime choices have already been absorbed into one fixed
coefficient by `QualitativeDivisorStructure.lean`. -/
theorem erdos_387_of_frozen_roughProduct_bounds
    (h : ∀ m : ℕ, 3 ≤ m →
      ∃ k : ℕ, ∃ C : CoverBPZ.AbsorberCoverValid m k,
        ∃ t₀ T z : ℕ,
          3 ≤ k ∧
          (FrozenRoughProductErrors C t₀ T z).card <
            (SiftedAbsorberParameterCandidates (C.frozen t₀) T z).card) :
    False ↔ ∃ c : ℝ, 0 < c ∧ ∀ n k : ℕ, 1 ≤ k → k < n →
      ∃ d : ℕ, (d : ℝ) ∈ Set.Ioc (c * n) n ∧ d ∣ n.choose k := by
  apply erdos_387_of_fixedB
  intro B hB
  let m := max 3 B
  have hm3 : 3 ≤ m := le_max_left 3 B
  have hBm : B ≤ m := le_max_right 3 B
  obtain ⟨k, C, t₀, T, z, hk3, herrors⟩ := h m hm3
  obtain ⟨t, _htWindow, _hcop, hbad⟩ :=
    exists_frozenAbsorberCounterexample_of_roughProduct_card_lt
      C (by omega : 0 < m) (by omega : 0 < k) herrors
  refine ⟨(C.frozen t₀).nNat t, k, ?_, (C.frozen t₀).k_lt_nNat t, ?_⟩
  · omega
  · intro d hdB hdvd
    apply hbad d ?_ hdvd
    refine ⟨?_, hdB.2⟩
    have hBpos : (0 : ℝ) < B := by
      exact_mod_cast (lt_of_lt_of_le (by norm_num) hB)
    have hmpos : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
    exact lt_of_le_of_lt
      (div_le_div_of_nonneg_left (by positivity) hBpos
        (by exact_mod_cast hBm))
      hdB.1

/-- Exact remaining analytic interface on the literal BNPZ refined
progression.  The cover and its finite CRT refinement are unconditional;
only the four Section 7--10 error estimates remain in this hypothesis. -/
theorem erdos_387_of_refined_error_bounds
    (h : ∀ B K : ℕ, 3 ≤ B →
      ∀ S : CoverBPZ.BPZSection6Input B K,
        ∃ X z y medium large : ℕ,
          2 ≤ y ∧
          (CoverBPZ.RefinedLargeErrors S X z large).card +
              (CoverBPZ.RefinedMediumErrors S X z medium large).card +
              (CoverBPZ.RefinedConvenientErrors S X z y medium).card +
              (CoverBPZ.RefinedAlmostPrimeErrors S X z y medium).card <
            (RefinedSiftedCandidates S X z).card) :
    False ↔ ∃ c : ℝ, 0 < c ∧ ∀ n k : ℕ, 1 ≤ k → k < n →
      ∃ d : ℕ, (d : ℝ) ∈ Set.Ioc (c * n) n ∧ d ∣ n.choose k := by
  apply erdos_387_of_fixedB
  intro B hB
  let m := max 3 B
  have hm3 : 3 ≤ m := le_max_left 3 B
  have hBm : B ≤ m := le_max_right 3 B
  obtain ⟨S, -⟩ :=
    CoverBPZ.unconditional_fixed_B_cover_section6_input m m hm3
  obtain ⟨X, z, y, medium, large, hy, herrors⟩ := h m m hm3 S
  obtain ⟨n, _hnWindow, hn, _hnRefined, _hrough, hbad⟩ :=
    CoverBPZ.exists_refined_counterexample_of_error_sum_lt
      S (by omega : 0 < m) hy herrors
  refine ⟨n, S.k, ?_, hn, ?_⟩
  · exact le_trans (by norm_num) S.hk3
  · intro d hdB hdvd
    apply hbad d ?_ hdvd
    refine ⟨?_, hdB.2⟩
    have hBpos : (0 : ℝ) < B := by
      exact_mod_cast (lt_of_lt_of_le (by norm_num) hB)
    have hmpos : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
    exact lt_of_le_of_lt
      (div_le_div_of_nonneg_left (by positivity) hBpos
        (by exact_mod_cast hBm))
      hdB.1

/-- The sharpened remaining analytic interface matching the five divisor
estimates in BNPZ Propositions 6.2--6.6.  The almost-prime case has been
split unconditionally by `AlmostPrimeExhaustion.lean`. -/
theorem erdos_387_of_refined_five_error_bounds
    (h : ∀ B K : ℕ, 3 ≤ B →
      ∀ S : CoverBPZ.BPZSection6Input B K,
        ∃ X z y medium large secondMin gap : ℕ,
          2 ≤ y ∧ 1 ≤ secondMin ∧
          B * y ^ (3 * S.k) * medium * secondMin ^ (S.k - 1) ≤ X / 2 ∧
          B * y ^ (3 * S.k) * (gap * secondMin) ^ S.k ≤ X / 2 ∧
          (CoverBPZ.RefinedLargeErrors S X z large).card +
              (CoverBPZ.RefinedMediumErrors S X z medium large).card +
              (CoverBPZ.RefinedConvenientErrors S X z y medium).card +
              (CoverBPZ.RefinedComparablePrimeErrors S X z secondMin gap
                medium).card +
              (CoverBPZ.RefinedSeparatedAlmostPrimeErrors S X z y medium
                secondMin gap).card <
            (RefinedSiftedCandidates S X z).card) :
    False ↔ ∃ c : ℝ, 0 < c ∧ ∀ n k : ℕ, 1 ≤ k → k < n →
      ∃ d : ℕ, (d : ℝ) ∈ Set.Ioc (c * n) n ∧ d ∣ n.choose k := by
  apply erdos_387_of_fixedB
  intro B hB
  let m := max 3 B
  have hm3 : 3 ≤ m := le_max_left 3 B
  have hBm : B ≤ m := le_max_right 3 B
  obtain ⟨S, -⟩ :=
    CoverBPZ.unconditional_fixed_B_cover_section6_input m m hm3
  obtain ⟨X, z, y, medium, large, secondMin, gap, hy, hsecond,
      hscaleSecond, hscaleGap, herrors⟩ := h m m hm3 S
  obtain ⟨n, _hnWindow, hn, _hnRefined, _hrough, hbad⟩ :=
    CoverBPZ.exists_refined_counterexample_of_five_error_sum_lt
      S (by omega : 0 < m) hy hsecond hscaleSecond hscaleGap herrors
  refine ⟨n, S.k, ?_, hn, ?_⟩
  · exact le_trans (by norm_num) S.hk3
  · intro d hdB hdvd
    apply hbad d ?_ hdvd
    refine ⟨?_, hdB.2⟩
    have hBpos : (0 : ℝ) < B := by
      exact_mod_cast (lt_of_lt_of_le (by norm_num) hB)
    have hmpos : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
    exact lt_of_le_of_lt
      (div_le_div_of_nonneg_left (by positivity) hBpos
        (by exact_mod_cast hBm))
      hdB.1

#print axioms erdos_387_of_counterexamples
#print axioms counterexamples_of_fixedB
#print axioms counterexamples_of_eventually_fixedB
#print axioms counterexamples_of_eventually_BNPZ
#print axioms erdos_387_of_fixedB
#print axioms erdos_387_of_eventually_fixedB
#print axioms erdos_387_of_eventually_BNPZ
#print axioms fixedBCounterexample_of_cover
#print axioms erdos_387_of_cover_certificates
#print axioms erdos_387_of_absorber_error_bounds
#print axioms erdos_387_of_frozen_roughProduct_bounds
#print axioms erdos_387_of_refined_error_bounds
#print axioms erdos_387_of_refined_five_error_bounds
#print axioms BoundedGaps.BombieriVinogradov.unconditional_weightedBombieriVinogradov
#print axioms shiftedSiegelWalfiszLower
#print axioms CoverBPZ.unconditional_fixed_B_cover_section6_input
#print axioms CoverBPZ.unconditional_fixed_B_cover
#print axioms CoverBPZ.unconditional_fixed_B_cover_section6_input_refined
#print axioms refinedSiftedCandidates_brunLowerBound
#print axioms CoverBPZ.exists_refined_counterexample_of_error_sum_lt
#print axioms CoprimeCoverDivisorTuple.exists_of_nearDivisor
#print axioms card_simultaneousClassIoc_le
#print axioms card_biUnion_modularPreimageIoc_le
#print axioms refinedNearDivisor_has_simultaneousClass
#print axioms card_refinedSimultaneousClassIoc_le
#print axioms CoverBPZ.refinedLargeErrors_card_le_certificateSum
#print axioms CoverBPZ.largeError_switching_data
#print axioms CoverBPZ.refinedLargeErrors_card_le_switchedMain_add_endpoint
#print axioms CoverBPZ.switchedCertificate_reciprocalSum_le_mass_pow
#print axioms RoughHarmonic.roughReciprocalIocMass_le_roughMass_div_log
#print axioms CoverBPZ.switchedCertificate_reciprocalSum_le_localizedEnvelope
#print axioms CoverBPZ.refinedLargeErrors_card_le_brun_localized_endpoint
#print axioms CoverBPZ.card_switchedLargeTupleCertificates_real_le_envelope
#print axioms CoverBPZ.refinedAlmostPrimeErrors_subset_comparable_union_separated
#print axioms CoverBPZ.exists_refined_counterexample_of_five_error_sum_lt
#print axioms BPZScale.almostSecond_scale
#print axioms BPZScale.almostGap_scale
#print axioms BPZScale.large_switch_square_scale
#print axioms PrimeReciprocal.primeReciprocalSum_le_log_log_two
#print axioms PrimeReciprocal.exists_logarithmicBrunDepth_parameters
#print axioms CoverBPZ.exists_refined_brunTail_le_half_logarithmicDepth
#print axioms CoverBPZ.exists_refined_tail_and_euler_reciprocal_depth
#print axioms CoverBPZ.refinedSiftedCandidates_card_lowerBound_density
#print axioms SubpowerScale.brunSupport_pow_le_half
#print axioms SubpowerScale.tendsto_localizedSwitchedReciprocalEnvelope_zero
#print axioms SubpowerScale.tendsto_switchedCertificateCountEnvelope_div_X_zero
#print axioms SubpowerScale.tendsto_refinedLargeErrors_normalized_zero
#print axioms SubpowerScale.eventually_refinedSiftedCandidates_card_ge_scale
#print axioms SubpowerScale.eventually_refinedLargeErrors_card_lt_refinedSiftedCandidates
#print axioms SubpowerScale.eventually_refinedComparablePrimeErrors_normalized_lt
#print axioms SubpowerScale.eventually_refinedComparablePrimeErrors_card_lt_scale
#print axioms SubpowerScale.comparable_constant_lt_budget_of_k
#print axioms isSquarefull_prod_of_reciprocalSum_eq
#print axioms reciprocalEnergyTuples_card_le_squarefull_divisorSum
#print axioms card_divisors_le_two_pow_of_rough_lt_pow
#print axioms roughSquarefullRange_card_le_sqrt_mul_two_pow
#print axioms reciprocalHalfEnergy_card_le_envelope
#print axioms SubpowerScale.reciprocalHalfEnergy_card_le_medium_envelope
#print axioms ReciprocalMoment.sum_halfPhase_fibre_secondMoment_le_modularEnergyFamily
#print axioms SubpowerScale.sum_halfPhase_fibre_secondMoment_le_medium_mul_base
#print axioms InversePhase.sum_norm_residueFiberSum_sq_le_short_box
#print axioms AdditiveOrthogonality.sum_norm_stdAddCharFourierSum_sq
#print axioms InversePhase.sum_norm_characterSum_sq_le_short_box_family
#print axioms BilinearMoment.subpower_bilinear_character_cauchy
#print axioms HighMoment.norm_weighted_reciprocal_sum_pow_grouped_eq
#print axioms ConvenientMoment.subpower_sum_norm_reciprocalCharacter_pow_sq_le
#print axioms Kloosterman.sum_norm_incompleteSum_sq_le
#print axioms Kloosterman.sum_norm_sq
#print axioms Kloosterman.incompleteInterval_eq_complete
#print axioms Kloosterman.norm_incompleteInterval_le_log_of_complete_bound
#print axioms Kloosterman.norm_sum_le_three_sqrt_add_one
#print axioms Kloosterman.norm_sum_zero_left_le_sqrt
#print axioms Kloosterman.sum_product
#print axioms Kloosterman.norm_sum_natCast_mul_unit_squarefree
#print axioms FiniteWeyl.norm_sum_iteratedInversePhase_sq_le
#print axioms InverseRational.iteratedInversePhase_eq_numerator_mul_inv_denominator
#print axioms InverseRational.denominator_eq_poleOffsets_prod
#print axioms InverseRational.natDegree_denominatorPolynomial
#print axioms InverseRational.natDegree_numeratorPolynomial_le
#print axioms InverseRational.singlePole_iteratedDifference_nonempty
#print axioms InverseRational.simplePolePhase_iteratedDifferenceCoefficient
#print axioms InverseRational.not_artinSchreier_crossMultiply_of_simplePole
#print axioms InverseRational.iteratedDifference_not_artinSchreier
#print axioms InverseRational.zmodIteratedInversePhase_eq_commonFraction
#print axioms InverseRational.natDegree_positiveShift_denominator_le
#print axioms InverseRational.natDegree_positiveShift_numerator_le
#print axioms InverseRational.positiveShift_not_artinSchreier
#print axioms PositiveShiftCompleteSum.norm_sum_le_conductor
#print axioms PositiveShiftCompleteSum.norm_sum_le
#print axioms CyclicWeyl.norm_sum_twistedInversePhase_sq_le
#print axioms ReciprocalIntervalCompletion.shortInversePhase_eq_complete
#print axioms ReciprocalIntervalCompletion.norm_shortInversePhase_le
#print axioms IteratedReciprocalCompletion.norm_sum_twistedSequence_sq_le
#print axioms IteratedReciprocalCompletion.norm_shortPhase_le
#print axioms IteratedWeylBound.norm_sum_iteratedInversePhase_le
#print axioms IteratedWeylBound.norm_sum_inversePhase_le
#print axioms ProgressionFourier.card_residueClass_eq_phase_sum
#print axioms ProgressionFourier.int_card_residueClass_eq_phase_sum
#print axioms ProgressionFourier.sum_norm_intCoefficient_Ioc_le
#print axioms BezoutAdditiveCharacter.stdAddChar_product
#print axioms BezoutAdditiveCharacter.stdAddChar_product_crt
#print axioms SimultaneousFourier.simultaneousClassIoc_eq_residueClass
#print axioms SimultaneousFourier.card_simultaneousClassIoc_eq_phase_sum
#print axioms SimultaneousFourier.chineseRemainder_simultaneousResidue
#print axioms SimultaneousFourier.stdAddChar_neg_mul_simultaneousResidue
#print axioms SimultaneousFourier.stdAddChar_mul_simultaneousResidue_reciprocity
#print axioms SimultaneousFourier.card_simultaneousClassIoc_eq_split_phase_sum
#print axioms TupleCertificate.factor_coprime_otherValue
#print axioms TupleCertificate.otherResidue_mod_factor
#print axioms TupleCertificate.crtResidue_eq_simultaneousResidue_other
#print axioms TupleCertificate.stdAddChar_neg_mul_crtResidue_coordinate_split
#print axioms TupleCertificate.stdAddChar_mul_crtResidue_reciprocity
#print axioms TupleCertificate.gcd_otherResidue_sub_index_otherValue_eq_one
#print axioms CoverBPZ.refinedMediumErrors_subset_certificateClasses
#print axioms CoverBPZ.mediumError_coordinate_data
#print axioms RationalWeil.polynomialWeight_mul
#print axioms RationalWeil.eval_derivative_derivativeProbe_at_selected_ne_zero
#print axioms RationalWeil.sum_polynomialWeight_add_probe_eq_zero
#print axioms RationalWeil.sum_polynomialWeight_monicPolynomial_eq_zero
#print axioms RationalWeil.natDegree_artinLPolynomial_lt
#print axioms RationalWeil.coeff_localEulerProduct_polynomialWeight_eq_monicWeightSum
#print axioms RationalWeil.irreducible_sum_eq_neg_artinRootPowerSum
#print axioms RationalWeil.extensionPointWeight_eq_zeroExtendedTraceWeight
#print axioms RationalWeil.sum_finiteExtension_eq_irreducibleSum
#print axioms RationalWeil.extensionTraceSum_eq_neg_artinRootPowerSum
#print axioms RationalWeil.norm_reverse_artinLPolynomial_root_le_sqrt_of_evenExtensionBound
#print axioms RationalWeil.finiteExtensionTraceSum_eq_neg_artinRootPowerSum
#print axioms RationalWeil.baseTraceSum_eq_neg_artinRootSum
#print axioms RationalWeil.zeroExtendedTraceWeight_self
#print axioms RationalWeil.norm_zeroExtendedSimplePolePhase_sum_le_of_evenExtensionBound
#print axioms RationalStepanov.mappedSimplePolePhase_eq_numerator_mul_inv_denominator
#print axioms RationalStepanov.frobenius_pow_ne_mappedPole
#print axioms RationalStepanov.eval_fullRationalTrace_eq_algebraMap_trace
#print axioms RationalStepanov.natDegree_fullMappedSimplePoleNumerator_le
#print axioms RationalStepanov.natDegree_fullMappedSimplePoleDenominator_le
#print axioms RationalStepanov.rationalAuxiliaryPolynomial_ne_zero
#print axioms RationalStepanov.card_nonpole_trace_fiber_le
#print axioms RationalStepanov.hasEvenExtensionSquareRootBound
#print axioms RationalStepanov.norm_zeroExtendedSimplePolePhase_sum_le
#print axioms RationalStepanov.norm_simplePolePhase_sum_le
#print axioms RoughHarmonic.log_mul_preSieveSingularSeries_le_one
#print axioms RoughHarmonic.roughReciprocalMass_eq_coprimeHarmonicSum
#print axioms RoughHarmonic.exists_uniform_roughReciprocalMass_le_log_ratio
#print axioms CoverBPZ.exists_uniform_refinedLargeErrors_card_le_logRatioEnvelope
#print axioms CoverBPZ.switchedClassBoundingSieve_abs_rem_le
#print axioms CoverBPZ.refinedLargeErrors_card_le_brun_roughMass_endpoint
#print axioms CoverBPZ.exists_absorberCoverValid_above
#print axioms CoverBPZ.AbsorberCoverValid.choose_eq_prod_residual
#print axioms CoverBPZ.AbsorberCoverValid.affineRescale
#print axioms CoverBPZ.AbsorberCoverValid.factorization_residual_affine_frozen
#print axioms CoverBPZ.AbsorberCoverValid.smallPrimePart_frozen_residual
#print axioms largePrimePart_isZRough_of_coprime_sievePrimeProduct
#print axioms frozen_residual_eq_fixedSmallPart_mul_rough
#print axioms exists_frozen_residualDivisor_split
#print axioms exists_roughProduct_of_near_frozen_residualDivisor
#print axioms exists_frozenAbsorberCounterexample_of_roughProduct_card_lt
#print axioms CoverBPZ.AbsorberCoverValid.residual_coprime
#print axioms CoverBPZ.AbsorberCoverValid.residual_le_div
#print axioms CoverBPZ.AbsorberCoverValid.toCoverFactorization
#print axioms CoverBPZ.AbsorberCoverValid.coverQuotient_eq_residual
#print axioms CoverBPZ.AbsorberCoverValid.dvd_choose_iff_mod_mem_parameterResidues
#print axioms abs_card_divisibleAbsorberParameterCandidates_sub_density
#print axioms absorberBoundingSieve_abs_rem_le
#print axioms absorberBoundingSieve_brunErrSum_le
#print axioms exists_siftedAbsorberParameter_above
#print axioms exists_absorberCounterexample_of_bad_card_lt
#print axioms absorberNearDivisor_has_residualTuple
#print axioms badSiftedAbsorber_card_le_error_sum
#print axioms exists_absorberCounterexample_of_error_sum_lt
#print axioms siftedAbsorberParameters_brunLowerBound
#print axioms siftedAbsorberParameters_brunUpperBound
#print axioms two_mul_brunSubsetTail_le_of_moment
#print axioms siftedAbsorberParameters_card_lowerBound
#print axioms siftedAbsorberParameters_card_lowerBound_of_moment
#print axioms siftedAbsorberParameters_card_pos_of_brun
#print axioms prod_one_add_nat_div_le_pow
#print axioms prod_binomialMomentMajorant_le
#print axioms absorber_brunTail_le_half_elementaryDepth
#print axioms one_le_elementaryMajorant_mul_absorberEulerProduct
#print axioms exists_siftedAbsorberParameter_above_of_brunTail
#print axioms exists_siftedAbsorberParameter_above_elementaryDepth
#print axioms exists_siftedAbsorberParameter_in_elementaryScale
#print axioms PNT_fixed_modulus
#print axioms eventually_fixed_shifted_dyadic_lower
#print axioms eventually_finite_fixed_shifted_dyadic_lower
#print axioms bounded_shifted_dyadic_lower
#print axioms cover_lemma
#print axioms CoverBPZ.wcbd_zSet_aux_for_total
#print axioms CoverBPZ.fixed_B_cover
#print axioms CoverBPZ.BPZSection6Input.coverQuotients_pairwise_coprime
#print axioms CoverBPZ.BPZSection6Input.coverQuotient_le_div
#print axioms divisorFactors_unique_of_pairwise_coprime
#print axioms CoverDivisorTuple.exists_value_eq
#print axioms CoverDivisorTuple.value_injective
#print axioms exists_almostPrime_decomposition
#print axioms exists_counterexample_of_bad_card_lt
#print axioms nearDivisor_has_residualTuple
#print axioms CoverDivisorTuple.errorClass_exhaustion
#print axioms CoverBPZ.exists_counterexample_of_error_sum_lt
#print axioms prime_dvd_choose_iff_mod_mem_localBadResidues
#print axioms card_localBadResidues
#print axioms card_localAssignmentResidues
#print axioms squarefree_dvd_choose_iff_exists_localAssignment
#print axioms squarefree_dvd_choose_iff_mod_mem_localAssignmentResidues
#print axioms card_modularPreimage
#print axioms card_localAssignment_modularPreimage
#print axioms abs_card_modularPreimageIoc_sub_density
#print axioms BoundingSieve.totalMass_mainSum_sub_errSum_le_siftedSum
#print axioms truncated_moebius_divisorSum_eq_brunTruncation
#print axioms brunLowerWeight_isLowerOnProdPrimes
#print axioms brunLowerBound
#print axioms brunUpperWeight_isUpperOnProdPrimes
#print axioms brunUpperBound
#print axioms boundingSieve_brunMainSums_half_threeHalves
#print axioms CoverBPZ.BPZSection6Input.no_prime_le_k_dvd_choose
#print axioms binomialSieveNu_squarefree
#print axioms coprime_sievePrimeProduct_iff_rough
#print axioms binomialBoundingSieve_siftedSum
#print axioms binomialBoundingSieve_multSum
#print axioms abs_card_divisibleBaseCandidates_sub_density
#print axioms binomialBoundingSieve_abs_rem_le
#print axioms siftedCandidates_brunLowerBound
#print axioms siftedCandidates_brunUpperBound

end Erdos387
