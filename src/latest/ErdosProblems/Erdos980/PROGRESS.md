# Erdős 980 progress log

## Current phase

Complete.  The mathematical reconstruction is in `tex/980.tex`, and the
public theorem and its quadratic specialization are proved in
`ErdosProblems/Erdos980.lean`.

## Verified facts

- `Basic.lean`: exact total convention for the least kth-power nonresidue,
  existence on eligible primes, minimality, positivity, prime-valuedness, and
  the pointwise modulus bound.
- `KummerPatterns.lean`: canonical Kummer splitting fields, degrees, pattern
  weights, finite-field kth-power criteria, and number-field/Galois instances.
- `Assembly.lean` and `Model.lean`: fixed-pattern plus uniform-tail limit
  assembly for the exact strict prime sum.
- `NaturalChebotarev/DedekindZeroFree/Basic.lean`: the Dedekind zeta
  continuation is nonzero on `Re(s)=1` away from its pole.
- The ideal-Mangoldt logarithmic-derivative identity, Tauberian interfaces,
  boundary pole subtraction, and Wiener--Ikehara assembly have been checked;
  the unconditional weighted prime-ideal theorem is now complete.
- The weighted-to-counting interfaces and split-prime transfer modules have
  each been checked under the default Lean limits.
- The unconditional prime-ideal theorem and completely-split rational-prime
  asymptotic now build together.  `KummerPatterns.lean` consequently exports
  the unconditional ratio limit for every fixed exact Kummer split pattern,
  including the zero-density case when two adjacent fields coincide.
- The character encoding, Pólya--Vinogradov pointwise bound, character large
  sieve, finite smooth-amplifier bounds, and the current Elliott-tail aggregate
  have each been checked.
- The explicit smooth-amplifier parameters and resulting large-tail limit are
  unconditional and checked.  `ModelBridge.lean` identifies that tail exactly
  with the tail of the least-nonresidue model.
- The exact exponent-reduction theorem has been checked: uniform-tail control
  for a prime divisor of `k` transfers to exponent `k`.
- `GoodPrimeBridge.lean` now gives the unconditional strict-cutoff density of
  every exact least-nonresidue pattern and the positive natural density of
  eligible primes; its audited headline theorems use only the standard
  foundational axioms.
- `FinalAssembly.lean` now combines all completed algebraic, density, and
  positivity inputs with the single family of prime-exponent medium estimates.
  This conditional integration theorem type-checks under the default limits.
- `KummerPatterns.lean` now proves the unconditional multiquadratic degree
  formula `kummerDegree 2 r = 2 ^ r` and consequently the exact identity
  `elliottConstant 2 = ∑' j, rationalPrime j / 2 ^ (j + 1)`.  The audited
  declarations use only the standard foundational axioms.
- `PrimeIdealMertens.lean` proves the required reciprocal Euler-product
  upper bound over prime ideals, with the exact `1 / log z` saving needed by
  the Brun--Rosser specialization; its headline declarations have only the
  standard foundational axioms.
- `RayPrincipalization.lean` and `RayPrincipalizationHeight.lean` construct
  finitely many correction ideals, primary generators with the distinguished
  prime ideal occurring to exponent one, and a uniform archimedean height
  bound.  `OddPowerReciprocity.lean` and `OddPrimeTensorBridge.lean` turn
  literal local power conditions into exact correction-indexed ray-symbol
  fibres without importing the unproved one-sided reciprocity file.
- `IdealGeneratorCongruenceCount.lean`, `NumberFieldLargerSieve.lean`,
  `RayNormPrimeSieve.lean`, and `RayNormRemainder.lean` now provide the fixed
  ideal-lattice count, exact `ell ^ (-j)` tensor fraction, ray/norm CRT, and
  conductor-norm Rosser-sieve remainder interfaces.  These modules all pass
  direct Lean checks without forbidden placeholders.
- `CumulativeMediumTail.lean` and `CumulativeMediumApplication.lean` give the
  exact layer-cake reduction from cumulative exceptional-prime bounds to the
  `PrimeExponentMediumEstimate` interface used by `FinalAssembly.lean`.
- `QuadraticMediumSieve.lean` now proves the unconditional endpoint
  `quadraticPrimeExponentMediumEstimate : PrimeExponentMediumEstimate 2`.
  Its direct check and Lake target build pass under the default limits, and
  its axiom report is exactly `propext`, `Classical.choice`, and `Quot.sound`.
- `LocalNormEuler.lean` and `LocalNormRootBound.lean` now give the concrete
  fixed-ideal coordinate quotient, identify norm-form zeroes with nonunits,
  and prove the unconditional local estimate
  `D * p ^ (D - 1)` (and its squarefree multiplicative consequence).  Both
  files pass direct Lean checks.
- `OddInertAuxiliaryPrimes.lean` constructs the inert auxiliary-prime family,
  its cyclotomic quotient and power-class data, and the eventual cardinality
  bound needed to select the moving tensor depth.  The strengthened selected
  subfamily and all dependent tensor-cell modules pass direct and target
  checks.
- `OddPrimeMediumApplication.lean` proves the unconditional endpoint
  `oddPrimeExponentMediumEstimate` for every odd prime exponent.  The direct
  check and target build pass, and its axiom report contains exactly
  `propext`, `Classical.choice`, and `Quot.sound`.
- `UnconditionalTail.lean` combines the quadratic and odd-prime endpoints and
  proves uniform tail negligibility for every `k ≥ 2`.
- `ErdosProblems/Erdos980.lean` proves the exact strict-cutoff statement of
  Problem 980 and the dyadic quadratic-constant identity.  Both the direct
  check and `lake build ErdosProblems.Erdos980` pass under the default limits;
  both public declarations have only the standard foundational axioms.

## Current failures or open leaves

None.

## Final validation

The production file and aggregate compile under Lean 4.33 with default
limits, the required Lake target builds, the forbidden-declaration scan is
empty, and the final axiom reports are exactly `[propext, Classical.choice,
Quot.sound]`.
