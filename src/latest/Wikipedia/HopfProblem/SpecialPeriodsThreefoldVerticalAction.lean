import Wikipedia.HopfProblem.SpecialPeriodsThreefoldVerticalActionMultiplicative
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldVerticalActionGenerator

/-!
# The actual vertical action and native generator from Proposition 9.23

The original regular period translations, toric cusp cocharacter, and
logarithmic elliptic translations glue to the actual compact threefold.
The joint holomorphic flow has exactly the integer kernel; the genuine
normalized exponential quotient therefore gives an effective fibrewise
holomorphic action of `ℂˣ`.  Its native holomorphic tangent-section
generator is nonzero and has exactly the original `e₂` normalization on
the regular period-vector covering.

These are the construction and effectiveness assertions of Proposition
9.23.  This package does not assert that every global vector field is a
multiple of the generator, or identify the connected automorphism group.
-/
