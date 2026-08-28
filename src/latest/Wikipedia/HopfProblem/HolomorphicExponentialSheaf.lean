import Wikipedia.HopfProblem.HolomorphicExponentialSheafULiftSequence

/-!
# The actual holomorphic exponential sequence

On the original complex charts, `exponentialComplex_shortExact` proves
`0 → ℤ → O → O* → 0` in Mathlib's category of abelian sheaves. The source
is the genuine sheafification of the constant additive integer presheaf,
the middle object is the existing holomorphic function sheaf, and the
target consists of the actual units of its holomorphic section rings.

The maps use `n ↦ (n : ℂ) * (2 * π * I)` and the ordinary complex
exponential. Local logarithms and local integer kernel representatives
are constructed; neither local solvability nor exactness is an assumption.

The canonical comparison also gives a short exact sequence whose source
is the literal constant `ULift ℤ` sheaf used by Mathlib's sheaf cohomology.

This supporting result does not identify line bundles with first sheaf
cohomology and does not assert any value of the cohomology groups.
-/
