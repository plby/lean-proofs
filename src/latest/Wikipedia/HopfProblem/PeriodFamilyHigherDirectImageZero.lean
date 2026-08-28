import Wikipedia.HopfProblem.PeriodFamilyHigherDirectImageZeroDerived
import Wikipedia.HopfProblem.PeriodFamilyHigherDirectImageZeroLinear

/-!
# The unconditional native degree-zero direct image of a varying period family

For every original holomorphic period family over a complex manifold,
actual pullback identifies the holomorphic algebras on every base open
with those on its full preimage. Its literal inverse is evaluation along
the original holomorphic zero section; compact native period tori prove
the other inverse identity. Both maps preserve all actual restrictions,
complex scalars, and the genuine action of base holomorphic functions.

The resulting ring-sheaf isomorphism gives the actual additive
`O_B ≅ R⁰f_*O_Total` through Mathlib's native derived-zero comparison.
The original varying-period quotient atlas is used throughout. No
finite-dimensionality or compactness of the base model is assumed, and
no assertion about positive-degree higher direct images is made here.
-/
