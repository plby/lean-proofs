import Wikipedia.HopfProblem.HolomorphicPicardCechExtensionClassNaturality
import Wikipedia.HopfProblem.HolomorphicPicardCechExtensionClassZero
import Wikipedia.HopfProblem.HolomorphicPicardCechExtensionEvaluationLocal
import Wikipedia.HopfProblem.HolomorphicPicardCechExtensionComparison
import Wikipedia.HopfProblem.HolomorphicPicardCechExtensionRepresentation

/-!
# Actual sheaf extensions and derived classes of Čech one-cocycles

For any additive sheaf on the actual small open-set site, a cocycle on
an actual open cover gives a genuine short exact sequence with original
kernel sheaf and the native constant `ULift ℤ` quotient used by `Sheaf.H`.
The middle sheaf is constructed by sheafifying compatible integer and
local-section data. Kernel exactness, local degree lifts, and evaluations
are proved from the actual sheaf condition and cocycle equations.

The resulting class belongs to the genuine derived-category `H¹` group.
It is natural for sheaf morphisms, vanishes exactly for actual local
coboundaries, and every native `H¹` class has such a representative.
The comparison with any genuine extension and compatible local lifts is
an actual isomorphism preserving both endpoints.

The convention is `b i - b j = n • c i j`; hence the constructed degree-one
local sections satisfy `t j - t i = inclusion (c i j)`. The native Ext
representation uses the explicitly sign-corrected cocycle with this same
equation. No representability, sheafification, local-constancy, lifting,
exactness, or cohomology-comparison premise is imposed on the final results.
-/
