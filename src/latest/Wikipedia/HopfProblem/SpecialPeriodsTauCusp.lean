import Wikipedia.HopfProblem.SpecialPeriodsTauCuspExpansion
import Wikipedia.HopfProblem.SpecialPeriodsTauCuspMeromorphic
import Wikipedia.HopfProblem.SpecialPeriodsTauCuspContinuation
import Wikipedia.HopfProblem.SpecialPeriodsTauCuspGlobal
import Wikipedia.HopfProblem.SpecialPeriodsTauCuspCovariance

/-!
# Actual cusp expansions for the special modular period

The modules collected here derive the logarithmic cusp expansion from the
actual inverse cusp chart of the modular j-function and an actual
meromorphic simple pole. The analytic unit and its logarithm are proved
to exist, including their prescribed leading coefficients.

They also identify supplied high-cusp lifts up to a single integer, and
propagate a prescribed germ of a native global holomorphic lift throughout
the source cusp half-plane. Arbitrary positive source widths retain the
exact clockwise translation law.

For a supplied global holomorphic source function with the required finite
elliptic orders and an actual meromorphic simple pole at the cusp, these
results construct a native global modular lift with the normalized cusp
formula. Neither an initial lift germ nor a target-height hypothesis is
assumed. Constructing the particular global source function remains a
separate input to this general lifting theorem.

The derived cusp formula also implies the literal parabolic covariance
on the entire upper half-plane, by the analytic identity theorem.
-/
