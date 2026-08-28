import Wikipedia.HopfProblem.CuspCentralCohomologyMonodromyGeometryFrozen
import Wikipedia.HopfProblem.CuspCentralCohomologyMonodromyGeometryTransport

/-!
# Actual circle transport and its marked endpoint

This package constructs jointly continuous transport around the actual
nonzero base circle for frozen and varying cusp data.  Each intermediate
slice is a homeomorphism onto the original quotient fibre.  The positive
full-turn endpoint is the actual `M₀` map in the same four-period marking
used for specialization.  Thus it also represents inverse transport
around a clockwise circle, the source's monodromy convention.

No global choice of argument or replacement quotient topology is used.
-/
