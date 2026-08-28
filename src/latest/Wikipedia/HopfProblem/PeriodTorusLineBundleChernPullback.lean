import Wikipedia.HopfProblem.PeriodTorusLineBundleChernPullbackBundle
import Wikipedia.HopfProblem.PeriodTorusLineBundleChernPullbackClass

/-!
# Compatible-linear pullback of actual period-torus line bundles

Every complex continuous linear map carrying the source period lattice
into the target lattice induces an actual analytic torus map and a genuine
pulled-back holomorphic factor.  Its native line bundle is analytically,
fibrewise complex-linearly isomorphic to Mathlib's actual pullback bundle.
The representative formula is exactly `[z,c] ↦ [Lz,c]`.

Normalized logarithms and their integer defects pull back exactly.  The
actual positive period loops and their homology products prove naturality
of the genuine first Chern class in native integral singular cohomology.
-/
