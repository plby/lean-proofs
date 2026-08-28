import Wikipedia.HopfProblem.HolomorphicFunctionSheafCohomologyZeroScalars

/-!
# Degree-zero cohomology of the genuine holomorphic function sheaf

`HolomorphicFunctionSheaf.H0` is mathlib's actual degree-zero sheaf
cohomology of the underlying additive holomorphic-function sheaf.
`h0GlobalLinearEquiv` identifies it with literal global sections, and
`h0HolomorphicMapLinearEquiv` with actual bundled holomorphic functions.

The complex scalar action agrees with the maps induced on cohomology by
the actual scalar sheaf endomorphisms, as proved in
`h0_map_scalarSheafEnd`. No higher-cohomology assertion is made here.
-/
