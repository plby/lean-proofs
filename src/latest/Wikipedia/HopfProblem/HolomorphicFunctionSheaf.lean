import Wikipedia.HopfProblem.HolomorphicFunctionSheafGlobal
import Wikipedia.HopfProblem.HolomorphicFunctionSheafLocalRing
import Wikipedia.HopfProblem.HolomorphicFunctionSheafStalkEval
import Wikipedia.HopfProblem.HolomorphicFunctionSheafStalkChart
import Wikipedia.HopfProblem.HolomorphicFunctionSheafCohomologyZero

/-!
# Holomorphic function sheaves, genuine stalks, and degree-zero cohomology

The sheaf assigns actual bundled `ContMDiff ω` complex-valued functions
to each open set, with literal restrictions and pointwise operations.
Its global sections are complex-algebra equivalent to the actual bundled
holomorphic maps on the original manifold.

The categorical stalks are local rings, defined through the actual
open-neighbourhood colimits. On normed models they are identified with
actual analytic neighbourhood germs. For a boundaryless complex manifold
the same identification is made through its actual extended charts.

`H0` is mathlib's genuine `Ext`-defined sheaf cohomology in degree zero.
The degree-zero comparison with global sections is complex linear, and
its scalar action is proved to agree with the cohomology maps induced by
actual pointwise scalar sheaf endomorphisms. No higher cohomology is
computed here.
-/
