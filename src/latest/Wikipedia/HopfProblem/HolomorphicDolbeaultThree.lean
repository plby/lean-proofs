import Wikipedia.HopfProblem.HolomorphicDolbeaultThreeCauchy
import Wikipedia.HopfProblem.HolomorphicDolbeaultThreeLocal
import Wikipedia.HopfProblem.HolomorphicDolbeaultThreePeriodFamilyOpen

/-!
# Original native degree-one Dolbeault comparison in complex dimension three

The native short exact sequence `0 → O → A⁰ → Z¹ → 0` is proved from
the actual holomorphic kernel and genuine local Cauchy--Green primitives
in the unchanged complex model `ℂ × ComplexPlane₂`.  The forms are
actual smooth anti-linear real cotangent sections satisfying their
actual closedness PDE in every original chart.

Actual smooth partitions of unity give `H¹(A⁰)=0`.  The positive native
Ext connecting map therefore identifies closed global forms modulo
actual globally exact forms with the original `Sheaf.H¹(O)`, complex
linearly for the original sheaf-induced actions.  All hypotheses are
discharged for the original period-family total space and every actual
inherited open subset, including every full inverse image of a base open.

This package makes no claim about the values or splitting of any higher
direct-image sheaf and does not replace a native complex atlas by a
real-product atlas.
-/
