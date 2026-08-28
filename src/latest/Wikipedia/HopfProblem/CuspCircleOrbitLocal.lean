import Wikipedia.HopfProblem.CuspCircleOrbitLocalQuotient
import Wikipedia.HopfProblem.CuspCircleOrbitLocalSpace

/-!
# The actual local circle-orbit model at the cusp

This package proves the opposite-weight Hopf quotient `ℂ²/S¹ ≃ₜ ℂ × ℝ`
and its exact restriction to the original cusp coordinate domain. The
orbit relation is the original norm-one-unit action, equivalently the
unchanged period-one `DeltaSweep.circleParameter`. The native coordinate
cover intertwines this action with the original global action.

The native domain quotient is homeomorphic to the open invariant domain
`‖aβ/2‖ < radius`, with invariant coordinates
`(a, β, s) = (z₁, 2z₀z₂, ‖z₀‖² - ‖z₂‖²)`. The original chart transition,
time function, and fixed-axis image are retained. Every statement here
is unconditional and uses the ordinary quotient topology.

The additional cusp deck quotient, global orbit-space attachments, an
invariant tubular neighborhood, and any identification with a sphere
are not asserted by this local package.
-/
