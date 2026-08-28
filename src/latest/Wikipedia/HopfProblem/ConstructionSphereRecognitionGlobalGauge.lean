import Wikipedia.HopfProblem.ConstructionSphereRecognitionGlobalGaugeAttaching
import Wikipedia.HopfProblem.ConstructionSphereRecognitionGlobalGaugeNormal

/-!
# Supported elliptic gauge isotopies of the original global threefold

`GlobalGauge.globalDiffeomorph` extends the actual supported elliptic cap
map by the identity.  A proved closed support inside the original open
cap makes this literal extension jointly real smooth in the unchanged
global atlas.  Its inverse is the same map at negative time, its original
base projection is fixed, and it commutes with the full original complex
vertical flow.

The two cap patches are genuinely disjoint.  Thus
`GlobalGauge.combinedDiffeomorph` and `GlobalGauge.combinedIsotopy` perform
both corrections simultaneously.  The exact original boundary maps at
time one are the included native linear-gauge regular-family maps.  The
whole cusp piece, the actual fixed-curve normal neighborhood, the literal
standard closed disk, and the original normal collar are fixed pointwise.

These are actual global reparametrizations with exact boundary formulas.
They do not assert equality on a larger overlap, a global coinvariant
coordinate, a replacement Jacobian product, a complement identification,
or recognition of the original manifold as a standard sphere.
-/
