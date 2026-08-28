import Wikipedia.HopfProblem.HolomorphicDolbeaultThreeLocalNative

/-!
# Native degree-one local Dolbeault primitives in complex dimension three

`HolomorphicDolbeaultThree.Local.exists_native_primitive_germ` applies to
actual smooth anti-complex-linear covector fields on the original model
`ℂ × ComplexPlane₂`.  It assumes precisely their actual closedness
equations and constructs a globally smooth function with the prescribed
full antiholomorphic differential near the chosen point.

The proof uses genuine coordinate Cauchy–Green integrals, smooth compact
cutoffs, and the real symmetry of second derivatives.  Intermediate
coordinate changes are explicit complex continuous linear equivalences;
no topology or manifold atlas is replaced.
-/
