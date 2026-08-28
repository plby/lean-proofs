import Wikipedia.HopfProblem.HolomorphicPicardNativeRecovery

/-!
# Original native holomorphic line bundles and actual unit-sheaf cocycles

`nativeCocycle` extracts a genuine Čech one-cocycle on the original native
trivializing cover. `cocycleTransitionData` glues any genuine unit-sheaf
cocycle on a covering family of opens into an actual native holomorphic
line bundle. `nativeCocycleBundleIso` proves that gluing the extracted
cocycle recovers the original native bundle by an actual analytic bundle
isomorphism, respecting every original chart.
-/
