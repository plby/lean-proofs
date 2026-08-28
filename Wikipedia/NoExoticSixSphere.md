# No exotic smooth six-sphere

`src/latest/Wikipedia/NoExoticSixSphere.lean` proves that any smooth manifold
homeomorphic to the standard six-sphere is diffeomorphic to it. The manifold's
original smooth atlas is independently supplied, not transported from the
homeomorphism. The public theorem is `NoExoticSixSphere.no_exotic_six_sphere`.

`SmoothModelRigidity.lean` extends the coordinate model from real Euclidean
six-space to any finite-dimensional real normed vector space of dimension six.
This is used by `SmoothSixDPoincare` and the smooth Hopf-problem conclusion.

The support modules share results with `HopfProblem` in both directions;
the individual-module import graph is acyclic. Comparator coverage is in
`src/latest/ComparatorChallenges/Wikipedia/NoExoticSixSphere.{lean,json}`.
The former plural-name source is preserved on local branch
`codex/six-sphere-archive`.
