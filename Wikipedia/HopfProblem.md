# The Hopf problem

The development in `src/latest/Wikipedia/HopfProblem.lean` constructs a complex
analytic atlas on the topological six-sphere (`Wikipedia.HopfProblem.hopf_problem`)
and proves compatibility with its original stereographic smooth structure
(`Wikipedia.HopfProblem.hopf_problem_smooth`). The latter theorem states that
the identity is real-smooth in both directions between the two atlases.

The constructed complex threefold is proved homotopy equivalent to the sphere.
`SmoothSixDPoincare` supplies a diffeomorphism for its original real atlas,
using the classification in `NoExoticSixSphere`. Both main conclusions are
unconditional; the older conditional recognition interface remains a helper.

`SpecialPeriods.Threefold.ProjectionHomotopy.projection_nullhomotopic` now proves
that the original projection is null-homotopic, without recognition or exponent
hypotheses. Its exponent input comes from the proved `π₆(S³) ≅ ℤ/12ℤ` calculation.

`SixSphereProjection.lean` transports this same projection through the proved
smooth identification. `SixSphereProjection.projection_holomorphic` gives
complex analyticity into the standard Riemann sphere; the corresponding
`sphere_projection_holomorphic`, `sphere_projection_surjective`, and
`sphere_projection_nullhomotopic` results use literal Euclidean `S⁶` and `S²`.
The source complex atlas retains the standard six-sphere's original smooth
structure, as proved by `SixSphereProjection.original_smooth_structure_agrees`.
The Comparator statement `SixSphereProjection.holomorphic_nullhomotopic_surjection`
asserts these properties jointly for one map, with a complex three-dimensional
source atlas compatible with the standard smooth structure. Its proof uses the
constructed projection, while the challenge is independent of that construction.

The former MathOverflow/MO1973 copy is consolidated here. Comparator coverage
is in `src/latest/ComparatorChallenges/Wikipedia/HopfProblem.{lean,json}`.
The superseded source snapshot is preserved on local branch
`codex/six-sphere-archive`.
