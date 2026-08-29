# Homotopy groups of spheres

`src/latest/Wikipedia/HomotopyGroupsOfSpheres.lean` exports nine unconditional
calculations of Mathlib's native homotopy groups of Euclidean unit spheres,
at arbitrary base points:

- `π₁(S¹) ≅ ℤ`, `π₂(S¹) ≅ 0`;
- `π₁(S²) ≅ 0`, `π₂(S²) ≅ ℤ`, `π₃(S²) ≅ ℤ`, `π₆(S²) ≅ ℤ/12ℤ`;
- `π₃(S³) ≅ ℤ`, `π₆(S³) ≅ ℤ/12ℤ`;
- `π₇(S⁷) ≅ ℤ`.

The isomorphisms are in namespace `Wikipedia.HomotopyGroupsOfSpheres`.
`HomotopyGroupsOfSpheres/AxiomAudit.lean` audits their proof dependencies.
Proposition-valued wrappers in `HomotopyGroupsOfSpheres/Statements.lean`
provide independent Comparator coverage for all nine calculations through
`src/latest/ComparatorChallenges/Wikipedia/HomotopyGroupsOfSpheres.{lean,json}`.

The sixth-group calculation for `S²` uses the existing higher Hopf-fibration
comparison with `S³`, under `NoExoticSixSphere/HigherHopfNativeEquivalence.lean`.

The sixth-group calculation for `S³` also discharges the exponent hypothesis in
`HopfProblem/QuaternionSphereExponent.lean`, yielding an unconditional
null-homotopy of the constructed threefold projection and its transported
map from the standard six-sphere.
