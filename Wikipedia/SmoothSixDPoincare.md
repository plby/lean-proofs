# The smooth six-dimensional Poincaré theorem

`src/latest/Wikipedia/SmoothSixDPoincare.lean` preserves the general recognition
results formerly associated with Smale's Theorem A. Every closed smooth
six-manifold homotopy equivalent to the standard sphere is homeomorphic to it;
combining this with `NoExoticSixSphere` upgrades the conclusion to a
diffeomorphism for the original smooth atlas.

The main theorems, in namespace `Wikipedia.SmoothSixDPoincare`, are
`homeomorphic_sixSphere_of_homotopySixSphere` and
`diffeomorphic_sixSphere_of_homotopySixSphere`. Supporting modules also retain
the general two-critical-point, disk-gluing, punctured-recognition, smooth
coordinate-disk, and localized Morse-perturbation results.

Comparator coverage is in
`src/latest/ComparatorChallenges/Wikipedia/SmoothSixDPoincare.{lean,json}`.
Both former `SmoothSixDSmalTheoremA` spellings and the separate MO1973 source
are preserved on local branch `codex/six-sphere-archive`.
