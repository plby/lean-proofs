import Wikipedia.HopfProblem.CuspNormalizationSheafCohomologyFinitePushforwardCusp

/-!
# Genuine cohomology invariance under finite closed pushforward

For a closed continuous map with finite fibres and Hausdorff source,
`SheafCohomologyFinitePushforward.pushforward_exact` and
`pushforward_shortExact` prove exactness of the actual sheaf pushforward.
The canonical `cohomologyEquiv` identifies Mathlib's genuine sheaf
cohomology of the pushforward with that of the source sheaf in every
degree. It commutes with actual `Sheaf.H.map` and agrees in degree zero
with the literal global-section identification.

The proof uses the constructed finite-fibre stalk equivalence, the
actual pullback adjunction, injective presentations, and the genuine
Ext long exact sequence. It assumes no higher-direct-image vanishing.

Concrete corollaries apply to the constructed cusp normalization and
the three actual source-ordered double curves, including compatibility
of their actual constant-to-holomorphic comparison maps.
-/
