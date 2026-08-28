import Wikipedia.HopfProblem.HolomorphicFunctionSheafSphereNegativeOneCohomologyBiproduct

/-!
# Genuine cohomology of the infinity ideal and its split sum with `O`

For the original holomorphic infinity-ideal sheaf on the actual Riemann
sphere, every Ext-defined sheaf-cohomology group vanishes.  Higher
degrees use the genuine short exact sequence
`0 → O(-∞) → O → C_∞ → 0`, together with the proved analytic vanishing
for `O` and the actual scalar skyscraper's injectivity.

For the actual categorical direct sum `O ⊞ O(-∞)`, the native cohomology
map of the first projection is a complex-linear equivalence in every
degree, with inverse induced by the first summand inclusion.  Degree
zero is canonically `ℂ`, by evaluation at infinity on the first summand;
its inverse is the class of the literal constant section in that
summand.  All positive-degree cohomology vanishes.

Every scalar module here is induced by the original pointwise sheaf
endomorphisms and the native cohomology functor.  These are computations
of the displayed base sheaves; this package makes no identification
with higher direct images of the constructed threefold.
-/
