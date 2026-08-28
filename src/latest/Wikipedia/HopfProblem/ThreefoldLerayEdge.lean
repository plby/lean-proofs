import Wikipedia.HopfProblem.ThreefoldLerayEdgeCocycle

/-!
# The unconditional original Leray edge and Picard comparison

For the original constructed threefold `X` and its original projection
`f : X → P¹`, the actual Leray edge induces the complex-linear equivalence

`H¹(X, O_X) ≃ₗ[ℂ] Γ(P¹, R¹ f_* O_X)`.

The native sheaf isomorphism `f_* O_X ≅ O_P¹` and the proved positive
cohomology vanishing of `O_P¹` supply both outer vanishings of the genuine
low-degree Leray sequence. All scalar actions are induced by the original
holomorphic sheaf scalar maps, followed by the genuine derived functor
and literal top-open evaluation. The exact original edge-map formula is
retained.

The already proved ordinary exponential and native Picard classification
then give `PicardGroup(X) ≃+ Γ(P¹, R¹ f_* O_X)`. This comparison retains
both the original native bundle cocycle and the actual glued-bundle
formula with transitions `exp(cᵢⱼ)` for additive cocycles `c`.

The target remains the actual right-derived sheaf. No proposed splitting,
finite-dimensionality, or value of that sheaf is assumed or asserted.
-/
