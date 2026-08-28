import Wikipedia.HopfProblem.CuspNormalizationSheafExactHolomorphic
import Wikipedia.HopfProblem.CuspNormalizationSheafConstantsResolution

/-!
# The two actual normalization resolutions of the cusp fibre

For the actual singular cusp fibre `W`, this package constructs the reduced
holomorphic-function sheaf, the actual normalization direct image, the
three actual double-curve direct images, and the scalar skyscrapers at the
two actual triple points. The source-oriented restriction differences and
alternating endpoint evaluations give the exact sequence

`0 → O_W → ν_*O_E₀ → ⨁ₖ (iₖ)_*O_Dₖ → ℂ_P ⊕ ℂ_Q → 0`.

`SheafResolution.resolution_exact` proves exactness as genuine Mathlib
sheaves of abelian groups, through the actual analytic-germ comparisons.
`SheafResolution.constantResolution_exact` proves the analogous sequence
of actual constant sheaves. `SheafResolution.constantResolutionComparison`
is the actual termwise constants morphism between the entire sequences,
and all its components are monomorphisms.

These are the normalization resolutions in source Lemma 9.12(i). This
package makes no higher-cohomology acyclicity or comparison assumption,
and does not yet assert the resulting cohomology dimensions of `W`.
-/
