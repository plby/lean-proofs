import Wikipedia.HopfProblem.CuspNormalizationSheafConstantsResolutionExact

/-!
# The actual constant and holomorphic normalization resolutions

The constant sequence uses Mathlib's actual constant sheaves, the actual
normalization and double-curve direct images, and the actual skyscraper
sheaves at the two triple points. Its maps are independently constructed
pullbacks, source-oriented differences, and the signed endpoint evaluations.

`SheafResolution.constantResolution_exact` proves exactness of this actual
sequence. `SheafResolution.constantResolutionComparison` is its genuine
termwise monomorphism to the proved exact holomorphic normalization
resolution, with identity on the skyscrapers and both zero endpoints.

The transfer of exactness uses constructed scalar-evaluation retractions
on the actual stalks. It does not assume a comparison theorem, local
exactness, or a locally constant model for disconnected-open sections.
No higher-cohomology vanishing or cohomology comparison is asserted here.
-/
