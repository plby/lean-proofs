import Wikipedia.HopfProblem.PeriodTorusCohomologyAlternatingDescent
import Wikipedia.HopfProblem.PeriodTorusCohomologyAlternatingFullEta
import Wikipedia.HopfProblem.PeriodTorusCohomologyAlternatingRealForms
import Wikipedia.HopfProblem.PeriodTorusCohomologyAlternatingTranslations

/-!
# Native integral second cohomology and genuine alternating period forms

This package identifies the actual singular-cochain cohomology of the
constructed period tori with their integral alternating forms, preserving
evaluation on genuine ordered products of positive period loops.  It
proves actual period-change and affine-deck pullbacks, the full-period
marking conversion, and the primitive distinguished class `η`.

The intrinsic real-form correspondence is exhaustive: no presentation by
six coefficients is assumed.  For the actual elliptic surfaces, the
original covering pulls back uniquely descended integral classes to `η`
and `2 η`, respectively.

The package does not claim a singular cup-product, a complex-orientation
comparison, or identification with first Chern classes.  Those require
separate geometric comparisons.
-/
