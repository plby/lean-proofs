import Wikipedia.HopfProblem.PeriodTorusAppellHumbertEtaNontrivial
import Wikipedia.HopfProblem.PeriodTorusAppellHumbertIntrinsicSections
import Wikipedia.HopfProblem.PeriodTorusAppellHumbertCoreTensor

/-!
# Actual Appell--Humbert line bundles on the actual period tori

Integral alternating forms of type `(1,1)` determine explicitly constructed
norm-one semicharacters and holomorphic factors on the actual period lattice.
The factor cocycle defines the actual orbit quotient of `ℂ² × ℂ`.
Its analytic covering atlas and its projection preserve the original
period-torus complex structure. Holomorphic transition functions define
an independently topologized line-bundle core, and an explicit analytic
fibre-linear diffeomorphism identifies that core with the orbit quotient.

Mathlib's genuine holomorphic sections of this bundle are proved equivalent
to entire analytic scalar functions with the displayed theta automorphy.
For every nonzero integer multiple of `η`, the actual holomorphic-section
module is zero. The zero multiple has an explicit analytic trivialization;
no nonzero multiple is analytically trivial. Coefficient addition and
integer scaling give actual factor products and powers; fibre tensor
equivalences intertwine the original transition maps and local charts.

This is a realizability and section theorem for constructed bundles.
No classification of arbitrary line bundles, first-Chern-class comparison,
Néron--Severi identification, or algebraic-dimension conclusion is assumed.
-/
