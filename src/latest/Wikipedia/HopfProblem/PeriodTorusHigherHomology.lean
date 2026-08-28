import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCircleNormalization
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCrossProductFormalPrism
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCrossProductTensor
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyMarkingFullPeriod
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyMonodromy
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyPontryagin
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyTensorSplitting
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyTensorTransport
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyTranslations

/-!
# Actual higher singular homology of the period tori

This entry collects the actual singular-chain and Mayer--Vietoris proofs
of the integral homology of finite products of circles and the actual
period tori in `tex/s6.tex`.

The principal geometric results are:

* `productTorusHomologyEquiv`: in every degree, the actual integral
  homology of the product of `r` circles is free of rank `Nat.choose r n`;
* `periodTorusH2ExteriorEquiv` and `periodTorusH3ExteriorEquiv`: canonical
  exterior-square and exterior-cube markings of actual period-torus
  homology, with inverses given by actual ordered products of positive
  period loops;
* `periodTorusH2_step₁_conjugate`, `periodTorusH2_step₂_conjugate`,
  `periodTorusH2_step₀_conjugate` and their degree-three counterparts:
  the actual induced maps are the literal ordered-minor matrices of
  `A₁`, `A₂`, and `M₀`;
* the corresponding canonical markings for every full period matrix
  and the four-circle coordinate torus, including arbitrary integral
  matrix actions on the latter;
* actual translations act trivially on singular homology in all degrees.

The underlying circle-product calculation uses the proved singular
Mayer--Vietoris sequence. Cross products, their normalization, symmetry,
associativity, and naturality are constructed on actual singular chains.
No Künneth comparison or exterior-power homology identification is assumed.

These statements concern the constructed tori and their actual maps.
They do not identify the homology of a global glued threefold, a singular
cusp central fibre, or an elliptic quotient surface.
-/
