import Wikipedia.HopfProblem.CuspNormalizationGermsAtPoint
import Wikipedia.HopfProblem.CuspNormalizationGermsClosure

/-!
# Actual holomorphic-germ integral closure for the cusp normalization

This module completes the local integral-closure characterization of the
actual component map in Proposition 4.6(i).

* Analytic germs are genuine neighbourhood germs admitting holomorphic
  representatives. Their local-ring structure and maximal ideals are
  proved using evaluation and actual analytic reciprocals.
* The actual central-set germ ring in an adapted cusp chart embeds by
  actual component pullback into its analytic branch-germ product. The
  kernel is the intersection of the actual branch vanishing ideals, and
  this extension is finite and integral.
* Actual coordinate cofactors identify the genuine total fraction ring
  with the product of the branch fraction fields.
* The smooth two-variable analytic-germ rings are proved integrally
  closed: a monic equation bounds a fraction, and a transverse fixed-circle
  Cauchy construction gives its genuine jointly analytic extension.
* `Germs.componentProjection_local_integral_closure` identifies the branch
  product with the literal integral closure at every actual central point,
  compatibly with pullback along the actual component map.

The rings on the singular fibre are actual restricted ambient-analytic
function germs on its reduced central set. No polynomial or formal
power-series replacement, normalization theorem, or analytic extension
hypothesis is used for the final local integral-closure theorem.
-/
