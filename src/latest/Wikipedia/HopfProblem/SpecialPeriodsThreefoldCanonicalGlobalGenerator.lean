import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalGlobalGeneratorInverse

/-!
# The actual global generator used in Proposition 9.11

The imported construction retains the actual Eisenstein-root generator
from Lemma 3.10 at the proved special period map.  All its hypotheses are
discharged by the normalized triangle quotient and modular lifting:

* it is holomorphic on the upper half-plane, and its zero set is exactly
  the two actual elliptic orbits;
* it has the source's two generator covariance laws and actual cusp
  invariance;
* its orders in the actual normalized elliptic discs are two and one,
  with analytic nonvanishing quotient germs represented on positive balls;
* in the original cusp exponential coordinate it has a simple pole, with
  an analytic nonvanishing coefficient on one chosen positive disc;
* the reciprocal coefficient extends with a simple zero at the cusp,
  while the cancelled elliptic reciprocal coefficients extend as units.

The implementation is in `SpecialPeriods.Threefold.Canonical.GlobalGenerator`.
No global generator, cusp germ, coordinate-order identity, or analytic
unit is assumed as input.
-/
