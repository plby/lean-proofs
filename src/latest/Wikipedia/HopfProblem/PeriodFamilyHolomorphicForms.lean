import Wikipedia.HopfProblem.PeriodFamilyHolomorphicFormsSpecial
import Wikipedia.HopfProblem.PeriodFamilyHolomorphicFormsTranslation

/-!
# Period-family holomorphic coefficient normal forms

This package proves the scalar coefficient calculation of Lemma 9.15:
actual full-lattice quasiperiodicity gives an affine function, the two
fixed real period columns kill its linear part, and the constructed
special periods give the one-, two-, and three-covector normal forms on
every open upper-half-plane subset. The dense nonvanishing of the actual
first-period derivative is proved, not an extra input to the special
two-form theorem.

Full scalar pullback evaluations imply the required period identities
and all three group covariance formulas (9.8)--(9.10). The surrounding
native differential-form layer supplies these evaluations for genuine
holomorphic tangent-covector sections; this package introduces no
replacement definition of differential forms.
-/
