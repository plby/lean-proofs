import Wikipedia.HopfProblem.PeriodTorusTypeOneOnePositivity

/-!
# Integral tangent forms of type `(1,1)` on the actual period tori

This family proves the linear-algebra assertions underlying source
Lemmas 9.2 and 9.4, with the actual period lattice and its actual real
period equivalence:

* every alternating lattice-integral real form has unique integer
  coefficients in the ordered positions `γu, γw, γδ, uw, uδ, wδ`;
* invariance under simultaneous multiplication by `I` is equivalent to
  the displayed source period polynomial vanishing;
* each such form has its uniquely associated first-linear Hermitian
  form whose imaginary part is the given form;
* `η = u ∧ w + 6 γ ∧ δ` is nondegenerate, has signature `(1,1)`, and
  has square `12 γ ∧ u ∧ w ∧ δ` in the genuine integral exterior algebra;
* outside the proved countable exceptional locus of the actual special
  period map, every intrinsic integral form of type `(1,1)` is a unique
  integer multiple of `η`; every nonzero such form is nondegenerate and
  indefinite, so the only one with nonnegative associated Hermitian
  form is zero.

No identification with Néron--Severi groups, de Rham cohomology, line
bundles, or algebraic dimension is assumed or claimed by these files.
-/
