import Wikipedia.HopfProblem.SmoothMorseLemmaSignedChart

/-!
# The genuine finite-dimensional smooth Morse lemma

For a real function smooth on an open subset of a finite-dimensional
normed real space, an actual critical point with bijective actual Hessian
has a native `C∞` partial-diffeomorphism chart. The source is contained in
the original open set. Both the forward and inverse normal-form identities
hold for the original function.

The principal results in `Wikipedia.HopfProblem.SmoothMorseLemma` are:

* `exists_morse_chart_of_contDiffOn`: the exact half-Hessian normal form,
  with chart derivative the identity at the critical point;
* `exists_signed_morse_chart_of_contDiffOn`: the classical sum of squares
  with every coefficient exactly `-1` or `1`;
* `exists_morse_chart` and `exists_signed_morse_chart`: their globally
  smooth specializations.

The proof constructs a smooth symmetric Taylor factor using the actual
integral Hessian, proves a local smooth congruence factor by applying the
inverse-function theorem to a polynomial with derivative `2 • id`, and
then applies that theorem again to the actual coordinate map. A genuine
smooth bump handles local domains; Sylvester's theorem supplies the final
signed linear coordinates. No normal form, sphere-recognition theorem,
or smooth topological classification result is assumed.
-/
