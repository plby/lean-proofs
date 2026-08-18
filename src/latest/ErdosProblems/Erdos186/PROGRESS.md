# Erdős Problem 186 progress

## Current phase

Lean formalization: sharp upper bound.

## Verified

- `tex/186.tex` gives the detailed Bosznay lower bound, the
  Conlon--Fox--Pham/Pham--Zakharov upper-bound dependency chain, and the
  Leanization plan.
- `Foundations.lean`, `SubsetSums.lean`, and `LowerBound.lean` formalize the
  exact extremal problem and prove Bosznay's `N^(1/4) = O(F(N))` bound.
- The finite maximum/asymptotic packaging, GAP and subset-sum algebra,
  normalization, reduction estimates, zonotope rounding, lattice
  intersection, convex-normalization reductions, and final density-iteration
  contradiction are checked.
- The adapted-HNF repair and its inverse coefficient estimates are checked;
  `DenseBox.exists_basisProgression_sandwich_symmetricBox` now proves the
  required two-sided lattice-box/GAP containment without an extra lattice
  assumption.
- The full integer Lev interval theorem is checked and is now consumed by
  the dense-box development.
- Bilu's exact badly-approximable estimate, distortion-measure lower bound,
  torus fundamental-domain lift, and their Section 8 measure synthesis are
  checked.
- The general Mahler basis theorem and both halves of Minkowski's second
  theorem are checked in every dimension; the upper bound currently uses the
  dimension-only constant `8^d`, which is sufficient for CFP and discrete
  John.
- `DenseBox.denseBoxLemma` is now the unconditional CFP dense-box lemma; its
  explicit certificate construction and complete numerical discharge are
  checked.
- The discrete-John theorem is now unconditional: Mahler extraction, the
  active saturated rank, exact coordinate transport, and a sufficient
  dimension-only factor derived from the `8^d` upper Minkowski bound are all
  checked.
- The finite-hull determinant-cancellation proof is source-complete.
  Maximal-simplex normalization handles full affine span, the lower-span
  difference body is null, and the two branches give the exact all-rank
  symmetric-reduction input to PZ Lemma 7.  Its focused object-file build is
  pending restoration of the currently saturated shared Lean host, so it is
  not yet counted as independently verified.
- Bilu's exact central-section inequality (Lemma 6.7) and its arbitrary
  isometric codimension-one consequence (Lemma 6.6) are checked without an
  assumed Rogers--Shephard or Brunn inequality.
- The concrete zonotope error-box absorption and Equation (15), the
  projection-cardinality full-rank criterion, and the canonical
  lattice-qualified two-side target constructor are checked.
- `ErdosProblems/Erdos186.lean` checks with the full current PZ composition
  import.  Its two conditional assembly theorems have only the standard
  Mathlib axioms `propext`, `Classical.choice`, and `Quot.sound`.
- The global forbidden-token/limit scan and `git diff --check` are currently
  clean.

## Open failures

- CFP Theorem 1.5 / the higher-dimensional Corollary 5 is not yet proved.
  The dominant missing input is the general Bilu sorted Freiman-container
  theorem; dense-box is complete, while its Corollary 2.17 packaging,
  preprocessing trace bounds, and the remaining Bilu container steps are
  still being assembled.
- The PZ all-dimensional convex-density theorem is reduced to the exact
  normalized finite-hull core.  The clamped unit-grid shell, affine graph
  normalization, and small-hull branch are checked; the large-hull cap/graph
  branch and its numerical join remain.
- The post-CFP intersection theorem still needs the source coefficient-balanced
  two-side selection and centered-zonotope thickness lemma, together with the
  context-dependent `M` hierarchy feeding the checked inverse-coordinate,
  canonical-target, and projection-cardinality mechanisms.
- The irreducible-replacement theorem has a checked guarded terminal and
  first-crossing contradiction; the remaining step is to discharge the three
  terminal rank cases and compose the public statement.
- PZ Lemma 7 now has a single continuous gap: the outer-volume estimate for
  the canonical active full-rank certificate, including mixed small radii and
  the additive lattice-rounding term.  The formerly broader arbitrary rank-d
  certificate statement was false because of padded zero-radius directions
  and has been corrected to the canonical section rank.
- The conditional component theorems have not yet been assembled into an
  unconditional `PZBoxBound`; therefore the final theorem `erdos_186` does not
  yet exist.

## Next step

Complete the remaining CFP/Bilu, convex-density, and intersection existence
theorems; prove the one-step assembly; define unconditional `erdos_186`; then
rerun the main Lean check, full forbidden-token scan, whitespace check, and
`#print axioms Erdos186.erdos_186`.
