import Wikipedia.HopfProblem.FourthHurewiczFiveSimplexWhiskerPath
import Wikipedia.HopfProblem.FourthHurewiczFiveSimplexWhiskerFacets

/-!
# Actual cubical whiskering and all of its facet identities

`whiskeredCell` takes an actual codimension-two-based `(n+2)`-cube to an
actual codimension-two-based `(n+1)`-cube of native one-loops. The compact-open
continuity and full basedness conditions are proved, including for `n = 0`.

`whiskeredLoop_path` identifies the loop with the prescribed three-piece
path concatenation. `whiskeredCell_face_normal` and
`whiskeredCell_face_last_upper` identify every uncurried facet as a literal
concatenation of the original native facets, in their original coordinates.
No homotopy quotient, Hurewicz theorem, or connectivity hypothesis is used
to replace these equalities.
-/
