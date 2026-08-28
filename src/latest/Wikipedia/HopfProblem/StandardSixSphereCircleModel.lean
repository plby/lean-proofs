import Wikipedia.HopfProblem.StandardSixSphereCircleModelEquator
import Wikipedia.HopfProblem.StandardSixSphereCircleModelRegions
import Wikipedia.HopfProblem.StandardSixSphereCircleModelSmooth

/-!
# The original standard six-sphere complement and its marked boundary

All spaces in this package are literal subspaces of standard Euclidean
spaces, with the original sphere, open-subset, and product smooth atlases.

* `equatorHomeomorph` identifies the equator `y = 0` with the unit `S²`.
* `diffeomorph` identifies the actual complement `y ≠ 0` with `ℝ³ × S³`
  by `(x,y) ↦ (x/‖y‖, y/‖y‖)`.
* `forward_boundaryPoint` preserves the marked normal unit vector exactly.
* `levelHomeomorph` restricts this same chart to complete radius level sets.
* `closedExteriorHomeomorph` identifies the actual region `‖y‖ ≥ r`
  with a closed Euclidean three-ball times `S³`.

No assertion about the constructed complex threefold or its complement is
made here. In particular, no identification, recognition, or handle theorem
is assumed or inferred from this standard-model calculation.
-/
