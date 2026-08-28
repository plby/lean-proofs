import Wikipedia.HopfProblem.CuspCircleNormalTrivializationConifoldNormalization
import Wikipedia.HopfProblem.CuspCircleNormalTrivializationConifoldSmooth
import Wikipedia.HopfProblem.CuspCircleNormalTrivializationConifoldRank

/-!
# The native toric small resolution and its genuine conifold boundary

The original two toric charts define a real-analytic map to the actual
two-by-two complex matrix space, with their literal small-resolution
formulae. Its determinant vanishes, its Frobenius radius is the original
normal radius, its zero fibre is the original middle curve, and it is
injective elsewhere and onto the entire determinant-zero locus.

Every nonzero normal-radius boundary is genuinely homeomorphic to the
literal rank-one Frobenius level. The original diagonal circle action
becomes right multiplication by `diag(u⁻¹,u)`. For every positive native
radius, the explicit normalized smoothing comparison retains the actual
unit normal vector `F/r`.

These are local native geometry and boundary identifications. No claim
about a global threefold complement or smooth sphere recognition is made.
-/

namespace Wikipedia.HopfProblem.CuspCircleNormalTrivialization.Conifold

/-- The actual global product matrix always has complex rank at most one. -/
theorem productMap_rank_le_one (p : RiemannSphere × Fibre) : (productMap p).rank ≤ 1 :=
  matrix_rank_le_one_of_det_zero (productMap p) (productMap_det p)

/-- The original global toric matrix always has complex rank at most one. -/
theorem toricMap_rank_le_one (y : toricNeighborhood) : (toricMap y).rank ≤ 1 :=
  matrix_rank_le_one_of_det_zero (toricMap y) (toricMap_det y)

/-- Off the actual zero section, the original global product matrix has rank exactly one. -/
theorem productMap_rank_eq_one (p : RiemannSphere × Fibre) (hp : p.2 ≠ 0) :
    (productMap p).rank = 1 :=
  matrix_rank_eq_one_of_det_zero (productMap p) (productMap_det p)
    (fun h => hp ((productMap_eq_zero_iff p).mp h))

/-- Off the original middle curve, the genuine toric matrix has rank exactly one. -/
theorem toricMap_rank_eq_one (y : toricNeighborhood)
    (hy : (toricNeighborhoodDiffeomorph.symm y).2 ≠ 0) : (toricMap y).rank = 1 :=
  matrix_rank_eq_one_of_det_zero (toricMap y) (toricMap_det y)
    (fun h => hy ((toricMap_eq_zero_iff y).mp h))

/-- In particular, every actual nonzero-radius toric boundary maps to rank-one matrices. -/
theorem toricBoundaryHomeomorph_rank_one {r : ℝ} (hr : r ≠ 0) (y : ToricBoundary r) :
    ((toricBoundaryHomeomorph hr y).val).rank = 1 :=
  matrix_rank_eq_one_of_det_zero (toricBoundaryHomeomorph hr y).val
    (toricBoundaryHomeomorph hr y).property.1
    (ConifoldStandardBoundary.conifoldBoundary_ne_zero hr (toricBoundaryHomeomorph hr y))

end Wikipedia.HopfProblem.CuspCircleNormalTrivialization.Conifold
