import Wikipedia.HopfProblem.TriangleHolomorphicDifferentialsEllipticPower
import Wikipedia.HopfProblem.TriangleHolomorphicDifferentialsDescent
import Wikipedia.HopfProblem.TriangleHolomorphicDifferentialsVanishing
import Wikipedia.HopfProblem.TriangleHolomorphicDifferentialsCuspOrderChart
import Wikipedia.HopfProblem.TriangleHolomorphicDifferentialsCuspDescent
import Wikipedia.HopfProblem.TriangleHolomorphicDifferentialsSphere
import Wikipedia.HopfProblem.TriangleHolomorphicDifferentialsRemovable

/-!
# Holomorphic scalar differentials for the actual triangle action

This package proves the source's local cyclic descent and scalar
vanishing arguments (Lemmas 9.17--9.19). The action, special periods,
elliptic branching, cusp coordinate, and compact quotient are the
actual previously constructed objects.

The scalar coefficient hypotheses express holomorphicity, the stated
pullback law, and analytic first-order decay in the actual cusp
parameter. No descended extension, degree formula, or vanishing result
is assumed. The main conclusions are `invariant_oneForm_eq_zero` and
`weight_oneForm_eq_zero` in `TriangleHolomorphicDifferentials`.
-/
