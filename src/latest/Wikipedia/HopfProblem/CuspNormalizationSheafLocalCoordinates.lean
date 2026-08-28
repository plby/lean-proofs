import Wikipedia.HopfProblem.CuspNormalizationSheafLocalCoordinatesTriplePoints
import Wikipedia.HopfProblem.CuspNormalizationGermsChartMap

/-!
# Actual local coordinates for the normalization sheaf maps

The genuine normalization fibre is indexed by its active coordinate planes.
The actual source double curves through the point are in bijection with
the pairs of these active planes. Their signed lifts select the appropriate
actual fibre points, and their inverse axis charts lie in the existing
maximal holomorphic atlas.

In the actual centered branch and curve charts, the signed lifts are
literal coordinate-axis inclusions. Their analytic-germ pullbacks are the
axis restrictions used by the local exact complexes. The imported actual
normalization pullback is likewise the coordinate-plane restriction.
The triple-point branch and axis tables retain the source's global signs.

This package supplies the local geometric comparisons; it does not assume
or assert the exactness of the global sheaf resolution.
-/
