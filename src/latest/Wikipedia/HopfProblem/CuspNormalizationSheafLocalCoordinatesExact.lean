import Wikipedia.HopfProblem.CuspNormalizationSheafLocalCoordinatesExactUniform
import Wikipedia.HopfProblem.CuspNormalizationSheafLocalCoordinatesExactAugmentation
import Wikipedia.HopfProblem.CuspNormalizationSheafLocalCoordinatesExactComplexes

/-!
# Exactness of the actual source-oriented local analytic-germ maps

For any active branch subset, genuine restricted ambient-analytic germs
are exactly the tuples with zero signed differences on all incident axes.
These uniform differences are exact at the axis term against alternating
evaluation when the full triple is active, and against zero otherwise.

The smooth and double cases are short exact, and the full triple has an
exact resolution including both zero endpoints. All maps retain the source
orientation. The imported geometric coordinate identities identify these
axis restrictions with pullback along the actual two normalization lifts.

No exactness assertion for global sheaves is assumed here: this package
supplies the proved local analytic-germ complexes used for that comparison.
-/
