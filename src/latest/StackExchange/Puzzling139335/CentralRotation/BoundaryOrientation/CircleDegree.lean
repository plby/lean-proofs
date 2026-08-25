import StackExchange.Puzzling139335.CentralRotation.BoundaryOrientation.CircleDegree.Algebra
import StackExchange.Puzzling139335.CentralRotation.BoundaryOrientation.CircleDegree.Composition
import StackExchange.Puzzling139335.CentralRotation.BoundaryOrientation.CircleDegree.Homotopy
import StackExchange.Puzzling139335.CentralRotation.BoundaryOrientation.CircleDegree.Homeomorphism

/-!
# Circle displacement and boundary orientation

`CircleDegree.displacement` is the endpoint difference of an actual lift of a
continuous path through the covering `ℝ → AddCircle 1`.  The imported theorems
prove that it is independent of the chosen starting lift, additive under path
concatenation, negated by reversal, unchanged by constant circle translation,
and invariant under a free homotopy of loops.  Zero displacement is equivalent
to contraction relative to the endpoints.

For circle maps, `CircleDegree.degree` is integral, homotopy invariant, and
multiplicative under composition.  Applying a circle map to a closed path
multiplies its displacement by the map's degree.
Every circle homeomorphism has degree `1` or `-1`, with the corresponding
increasing or decreasing real lift.  All statements are proved from the
covering-map and ordered-real-line APIs; no orientation premise is inserted in
the definition of a circle homeomorphism.
-/
