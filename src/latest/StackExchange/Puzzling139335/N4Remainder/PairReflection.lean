import StackExchange.Puzzling139335.N4Remainder.PairReflection.Classification
import StackExchange.Puzzling139335.N4Remainder.PairReflection.Images

/-!
# The intrinsic reflection preserving the bottom pair

A reversing affine isometry preserving a set with nonempty interior in
the square, and preserving its bottom endpoint pair, is the square's
vertical reflection. Consequently, the horizontal reflection of the set
equals its image under the global half-turn about the square center.
-/

open Set

namespace Puzzling139335.N4Remainder

theorem horizontal_image_eq_pointReflection_image_of_invariant_bottom_pair
    {P : Set Plane} (e : Plane ≃ᵃⁱ[ℝ] Plane)
    (hdet : (PlaneIsometries.linearMatrix e).det = -1)
    (hpair : e '' {corner 0, corner 1} = {corner 0, corner 1})
    (hP : P ⊆ unitSquare) (hint : (interior P).Nonempty) (heP : e '' P = P) :
    ReflectionSeparation.horizontal '' P =
      (AffineIsometryEquiv.pointReflection ℝ squareCenter) '' P := by
  apply horizontal_image_eq_pointReflection_image
  have heq := eq_vertical_of_invariant_bottom_pair e hdet hpair hP hint heP
  simpa only [heq] using heP

end Puzzling139335.N4Remainder
