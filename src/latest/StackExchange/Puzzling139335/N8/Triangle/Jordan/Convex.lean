import StackExchange.Puzzling139335.JordanTransport
import StackExchange.Puzzling139335.SquareExterior
import StackExchange.Puzzling139335.RectangularHull.CornerGeometry
import Mathlib.Analysis.Convex.GaugeRescale

/-!
# Compact convex regions with interior are Jordan regions

The gauge-rescaling homeomorphism of the ambient plane transports the
unit square to any compact convex set with nonempty interior.
-/

open Set

namespace Puzzling139335.N8

/-- A compact convex planar set with nonempty interior is a Jordan region. -/
theorem isJordanRegion_of_isCompact_convex {K : Set Plane}
    (hcompact : IsCompact K) (hconvex : Convex ℝ K)
    (hinterior : (interior K).Nonempty) : IsJordanRegion K := by
  obtain ⟨e, _, he, _⟩ := exists_homeomorph_image_eq
    RectangularHull.convex_unitSquare isJordanRegion_unitSquare.interior_nonempty
    (NormedSpace.isVonNBounded_of_isBounded ℝ isJordanRegion_unitSquare.isBounded)
    hconvex hinterior (NormedSpace.isVonNBounded_of_isBounded ℝ hcompact.isBounded)
  have himage : e '' unitSquare = K := by
    simpa only [isClosed_unitSquare.closure_eq, hcompact.isClosed.closure_eq] using he
  rw [← himage]
  exact isJordanRegion_unitSquare.image_homeomorph e

end Puzzling139335.N8
