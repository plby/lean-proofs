import Wikipedia.HopfProblem.SpecialPeriodsThreefoldEllipticPieces
import Wikipedia.HopfProblem.SpecialPeriodsEllipticFillingSmallOverlap

/-!
# The actual small elliptic overlap maps

The logarithmic gauges and period-family comparisons give genuine partial
biholomorphisms from the two actual small elliptic pieces to the actual
regular family.  Their source and target are the full inverse images of
the corresponding base patches, and they preserve the original compact
base point.  All data are now unconditional.
-/

noncomputable section

open Set Topology UpperHalfPlane
open scoped ContDiff Manifold OnePoint

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold

attribute [local instance] triangleCompactifiedChartedSpace specialRegularFamilyChartedSpace
  specialEllipticPieceChartedSpace

local notation "IF" => modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)

/-- The actual overlap, restricted to the chosen main elliptic filling. -/
def specialEllipticOverlap (j : Elliptic.Kind) :
    PartialDiffeomorph IF IF (SpecialEllipticPiece j) SpecialRegularFamily ω :=
  EllipticFilling.smallOverlap specialPeriodMap specialPeriodMap_generator₁
    specialPeriodMap_generator₂ specialBaseCover j

theorem specialEllipticOverlap_source (j : Elliptic.Kind) :
    (specialEllipticOverlap j).source =
      specialEllipticPieceProjectionToBase j ⁻¹'
        (regularPatch : Set TriangleCompactifiedOrbitSpace) :=
  EllipticFilling.smallOverlap_source specialPeriodMap specialPeriodMap_generator₁
    specialPeriodMap_generator₂ specialBaseCover j

theorem specialEllipticOverlap_target (j : Elliptic.Kind) :
    (specialEllipticOverlap j).target =
      specialRegularFamilyProjectionToBase ⁻¹'
        (specialBaseCover.fillingPatch (some j) : Set TriangleCompactifiedOrbitSpace) :=
  EllipticFilling.smallOverlap_target specialPeriodMap specialPeriodMap_generator₁
    specialPeriodMap_generator₂ specialBaseCover j

theorem specialEllipticOverlap_base (j : Elliptic.Kind) (x : SpecialEllipticPiece j)
    (hx : x ∈ (specialEllipticOverlap j).source) :
    specialRegularFamilyProjectionToBase (specialEllipticOverlap j x) =
      specialEllipticPieceProjectionToBase j x :=
  EllipticFilling.smallOverlap_base specialPeriodMap specialPeriodMap_generator₁
    specialPeriodMap_generator₂ specialBaseCover j x hx

end Wikipedia.HopfProblem.SpecialPeriods.Threefold
