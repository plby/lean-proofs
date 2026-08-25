import StackExchange.Puzzling139335.Definitions
import StackExchange.Puzzling139335.Basic
import StackExchange.Puzzling139335.DissectionTopology
import StackExchange.Puzzling139335.InitialReduction
import StackExchange.Puzzling139335.IntrinsicCorners
import StackExchange.Puzzling139335.FourIncidences
import StackExchange.Puzzling139335.GeometricReduction
import StackExchange.Puzzling139335.CaseReduction
import StackExchange.Puzzling139335.Transform
import StackExchange.Puzzling139335.Mass
import StackExchange.Puzzling139335.BandMass
import StackExchange.Puzzling139335.SingletonBand
import StackExchange.Puzzling139335.QuadrantMass
import StackExchange.Puzzling139335.JordanCrosscut
import StackExchange.Puzzling139335.AntipodalEndpoints
import StackExchange.Puzzling139335.QuarterTurnPair
import StackExchange.Puzzling139335.CentralTwoPiece
import StackExchange.Puzzling139335.HalfTurnPair
import StackExchange.Puzzling139335.SymmetryOrbit
import StackExchange.Puzzling139335.SegmentCrossing
import StackExchange.Puzzling139335.ReflectionSeparation
import StackExchange.Puzzling139335.PlaneIsometries
import StackExchange.Puzzling139335.ArcVariation
import StackExchange.Puzzling139335.LoopVariation
import StackExchange.Puzzling139335.TranslationCancellation
import StackExchange.Puzzling139335.UnitPairs
import StackExchange.Puzzling139335.AcuteCorner
import StackExchange.Puzzling139335.ThreeCorners
import StackExchange.Puzzling139335.PrefixCertificate
import StackExchange.Puzzling139335.N5Facet
import StackExchange.Puzzling139335.N7Geometry
import StackExchange.Puzzling139335.ProperRotation
import StackExchange.Puzzling139335.GlideCrossing
import StackExchange.Puzzling139335.TwoSideFaces
import StackExchange.Puzzling139335.SourceFaceBridge
import StackExchange.Puzzling139335.DoubleCorner
import StackExchange.Puzzling139335.N4Midline
import StackExchange.Puzzling139335.N4Diagonal
import StackExchange.Puzzling139335.N4TwoOneOne
import StackExchange.Puzzling139335.N4OuterPairMiddle
import StackExchange.Puzzling139335.RemainingCases
import StackExchange.Puzzling139335.N6
import StackExchange.Puzzling139335.FinalReduction
import StackExchange.Puzzling139335.N5

/-!
# Puzzling Stack Exchange 139335: four congruent pieces avoiding the center

The main result is `Puzzling139335.square_center_theorem`, proving
`Puzzling139335.SquareCenterTheorem`:
every four-piece dissection into congruent closed Jordan regions has its
center on the cut set. The definition of `SquareDissection` includes only
the original geometric hypotheses, not any intermediate classification.

The proof excludes every possible corner-incidence count. All intrinsic
corner types, contact intervals, supporting directions, and normalized
placements are derived from the actual dissection.

No computational limits are raised and no new axiom is declared. The
Jordan/Schoenflies results are supplied by the existing development.
`IntegrationAudit` records the axiom dependencies of the final theorem.
-/

open Set

namespace Puzzling139335

/-- A square cannot be dissected into four congruent closed Jordan pieces
with an open neighborhood of its center contained in one piece. -/
theorem square_center_theorem :
    ∀ d : SquareDissection, ¬ ∃ i : Fin 4, squareCenter ∈ interior (d.piece i) := by
  intro d hc
  obtain ⟨D, ⟨q⟩⟩ := d.exists_prepared_of_protected_center hc
  exact q.impossible

theorem SquareDissection.not_hasProtectedCenter (d : SquareDissection) :
    ¬ d.HasProtectedCenter := square_center_theorem d

/-- The neighborhood formulation: every positive-radius ball at the center
contains a point outside any prescribed piece. -/
theorem SquareDissection.center_ball_not_subset_piece (d : SquareDissection)
    (i : Fin 4) {r : ℝ} (hr : 0 < r) :
    ¬ Metric.ball squareCenter r ⊆ d.piece i := by
  intro hsub
  apply d.not_hasProtectedCenter
  exact ⟨i, mem_interior_iff_mem_nhds.mpr (Metric.mem_nhds_iff.mpr ⟨r, hr, hsub⟩)⟩

/-- The center lies on the boundaries of at least two distinct pieces. -/
theorem SquareDissection.center_mem_two_frontiers (d : SquareDissection) :
    ∃ i j : Fin 4, i ≠ j ∧ squareCenter ∈ frontier (d.piece i) ∧
      squareCenter ∈ frontier (d.piece j) :=
  d.center_mem_two_frontiers_of_not_protected d.not_hasProtectedCenter

end Puzzling139335

#print axioms Puzzling139335.square_center_theorem
