/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.HLOZPositiveInterfaceAggregateRecovery
import ErdosProblems.Erdos1165.TilingOrientedPrefixedBoundarySourceLocalTime

/-!
# The positive-interface base window lies below the retained count cutoff

The physical deficit-shell window must be intersected with the honest
same-rank accepted window.  Its fixed boundary maximum dominates the
retained coordinate multiplicity: the latter is the local time at the
orientation-selected endpoint, which is one of the two endpoints entering
the maximum.  Consequently the accepted base window automatically removes
the saturated part of natural subtraction.
-/

namespace Erdos1165.HLOZPositiveInterfacePhysicalBaseWindow

open HLOZPositiveInterfaceAggregateRecovery
open HLOZPositiveInterfaceSupportSelector
open LazyDecomposition
open TilingCappedMarginalization
open TilingOrientedAllCreationStoppedCoordinate
open TilingOrientedAllRepresentedExternalFiber
open TilingOrientedPrefixedBoundarySourceLocalTime
open TilingOrientedRetainedDominoEndpoint
open TilingOrientedShellZeroSourcePartition
open TilingOrientedSupportAwayCoordinates
open TilingPrefixedFavoriteTraceSupport
open TilingPrefixedInsertedLocalTime
open TilingSpatialInsertionFiber

noncomputable section

abbrev DominoTiling := Tilings.Tiling

attribute [local instance] Classical.propDecidable

/-- The retained multiplicity of a positive-interface coordinate is bounded
by the larger of the two fixed physical endpoint local times. -/
theorem positiveInterfaceCoordinateCount_le_fixedBoundaryDominoMax
    {t : DominoTiling} {o : Orientation} {m k externalThreshold : ℕ}
    (eta : PositiveInterfaceSupportedIndex t o m k externalThreshold)
    (hm : 1 < m) (hk : 0 < k)
    (b : TilingExternalDomino t eta.1.1.external.start
      eta.1.1.external.retained) :
    Fintype.card (TilingCoordinatesAt t eta.1.1.external.start
        eta.1.1.external.retained b) ≤
      prefixedTilingFixedBoundaryDominoMax eta.1.1.external.initial.1
        eta.1.1.external.start eta.1.1.external.retained
        (positiveInterfaceTerminal eta) b := by
  classical
  let etaExternal : SupportedIndex t o m k :=
    ⟨eta.1.1.external, by
      rcases eta.2 with ⟨s, hs⟩
      refine ⟨s, hs.1.1, hs.1.2.1, ?_⟩
      exact congrArg OrientedAllCreationTraceCode.external hs.1.2.2⟩
  have hcard :=
    prefixedBoundaryLocalTime_orientedEndpoint_eq_coordinateCard
      etaExternal hm hk (fun _ ↦ 0) b
  have hcard' :
      prefixedTilingFixedBoundaryLocalTime eta.1.1.external.initial.1
          eta.1.1.external.start eta.1.1.external.retained
          (positiveInterfaceTerminal eta)
          (orientedDominoEndpoint t o b.1) =
        Fintype.card (TilingCoordinatesAt t eta.1.1.external.start
          eta.1.1.external.retained b) := by
    simpa only [etaExternal, positiveInterfaceTerminal] using hcard
  rw [← hcard']
  unfold prefixedTilingFixedBoundaryDominoMax orientedDominoEndpoint
  split_ifs
  · exact Nat.le_max_left _ _
  · exact Nat.le_max_right _ _

/-- The honest prefix-correct base window is automatically contained in the
strict-below-level range defined by retained coordinate multiplicity. -/
theorem positiveInterfaceBaseWindow_subset_coordinateRange
    {t : DominoTiling} {o : Orientation} {m k externalThreshold : ℕ}
    (eta : PositiveInterfaceSupportedIndex t o m k externalThreshold)
    (hm : 1 < m) (hk : 0 < k) (cap : ℕ)
    (b : TilingAwayDomino t ((PositiveInterfaceFiber eta).start cap)
      ((PositiveInterfaceFiber eta).retained cap)
      ((PositiveInterfaceFiber eta).distinguished cap)) :
    positiveInterfaceBaseWindow eta cap b ⊆ Finset.range
      (m - Fintype.card (TilingCoordinatesAt t
        ((PositiveInterfaceFiber eta).start cap)
        ((PositiveInterfaceFiber eta).retained cap) b.1)) := by
  intro v hv
  unfold positiveInterfaceBaseWindow at hv
  rw [Finset.mem_range] at hv ⊢
  have hcard := positiveInterfaceCoordinateCount_le_fixedBoundaryDominoMax
    eta hm hk b.1
  exact hv.trans_le (Nat.sub_le_sub_left hcard m)

end

end Erdos1165.HLOZPositiveInterfacePhysicalBaseWindow
