/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.HLOZDominantPositiveInterfaceSupportSelector
import ErdosProblems.Erdos1165.TilingOrientedExternalAllCreationStoppedCoordinate

/-!
# Exact stopped fibres on one adjacent physical pair support

The raw positive-interface fibre exposes every thick retained domino.  An
actual-rank comparison must expose only the coordinates which occur in the
two adjacent physical rows; otherwise the possible endpoint increment is
proportional to the entire retained support.  This file packages the exact
pair selector as the standard all-creation stopped fibre.  No product or
probability estimate is asserted here.
-/

namespace Erdos1165.HLOZPositiveInterfacePairSupportFiber

open HLOZDominantPositiveInterfaceSupportSelector
open HLOZPositiveInterfacePairSupportSelector
open HLOZPositiveInterfaceSupportSelector
open HLOZPrefixedAllCreationStaticSupportAggregateRefinement
open LazyDecomposition
open TilingOrientedAllCreationConcreteFamily
open TilingOrientedAllCreationStoppedCoordinate
open TilingOrientedExternalAllCreationStoppedCoordinate
open TilingOrientedRetainedDominoEndpoint
open TilingOrientedSupportAwayCoordinates
open TilingCappedMarginalization
open TilingLazyDecomposition
open TilingPrefixedFavoriteTraceSupport
open TilingPrefixedInsertedLocalTime
open TilingSpatialInsertionFiber
open VariableStoppedTracePartition

noncomputable section

abbrev DominoTiling := Tilings.Tiling

/-- The exact adjacent-pair support selector, with the parameters ordered as
used by its stopped-coordinate family. -/
abbrev PositiveInterfacePairSupportAt
    (t : DominoTiling) (o : Orientation)
    (m externalThreshold width shell : ℕ) :=
  orientedDominantPositiveInterfacePairSupportAt t o m externalThreshold
    width shell

/-- Nonempty exact creation histories fixing the physical external trace and
the adjacent-pair support. -/
abbrev PositiveInterfacePairSupportedIndex
    (t : DominoTiling) (o : Orientation)
    (m k externalThreshold width shell : ℕ) :=
  OrientedAllCreationSupportedAtomIndex t o m k
    (PositiveInterfacePairSupportAt t o m externalThreshold width shell)

/-- The concrete prefixed stopped-coordinate fibre on one exact pair
history. -/
abbrev PositiveInterfacePairFiber
    {t : DominoTiling} {o : Orientation}
    {m k externalThreshold width shell : ℕ}
    (eta : PositiveInterfacePairSupportedIndex t o m k externalThreshold
      width shell) :=
  ConcreteFiber
    (orientedDominantPositiveInterfacePairSupportSelectorData t o m k
      externalThreshold width shell) eta

/-- Nonempty external-word atoms on the exact pair support.  Current
favorite data is erased so replacement coordinates may change it. -/
abbrev PositiveInterfaceExternalPairSupportedIndex
    (t : DominoTiling) (o : Orientation)
    (m k externalThreshold width shell : ℕ) :=
  SupportedIndex t o m k
    (PositiveInterfacePairSupportAt t o m externalThreshold width shell)

/-- The external-word stopped fibre on one exact adjacent-pair support. -/
abbrev PositiveInterfaceExternalPairFiber
    {t : DominoTiling} {o : Orientation}
    {m k externalThreshold width shell : ℕ}
    (eta : PositiveInterfaceExternalPairSupportedIndex t o m k
      externalThreshold width shell) :=
  TilingOrientedExternalAllCreationStoppedCoordinate.concreteFiber o m k
    (PositiveInterfacePairSupportAt t o m externalThreshold width shell)
    (orientedDominantPositiveInterfacePairSupportSelectorData t o m k
      externalThreshold width shell) eta

/-- Exposed away coordinates of one external pair fibre. -/
abbrev PositiveInterfaceExternalPairCoordinate
    {t : DominoTiling} {o : Orientation}
    {m k externalThreshold width shell : ℕ}
    (eta : PositiveInterfaceExternalPairSupportedIndex t o m k
      externalThreshold width shell) :=
  TilingAwayDomino t eta.1.1.start eta.1.1.retained
    (supportComplementDistinguished t eta.1.1.start eta.1.1.retained eta.1.2)

/-- The external-word terminal is independent of insertion totals. -/
noncomputable def positiveInterfaceExternalPairTerminal
    {t : DominoTiling} {o : Orientation}
    {m k externalThreshold width shell : ℕ}
    (eta : PositiveInterfaceExternalPairSupportedIndex t o m k
      externalThreshold width shell) : Option Point :=
  prefixedTilingInsertionTerminal eta.1.1.initial t eta.1.1.start
    eta.1.1.retained (fun _ ↦ 0) eta.1.1.tail

theorem positiveInterfaceExternalPairTerminal_eq_coordinates
    {t : DominoTiling} {o : Orientation}
    {m k externalThreshold width shell : ℕ}
    (eta : PositiveInterfaceExternalPairSupportedIndex t o m k
      externalThreshold width shell)
    (q : Fin (eta.1.1.retainedCount + 1) → ℕ) :
    prefixedTilingInsertionTerminal eta.1.1.initial t eta.1.1.start
        eta.1.1.retained q eta.1.1.tail =
      positiveInterfaceExternalPairTerminal eta := by
  exact prefixedTilingInsertionTerminal_eq_of_coordinates
    eta.1.1.initial t eta.1.1.start eta.1.1.retained q (fun _ ↦ 0)
      eta.1.1.tail rfl

/-- Every coordinate of an external pair atom retains the thickness lower
bound inherited from the ambient positive-interface support. -/
theorem positiveInterfaceExternalPairCoordinateCount_ge_externalThreshold
    {t : DominoTiling} {o : Orientation}
    {m k externalThreshold width shell : ℕ}
    (eta : PositiveInterfaceExternalPairSupportedIndex t o m k
      externalThreshold width shell) (_cap : ℕ)
    (b : TilingAwayDomino t eta.1.1.start eta.1.1.retained
      (supportComplementDistinguished t eta.1.1.start eta.1.1.retained
        eta.1.2)) :
    externalThreshold ≤ Fintype.card
      (TilingCoordinatesAt t eta.1.1.start eta.1.1.retained b.1) := by
  classical
  have hbS : b.1.1 ∈ eta.1.2 :=
    (away_mem_support_iff t eta.1.1.start eta.1.1.retained eta.1.2 b.1).1 b.2
  rcases eta.2 with ⟨s, hs⟩
  rw [orientedExternalAllCreationSupportTraceAtom_eq] at hs
  let n := creationTimeNat m k s
  have hbPair : b.1.1 ∈ orientedPositiveInterfacePairSupportAt t o m
      externalThreshold width shell s n := by
    have hbDominant : b.1.1 ∈ orientedDominantPositiveInterfacePairSupportAt
        t o m externalThreshold width shell s n := by
      change b.1.1 ∈ PositiveInterfacePairSupportAt t o m externalThreshold
        width shell s n
      dsimp only [n]
      rw [hs.2.2.2]
      exact hbS
    exact orientedDominantPositiveInterfacePairSupportAt_subset_raw
      t o m externalThreshold width shell s n hbDominant
  have hbSupport := orientedPositiveInterfacePairSupportAt_subset t o m
    externalThreshold width shell s n hbPair
  unfold orientedPositiveInterfaceSupportAt at hbSupport
  rw [hs.2.2.1] at hbSupport
  rcases mem_orientedPositiveInterfaceCodeSupport_iff.mp hbSupport with
    ⟨_hb, hthick, _hbelow⟩
  simpa using hthick

/-- Every exposed coordinate belongs to the normalized dominant support, so
its orientation-selected endpoint dominates its mate at the fixed external
boundary. -/
theorem positiveInterfaceExternalPairCoordinate_dominant
    {t : DominoTiling} {o : Orientation}
    {m k externalThreshold width shell : ℕ}
    (eta : PositiveInterfaceExternalPairSupportedIndex t o m k
      externalThreshold width shell)
    (b : PositiveInterfaceExternalPairCoordinate eta) :
    prefixedTilingFixedBoundaryLocalTime eta.1.1.initial.1 eta.1.1.start
          eta.1.1.retained (positiveInterfaceExternalPairTerminal eta)
          (tilingPartner t (orientedDominoEndpoint t o b.1.1)) ≤
      prefixedTilingFixedBoundaryLocalTime eta.1.1.initial.1 eta.1.1.start
          eta.1.1.retained (positiveInterfaceExternalPairTerminal eta)
          (orientedDominoEndpoint t o b.1.1) := by
  classical
  have hbS : b.1.1 ∈ eta.1.2 :=
    (away_mem_support_iff t eta.1.1.start eta.1.1.retained eta.1.2 b.1).1 b.2
  rcases eta.2 with ⟨s, hs⟩
  rw [orientedExternalAllCreationSupportTraceAtom_eq] at hs
  let n := creationTimeNat m k s
  have hbPair : b.1.1 ∈ orientedDominantPositiveInterfacePairSupportAt
      t o m externalThreshold width shell s n := by
    change b.1.1 ∈ PositiveInterfacePairSupportAt t o m externalThreshold
      width shell s n
    dsimp only [n]
    rw [hs.2.2.2]
    exact hbS
  have hdominant := orientedEndpointDominantAt_of_mem_pairSupport hbPair
  unfold orientedEndpointDominantAt at hdominant
  rw [hs.2.2.1] at hdominant
  exact hdominant

/-- The optional physical terminal does not depend on insertion totals. -/
noncomputable def positiveInterfacePairTerminal
    {t : DominoTiling} {o : Orientation}
    {m k externalThreshold width shell : ℕ}
    (eta : PositiveInterfacePairSupportedIndex t o m k externalThreshold
      width shell) : Option Point :=
  prefixedTilingInsertionTerminal eta.1.1.external.initial t
    eta.1.1.external.start eta.1.1.external.retained (fun _ ↦ 0)
    eta.1.1.external.tail

theorem positiveInterfacePairTerminal_eq_coordinates
    {t : DominoTiling} {o : Orientation}
    {m k externalThreshold width shell : ℕ}
    (eta : PositiveInterfacePairSupportedIndex t o m k externalThreshold
      width shell)
    (q : Fin (eta.1.1.external.retainedCount + 1) → ℕ) :
    prefixedTilingInsertionTerminal eta.1.1.external.initial t
        eta.1.1.external.start eta.1.1.external.retained q
        eta.1.1.external.tail =
      positiveInterfacePairTerminal eta := by
  exact prefixedTilingInsertionTerminal_eq_of_coordinates
    eta.1.1.external.initial t eta.1.1.external.start
    eta.1.1.external.retained q (fun _ ↦ 0) eta.1.1.external.tail rfl

end

end Erdos1165.HLOZPositiveInterfacePairSupportFiber
