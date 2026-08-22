/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.HLOZDominantPositiveInterfaceSupportSelector
import ErdosProblems.Erdos1165.TilingOrientedExternalAllCreationStoppedCoordinate

/-!
# Stopped fibres on the dominant adjacent-pair support
-/

namespace Erdos1165.HLOZDominantPositiveInterfacePairSupportFiber

open HLOZDominantPositiveInterfaceSupportSelector
open HLOZPositiveInterfacePairSupportSelector
open HLOZPositiveInterfaceSupportSelector
open HLOZPrefixedAllCreationStaticSupportAggregateRefinement
open LazyDecomposition
open TilingOrientedAllCreationConcreteFamily
open TilingOrientedAllCreationStoppedCoordinate
open TilingOrientedExternalAllCreationStoppedCoordinate
open TilingOrientedRetainedDominoEndpoint
open TilingOrientedShellZeroSourcePartition
open TilingOrientedSupportAwayCoordinates
open TilingCappedMarginalization
open TilingPrefixedFavoriteTraceSupport
open TilingPrefixedInsertedLocalTime
open TilingLazyDecomposition
open TilingSpatialInsertionFiber
open VariableStoppedTracePartition

noncomputable section

abbrev DominoTiling := Tilings.Tiling

abbrev DominantPositiveInterfacePairSupportAt
    (t : DominoTiling) (o : Orientation)
    (m externalThreshold width shell : ℕ) :=
  orientedDominantPositiveInterfacePairSupportAt t o m externalThreshold
    width shell

abbrev DominantPositiveInterfaceExternalPairSupportedIndex
    (t : DominoTiling) (o : Orientation)
    (m k externalThreshold width shell : ℕ) :=
  SupportedIndex t o m k
    (DominantPositiveInterfacePairSupportAt t o m externalThreshold width shell)

abbrev DominantPositiveInterfaceExternalPairFiber
    {t : DominoTiling} {o : Orientation}
    {m k externalThreshold width shell : ℕ}
    (eta : DominantPositiveInterfaceExternalPairSupportedIndex t o m k
      externalThreshold width shell) :=
  TilingOrientedExternalAllCreationStoppedCoordinate.concreteFiber o m k
    (DominantPositiveInterfacePairSupportAt t o m externalThreshold width shell)
    (orientedDominantPositiveInterfacePairSupportSelectorData t o m k
      externalThreshold width shell) eta

abbrev DominantPositiveInterfaceExternalPairCoordinate
    {t : DominoTiling} {o : Orientation}
    {m k externalThreshold width shell : ℕ}
    (eta : DominantPositiveInterfaceExternalPairSupportedIndex t o m k
      externalThreshold width shell) :=
  TilingAwayDomino t eta.1.1.start eta.1.1.retained
    (supportComplementDistinguished t eta.1.1.start eta.1.1.retained eta.1.2)

noncomputable def dominantPositiveInterfaceExternalPairTerminal
    {t : DominoTiling} {o : Orientation}
    {m k externalThreshold width shell : ℕ}
    (eta : DominantPositiveInterfaceExternalPairSupportedIndex t o m k
      externalThreshold width shell) : Option Point :=
  prefixedTilingInsertionTerminal eta.1.1.initial t eta.1.1.start
    eta.1.1.retained (fun _ ↦ 0) eta.1.1.tail

theorem dominantPositiveInterfaceExternalPairTerminal_eq_coordinates
    {t : DominoTiling} {o : Orientation}
    {m k externalThreshold width shell : ℕ}
    (eta : DominantPositiveInterfaceExternalPairSupportedIndex t o m k
      externalThreshold width shell)
    (q : Fin (eta.1.1.retainedCount + 1) → ℕ) :
    prefixedTilingInsertionTerminal eta.1.1.initial t eta.1.1.start
        eta.1.1.retained q eta.1.1.tail =
      dominantPositiveInterfaceExternalPairTerminal eta := by
  exact prefixedTilingInsertionTerminal_eq_of_coordinates
    eta.1.1.initial t eta.1.1.start eta.1.1.retained q (fun _ ↦ 0)
      eta.1.1.tail rfl

/-- Thickness is inherited from the ambient oriented interface support. -/
theorem dominantPositiveInterfaceExternalPairCoordinateCount_ge_externalThreshold
    {t : DominoTiling} {o : Orientation}
    {m k externalThreshold width shell : ℕ}
    (eta : DominantPositiveInterfaceExternalPairSupportedIndex t o m k
      externalThreshold width shell) (_cap : ℕ)
    (b : DominantPositiveInterfaceExternalPairCoordinate eta) :
    externalThreshold ≤ Fintype.card
      (TilingCoordinatesAt t eta.1.1.start eta.1.1.retained b.1) := by
  classical
  have hbS : b.1.1 ∈ eta.1.2 :=
    (away_mem_support_iff t eta.1.1.start eta.1.1.retained eta.1.2 b.1).1 b.2
  rcases eta.2 with ⟨s, hs⟩
  rw [orientedExternalAllCreationSupportTraceAtom_eq] at hs
  let n := creationTimeNat m k s
  have hbPair : b.1.1 ∈ orientedDominantPositiveInterfacePairSupportAt
      t o m externalThreshold width shell s n := by
    change b.1.1 ∈ DominantPositiveInterfacePairSupportAt t o m
      externalThreshold width shell s n
    dsimp only [n]
    rw [hs.2.2.2]
    exact hbS
  have hbRaw := orientedDominantPositiveInterfacePairSupportAt_subset_raw
    t o m externalThreshold width shell s n hbPair
  have hbSupport := orientedPositiveInterfacePairSupportAt_subset t o m
    externalThreshold width shell s n hbRaw
  unfold orientedPositiveInterfaceSupportAt at hbSupport
  rw [hs.2.2.1] at hbSupport
  rcases mem_orientedPositiveInterfaceCodeSupport_iff.mp hbSupport with
    ⟨_hb, hthick, _hbelow⟩
  simpa using hthick

/-- Dominance is fixed by the external word and therefore holds on every
coordinate of the stopped fibre. -/
theorem dominantPositiveInterfaceExternalPairCoordinate_dominant
    {t : DominoTiling} {o : Orientation}
    {m k externalThreshold width shell : ℕ}
    (eta : DominantPositiveInterfaceExternalPairSupportedIndex t o m k
      externalThreshold width shell)
    (b : DominantPositiveInterfaceExternalPairCoordinate eta) :
    prefixedTilingFixedBoundaryLocalTime eta.1.1.initial.1 eta.1.1.start
          eta.1.1.retained (dominantPositiveInterfaceExternalPairTerminal eta)
          (tilingPartner t (orientedDominoEndpoint t o b.1.1)) ≤
      prefixedTilingFixedBoundaryLocalTime eta.1.1.initial.1 eta.1.1.start
          eta.1.1.retained (dominantPositiveInterfaceExternalPairTerminal eta)
          (orientedDominoEndpoint t o b.1.1) := by
  classical
  have hbS : b.1.1 ∈ eta.1.2 :=
    (away_mem_support_iff t eta.1.1.start eta.1.1.retained eta.1.2 b.1).1 b.2
  rcases eta.2 with ⟨s, hs⟩
  rw [orientedExternalAllCreationSupportTraceAtom_eq] at hs
  let n := creationTimeNat m k s
  have hbPair : b.1.1 ∈ orientedDominantPositiveInterfacePairSupportAt
      t o m externalThreshold width shell s n := by
    change b.1.1 ∈ DominantPositiveInterfacePairSupportAt t o m
      externalThreshold width shell s n
    dsimp only [n]
    rw [hs.2.2.2]
    exact hbS
  have hdominant := orientedEndpointDominantAt_of_mem_pairSupport hbPair
  unfold orientedEndpointDominantAt at hdominant
  rw [hs.2.2.1] at hdominant
  exact hdominant

end

end Erdos1165.HLOZDominantPositiveInterfacePairSupportFiber
