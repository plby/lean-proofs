/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.HLOZPositiveInterfacePairSupportFiber
import ErdosProblems.Erdos1165.HLOZPositiveInterfacePhysicalBalanceData
import ErdosProblems.Erdos1165.HLOZPositiveInterfacePairWeightedScreen

/-!
# Physical balance data on exact positive-interface pair histories

An external pair history fixes the same physical external word as a broad
positive-interface history, but records only the two adjacent shell rows in
its support.  The pair support is contained in the broad support, so every
exposed pair coordinate is also an exposed coordinate of that broad history.
Consequently the deterministic physical balance hypotheses restrict to the
exact pair fibre.
-/

namespace Erdos1165.HLOZPositiveInterfacePairPhysicalBalance

open HLOZPositiveInterfaceAggregateRecovery
open HLOZPositiveInterfacePairSupportFiber
open HLOZPositiveInterfacePairSupportSelector
open HLOZPositiveInterfacePairWeightedScreen
open HLOZPositiveInterfacePhysicalBalanceData
open HLOZPositiveInterfacePhysicalWindowRatio
open HLOZProposition48Candidates
open HLOZPositiveInterfaceSupportSelector
open LazyDecomposition
open SmallWindow
open TilingCappedMarginalization
open TilingOrientedAllCreationStoppedCoordinate
open TilingOrientedExternalAllCreationStoppedCoordinate
open TilingOrientedSupportAwayCoordinates
open TilingSpatialInsertionFiber
open TilingVariableStoppedTracePartition
open VariableStoppedTracePartition

noncomputable section

abbrev DominoTiling := Tilings.Tiling

private theorem card_eq_of_fintype_instances
    {α : Type*} (I J : Fintype α) :
    @Fintype.card α I = @Fintype.card α J :=
  @Fintype.card_congr α α I J (Equiv.refl α)

/-- The broad positive-interface history carried by an external exact-pair
history.  We retain its external word and recover current-favorite data and
the broad support from one path in the nonempty external atom. -/
noncomputable def positiveInterfaceSupportedIndexOfExternalPair
    {t : DominoTiling} {o : Orientation}
    {m k externalThreshold width shell : ℕ}
    (eta : PositiveInterfaceExternalPairSupportedIndex t o m k
      externalThreshold width shell) :
    PositiveInterfaceSupportedIndex t o m k externalThreshold := by
  let s := Classical.choose eta.2
  have hs := Classical.choose_spec eta.2
  have hexists : ∃ favorite : TilingCreationFavoriteData,
      s ∈ orientedAllCreationSupportTraceAtom t o m k
        (PositiveInterfacePairSupportAt t o m externalThreshold width shell)
        (withFavorite eta.1.1 favorite) eta.1.2 :=
    Set.mem_iUnion.mp hs
  let favorite := Classical.choose hexists
  have hpairAtom := Classical.choose_spec hexists
  let S := orientedPositiveInterfaceSupportAt t o m externalThreshold s
    (creationTimeNat m k s)
  exact ⟨(withFavorite eta.1.1 favorite, S), ⟨s, hpairAtom.1, rfl⟩⟩

@[simp] theorem positiveInterfaceSupportedIndexOfExternalPair_external
    {t : DominoTiling} {o : Orientation}
    {m k externalThreshold width shell : ℕ}
    (eta : PositiveInterfaceExternalPairSupportedIndex t o m k
      externalThreshold width shell) :
    (positiveInterfaceSupportedIndexOfExternalPair eta).1.1.external =
      eta.1.1 := by
  simp [positiveInterfaceSupportedIndexOfExternalPair]

/-- An exact pair coordinate, viewed as a coordinate in the recovered broad
positive-interface history. -/
noncomputable def positiveInterfaceExternalPairCoordinateToBroad
    {t : DominoTiling} {o : Orientation}
    {m k externalThreshold width shell : ℕ}
    (eta : PositiveInterfaceExternalPairSupportedIndex t o m k
      externalThreshold width shell)
    (b : PositiveInterfaceExternalPairCoordinate eta) :
    TilingAwayDomino t
      (positiveInterfaceSupportedIndexOfExternalPair eta).1.1.external.start
      (positiveInterfaceSupportedIndexOfExternalPair eta).1.1.external.retained
      (supportComplementDistinguished t
        (positiveInterfaceSupportedIndexOfExternalPair eta).1.1.external.start
        (positiveInterfaceSupportedIndexOfExternalPair eta).1.1.external.retained
        (positiveInterfaceSupportedIndexOfExternalPair eta).1.2) := by
  let s := Classical.choose eta.2
  have hs := Classical.choose_spec eta.2
  have hexists : ∃ favorite : TilingCreationFavoriteData,
      s ∈ orientedAllCreationSupportTraceAtom t o m k
        (PositiveInterfacePairSupportAt t o m externalThreshold width shell)
        (withFavorite eta.1.1 favorite) eta.1.2 :=
    Set.mem_iUnion.mp hs
  let favorite := Classical.choose hexists
  have hpairAtom := Classical.choose_spec hexists
  have hbPair : b.1.1 ∈ eta.1.2 :=
    (away_mem_support_iff t eta.1.1.start eta.1.1.retained eta.1.2 b.1).1
      b.2
  have hbPath : b.1.1 ∈ orientedPositiveInterfacePairSupportAt t o m
      externalThreshold width shell s (creationTimeNat m k s) := by
    have hsupport : orientedPositiveInterfacePairSupportAt t o m
        externalThreshold width shell s (creationTimeNat m k s) = eta.1.2 :=
      hpairAtom.2
    exact hsupport.symm ▸ hbPair
  have hbBroad := orientedPositiveInterfacePairSupportAt_subset t o m
    externalThreshold width shell s (creationTimeNat m k s) hbPath
  refine ⟨b.1, ?_⟩
  apply (away_mem_support_iff t
    (positiveInterfaceSupportedIndexOfExternalPair eta).1.1.external.start
    (positiveInterfaceSupportedIndexOfExternalPair eta).1.1.external.retained
    (positiveInterfaceSupportedIndexOfExternalPair eta).1.2 b.1).2
  simpa only [positiveInterfaceSupportedIndexOfExternalPair, s, hexists,
    favorite] using hbBroad

@[simp] theorem positiveInterfaceExternalPairCoordinateToBroad_val
    {t : DominoTiling} {o : Orientation}
    {m k externalThreshold width shell : ℕ}
    (eta : PositiveInterfaceExternalPairSupportedIndex t o m k
      externalThreshold width shell)
    (b : PositiveInterfaceExternalPairCoordinate eta) :
    (positiveInterfaceExternalPairCoordinateToBroad eta b).1 = b.1 := by
  rfl

/-- Physical balance on the broad positive-interface support restricts to
the exact adjacent-pair support. -/
theorem positiveInterfaceExternalPairArithmetic_of_physicalBalance
    {t : DominoTiling} {o : Orientation}
    {m k externalThreshold width shell : ℕ}
    (data : PhysicalInterfaceBalanceData t o m k externalThreshold width
      shell)
    (hexternal : 0 < externalThreshold)
    (eta : PositiveInterfaceExternalPairSupportedIndex t o m k
      externalThreshold width shell) (cap : ℕ) :
    PositiveInterfaceExternalPairArithmetic eta cap where
  external_pos := hexternal
  width_ge_four := data.width_ge_four
  window_ratio := by
    intro b
    have hi : Fintype.card (TilingCoordinatesAt t eta.1.1.start
          eta.1.1.retained b.1) ≤ m - (shell + 2) * width + 1 := by
      convert data.coordinate_fit
        (positiveInterfaceSupportedIndexOfExternalPair eta) cap
        (positiveInterfaceExternalPairCoordinateToBroad eta b) using 1 <;>
        simp [positiveInterfaceSupportedIndexOfExternalPair,
          positiveInterfaceExternalPairCoordinateToBroad,
          OrientedAllCreationPrefixedStoppedCoordinateSpec.start,
          OrientedAllCreationPrefixedStoppedCoordinateSpec.retained] <;>
        apply card_eq_of_fintype_instances
    have hmode : 15 * (m - shell * width -
          Fintype.card (TilingCoordinatesAt t eta.1.1.start
            eta.1.1.retained b.1)) + 1 ≤
        Fintype.card (TilingCoordinatesAt t eta.1.1.start
          eta.1.1.retained b.1) := by
      convert data.below_mode
        (positiveInterfaceSupportedIndexOfExternalPair eta) cap
        (positiveInterfaceExternalPairCoordinateToBroad eta b) using 1 <;>
        simp [positiveInterfaceSupportedIndexOfExternalPair,
          positiveInterfaceExternalPairCoordinateToBroad,
          OrientedAllCreationPrefixedStoppedCoordinateSpec.start,
          OrientedAllCreationPrefixedStoppedCoordinateSpec.retained] <;>
        first
        | apply card_eq_of_fintype_instances
        | congr 1
    have hiPos : 0 < Fintype.card (TilingCoordinatesAt t eta.1.1.start
        eta.1.1.retained b.1) := hexternal.trans_le
      (positiveInterfaceExternalPairCoordinateCount_ge_externalThreshold
        eta cap b)
    exact (acceptedPhysicalAdjacentWindowMass_le_four_thirds_of_endpoint
      hiPos data.width_ge_four data.shells_fit hi hmode).trans
        (mul_le_mul_of_nonneg_right four_thirds_le_positiveInterfaceRatioConstant
          (windowMass_nonneg _ _))
  boundary_lt := by
    intro b
    convert data.boundary_lt
      (positiveInterfaceSupportedIndexOfExternalPair eta) cap
      (positiveInterfaceExternalPairCoordinateToBroad eta b) using 1 <;>
      simp [positiveInterfaceSupportedIndexOfExternalPair,
        positiveInterfaceExternalPairCoordinateToBroad,
        OrientedAllCreationPrefixedStoppedCoordinateSpec.start,
        OrientedAllCreationPrefixedStoppedCoordinateSpec.retained,
        positiveInterfaceTerminal, positiveInterfaceExternalPairTerminal] <;>
      apply card_eq_of_fintype_instances

end

end Erdos1165.HLOZPositiveInterfacePairPhysicalBalance
