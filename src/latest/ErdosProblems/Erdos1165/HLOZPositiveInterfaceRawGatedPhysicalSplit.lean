/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.HLOZPositiveInterfaceRawPhysicalReconstruction

/-!
# Splitting the raw physical positive interface at the coordinate gate

The raw adjacent-shell growth reconstruction first lands in the ungated
physical stopped-coordinate tail.  This module applies the exact coordinate
gate split.  The good branch is the screened product event.  The other branch
retains the raw thresholded tail and records an actual upper-row coordinate
which fails the physical eligibility conditions.  No estimate is asserted for
that explicit remainder here.
-/

open Set

namespace Erdos1165.HLOZPositiveInterfaceRawGatedPhysicalSplit

open FiniteDominoProductLaw HeterogeneousProductTail
open HLOZAllCreationCofinalConditionalSharpWindow
open HLOZAllSixBandProductClosure
open HLOZDynamicThresholdedScreening
open HLOZGapRandomClockScreen HLOZPathEvents
open HLOZPositiveInterfaceAggregateRecovery
open HLOZPositiveInterfaceGatedPhysicalScreenedEvent
open HLOZPositiveInterfaceGatedPhysicalSplit
open HLOZPositiveInterfacePhysicalScreenedEvent
open HLOZPositiveInterfacePhysicalWindows
open HLOZPositiveInterfaceRawPhysicalReconstruction
open HLOZPrefixedAllCreationStaticSupportAggregateRefinement
open HLOZPrefixedAllCreationStaticSupportAggregateRefinement.StaticSupportRecoveryCertificate
open HLOZProposition48Candidates
open HLOZRawFullGapProductPromotion
open LazyDecomposition NearFavoriteShells NearFavoriteThresholded
open PathInsertion PreStoppingFiber
open TilingCappedMarginalization
open TilingOrientedAllCreationConcreteFamily
open TilingOrientedAllCreationStoppedCoordinate
open TilingOrientedSupportAwayCoordinates
open TilingPrefixedStoppedProductDisintegration
open TilingSpatialInsertionFiber VariableStoppedTracePartition

noncomputable section

attribute [local instance] Classical.propDecidable

abbrev DominoTiling := Tilings.Tiling

/-- On one capped exact atom, the honest physical tail together with an actual
upper-row coordinate which fails the deterministic coordinate gate.  The raw
tail is retained: this is not enlarged to the bare existence of an ineligible
coordinate. -/
noncomputable def positiveInterfacePhysicalIneligibleUpperPredicate
    {t : DominoTiling} {o : Orientation} {m k externalThreshold : ℕ}
    (eta : PositiveInterfaceSupportedIndex t o m k externalThreshold)
    (hm : 1 < m) (hk : 0 < k) (threshold : ℕ → ℕ)
    (width shell bound cap : ℕ)
    (q : TilingCappedCoordinates eta.1.1.external.retainedCount
      ((PositiveInterfaceFiber eta).coordinateCap cap)) : Prop :=
  let cert := positiveInterfaceStaticSupportRecoveryCertificate eta hm hk
  (PositiveInterfaceFiber eta).atomPredicate cap q ∧
    ∃ ell : TruncatedTotals ((PositiveInterfaceFiber eta).upper cap),
      cert.baseProp cap ell ∧
      allCreationRandomTotalThresholdedUpperTail (PositiveInterfaceFiber eta)
        cap
        (fun b (u : Fin ((PositiveInterfaceFiber eta).upper cap b)) ↦
          (u : ℕ) ∈ physicalDeficitFailureWindow m width
            (Fintype.card (TilingCoordinatesAt t
              ((PositiveInterfaceFiber eta).start cap)
              ((PositiveInterfaceFiber eta).retained cap) b.1)) (shell + 1))
        (fun b (u : Fin ((PositiveInterfaceFiber eta).upper cap b)) ↦
          (u : ℕ) ∈ physicalDeficitFailureWindow m width
            (Fintype.card (TilingCoordinatesAt t
              ((PositiveInterfaceFiber eta).start cap)
              ((PositiveInterfaceFiber eta).retained cap) b.1)) shell)
        threshold shellGrowth48 shell bound ell ∧
      (∃ b, ¬ positiveInterfacePhysicalEligible width shell eta cap b ∧
        positiveInterfacePhysicalUpper width shell eta cap b (ell b)) ∧
      ∀ b, tilingAwayTotal t ((PositiveInterfaceFiber eta).start cap)
          ((PositiveInterfaceFiber eta).retained cap)
          ((PositiveInterfaceFiber eta).distinguished cap)
          ((splitTilingCoordinatesEquiv t
            ((PositiveInterfaceFiber eta).start cap)
            ((PositiveInterfaceFiber eta).retained cap)
            ((PositiveInterfaceFiber eta).distinguished cap) q).2) b = ell b

/-- One exact stopped fibre of the ineligible-upper remainder. -/
def positiveInterfacePhysicalIneligibleUpperFiber
    {t : DominoTiling} {o : Orientation} {m k externalThreshold : ℕ}
    (eta : PositiveInterfaceSupportedIndex t o m k externalThreshold)
    (hm : 1 < m) (hk : 0 < k) (threshold : ℕ → ℕ)
    (width shell bound cap : ℕ) : Set WalkPath :=
  walkLift (prefixedTilingPreStoppingFiberEvent
    ((PositiveInterfaceFiber eta).stoppingTime cap)
    ((PositiveInterfaceFiber eta).initial cap) t
    ((PositiveInterfaceFiber eta).start cap)
    ((PositiveInterfaceFiber eta).retained cap)
    ((PositiveInterfaceFiber eta).coordinateCap cap)
    ((PositiveInterfaceFiber eta).tail cap)
    (positiveInterfacePhysicalIneligibleUpperPredicate eta hm hk threshold
      width shell bound cap))

/-- Cofinal union of exact physical tails possessing an actual ineligible
upper-row witness.  Its definition deliberately retains the raw tail and the
exact stopped totals. -/
def positiveInterfacePhysicalIneligibleUpperEvent
    (t : DominoTiling) (o : Orientation) (m k externalThreshold : ℕ)
    (hm : 1 < m) (hk : 0 < k) (threshold : ℕ → ℕ)
    (width shell bound : ℕ) : Set WalkPath :=
  ⋃ eta : PositiveInterfaceSupportedIndex t o m k externalThreshold,
    ⋃ cap : ℕ,
      positiveInterfacePhysicalIneligibleUpperFiber eta hm hk threshold width
        shell bound cap

/-- The ungated physical event splits exactly into the product-paid gated
event and a raw-tail event with an actual ineligible upper coordinate. -/
theorem positiveInterfacePhysicalScreenedEvent_subset_gated_union_ineligible
    (t : DominoTiling) (o : Orientation) (m k externalThreshold : ℕ)
    (hm : 1 < m) (hk : 0 < k) (threshold : ℕ → ℕ)
    (width shell bound : ℕ) :
    positiveInterfacePhysicalScreenedEvent t o m k externalThreshold hm hk
        threshold width shell bound ⊆
      positiveInterfaceGatedPhysicalScreenedEvent t o m k externalThreshold
          hm hk threshold width shell bound ∪
        positiveInterfacePhysicalIneligibleUpperEvent t o m k
          externalThreshold hm hk threshold width shell bound := by
  classical
  intro s hs
  rcases Set.mem_iUnion.mp hs with ⟨eta, hs⟩
  rcases Set.mem_iUnion.mp hs with ⟨cap, hs⟩
  rcases hs with ⟨hvalid, hfiber⟩
  rcases Set.mem_iUnion.mp hfiber with ⟨qacc, hqstop⟩
  rcases qacc with ⟨q, hscreened, haccepted⟩
  rcases hscreened with ⟨hpred, ell, hell, htotal⟩
  have hraw := (positiveInterfacePhysicalScreenedAccepts_eq_true_iff eta hm hk
    threshold width shell bound cap ell).mp hell
  have hrawNamed : allCreationRandomTotalThresholdedUpperTail
      (PositiveInterfaceFiber eta) cap
      (positiveInterfacePhysicalUpper width shell eta cap)
      (positiveInterfacePhysicalLower width shell eta cap)
      threshold shellGrowth48 shell bound ell := by
    unfold positiveInterfacePhysicalUpper positiveInterfacePhysicalLower
    unfold allCreationRandomTotalThresholdedUpperTail at hraw ⊢
    convert hraw.2 using 1
  rcases physicalTail_gated_or_exists_ineligible_upper eta threshold width
      shell bound cap ell hrawNamed with hgated | hineligible
  · apply Or.inl
    refine Set.mem_iUnion.mpr ⟨eta, Set.mem_iUnion.mpr ⟨cap, ?_⟩⟩
    refine ⟨hvalid, Set.mem_iUnion.mpr ⟨⟨q, ?_, haccepted⟩, hqstop⟩⟩
    refine ⟨hpred, ell, ?_, htotal⟩
    dsimp only
    unfold StaticSupportRecoveryCertificate.gatedPhysicalScreenedAccepts
    apply decide_eq_true
    refine ⟨hraw.1, ?_⟩
    unfold StaticSupportRecoveryCertificate.gatedPhysicalUpper
      StaticSupportRecoveryCertificate.gatedPhysicalLower
    unfold StaticSupportRecoveryCertificate.gatedFiber
    unfold allCreationRandomTotalThresholdedUpperTail at hgated ⊢
    unfold positiveInterfacePhysicalUpper positiveInterfacePhysicalLower at hgated
    convert hgated using 1
  · apply Or.inr
    refine Set.mem_iUnion.mpr ⟨eta, Set.mem_iUnion.mpr ⟨cap, ?_⟩⟩
    refine ⟨hvalid, Set.mem_iUnion.mpr ⟨⟨q, ?_, haccepted⟩, hqstop⟩⟩
    exact ⟨hpred, ell, hraw.1, hraw.2, hineligible, htotal⟩

/-- Direct raw-path version of the exact gated/ineligible split. -/
theorem mem_positiveInterfaceGated_or_ineligible_of_raw_growth
    {t : DominoTiling} {m cutoff n : ℕ} {band : RandomClockBand}
    {threshold : ℕ → ℕ} {shell : ℕ} {s : WalkPath}
    (hm : 1 < m)
    (hphase : band.vertexPhase = false)
    (hthreshold : 0 < band.externalThreshold)
    (hcreation : ThresholdCreation s m band.oldRank n)
    (hnext : thresholdCount s n (m + 1) = 0)
    (hclock : n ≤ cutoff)
    (hvalid : s ∈ validStepWalk)
    (hfailure : s ∈ thresholdedGrowthFailure
      (tilingBandOccupancy t m cutoff band) threshold shellGrowth48 shell) :
    s ∈ positiveInterfaceGatedPhysicalScreenedEvent t band.orientation m
          band.oldRank band.externalThreshold hm band.oldRank_pos threshold
          (shellWidth48 m) shell cutoff ∪
        positiveInterfacePhysicalIneligibleUpperEvent t band.orientation m
          band.oldRank band.externalThreshold hm band.oldRank_pos threshold
          (shellWidth48 m) shell cutoff := by
  apply positiveInterfacePhysicalScreenedEvent_subset_gated_union_ineligible
  exact mem_positiveInterfacePhysicalScreenedEvent_of_raw_growth hm hphase
    hthreshold hcreation hnext hclock hvalid hfailure

end

end Erdos1165.HLOZPositiveInterfaceRawGatedPhysicalSplit
