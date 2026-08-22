/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.HLOZPositiveInterfacePairSupportFiber
import ErdosProblems.Erdos1165.HLOZPositiveInterfaceRawGatedPhysicalSplit

/-!
# Recovering the exact adjacent-pair support from stopped totals

The finite-product tail records its active coordinates as `pairSupport`.
This file identifies the corresponding canonical tiling bases with the
pathwise adjacent physical pair support.  The statement is an equality of
finite sets, not merely a cardinality comparison; this is what permits the
non-pair coordinates to remain in the distinguished stopped carrier.
-/

namespace Erdos1165.HLOZPositiveInterfacePairSupportPath

open FiniteDominoProductLaw HeterogeneousProductTail
open HLOZPositiveInterfaceAggregateRecovery
open HLOZPositiveInterfaceGatedPhysicalSplit
open HLOZPositiveInterfacePairSupportSelector
open HLOZPositiveInterfacePhysicalCoordinateRecovery
open HLOZPositiveInterfacePhysicalWindows
open HLOZPositiveInterfaceSupportSelector
open LazyDecomposition PathInsertion PreStoppingFiber StoppedInsertion
open TilingCappedMarginalization
open TilingOrientedAllCreationStoppedCoordinate
open TilingOrientedRetainedDominoEndpoint
open TilingOrientedSupportAwayCoordinates
open TilingPrefixedFavoriteTraceSupport
open TilingPrefixedInsertedLocalTime
open TilingPrefixedStoppedProductDisintegration
open TilingSpatialInsertionFiber
open VariableStoppedTracePartition

noncomputable section

abbrev DominoTiling := Tilings.Tiling

attribute [local instance] Classical.propDecidable

/-- Canonical retained bases of the random-total adjacent pair support. -/
def positiveInterfacePairSupportBases
    {t : DominoTiling} {o : Orientation} {m k externalThreshold : ℕ}
    (eta : PositiveInterfaceSupportedIndex t o m k externalThreshold)
    (width shell cap : ℕ)
    (ell : TruncatedTotals ((PositiveInterfaceFiber eta).upper cap)) :
    Finset Point :=
  (pairSupport (positiveInterfacePhysicalUpper width shell eta cap)
      (positiveInterfacePhysicalLower width shell eta cap) ell).image
    fun b ↦ b.1.1

theorem positiveInterfacePairSupportBases_subset_represented
    {t : DominoTiling} {o : Orientation} {m k externalThreshold : ℕ}
    (eta : PositiveInterfaceSupportedIndex t o m k externalThreshold)
    (width shell cap : ℕ)
    (ell : TruncatedTotals ((PositiveInterfaceFiber eta).upper cap)) :
    positiveInterfacePairSupportBases eta width shell cap ell ⊆
      tilingExternalDominoBases t eta.1.1.external.start
        eta.1.1.external.retained := by
  intro b hb
  rw [positiveInterfacePairSupportBases, Finset.mem_image] at hb
  rcases hb with ⟨c, _hc, rfl⟩
  exact c.1.2

/-- On an exact stopped vector, the product's active pair bases are exactly
the pathwise adjacent physical pair support. -/
theorem positiveInterfacePairSupportBases_eq_pathSupport
    {t : DominoTiling} {o : Orientation} {m k externalThreshold : ℕ}
    (eta : PositiveInterfaceSupportedIndex t o m k externalThreshold)
    (hm : 1 < m) (hk : 0 < k) {cap : ℕ}
    (q : TilingCappedCoordinates eta.1.1.external.retainedCount
      ((PositiveInterfaceFiber eta).coordinateCap cap))
    (ell : TruncatedTotals ((PositiveInterfaceFiber eta).upper cap))
    (htotal : ∀ b,
      tilingAwayTotal t eta.1.1.external.start eta.1.1.external.retained
        (supportComplementDistinguished t eta.1.1.external.start
          eta.1.1.external.retained eta.1.2)
        ((splitTilingCoordinatesEquiv t eta.1.1.external.start
          eta.1.1.external.retained
          (supportComplementDistinguished t eta.1.1.external.start
            eta.1.1.external.retained eta.1.2) q).2) b = ell b)
    (s : WalkPath)
    (hprefix :
      let v := prefixedTilingInsertionPrefixList
        eta.1.1.external.initial.1 t eta.1.1.external.start
        eta.1.1.external.retained (fun j ↦ (q j : ℕ))
        eta.1.1.external.tail.1
      let sq := trajectory (extendPrefix (directionVectorOfList v))
      pathPrefix s v.length = pathPrefix sq v.length)
    (hsupport :
      let v := prefixedTilingInsertionPrefixList
        eta.1.1.external.initial.1 t eta.1.1.external.start
        eta.1.1.external.retained (fun j ↦ (q j : ℕ))
        eta.1.1.external.tail.1
      orientedPositiveInterfaceSupportAt t o m externalThreshold s v.length =
        eta.1.2)
    (hbelow :
      let v := prefixedTilingInsertionPrefixList
        eta.1.1.external.initial.1 t eta.1.1.external.start
        eta.1.1.external.retained (fun j ↦ (q j : ℕ))
        eta.1.1.external.tail.1
      ∀ b : TilingAwayDomino t eta.1.1.external.start
        eta.1.1.external.retained
        (supportComplementDistinguished t eta.1.1.external.start
          eta.1.1.external.retained eta.1.2),
        localTime s v.length (orientedDominoEndpoint t o b.1.1) < m)
    (width shell : ℕ) :
    let v := prefixedTilingInsertionPrefixList eta.1.1.external.initial.1 t
      eta.1.1.external.start eta.1.1.external.retained
      (fun j ↦ (q j : ℕ)) eta.1.1.external.tail.1
    positiveInterfacePairSupportBases eta width shell cap ell =
      orientedPositiveInterfacePairSupportAt t o m externalThreshold width
        shell s v.length := by
  classical
  dsimp only
  let D := supportComplementDistinguished t eta.1.1.external.start
    eta.1.1.external.retained eta.1.2
  let v := prefixedTilingInsertionPrefixList eta.1.1.external.initial.1 t
    eta.1.1.external.start eta.1.1.external.retained
      (fun j ↦ (q j : ℕ)) eta.1.1.external.tail.1
  ext b
  constructor
  · intro hb
    rw [positiveInterfacePairSupportBases, Finset.mem_image] at hb
    rcases hb with ⟨c, hc, rfl⟩
    simp only [pairSupport, Finset.mem_filter, Finset.mem_univ, true_and] at hc
    rw [orientedPositiveInterfacePairSupportAt, Finset.mem_filter]
    refine ⟨?_, ?_⟩
    · rw [hsupport]
      exact (away_mem_support_iff t eta.1.1.external.start
        eta.1.1.external.retained eta.1.2 c.1).1 c.2
    · rcases hc with hcUpper | hcLower
      · right
        apply (positiveInterface_awayTotal_mem_physicalWindow_iff
          eta hm hk q c s hprefix (hbelow c) width (shell + 1)).mp
        rw [htotal c]
        exact hcUpper
      · left
        apply (positiveInterface_awayTotal_mem_physicalWindow_iff
          eta hm hk q c s hprefix (hbelow c) width shell).mp
        rw [htotal c]
        exact hcLower
  · intro hb
    rw [orientedPositiveInterfacePairSupportAt, Finset.mem_filter] at hb
    have hbS : b ∈ eta.1.2 := by
      rw [← hsupport]
      exact hb.1
    let c := supportAwayChosen t eta.1.1.external.start
      eta.1.1.external.retained eta.1.2
      (PositiveInterfaceFiber eta).support_represented b hbS
    have hcbase : c.1.1 = b :=
      supportAwayChosen_base t eta.1.1.external.start
        eta.1.1.external.retained eta.1.2
        (PositiveInterfaceFiber eta).support_represented b hbS
    rw [positiveInterfacePairSupportBases, Finset.mem_image]
    refine ⟨c, ?_, ?_⟩
    · unfold pairSupport
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      rcases hb.2 with hbLower | hbUpper
      · apply Or.inr
        unfold positiveInterfacePhysicalLower
        rw [← htotal c]
        apply (positiveInterface_awayTotal_mem_physicalWindow_iff
          eta hm hk q c s hprefix (hbelow c) width shell).mpr
        simpa only [hcbase] using hbLower
      · apply Or.inl
        unfold positiveInterfacePhysicalUpper
        rw [← htotal c]
        apply (positiveInterface_awayTotal_mem_physicalWindow_iff
          eta hm hk q c s hprefix (hbelow c) width (shell + 1)).mpr
        simpa only [hcbase] using hbUpper
    · exact supportAwayChosen_base t eta.1.1.external.start
        eta.1.1.external.retained eta.1.2
        (PositiveInterfaceFiber eta).support_represented b hbS

end

end Erdos1165.HLOZPositiveInterfacePairSupportPath
