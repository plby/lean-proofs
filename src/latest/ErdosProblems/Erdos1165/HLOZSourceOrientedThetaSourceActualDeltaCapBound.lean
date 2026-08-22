/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.HLOZSourceOrientedThetaSourceActualDeltaProduct
import ErdosProblems.Erdos1165.TilingOrientedExternalStaticDStoppedCoordinate

/-!
# Cap-level source-Theta bound by honest actual-rank fibres

For one retained source slot and one coordinate cap, the strengthened
source-Theta stopped fibre is bounded by the checked one-coordinate cost
times the finite sum of the honest actual endpoint-increment fibres.  This
file performs only the stopped-product disintegration.  Cofinal cap removal
and the disjoint countable history sum are kept in a separate layer.
-/

open MeasureTheory Set
open scoped ENNReal

namespace Erdos1165.HLOZSourceOrientedThetaSourceActualDeltaCapBound

open HLOZSourceOrientedThetaExternalProduct
open HLOZSourceOrientedThetaExternalAccepted
open HLOZSourceOrientedThetaExternalSourceAccepted
open HLOZSourceOrientedThetaAcceptedCreationPath
open HLOZSourceOrientedThetaSourceActualDeltaProduct
open HLOZSourceOrientedThetaSourceSelectedCarrier
open HLOZSourceOrientedThetaSourceSingletonAccepted
open HLOZPathEvents LazyDecomposition PathInsertion PreStoppingFiber
open SpatialInsertionFiber StoppedInsertion TilingCappedMarginalization
open TilingLazyDecomposition
open TilingDistinguishedTraceInvariant
open TilingOrientedAllCreationConcreteFamily
open TilingOrientedExternalAllCreationStoppedCoordinate
open TilingOrientedExternalStaticDStoppedCoordinate
open TilingOrientedAllRepresentedExternalFiber
open TilingOrientedShellZeroSourcePartition
open TilingOrientedSupportAwayCoordinates
open TilingPrefixedStoppedProductDisintegration
open TilingShellZeroSourcePartition
open TilingSpatialInsertionFiber
open TilingVariableStoppedTracePartition
open VariableStoppedTracePartition

noncomputable section

abbrev DominoTiling := Tilings.Tiling

/-- The source-window bad stopped fibre at one cap. -/
def sourceThetaCap
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    {supportAt : WalkPath → ℕ → Finset Point}
    (supportData : OrientedAllCreationSupportSelectorData t o m k supportAt)
    (eta : SupportedIndex t o m k supportAt)
    (cap w externalLow externalHigh : ℕ) : Set WalkPath :=
  let data := concreteFiber o m k supportAt supportData eta
  let sourceData := withExternalSourceSelected data w externalLow externalHigh
  walkLift (prefixedTilingPreStoppingFiberEvent
    (sourceData.stoppingTime cap) eta.1.1.initial.1 t eta.1.1.start
    eta.1.1.retained (sourceData.coordinateCap cap) eta.1.1.tail.1
    (externalAcceptedSourceThetaPredicate sourceData w externalLow
      externalHigh cap))

/-- One honest actual-endpoint-increment stopped fibre at the same cap. -/
def sourceActualDeltaCap
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    {supportAt : WalkPath → ℕ → Finset Point}
    (supportData : OrientedAllCreationSupportSelectorData t o m k supportAt)
    (eta : SupportedIndex t o m k supportAt)
    (cap w externalLow externalHigh : ℕ)
    (delta : SourceActualDeltaIndex
      (concreteFiber o m k supportAt supportData eta)) : Set WalkPath :=
  let data := concreteFiber o m k supportAt supportData eta
  walkLift (prefixedTilingPreStoppingFiberEvent
    (sourceActualDeltaStoppingTime data cap delta)
    eta.1.1.initial.1 t eta.1.1.start eta.1.1.retained
    (data.coordinateCap cap) eta.1.1.tail.1
    (sourceActualDeltaPredicate data w externalLow externalHigh cap delta))

theorem measurableSet_sourceThetaCap
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    {supportAt : WalkPath → ℕ → Finset Point}
    (supportData : OrientedAllCreationSupportSelectorData t o m k supportAt)
    (eta : SupportedIndex t o m k supportAt)
    (cap w externalLow externalHigh : ℕ) :
    MeasurableSet (sourceThetaCap supportData eta cap w externalLow
      externalHigh) := by
  apply measurableSet_walkLift
  exact measurableSet_prefixedTilingPreStoppingFiberEvent
    ((withExternalSourceSelected
      (concreteFiber o m k supportAt supportData eta)
        w externalLow externalHigh).isStoppingTime cap)
    eta.1.1.initial.1 t eta.1.1.start eta.1.1.retained
    ((withExternalSourceSelected
      (concreteFiber o m k supportAt supportData eta)
        w externalLow externalHigh).coordinateCap cap)
    eta.1.1.tail.1
    (externalAcceptedSourceThetaPredicate
      (withExternalSourceSelected
        (concreteFiber o m k supportAt supportData eta)
          w externalLow externalHigh)
      w externalLow externalHigh cap)

theorem measurableSet_sourceActualDeltaCap
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    {supportAt : WalkPath → ℕ → Finset Point}
    (supportData : OrientedAllCreationSupportSelectorData t o m k supportAt)
    (eta : SupportedIndex t o m k supportAt)
    (cap w externalLow externalHigh : ℕ)
    (delta : SourceActualDeltaIndex
      (concreteFiber o m k supportAt supportData eta)) :
    MeasurableSet (sourceActualDeltaCap supportData eta cap w externalLow
      externalHigh delta) := by
  apply measurableSet_walkLift
  exact measurableSet_prefixedTilingPreStoppingFiberEvent
    (isFiniteStoppingTime_truncatedLevelTime m
      (k + (delta : ℕ))
      (externalCoordinateCutoff eta.1.1
        ((concreteFiber o m k supportAt supportData eta).coordinateCap cap)))
    eta.1.1.initial.1 t eta.1.1.start eta.1.1.retained
    ((concreteFiber o m k supportAt supportData eta).coordinateCap cap)
    eta.1.1.tail.1
    (sourceActualDeltaPredicate
      (concreteFiber o m k supportAt supportData eta)
      w externalLow externalHigh cap delta)

/-- Every actual-delta cap piece is carried by the complete external-word
creation atom at its honest raised rank. -/
theorem sourceActualDeltaCap_subset_externalOnlyCreationTraceAtom
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    {supportAt : WalkPath → ℕ → Finset Point}
    (supportData : OrientedAllCreationSupportSelectorData t o m k supportAt)
    (eta : SupportedIndex t o m k supportAt)
    (hm : 1 < m) (hk : 0 < k)
    (cap w externalLow externalHigh : ℕ)
    (delta : SourceActualDeltaIndex
      (concreteFiber o m k supportAt supportData eta)) :
    sourceActualDeltaCap supportData eta cap w externalLow externalHigh delta ⊆
      orientedExternalOnlyCreationTraceAtom t o m (k + (delta : ℕ)) eta.1.1 := by
  classical
  intro s hs
  rcases hs with ⟨hvalid, hs⟩
  rcases Set.mem_iUnion.mp hs with ⟨q, hq⟩
  let data := concreteFiber o m k supportAt supportData eta
  let v := prefixedTilingInsertionPrefixList eta.1.1.initial.1 t
    eta.1.1.start eta.1.1.retained (fun j ↦ (q.1 j : ℕ)) eta.1.1.tail.1
  let sq := trajectory (extendPrefix (directionVectorOfList v))
  have hlt : v.length <
      externalCoordinateCutoff eta.1.1 (data.coordinateCap cap) := by
    let dummy : TilingCreationFavoriteData :=
      ((∅, ∅), (eta.1.1.start, eta.1.1.start))
    have hraw := prefixedInsertion_lt_orientedAllCreationCoordinateCutoff
      (withFavorite eta.1.1 dummy) (data.coordinateCap cap) q.1
    rw [orientedAllCreationCoordinateCutoff_withFavorite] at hraw
    exact hraw
  have hcreationQ : ThresholdCreation sq m (k + (delta : ℕ)) v.length := by
    apply (truncatedLevelTime_eq_iff_thresholdCreation_of_lt_cutoff
      m (k + (delta : ℕ))
      (externalCoordinateCutoff eta.1.1 (data.coordinateCap cap))
      v.length _ hlt).mp
    exact q.2.2
  have hp : pathPrefix s v.length = pathPrefix sq v.length := by
    have hp' := pathPrefix_eq_canonical_of_mem_prefixedTilingStoppedInsertionAtom
      eta.1.1.initial.1 eta.1.1.start eta.1.1.retained
      (fun j ↦ (q.1 j : ℕ)) eta.1.1.tail.1 (stepsOfWalk s) hq
    change trajectory (stepsOfWalk s) = s at hvalid
    rw [hvalid] at hp'
    simpa only [sq, v] using hp'
  have hcreationS : ThresholdCreation s m (k + (delta : ℕ)) v.length :=
    (thresholdCreation_iff_of_pathPrefix_eq hp
      (Nat.le_refl v.length)).mpr hcreationQ
  have htime : creationTimeNat m (k + (delta : ℕ)) s = v.length :=
    creationTimeNat_eq_of_creation hcreationS
  have heta_nonempty :
      (allRepresentedExternalCreationTraceAtom t o m k eta.1.1).Nonempty := by
    rcases eta.2 with ⟨s₀, hs₀⟩
    rw [orientedExternalAllCreationSupportTraceAtom_eq] at hs₀
    exact ⟨s₀, hs₀.1, hs₀.2.1, hs₀.2.2.1⟩
  let etaAll : TilingOrientedAllRepresentedExternalFiber.SupportedIndex
      t o m k := ⟨eta.1.1, heta_nonempty⟩
  have hcodeQ : fixedOrientedTypedExternalWordCode t o v.length sq =
      eta.1.1 := by
    simpa only [etaAll, sq, v] using
      (fixedCode_prefixedInsertion etaAll hm hk (fun j ↦ (q.1 j : ℕ)))
  have hcodeS : fixedOrientedTypedExternalWordCode t o v.length s =
      eta.1.1 := by
    exact (fixedOrientedTypedExternalWordCode_eq_of_pathPrefix_eq
      t o hp).trans hcodeQ
  refine ⟨?_, ⟨v.length, hcreationS.1⟩, ?_⟩
  · exact hvalid
  · rw [htime]
    exact hcodeS

/-- For a retained-word-defined support selector, the external code already
determines the complete supported index. -/
theorem supportedIndex_eq_of_externalCode_eq
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    {supportAt : WalkPath → ℕ → Finset Point}
    (supportOfCode : OrientedTilingTypedExternalWordCode t → Finset Point)
    (support_code : ∀ s n, supportAt s n = supportOfCode
      (fixedOrientedTypedExternalWordCode t o n s))
    {eta eta' : SupportedIndex t o m k supportAt}
    (hcode : eta.1.1 = eta'.1.1) : eta = eta' := by
  apply Subtype.ext
  apply Prod.ext
  · exact hcode
  · rcases eta.2 with ⟨s, hs⟩
    rcases eta'.2 with ⟨s', hs'⟩
    rw [orientedExternalAllCreationSupportTraceAtom_eq] at hs hs'
    calc
      eta.1.2 = supportAt s (creationTimeNat m k s) := hs.2.2.2.symm
      _ = supportOfCode eta.1.1 := by rw [support_code, hs.2.2.1]
      _ = supportOfCode eta'.1.1 := by rw [hcode]
      _ = supportAt s' (creationTimeNat m k s') := by
        rw [support_code, hs'.2.2.1]
      _ = eta'.1.2 := hs'.2.2.2

/-- At any fixed raised rank, the coarse external atoms belonging to the
supported histories of one retained-word slot are pairwise disjoint. -/
theorem pairwise_disjoint_externalOnlyCreationTraceAtom
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    {supportAt : WalkPath → ℕ → Finset Point}
    (supportOfCode : OrientedTilingTypedExternalWordCode t → Finset Point)
    (support_code : ∀ s n, supportAt s n = supportOfCode
      (fixedOrientedTypedExternalWordCode t o n s))
    (rank : ℕ) :
    Pairwise fun eta eta' : SupportedIndex t o m k supportAt ↦
      Disjoint
        (orientedExternalOnlyCreationTraceAtom t o m rank eta.1.1)
        (orientedExternalOnlyCreationTraceAtom t o m rank eta'.1.1) := by
  intro eta eta' hne
  rw [Set.disjoint_left]
  intro s hs hs'
  apply hne
  apply supportedIndex_eq_of_externalCode_eq supportOfCode support_code
  exact hs.2.2.symm.trans hs'.2.2

/-- A singleton source slot has one away domino, hence exactly the three
possible endpoint increments `0,1,2`. -/
noncomputable def sourceActualDeltaIndexEquivFinThree
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    {supportAt : WalkPath → ℕ → Finset Point}
    (supportData : OrientedAllCreationSupportSelectorData t o m k supportAt)
    (eta : SupportedIndex t o m k supportAt)
    (b : Point) (hS : eta.1.2 = {b})
    (hb : b ∈ tilingExternalDominoBases t eta.1.1.start eta.1.1.retained) :
    SourceActualDeltaIndex
        (concreteFiber o m k supportAt supportData eta) ≃ Fin 3 := by
  classical
  letI : Fintype
      (TilingAwayDomino t eta.1.1.start eta.1.1.retained
        (supportComplementDistinguished t eta.1.1.start eta.1.1.retained
          eta.1.2)) :=
    instFintypeTilingAwayDomino t eta.1.1.start eta.1.1.retained
      (supportComplementDistinguished t eta.1.1.start eta.1.1.retained
        eta.1.2)
  have hcard : Fintype.card
      (TilingAwayDomino t eta.1.1.start eta.1.1.retained
        (supportComplementDistinguished t eta.1.1.start eta.1.1.retained
          eta.1.2)) = 1 := by
    rw [Fintype.card_eq_one_iff]
    let chosen : TilingAwayDomino t eta.1.1.start eta.1.1.retained
        (supportComplementDistinguished t eta.1.1.start eta.1.1.retained
          eta.1.2) := ⟨⟨b, hb⟩, by
            apply (away_mem_support_iff t eta.1.1.start
              eta.1.1.retained eta.1.2 ⟨b, hb⟩).2
            rw [hS]
            simp⟩
    exact ⟨chosen, fun c ↦ away_eq_of_singleton_support hS c chosen⟩
  let hsize : 2 * (Fintype.card
      (TilingAwayDomino t eta.1.1.start eta.1.1.retained
        (supportComplementDistinguished t eta.1.1.start eta.1.1.retained
          eta.1.2)) - 0) + 1 = 3 := by rw [hcard]
  exact finCongr hsize

@[simp] theorem sourceActualDeltaIndexEquivFinThree_apply_val
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    {supportAt : WalkPath → ℕ → Finset Point}
    (supportData : OrientedAllCreationSupportSelectorData t o m k supportAt)
    (eta : SupportedIndex t o m k supportAt)
    (b : Point) (hS : eta.1.2 = {b})
    (hb : b ∈ tilingExternalDominoBases t eta.1.1.start eta.1.1.retained)
    (delta : SourceActualDeltaIndex
      (concreteFiber o m k supportAt supportData eta)) :
    ((sourceActualDeltaIndexEquivFinThree supportData eta b hS hb delta :
      Fin 3) : ℕ) = (delta : ℕ) := by
  classical
  unfold sourceActualDeltaIndexEquivFinThree
  exact finCongr_apply_coe _ delta

@[simp] theorem sourceActualDeltaIndexEquivFinThree_symm_val
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    {supportAt : WalkPath → ℕ → Finset Point}
    (supportData : OrientedAllCreationSupportSelectorData t o m k supportAt)
    (eta : SupportedIndex t o m k supportAt)
    (b : Point) (hS : eta.1.2 = {b})
    (hb : b ∈ tilingExternalDominoBases t eta.1.1.start eta.1.1.retained)
    (delta : Fin 3) :
    (((sourceActualDeltaIndexEquivFinThree supportData eta b hS hb).symm
      delta : SourceActualDeltaIndex
        (concreteFiber o m k supportAt supportData eta)) : ℕ) =
      (delta : ℕ) := by
  let e := sourceActualDeltaIndexEquivFinThree supportData eta b hS hb
  have h := sourceActualDeltaIndexEquivFinThree_apply_val
    supportData eta b hS hb (e.symm delta)
  simpa only [e, Equiv.apply_symm_apply] using h.symm

/-- Literal stopped-product form of the actual-delta comparison.  The
coefficient is the checked finite-coordinate source-Theta cost, not an event
probability premise. -/
theorem simpleRandomWalk_sourceThetaCap_le_actualDelta_sum
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    {supportAt : WalkPath → ℕ → Finset Point}
    (supportData : OrientedAllCreationSupportSelectorData t o m k supportAt)
    (eta : SupportedIndex t o m k supportAt)
    (hm : 1 < m) (hk : 0 < k)
    (hfixedPos : 0 < eta.1.1.initial.1.length +
      2 * eta.1.1.retainedCount + eta.1.1.tail.1.length)
    (cap w externalLow externalHigh : ℕ)
    (arith : ExternalThetaProductArithmetic
      (withExternalSourceSelected
        (concreteFiber o m k supportAt supportData eta)
          w externalLow externalHigh)
      w externalLow externalHigh cap)
    (b : Point) (hS : eta.1.2 = {b})
    (hb : b ∈ tilingExternalDominoBases t eta.1.1.start eta.1.1.retained)
    (hcompat : OrientationCompatible o b)
    (q₀ : TilingCappedCoordinates eta.1.1.retainedCount
      ((concreteFiber o m k supportAt supportData eta).coordinateCap cap))
    (window : Finset ℕ)
    (hVTwo :
      let v := prefixedTilingInsertionPrefixList eta.1.1.initial.1 t
        eta.1.1.start eta.1.1.retained (fun j ↦ (q₀ j : ℕ))
          eta.1.1.tail.1
      let s := trajectory (extendPrefix (directionVectorOfList v))
      tilingVTwoAt t window s v.length b) :
    simpleRandomWalk
        (sourceThetaCap supportData eta cap w externalLow externalHigh) ≤
      ENNReal.ofReal
          (2 * ∑ c, externalThetaCost
            (withExternalSourceSelected
              (concreteFiber o m k supportAt supportData eta)
                w externalLow externalHigh)
            cap c) *
        ∑' delta, simpleRandomWalk
          (sourceActualDeltaCap supportData eta cap w externalLow
            externalHigh delta) := by
  let data := concreteFiber o m k supportAt supportData eta
  let sourceData := withExternalSourceSelected data w externalLow externalHigh
  have hcommon : 0 ≤ prefixedPrefixFiberConstant eta.1.1.initial.1
      eta.1.1.retainedCount eta.1.1.tail.1 :=
    prefixedPrefixFiberConstant_nonneg _ _ _
  have hcost : 0 ≤ 2 * ∑ c, externalThetaCost sourceData cap c := by
    apply mul_nonneg
    · norm_num
    · apply Finset.sum_nonneg
      intro c _hc
      unfold externalThetaCost
      unfold HLOZSourceOrientedThetaProduct.thetaCoordinateCost
      split <;> positivity
  have hsourceMeasure : simpleRandomWalk
      (sourceThetaCap supportData eta cap w externalLow externalHigh) =
      ENNReal.ofReal (prefixedPrefixFiberConstant eta.1.1.initial.1
          eta.1.1.retainedCount eta.1.1.tail.1 *
        prefixedTilingStoppedAcceptedGeometricMass
          (sourceData.stoppingTime cap) eta.1.1.initial.1 t eta.1.1.start
          eta.1.1.retained (sourceData.coordinateCap cap) eta.1.1.tail.1
          (externalAcceptedSourceThetaPredicate sourceData w externalLow
            externalHigh cap)) := by
    unfold sourceThetaCap
    dsimp only
    simp only [OrientedTilingTypedExternalWordCode.start]
    exact simpleRandomWalk_walkLift_prefixedTilingPreStoppingFiberEvent
      (sourceData.isStoppingTime cap) _ _ _ _ _ _ _
  have hrankMeasure (delta : SourceActualDeltaIndex data) :
      simpleRandomWalk
          (sourceActualDeltaCap supportData eta cap w externalLow
            externalHigh delta) =
        ENNReal.ofReal (prefixedPrefixFiberConstant eta.1.1.initial.1
            eta.1.1.retainedCount eta.1.1.tail.1 *
          prefixedTilingStoppedAcceptedGeometricMass
            (sourceActualDeltaStoppingTime data cap delta)
            eta.1.1.initial.1 t eta.1.1.start eta.1.1.retained
            (data.coordinateCap cap) eta.1.1.tail.1
            (sourceActualDeltaPredicate data w externalLow externalHigh
              cap delta)) := by
    unfold sourceActualDeltaCap
    dsimp only
    simp only [OrientedTilingTypedExternalWordCode.start]
    exact simpleRandomWalk_walkLift_prefixedTilingPreStoppingFiberEvent
      (isFiniteStoppingTime_truncatedLevelTime m (k + (delta : ℕ))
        (externalCoordinateCutoff eta.1.1 (data.coordinateCap cap)))
      _ _ _ _ _ _ _
  rw [hsourceMeasure]
  simp_rw [hrankMeasure]
  simp_rw [ENNReal.ofReal_mul hcommon]
  rw [ENNReal.tsum_mul_left]
  calc
    ENNReal.ofReal (prefixedPrefixFiberConstant eta.1.1.initial.1
          eta.1.1.retainedCount eta.1.1.tail.1) *
        ENNReal.ofReal (prefixedTilingStoppedAcceptedGeometricMass
          (sourceData.stoppingTime cap) eta.1.1.initial.1 t eta.1.1.start
          eta.1.1.retained (sourceData.coordinateCap cap) eta.1.1.tail.1
          (externalAcceptedSourceThetaPredicate sourceData w externalLow
            externalHigh cap)) ≤
      ENNReal.ofReal (prefixedPrefixFiberConstant eta.1.1.initial.1
          eta.1.1.retainedCount eta.1.1.tail.1) *
        ENNReal.ofReal
          ((2 * ∑ c, externalThetaCost sourceData cap c) *
            externalAcceptedThetaCarrier sourceData cap) := by
      apply mul_le_mul_of_nonneg_left
      · apply ENNReal.ofReal_le_ofReal
        exact externalSourceSelectedStoppedGeometricMass_le data w externalLow
          externalHigh cap arith
      · exact bot_le
    _ = ENNReal.ofReal (2 * ∑ c, externalThetaCost sourceData cap c) *
        (ENNReal.ofReal (prefixedPrefixFiberConstant eta.1.1.initial.1
            eta.1.1.retainedCount eta.1.1.tail.1) *
          ENNReal.ofReal (externalAcceptedThetaCarrier sourceData cap)) := by
      rw [ENNReal.ofReal_mul hcost]
      ac_rfl
    _ = ENNReal.ofReal (2 * ∑ c, externalThetaCost sourceData cap c) *
        (∑' delta : SourceActualDeltaIndex data,
          ENNReal.ofReal (prefixedPrefixFiberConstant eta.1.1.initial.1
              eta.1.1.retainedCount eta.1.1.tail.1) *
            ENNReal.ofReal (prefixedTilingStoppedAcceptedGeometricMass
              (sourceActualDeltaStoppingTime data cap delta)
              eta.1.1.initial.1 t eta.1.1.start eta.1.1.retained
              (data.coordinateCap cap) eta.1.1.tail.1
              (sourceActualDeltaPredicate data w externalLow externalHigh
                cap delta))) := by
      congr 1
      rw [ENNReal.tsum_mul_left]
      congr 1
      rw [tsum_fintype]
      rw [← ENNReal.ofReal_sum_of_nonneg]
      · congr 1
        exact (sum_sourceActualDeltaStoppedGeometricMass_eq_carrier
          supportData eta hm hk hfixedPos cap w externalLow externalHigh b hS
          hb hcompat q₀ window hVTwo).symm
      · intro delta _hdelta
        exact prefixedTilingStoppedAcceptedGeometricMass_nonneg
          (sourceActualDeltaStoppingTime data cap delta)
          eta.1.1.initial.1 t eta.1.1.start eta.1.1.retained
          (data.coordinateCap cap) eta.1.1.tail.1
          (sourceActualDeltaPredicate data w externalLow externalHigh cap delta)
    _ = _ := by
      rw [ENNReal.tsum_mul_left]

end

end Erdos1165.HLOZSourceOrientedThetaSourceActualDeltaCapBound
