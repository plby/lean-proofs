import ErdosProblems.Erdos1165.TilingTraceCappedStageAdapter
import ErdosProblems.Erdos1165.HLOZLazyOverflowClosure

/-!
# Capped tiling traces on the canonical walk support

Every stopped insertion cylinder lies in `validStepWalk`.  Accordingly, the
coordinate product certificate partitions only the valid part of each HLOZ
stage.  The omitted complement is null for simple random walk.  This avoids
the unsound requirement that a stopped insertion cylinder cover the `none`
trace code, whose piece consists precisely of noncanonical paths.
-/

open MeasureTheory Set
open scoped ENNReal NNReal

namespace Erdos1165.TilingValidTraceCappedStageAdapter

open HLOZPathEvents HLOZLazyOverflowClosure
open HLOZStoppedProductRefinement HLOZTraceCappedProductScreening
open HLOZStoppedSpatialScreening HLOZTracePartitionAdapter
open CappedCoordinateMassCertificate TilingStoppedProductDisintegration
open TilingVariableStoppedTracePartition VariableStoppedTracePartition

noncomputable section

abbrev DominoTiling := Tilings.Tiling

/-- Non-null favorite trace codes. -/
abbrev ValidFavoriteTilingTraceCode (t : DominoTiling) :=
  TilingExternalWordCode t × TilingCreationFavoriteData

/-- The non-null trace piece, restricted to an arbitrary transition stage. -/
def validFavoriteTilingStagePiece (t : DominoTiling) (m k : ℕ)
    (stage : Set WalkPath) (z : ValidFavoriteTilingTraceCode t) : Set WalkPath :=
  favoriteTilingStagePiece t m k stage (some z)

theorem measurableSet_validFavoriteTilingStagePiece (t : DominoTiling)
    (m k : ℕ) {stage : Set WalkPath} (hstage : MeasurableSet stage)
    (z : ValidFavoriteTilingTraceCode t) :
    MeasurableSet (validFavoriteTilingStagePiece t m k stage z) :=
  measurableSet_favoriteTilingStagePiece t m k hstage (some z)

theorem disjoint_validFavoriteTilingStagePiece_of_ne (t : DominoTiling)
    (m k : ℕ) (stage : Set WalkPath)
    {z w : ValidFavoriteTilingTraceCode t} (hzw : z ≠ w) :
    Disjoint (validFavoriteTilingStagePiece t m k stage z)
      (validFavoriteTilingStagePiece t m k stage w) := by
  exact disjoint_favoriteTilingStagePiece_of_ne t m k stage
    (fun h ↦ hzw (Option.some.inj h))

/-- Non-null codes partition exactly the canonical support of a reaching
stage. -/
theorem iUnion_validFavoriteTilingStagePiece (t : DominoTiling) (m k : ℕ)
    {stage : Set WalkPath} (hstage : stage ⊆ thresholdReachStage m k) :
    (⋃ z : ValidFavoriteTilingTraceCode t,
        validFavoriteTilingStagePiece t m k stage z) =
      stage ∩ validStepWalk := by
  classical
  ext s
  simp only [Set.mem_iUnion]
  constructor
  · rintro ⟨z, hz⟩
    change s ∈ favoriteTilingCreationPiece t m k (some z) ∩ stage at hz
    change s ∈ stage ∩ validStepWalk
    exact ⟨hz.2, hz.1.1.1.2⟩
  · rintro ⟨hs, hvalid⟩
    refine ⟨(tilingCreationExternalCode t m k s,
      tilingCreationFavoriteData t m k s), ?_⟩
    change s ∈ favoriteTilingCreationPiece t m k
      (some (tilingCreationExternalCode t m k s,
        tilingCreationFavoriteData t m k s)) ∩ stage
    exact ⟨⟨⟨⟨hstage hs, hvalid⟩, rfl⟩, rfl⟩, hs⟩

/-- Removing the noncanonical complement does not change simple-random-walk
mass. -/
theorem simpleRandomWalk_inter_validStepWalk (A : Set WalkPath)
    (hA : MeasurableSet A) :
    simpleRandomWalk (A ∩ validStepWalk) = simpleRandomWalk A := by
  have hnull : simpleRandomWalk (A \ validStepWalk) = 0 :=
    measure_mono_null (fun _ h ↦ h.2)
      simpleRandomWalk_validStepWalk_compl
  have hdisjoint : Disjoint (A ∩ validStepWalk) (A \ validStepWalk) := by
    exact Set.disjoint_left.2 fun _ hvalid hinvalid ↦ hinvalid.2 hvalid.2
  have hunion : (A ∩ validStepWalk) ∪ (A \ validStepWalk) = A := by
    ext s
    by_cases hv : s ∈ validStepWalk <;> simp [hv]
  calc
    simpleRandomWalk (A ∩ validStepWalk) =
        simpleRandomWalk ((A ∩ validStepWalk) ∪ (A \ validStepWalk)) := by
      rw [measure_union hdisjoint (hA.diff measurableSet_validStepWalk),
        hnull, add_zero]
    _ = simpleRandomWalk A := congrArg simpleRandomWalk hunion

/-- Build the exact capped trace screen on canonical paths.  Both the stage
and transition are intersected with `validStepWalk`; the coordinate system
therefore has no spurious `none` index. -/
def someValidFavoriteTilingTraceCappedScreenOfStoppedCoordinateSpec
    (t : DominoTiling) (m k : ℕ) (stage next : Set WalkPath)
    (cost : ℝ≥0∞) (hstageMeasurable : MeasurableSet stage)
    (hstage : stage ⊆ thresholdReachStage m k) (hnext : next ⊆ stage)
    (spec : TilingStoppedCoordinateProductSpec
      (validFavoriteTilingStagePiece t m k stage)
      (next ∩ validStepWalk) cost) :
    SomeTraceCappedProductScreening (stage ∩ validStepWalk)
      (next ∩ validStepWalk) cost := by
  exact someTraceCappedProductScreeningOfCoordinateMassSpec
    (stage ∩ validStepWalk) (next ∩ validStepWalk) cost
    (validFavoriteTilingStagePiece t m k stage)
    (measurableSet_validFavoriteTilingStagePiece t m k hstageMeasurable)
    (fun _ _ h ↦ disjoint_validFavoriteTilingStagePiece_of_ne
      t m k stage h)
    (iUnion_validFavoriteTilingStagePiece t m k hstage)
    (fun _ hs ↦ ⟨hnext hs.1, hs.2⟩)
    (coordinateMassSpecOfTilingStoppedCoordinateProductSpec spec)

/-- A valid-support capped coordinate law implies the original transition
inequality.  The only discarded paths belong to the explicitly proved null
complement of `validStepWalk`. -/
theorem transition_measure_le_of_validFavoriteTilingStoppedCoordinateSpec
    (t : DominoTiling) (m k : ℕ) (stage next : Set WalkPath)
    (cost : ℝ≥0∞) (hstageMeasurable : MeasurableSet stage)
    (hnextMeasurable : MeasurableSet next)
    (hstage : stage ⊆ thresholdReachStage m k) (hnext : next ⊆ stage)
    (hcost : cost ≠ ∞)
    (spec : TilingStoppedCoordinateProductSpec
      (validFavoriteTilingStagePiece t m k stage)
      (next ∩ validStepWalk) cost) :
    simpleRandomWalk next ≤ cost * simpleRandomWalk stage := by
  let cert := someValidFavoriteTilingTraceCappedScreenOfStoppedCoordinateSpec
    t m k stage next cost hstageMeasurable hstage hnext spec
  have hvalidBound : simpleRandomWalk (next ∩ validStepWalk) ≤
      cost * simpleRandomWalk (stage ∩ validStepWalk) :=
    @transition_measure_le_of_traceCappedProductScreening cert.Index
      cert.countableIndex (stage ∩ validStepWalk) (next ∩ validStepWalk)
      (hnextMeasurable.inter measurableSet_validStepWalk) cost hcost
      cert.screening
  rw [← simpleRandomWalk_inter_validStepWalk next hnextMeasurable]
  exact hvalidBound.trans (by
    simpa only [mul_comm] using
      (mul_le_mul_left (measure_mono inter_subset_left) cost))

/-- The three transition specifications, all formulated only on canonical
walk support. -/
structure ThreeValidTransitionStoppedCoordinateSpecs
    (K : ℝ≥0) (t : DominoTiling) (m : ℕ)
    (a : (GapScale × GapScale) × GapScale) where
  first : TilingStoppedCoordinateProductSpec
    (validFavoriteTilingStagePiece t m 1 (firstCreationStage m))
    (firstTransitionEvent t m a ∩ validStepWalk)
    (UpperCanonical.hlozTransitionCost K m)
  second : TilingStoppedCoordinateProductSpec
    (validFavoriteTilingStagePiece t m 2 (firstTransitionEvent t m a))
    (secondTransitionEvent t m a ∩ validStepWalk)
    (UpperCanonical.hlozTransitionCost K m)
  third : TilingStoppedCoordinateProductSpec
    (validFavoriteTilingStagePiece t m 3 (secondTransitionEvent t m a))
    (screenedThirdTransitionEvent t m a ∩ validStepWalk)
    (UpperCanonical.hlozTransitionCost K m)

theorem firstTransition_measure_le_of_validStoppedSpecs
    (K : ℝ≥0) (t : DominoTiling) (m : ℕ)
    (a : (GapScale × GapScale) × GapScale)
    (specs : ThreeValidTransitionStoppedCoordinateSpecs K t m a) :
    simpleRandomWalk (firstTransitionEvent t m a) ≤
      UpperCanonical.hlozTransitionCost K m := by
  have hstageMeasurable : MeasurableSet (firstCreationStage m) := by
    rw [← thresholdReachStage_one_eq_firstCreationStage]
    exact measurableSet_thresholdReachStage m 1
  have hstage : firstCreationStage m ⊆ thresholdReachStage m 1 := by
    rw [thresholdReachStage_one_eq_firstCreationStage]
  have hnext : firstTransitionEvent t m a ⊆ firstCreationStage m := by
    rw [← thresholdReachStage_one_eq_firstCreationStage]
    exact firstTransitionEvent_subset_thresholdReachStage_one t m a
  have hbound :=
    transition_measure_le_of_validFavoriteTilingStoppedCoordinateSpec
      t m 1 (firstCreationStage m) (firstTransitionEvent t m a)
      (UpperCanonical.hlozTransitionCost K m) hstageMeasurable
      (measurableSet_firstTransitionEvent t m a) hstage hnext
      (hlozTransitionCost_ne_top K m) specs.first
  have hstageMass : simpleRandomWalk (firstCreationStage m) ≤ 1 := by
    simpa using measure_mono (μ := simpleRandomWalk)
      (subset_univ (firstCreationStage m))
  exact hbound.trans (by
    simpa only [mul_one, one_mul, mul_comm] using
      (mul_le_mul_left hstageMass (UpperCanonical.hlozTransitionCost K m)))

theorem secondTransition_measure_le_of_validStoppedSpecs
    (K : ℝ≥0) (t : DominoTiling) (m : ℕ)
    (a : (GapScale × GapScale) × GapScale)
    (specs : ThreeValidTransitionStoppedCoordinateSpecs K t m a) :
    simpleRandomWalk (secondTransitionEvent t m a) ≤
      UpperCanonical.hlozTransitionCost K m *
        simpleRandomWalk (firstTransitionEvent t m a) :=
  transition_measure_le_of_validFavoriteTilingStoppedCoordinateSpec
    t m 2 (firstTransitionEvent t m a) (secondTransitionEvent t m a)
    (UpperCanonical.hlozTransitionCost K m)
    (measurableSet_firstTransitionEvent t m a)
    (measurableSet_secondTransitionEvent t m a)
    (firstTransitionEvent_subset_thresholdReachStage_two t m a)
    (secondTransitionEvent_subset_first t m a)
    (hlozTransitionCost_ne_top K m) specs.second

theorem screenedThirdTransition_measure_le_of_validStoppedSpecs
    (K : ℝ≥0) (t : DominoTiling) (m : ℕ)
    (a : (GapScale × GapScale) × GapScale)
    (specs : ThreeValidTransitionStoppedCoordinateSpecs K t m a) :
    simpleRandomWalk (screenedThirdTransitionEvent t m a) ≤
      UpperCanonical.hlozTransitionCost K m *
        simpleRandomWalk (secondTransitionEvent t m a) := by
  apply transition_measure_le_of_validFavoriteTilingStoppedCoordinateSpec
    t m 3 (secondTransitionEvent t m a) (screenedThirdTransitionEvent t m a)
    (UpperCanonical.hlozTransitionCost K m)
    (measurableSet_secondTransitionEvent t m a)
    (measurableSet_screenedThirdTransitionEvent t m a)
    (secondTransitionEvent_subset_thresholdReachStage_three t m a)
    _ (hlozTransitionCost_ne_top K m) specs.third
  exact fun _ hs ↦ thirdTransitionEvent_subset_second t m a hs.1

end

end Erdos1165.TilingValidTraceCappedStageAdapter
