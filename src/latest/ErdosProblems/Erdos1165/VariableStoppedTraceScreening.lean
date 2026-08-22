import ErdosProblems.Erdos1165.ExactFavoriteTruncation

open MeasureTheory Set
open scoped ENNReal NNReal

namespace Erdos1165.VariableStoppedTraceScreening

open LazyDecomposition VariableStoppedFiber VariableStoppedTracePartition
open HLOZStoppedSpatialScreening HLOZStoppedProductRefinement HLOZPathEvents
open HLOZSpatialAdapter

noncomputable section

/-!
# Screening adapters for the sound trace/favorite partition

The only path-space point outside the increment representation is the null
`none` piece.  This module shows that product-screen data constructed on the
genuine trace/favorite fibres extends canonically across that junk piece.
No transition estimate is assumed in this extension.
-/

/-- Add one null piece to product-screen data.  On that piece the screened
event is `junk ∩ next`, while both its restricted measure and its product
mass are zero. -/
def extendUpperProductScreenDataWithNull
    {index : Type*} (piece : index → Set WalkPath) (junk next : Set WalkPath)
    (hmeasJunk : MeasurableSet junk) (hmeasNext : MeasurableSet next)
    (hjunk : simpleRandomWalk junk = 0)
    (data : UpperProductScreenData piece next) :
    UpperProductScreenData
      (fun z : Option index ↦ match z with | none => junk | some i => piece i)
      next where
  orientation z cap := match z with
    | none => .even
    | some i => data.orientation i cap
  retainedCount z cap := match z with
    | none => 0
    | some i => data.retainedCount i cap
  start z cap := match z with
    | none => (0, 0)
    | some i => data.start i cap
  retained z cap := by
    cases z with
    | none => exact Fin.elim0
    | some i => exact data.retained i cap
  distinguished z cap := match z with
    | none => ∅
    | some i => data.distinguished i cap
  upper z cap := by
    cases z with
    | none => exact fun _ ↦ 0
    | some i => exact data.upper i cap
  accepts z cap := by
    cases z with
    | none => exact fun _ ↦ false
    | some i => exact data.accepts i cap
  screened z cap := match z with
    | none => junk ∩ next
    | some i => data.screened i cap
  fiber z cap := match z with
    | none => ∅
    | some i => data.fiber i cap
  measurable_screened z cap := by
    cases z with
    | none =>
        exact hmeasJunk.inter hmeasNext
    | some i => exact data.measurable_screened i cap
  monotone_screened z := by
    cases z with
    | none =>
        intro a b hab s hs
        exact hs
    | some i => exact data.monotone_screened i
  transition_covered z := by
    cases z with
    | none =>
        intro s hs
        exact Set.mem_iUnion.mpr ⟨0, hs⟩
    | some i => exact data.transition_covered i
  disintegrate z cap := by
    cases z with
    | some i => exact data.disintegrate i cap
    | none =>
        have hrestrict : simpleRandomWalk.restrict junk = 0 :=
          Measure.restrict_eq_zero.mpr hjunk
        rw [hrestrict]
        simp [PreStoppingConditionalLaw.upperProductScreenMass]

theorem finiteProductScreenBound_extendWithNull
    {index : Type*} (piece : index → Set WalkPath) (junk next : Set WalkPath)
    (hmeasJunk : MeasurableSet junk) (hmeasNext : MeasurableSet next)
    (hjunk : simpleRandomWalk junk = 0)
    (data : UpperProductScreenData piece next) (cost : ℝ≥0∞)
    (hbound : FiniteProductScreenBound data cost) :
    FiniteProductScreenBound
      (extendUpperProductScreenDataWithNull piece junk next
        hmeasJunk hmeasNext hjunk data) cost := by
  intro z cap
  cases z with
  | some i => exact hbound i cap
  | none =>
      simp [extendUpperProductScreenDataWithNull,
        PreStoppingConditionalLaw.upperProductScreenMass]

/-- The genuine (non-junk) favorite/trace fibres. -/
def supportedFavoriteCreationPiece {o : Orientation} (m k : ℕ)
    (z : ExternalWordCode o × CreationFavoriteData) : Set WalkPath :=
  favoriteCreationPiece m k (some z)

theorem favoriteCreationPiece_eq_option {o : Orientation} (m k : ℕ) :
    favoriteCreationPiece (o := o) m k =
      fun z : Option (ExternalWordCode o × CreationFavoriteData) ↦
        match z with
        | none => thresholdReachStage m k \ validStepWalk
        | some i => supportedFavoriteCreationPiece m k i := by
  funext z
  cases z <;> rfl

/-- Extend supported product data to the exact favorite/trace partition. -/
def extendFavoriteProductScreenData {o : Orientation} (m k : ℕ)
    (next : Set WalkPath) (hmeasNext : MeasurableSet next)
    (data : UpperProductScreenData
      (supportedFavoriteCreationPiece (o := o) m k) next) :
    UpperProductScreenData (favoriteCreationPiece (o := o) m k) next where
  orientation z cap := match z with
    | none => .even
    | some i => data.orientation i cap
  retainedCount z cap := match z with
    | none => 0
    | some i => data.retainedCount i cap
  start z cap := match z with
    | none => (0, 0)
    | some i => data.start i cap
  retained z cap := by
    cases z with
    | none => exact Fin.elim0
    | some i => exact data.retained i cap
  distinguished z cap := match z with
    | none => ∅
    | some i => data.distinguished i cap
  upper z cap := by
    cases z with
    | none => exact fun _ ↦ 0
    | some i => exact data.upper i cap
  accepts z cap := by
    cases z with
    | none => exact fun _ ↦ false
    | some i => exact data.accepts i cap
  screened z cap := match z with
    | none => (thresholdReachStage m k \ validStepWalk) ∩ next
    | some i => data.screened i cap
  fiber z cap := match z with
    | none => ∅
    | some i => data.fiber i cap
  measurable_screened z cap := by
    cases z with
    | none =>
        exact ((measurableSet_thresholdReachStage m k).diff
          measurableSet_validStepWalk).inter hmeasNext
    | some i => exact data.measurable_screened i cap
  monotone_screened z := by
    cases z with
    | none => intro _ _ _ _ h; exact h
    | some i => exact data.monotone_screened i
  transition_covered z := by
    cases z with
    | none => intro s hs; exact Set.mem_iUnion.mpr ⟨0, hs⟩
    | some i => exact data.transition_covered i
  disintegrate z cap := by
    cases z with
    | some i => exact data.disintegrate i cap
    | none =>
        have hrestrict : simpleRandomWalk.restrict
            (favoriteCreationPiece (o := o) m k none) = 0 :=
          Measure.restrict_eq_zero.mpr
            (simpleRandomWalk_favoriteCreationPiece_none (o := o) m k)
        rw [hrestrict]
        simp [PreStoppingConditionalLaw.upperProductScreenMass]

theorem finiteProductScreenBound_extendFavorite
    {o : Orientation} (m k : ℕ) (next : Set WalkPath)
    (hmeasNext : MeasurableSet next)
    (data : UpperProductScreenData
      (supportedFavoriteCreationPiece (o := o) m k) next)
    (cost : ℝ≥0∞) (hbound : FiniteProductScreenBound data cost) :
    FiniteProductScreenBound
      (extendFavoriteProductScreenData m k next hmeasNext data) cost := by
  intro z cap
  cases z with
  | some i => exact hbound i cap
  | none =>
      simp [extendFavoriteProductScreenData,
        PreStoppingConditionalLaw.upperProductScreenMass]

/-- A constructor for the first trace-screening package.  The countable
partition fields and the null piece are discharged here; the remaining
supported `data` is precisely the genuine stopped-fibre disintegration. -/
def firstTraceProductScreening_of_supportedFavoriteData
    {o : Orientation} (K : ℝ≥0) (t : DominoTiling) (m : ℕ)
    (a : (GapScale × GapScale) × GapScale)
    (data : UpperProductScreenData
      (supportedFavoriteCreationPiece (o := o) m 1)
      (firstTransitionEvent t m a))
    (hbound : FiniteProductScreenBound data
      (UpperCanonical.hlozTransitionCost K m)) :
    FirstTraceProductScreening (FavoriteTraceCode o) K t m a where
  piece := favoriteCreationPiece m 1
  measurable_piece := measurableSet_favoriteCreationPiece m 1
  disjoint_piece := fun _ _ h ↦ disjoint_favoriteCreationPiece_of_ne m 1 h
  union_piece := iUnion_favoriteCreationPiece_eq_firstCreationStage m
  next_subset_stage := by
    intro s hs
    simpa [firstCreationStage, firstCreationAtom] using
      (firstTransitionEvent_subset_iUnion_firstCreationAtom t m a hs)
  data := extendFavoriteProductScreenData m 1
    (firstTransitionEvent t m a)
    (measurableSet_firstTransitionEvent t m a) data
  product_bound := finiteProductScreenBound_extendFavorite m 1
    (firstTransitionEvent t m a)
    (measurableSet_firstTransitionEvent t m a) data
    (UpperCanonical.hlozTransitionCost K m) hbound

end

end Erdos1165.VariableStoppedTraceScreening
