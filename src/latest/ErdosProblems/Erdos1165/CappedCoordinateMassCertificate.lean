import ErdosProblems.Erdos1165.HLOZTraceCappedProductScreening

/-!
# From exact finite coordinate masses to capped product certificates

This is the coordinate-system-neutral disintegration lemma used by the six
state-dependent tiling fibres.  The input consists of exact finite prefix
mass formulae and a discrete product identity.  The output is the literal
restricted-real certificate consumed by the trace screening endgame.
-/

open MeasureTheory Set
open scoped ENNReal

namespace Erdos1165.CappedCoordinateMassCertificate

open HLOZSpatialAdapter PreStoppingConditionalLaw
open HLOZTraceCappedProductScreening

noncomputable section

/-- Restriction to an ambient trace piece does not change the real mass of a
measurable event already contained in that piece. -/
theorem restrictedReal_eq_real_of_subset
    {piece event : Set WalkPath} (hevent : MeasurableSet event)
    (hsub : event ⊆ piece) :
    (simpleRandomWalk.restrict piece).real event =
      simpleRandomWalk.real event := by
  change (simpleRandomWalk.restrict piece event).toReal =
    (simpleRandomWalk event).toReal
  rw [Measure.restrict_apply hevent, inter_eq_left.mpr hsub]

/-- Exact finite coordinate information on every trace atom and cap.

The two `event_mass` fields are normally proved by the prefix-free stopped
cylinder partition.  The `coordinate_identity` is normally proved by
grouping insertion coordinates by tiling domino and marginalizing the
distinguished dominoes.  None of these fields is a target transition
inequality. -/
structure CoordinateMassSpec {index : Type*}
    (piece : index → Set WalkPath) (next : Set WalkPath) (cost : ℝ≥0∞) where
  screened : index → ℕ → Set WalkPath
  fiber : index → ℕ → Set WalkPath
  measurable_screened : ∀ z cap, MeasurableSet (screened z cap)
  measurable_fiber : ∀ z cap, MeasurableSet (fiber z cap)
  screened_subset_piece : ∀ z cap, screened z cap ⊆ piece z
  fiber_subset_piece : ∀ z cap, fiber z cap ⊆ piece z
  monotone_screened : ∀ z, Monotone (screened z)
  transition_covered : ∀ z, piece z ∩ next ⊆ ⋃ cap, screened z cap
  commonFactor : index → ℕ → ℝ
  screenedCoordinateMass : index → ℕ → ℝ
  fiberCoordinateMass : index → ℕ → ℝ
  productProbability : index → ℕ → ℝ
  coordinate_identity : ∀ z cap,
    screenedCoordinateMass z cap =
      productProbability z cap * fiberCoordinateMass z cap
  screened_event_mass : ∀ z cap,
    simpleRandomWalk.real (screened z cap) =
      commonFactor z cap * screenedCoordinateMass z cap
  fiber_event_mass : ∀ z cap,
    simpleRandomWalk.real (fiber z cap) =
      commonFactor z cap * fiberCoordinateMass z cap
  product_bound : ∀ z cap, productProbability z cap ≤ cost.toReal

/-- Exact restricted-real identity derived from the two prefix-mass formulae
and the finite coordinate product identity. -/
theorem CoordinateMassSpec.disintegrate
    {index : Type*} {piece : index → Set WalkPath}
    {next : Set WalkPath} {cost : ℝ≥0∞}
    (spec : CoordinateMassSpec piece next cost) (z : index) (cap : ℕ) :
    (simpleRandomWalk.restrict (piece z)).real (spec.screened z cap) =
      spec.productProbability z cap *
        (simpleRandomWalk.restrict (piece z)).real (spec.fiber z cap) := by
  rw [restrictedReal_eq_real_of_subset (spec.measurable_screened z cap)
      (spec.screened_subset_piece z cap),
    restrictedReal_eq_real_of_subset (spec.measurable_fiber z cap)
      (spec.fiber_subset_piece z cap),
    spec.screened_event_mass z cap, spec.fiber_event_mass z cap,
    spec.coordinate_identity z cap]
  ring

/-- Convert exact coordinate mass data into the generic capped certificate. -/
def cappedProductScreenCertificateOfCoordinateMassSpec
    {index : Type*} {piece : index → Set WalkPath}
    {next : Set WalkPath} {cost : ℝ≥0∞}
    (spec : CoordinateMassSpec piece next cost) :
    CappedProductScreenCertificate piece next cost where
  screened := spec.screened
  fiber := spec.fiber
  productProbability := spec.productProbability
  measurable_screened := spec.measurable_screened
  monotone_screened := spec.monotone_screened
  next_subset := spec.transition_covered
  product_bound := spec.product_bound
  disintegrate := spec.disintegrate

/-- Populate a complete generic trace screen once the countable disjoint
trace partition and its coordinate mass specification have been proved. -/
def traceCappedProductScreeningOfCoordinateMassSpec
    {index : Type*} [Countable index]
    (stage next : Set WalkPath) (cost : ℝ≥0∞)
    (piece : index → Set WalkPath)
    (hmeas : ∀ z, MeasurableSet (piece z))
    (hdisjoint : Pairwise fun z w ↦ Disjoint (piece z) (piece w))
    (hunion : (⋃ z, piece z) = stage) (hnext : next ⊆ stage)
    (spec : CoordinateMassSpec piece next cost) :
    TraceCappedProductScreening (Index := index) stage next cost where
  piece := piece
  measurable_piece := hmeas
  disjoint_piece := hdisjoint
  union_piece := hunion
  next_subset_stage := hnext
  certificate := cappedProductScreenCertificateOfCoordinateMassSpec spec

/-- Existential package form of the preceding constructor. -/
def someTraceCappedProductScreeningOfCoordinateMassSpec
    {index : Type} [Countable index]
    (stage next : Set WalkPath) (cost : ℝ≥0∞)
    (piece : index → Set WalkPath)
    (hmeas : ∀ z, MeasurableSet (piece z))
    (hdisjoint : Pairwise fun z w ↦ Disjoint (piece z) (piece w))
    (hunion : (⋃ z, piece z) = stage) (hnext : next ⊆ stage)
    (spec : CoordinateMassSpec piece next cost) :
    SomeTraceCappedProductScreening stage next cost where
  Index := index
  countableIndex := inferInstance
  screening := traceCappedProductScreeningOfCoordinateMassSpec
    stage next cost piece hmeas hdisjoint hunion hnext spec

end

end Erdos1165.CappedCoordinateMassCertificate
