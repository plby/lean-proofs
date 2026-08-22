/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.HLOZSourceEndpointTransportTable
import ErdosProblems.Erdos1165.TilingLiteralPrefixedConditionalRefinement

/-!
# Exact stopped-fibre transport along the dominant-endpoint table

Checker recentering and column reflection act on complete path events, not on
an unshifted retained word.  This module therefore transports the already
constructed prefixed stopped fibres by literal preimage.  The coordinate
masses and their common physical-prefix factor are left unchanged; the exact
simple-random-walk preimage law transports the two event-mass identities.
-/

open MeasureTheory Set
open scoped ENNReal

namespace Erdos1165.HLOZSourceTransportCoordinateMass

open CappedCoordinateMassCertificate
open HLOZSourceEndpointTransportTable

noncomputable section

abbrev DominoTiling := Tilings.Tiling

/-- A target event pulled back through one row of the normalized endpoint
transport table. -/
def sourceTransportPreimage (t : DominoTiling)
    (cls : DominantEndpointClass) (A : Set WalkPath) : Set WalkPath :=
  sourceTransportPath t cls ⁻¹' A

/-- Exact pullback of a coordinate-mass specification.  In particular, this
is not an original-trace identification: every target fibre remains a full
prefixed target fibre and only its complete path event is pulled back. -/
noncomputable def coordinateMassSpecSourceTransport
    {index : Type*} {piece : index → Set WalkPath}
    {next : Set WalkPath} {cost : ℝ≥0∞}
    (t : DominoTiling) (cls : DominantEndpointClass)
    (spec : CoordinateMassSpec piece next cost) :
    CoordinateMassSpec
      (fun z ↦ sourceTransportPreimage t cls (piece z))
      (sourceTransportPreimage t cls next) cost where
  screened := fun z cap ↦
    sourceTransportPreimage t cls (spec.screened z cap)
  fiber := fun z cap ↦
    sourceTransportPreimage t cls (spec.fiber z cap)
  measurable_screened := fun z cap ↦
    (spec.measurable_screened z cap).preimage
      (measurable_sourceTransportPath t cls)
  measurable_fiber := fun z cap ↦
    (spec.measurable_fiber z cap).preimage
      (measurable_sourceTransportPath t cls)
  screened_subset_piece := fun z cap _ hs ↦ spec.screened_subset_piece z cap hs
  fiber_subset_piece := fun z cap _ hs ↦ spec.fiber_subset_piece z cap hs
  monotone_screened := by
    intro z a b hab s hs
    exact spec.monotone_screened z hab hs
  transition_covered := by
    intro z s hs
    have htarget : sourceTransportPath t cls s ∈ piece z ∩ next := hs
    rcases Set.mem_iUnion.mp (spec.transition_covered z htarget) with
      ⟨cap, hcap⟩
    exact Set.mem_iUnion.mpr ⟨cap, hcap⟩
  commonFactor := spec.commonFactor
  screenedCoordinateMass := spec.screenedCoordinateMass
  fiberCoordinateMass := spec.fiberCoordinateMass
  productProbability := spec.productProbability
  coordinate_identity := spec.coordinate_identity
  screened_event_mass := by
    intro z cap
    have hmeasure := simpleRandomWalk_preimage_sourceTransportPath t cls
      (spec.measurable_screened z cap)
    exact congrArg ENNReal.toReal hmeasure |>.trans (spec.screened_event_mass z cap)
  fiber_event_mass := by
    intro z cap
    have hmeasure := simpleRandomWalk_preimage_sourceTransportPath t cls
      (spec.measurable_fiber z cap)
    exact congrArg ENNReal.toReal hmeasure |>.trans (spec.fiber_event_mass z cap)
  product_bound := spec.product_bound

@[simp] theorem coordinateMassSpecSourceTransport_screened
    {index : Type*} {piece : index → Set WalkPath}
    {next : Set WalkPath} {cost : ℝ≥0∞}
    (t : DominoTiling) (cls : DominantEndpointClass)
    (spec : CoordinateMassSpec piece next cost) (z : index) (cap : ℕ) :
    (coordinateMassSpecSourceTransport t cls spec).screened z cap =
      sourceTransportPath t cls ⁻¹' spec.screened z cap := rfl

@[simp] theorem coordinateMassSpecSourceTransport_fiber
    {index : Type*} {piece : index → Set WalkPath}
    {next : Set WalkPath} {cost : ℝ≥0∞}
    (t : DominoTiling) (cls : DominantEndpointClass)
    (spec : CoordinateMassSpec piece next cost) (z : index) (cap : ℕ) :
    (coordinateMassSpecSourceTransport t cls spec).fiber z cap =
      sourceTransportPath t cls ⁻¹' spec.fiber z cap := rfl

@[simp] theorem coordinateMassSpecSourceTransport_productProbability
    {index : Type*} {piece : index → Set WalkPath}
    {next : Set WalkPath} {cost : ℝ≥0∞}
    (t : DominoTiling) (cls : DominantEndpointClass)
    (spec : CoordinateMassSpec piece next cost) (z : index) (cap : ℕ) :
    (coordinateMassSpecSourceTransport t cls spec).productProbability z cap =
      spec.productProbability z cap := rfl

end

end Erdos1165.HLOZSourceTransportCoordinateMass
