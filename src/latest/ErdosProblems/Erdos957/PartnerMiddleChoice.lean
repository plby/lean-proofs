import ErdosProblems.Erdos957.PartnerMiddle
import ErdosProblems.Erdos957.CaseClassification

/-!
# Coherence of canonical middle choices at adjacent sources

The geometric work is in `PartnerMiddle`.  This leaf module identifies its
shared equilateral point with the deterministic phase-bin choice made by
`bisectorSourceMiddle` whenever the adjacent endpoint is itself a source.
-/

open scoped RealInnerProductSpace

noncomputable section

namespace Erdos957PartnerMiddleChoice

open Erdos957
open Erdos957GeometryCore
open Erdos957HullGeometryBridge
open Erdos957BisectorFrame
open Erdos957TurnSum.HullOrderBridge

abbrev Point := Erdos957.Point

/-- At a source whose successor is the other endpoint of a supported unit
equilateral triangle, the canonical bisector middle is its third vertex. -/
theorem bisectorSourceMiddle_eq_of_next
    {A : Finset Point} (hA : IsOneSeparated A)
    (O : CyclicHullOrder A) (L : LiftedCyclicHullOrder O)
    (W : DiameterWitnessData (cyclicHullDataOfOrder O L))
    (partner : {p // p ∈ (cyclicHullDataOfOrder O L).H})
    (hp : partner.1 ∈ sourceVertices (cyclicHullDataOfOrder O L) W)
    (middle : Erdos957GeometryCore.Vertex A)
    (hpartnerNext : (unitDistanceGraph A).Adj partner.1
      ((cyclicHullDataOfOrder O L).next partner).1)
    (hpartnerMiddle : (unitDistanceGraph A).Adj partner.1 middle)
    (hnextMiddle : (unitDistanceGraph A).Adj
      ((cyclicHullDataOfOrder O L).next partner).1 middle) :
    Erdos957CaseClassification.PairCases.bisectorSourceMiddle
      hA O L W partner hp = middle := by
  apply Erdos957TwoExtremeFrame.eq_of_source_adj_of_inOpenMiddleCone
    hA (cyclicHullDataOfOrder O L) (bisectorAlignedChartData O L) partner
  · exact Erdos957CaseClassification.PairCases.bisectorSourceMiddle_adj
      hA O L W partner hp
  · exact hpartnerMiddle
  · exact Erdos957CaseClassification.PairCases.bisectorSourceMiddle_in_open_cone
      hA O L W partner hp
  · exact Erdos957PartnerMiddle.middle_in_partner_bisector_openCone_of_next
      hA O L partner
      (Erdos957CaseClassification.source_isFlat
        (cyclicHullDataOfOrder O L) W partner hp)
      middle hpartnerNext hpartnerMiddle hnextMiddle

/-- The predecessor-side analogue of `bisectorSourceMiddle_eq_of_next`. -/
theorem bisectorSourceMiddle_eq_of_previous
    {A : Finset Point} (hA : IsOneSeparated A)
    (O : CyclicHullOrder A) (L : LiftedCyclicHullOrder O)
    (W : DiameterWitnessData (cyclicHullDataOfOrder O L))
    (partner : {p // p ∈ (cyclicHullDataOfOrder O L).H})
    (hp : partner.1 ∈ sourceVertices (cyclicHullDataOfOrder O L) W)
    (middle : Erdos957GeometryCore.Vertex A)
    (hpartnerPrevious : (unitDistanceGraph A).Adj partner.1
      ((cyclicHullDataOfOrder O L).next⁻¹ partner).1)
    (hpartnerMiddle : (unitDistanceGraph A).Adj partner.1 middle)
    (hpreviousMiddle : (unitDistanceGraph A).Adj
      ((cyclicHullDataOfOrder O L).next⁻¹ partner).1 middle) :
    Erdos957CaseClassification.PairCases.bisectorSourceMiddle
      hA O L W partner hp = middle := by
  apply Erdos957TwoExtremeFrame.eq_of_source_adj_of_inOpenMiddleCone
    hA (cyclicHullDataOfOrder O L) (bisectorAlignedChartData O L) partner
  · exact Erdos957CaseClassification.PairCases.bisectorSourceMiddle_adj
      hA O L W partner hp
  · exact hpartnerMiddle
  · exact Erdos957CaseClassification.PairCases.bisectorSourceMiddle_in_open_cone
      hA O L W partner hp
  · exact Erdos957PartnerMiddle.middle_in_partner_bisector_openCone_of_previous
      hA O L partner
      (Erdos957CaseClassification.source_isFlat
        (cyclicHullDataOfOrder O L) W partner hp)
      middle hpartnerPrevious hpartnerMiddle hpreviousMiddle

/-- For two adjacent sources sharing a supported unit equilateral point,
both deterministic bisector choices are that same actual point.  This is
the coherence form consumed by paired Case-4 row construction. -/
theorem bisectorSourceMiddles_eq_of_adjacent
    {A : Finset Point} (hA : IsOneSeparated A)
    (O : CyclicHullOrder A) (L : LiftedCyclicHullOrder O)
    (W : DiameterWitnessData (cyclicHullDataOfOrder O L))
    (source : {p // p ∈ (cyclicHullDataOfOrder O L).H})
    (hs : source.1 ∈ sourceVertices (cyclicHullDataOfOrder O L) W)
    (ht : ((cyclicHullDataOfOrder O L).next source).1 ∈
      sourceVertices (cyclicHullDataOfOrder O L) W)
    (middle : Erdos957GeometryCore.Vertex A)
    (hsourceNext : (unitDistanceGraph A).Adj source.1
      ((cyclicHullDataOfOrder O L).next source).1)
    (hsourceMiddle : (unitDistanceGraph A).Adj source.1 middle)
    (hnextMiddle : (unitDistanceGraph A).Adj
      ((cyclicHullDataOfOrder O L).next source).1 middle) :
    Erdos957CaseClassification.PairCases.bisectorSourceMiddle
        hA O L W source hs = middle ∧
      Erdos957CaseClassification.PairCases.bisectorSourceMiddle
        hA O L W ((cyclicHullDataOfOrder O L).next source) ht = middle := by
  constructor
  · exact bisectorSourceMiddle_eq_of_next hA O L W source hs middle
      hsourceNext hsourceMiddle hnextMiddle
  · apply bisectorSourceMiddle_eq_of_previous hA O L W
      ((cyclicHullDataOfOrder O L).next source) ht middle
    · rw [show ((cyclicHullDataOfOrder O L).next⁻¹
          ((cyclicHullDataOfOrder O L).next source)) = source by
          exact (cyclicHullDataOfOrder O L).next.symm_apply_apply source]
      exact hsourceNext.symm
    · exact hnextMiddle
    · rw [show ((cyclicHullDataOfOrder O L).next⁻¹
          ((cyclicHullDataOfOrder O L).next source)) = source by
          exact (cyclicHullDataOfOrder O L).next.symm_apply_apply source]
      exact hsourceMiddle

end Erdos957PartnerMiddleChoice
