import ErdosProblems.Erdos957.Case2SecondaryNoThree
import ErdosProblems.Erdos957.Case4SplitClassification

/-!
# Mixed Case-2/Case-4 same-side leaves

This file isolates the recipient-relative geometry for a Case-2 secondary
arrival and a produced Case-4 split-right arrival.  In particular it does
not alter the generic Case-2 collision dispatcher.
-/

open scoped RealInnerProductSpace

noncomputable section

namespace Erdos957Case2Case4SameSide

open Erdos957GeometryCore
open Erdos957CaseClassification
open Erdos957Case2RoleUniqueness
open Erdos957Case2SecondaryNoThree
open Erdos957Case4SplitClassification
open Erdos957CollisionInstantiation
open Erdos957GeometryLocalRows
open Erdos957RoleCollisions
open Erdos957CoherentRealizedRows

abbrev Point := Erdos957GeometryCore.Point

variable {A : Finset Point} {P : CyclicHullData A}
variable {W : DiameterWitnessData P}
variable {F : P.FlatAlignedFrameData}

/-- An arbitrary arrival within two unit edges through the second incident
source forces the selected Case-4 recipient to carry the incident-side
association.  Unlike the older split/split wrapper, the competing arrival
need not itself be Case 4. -/
lemma case4SplitRight_association_eq_side_of_within_two_incident_second
    (hA : IsOneSeparated A)
    (Q : CommonCoherentRealizedSourceRows P W F.chart)
    {t : Source P W} {v : Vertex A}
    (T : RealizedArrivalAt (F := F) Q.rows t v)
    (htRole : T.target.role = PairCases.TargetRoleName.case4SplitRight)
    (Qt : CommonPairedCase4Rows Q.rows t.1 t.property)
    {r : {p // p ∈ P.H}}
    (hrIndex : r = Erdos957Case4NoThree.incidentHullVertex P
      (sourceIndex P W t.1 t.property) Qt.twoExtreme.side 1)
    (hrWithin : WithinTwoUnitEdges r.1 v) :
    T.descriptor.association =
      cyclicSideAssociation Qt.twoExtreme.side := by
  have htTarget : T.target.target = Qt.currentSecondaryTarget := by
    apply Option.some.inj
    rw [← T.target.target_at_role, htRole, Qt.current_secondary_role]
  have htVertex : Qt.currentSecondaryTarget.vertex = v := by
    calc
      Qt.currentSecondaryTarget.vertex = T.target.target.vertex :=
        congrArg LocalTarget.vertex htTarget.symm
      _ = v := T.target.vertex_eq.symm
  have hwithin : WithinTwoUnitEdges
      (Erdos957Case4NoThree.incidentHullVertex P
        (sourceIndex P W t.1 t.property) Qt.twoExtreme.side 1).1
      Qt.currentSecondaryTarget.vertex := by
    rw [← hrIndex, htVertex]
    exact hrWithin
  have hrow : (Q.rows t.1 t.property).roleAssociation
      PairCases.TargetRoleName.case4SplitRight =
        cyclicSideAssociation Qt.twoExtreme.side := by
    by_contra hne
    exact (CommonPairedCase4Rows.not_within_two_incident_second_of_association_ne_side
      hA F Qt (source_isFlat P W _ t.property) hne) hwithin
  calc
    T.descriptor.association =
        (Q.rows t.1 t.property).roleAssociation T.target.role :=
      T.descriptor.association_eq
    _ = (Q.rows t.1 t.property).roleAssociation
        PairCases.TargetRoleName.case4SplitRight := by rw [htRole]
    _ = _ := hrow

/-- Dually, an arbitrary arrival within two unit edges through the second
away source forces the selected split recipient to carry the association
opposite its incident edge. -/
lemma case4SplitRight_association_eq_opposite_of_within_two_away_second
    (hA : IsOneSeparated A)
    (Q : CommonCoherentRealizedSourceRows P W F.chart)
    {t : Source P W} {v : Vertex A}
    (T : RealizedArrivalAt (F := F) Q.rows t v)
    (htRole : T.target.role = PairCases.TargetRoleName.case4SplitRight)
    (Qt : CommonPairedCase4Rows Q.rows t.1 t.property)
    {r : {p // p ∈ P.H}}
    (hrIndex : r = Erdos957Case4NoThree.awayHullVertex P
      (sourceIndex P W t.1 t.property) Qt.twoExtreme.side 1)
    (hrWithin : WithinTwoUnitEdges r.1 v) :
    T.descriptor.association =
      oppositeCyclicSideAssociation Qt.twoExtreme.side := by
  have htTarget : T.target.target = Qt.currentSecondaryTarget := by
    apply Option.some.inj
    rw [← T.target.target_at_role, htRole, Qt.current_secondary_role]
  have htVertex : Qt.currentSecondaryTarget.vertex = v := by
    calc
      Qt.currentSecondaryTarget.vertex = T.target.target.vertex :=
        congrArg LocalTarget.vertex htTarget.symm
      _ = v := T.target.vertex_eq.symm
  have hwithin : WithinTwoUnitEdges
      (Erdos957Case4NoThree.awayHullVertex P
        (sourceIndex P W t.1 t.property) Qt.twoExtreme.side 1).1
      Qt.currentSecondaryTarget.vertex := by
    rw [← hrIndex, htVertex]
    exact hrWithin
  have hrowNe : (Q.rows t.1 t.property).roleAssociation
      PairCases.TargetRoleName.case4SplitRight ≠
        cyclicSideAssociation Qt.twoExtreme.side := by
    intro hrow
    exact (CommonPairedCase4Rows.not_within_two_away_second_of_association_eq_side
      hA F Qt (source_isFlat P W _ t.property) hrow) hwithin
  have hrow : (Q.rows t.1 t.property).roleAssociation
      PairCases.TargetRoleName.case4SplitRight =
        oppositeCyclicSideAssociation Qt.twoExtreme.side := by
    cases hside : Qt.twoExtreme.side <;>
      cases ha : (Q.rows t.1 t.property).roleAssociation
        PairCases.TargetRoleName.case4SplitRight <;>
      simp [hside, ha, cyclicSideAssociation,
        oppositeCyclicSideAssociation] at hrowNe ⊢
  calc
    T.descriptor.association =
        (Q.rows t.1 t.property).roleAssociation T.target.role :=
      T.descriptor.association_eq
    _ = (Q.rows t.1 t.property).roleAssociation
        PairCases.TargetRoleName.case4SplitRight := by rw [htRole]
    _ = _ := hrow

/-- A mixed Case-2/Case-4 same-associated collision cannot occur at the
second source continuing away from the Case-2 incident edge. -/
theorem case2Secondary_case4SplitRight_associations_ne_at_away_second
    (hA : IsOneSeparated A)
    (Q : CommonCoherentRealizedSourceRows P W F.chart)
    {s t : Source P W} {v : Vertex A}
    (S : RealizedArrivalAt (F := F) Q.rows s v)
    (T : RealizedArrivalAt (F := F) Q.rows t v)
    (hsRole : S.target.role = PairCases.TargetRoleName.case2Secondary)
    (htRole : T.target.role = PairCases.TargetRoleName.case4SplitRight)
    (B : Case2SecondaryArrivalFormula S.target S.descriptor)
    (Qt : CommonPairedCase4Rows Q.rows t.1 t.property)
    (htIndex : sourceIndex P W t.1 t.property =
      Erdos957Case4NoThree.awayHullVertex P
        (sourceIndex P W s.1 s.property) B.formula.side 1) :
    S.descriptor.association ≠ T.descriptor.association := by
  have hsAssoc : S.descriptor.association =
      oppositeCyclicSideAssociation B.formula.side := B.association_eq
  have hsWithin : WithinTwoUnitEdges
      (sourceIndex P W s.1 s.property).1 v := by
    have h := S.target.target.within_two
    simpa [S.target.vertex_eq] using h
  cases hsSide : B.formula.side <;>
    cases htSide : Qt.twoExtreme.side
  · have hsIndex : sourceIndex P W s.1 s.property =
        Erdos957Case4NoThree.incidentHullVertex P
          (sourceIndex P W t.1 t.property) Qt.twoExtreme.side 1 := by
      have hh := congrArg (fun x ↦ ((P.next⁻¹) ^ 2) x) htIndex
      simpa [Erdos957Case4NoThree.awayHullVertex,
        Erdos957Case4NoThree.incidentHullVertex, hsSide, htSide] using hh.symm
    have htAssoc :=
      case4SplitRight_association_eq_side_of_within_two_incident_second
        hA Q T htRole Qt hsIndex hsWithin
    rw [hsAssoc, htAssoc]
    simp [hsSide, htSide, oppositeCyclicSideAssociation,
      cyclicSideAssociation]
  · have hsIndex : sourceIndex P W s.1 s.property =
        Erdos957Case4NoThree.awayHullVertex P
          (sourceIndex P W t.1 t.property) Qt.twoExtreme.side 1 := by
      have hh := congrArg (fun x ↦ ((P.next⁻¹) ^ 2) x) htIndex
      simpa [Erdos957Case4NoThree.awayHullVertex,
        hsSide, htSide] using hh.symm
    have htAssoc :=
      case4SplitRight_association_eq_opposite_of_within_two_away_second
        hA Q T htRole Qt hsIndex hsWithin
    rw [hsAssoc, htAssoc]
    simp [hsSide, htSide, oppositeCyclicSideAssociation]
  · have hsIndex : sourceIndex P W s.1 s.property =
        Erdos957Case4NoThree.awayHullVertex P
          (sourceIndex P W t.1 t.property) Qt.twoExtreme.side 1 := by
      have hh := congrArg (fun x ↦ (P.next ^ 2) x) htIndex
      simpa [Erdos957Case4NoThree.awayHullVertex,
        hsSide, htSide] using hh.symm
    have htAssoc :=
      case4SplitRight_association_eq_opposite_of_within_two_away_second
        hA Q T htRole Qt hsIndex hsWithin
    rw [hsAssoc, htAssoc]
    simp [hsSide, htSide, oppositeCyclicSideAssociation]
  · have hsIndex : sourceIndex P W s.1 s.property =
        Erdos957Case4NoThree.incidentHullVertex P
          (sourceIndex P W t.1 t.property) Qt.twoExtreme.side 1 := by
      have hh := congrArg (fun x ↦ (P.next ^ 2) x) htIndex
      simpa [Erdos957Case4NoThree.awayHullVertex,
        Erdos957Case4NoThree.incidentHullVertex, hsSide, htSide] using hh.symm
    have htAssoc :=
      case4SplitRight_association_eq_side_of_within_two_incident_second
        hA Q T htRole Qt hsIndex hsWithin
    rw [hsAssoc, htAssoc]
    simp [hsSide, htSide, oppositeCyclicSideAssociation,
      cyclicSideAssociation]

end Erdos957Case2Case4SameSide

namespace Erdos957Case2Case4SameSide

#print axioms case4SplitRight_association_eq_side_of_within_two_incident_second
#print axioms case4SplitRight_association_eq_opposite_of_within_two_away_second
#print axioms case2Secondary_case4SplitRight_associations_ne_at_away_second

end Erdos957Case2Case4SameSide
