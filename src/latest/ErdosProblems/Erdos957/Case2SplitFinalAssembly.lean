import ErdosProblems.Erdos957.Case2SplitFinalReduction

/-!
# One-leaf assembly of the degree-five Case-2 split residual

The finite metric reduction leaves four outward-facing fields.  Three are
mixed Case-2/Case-4 configurations.  Re-centering the middle mixed branch at
its second Case-2 source and using pair coherence discharges all three.  The
only remaining input is the adjacent away-first/away-second split pair.
-/

noncomputable section

namespace Erdos957Case2SplitFinalAssembly

open Erdos957GeometryCore
open Erdos957GeometryLocalRows
open Erdos957CollisionInstantiation
open Erdos957CaseClassification
open Erdos957Case2RoleUniqueness
open Erdos957Case2SecondaryNoThree
open Erdos957CoherentRealizedRows
open Erdos957RoleCollisions
open Erdos957Case2SplitDegreeFive
open Erdos957Case2SplitFinalReduction

abbrev Point := Erdos957GeometryCore.Point

variable {A : Finset Point} {P : CyclicHullData A}
variable {W : DiameterWitnessData P} {F : P.FlatAlignedFrameData}

/-- The single strict-turn boundary left after all mixed outward branches
have been eliminated. -/
structure TwoSplitAwayFirstSecondResidual
    (Q : CommonCoherentRealizedSourceRows P W F.chart) where
  eliminate :
    ∀ {s t u : Source P W} {v : Vertex A}
      (S : RealizedArrivalAt (F := F) Q.rows s v)
      (T : RealizedArrivalAt (F := F) Q.rows t v)
      (U : RealizedArrivalAt (F := F) Q.rows u v)
      (B : Case2SecondaryArrivalFormula S.target S.descriptor),
      S.target.role = PairCases.TargetRoleName.case2Secondary →
      T.target.role = PairCases.TargetRoleName.case4SplitRight →
      U.target.role = PairCases.TargetRoleName.case4SplitRight →
      (unitDistanceGraph A).degree v = 5 →
      sourceIndex P W t.1 t.property =
        Erdos957Case4NoThree.awayHullVertex P
          (sourceIndex P W s.1 s.property) B.formula.side 0 →
      sourceIndex P W u.1 u.property =
        Erdos957Case4NoThree.awayHullVertex P
          (sourceIndex P W s.1 s.property) B.formula.side 1 →
      s ≠ t → s ≠ u → t ≠ u → False

/-- All three mixed outward fields follow from the checked incident target
pinning, the outward first-edge theorem, and coherent partner exclusion. -/
theorem outwardResiduals_of_two_split
    (hA : IsOneSeparated A)
    (Q : CommonCoherentRealizedSourceRows P W F.chart)
    (K : TwoSplitAwayFirstSecondResidual Q) :
    Case2SplitOutwardResiduals Q where
  case2_incident_split_away_first := by
    intro s t u v S T U B hsRole htRole huRole hdegree
      htIndex huIndex hst hsu htu
    let E := Classical.choice
      (nonempty_case2SecondaryArrivalFormula T.target T.descriptor htRole)
    have hw := target_eq_w_of_case2Secondary_at_incident_of_degree_five
      hA B.formula E.formula hdegree htIndex
    exact no_case4SplitRight_at_outward_away_first_of_target_eq_w
      Q S U hsRole huRole B hw huIndex
  case2_away_first_split_away_second := by
    intro s t u v S T U B hsRole htRole huRole hdegree
      htIndex huIndex hst hsu htu
    let Bt := Classical.choice
      (nonempty_case2SecondaryArrivalFormula T.target T.descriptor htRole)
    by_cases hsame : Bt.formula.side = B.formula.side
    · have hsIncident : sourceIndex P W s.1 s.property =
          incidentHullVertex P (sourceIndex P W t.1 t.property)
            Bt.formula.side 0 := by
        cases hB : B.formula.side <;>
          cases hT : Bt.formula.side <;>
          simp_all [incidentHullVertex,
            Erdos957Case4NoThree.awayHullVertex]
      have huAway : sourceIndex P W u.1 u.property =
          Erdos957Case4NoThree.awayHullVertex P
            (sourceIndex P W t.1 t.property) Bt.formula.side 0 := by
        cases hB : B.formula.side <;>
          cases hT : Bt.formula.side <;>
          simp_all [incidentHullVertex,
            Erdos957Case4NoThree.awayHullVertex, pow_succ]
      have hw := target_eq_w_of_case2Secondary_at_incident_of_degree_five
        hA Bt.formula B.formula hdegree hsIncident
      exact no_case4SplitRight_at_outward_away_first_of_target_eq_w
        Q T U htRole huRole Bt hw huAway
    · have huIncident : sourceIndex P W u.1 u.property =
          incidentHullVertex P (sourceIndex P W t.1 t.property)
            Bt.formula.side 0 := by
        cases hB : B.formula.side <;>
          cases hT : Bt.formula.side <;>
          simp_all [incidentHullVertex,
            Erdos957Case4NoThree.awayHullVertex, pow_succ]
      exact no_case4SplitRight_at_incident_of_case2_degree_five
        hA Q T U htRole huRole hdegree huIncident
  case2_away_second_split_away_first := by
    intro s t u v S T U B hsRole htRole huRole hdegree
      htIndex huIndex hst hsu htu
    exact no_case2_away_second_case4_away_first
      Q S T U B hsRole htRole huRole htIndex huIndex
  two_split_away_first_second := K.eliminate

/-- The one strict-turn leaf is sufficient for the complete two-field
degree-five residual consumed by weighted completion. -/
theorem case2SecondarySplitDegreeFiveResiduals_of_two_split
    (hA : IsOneSeparated A)
    (Q : CommonCoherentRealizedSourceRows P W F.chart)
    (K : TwoSplitAwayFirstSecondResidual Q) :
    Case2SecondarySplitDegreeFiveResiduals (F := F) Q.rows :=
  case2SecondarySplitDegreeFiveResiduals_of_outward hA Q
    (outwardResiduals_of_two_split hA Q K)

end Erdos957Case2SplitFinalAssembly

#print axioms Erdos957Case2SplitFinalAssembly.outwardResiduals_of_two_split
#print axioms Erdos957Case2SplitFinalAssembly.case2SecondarySplitDegreeFiveResiduals_of_two_split
