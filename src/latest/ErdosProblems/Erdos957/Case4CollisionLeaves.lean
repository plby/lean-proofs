import ErdosProblems.Erdos957.Case4NoThree
import ErdosProblems.Erdos957.ExceptionalCollisionGeometry
import ErdosProblems.Erdos957.CoherentRealizedRows
import ErdosProblems.Erdos957.ExceptionalWindowDispatch
import ErdosProblems.Erdos957.RoleCollisions

/-!
# Checked collision leaves for generalized Case 4

This file connects the reflection-safe prefix estimates to the literal
common pair chart retained by coherent Case-4 rows.  It contains only
metric exclusions for direct competitors; exceptional cross-frame
competitors are handled separately.
-/

open scoped RealInnerProductSpace

noncomputable section

namespace Erdos957Case4CollisionLeaves

open Erdos957GeometryCore
open Erdos957GeometryLocalRows
open Erdos957CaseClassification
open Erdos957CoherentRealizedRows
open Erdos957CollisionInstantiation
open Erdos957RoleCollisions

abbrev Point := Erdos957GeometryCore.Point

variable {A : Finset Point} {P : CyclicHullData A}
variable {W : DiameterWitnessData P} {F : P.FlatAlignedFrameData}

private lemma cyclicSideAssociation_injective :
    Function.Injective cyclicSideAssociation := by
  intro a b h
  cases a <;> cases b <;> simp_all [cyclicSideAssociation]

/-- In any realized row which exposes both split Case-4 roles, every direct
positive target is the split-left target.  This is a finite constructor
elimination; it adds no geometric or capacity hypothesis. -/
lemma direct_target_eq_splitLeft_of_split_roles
    {C : P.AlignedChartData} {source : {p // p ∈ P.H}}
    {R : RealizedSourceRow P C source} {v : Vertex A}
    (D : RealizedPositiveTarget R v) (hdirect : IsDirectTargetRole D.role)
    {middle secondary : LocalTarget P C source}
    (hmiddle : R.targetAtRole PairCases.TargetRoleName.case4SplitLeft =
      some middle)
    (hsecondary : R.targetAtRole PairCases.TargetRoleName.case4SplitRight =
      some secondary) :
    D.target = middle := by
  rcases D with ⟨role, target, htarget, hv⟩
  cases R with
  | case1 middleVertex hdegree hone middleCoord hmiddleCoord hmiddleNotHull
      hunit row =>
      simp [RealizedSourceRow.targetAtRole] at hsecondary
  | case2 middleVertex hdegree htwo hmiddleNotHull twoExtreme normalized row =>
      simp [RealizedSourceRow.targetAtRole] at hsecondary
  | case3 middleVertex hdegree hone middleCoord row hmiddleVertex =>
      cases row <;> simp [RealizedSourceRow.targetAtRole] at hsecondary
  | case4 middleVertex hdegree htwo twoExtreme normalized row hmiddleVertex =>
      cases row with
      | whole middleTarget hcoord hfour =>
          simp [RealizedSourceRow.targetAtRole] at hsecondary
      | orderedLow farthest hfive middleTarget lowTarget hm hl hne =>
          have hmiddle' : middleTarget = middle := by
            simpa [RealizedSourceRow.targetAtRole] using hmiddle
          cases role <;>
            simp [IsDirectTargetRole, RealizedSourceRow.targetAtRole] at hdirect htarget
          exact htarget.symm.trans hmiddle'
      | orderedHigh farthest hsix recipients middleTarget sideTarget hm hs hne =>
          have hmiddle' : middleTarget = middle := by
            simpa [RealizedSourceRow.targetAtRole] using hmiddle
          cases role <;>
            simp [IsDirectTargetRole, RealizedSourceRow.targetAtRole] at hdirect htarget
          exact htarget.symm.trans hmiddle'
      | pairedSplit commonFrame farthest branch rightSource hright middleTarget
          secondaryTarget hsource hm hs hne =>
          have hmiddle' : middleTarget = middle := by
            simpa [RealizedSourceRow.targetAtRole] using hmiddle
          cases role <;>
            simp [IsDirectTargetRole, RealizedSourceRow.targetAtRole] at hdirect htarget
          exact htarget.symm.trans hmiddle'

/-- Hull vertices continuing through the incident partner, as opposed to
the `awayHullVertex` orbit on the other side of the source. -/
def incidentContinuationHullVertex (P : CyclicHullData A)
    (source : {p // p ∈ P.H}) (side : CyclicSide) (k : Fin 3) : {p // p ∈ P.H} :=
  match side with
  | .previous => ((P.next⁻¹) ^ (k.1 + 1)) source
  | .next => (P.next ^ (k.1 + 1)) source

/-- The coherently selected secondary recipient is genuinely different
from the equilateral middle.  This is the pulled-back form of the checked
`sourceRecipient_ne_v` property of the selected branch. -/
lemma CommonPairedCase4Rows.currentSecondary_ne_middle
    {C : P.AlignedChartData}
    {rows : HasRealizedSourceRows P W C}
    {u : Vertex A} {hu : u ∈ sourceVertices P W}
    (Q : CommonPairedCase4Rows rows u hu) :
    Q.currentSecondaryTarget.vertex ≠ Q.middle := by
  rw [Q.current_secondary_vertex]
  intro h
  have hcoord := congrArg
    (fun z : Vertex A => Q.commonFrame.frame.toCanonical (z : Point)) h
  have hmiddle : Q.commonFrame.frame.toCanonical Q.middle =
      Erdos957Cases24.Case2.v := by
    simpa [ActualCase24Rows.TwoExtremeCommonPairFrame.frame] using
      Q.commonFrame.middle_coordinate
  have hrecipient : Q.commonFrame.frame.toCanonical
      (Q.pairBranch.actualRecipient
        (ActualCase24Rows.case4SourceIsRight Q.twoExtreme)) =
      Q.pairBranch.branch.sourceRecipient
        (ActualCase24Rows.case4SourceIsRight Q.twoExtreme) := by
    simp [CommonCase4.CommonCase4HullPairBranch.actualRecipient]
  rw [hrecipient, hmiddle] at hcoord
  exact Q.pairBranch.branch.sourceRecipient_ne_v
    (ActualCase24Rows.case4SourceIsRight Q.twoExtreme) hcoord

/-- In the source-free common pair chart, the second vertex continuing
away from the incident edge is more than two horizontal units from the
Case-4 middle.  The two endpoint orientations are treated by the exact
reflection `x ↦ -x-1`; no chart equality is assumed. -/
lemma commonFrame_away_second_fst_gap_gt_two
    (F : P.FlatAlignedFrameData)
    (source : {p // p ∈ P.H}) (middle : Vertex A)
    (T : TwoExtremeCyclicWitness P source middle)
    (N : ActualCase24Rows.TwoExtremeNormalizedFrame source middle T)
    (E : ActualCase24Rows.TwoExtremeCommonPairFrame source middle T)
    (hi : P.IsFlat source) :
    2 < |(E.frame.toCanonical middle) 0 -
      (E.frame.toCanonical
        (Erdos957Case4NoThree.awayHullVertex P source T.side 1).1) 0| := by
  have hx := Erdos957Case4NoThree.normalizedFrame_away_second_fst_gt_three_halves
    F source middle T N hi
  have hm : E.frame.toCanonical middle = Erdos957Cases24.Case2.v := by
    simpa [ActualCase24Rows.TwoExtremeCommonPairFrame.frame] using
      E.middle_coordinate
  cases hside : T.side with
  | previous =>
      have hcoord :
          N.frame.toCanonical
              (Erdos957Case4NoThree.awayHullVertex P source T.side 1).1 =
            E.frame.toCanonical
              (Erdos957Case4NoThree.awayHullVertex P source T.side 1).1 := by
        cases N.frame_spec with
        | previous hs hunit hframe =>
            rw [hframe]
            simp [ActualCase24Rows.TwoExtremeCommonPairFrame.frame,
              ActualCase24Rows.case4PairEdgeBase, hside]
        | next hs hunit hframe => simp [hside] at hs
      simp only [Fin.isValue, gt_iff_lt] at hx hcoord ⊢
      rw [hcoord] at hx
      rw [hm]
      simp only [Erdos957Cases24.Case2.v,
        Erdos957Cases24.point_apply_zero]
      rw [abs_of_neg (by linarith)]
      linarith
  | next =>
      have hcoord :
          (N.frame.toCanonical
            (Erdos957Case4NoThree.awayHullVertex P source T.side 1).1) 0 =
            -(E.frame.toCanonical
              (Erdos957Case4NoThree.awayHullVertex P source T.side 1).1) 0 - 1 := by
        cases N.frame_spec with
        | previous hs hunit hframe => simp [hside] at hs
        | next hs hunit hframe =>
            rw [hframe]
            simp [Erdos957TwoExtremeAligned.reflectedSuccessorUnitEdgeRigidChart,
              Equiv.trans_apply, Erdos957TwoExtremeAligned.swapEndpointEquiv_apply,
              Erdos957TwoExtremeAligned.swapEndpointCoord_apply_zero,
              ActualCase24Rows.TwoExtremeCommonPairFrame.frame,
              ActualCase24Rows.case4PairEdgeBase, hside]
      simp only [Fin.isValue, gt_iff_lt] at hx hcoord ⊢
      rw [hm]
      simp only [Erdos957Cases24.Case2.v,
        Erdos957Cases24.point_apply_zero]
      rw [abs_of_pos (by linarith)]
      linarith

/-- The corresponding third away vertex has the same strict horizontal
gap in the common chart. -/
lemma commonFrame_away_third_fst_gap_gt_two
    (F : P.FlatAlignedFrameData)
    (source : {p // p ∈ P.H}) (middle : Vertex A)
    (T : TwoExtremeCyclicWitness P source middle)
    (N : ActualCase24Rows.TwoExtremeNormalizedFrame source middle T)
    (E : ActualCase24Rows.TwoExtremeCommonPairFrame source middle T)
    (hi : P.IsFlat source) :
    2 < |(E.frame.toCanonical middle) 0 -
      (E.frame.toCanonical
        (Erdos957Case4NoThree.awayHullVertex P source T.side 2).1) 0| := by
  have hx := Erdos957Case4NoThree.normalizedFrame_away_third_fst_gt_five_halves
    F source middle T N hi
  have hm : E.frame.toCanonical middle = Erdos957Cases24.Case2.v := by
    simpa [ActualCase24Rows.TwoExtremeCommonPairFrame.frame] using
      E.middle_coordinate
  cases hside : T.side with
  | previous =>
      have hcoord :
          N.frame.toCanonical
              (Erdos957Case4NoThree.awayHullVertex P source T.side 2).1 =
            E.frame.toCanonical
              (Erdos957Case4NoThree.awayHullVertex P source T.side 2).1 := by
        cases N.frame_spec with
        | previous hs hunit hframe =>
            rw [hframe]
            simp [ActualCase24Rows.TwoExtremeCommonPairFrame.frame,
              ActualCase24Rows.case4PairEdgeBase, hside]
        | next hs hunit hframe => simp [hside] at hs
      simp only [Fin.isValue, gt_iff_lt] at hx hcoord ⊢
      rw [hcoord] at hx
      rw [hm]
      simp only [Erdos957Cases24.Case2.v,
        Erdos957Cases24.point_apply_zero]
      rw [abs_of_neg (by linarith)]
      linarith
  | next =>
      have hcoord :
          (N.frame.toCanonical
            (Erdos957Case4NoThree.awayHullVertex P source T.side 2).1) 0 =
            -(E.frame.toCanonical
              (Erdos957Case4NoThree.awayHullVertex P source T.side 2).1) 0 - 1 := by
        cases N.frame_spec with
        | previous hs hunit hframe => simp [hside] at hs
        | next hs hunit hframe =>
            rw [hframe]
            simp [Erdos957TwoExtremeAligned.reflectedSuccessorUnitEdgeRigidChart,
              Equiv.trans_apply, Erdos957TwoExtremeAligned.swapEndpointEquiv_apply,
              Erdos957TwoExtremeAligned.swapEndpointCoord_apply_zero,
              ActualCase24Rows.TwoExtremeCommonPairFrame.frame,
              ActualCase24Rows.case4PairEdgeBase, hside]
      simp only [Fin.isValue, gt_iff_lt] at hx hcoord ⊢
      rw [hm]
      simp only [Erdos957Cases24.Case2.v,
        Erdos957Cases24.point_apply_zero]
      rw [abs_of_pos (by linarith)]
      linarith

/-- The third vertex continuing through the incident endpoint is likewise
more than two horizontal units from the Case-4 middle in the common chart. -/
lemma commonFrame_incident_third_fst_gap_gt_two
    (F : P.FlatAlignedFrameData)
    (source : {p // p ∈ P.H}) (middle : Vertex A)
    (T : TwoExtremeCyclicWitness P source middle)
    (N : ActualCase24Rows.TwoExtremeNormalizedFrame source middle T)
    (E : ActualCase24Rows.TwoExtremeCommonPairFrame source middle T)
    (hi : P.IsFlat source) :
    2 < |(E.frame.toCanonical middle) 0 -
      (E.frame.toCanonical
        (incidentContinuationHullVertex P source T.side 2).1) 0| := by
  have hx := Erdos957Case4NoThree.normalizedFrame_incident_third_fst_lt_neg_five_halves
    F source middle T N hi
  have hm : E.frame.toCanonical middle = Erdos957Cases24.Case2.v := by
    simpa [ActualCase24Rows.TwoExtremeCommonPairFrame.frame] using
      E.middle_coordinate
  cases hside : T.side with
  | previous =>
      have hcoord :
          N.frame.toCanonical
              (incidentContinuationHullVertex P source T.side 2).1 =
            E.frame.toCanonical
              (incidentContinuationHullVertex P source T.side 2).1 := by
        cases N.frame_spec with
        | previous hs hunit hframe =>
            rw [hframe]
            simp [incidentContinuationHullVertex,
              ActualCase24Rows.TwoExtremeCommonPairFrame.frame,
              ActualCase24Rows.case4PairEdgeBase, hside,
              Erdos957Case4NoThree.incidentHullVertex]
        | next hs hunit hframe => simp [hside] at hs
      simp only [Fin.isValue, gt_iff_lt] at hx hcoord ⊢
      rw [hcoord] at hx
      rw [hm]
      simp only [Erdos957Cases24.Case2.v,
        Erdos957Cases24.point_apply_zero]
      rw [abs_of_pos (by linarith)]
      linarith
  | next =>
      have hcoord :
          (N.frame.toCanonical
            (incidentContinuationHullVertex P source T.side 2).1) 0 =
            -(E.frame.toCanonical
              (incidentContinuationHullVertex P source T.side 2).1) 0 - 1 := by
        cases N.frame_spec with
        | previous hs hunit hframe => simp [hside] at hs
        | next hs hunit hframe =>
            rw [hframe]
            simp [incidentContinuationHullVertex,
              Erdos957Case4NoThree.incidentHullVertex,
              Erdos957TwoExtremeAligned.reflectedSuccessorUnitEdgeRigidChart,
              Equiv.trans_apply, Erdos957TwoExtremeAligned.swapEndpointEquiv_apply,
              Erdos957TwoExtremeAligned.swapEndpointCoord_apply_zero,
              ActualCase24Rows.TwoExtremeCommonPairFrame.frame,
              ActualCase24Rows.case4PairEdgeBase, hside]
      simp only [Fin.isValue, gt_iff_lt] at hx hcoord ⊢
      rw [hm]
      simp only [Erdos957Cases24.Case2.v,
        Erdos957Cases24.point_apply_zero]
      rw [abs_of_neg (by linarith)]
      linarith

/-- A direct arrival from the second away hull source cannot hit the
coherently retained split-right recipient. -/
theorem CommonPairedCase4Rows.not_direct_away_second
    (F : P.FlatAlignedFrameData)
    {C : P.AlignedChartData}
    {rows : HasRealizedSourceRows P W C}
    {u : Vertex A} {hu : u ∈ sourceVertices P W}
    (Q : CommonPairedCase4Rows rows u hu)
    (hi : P.IsFlat (sourceIndex P W u hu)) :
    ¬ (unitDistanceGraph A).Adj
      (Erdos957Case4NoThree.awayHullVertex P
        (sourceIndex P W u hu) Q.twoExtreme.side 1).1
      Q.currentSecondaryTarget.vertex := by
  intro hadj
  apply Erdos957ExceptionalCollisionGeometry.no_common_unit_target_of_rigid_fst_gap_gt_two
    Q.commonFrame.frame
    (middle := Q.middle)
    (competitor := (Erdos957Case4NoThree.awayHullVertex P
      (sourceIndex P W u hu) Q.twoExtreme.side 1).1)
    (target := Q.currentSecondaryTarget.vertex)
  · rw [Q.current_secondary_vertex]
    change dist (Q.middle : Point) (Q.pairBranch.actualRecipient
      (ActualCase24Rows.case4SourceIsRight Q.twoExtreme) : Point) = 1
    let b := ActualCase24Rows.case4SourceIsRight Q.twoExtreme
    let q := Q.pairBranch.branch.sourceRecipient b
    have hq : dist Erdos957Cases24.Case2.v q = 1 := by
      simpa [Erdos957Cases24.Case4.v] using
        (Erdos957Case24Bridge.Case4.mem_residualNeighbors.mp
          (Q.pairBranch.branch.sourceRecipient_mem b)).2.1
    calc
      dist (Q.middle : Point) (Q.pairBranch.actualRecipient b : Point) =
          dist (Q.commonFrame.frame.toCanonical Q.middle)
            (Q.commonFrame.frame.toCanonical
              (Q.pairBranch.actualRecipient b)) :=
        (Q.commonFrame.frame.dist_eq _ _).symm
      _ = dist Erdos957Cases24.Case2.v q := by
        rw [show Q.commonFrame.frame.toCanonical Q.middle =
          Erdos957Cases24.Case2.v by
            simpa [ActualCase24Rows.TwoExtremeCommonPairFrame.frame] using
              Q.commonFrame.middle_coordinate]
        simp [q, b, CommonCase4.CommonCase4HullPairBranch.actualRecipient]
      _ = 1 := hq
  · exact hadj
  · exact commonFrame_away_second_fst_gap_gt_two
      F (sourceIndex P W u hu) Q.middle Q.twoExtreme Q.normalized
        Q.commonFrame hi

/-- A direct arrival from the third away hull source cannot hit the
coherently retained split-right recipient. -/
theorem CommonPairedCase4Rows.not_direct_away_third
    (F : P.FlatAlignedFrameData)
    {C : P.AlignedChartData}
    {rows : HasRealizedSourceRows P W C}
    {u : Vertex A} {hu : u ∈ sourceVertices P W}
    (Q : CommonPairedCase4Rows rows u hu)
    (hi : P.IsFlat (sourceIndex P W u hu)) :
    ¬ (unitDistanceGraph A).Adj
      (Erdos957Case4NoThree.awayHullVertex P
        (sourceIndex P W u hu) Q.twoExtreme.side 2).1
      Q.currentSecondaryTarget.vertex := by
  intro hadj
  apply Erdos957ExceptionalCollisionGeometry.no_common_unit_target_of_rigid_fst_gap_gt_two
    Q.commonFrame.frame
    (middle := Q.middle)
    (competitor := (Erdos957Case4NoThree.awayHullVertex P
      (sourceIndex P W u hu) Q.twoExtreme.side 2).1)
    (target := Q.currentSecondaryTarget.vertex)
  · rw [Q.current_secondary_vertex]
    let b := ActualCase24Rows.case4SourceIsRight Q.twoExtreme
    let q := Q.pairBranch.branch.sourceRecipient b
    have hq : dist Erdos957Cases24.Case2.v q = 1 := by
      simpa [Erdos957Cases24.Case4.v] using
        (Erdos957Case24Bridge.Case4.mem_residualNeighbors.mp
          (Q.pairBranch.branch.sourceRecipient_mem b)).2.1
    calc
      dist (Q.middle : Point) (Q.pairBranch.actualRecipient b : Point) =
          dist (Q.commonFrame.frame.toCanonical Q.middle)
            (Q.commonFrame.frame.toCanonical
              (Q.pairBranch.actualRecipient b)) :=
        (Q.commonFrame.frame.dist_eq _ _).symm
      _ = dist Erdos957Cases24.Case2.v q := by
        rw [show Q.commonFrame.frame.toCanonical Q.middle =
          Erdos957Cases24.Case2.v by
            simpa [ActualCase24Rows.TwoExtremeCommonPairFrame.frame] using
              Q.commonFrame.middle_coordinate]
        simp [q, b, CommonCase4.CommonCase4HullPairBranch.actualRecipient]
      _ = 1 := hq
  · exact hadj
  · exact commonFrame_away_third_fst_gap_gt_two
      F (sourceIndex P W u hu) Q.middle Q.twoExtreme Q.normalized
        Q.commonFrame hi

/-- A direct arrival from the third hull source continuing through the
incident endpoint cannot hit the coherently retained split-right recipient. -/
theorem CommonPairedCase4Rows.not_direct_incident_third
    (F : P.FlatAlignedFrameData)
    {C : P.AlignedChartData}
    {rows : HasRealizedSourceRows P W C}
    {u : Vertex A} {hu : u ∈ sourceVertices P W}
    (Q : CommonPairedCase4Rows rows u hu)
    (hi : P.IsFlat (sourceIndex P W u hu)) :
    ¬ (unitDistanceGraph A).Adj
      (incidentContinuationHullVertex P
        (sourceIndex P W u hu) Q.twoExtreme.side 2).1
      Q.currentSecondaryTarget.vertex := by
  intro hadj
  apply Erdos957ExceptionalCollisionGeometry.no_common_unit_target_of_rigid_fst_gap_gt_two
    Q.commonFrame.frame
    (middle := Q.middle)
    (competitor := (incidentContinuationHullVertex P
      (sourceIndex P W u hu) Q.twoExtreme.side 2).1)
    (target := Q.currentSecondaryTarget.vertex)
  · rw [Q.current_secondary_vertex]
    let b := ActualCase24Rows.case4SourceIsRight Q.twoExtreme
    let q := Q.pairBranch.branch.sourceRecipient b
    have hq : dist Erdos957Cases24.Case2.v q = 1 := by
      simpa [Erdos957Cases24.Case4.v] using
        (Erdos957Case24Bridge.Case4.mem_residualNeighbors.mp
          (Q.pairBranch.branch.sourceRecipient_mem b)).2.1
    calc
      dist (Q.middle : Point) (Q.pairBranch.actualRecipient b : Point) =
          dist (Q.commonFrame.frame.toCanonical Q.middle)
            (Q.commonFrame.frame.toCanonical
              (Q.pairBranch.actualRecipient b)) :=
        (Q.commonFrame.frame.dist_eq _ _).symm
      _ = dist Erdos957Cases24.Case2.v q := by
        rw [show Q.commonFrame.frame.toCanonical Q.middle =
          Erdos957Cases24.Case2.v by
            simpa [ActualCase24Rows.TwoExtremeCommonPairFrame.frame] using
              Q.commonFrame.middle_coordinate]
        simp [q, b, CommonCase4.CommonCase4HullPairBranch.actualRecipient]
      _ = 1 := hq
  · exact hadj
  · exact commonFrame_incident_third_fst_gap_gt_two
      F (sourceIndex P W u hu) Q.middle Q.twoExtreme Q.normalized
        Q.commonFrame hi

/-- The incident hull partner cannot contribute a direct arrival to the
current split-right recipient.  If that endpoint is an emitter, global row
coherence identifies its direct split-left target with the common middle;
the selected branch recipient is different from that middle. -/
theorem realized_no_direct_competitor_at_incident_partner
    (Q : CommonCoherentRealizedSourceRows P W F.chart)
    {s t : Source P W} {v : Vertex A}
    (Ds : RealizedPositiveTarget (Q.rows s.1 s.property) v)
    (Dt : RealizedPositiveTarget (Q.rows t.1 t.property) v)
    (hsrole : Ds.role = PairCases.TargetRoleName.case4SplitRight)
    (htdirect : IsDirectTargetRole Dt.role)
    (htIndex : sourceIndex P W t.1 t.property =
      incidentContinuationHullVertex P
        (sourceIndex P W s.1 s.property)
        (Q.case4_pair s.1 s.property
          ⟨Ds.target, by simpa [hsrole] using Ds.target_at_role⟩).twoExtreme.side 0) :
    False := by
  let Qs := Q.case4_pair s.1 s.property
    ⟨Ds.target, by simpa [hsrole] using Ds.target_at_role⟩
  change sourceIndex P W t.1 t.property =
    incidentContinuationHullVertex P
      (sourceIndex P W s.1 s.property) Qs.twoExtreme.side 0 at htIndex
  have htPartner : t.1 = cyclicSideVertex P
      (sourceIndex P W s.1 s.property) Qs.twoExtreme.side := by
    have h := congrArg Subtype.val htIndex
    cases hside : Qs.twoExtreme.side <;>
      simpa [sourceIndex, incidentContinuationHullVertex,
        cyclicSideVertex, hside] using h
  have hp : cyclicSideVertex P (sourceIndex P W s.1 s.property)
      Qs.twoExtreme.side ∈ sourceVertices P W := by
    rw [← htPartner]
    exact t.property
  have htSource : t =
      ⟨cyclicSideVertex P (sourceIndex P W s.1 s.property)
        Qs.twoExtreme.side, hp⟩ := by
    apply Subtype.ext
    exact htPartner
  subst t
  rcases Qs.partner_absent_or_coherent with habsent | hcoherent
  · exact (habsent hp).elim
  obtain ⟨partnerMiddleTarget, partnerSecondaryTarget,
      hpartnerMiddleRole, hpartnerSecondaryRole,
      hpartnerMiddleVertex, hpartnerSecondaryVertex,
      _hpartnerSecondaryAssociation⟩ := hcoherent hp
  have htTarget : Dt.target = partnerMiddleTarget :=
    direct_target_eq_splitLeft_of_split_roles Dt htdirect
      hpartnerMiddleRole hpartnerSecondaryRole
  have hsTarget : Ds.target = Qs.currentSecondaryTarget := by
    apply Option.some.inj
    rw [← Ds.target_at_role, hsrole, Qs.current_secondary_role]
  apply CommonPairedCase4Rows.currentSecondary_ne_middle Qs
  calc
    Qs.currentSecondaryTarget.vertex = Ds.target.vertex :=
      congrArg LocalTarget.vertex hsTarget.symm
    _ = v := Ds.vertex_eq.symm
    _ = Dt.target.vertex := Dt.vertex_eq
    _ = partnerMiddleTarget.vertex := congrArg LocalTarget.vertex htTarget
    _ = Qs.middle := hpartnerMiddleVertex

/-- Conditional legacy side-enum form of the incident-partner statement.
The recipient-relative Case-4 association is no longer definitionally the
two-extreme side: callers which have independently identified both labels
with their cyclic-side enums may still use this geometric endpoint lemma. -/
theorem split_right_associations_ne_at_incident_partner
    (hA : IsOneSeparated A)
    (Q : CommonCoherentRealizedSourceRows P W F.chart)
    {s t : Source P W} {v : Vertex A}
    (S : RealizedArrivalAt (F := F) Q.rows s v)
    (T : RealizedArrivalAt (F := F) Q.rows t v)
    (hsRole : S.target.role = PairCases.TargetRoleName.case4SplitRight)
    (htRole : T.target.role = PairCases.TargetRoleName.case4SplitRight)
    (htIndex : sourceIndex P W t.1 t.property =
      incidentContinuationHullVertex P
        (sourceIndex P W s.1 s.property)
        (Q.case4_pair s.1 s.property
          ⟨S.target.target, by simpa [hsRole] using S.target.target_at_role⟩).twoExtreme.side 0)
    (hSAssoc : S.descriptor.association =
      cyclicSideAssociation
        (Q.case4_pair s.1 s.property
          ⟨S.target.target, by simpa [hsRole] using S.target.target_at_role⟩).twoExtreme.side)
    (hTAssoc : T.descriptor.association =
      cyclicSideAssociation
        (Q.case4_pair t.1 t.property
          ⟨T.target.target, by simpa [htRole] using T.target.target_at_role⟩).twoExtreme.side) :
    S.descriptor.association ≠ T.descriptor.association := by
  let Qs := Q.case4_pair s.1 s.property
    ⟨S.target.target, by simpa [hsRole] using S.target.target_at_role⟩
  change sourceIndex P W t.1 t.property =
    incidentContinuationHullVertex P
      (sourceIndex P W s.1 s.property) Qs.twoExtreme.side 0 at htIndex
  have htPartner : t.1 = cyclicSideVertex P
      (sourceIndex P W s.1 s.property) Qs.twoExtreme.side := by
    have h := congrArg Subtype.val htIndex
    cases hside : Qs.twoExtreme.side <;>
      simpa [sourceIndex, incidentContinuationHullVertex,
        cyclicSideVertex, hside] using h
  have hp : cyclicSideVertex P (sourceIndex P W s.1 s.property)
      Qs.twoExtreme.side ∈ sourceVertices P W := by
    rw [← htPartner]
    exact t.property
  have htSource : t =
      ⟨cyclicSideVertex P (sourceIndex P W s.1 s.property)
        Qs.twoExtreme.side, hp⟩ := by
    apply Subtype.ext
    exact htPartner
  subst t
  let Qt := Q.case4_pair
    (cyclicSideVertex P (sourceIndex P W s.1 s.property) Qs.twoExtreme.side)
    hp ⟨T.target.target, by simpa [htRole] using T.target.target_at_role⟩
  rcases Qs.partner_absent_or_coherent with habsent | hcoherent
  · exact (habsent hp).elim
  obtain ⟨partnerMiddleTarget, partnerSecondaryTarget,
      hpartnerMiddleRole, hpartnerSecondaryRole,
      hpartnerMiddleVertex, hpartnerSecondaryVertex,
      _hpartnerSecondaryAssociation⟩ := hcoherent hp
  have hmiddleTargets : Qt.currentMiddleTarget = partnerMiddleTarget := by
    apply Option.some.inj
    rw [← Qt.current_middle_role, hpartnerMiddleRole]
  have hmiddles : Qt.middle = Qs.middle := by
    calc
      Qt.middle = Qt.currentMiddleTarget.vertex := Qt.current_middle_vertex.symm
      _ = partnerMiddleTarget.vertex := congrArg LocalTarget.vertex hmiddleTargets
      _ = Qs.middle := hpartnerMiddleVertex
  have hsMem : (sourceIndex P W s.1 s.property).1 ∈ sourceVertices P W := by
    simpa [sourceIndex] using s.property
  have hsMiddle : (unitDistanceGraph A).Adj
      (sourceIndex P W s.1 s.property).1 Qs.middle := by
    have hm : (sourceIndex P W s.1 s.property).1 ∈
        hullUnitNeighbors P Qs.middle := by
      rw [Qs.twoExtreme.neighbors_eq]
      simp
    exact (mem_hullUnitNeighbors.mp hm).2.symm
  have hside := partner_case4SourceIsRight_eq_not_of_middle_eq hA W
    (sourceIndex P W s.1 s.property) hsMem Qs.middle Qt.middle
    hmiddles hsMiddle Qs.twoExtreme hp Qt.twoExtreme
  rw [hSAssoc, hTAssoc]
  intro hassoc
  have hsides : Qs.twoExtreme.side = Qt.twoExtreme.side :=
    cyclicSideAssociation_injective hassoc
  have hself : ActualCase24Rows.case4SourceIsRight Qt.twoExtreme =
      !(ActualCase24Rows.case4SourceIsRight Qt.twoExtreme) := by
    simpa [ActualCase24Rows.case4SourceIsRight, hsides] using hside
  cases hb : ActualCase24Rows.case4SourceIsRight Qt.twoExtreme <;>
    simp [hb] at hself

/-- Realized-row form of the second-away exclusion.  It uses the exact
split-right slot selected by the coherent family and the formula-derived
direct incidence of the competing row. -/
theorem realized_no_direct_competitor_at_away_second
    (Q : CommonCoherentRealizedSourceRows P W F.chart)
    {s t : Source P W} {v : Vertex A}
    (Ds : RealizedPositiveTarget (Q.rows s.1 s.property) v)
    (Dt : RealizedPositiveTarget (Q.rows t.1 t.property) v)
    (hsrole : Ds.role = PairCases.TargetRoleName.case4SplitRight)
    (htCase2 : Dt.role ≠ PairCases.TargetRoleName.case2Secondary)
    (htCase4 : Dt.role ≠ PairCases.TargetRoleName.case4SplitRight)
    (htIndex : sourceIndex P W t.1 t.property =
      Erdos957Case4NoThree.awayHullVertex P
        (sourceIndex P W s.1 s.property)
        (Q.case4_pair s.1 s.property
          ⟨Ds.target, by simpa [hsrole] using Ds.target_at_role⟩).twoExtreme.side 1) :
    False := by
  let Qs := Q.case4_pair s.1 s.property
    ⟨Ds.target, by simpa [hsrole] using Ds.target_at_role⟩
  have hslot : Ds.target = Qs.currentSecondaryTarget := by
    apply Option.some.inj
    rw [← Ds.target_at_role, hsrole, Qs.current_secondary_role]
  have hv : v = Qs.currentSecondaryTarget.vertex := by
    calc
      v = Ds.target.vertex := Ds.vertex_eq
      _ = Qs.currentSecondaryTarget.vertex := congrArg LocalTarget.vertex hslot
  have hadj := Dt.direct_target_adj htCase2 htCase4
  change sourceIndex P W t.1 t.property =
    Erdos957Case4NoThree.awayHullVertex P
      (sourceIndex P W s.1 s.property) Qs.twoExtreme.side 1 at htIndex
  rw [htIndex, hv] at hadj
  exact Erdos957Case4CollisionLeaves.CommonPairedCase4Rows.not_direct_away_second F Qs
    (Erdos957GeometryLocalityBridge.sourceIndex_isFlat W s) hadj

/-- Realized-row form of the third-away exclusion. -/
theorem realized_no_direct_competitor_at_away_third
    (Q : CommonCoherentRealizedSourceRows P W F.chart)
    {s t : Source P W} {v : Vertex A}
    (Ds : RealizedPositiveTarget (Q.rows s.1 s.property) v)
    (Dt : RealizedPositiveTarget (Q.rows t.1 t.property) v)
    (hsrole : Ds.role = PairCases.TargetRoleName.case4SplitRight)
    (htCase2 : Dt.role ≠ PairCases.TargetRoleName.case2Secondary)
    (htCase4 : Dt.role ≠ PairCases.TargetRoleName.case4SplitRight)
    (htIndex : sourceIndex P W t.1 t.property =
      Erdos957Case4NoThree.awayHullVertex P
        (sourceIndex P W s.1 s.property)
        (Q.case4_pair s.1 s.property
          ⟨Ds.target, by simpa [hsrole] using Ds.target_at_role⟩).twoExtreme.side 2) :
    False := by
  let Qs := Q.case4_pair s.1 s.property
    ⟨Ds.target, by simpa [hsrole] using Ds.target_at_role⟩
  have hslot : Ds.target = Qs.currentSecondaryTarget := by
    apply Option.some.inj
    rw [← Ds.target_at_role, hsrole, Qs.current_secondary_role]
  have hv : v = Qs.currentSecondaryTarget.vertex := by
    calc
      v = Ds.target.vertex := Ds.vertex_eq
      _ = Qs.currentSecondaryTarget.vertex := congrArg LocalTarget.vertex hslot
  have hadj := Dt.direct_target_adj htCase2 htCase4
  change sourceIndex P W t.1 t.property =
    Erdos957Case4NoThree.awayHullVertex P
      (sourceIndex P W s.1 s.property) Qs.twoExtreme.side 2 at htIndex
  rw [htIndex, hv] at hadj
  exact Erdos957Case4CollisionLeaves.CommonPairedCase4Rows.not_direct_away_third F Qs
    (Erdos957GeometryLocalityBridge.sourceIndex_isFlat W s) hadj

/-- Realized-row form of the third-incident-continuation exclusion. -/
theorem realized_no_direct_competitor_at_incident_third
    (Q : CommonCoherentRealizedSourceRows P W F.chart)
    {s t : Source P W} {v : Vertex A}
    (Ds : RealizedPositiveTarget (Q.rows s.1 s.property) v)
    (Dt : RealizedPositiveTarget (Q.rows t.1 t.property) v)
    (hsrole : Ds.role = PairCases.TargetRoleName.case4SplitRight)
    (htCase2 : Dt.role ≠ PairCases.TargetRoleName.case2Secondary)
    (htCase4 : Dt.role ≠ PairCases.TargetRoleName.case4SplitRight)
    (htIndex : sourceIndex P W t.1 t.property =
      incidentContinuationHullVertex P
        (sourceIndex P W s.1 s.property)
        (Q.case4_pair s.1 s.property
          ⟨Ds.target, by simpa [hsrole] using Ds.target_at_role⟩).twoExtreme.side 2) :
    False := by
  let Qs := Q.case4_pair s.1 s.property
    ⟨Ds.target, by simpa [hsrole] using Ds.target_at_role⟩
  have hslot : Ds.target = Qs.currentSecondaryTarget := by
    apply Option.some.inj
    rw [← Ds.target_at_role, hsrole, Qs.current_secondary_role]
  have hv : v = Qs.currentSecondaryTarget.vertex := by
    calc
      v = Ds.target.vertex := Ds.vertex_eq
      _ = Qs.currentSecondaryTarget.vertex := congrArg LocalTarget.vertex hslot
  have hadj := Dt.direct_target_adj htCase2 htCase4
  change sourceIndex P W t.1 t.property =
    incidentContinuationHullVertex P
      (sourceIndex P W s.1 s.property) Qs.twoExtreme.side 2 at htIndex
  rw [htIndex, hv] at hadj
  exact Erdos957Case4CollisionLeaves.CommonPairedCase4Rows.not_direct_incident_third
    F Qs (Erdos957GeometryLocalityBridge.sourceIndex_isFlat W s) hadj

/-- After the checked horizontal-gap exclusions, a direct competitor in
the genuine seven-window is reduced to four near slots: the incident
partner, the next two continuations through it, or the first away vertex.
This is the exact finite residual consumed by the remaining Case-4
collision argument. -/
theorem direct_competitor_reduces_to_near_four
    (Q : CommonCoherentRealizedSourceRows P W F.chart)
    {s t : Source P W} {v : Vertex A}
    (Ds : RealizedPositiveTarget (Q.rows s.1 s.property) v)
    (Dt : RealizedPositiveTarget (Q.rows t.1 t.property) v)
    (hsrole : Ds.role = PairCases.TargetRoleName.case4SplitRight)
    (htCase2 : Dt.role ≠ PairCases.TargetRoleName.case2Secondary)
    (htCase4 : Dt.role ≠ PairCases.TargetRoleName.case4SplitRight)
    (htWindow : t.1 ∈ Finset.univ.image (fun j : Fin 7 ↦
      (sevenShift P.next j (sourceIndex P W s.1 s.property)).1))
    (hst : s ≠ t) :
    let side := (Q.case4_pair s.1 s.property
      ⟨Ds.target, by simpa [hsrole] using Ds.target_at_role⟩).twoExtreme.side
    sourceIndex P W t.1 t.property =
        incidentContinuationHullVertex P
          (sourceIndex P W s.1 s.property) side 0 ∨
      sourceIndex P W t.1 t.property =
        incidentContinuationHullVertex P
          (sourceIndex P W s.1 s.property) side 1 ∨
      sourceIndex P W t.1 t.property =
        incidentContinuationHullVertex P
          (sourceIndex P W s.1 s.property) side 2 ∨
      sourceIndex P W t.1 t.property =
        Erdos957Case4NoThree.awayHullVertex P
          (sourceIndex P W s.1 s.property) side 0 := by
  let Qs := Q.case4_pair s.1 s.property
    ⟨Ds.target, by simpa [hsrole] using Ds.target_at_role⟩
  change sourceIndex P W t.1 t.property =
        incidentContinuationHullVertex P
          (sourceIndex P W s.1 s.property) Qs.twoExtreme.side 0 ∨
      sourceIndex P W t.1 t.property =
        incidentContinuationHullVertex P
          (sourceIndex P W s.1 s.property) Qs.twoExtreme.side 1 ∨
      sourceIndex P W t.1 t.property =
        incidentContinuationHullVertex P
          (sourceIndex P W s.1 s.property) Qs.twoExtreme.side 2 ∨
      sourceIndex P W t.1 t.property =
        Erdos957Case4NoThree.awayHullVertex P
          (sourceIndex P W s.1 s.property) Qs.twoExtreme.side 0
  have horbits :=
    Erdos957ExceptionalWindowDispatch.sourceIndex_orbit_cases_of_mem_seven_window
      htWindow hst
  cases hside : Qs.twoExtreme.side with
  | previous =>
      rcases horbits with h | h | h | h | h | h
      · exact Or.inr (Or.inr (Or.inl (by
          simpa [incidentContinuationHullVertex, hside] using h)))
      · exact Or.inr (Or.inl (by
          simpa [incidentContinuationHullVertex, hside] using h))
      · exact Or.inl (by
          simpa [incidentContinuationHullVertex, hside] using h)
      · exact Or.inr (Or.inr (Or.inr (by
          simpa [Erdos957Case4NoThree.awayHullVertex, hside] using h)))
      · exfalso
        apply realized_no_direct_competitor_at_away_second
          Q Ds Dt hsrole htCase2 htCase4
        change sourceIndex P W t.1 t.property =
          Erdos957Case4NoThree.awayHullVertex P
            (sourceIndex P W s.1 s.property) Qs.twoExtreme.side 1
        simpa [Erdos957Case4NoThree.awayHullVertex, hside] using h
      · exfalso
        apply realized_no_direct_competitor_at_away_third
          Q Ds Dt hsrole htCase2 htCase4
        change sourceIndex P W t.1 t.property =
          Erdos957Case4NoThree.awayHullVertex P
            (sourceIndex P W s.1 s.property) Qs.twoExtreme.side 2
        simpa [Erdos957Case4NoThree.awayHullVertex, hside] using h
  | next =>
      rcases horbits with h | h | h | h | h | h
      · exfalso
        apply realized_no_direct_competitor_at_away_third
          Q Ds Dt hsrole htCase2 htCase4
        change sourceIndex P W t.1 t.property =
          Erdos957Case4NoThree.awayHullVertex P
            (sourceIndex P W s.1 s.property) Qs.twoExtreme.side 2
        simpa [Erdos957Case4NoThree.awayHullVertex, hside] using h
      · exfalso
        apply realized_no_direct_competitor_at_away_second
          Q Ds Dt hsrole htCase2 htCase4
        change sourceIndex P W t.1 t.property =
          Erdos957Case4NoThree.awayHullVertex P
            (sourceIndex P W s.1 s.property) Qs.twoExtreme.side 1
        simpa [Erdos957Case4NoThree.awayHullVertex, hside] using h
      · exact Or.inr (Or.inr (Or.inr (by
          simpa [Erdos957Case4NoThree.awayHullVertex, hside] using h)))
      · exact Or.inl (by
          simpa [incidentContinuationHullVertex, hside] using h)
      · exact Or.inr (Or.inl (by
          simpa [incidentContinuationHullVertex, hside] using h))
      · exact Or.inr (Or.inr (Or.inl (by
          simpa [incidentContinuationHullVertex, hside] using h)))

/-- Adding the checked third-incident horizontal-gap exclusion leaves only
the incident partner, the next continuation, or the first away vertex. -/
theorem direct_competitor_reduces_to_near_three
    (Q : CommonCoherentRealizedSourceRows P W F.chart)
    {s t : Source P W} {v : Vertex A}
    (Ds : RealizedPositiveTarget (Q.rows s.1 s.property) v)
    (Dt : RealizedPositiveTarget (Q.rows t.1 t.property) v)
    (hsrole : Ds.role = PairCases.TargetRoleName.case4SplitRight)
    (htCase2 : Dt.role ≠ PairCases.TargetRoleName.case2Secondary)
    (htCase4 : Dt.role ≠ PairCases.TargetRoleName.case4SplitRight)
    (htWindow : t.1 ∈ Finset.univ.image (fun j : Fin 7 ↦
      (sevenShift P.next j (sourceIndex P W s.1 s.property)).1))
    (hst : s ≠ t) :
    let side := (Q.case4_pair s.1 s.property
      ⟨Ds.target, by simpa [hsrole] using Ds.target_at_role⟩).twoExtreme.side
    sourceIndex P W t.1 t.property =
        incidentContinuationHullVertex P
          (sourceIndex P W s.1 s.property) side 0 ∨
      sourceIndex P W t.1 t.property =
        incidentContinuationHullVertex P
          (sourceIndex P W s.1 s.property) side 1 ∨
      sourceIndex P W t.1 t.property =
        Erdos957Case4NoThree.awayHullVertex P
          (sourceIndex P W s.1 s.property) side 0 := by
  let Qs := Q.case4_pair s.1 s.property
    ⟨Ds.target, by simpa [hsrole] using Ds.target_at_role⟩
  change sourceIndex P W t.1 t.property =
        incidentContinuationHullVertex P
          (sourceIndex P W s.1 s.property) Qs.twoExtreme.side 0 ∨
      sourceIndex P W t.1 t.property =
        incidentContinuationHullVertex P
          (sourceIndex P W s.1 s.property) Qs.twoExtreme.side 1 ∨
      sourceIndex P W t.1 t.property =
        Erdos957Case4NoThree.awayHullVertex P
          (sourceIndex P W s.1 s.property) Qs.twoExtreme.side 0
  have hfour := direct_competitor_reduces_to_near_four
    Q Ds Dt hsrole htCase2 htCase4 htWindow hst
  change sourceIndex P W t.1 t.property =
        incidentContinuationHullVertex P
          (sourceIndex P W s.1 s.property) Qs.twoExtreme.side 0 ∨
      sourceIndex P W t.1 t.property =
        incidentContinuationHullVertex P
          (sourceIndex P W s.1 s.property) Qs.twoExtreme.side 1 ∨
      sourceIndex P W t.1 t.property =
        incidentContinuationHullVertex P
          (sourceIndex P W s.1 s.property) Qs.twoExtreme.side 2 ∨
      sourceIndex P W t.1 t.property =
        Erdos957Case4NoThree.awayHullVertex P
          (sourceIndex P W s.1 s.property) Qs.twoExtreme.side 0 at hfour
  rcases hfour with h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exfalso
    exact realized_no_direct_competitor_at_incident_third
      Q Ds Dt hsrole htCase2 htCase4 h
  · exact Or.inr (Or.inr h)

/-- Coherence eliminates the incident partner from the three-slot result.
A direct competitor can therefore only be the next continuation through
that partner or the first hull vertex on the opposite side. -/
theorem direct_competitor_reduces_to_near_two
    (Q : CommonCoherentRealizedSourceRows P W F.chart)
    {s t : Source P W} {v : Vertex A}
    (Ds : RealizedPositiveTarget (Q.rows s.1 s.property) v)
    (Dt : RealizedPositiveTarget (Q.rows t.1 t.property) v)
    (hsrole : Ds.role = PairCases.TargetRoleName.case4SplitRight)
    (htCase2 : Dt.role ≠ PairCases.TargetRoleName.case2Secondary)
    (htCase4 : Dt.role ≠ PairCases.TargetRoleName.case4SplitRight)
    (htWindow : t.1 ∈ Finset.univ.image (fun j : Fin 7 ↦
      (sevenShift P.next j (sourceIndex P W s.1 s.property)).1))
    (hst : s ≠ t) :
    let side := (Q.case4_pair s.1 s.property
      ⟨Ds.target, by simpa [hsrole] using Ds.target_at_role⟩).twoExtreme.side
    sourceIndex P W t.1 t.property =
        incidentContinuationHullVertex P
          (sourceIndex P W s.1 s.property) side 1 ∨
      sourceIndex P W t.1 t.property =
        Erdos957Case4NoThree.awayHullVertex P
          (sourceIndex P W s.1 s.property) side 0 := by
  let Qs := Q.case4_pair s.1 s.property
    ⟨Ds.target, by simpa [hsrole] using Ds.target_at_role⟩
  change sourceIndex P W t.1 t.property =
        incidentContinuationHullVertex P
          (sourceIndex P W s.1 s.property) Qs.twoExtreme.side 1 ∨
      sourceIndex P W t.1 t.property =
        Erdos957Case4NoThree.awayHullVertex P
          (sourceIndex P W s.1 s.property) Qs.twoExtreme.side 0
  have hthree := direct_competitor_reduces_to_near_three
    Q Ds Dt hsrole htCase2 htCase4 htWindow hst
  change sourceIndex P W t.1 t.property =
        incidentContinuationHullVertex P
          (sourceIndex P W s.1 s.property) Qs.twoExtreme.side 0 ∨
      sourceIndex P W t.1 t.property =
        incidentContinuationHullVertex P
          (sourceIndex P W s.1 s.property) Qs.twoExtreme.side 1 ∨
      sourceIndex P W t.1 t.property =
        Erdos957Case4NoThree.awayHullVertex P
          (sourceIndex P W s.1 s.property) Qs.twoExtreme.side 0 at hthree
  rcases hthree with h | h | h
  · exfalso
    exact realized_no_direct_competitor_at_incident_partner
      Q Ds Dt hsrole (by
        cases hrole : Dt.role <;>
          simp [IsDirectTargetRole, hrole] at htCase2 htCase4 ⊢) h
  · exact Or.inl h
  · exact Or.inr h

/-- Two distinct direct competitors cannot both hit one coherently selected
split-right target.  The prefix estimates reduce each competitor to one of
two slots.  Equal slots identify the sources, while the two different slots
are three hull steps apart and hence cannot have a common unit target. -/
theorem no_two_direct_competitors_of_split_right
    (Q : CommonCoherentRealizedSourceRows P W F.chart)
    {s t u : Source P W} {v : Vertex A}
    (Ds : RealizedPositiveTarget (Q.rows s.1 s.property) v)
    (Dt : RealizedPositiveTarget (Q.rows t.1 t.property) v)
    (Du : RealizedPositiveTarget (Q.rows u.1 u.property) v)
    (hsrole : Ds.role = PairCases.TargetRoleName.case4SplitRight)
    (htCase2 : Dt.role ≠ PairCases.TargetRoleName.case2Secondary)
    (htCase4 : Dt.role ≠ PairCases.TargetRoleName.case4SplitRight)
    (huCase2 : Du.role ≠ PairCases.TargetRoleName.case2Secondary)
    (huCase4 : Du.role ≠ PairCases.TargetRoleName.case4SplitRight)
    (htWindow : t.1 ∈ Finset.univ.image (fun j : Fin 7 ↦
      (sevenShift P.next j (sourceIndex P W s.1 s.property)).1))
    (huWindow : u.1 ∈ Finset.univ.image (fun j : Fin 7 ↦
      (sevenShift P.next j (sourceIndex P W s.1 s.property)).1))
    (hst : s ≠ t) (hsu : s ≠ u) (htu : t ≠ u) : False := by
  let Qs := Q.case4_pair s.1 s.property
    ⟨Ds.target, by simpa [hsrole] using Ds.target_at_role⟩
  have htNear := direct_competitor_reduces_to_near_two
    Q Ds Dt hsrole htCase2 htCase4 htWindow hst
  have huNear := direct_competitor_reduces_to_near_two
    Q Ds Du hsrole huCase2 huCase4 huWindow hsu
  change sourceIndex P W t.1 t.property =
        incidentContinuationHullVertex P
          (sourceIndex P W s.1 s.property) Qs.twoExtreme.side 1 ∨
      sourceIndex P W t.1 t.property =
        Erdos957Case4NoThree.awayHullVertex P
          (sourceIndex P W s.1 s.property) Qs.twoExtreme.side 0 at htNear
  change sourceIndex P W u.1 u.property =
        incidentContinuationHullVertex P
          (sourceIndex P W s.1 s.property) Qs.twoExtreme.side 1 ∨
      sourceIndex P W u.1 u.property =
        Erdos957Case4NoThree.awayHullVertex P
          (sourceIndex P W s.1 s.property) Qs.twoExtreme.side 0 at huNear
  have htAdj := Dt.direct_target_adj htCase2 htCase4
  have huAdj := Du.direct_target_adj huCase2 huCase4
  rcases htNear with ht | ht <;> rcases huNear with hu | hu
  · apply htu
    apply Subtype.ext
    simpa [sourceIndex] using congrArg Subtype.val (ht.trans hu.symm)
  · cases hside : Qs.twoExtreme.side with
    | previous =>
        apply Erdos957RoleCollisions.no_common_unit_target_third_successor
          F htAdj huAdj
        rw [ht, hu]
        simp [incidentContinuationHullVertex,
          Erdos957Case4NoThree.awayHullVertex, hside, pow_succ]
    | next =>
        apply Erdos957RoleCollisions.no_common_unit_target_third_predecessor
          F htAdj huAdj
        rw [ht, hu]
        simp [incidentContinuationHullVertex,
          Erdos957Case4NoThree.awayHullVertex, hside, pow_succ]
  · cases hside : Qs.twoExtreme.side with
    | previous =>
        apply Erdos957RoleCollisions.no_common_unit_target_third_predecessor
          F htAdj huAdj
        rw [ht, hu]
        simp [incidentContinuationHullVertex,
          Erdos957Case4NoThree.awayHullVertex, hside, pow_succ]
    | next =>
        apply Erdos957RoleCollisions.no_common_unit_target_third_successor
          F htAdj huAdj
        rw [ht, hu]
        simp [incidentContinuationHullVertex,
          Erdos957Case4NoThree.awayHullVertex, hside, pow_succ]
  · apply htu
    apply Subtype.ext
    simpa [sourceIndex] using congrArg Subtype.val (ht.trans hu.symm)

end Erdos957Case4CollisionLeaves

#print axioms Erdos957Case4CollisionLeaves.commonFrame_away_second_fst_gap_gt_two
#print axioms Erdos957Case4CollisionLeaves.commonFrame_away_third_fst_gap_gt_two
#print axioms Erdos957Case4CollisionLeaves.commonFrame_incident_third_fst_gap_gt_two
#print axioms Erdos957Case4CollisionLeaves.CommonPairedCase4Rows.currentSecondary_ne_middle
#print axioms Erdos957Case4CollisionLeaves.realized_no_direct_competitor_at_incident_partner
#print axioms Erdos957Case4CollisionLeaves.split_right_associations_ne_at_incident_partner
#print axioms Erdos957Case4CollisionLeaves.CommonPairedCase4Rows.not_direct_away_second
#print axioms Erdos957Case4CollisionLeaves.CommonPairedCase4Rows.not_direct_away_third
#print axioms Erdos957Case4CollisionLeaves.CommonPairedCase4Rows.not_direct_incident_third
#print axioms Erdos957Case4CollisionLeaves.realized_no_direct_competitor_at_away_second
#print axioms Erdos957Case4CollisionLeaves.realized_no_direct_competitor_at_away_third
#print axioms Erdos957Case4CollisionLeaves.realized_no_direct_competitor_at_incident_third
#print axioms Erdos957Case4CollisionLeaves.direct_competitor_reduces_to_near_four
#print axioms Erdos957Case4CollisionLeaves.direct_competitor_reduces_to_near_three
#print axioms Erdos957Case4CollisionLeaves.direct_competitor_reduces_to_near_two
#print axioms Erdos957Case4CollisionLeaves.no_two_direct_competitors_of_split_right
