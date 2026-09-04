import ErdosProblems.Erdos957.Case4CollisionLeaves

/-!
# Metric position exclusions for generalized Case-4 split recipients

The third hull source on the side away from a selected Case-4 edge is
strictly more than three horizontal units from the equilateral middle in
the common rigid chart.  A selected recipient is one unit from that middle,
whereas every competing realized target is within two unit edges of its
source.  This excludes the third-away split source without assuming any
pairwise collision or capacity conclusion.
-/

noncomputable section

namespace Erdos957Case4SplitDistance

open Erdos957GeometryCore
open Erdos957GeometryLocalRows
open Erdos957CaseClassification
open Erdos957CoherentRealizedRows
open Erdos957CollisionInstantiation
open Erdos957RoleCollisions

abbrev Point := Erdos957GeometryCore.Point

variable {A : Finset Point} {P : CyclicHullData A}
variable {W : DiameterWitnessData P} {F : P.FlatAlignedFrameData}

private lemma no_unit_and_within_two_of_rigid_fst_gap_gt_three
    (E : Erdos957Case24Bridge.Framed.RigidChart)
    {middle competitor target : Vertex A}
    (hm : (unitDistanceGraph A).Adj middle target)
    (hc : WithinTwoUnitEdges competitor target)
    (hgap : 3 < |(E.toCanonical middle) 0 -
      (E.toCanonical competitor) 0|) : False := by
  have hdistLe : dist (middle : Point) (competitor : Point) ≤ 3 := by
    calc
      dist (middle : Point) (competitor : Point) ≤
          dist (middle : Point) (target : Point) +
            dist (target : Point) (competitor : Point) := dist_triangle _ _ _
      _ ≤ 1 + 2 := by
        have hm' : dist (middle : Point) (target : Point) = 1 := by
          simpa [unitDistanceGraph] using hm
        have hc' : dist (target : Point) (competitor : Point) ≤ 2 := by
          simpa [dist_comm] using dist_le_two_of_withinTwoUnitEdges hc
        rw [hm']
        linarith
      _ = 3 := by norm_num
  have hdistCoord : dist (E.toCanonical middle)
      (E.toCanonical competitor) ≤ 3 := by
    rw [E.dist_eq]
    exact hdistLe
  have hs := Erdos957Cases24.dist_sq_eq_coordinates
    (E.toCanonical middle) (E.toCanonical competitor)
  have hgapSq : 9 < ((E.toCanonical middle) 0 -
      (E.toCanonical competitor) 0) ^ 2 := by
    nlinarith [sq_abs ((E.toCanonical middle) 0 -
      (E.toCanonical competitor) 0)]
  have hsnd : 0 ≤ ((E.toCanonical middle) 1 -
      (E.toCanonical competitor) 1) ^ 2 := sq_nonneg _
  have hdistNonneg : 0 ≤ dist (E.toCanonical middle)
      (E.toCanonical competitor) := dist_nonneg
  nlinarith

/-- The third away hull vertex is more than three horizontal units from
the selected Case-4 middle in the source-free common chart. -/
lemma commonFrame_away_third_fst_gap_gt_three
    (F : P.FlatAlignedFrameData)
    (source : {p // p ∈ P.H}) (middle : Vertex A)
    (T : TwoExtremeCyclicWitness P source middle)
    (N : ActualCase24Rows.TwoExtremeNormalizedFrame source middle T)
    (E : ActualCase24Rows.TwoExtremeCommonPairFrame source middle T)
    (hi : P.IsFlat source) :
    3 < |(E.frame.toCanonical middle) 0 -
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

/-- No target selected within two unit edges of the third-away source can
be the current coherent split-right recipient. -/
theorem CommonPairedCase4Rows.not_within_two_away_third
    (F : P.FlatAlignedFrameData)
    {C : P.AlignedChartData}
    {rows : HasRealizedSourceRows P W C}
    {u : Vertex A} {hu : u ∈ sourceVertices P W}
    (Q : CommonPairedCase4Rows rows u hu)
    (hi : P.IsFlat (sourceIndex P W u hu)) :
    ¬ WithinTwoUnitEdges
      (Erdos957Case4NoThree.awayHullVertex P
        (sourceIndex P W u hu) Q.twoExtreme.side 2).1
      Q.currentSecondaryTarget.vertex := by
  intro hwithin
  apply no_unit_and_within_two_of_rigid_fst_gap_gt_three Q.commonFrame.frame
    (middle := Q.middle)
    (competitor := (Erdos957Case4NoThree.awayHullVertex P
      (sourceIndex P W u hu) Q.twoExtreme.side 2).1)
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
  · exact hwithin
  · exact commonFrame_away_third_fst_gap_gt_three
      F (sourceIndex P W u hu) Q.middle Q.twoExtreme Q.normalized
        Q.commonFrame hi

/-- Realized-row wrapper: a distinct split-right competitor cannot occupy
the third away source position of the anchor. -/
theorem no_split_right_competitor_at_away_third
    (Q : CommonCoherentRealizedSourceRows P W F.chart)
    {s t : Source P W} {v : Vertex A}
    (S : RealizedArrivalAt (F := F) Q.rows s v)
    (T : RealizedArrivalAt (F := F) Q.rows t v)
    (hsRole : S.target.role = PairCases.TargetRoleName.case4SplitRight)
    (_htRole : T.target.role = PairCases.TargetRoleName.case4SplitRight)
    (htIndex : sourceIndex P W t.1 t.property =
      Erdos957Case4NoThree.awayHullVertex P
        (sourceIndex P W s.1 s.property)
        (Q.case4_pair s.1 s.property
          ⟨S.target.target, by simpa [hsRole] using S.target.target_at_role⟩).twoExtreme.side 2) :
    False := by
  let Qs := Q.case4_pair s.1 s.property
    ⟨S.target.target, by simpa [hsRole] using S.target.target_at_role⟩
  have htValue : t.1 =
      (Erdos957Case4NoThree.awayHullVertex P
        (sourceIndex P W s.1 s.property) Qs.twoExtreme.side 2).1 := by
    simpa [sourceIndex] using congrArg Subtype.val htIndex
  have hsTarget : S.target.target = Qs.currentSecondaryTarget := by
    apply Option.some.inj
    rw [← S.target.target_at_role, hsRole, Qs.current_secondary_role]
  have htVertex : T.target.target.vertex = Qs.currentSecondaryTarget.vertex := by
    calc
      T.target.target.vertex = v := T.target.vertex_eq.symm
      _ = S.target.target.vertex := S.target.vertex_eq
      _ = Qs.currentSecondaryTarget.vertex :=
        congrArg LocalTarget.vertex hsTarget
  apply Erdos957Case4SplitDistance.CommonPairedCase4Rows.not_within_two_away_third
    F Qs
    (source_isFlat P W (sourceIndex P W s.1 s.property) s.property)
  rw [← htValue]
  rw [← htVertex]
  exact T.target.target.within_two

end Erdos957Case4SplitDistance

#print axioms Erdos957Case4SplitDistance.commonFrame_away_third_fst_gap_gt_three
#print axioms Erdos957Case4SplitDistance.no_split_right_competitor_at_away_third
