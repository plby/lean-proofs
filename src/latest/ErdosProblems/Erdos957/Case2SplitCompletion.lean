import ErdosProblems.Erdos957.Case2SplitStrict
import ErdosProblems.Erdos957.Case2SplitCoordinateLift
import ErdosProblems.Erdos957.Case2SplitFinalReduction
import ErdosProblems.Erdos957.Case2SplitFinalAssembly

noncomputable section

namespace Erdos957Case2SplitCompletion

open Erdos957GeometryCore
open Erdos957GeometryLocalRows
open Erdos957CollisionInstantiation
open Erdos957CaseClassification
open Erdos957Case2RoleUniqueness
open Erdos957Case2SecondaryNoThree
open Erdos957Case4SplitClassification
open Erdos957CoherentRealizedRows
open Erdos957RoleCollisions
open Erdos957Case2SplitStrict
open Erdos957Case2SplitCoordinateLift

abbrev Point := Erdos957GeometryCore.Point

variable {A : Finset Point} {P : CyclicHullData A}
variable {W : DiameterWitnessData P} {F : P.FlatAlignedFrameData}

lemma toCanonical_midpoint_of_dist_two_unit_unit
    (E : Erdos957Case24Bridge.Framed.RigidChart)
    (s q b : Point)
    (hsq : dist s q = 2) (hsb : dist s b = 1) (hbq : dist b q = 1) :
    E.toCanonical b = (1 / 2 : ℝ) • (E.toCanonical s + E.toCanonical q) := by
  have hsq' : dist (E.toCanonical s) (E.toCanonical q) = 2 := by
    rw [E.dist_eq, hsq]
  have hsb' : dist (E.toCanonical s) (E.toCanonical b) = 1 := by
    rw [E.dist_eq, hsb]
  have hbq' : dist (E.toCanonical b) (E.toCanonical q) = 1 := by
    rw [E.dist_eq, hbq]
  have hsqSq := Erdos957Cases24.dist_sq_eq_coordinates
    (E.toCanonical s) (E.toCanonical q)
  have hsbSq := Erdos957Cases24.dist_sq_eq_coordinates
    (E.toCanonical s) (E.toCanonical b)
  have hbqSq := Erdos957Cases24.dist_sq_eq_coordinates
    (E.toCanonical b) (E.toCanonical q)
  rw [hsq'] at hsqSq
  rw [hsb'] at hsbSq
  rw [hbq'] at hbqSq
  ext i
  fin_cases i
  · change (E.toCanonical b) 0 =
      (1 / 2 : ℝ) * ((E.toCanonical s) 0 + (E.toCanonical q) 0)
    have hzero :
        (2 * (E.toCanonical b) 0 -
            (E.toCanonical s) 0 - (E.toCanonical q) 0) ^ 2 +
          (2 * (E.toCanonical b) 1 -
            (E.toCanonical s) 1 - (E.toCanonical q) 1) ^ 2 = 0 := by
      nlinarith only [hsqSq, hsbSq, hbqSq]
    have hx : 2 * (E.toCanonical b) 0 -
          (E.toCanonical s) 0 - (E.toCanonical q) 0 = 0 := by
      nlinarith only [hzero,
        sq_nonneg (2 * (E.toCanonical b) 1 -
          (E.toCanonical s) 1 - (E.toCanonical q) 1)]
    linarith only [hx]
  · change (E.toCanonical b) 1 =
      (1 / 2 : ℝ) * ((E.toCanonical s) 1 + (E.toCanonical q) 1)
    have hzero :
        (2 * (E.toCanonical b) 0 -
            (E.toCanonical s) 0 - (E.toCanonical q) 0) ^ 2 +
          (2 * (E.toCanonical b) 1 -
            (E.toCanonical s) 1 - (E.toCanonical q) 1) ^ 2 = 0 := by
      nlinarith only [hsqSq, hsbSq, hbqSq]
    have hy : 2 * (E.toCanonical b) 1 -
          (E.toCanonical s) 1 - (E.toCanonical q) 1 = 0 := by
      nlinarith only [hzero,
        sq_nonneg (2 * (E.toCanonical b) 0 -
          (E.toCanonical s) 0 - (E.toCanonical q) 0)]
    linarith only [hy]

lemma CommonPairedCase4Rows.normalized_currentSecondary_snd_eq_common
    {rows : HasRealizedSourceRows P W F.chart}
    {u : Vertex A} {hu : u ∈ sourceVertices P W}
    (Q : CommonPairedCase4Rows rows u hu) :
    (Q.normalized.frame.toCanonical Q.currentSecondaryTarget.vertex) 1 =
      (Q.commonFrame.frame.toCanonical Q.currentSecondaryTarget.vertex) 1 := by
  rw [Q.current_secondary_vertex]
  cases hside : Q.twoExtreme.side with
  | previous =>
      have hb : ActualCase24Rows.case4SourceIsRight Q.twoExtreme = true := by
        simp [ActualCase24Rows.case4SourceIsRight, hside]
      rw [hb]
      cases Q.normalized.frame_spec with
      | previous hs hunit hframe =>
          rw [hframe]
          simp [CommonCase4.CommonCase4HullPairBranch.actualRecipient,
            ActualCase24Rows.TwoExtremeCommonPairFrame.frame,
            ActualCase24Rows.case4PairEdgeBase, hside]
      | next hs hunit hframe => simp [hside] at hs
  | next =>
      have hb : ActualCase24Rows.case4SourceIsRight Q.twoExtreme = false := by
        simp [ActualCase24Rows.case4SourceIsRight, hside]
      rw [hb]
      cases Q.normalized.frame_spec with
      | previous hs hunit hframe => simp [hside] at hs
      | next hs hunit hframe =>
          rw [hframe]
          simp [CommonCase4.CommonCase4HullPairBranch.actualRecipient,
            Erdos957TwoExtremeAligned.reflectedSuccessorUnitEdgeRigidChart,
            Equiv.trans_apply, Erdos957TwoExtremeAligned.swapEndpointEquiv_apply,
            ActualCase24Rows.TwoExtremeCommonPairFrame.frame,
            ActualCase24Rows.case4PairEdgeBase, hside]

lemma CommonPairedCase4Rows.normalized_currentSecondary_fst_mem_interval_of_low
    (hA : IsOneSeparated A)
    {rows : HasRealizedSourceRows P W F.chart}
    {u : Vertex A} {hu : u ∈ sourceVertices P W}
    (Q : CommonPairedCase4Rows rows u hu)
    {hlow : Erdos957Case24Bridge.unitDegree
      (Q.commonFrame.frame.image A) Q.pairBranch.farthest.point ≤ 5}
    (hbranch : Q.pairBranch.branch =
      Erdos957Case24Bridge.Case4.FarthestBranchData.low hlow) :
    -(1 : ℝ) ≤
        (Q.normalized.frame.toCanonical Q.currentSecondaryTarget.vertex) 0 ∧
      (Q.normalized.frame.toCanonical Q.currentSecondaryTarget.vertex) 0 ≤ 0 := by
  have huPrevA : Erdos957Cases24.Case2.uPrev ∈
      Q.commonFrame.frame.image A := by
    apply Q.commonFrame.frame.mem_image_iff.mpr
    cases hright : ActualCase24Rows.case4SourceIsRight Q.twoExtreme
    · have heq : Q.commonFrame.frame.actual Erdos957Cases24.Case2.uPrev =
          (sourceIndex P W u hu).1 := by
        apply Q.commonFrame.frame.toCanonical.injective
        rw [Q.commonFrame.frame.toCanonical_actual,
          Q.commonFrame.source_coordinate]
        simp [hright, Erdos957Case24Bridge.Case4.sideSource]
      rw [heq]
      exact (sourceIndex P W u hu).1.property
    · have heq : Q.commonFrame.frame.actual Erdos957Cases24.Case2.uPrev =
          cyclicSideVertex P (sourceIndex P W u hu) Q.twoExtreme.side := by
        apply Q.commonFrame.frame.toCanonical.injective
        rw [Q.commonFrame.frame.toCanonical_actual,
          Q.commonFrame.side_coordinate]
        simp [hright, Erdos957Case24Bridge.Case4.sideSource]
      rw [heq]
      exact (cyclicSideVertex P (sourceIndex P W u hu)
        Q.twoExtreme.side).property
  have huA : Erdos957Cases24.Case2.u ∈
      Q.commonFrame.frame.image A := by
    apply Q.commonFrame.frame.mem_image_iff.mpr
    cases hright : ActualCase24Rows.case4SourceIsRight Q.twoExtreme
    · have heq : Q.commonFrame.frame.actual Erdos957Cases24.Case2.u =
          cyclicSideVertex P (sourceIndex P W u hu) Q.twoExtreme.side := by
        apply Q.commonFrame.frame.toCanonical.injective
        rw [Q.commonFrame.frame.toCanonical_actual,
          Q.commonFrame.side_coordinate]
        simp [hright, Erdos957Case24Bridge.Case4.sideSource]
      rw [heq]
      exact (cyclicSideVertex P (sourceIndex P W u hu)
        Q.twoExtreme.side).property
    · have heq : Q.commonFrame.frame.actual Erdos957Cases24.Case2.u =
          (sourceIndex P W u hu).1 := by
        apply Q.commonFrame.frame.toCanonical.injective
        rw [Q.commonFrame.frame.toCanonical_actual,
          Q.commonFrame.source_coordinate]
        simp [hright, Erdos957Case24Bridge.Case4.sideSource]
      rw [heq]
      exact (sourceIndex P W u hu).1.property
  have hvDegree : Erdos957Case24Bridge.unitDegree
      (Q.commonFrame.frame.image A) Erdos957Cases24.Case4.v = 5 := by
    rw [Q.commonFrame.frame.unitDegree_image_actual A,
      Erdos957Cases24.Case4.v, Q.commonFrame.middle_actual]
    rw [← ActualCase24Rows.graph_degree_eq_unitDegree]
    exact Q.middle_degree_five
  have hx := Erdos957Case4SplitClassification.farthestBelowData_fst_mem_source_interval
    (Q.commonFrame.frame.image_oneSeparated hA) huPrevA huA hvDegree
      Q.pairBranch.farthest
  have hcanonical : Q.commonFrame.frame.toCanonical
      Q.currentSecondaryTarget.vertex = Q.pairBranch.farthest.point := by
    rw [Q.current_secondary_vertex]
    change Q.commonFrame.frame.toCanonical
      (Q.commonFrame.frame.actual
        (Q.pairBranch.branch.sourceRecipient
          (ActualCase24Rows.case4SourceIsRight Q.twoExtreme))) = _
    rw [Q.commonFrame.frame.toCanonical_actual]
    simp [hbranch]
  cases hside : Q.twoExtreme.side with
  | previous =>
      have hb : ActualCase24Rows.case4SourceIsRight Q.twoExtreme = true := by
        simp [ActualCase24Rows.case4SourceIsRight, hside]
      rw [Q.current_secondary_vertex, hb]
      cases Q.normalized.frame_spec with
      | previous hs hunit hframe =>
          rw [hframe]
          have hgoal : -(1 : ℝ) ≤
                (Erdos957Case24Bridge.Case4.FarthestBranchData.sourceRecipient
                  (Erdos957Case24Bridge.Case4.FarthestBranchData.low hlow)
                  true) 0 ∧
              (Erdos957Case24Bridge.Case4.FarthestBranchData.sourceRecipient
                (Erdos957Case24Bridge.Case4.FarthestBranchData.low hlow)
                true) 0 ≤ 0 := by
            rw [Erdos957Case24Bridge.Case4.FarthestBranchData.sourceRecipient_low]
            exact hx
          simpa [CommonCase4.CommonCase4HullPairBranch.actualRecipient,
            ActualCase24Rows.TwoExtremeCommonPairFrame.frame,
            ActualCase24Rows.case4PairEdgeBase, hside, hbranch] using hgoal
      | next hs hunit hframe => simp [hside] at hs
  | next =>
      have hb : ActualCase24Rows.case4SourceIsRight Q.twoExtreme = false := by
        simp [ActualCase24Rows.case4SourceIsRight, hside]
      rw [Q.current_secondary_vertex, hb]
      cases Q.normalized.frame_spec with
      | previous hs hunit hframe => simp [hside] at hs
      | next hs hunit hframe =>
          rw [hframe]
          have hgoal : -(1 : ℝ) ≤
                -(Erdos957Case24Bridge.Case4.FarthestBranchData.sourceRecipient
                  (Erdos957Case24Bridge.Case4.FarthestBranchData.low hlow)
                  false) 0 - 1 ∧
              -(Erdos957Case24Bridge.Case4.FarthestBranchData.sourceRecipient
                (Erdos957Case24Bridge.Case4.FarthestBranchData.low hlow)
                false) 0 - 1 ≤ 0 := by
            rw [Erdos957Case24Bridge.Case4.FarthestBranchData.sourceRecipient_low]
            constructor <;> linarith only [hx.1, hx.2]
          simpa [CommonCase4.CommonCase4HullPairBranch.actualRecipient,
            Erdos957TwoExtremeAligned.reflectedSuccessorUnitEdgeRigidChart,
            Equiv.trans_apply, Erdos957TwoExtremeAligned.swapEndpointEquiv_apply,
            ActualCase24Rows.TwoExtremeCommonPairFrame.frame,
            ActualCase24Rows.case4PairEdgeBase, hside, hbranch] using hgoal

/-- The final adjacent split/split configuration is excluded by the third
source-neighbour sector. -/
theorem no_two_split_away_first_second
    (hA : IsOneSeparated A)
    (Q : CommonCoherentRealizedSourceRows P W F.chart)
    {s t u : Source P W} {v : Vertex A}
    (S : RealizedArrivalAt (F := F) Q.rows s v)
    (T : RealizedArrivalAt (F := F) Q.rows t v)
    (U : RealizedArrivalAt (F := F) Q.rows u v)
    (B : Case2SecondaryArrivalFormula S.target S.descriptor)
    (hsRole : S.target.role = PairCases.TargetRoleName.case2Secondary)
    (htRole : T.target.role = PairCases.TargetRoleName.case4SplitRight)
    (huRole : U.target.role = PairCases.TargetRoleName.case4SplitRight)
    (hdegree : (unitDistanceGraph A).degree v = 5)
    (htAway : sourceIndex P W t.1 t.property =
      Erdos957Case4NoThree.awayHullVertex P
        (sourceIndex P W s.1 s.property) B.formula.side 0)
    (huAway : sourceIndex P W u.1 u.property =
      Erdos957Case4NoThree.awayHullVertex P
        (sourceIndex P W s.1 s.property) B.formula.side 1) : False := by
  let Qt := Q.case4_pair t.1 t.property
    ⟨T.target.target, by simpa [htRole] using T.target.target_at_role⟩
  have hsideNe : Qt.twoExtreme.side ≠ B.formula.side :=
    Erdos957Case2SplitDegreeFive.case4SplitRight_side_ne_case2_side_at_away_first
      Q S T hsRole htRole B Qt htAway
  have huPartner : sourceIndex P W u.1 u.property =
      Erdos957Case4NoThree.incidentHullVertex P
        (sourceIndex P W t.1 t.property) Qt.twoExtreme.side 0 := by
    apply Subtype.ext
    have htValue := congrArg Subtype.val htAway
    have huValue := congrArg Subtype.val huAway
    cases hB : B.formula.side <;>
      cases hQ : Qt.twoExtreme.side <;>
      simp_all [Erdos957Case4NoThree.awayHullVertex,
        Erdos957Case4NoThree.incidentHullVertex,
        cyclicSideVertex, pow_succ]
  obtain ⟨hlow, hbranch⟩ :=
    Erdos957Case4SplitClassification.eq_low_of_incident_partner_split_right_collision
      Q T.target U.target htRole huRole huPartner
  have htarget : T.target.target = Qt.currentSecondaryTarget := by
    apply Option.some.inj
    rw [← T.target.target_at_role, htRole, Qt.current_secondary_role]
  have hvSecondary : Qt.currentSecondaryTarget.vertex = v := by
    calc
      Qt.currentSecondaryTarget.vertex = T.target.target.vertex :=
        congrArg LocalTarget.vertex htarget.symm
      _ = v := T.target.vertex_eq.symm
  have hwNext : B.formula.edgeFrame.toCanonical v =
      Erdos957Cases24.Case2.wNext := by
    rcases Case2SecondaryFormula.target_eq_w_or_wNext_of_degree_five
        hA B.formula hdegree with hw | hwNext
    · exact
        (Erdos957Case2SplitFinalReduction.no_case4SplitRight_at_outward_away_first_of_target_eq_w
          Q S T hsRole htRole B hw htAway).elim
    · exact hwNext
  have hsAway : sourceIndex P W s.1 s.property =
      Erdos957Case4NoThree.awayHullVertex P
        (sourceIndex P W t.1 t.property) Qt.twoExtreme.side 0 := by
    apply Subtype.ext
    have htValue := congrArg Subtype.val htAway
    cases hB : B.formula.side <;>
      cases hQ : Qt.twoExtreme.side <;>
      simp_all [Erdos957Case4NoThree.awayHullVertex,
        cyclicSideVertex, pow_succ]
  have hsBounds := Erdos957Case4NoThree.normalizedFrame_away_prefix_bounds
    F (sourceIndex P W t.1 t.property) Qt.middle Qt.twoExtreme Qt.normalized
      (Erdos957GeometryLocalityBridge.sourceIndex_isFlat W t) 0
  have hsBounds' :
      (Qt.normalized.frame.toCanonical
        (sourceIndex P W s.1 s.property).1) 1 < 0 ∧
      (399 / 400 : ℝ) <
        (Qt.normalized.frame.toCanonical
          (sourceIndex P W s.1 s.property).1) 0 ∧
      -(Qt.normalized.frame.toCanonical
          (sourceIndex P W s.1 s.property).1) 1 ≤
        (Qt.normalized.frame.toCanonical
          (sourceIndex P W s.1 s.property).1) 0 / 10 := by
    simpa [hsAway] using hsBounds
  have hqX : -(1 : ℝ) ≤ (Qt.normalized.frame.toCanonical v) 0 ∧
      (Qt.normalized.frame.toCanonical v) 0 ≤ 0 := by
    rw [← hvSecondary]
    exact CommonPairedCase4Rows.normalized_currentSecondary_fst_mem_interval_of_low
      hA Qt hbranch
  have hqY : (Qt.normalized.frame.toCanonical v) 1 ≤
      -Erdos957Cases24.sqrtThree := by
    rw [← hvSecondary,
      CommonPairedCase4Rows.normalized_currentSecondary_snd_eq_common Qt]
    exact
      CommonPairedCase4Rows.currentSecondary_common_snd_le_neg_sqrtThree_of_low
        hA Qt hbranch
  have hsourceTarget : dist
      ((sourceIndex P W s.1 s.property).1 : Point) (v : Point) = 2 := by
    calc
      _ = dist (B.formula.edgeFrame.toCanonical
          (sourceIndex P W s.1 s.property).1)
          (B.formula.edgeFrame.toCanonical v) :=
        (B.formula.edgeFrame.dist_eq _ _).symm
      _ = dist Erdos957Cases24.Case2.u
          Erdos957Cases24.Case2.wNext := by
        rw [← B.formula.source_actual,
          B.formula.edgeFrame.toCanonical_actual, hwNext]
      _ = 2 := by
        have hsq : dist Erdos957Cases24.Case2.u
            Erdos957Cases24.Case2.wNext ^ 2 = 4 := by
          rw [Erdos957Cases24.dist_sq_eq_coordinates]
          norm_num [Erdos957Cases24.Case2.u,
            Erdos957Cases24.Case2.wNext,
            Erdos957Cases24.sqrtThree_sq]
        have hnonneg := dist_nonneg (x := Erdos957Cases24.Case2.u)
          (y := Erdos957Cases24.Case2.wNext)
        nlinarith only [hsq, hnonneg]
  have hsourceOuter : dist
      ((sourceIndex P W s.1 s.property).1 : Point)
      (B.formula.outer : Point) = 1 := B.formula.source_outer_adj
  have houterTarget : dist (B.formula.outer : Point) (v : Point) = 1 := by
    calc
      _ = dist (B.formula.edgeFrame.toCanonical B.formula.outer)
          (B.formula.edgeFrame.toCanonical v) :=
        (B.formula.edgeFrame.dist_eq _ _).symm
      _ = dist Erdos957Cases24.Case2.b
          Erdos957Cases24.Case2.wNext := by
        rw [B.formula.outer_edge_coordinate, hwNext]
      _ = 1 := Erdos957Cases24.Case2.dist_b_wNext
  have hmid := toCanonical_midpoint_of_dist_two_unit_unit
    Qt.normalized.frame
      ((sourceIndex P W s.1 s.property).1 : Point) (v : Point)
      (B.formula.outer : Point) hsourceTarget hsourceOuter houterTarget
  obtain ⟨n, hnAdj, hnNeSide, hnNeMiddle, hnX, hnY⟩ :=
    exists_third_source_neighbor_fst_ge_half hA Qt
  have hnNorm :
      (Qt.normalized.frame.toCanonical n) 0 ^ 2 +
        (Qt.normalized.frame.toCanonical n) 1 ^ 2 = 1 := by
    have hdist : dist Erdos957Cases24.Case2.u
        (Qt.normalized.frame.toCanonical n) = 1 := by
      calc
        _ = dist (Qt.normalized.frame.toCanonical
            (sourceIndex P W t.1 t.property).1)
            (Qt.normalized.frame.toCanonical n) := by
          rw [← Qt.normalized.source_actual,
            Qt.normalized.frame.toCanonical_actual]
        _ = dist ((sourceIndex P W t.1 t.property).1 : Point) (n : Point) :=
          Qt.normalized.frame.dist_eq _ _
        _ = 1 := hnAdj
    have hsq := Erdos957Cases24.dist_sq_eq_coordinates
      Erdos957Cases24.Case2.u (Qt.normalized.frame.toCanonical n)
    rw [hdist] at hsq
    simpa [Erdos957Cases24.Case2.u] using hsq.symm
  have hnEq :=
    Erdos957Case2SplitCoordinateLift.third_arc_vertex_eq_source_or_outer
      hA Qt.normalized.frame
      (sourceIndex P W s.1 s.property).1 v B.formula.outer n
      hsBounds'.2.1 hsBounds'.1 hsBounds'.2.2 hqX.1 hqX.2 hqY
      hsourceTarget hsourceOuter houterTarget hnNorm hnX hnY
  rcases hnEq with hnSource | hnOuter
  · have hsideNeMiddle :
          cyclicSideVertex P (sourceIndex P W s.1 s.property)
              B.formula.side ≠ B.formula.middle := by
      intro h
      have hc := congrArg
        (fun z : Vertex A ↦ B.formula.edgeFrame.toCanonical (z : Point)) h
      rw [B.formula.side_edge_coordinate, ← B.formula.middle_actual,
        B.formula.edgeFrame.toCanonical_actual] at hc
      norm_num [Erdos957Cases24.Case2.uPrev,
        Erdos957Cases24.Case2.v] at hc
    have hsideNeOuter :
        cyclicSideVertex P (sourceIndex P W s.1 s.property)
            B.formula.side ≠ B.formula.outer := by
      intro h
      have hc := congrArg
        (fun z : Vertex A ↦ B.formula.edgeFrame.toCanonical (z : Point)) h
      rw [B.formula.side_edge_coordinate,
        B.formula.outer_edge_coordinate] at hc
      norm_num [Erdos957Cases24.Case2.uPrev,
        Erdos957Cases24.Case2.b] at hc
    have hmiddleNeOuter : B.formula.middle ≠ B.formula.outer := by
      intro h
      have hc := congrArg
        (fun z : Vertex A ↦ B.formula.edgeFrame.toCanonical (z : Point)) h
      rw [← B.formula.middle_actual,
        B.formula.edgeFrame.toCanonical_actual,
        B.formula.outer_edge_coordinate] at hc
      norm_num [Erdos957Cases24.Case2.v,
        Erdos957Cases24.Case2.b] at hc
    have htBounds :=
      Erdos957Case4NoThree.sideNormalizedFrame_away_prefix_metric_bounds
        F (sourceIndex P W s.1 s.property) B.formula.side
          B.formula.edgeFrame B.formula.edgeFrame_spec
          (Erdos957GeometryLocalityBridge.sourceIndex_isFlat W s) 0
    have htX : (399 / 400 : ℝ) <
        (B.formula.edgeFrame.toCanonical
          (sourceIndex P W t.1 t.property).1) 0 := by
      simpa [htAway] using htBounds.1
    have htNeSide : (sourceIndex P W t.1 t.property).1 ≠
        cyclicSideVertex P (sourceIndex P W s.1 s.property)
          B.formula.side := by
      intro h
      rw [h, B.formula.side_edge_coordinate] at htX
      norm_num [Erdos957Cases24.Case2.uPrev] at htX
    have htNeMiddle : (sourceIndex P W t.1 t.property).1 ≠
        B.formula.middle := by
      intro h
      apply B.formula.middle_not_hull
      rw [← h]
      exact (sourceIndex P W t.1 t.property).property
    have htNeOuter : (sourceIndex P W t.1 t.property).1 ≠
        B.formula.outer := by
      intro h
      apply B.formula.outer_not_hull
      rw [← h]
      exact (sourceIndex P W t.1 t.property).property
    let N := (unitDistanceGraph A).neighborFinset
      (sourceIndex P W s.1 s.property).1
    have hsideN : cyclicSideVertex P
        (sourceIndex P W s.1 s.property) B.formula.side ∈ N := by
      exact (SimpleGraph.mem_neighborFinset
        (G := unitDistanceGraph A)
        (v := (sourceIndex P W s.1 s.property).1)
        (cyclicSideVertex P (sourceIndex P W s.1 s.property)
          B.formula.side)).mpr (by
            change dist ((sourceIndex P W s.1 s.property).1 : Point)
              (cyclicSideVertex P (sourceIndex P W s.1 s.property)
                B.formula.side : Point) = 1
            exact B.formula.side_unit)
    have hmiddleN : B.formula.middle ∈ N :=
      (SimpleGraph.mem_neighborFinset
        (G := unitDistanceGraph A)
        (v := (sourceIndex P W s.1 s.property).1)
        B.formula.middle).mpr B.formula.source_middle_adj
    have houterN : B.formula.outer ∈ N :=
      (SimpleGraph.mem_neighborFinset
        (G := unitDistanceGraph A)
        (v := (sourceIndex P W s.1 s.property).1)
        B.formula.outer).mpr B.formula.source_outer_adj
    have htN : (sourceIndex P W t.1 t.property).1 ∈ N := by
      apply (SimpleGraph.mem_neighborFinset
        (G := unitDistanceGraph A)
        (v := (sourceIndex P W s.1 s.property).1)
        (sourceIndex P W t.1 t.property).1).mpr
      rw [hnSource] at hnAdj
      exact hnAdj.symm
    have hsub :
        {cyclicSideVertex P (sourceIndex P W s.1 s.property)
            B.formula.side,
          B.formula.middle, B.formula.outer,
          (sourceIndex P W t.1 t.property).1} ⊆ N := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact hsideN
      · exact hmiddleN
      · exact houterN
      · exact htN
    have hcardLe := Finset.card_le_card hsub
    have hcardN : N.card = 3 := by
      change ((unitDistanceGraph A).neighborFinset
        (sourceIndex P W s.1 s.property).1).card = 3
      rw [← SimpleGraph.degree]
      exact (source_facts (P := P) (W := W) s.property).2.2
    have hcardFour :
        ({cyclicSideVertex P (sourceIndex P W s.1 s.property)
            B.formula.side,
          B.formula.middle, B.formula.outer,
          (sourceIndex P W t.1 t.property).1} : Finset (Vertex A)).card = 4 := by
      have ha : cyclicSideVertex P (sourceIndex P W s.1 s.property)
          B.formula.side ∉
            ({B.formula.middle, B.formula.outer,
              (sourceIndex P W t.1 t.property).1} : Finset (Vertex A)) := by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨hsideNeMiddle, hsideNeOuter, htNeSide.symm⟩
      have hb : B.formula.middle ∉
          ({B.formula.outer,
            (sourceIndex P W t.1 t.property).1} : Finset (Vertex A)) := by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨hmiddleNeOuter, htNeMiddle.symm⟩
      have hc : B.formula.outer ∉
          ({(sourceIndex P W t.1 t.property).1} : Finset (Vertex A)) := by
        simpa only [Finset.mem_singleton] using htNeOuter.symm
      rw [Finset.card_insert_of_notMem ha,
        Finset.card_insert_of_notMem hb,
        Finset.card_insert_of_notMem hc]
      norm_num
    rw [hcardFour, hcardN] at hcardLe
    omega
  · have hmidY := congrArg (fun z : Point ↦ z 1) hmid
    norm_num [PiLp.smul_apply] at hmidY
    have hnMidY : (Qt.normalized.frame.toCanonical n) 1 =
        ((Qt.normalized.frame.toCanonical
            (sourceIndex P W s.1 s.property).1) 1 +
          (Qt.normalized.frame.toCanonical v) 1) / 2 := by
      rw [hnOuter]
      linarith only [hmidY]
    have hnLower :=
      Erdos957Case2SplitCoordinateLift.lower_unit_arc_snd_ge_neg_sqrtThree_half
        hnNorm hnX hnY
    rw [hnMidY] at hnLower
    nlinarith only [hnLower, hsBounds'.1, hqY]

noncomputable def twoSplitAwayFirstSecondResidual
    (hA : IsOneSeparated A)
    (Q : CommonCoherentRealizedSourceRows P W F.chart) :
    Erdos957Case2SplitFinalAssembly.TwoSplitAwayFirstSecondResidual Q where
  eliminate := by
    intro s t u v S T U B hsRole htRole huRole hdegree
      htAway huAway hst hsu htu
    exact no_two_split_away_first_second hA Q S T U B hsRole htRole huRole
      hdegree htAway huAway

/-- The completed two-split exclusion supplies the exact two-field
degree-five residual required by the weighted Case-2 assembly. -/
noncomputable def case2SecondarySplitDegreeFiveResiduals
    (hA : IsOneSeparated A)
    (Q : CommonCoherentRealizedSourceRows P W F.chart) :
    Case2SecondarySplitDegreeFiveResiduals (F := F) Q.rows :=
  Erdos957Case2SplitFinalAssembly.case2SecondarySplitDegreeFiveResiduals_of_two_split
    hA Q (twoSplitAwayFirstSecondResidual hA Q)

end Erdos957Case2SplitCompletion

#print axioms Erdos957Case2SplitCompletion.CommonPairedCase4Rows.normalized_currentSecondary_snd_eq_common
#print axioms Erdos957Case2SplitCompletion.CommonPairedCase4Rows.normalized_currentSecondary_fst_mem_interval_of_low
#print axioms Erdos957Case2SplitCompletion.no_two_split_away_first_second
#print axioms Erdos957Case2SplitCompletion.twoSplitAwayFirstSecondResidual
#print axioms Erdos957Case2SplitCompletion.case2SecondarySplitDegreeFiveResiduals
