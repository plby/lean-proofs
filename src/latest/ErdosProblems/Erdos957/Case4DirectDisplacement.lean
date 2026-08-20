import ErdosProblems.Erdos957.Case4DirectSameSide

noncomputable section

namespace Erdos957Case4DirectDisplacement

open Erdos957GeometryCore
open Erdos957GeometryLocalRows
open Erdos957CaseClassification
open Erdos957CoherentRealizedRows
open Erdos957Case4SplitClassification
open Erdos957CollisionInstantiation

abbrev Point := Erdos957GeometryCore.Point

lemma commonFrame_currentSecondary_displacement_at_near_source
    {A : Finset Point} {P : CyclicHullData A}
    {W : DiameterWitnessData P} {C : P.AlignedChartData}
    {rows : HasRealizedSourceRows P W C}
    {u : Vertex A} {hu : u ∈ sourceVertices P W}
    (F : P.FlatAlignedFrameData)
    (Q : CommonPairedCase4Rows rows u hu)
    (hi : P.IsFlat (sourceIndex P W u hu))
    {t : {p // p ∈ P.H}}
    (hnear : t = Erdos957Case4CollisionLeaves.incidentContinuationHullVertex
        P (sourceIndex P W u hu) Q.twoExtreme.side 1 ∨
      t = Erdos957Case4NoThree.awayHullVertex P
        (sourceIndex P W u hu) Q.twoExtreme.side 0) :
    let z := Q.commonFrame.frame.toCanonical Q.currentSecondaryTarget.vertex
    let p := Q.commonFrame.frame.toCanonical t.1
    (Q.twoExtreme.side = .previous ∧
        t = Erdos957Case4CollisionLeaves.incidentContinuationHullVertex
          P (sourceIndex P W u hu) Q.twoExtreme.side 1 ∧
        (99 / 200 : ℝ) ≤ z 0 - p 0) ∨
      (Q.twoExtreme.side = .previous ∧
        t = Erdos957Case4NoThree.awayHullVertex P
          (sourceIndex P W u hu) Q.twoExtreme.side 0 ∧
        z 0 - p 0 ≤ -(99 / 200 : ℝ)) ∨
      (Q.twoExtreme.side = .next ∧
        t = Erdos957Case4CollisionLeaves.incidentContinuationHullVertex
          P (sourceIndex P W u hu) Q.twoExtreme.side 1 ∧
        z 0 - p 0 ≤ -(99 / 200 : ℝ)) ∨
      (Q.twoExtreme.side = .next ∧
        t = Erdos957Case4NoThree.awayHullVertex P
          (sourceIndex P W u hu) Q.twoExtreme.side 0 ∧
        (99 / 200 : ℝ) ≤ z 0 - p 0) := by
  let z := Q.commonFrame.frame.toCanonical Q.currentSecondaryTarget.vertex
  let p := Q.commonFrame.frame.toCanonical t.1
  let q := Q.pairBranch.branch.sourceRecipient
    (ActualCase24Rows.case4SourceIsRight Q.twoExtreme)
  have hz : z = q := by
    dsimp [z, q]
    rw [Q.current_secondary_vertex]
    simp [CommonCase4.CommonCase4HullPairBranch.actualRecipient]
  have hqBounds := residual_fst_mem_sharp_interval
    (Q.pairBranch.branch.sourceRecipient_mem
      (ActualCase24Rows.case4SourceIsRight Q.twoExtreme))
  rcases hnear with hincident | haway
  · have hincident' : t = Erdos957Case4NoThree.incidentHullVertex P
        (sourceIndex P W u hu) Q.twoExtreme.side 1 := by
      change t = Erdos957Case4NoThree.incidentHullVertex P
        (sourceIndex P W u hu) Q.twoExtreme.side 1 at hincident
      exact hincident
    have hpNorm := Erdos957Case4NoThree.normalizedFrame_incident_prefix_metric_bounds
      F (sourceIndex P W u hu) Q.middle Q.twoExtreme Q.normalized hi 1
    rw [← hincident'] at hpNorm
    norm_num at hpNorm
    cases hside : Q.twoExtreme.side with
    | previous =>
        left
        refine ⟨rfl, ?_, ?_⟩
        · simpa [hside] using hincident
        have hcoord : Q.normalized.frame.toCanonical t.1 =
            Q.commonFrame.frame.toCanonical t.1 := by
          cases Q.normalized.frame_spec with
          | previous hs hunit hframe =>
              rw [hframe]
              simp [ActualCase24Rows.TwoExtremeCommonPairFrame.frame,
                ActualCase24Rows.case4PairEdgeBase, hside]
          | next hs hunit hframe => simp [hside] at hs
        have hpX : (399 / 200 : ℝ) < -p 0 := by
          have hx := hpNorm.1
          rw [hcoord] at hx
          change (399 / 200 : ℝ) <
            -(Q.commonFrame.frame.toCanonical t.1) 0
          simpa [p] using hx
        change (99 / 200 : ℝ) ≤ z 0 - p 0
        rw [hz]
        linarith [hqBounds.1]
    | next =>
        right; right; left
        refine ⟨rfl, ?_, ?_⟩
        · simpa [hside] using hincident
        have hcoord :
            (Q.normalized.frame.toCanonical t.1) 0 = -p 0 - 1 := by
          cases Q.normalized.frame_spec with
          | previous hs hunit hframe => simp [hside] at hs
          | next hs hunit hframe =>
              rw [hframe]
              simp [p,
                Erdos957TwoExtremeAligned.reflectedSuccessorUnitEdgeRigidChart,
                Equiv.trans_apply,
                Erdos957TwoExtremeAligned.swapEndpointEquiv_apply,
                Erdos957TwoExtremeAligned.swapEndpointCoord_apply_zero,
                ActualCase24Rows.TwoExtremeCommonPairFrame.frame,
                ActualCase24Rows.case4PairEdgeBase, hside]
        have hpX : (199 / 200 : ℝ) < p 0 := by
          have hx := hpNorm.1
          rw [hcoord] at hx
          linarith
        change z 0 - p 0 ≤ -(99 / 200 : ℝ)
        rw [hz]
        linarith [hqBounds.2]
  · have hpNorm := Erdos957Case4NoThree.normalizedFrame_away_prefix_bounds
      F (sourceIndex P W u hu) Q.middle Q.twoExtreme Q.normalized hi 0
    rw [← haway] at hpNorm
    norm_num at hpNorm
    cases hside : Q.twoExtreme.side with
    | previous =>
        right; left
        refine ⟨rfl, ?_, ?_⟩
        · simpa [hside] using haway
        have hcoord : Q.normalized.frame.toCanonical t.1 =
            Q.commonFrame.frame.toCanonical t.1 := by
          cases Q.normalized.frame_spec with
          | previous hs hunit hframe =>
              rw [hframe]
              simp [ActualCase24Rows.TwoExtremeCommonPairFrame.frame,
                ActualCase24Rows.case4PairEdgeBase, hside]
          | next hs hunit hframe => simp [hside] at hs
        have hpX : (399 / 400 : ℝ) < p 0 := by
          have hx := hpNorm.2.1
          rw [hcoord] at hx
          simpa [p] using hx
        change z 0 - p 0 ≤ -(99 / 200 : ℝ)
        rw [hz]
        linarith [hqBounds.2]
    | next =>
        right; right; right
        refine ⟨rfl, ?_, ?_⟩
        · simpa [hside] using haway
        have hcoord :
            (Q.normalized.frame.toCanonical t.1) 0 = -p 0 - 1 := by
          cases Q.normalized.frame_spec with
          | previous hs hunit hframe => simp [hside] at hs
          | next hs hunit hframe =>
              rw [hframe]
              simp [p,
                Erdos957TwoExtremeAligned.reflectedSuccessorUnitEdgeRigidChart,
                Equiv.trans_apply,
                Erdos957TwoExtremeAligned.swapEndpointEquiv_apply,
                Erdos957TwoExtremeAligned.swapEndpointCoord_apply_zero,
                ActualCase24Rows.TwoExtremeCommonPairFrame.frame,
                ActualCase24Rows.case4PairEdgeBase, hside]
        have hpX : p 0 < -(799 / 400 : ℝ) := by
          have hx := hpNorm.2.1
          rw [hcoord] at hx
          linarith
        change (99 / 200 : ℝ) ≤ z 0 - p 0
        rw [hz]
        linarith [hqBounds.1]

lemma fst_pos_of_pairEdgeTransform_fst_pos
    {e x z : ℝ × ℝ}
    (he : e.1 ^ 2 + e.2 ^ 2 = 1)
    (hc : (399 / 400 : ℝ) ≤ e.1)
    (hs : |e.2| ≤ (7 / 100 : ℝ))
    (hz : z = Erdos957Case4NoThree.pairEdgeTransform e x)
    (hzx : (99 / 200 : ℝ) ≤ z.1)
    (hzy : |z.2| ≤ 1) :
    0 < x.1 := by
  have hinv : x.1 = e.1 * z.1 + (-e.2) * z.2 := by
    rw [hz]
    simp only [Erdos957Case4NoThree.pairEdgeTransform,
      Erdos957Case4NoThree.pairDot, CyclicHullData.pairCross]
    calc
      x.1 = (e.1 ^ 2 + e.2 ^ 2) * x.1 := by rw [he]; ring
      _ = e.1 * (e.1 * x.1 + e.2 * x.2) +
          -e.2 * (e.1 * x.2 - e.2 * x.1) := by ring
  rw [hinv]
  exact Erdos957EdgeConeTransport.fst_pos_under_small_rotation hc
    (by simpa using hs) hzx hzy

lemma fst_neg_of_pairEdgeTransform_fst_neg
    {e x z : ℝ × ℝ}
    (he : e.1 ^ 2 + e.2 ^ 2 = 1)
    (hc : (399 / 400 : ℝ) ≤ e.1)
    (hs : |e.2| ≤ (7 / 100 : ℝ))
    (hz : z = Erdos957Case4NoThree.pairEdgeTransform e x)
    (hzx : z.1 ≤ -(99 / 200 : ℝ))
    (hzy : |z.2| ≤ 1) :
    x.1 < 0 := by
  have hinv : x.1 = e.1 * z.1 + (-e.2) * z.2 := by
    rw [hz]
    simp only [Erdos957Case4NoThree.pairEdgeTransform,
      Erdos957Case4NoThree.pairDot, CyclicHullData.pairCross]
    calc
      x.1 = (e.1 ^ 2 + e.2 ^ 2) * x.1 := by rw [he]; ring
      _ = e.1 * (e.1 * x.1 + e.2 * x.2) +
          -e.2 * (e.1 * x.2 - e.2 * x.1) := by ring
  rw [hinv]
  exact Erdos957EdgeConeTransport.fst_neg_under_small_rotation hc
    (by simpa using hs) hzx hzy

lemma aligned_currentSecondary_fst_sign_at_near_source
    {A : Finset Point} {P : CyclicHullData A}
    {W : DiameterWitnessData P} {C : P.AlignedChartData}
    {rows : HasRealizedSourceRows P W C}
    {u : Vertex A} {hu : u ∈ sourceVertices P W}
    (F : P.FlatAlignedFrameData)
    (Q : CommonPairedCase4Rows rows u hu)
    (hi : P.IsFlat (sourceIndex P W u hu))
    {t : {p // p ∈ P.H}}
    (htFlat : P.IsFlat t)
    (hadj : (unitDistanceGraph A).Adj t.1
      Q.currentSecondaryTarget.vertex)
    (hnear : t = Erdos957Case4CollisionLeaves.incidentContinuationHullVertex
        P (sourceIndex P W u hu) Q.twoExtreme.side 1 ∨
      t = Erdos957Case4NoThree.awayHullVertex P
        (sourceIndex P W u hu) Q.twoExtreme.side 0) :
    (Q.twoExtreme.side = .previous ∧
        t = Erdos957Case4CollisionLeaves.incidentContinuationHullVertex
          P (sourceIndex P W u hu) Q.twoExtreme.side 1 ∧
        0 < (F.chart.coord t Q.currentSecondaryTarget.vertex).1) ∨
      (Q.twoExtreme.side = .previous ∧
        t = Erdos957Case4NoThree.awayHullVertex P
          (sourceIndex P W u hu) Q.twoExtreme.side 0 ∧
        (F.chart.coord t Q.currentSecondaryTarget.vertex).1 < 0) ∨
      (Q.twoExtreme.side = .next ∧
        t = Erdos957Case4CollisionLeaves.incidentContinuationHullVertex
          P (sourceIndex P W u hu) Q.twoExtreme.side 1 ∧
        (F.chart.coord t Q.currentSecondaryTarget.vertex).1 < 0) ∨
      (Q.twoExtreme.side = .next ∧
        t = Erdos957Case4NoThree.awayHullVertex P
          (sourceIndex P W u hu) Q.twoExtreme.side 0 ∧
        0 < (F.chart.coord t Q.currentSecondaryTarget.vertex).1) := by
  let base := ActualCase24Rows.case4PairEdgeBase Q.twoExtreme
  let o := P.next base
  let e := CyclicHullData.pairSub
    (F.chart.coord t o.1) (F.chart.coord t base.1)
  let x := F.chart.coord t Q.currentSecondaryTarget.vertex
  let z : ℝ × ℝ :=
    ((Q.commonFrame.frame.toCanonical Q.currentSecondaryTarget.vertex) 0 -
        (Q.commonFrame.frame.toCanonical t.1) 0,
      (Q.commonFrame.frame.toCanonical Q.currentSecondaryTarget.vertex) 1 -
        (Q.commonFrame.frame.toCanonical t.1) 1)
  have hunit : dist (base.1.1 : Point) (o.1.1 : Point) = 1 := by
    simpa [base, o] using Q.commonFrame.edge_unit
  have heSq : e.1 ^ 2 + e.2 ^ 2 = 1 := by
    have hs := F.chart.sqDist_coord t base.1 o.1
    rw [hunit] at hs
    norm_num at hs
    dsimp [e, CyclicHullData.pairSub]
    simp only [Erdos957Cases13.sqDist] at hs
    nlinarith only [hs]
  have heBounds :=
    Erdos957Case4DirectSameSide.commonPairEdge_direction_bounds_at_near_source
    F (sourceIndex P W u hu) t Q.middle Q.twoExtreme Q.commonFrame htFlat hnear
  have htransform : z = Erdos957Case4NoThree.pairEdgeTransform e x := by
    have h := Erdos957Case4DirectSameSide.edgePairDisplacement_eq_aligned
      F.chart t base.1 o.1
      Q.currentSecondaryTarget.vertex hunit
    simpa [z, e, x, base, o,
      ActualCase24Rows.TwoExtremeCommonPairFrame.frame,
      Erdos957EdgeFrame.edgePointCoord,
      Erdos957EdgeFrame.edgePairCoord,
      CyclicHullData.pairSub] using h
  have hdistActual : dist (Q.currentSecondaryTarget.vertex : Point) t.1 = 1 := by
    simpa [unitDistanceGraph, dist_comm] using hadj
  have hdistCommon : dist
      (Q.commonFrame.frame.toCanonical Q.currentSecondaryTarget.vertex)
      (Q.commonFrame.frame.toCanonical t.1) = 1 := by
    rw [Q.commonFrame.frame.dist_eq]
    exact hdistActual
  have hdistSq := Erdos957Cases24.dist_sq_eq_coordinates
    (Q.commonFrame.frame.toCanonical Q.currentSecondaryTarget.vertex)
    (Q.commonFrame.frame.toCanonical t.1)
  rw [hdistCommon] at hdistSq
  norm_num at hdistSq
  have hzySq : z.2 ^ 2 ≤ (1 : ℝ) ^ 2 := by
    dsimp [z]
    nlinarith [hdistSq, sq_nonneg
      ((Q.commonFrame.frame.toCanonical Q.currentSecondaryTarget.vertex) 0 -
        (Q.commonFrame.frame.toCanonical t.1) 0)]
  have hzy : |z.2| ≤ 1 := by
    apply (sq_le_sq₀ (abs_nonneg z.2) (by norm_num)).mp
    simpa only [sq_abs] using hzySq
  have hdisp := commonFrame_currentSecondary_displacement_at_near_source
    F Q hi hnear
  rcases hdisp with h | h | h | h
  · left
    refine ⟨h.1, h.2.1, ?_⟩
    have hx := fst_pos_of_pairEdgeTransform_fst_pos heSq heBounds.1
      heBounds.2 htransform h.2.2 hzy
    simpa [x] using hx
  · right; left
    refine ⟨h.1, h.2.1, ?_⟩
    have hx := fst_neg_of_pairEdgeTransform_fst_neg heSq heBounds.1
      heBounds.2 htransform h.2.2 hzy
    simpa [x] using hx
  · right; right; left
    refine ⟨h.1, h.2.1, ?_⟩
    have hx := fst_neg_of_pairEdgeTransform_fst_neg heSq heBounds.1
      heBounds.2 htransform h.2.2 hzy
    simpa [x] using hx
  · right; right; right
    refine ⟨h.1, h.2.1, ?_⟩
    have hx := fst_pos_of_pairEdgeTransform_fst_pos heSq heBounds.1
      heBounds.2 htransform h.2.2 hzy
    simpa [x] using hx

lemma singleton_direct_near_two_associations_ne
    {A : Finset Point} {P : CyclicHullData A}
    {W : DiameterWitnessData P} {F : P.FlatAlignedFrameData}
    (hA : IsOneSeparated A)
    (Q : CommonCoherentRealizedSourceRows P W F.chart)
    {s t : Source P W} {v : Vertex A}
    (S : Erdos957RoleCollisions.RealizedArrivalAt (F := F) Q.rows s v)
    (T : Erdos957RoleCollisions.RealizedArrivalAt (F := F) Q.rows t v)
    (hsRole : S.target.role = PairCases.TargetRoleName.case4SplitRight)
    (htDirect : IsDirectTargetRole T.target.role)
    (middleCoord : PairPoint)
    (htCoordinate : F.chart.coord (sourceIndex P W t.1 t.property) v =
      middleCoord)
    (htAssociation : T.descriptor.association =
      horizontalAssociation middleCoord.1)
    (hnear :
      let Qs := Q.case4_pair s.1 s.property
        ⟨S.target.target, by simpa [hsRole] using S.target.target_at_role⟩
      sourceIndex P W t.1 t.property =
          Erdos957Case4CollisionLeaves.incidentContinuationHullVertex P
            (sourceIndex P W s.1 s.property) Qs.twoExtreme.side 1 ∨
        sourceIndex P W t.1 t.property =
          Erdos957Case4NoThree.awayHullVertex P
            (sourceIndex P W s.1 s.property) Qs.twoExtreme.side 0) :
    S.descriptor.association ≠ T.descriptor.association := by
  let Qs := Q.case4_pair s.1 s.property
    ⟨S.target.target, by simpa [hsRole] using S.target.target_at_role⟩
  change sourceIndex P W t.1 t.property =
        Erdos957Case4CollisionLeaves.incidentContinuationHullVertex P
          (sourceIndex P W s.1 s.property) Qs.twoExtreme.side 1 ∨
      sourceIndex P W t.1 t.property =
        Erdos957Case4NoThree.awayHullVertex P
          (sourceIndex P W s.1 s.property) Qs.twoExtreme.side 0 at hnear
  have hslot : S.target.target = Qs.currentSecondaryTarget := by
    apply Option.some.inj
    rw [← S.target.target_at_role, hsRole, Qs.current_secondary_role]
  have hv : v = Qs.currentSecondaryTarget.vertex := by
    calc
      v = S.target.target.vertex := S.target.vertex_eq
      _ = Qs.currentSecondaryTarget.vertex := congrArg LocalTarget.vertex hslot
  have hadj : (unitDistanceGraph A).Adj
      (sourceIndex P W t.1 t.property).1
      Qs.currentSecondaryTarget.vertex := by
    rw [← hv]
    exact T.target.adj_source_of_directRole htDirect
  have hiS := Erdos957GeometryLocalityBridge.sourceIndex_isFlat W s
  have hiT := Erdos957GeometryLocalityBridge.sourceIndex_isFlat W t
  have hanchor :=
    Erdos957Case4DirectSameSide.current_secondary_association_of_adj_near_source
      hA F Qs hiS hadj hnear
  have hsign := aligned_currentSecondary_fst_sign_at_near_source
    F Qs hiS hiT hadj hnear
  have hsDescriptor : S.descriptor.association =
      (Q.rows s.1 s.property).roleAssociation .case4SplitRight := by
    calc
      S.descriptor.association =
          (Q.rows s.1 s.property).roleAssociation S.target.role :=
        S.descriptor.association_eq
      _ = _ := by rw [hsRole]
  have hslotsNe :
      Erdos957Case4CollisionLeaves.incidentContinuationHullVertex P
          (sourceIndex P W s.1 s.property) Qs.twoExtreme.side 1 ≠
        Erdos957Case4NoThree.awayHullVertex P
          (sourceIndex P W s.1 s.property) Qs.twoExtreme.side 0 := by
    intro heq
    have hiBound :=
      Erdos957Case4NoThree.normalizedFrame_incident_prefix_metric_bounds
        F (sourceIndex P W s.1 s.property) Qs.middle Qs.twoExtreme
          Qs.normalized hiS 1
    have haBound := Erdos957Case4NoThree.normalizedFrame_away_prefix_bounds
      F (sourceIndex P W s.1 s.property) Qs.middle Qs.twoExtreme
        Qs.normalized hiS 0
    change Erdos957Case4NoThree.incidentHullVertex P
      (sourceIndex P W s.1 s.property) Qs.twoExtreme.side 1 =
        Erdos957Case4NoThree.awayHullVertex P
          (sourceIndex P W s.1 s.property) Qs.twoExtreme.side 0 at heq
    rw [heq] at hiBound
    norm_num at hiBound haBound
    linarith [hiBound.1, haBound.2.1]
  rcases hsign with h | h | h | h
  · have hsAssoc : S.descriptor.association = .fromPrevious := by
      rw [hsDescriptor]
      rcases hanchor with ha | ha
      · rw [ha.2, h.1]
        rfl
      · exact (hslotsNe (h.2.1.symm.trans ha.1)).elim
    have htAssoc : T.descriptor.association = .fromNext := by
      rw [htAssociation]
      have hx : 0 < middleCoord.1 := by rw [← htCoordinate, hv]; exact h.2.2
      simp [horizontalAssociation, not_le.mpr hx]
    rw [hsAssoc, htAssoc]
    decide
  · have hsAssoc : S.descriptor.association = .fromNext := by
      rw [hsDescriptor]
      rcases hanchor with ha | ha
      · exact (hslotsNe (ha.1.symm.trans h.2.1)).elim
      · rw [ha.2, h.1]
        rfl
    have htAssoc : T.descriptor.association = .fromPrevious := by
      rw [htAssociation]
      have hx : middleCoord.1 ≤ 0 := by
        rw [← htCoordinate, hv]
        exact h.2.2.le
      simp [horizontalAssociation, hx]
    rw [hsAssoc, htAssoc]
    decide
  · have hsAssoc : S.descriptor.association = .fromNext := by
      rw [hsDescriptor]
      rcases hanchor with ha | ha
      · rw [ha.2, h.1]
        rfl
      · exact (hslotsNe (h.2.1.symm.trans ha.1)).elim
    have htAssoc : T.descriptor.association = .fromPrevious := by
      rw [htAssociation]
      have hx : middleCoord.1 ≤ 0 := by
        rw [← htCoordinate, hv]
        exact h.2.2.le
      simp [horizontalAssociation, hx]
    rw [hsAssoc, htAssoc]
    decide
  · have hsAssoc : S.descriptor.association = .fromPrevious := by
      rw [hsDescriptor]
      rcases hanchor with ha | ha
      · exact (hslotsNe (ha.1.symm.trans h.2.1)).elim
      · rw [ha.2, h.1]
        rfl
    have htAssoc : T.descriptor.association = .fromNext := by
      rw [htAssociation]
      have hx : 0 < middleCoord.1 := by rw [← htCoordinate, hv]; exact h.2.2
      simp [horizontalAssociation, not_le.mpr hx]
    rw [hsAssoc, htAssoc]
    decide

end Erdos957Case4DirectDisplacement

#print axioms Erdos957Case4DirectDisplacement.commonFrame_currentSecondary_displacement_at_near_source
#print axioms Erdos957Case4DirectDisplacement.singleton_direct_near_two_associations_ne
