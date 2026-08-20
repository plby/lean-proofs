import ErdosProblems.Erdos957.Case13RealizedRows
import ErdosProblems.Erdos957.RealizationWindow

open scoped RealInnerProductSpace

noncomputable section

namespace Erdos957Case2RealizedRows

open Erdos957
open Erdos957GeometryCore
open Erdos957GeometryLocalRows
open Erdos957HullGeometryBridge
open Erdos957BisectorFrame
open Erdos957BisectorPolar
open Erdos957EdgeFrame
open Erdos957ChartTransport
open Erdos957TurnSum
open Erdos957TurnSum.HullOrderBridge
open Erdos957CaseClassification
open Erdos957CaseClassification.ActualCase24Rows

abbrev Point := Erdos957GeometryCore.Point

/-- A unit outgoing hull edge is the unit direction selected by the lifted
cyclic order. -/
lemma outgoing_edge_eq_unitDirection
    {A : Finset Point} {O : CyclicHullOrder A}
    (L : LiftedCyclicHullOrder O) (a : Fin (hullVertexCount A))
    (hunit : dist (O.vertex a)
      (O.vertex (finRotate (hullVertexCount A) a)) = 1) :
    O.vertex (finRotate (hullVertexCount A) a) - O.vertex a =
      unitDirection
        (L.lift.angle ((previousIndex a).1 + 1)) := by
  let b := previousIndex a
  have hba : finRotate (hullVertexCount A) b = a := by
    exact (finRotate (hullVertexCount A)).apply_symm_apply a
  have hedge := L.successor_edge_eq b
  rw [hba] at hedge
  have hnorm :
      ‖O.vertex (finRotate (hullVertexCount A) a) - O.vertex a‖ = 1 := by
    rw [← dist_eq_norm]
    simpa [dist_comm] using hunit
  have hscale : L.edgeScale a = 1 := by
    rw [hedge, norm_smul, norm_unitDirection, mul_one,
      Real.norm_eq_abs, abs_of_pos (L.edgeScale_pos a)] at hnorm
    exact hnorm
  simpa [b, hscale] using hedge

/-- At a flat vertex the genuine bisector differs from the outgoing edge
direction by at most one degree. -/
lemma abs_bisectorAngle_sub_outgoing_le_one_degree
    {A : Finset Point} {O : CyclicHullOrder A}
    (L : LiftedCyclicHullOrder O) (a : Fin (hullVertexCount A))
    (hturn : (cyclicHullDataOfOrder O L).turn
      (indexEquivLiftedHull O a) < Real.pi / 180) :
    |bisectorAngle L a -
      L.lift.angle ((previousIndex a).1 + 1)| ≤ Real.pi / 180 := by
  let b := previousIndex a
  have hba : finRotate (hullVertexCount A) b = a := by
    exact (finRotate (hullVertexCount A)).apply_symm_apply a
  have hturnEq : (cyclicHullDataOfOrder O L).turn
      (indexEquivLiftedHull O a) = L.lift.turn b := by
    rw [← hba]
    exact cyclicHullDataOfOrder_turn_successor_indexEquiv O L b
  have hangle : L.lift.angle b.1 + L.lift.turn b =
      L.lift.angle (b.1 + 1) := by
    simp only [DirectionLift.turn]
    ring
  have hbnonneg : 0 ≤ L.lift.turn b := L.lift.turn_nonneg b
  rw [hturnEq] at hturn
  rw [bisectorAngle, incidentTurn]
  change |L.lift.angle b.1 + L.lift.turn b / 2 -
    L.lift.angle (b.1 + 1)| ≤ _
  rw [← hangle]
  rw [show L.lift.angle b.1 + L.lift.turn b / 2 -
      (L.lift.angle b.1 + L.lift.turn b) =
      -(L.lift.turn b / 2) by ring]
  rw [abs_neg, abs_of_nonneg (by positivity)]
  nlinarith [Real.pi_pos]

/-- Sharp recipient transport for the outgoing-edge normalization. -/
theorem outgoing_edge_recipient_horizontal_le_seven_four
    {A : Finset Point} {O : CyclicHullOrder A}
    (L : LiftedCyclicHullOrder O) (a : Fin (hullVertexCount A))
    (q : Erdos957GeometryCore.Vertex A)
    (hunit : dist (O.vertex a)
      (O.vertex (finRotate (hullVertexCount A) a)) = 1)
    (hturn : (cyclicHullDataOfOrder O L).turn
      (indexEquivLiftedHull O a) < Real.pi / 180)
    (hradius : dist (O.vertex a) (q : Point) ≤ 2)
    (hedge : |(edgePairCoord (O.vertex a)
      (O.vertex (finRotate (hullVertexCount A) a) - O.vertex a)
      (q : Point)).1| ≤ (3 : ℝ) / 2) :
    |((bisectorAlignedChartData O L).coord
      (indexEquivLiftedHull O a) q).1| ≤ (7 : ℝ) / 4 := by
  exact
    abs_bisectorAlignedChartData_coord_fst_le_seven_four_of_edgePairCoord
      L (indexEquivLiftedHull O a) q
      (O.vertex (finRotate (hullVertexCount A) a) - O.vertex a)
      (L.lift.angle ((previousIndex a).1 + 1))
      (outgoing_edge_eq_unitDirection L a hunit)
      (by simpa using
        abs_bisectorAngle_sub_outgoing_le_one_degree L a hturn)
      (by simpa using hradius) (by simpa using hedge)

/-- In the outgoing-edge chart, the incoming hull vertex stays within
`1/10` of the supporting axis at a flat source, when it lies within two
units of that source. -/
lemma incoming_edge_outgoing_height_abs_lt_one_tenth
    {A : Finset Point} {O : CyclicHullOrder A}
    (L : LiftedCyclicHullOrder O) (a : Fin (hullVertexCount A))
    (hunit : dist (O.vertex a)
      (O.vertex (finRotate (hullVertexCount A) a)) = 1)
    (hturn : (cyclicHullDataOfOrder O L).turn
      (indexEquivLiftedHull O a) < Real.pi / 180)
    (hradius : dist (O.vertex a) (O.vertex (previousIndex a)) ≤ 2) :
    |(edgePairCoord (O.vertex a)
      (O.vertex (finRotate (hullVertexCount A) a) - O.vertex a)
      (O.vertex (previousIndex a))).2| < (1 : ℝ) / 10 := by
  let b := previousIndex a
  have hba : finRotate (hullVertexCount A) b = a := by
    exact (finRotate (hullVertexCount A)).apply_symm_apply a
  have hin := L.edge_eq b
  rw [hba] at hin
  have hout := outgoing_edge_eq_unitDirection L a hunit
  have hturnEq : (cyclicHullDataOfOrder O L).turn
      (indexEquivLiftedHull O a) = L.lift.turn b := by
    rw [← hba]
    exact cyclicHullDataOfOrder_turn_successor_indexEquiv O L b
  have hdeltaPos : 0 < L.lift.turn b := by
    simpa [incidentTurn, previousIndex, b] using incidentTurn_pos L a
  have hdeltaLt : L.lift.turn b < Real.pi / 180 := by
    rwa [hturnEq] at hturn
  have hscale : L.edgeScale b ≤ 2 := by
    have hn : ‖O.vertex a - O.vertex b‖ ≤ 2 := by
      rw [← dist_eq_norm]
      simpa [b, dist_comm] using hradius
    rw [hin, norm_smul, norm_unitDirection, mul_one,
      Real.norm_eq_abs, abs_of_pos (L.edgeScale_pos b)] at hn
    exact hn
  have hsinNonneg : 0 ≤ Real.sin (L.lift.turn b) :=
    (Real.sin_pos_of_pos_of_lt_pi hdeltaPos
      (hdeltaLt.trans (by nlinarith [Real.pi_pos]))).le
  have hsinLt : Real.sin (L.lift.turn b) < (1 : ℝ) / 45 := by
    have habs : |Real.sin (L.lift.turn b)| ≤ |L.lift.turn b| :=
      Real.abs_sin_le_abs
    rw [abs_of_nonneg hdeltaPos.le] at habs
    rw [abs_of_nonneg hsinNonneg] at habs
    have hpi : Real.pi / 180 < (1 : ℝ) / 45 := by
      nlinarith [Real.pi_lt_four]
    linarith
  have hangle : L.lift.angle b.1 + L.lift.turn b =
      L.lift.angle (b.1 + 1) := by
    simp only [DirectionLift.turn]
    ring
  have hy : (edgePairCoord (O.vertex a)
      (O.vertex (finRotate (hullVertexCount A) a) - O.vertex a)
      (O.vertex b)).2 =
      -L.edgeScale b * Real.sin (L.lift.turn b) := by
    rw [hout]
    simp only [edgePairCoord]
    have hv : O.vertex b - O.vertex a =
        -(L.edgeScale b) • unitDirection (L.lift.angle b.1) := by
      rw [← neg_sub, hin]
      module
    rw [hv, ← hangle]
    simp only [PiLp.smul_apply, smul_eq_mul]
    calc
      _ = L.edgeScale b *
          det (unitDirection (L.lift.angle b.1 + L.lift.turn b))
            (unitDirection (L.lift.angle b.1)) := by
        change
          (unitDirection (L.lift.angle b.1 + L.lift.turn b)) 1 *
                (-L.edgeScale b * (unitDirection (L.lift.angle b.1)) 0) -
              (unitDirection (L.lift.angle b.1 + L.lift.turn b)) 0 *
                (-L.edgeScale b * (unitDirection (L.lift.angle b.1)) 1) =
            L.edgeScale b *
              ((unitDirection (L.lift.angle b.1 + L.lift.turn b)) 0 *
                  (unitDirection (L.lift.angle b.1)) 1 -
                (unitDirection (L.lift.angle b.1 + L.lift.turn b)) 1 *
                  (unitDirection (L.lift.angle b.1)) 0)
        ring
      _ = _ := by
        rw [det_unitDirection]
        rw [show L.lift.angle b.1 -
          (L.lift.angle b.1 + L.lift.turn b) = -L.lift.turn b by ring]
        rw [Real.sin_neg]
        ring
  change |(edgePairCoord (O.vertex a)
      (O.vertex (finRotate (hullVertexCount A) a) - O.vertex a)
      (O.vertex b)).2| < _
  rw [hy, abs_mul, abs_neg, abs_of_pos (L.edgeScale_pos b),
    abs_of_nonneg hsinNonneg]
  have hprod : L.edgeScale b * Real.sin (L.lift.turn b) < 2 / 45 := by
    nlinarith [L.edgeScale_pos b]
  norm_num at hprod ⊢
  linarith

/-- Every branch-selected Case-2 secondary has edge-chart horizontal
coordinate at most `3/2`. -/
lemma secondaryRecipient_abs_fst_le_three_halves (dw dwn : ℕ) :
    |(Erdos957Cases24.Case2.secondaryRecipient dw dwn) 0| ≤
      (3 : ℝ) / 2 := by
  simp only [Erdos957Cases24.Case2.secondaryRecipient]
  split_ifs <;>
    simp [Erdos957Cases24.Case2.w, Erdos957Cases24.Case2.wNext,
      Erdos957Cases24.Case2.e] <;> norm_num

/-- Every branch-selected Case-2 secondary lies much deeper than a flat
incident hull edge can lie in the normalized edge chart. -/
lemma one_tenth_lt_secondaryRecipient_abs_snd (dw dwn : ℕ) :
    (1 : ℝ) / 10 <
      |(Erdos957Cases24.Case2.secondaryRecipient dw dwn) 1| := by
  simp only [Erdos957Cases24.Case2.secondaryRecipient]
  split_ifs <;>
    simp only [Erdos957Cases24.Case2.w,
      Erdos957Cases24.Case2.wNext, Erdos957Cases24.Case2.e,
      Erdos957Cases24.point_apply_one, abs_neg]
  all_goals
    first
    | rw [abs_of_pos Erdos957Cases24.sqrtThree_pos]
    | rw [abs_of_pos
        (div_pos Erdos957Cases24.sqrtThree_pos (by norm_num))]
  all_goals
    nlinarith [Erdos957Cases24.sqrtThree_pos,
      Erdos957Cases24.sqrtThree_sq]

lemma secondaryRecipient_ne_u (dw dwn : ℕ) :
    Erdos957Cases24.Case2.secondaryRecipient dw dwn ≠
      Erdos957Cases24.Case2.u := by
  simp only [Erdos957Cases24.Case2.secondaryRecipient]
  split_ifs <;>
    norm_num [Erdos957Cases24.Case2.w, Erdos957Cases24.Case2.wNext,
      Erdos957Cases24.Case2.e, Erdos957Cases24.Case2.u,
      Erdos957Cases24.point_inj]
  all_goals exact ne_of_gt Erdos957Cases24.sqrtThree_pos

lemma secondaryRecipient_ne_uPrev (dw dwn : ℕ) :
    Erdos957Cases24.Case2.secondaryRecipient dw dwn ≠
      Erdos957Cases24.Case2.uPrev := by
  simp only [Erdos957Cases24.Case2.secondaryRecipient]
  split_ifs <;>
    norm_num [Erdos957Cases24.Case2.w, Erdos957Cases24.Case2.wNext,
      Erdos957Cases24.Case2.e, Erdos957Cases24.Case2.uPrev,
      Erdos957Cases24.point_inj]

/-- The canonical outer recipient also lies much deeper than a flat
incident hull edge. -/
lemma one_tenth_lt_case2_b_abs_snd :
    (1 : ℝ) / 10 < |Erdos957Cases24.Case2.b 1| := by
  simp only [Erdos957Cases24.Case2.b,
    Erdos957Cases24.point_apply_one, abs_neg]
  rw [abs_of_pos (div_pos Erdos957Cases24.sqrtThree_pos (by norm_num))]
  nlinarith [Erdos957Cases24.sqrtThree_pos,
    Erdos957Cases24.sqrtThree_sq]

/-- Degree six at the actual selected middle supplies the checked canonical
Case-2 formula data in any honest normalized two-extreme frame. -/
theorem case2CanonicalRowData_of_normalized
    {A : Finset Point} {P : CyclicHullData A}
    (hA : IsOneSeparated A) {source : {p // p ∈ P.H}}
    {middle : Erdos957GeometryCore.Vertex A}
    {T : TwoExtremeCyclicWitness P source middle}
    (N : TwoExtremeNormalizedFrame source middle T)
    (hmiddleDegree : (unitDistanceGraph A).degree middle = 6) :
    Case2CanonicalRowData (N.frame.image A) := by
  have huPrev : Erdos957Cases24.Case2.uPrev ∈ N.frame.image A := by
    apply N.frame.mem_image_iff.mpr
    rw [N.side_actual]
    exact (cyclicSideVertex P source T.side).property
  have hu : Erdos957Cases24.Case2.u ∈ N.frame.image A := by
    apply N.frame.mem_image_iff.mpr
    rw [N.source_actual]
    exact source.1.property
  have hv : Erdos957Cases24.Case2.v ∈ N.frame.image A := by
    apply N.frame.mem_image_iff.mpr
    rw [N.middle_actual]
    exact middle.property
  have hvDegree : Erdos957Case24Bridge.unitDegree (N.frame.image A)
      Erdos957Cases24.Case2.v = 6 := by
    rw [N.frame.unitDegree_image_actual A, N.middle_actual]
    rw [← graph_degree_eq_unitDegree]
    exact hmiddleDegree
  exact case2CanonicalRowData_of_middle_degree_six
    (N.frame.image_oneSeparated hA) N.strict_support huPrev hu hv hvDegree

/-- Exact edge-pair coordinates of a canonical point in a predecessor-side
normalized frame. -/
lemma previous_edgePairCoord_actual
    {A : Finset Point} {P : CyclicHullData A}
    {source : {p // p ∈ P.H}} {middle : Erdos957GeometryCore.Vertex A}
    {T : TwoExtremeCyclicWitness P source middle}
    (N : TwoExtremeNormalizedFrame source middle T)
    (hside : T.side = CyclicSide.previous)
    (q : Erdos957Cases24.Point) :
    edgePairCoord source.1.1
      (source.1.1 - (P.next⁻¹ source).1.1) (N.frame.actual q) =
        (q 0, q 1) := by
  cases N.frame_spec with
  | previous _ hunit hframe =>
      have hc0 := congrArg (fun z : Point ↦ z 0)
        (N.frame.toCanonical_actual q)
      have hc1 := congrArg (fun z : Point ↦ z 1)
        (N.frame.toCanonical_actual q)
      rw [hframe] at hc0 hc1 ⊢
      change
        (edgePairCoord source.1.1
          (source.1.1 - (P.next⁻¹ source).1.1)
          ((Erdos957EdgeFrame.terminalUnitEdgeRigidChart
            (P.next⁻¹ source).1.1 source.1.1 hunit).actual q)).1 = q 0
          at hc0
      change
        (edgePairCoord source.1.1
          (source.1.1 - (P.next⁻¹ source).1.1)
          ((Erdos957EdgeFrame.terminalUnitEdgeRigidChart
            (P.next⁻¹ source).1.1 source.1.1 hunit).actual q)).2 = q 1
          at hc1
      apply Prod.ext
      · exact hc0
      · exact hc1
  | next hs _ _ =>
      have : CyclicSide.previous = CyclicSide.next := hside.symm.trans hs
      cases this

/-- Exact outgoing edge-pair coordinates of a canonical point in a
successor-side reflected normalized frame. -/
lemma next_edgePairCoord_actual
    {A : Finset Point} {P : CyclicHullData A}
    {source : {p // p ∈ P.H}} {middle : Erdos957GeometryCore.Vertex A}
    {T : TwoExtremeCyclicWitness P source middle}
    (N : TwoExtremeNormalizedFrame source middle T)
    (hside : T.side = CyclicSide.next)
    (q : Erdos957Cases24.Point) :
    edgePairCoord source.1.1
      ((P.next source).1.1 - source.1.1) (N.frame.actual q) =
        (-q 0, q 1) := by
  cases N.frame_spec with
  | previous hs _ _ =>
      have : CyclicSide.previous = CyclicSide.next := hs.symm.trans hside
      cases this
  | next _ hunit hframe =>
      rw [hframe]
      have hc :=
        (Erdos957TwoExtremeAligned.reflectedSuccessorUnitEdgeRigidChart
          P source hunit).toCanonical_actual q
      have hf :=
        Erdos957TwoExtremeAligned.reflectedSuccessorUnitEdgeRigidChart_toCanonical
          P source hunit
            ((Erdos957TwoExtremeAligned.reflectedSuccessorUnitEdgeRigidChart
              P source hunit).actual q)
      rw [hf] at hc
      apply Prod.ext
      · have hx := congrArg (fun z : Point ↦ z 0) hc
        simpa [edgePointCoord_apply_zero] using congrArg Neg.neg hx
      · simpa [edgePointCoord_apply_one] using
          congrArg (fun z : Point ↦ z 1) hc

/-- A canonical recipient whose edge-chart horizontal coordinate is at most
`3/2` lies in the common `7/4` bisector strip.  This is the side-uniform
adapter from the retained normalized frame to the produced bisector chart. -/
theorem normalized_actual_horizontal_le_seven_four
    {A : Finset Point} (O : CyclicHullOrder A)
    (L : LiftedCyclicHullOrder O)
    (W : DiameterWitnessData (cyclicHullDataOfOrder O L))
    (source : {p // p ∈ (cyclicHullDataOfOrder O L).H})
    (hs : source.1 ∈ sourceVertices (cyclicHullDataOfOrder O L) W)
    {middle : Erdos957GeometryCore.Vertex A}
    {T : TwoExtremeCyclicWitness (cyclicHullDataOfOrder O L) source middle}
    (N : TwoExtremeNormalizedFrame source middle T)
    (q : Erdos957Cases24.Point) (hq : N.frame.actual q ∈ A)
    (hpath : WithinTwoUnitEdges source.1 (actualVertex N.frame q hq))
    (hx : |q 0| ≤ (3 : ℝ) / 2) :
    |((bisectorAlignedChartData O L).coord source
      (actualVertex N.frame q hq)).1| ≤ (7 : ℝ) / 4 := by
  let P := cyclicHullDataOfOrder O L
  let a := (indexEquivLiftedHull O).symm source
  have ha : indexEquivLiftedHull O a = source :=
    (indexEquivLiftedHull O).apply_symm_apply source
  have hsourcePoint : (source.1 : Point) = O.vertex a := by
    rw [← ha]
    exact indexEquivLiftedHull_point O a
  have hprevIndex : P.next⁻¹ source =
      indexEquivLiftedHull O (previousIndex a) := by
    rw [← ha]
    change (hullNext O).symm (indexEquivLiftedHull O a) = _
    simpa [previousIndex] using hullNext_symm_indexEquiv O (Fin.pos a) a
  have hnextIndex : P.next source =
      indexEquivLiftedHull O (finRotate (hullVertexCount A) a) := by
    rw [← ha]
    exact hullNext_indexEquiv O a
  have hprevPoint : (((P.next⁻¹ source).1 : Erdos957GeometryCore.Vertex A) : Point) =
      O.vertex (previousIndex a) := by
    rw [hprevIndex]
    exact indexEquivLiftedHull_point O (previousIndex a)
  have hnextPoint : (((P.next source).1 : Erdos957GeometryCore.Vertex A) : Point) =
      O.vertex (finRotate (hullVertexCount A) a) := by
    rw [hnextIndex]
    exact indexEquivLiftedHull_point O _
  have hflat : P.IsFlat source := source_isFlat P W source hs
  have hturn : P.turn (indexEquivLiftedHull O a) < Real.pi / 180 := by
    simpa [ha] using P.turn_lt_of_isFlat source hflat
  have hradius : dist (source.1 : Point)
      (actualVertex N.frame q hq : Point) ≤ 2 :=
    Erdos957GeometryLocalityBridge.dist_le_two_of_withinTwoUnitEdges hpath
  cases N.frame_spec with
  | previous hside hunit _ =>
      have hedgeCoord := previous_edgePairCoord_actual N hside q
      have hedge : |(edgePairCoord (source.1 : Point)
          ((source.1 : Point) - ((P.next⁻¹ source).1 : Point))
          (actualVertex N.frame q hq : Point)).1| ≤ (3 : ℝ) / 2 := by
        rw [show (actualVertex N.frame q hq : Point) = N.frame.actual q by rfl]
        rw [congrArg Prod.fst hedgeCoord]
        exact hx
      have hunit' : dist (O.vertex (previousIndex a)) (O.vertex a) = 1 := by
        rw [← hsourcePoint, ← hprevPoint]
        exact hunit
      have hturn' : (cyclicHullDataOfOrder O L).turn
          (indexEquivLiftedHull O a) < Real.pi / 180 := by
        simpa [P] using hturn
      have hradius' : dist (O.vertex a)
          (actualVertex N.frame q hq : Point) ≤ 2 := by
        rw [← hsourcePoint]
        exact hradius
      have hedge' : |(edgePairCoord (O.vertex a)
          (O.vertex a - O.vertex (previousIndex a))
          (actualVertex N.frame q hq : Point)).1| ≤ (3 : ℝ) / 2 := by
        rw [← hsourcePoint, ← hprevPoint]
        exact hedge
      have hresult := incoming_edge_recipient_horizontal_le_seven_four
        L a (actualVertex N.frame q hq) hunit' hturn' hradius' hedge'
      simpa only [ha] using hresult
  | next hside hunit _ =>
      have hedgeCoord := next_edgePairCoord_actual N hside q
      have hedge : |(edgePairCoord (source.1 : Point)
          (((P.next source).1 : Point) - (source.1 : Point))
          (actualVertex N.frame q hq : Point)).1| ≤ (3 : ℝ) / 2 := by
        rw [show (actualVertex N.frame q hq : Point) = N.frame.actual q by rfl]
        rw [congrArg Prod.fst hedgeCoord]
        simpa using hx
      have hunit' : dist (O.vertex a)
          (O.vertex (finRotate (hullVertexCount A) a)) = 1 := by
        rw [← hsourcePoint, ← hnextPoint]
        exact hunit
      have hturn' : (cyclicHullDataOfOrder O L).turn
          (indexEquivLiftedHull O a) < Real.pi / 180 := by
        simpa [P] using hturn
      have hradius' : dist (O.vertex a)
          (actualVertex N.frame q hq : Point) ≤ 2 := by
        rw [← hsourcePoint]
        exact hradius
      have hedge' : |(edgePairCoord (O.vertex a)
          (O.vertex (finRotate (hullVertexCount A) a) - O.vertex a)
          (actualVertex N.frame q hq : Point)).1| ≤ (3 : ℝ) / 2 := by
        rw [← hsourcePoint, ← hnextPoint]
        exact hedge
      have hresult := outgoing_edge_recipient_horizontal_le_seven_four
        L a (actualVertex N.frame q hq) hunit' hturn' hradius' hedge'
      simpa only [ha] using hresult

/-- A retained canonical recipient is non-extreme once its formula excludes
the two normalized edge endpoints and its depth exceeds the possible height
of the other incident flat hull vertex. -/
theorem normalized_actual_not_mem_hull
    {A : Finset Point} (hA : IsOneSeparated A) (O : CyclicHullOrder A)
    (L : LiftedCyclicHullOrder O)
    (W : DiameterWitnessData (cyclicHullDataOfOrder O L))
    (source : {p // p ∈ (cyclicHullDataOfOrder O L).H})
    (hs : source.1 ∈ sourceVertices (cyclicHullDataOfOrder O L) W)
    (hwindow : LocalHullWindowHypothesis (cyclicHullDataOfOrder O L) source)
    {middle : Erdos957GeometryCore.Vertex A}
    {T : TwoExtremeCyclicWitness (cyclicHullDataOfOrder O L) source middle}
    (N : TwoExtremeNormalizedFrame source middle T)
    (q : Erdos957Cases24.Point) (hq : N.frame.actual q ∈ A)
    (hpath : WithinTwoUnitEdges source.1 (actualVertex N.frame q hq))
    (hhorizontal : |((bisectorAlignedChartData O L).coord source
      (actualVertex N.frame q hq)).1| ≤ (7 : ℝ) / 4)
    (hneU : q ≠ Erdos957Cases24.Case2.u)
    (hnePrev : q ≠ Erdos957Cases24.Case2.uPrev)
    (hdepth : (1 : ℝ) / 10 < |q 1|) :
    actualVertex N.frame q hq ∉ (cyclicHullDataOfOrder O L).H := by
  let P := cyclicHullDataOfOrder O L
  let v := actualVertex N.frame q hq
  let a := (indexEquivLiftedHull O).symm source
  have ha : indexEquivLiftedHull O a = source :=
    (indexEquivLiftedHull O).apply_symm_apply source
  have hsourcePoint : (source.1 : Point) = O.vertex a := by
    rw [← ha]
    exact indexEquivLiftedHull_point O a
  have hprevIndex : P.next⁻¹ source =
      indexEquivLiftedHull O (previousIndex a) := by
    rw [← ha]
    change (hullNext O).symm (indexEquivLiftedHull O a) = _
    simpa [previousIndex] using hullNext_symm_indexEquiv O (Fin.pos a) a
  have hnextIndex : P.next source =
      indexEquivLiftedHull O (finRotate (hullVertexCount A) a) := by
    rw [← ha]
    exact hullNext_indexEquiv O a
  have hprevPoint : (((P.next⁻¹ source).1 :
      Erdos957GeometryCore.Vertex A) : Point) = O.vertex (previousIndex a) := by
    rw [hprevIndex]
    exact indexEquivLiftedHull_point O _
  have hnextPoint : (((P.next source).1 :
      Erdos957GeometryCore.Vertex A) : Point) =
      O.vertex (finRotate (hullVertexCount A) a) := by
    rw [hnextIndex]
    exact indexEquivLiftedHull_point O _
  have hflat : P.IsFlat source := source_isFlat P W source hs
  have hturn : P.turn (indexEquivLiftedHull O a) < Real.pi / 180 := by
    simpa [ha] using P.turn_lt_of_isFlat source hflat
  have hradius : dist (source.1 : Point) (v : Point) ≤ 2 :=
    Erdos957GeometryLocalityBridge.dist_le_two_of_withinTwoUnitEdges hpath
  have hneSource : v ≠ source.1 := by
    intro h
    apply hneU
    apply N.frame.actual_injective
    rw [N.source_actual]
    exact congrArg Subtype.val h
  have hneSide : v ≠ cyclicSideVertex P source T.side := by
    intro h
    apply hnePrev
    apply N.frame.actual_injective
    rw [N.side_actual]
    exact congrArg Subtype.val h
  dsimp [P] at hneSide
  cases N.frame_spec with
  | previous hside hunit _ =>
      have hneOther : v ≠ (P.next source).1 := by
        intro h
        have hradiusNext : dist (O.vertex a)
            (O.vertex (finRotate (hullVertexCount A) a)) ≤ 2 := by
          rw [← hsourcePoint, ← hnextPoint]
          rw [← show (v : Point) = ((P.next source).1 : Point) by
            exact congrArg Subtype.val h]
          exact hradius
        have hunit' : dist (O.vertex (previousIndex a)) (O.vertex a) = 1 := by
          rw [← hsourcePoint, ← hprevPoint]
          exact hunit
        have hheight := outgoing_edge_terminal_height_abs_lt_one_tenth
          L a hunit' (by simpa [P] using hturn) hradiusNext
        have hcoord := congrArg Prod.snd
          (previous_edgePairCoord_actual N hside q)
        have hheight' : |(edgePairCoord (source.1 : Point)
            ((source.1 : Point) - ((P.next⁻¹ source).1 : Point))
            (N.frame.actual q)).2| < (1 : ℝ) / 10 := by
          rw [hsourcePoint, hprevPoint]
          rw [show N.frame.actual q = ((P.next source).1 : Point) by
            exact congrArg Subtype.val h]
          rw [hnextPoint]
          exact hheight
        rw [hcoord] at hheight'
        exact (not_lt_of_ge hdepth.le) hheight'
      apply not_mem_hull_of_local_window_of_abs_fst_le
        (bisectorFlatAlignedFrameData O L hA) source hflat hwindow v
      · exact hpath
      · exact hhorizontal
      · exact hneSource
      · intro hv
        apply hneSide
        rw [hside]
        simpa [cyclicSideVertex] using hv
      · exact hneOther
  | next hside hunit _ =>
      have hneOther : v ≠ (P.next⁻¹ source).1 := by
        intro h
        have hradiusPrev : dist (O.vertex a)
            (O.vertex (previousIndex a)) ≤ 2 := by
          rw [← hsourcePoint, ← hprevPoint]
          rw [← show (v : Point) = ((P.next⁻¹ source).1 : Point) by
            exact congrArg Subtype.val h]
          exact hradius
        have hunit' : dist (O.vertex a)
            (O.vertex (finRotate (hullVertexCount A) a)) = 1 := by
          rw [← hsourcePoint, ← hnextPoint]
          exact hunit
        have hheight := incoming_edge_outgoing_height_abs_lt_one_tenth
          L a hunit' (by simpa [P] using hturn) hradiusPrev
        have hcoord := congrArg Prod.snd
          (next_edgePairCoord_actual N hside q)
        have hheight' : |(edgePairCoord (source.1 : Point)
            (((P.next source).1 : Point) - (source.1 : Point))
            (N.frame.actual q)).2| < (1 : ℝ) / 10 := by
          rw [hsourcePoint, hnextPoint]
          rw [show N.frame.actual q = ((P.next⁻¹ source).1 : Point) by
            exact congrArg Subtype.val h]
          rw [hprevPoint]
          exact hheight
        rw [hcoord] at hheight'
        exact (not_lt_of_ge hdepth.le) hheight'
      apply not_mem_hull_of_local_window_of_abs_fst_le
        (bisectorFlatAlignedFrameData O L hA) source hflat hwindow v
      · exact hpath
      · exact hhorizontal
      · exact hneSource
      · exact hneOther
      · intro hv
        apply hneSide
        rw [hside]
        simpa [cyclicSideVertex] using hv

/-- Honest source-level realization of Case 2 in the produced bisector
frame.  The normalized side, canonical recipient formulas, non-extremality,
and horizontal-strip bounds are all constructed from the genuine cyclic
data; no collision or capacity premise is used. -/
theorem exists_realized_case2
    {A : Finset Point} (hA : IsOneSeparated A) (O : CyclicHullOrder A)
    (L : LiftedCyclicHullOrder O)
    (W : DiameterWitnessData (cyclicHullDataOfOrder O L))
    (source : {p // p ∈ (cyclicHullDataOfOrder O L).H})
    (hs : source.1 ∈ sourceVertices (cyclicHullDataOfOrder O L) W)
    (hwindow : LocalHullWindowHypothesis (cyclicHullDataOfOrder O L) source)
    (middle : Erdos957GeometryCore.Vertex A)
    (hsourceMiddle : (unitDistanceGraph A).Adj source.1 middle)
    (hmiddleCone : Erdos957Cases13.InOpenMiddleCone
      ((bisectorAlignedChartData O L).coord source middle))
    (hmiddleDegree : (unitDistanceGraph A).degree middle = 6)
    (htwo : (hullUnitNeighbors (cyclicHullDataOfOrder O L) middle).card = 2) :
    ∃ (T : TwoExtremeCyclicWitness
          (cyclicHullDataOfOrder O L) source middle)
      (N : TwoExtremeNormalizedFrame source middle T)
      (row : Case2ActualRow (cyclicHullDataOfOrder O L)
        (bisectorAlignedChartData O L) source N.frame)
      (R : RealizedSourceRow (cyclicHullDataOfOrder O L)
        (bisectorAlignedChartData O L) source),
      R = .case2 middle hmiddleDegree htwo
        (middle_not_mem_hull_of_local_window
          (bisectorFlatAlignedFrameData O L hA) source
          (source_isFlat (cyclicHullDataOfOrder O L) W source hs)
          hwindow middle hsourceMiddle hmiddleCone) T N row ∧
        R.localCase = row.localCase := by
  let P := cyclicHullDataOfOrder O L
  let C := bisectorAlignedChartData O L
  let F := bisectorFlatAlignedFrameData O L hA
  have hseven : ∀ w : Erdos957GeometryCore.Vertex A, w ∈ P.H →
      (unitDistanceGraph A).Adj middle w →
        w ∈ Erdos957MiddleLocalization.sevenHullWindow P source := by
    intro w hw hmw
    exact hwindow w hw (Or.inr ⟨middle, hsourceMiddle, hmw⟩)
  obtain ⟨T⟩ := twoExtremeCyclicWitness_of_seven_window
    hA P F W source middle hs hsourceMiddle hmiddleCone hseven htwo
  have hstrict : ∀ q : Erdos957GeometryCore.Vertex A, q ≠ source.1 →
      (C.coord source q).2 < 0 := by
    intro q hq
    exact bisectorAlignedChartData_coord_snd_neg O L source q hq
  obtain ⟨N⟩ := exists_twoExtremeNormalizedFrame hA P C source middle T
    hstrict (source_facts hs).2.2 hsourceMiddle hmiddleCone
  let D := case2CanonicalRowData_of_normalized hA N hmiddleDegree
  let s := Erdos957Cases24.Case2.secondaryRecipient
    (Erdos957Case24Bridge.unitDegree (N.frame.image A)
      Erdos957Cases24.Case2.w)
    (Erdos957Case24Bridge.unitDegree (N.frame.image A)
      Erdos957Cases24.Case2.wNext)
  have huA : N.frame.actual Erdos957Cases24.Case2.u ∈ A := by
    rw [N.source_actual]
    exact source.1.property
  have hvA : N.frame.actual Erdos957Cases24.Case2.v ∈ A := by
    rw [N.middle_actual]
    exact middle.property
  have hbA : N.frame.actual Erdos957Cases24.Case2.b ∈ A :=
    N.frame.mem_image_iff.mp D.outer_mem
  have hsA : N.frame.actual s ∈ A := by
    exact N.frame.mem_image_iff.mp D.secondary_mem
  let outerV := actualVertex N.frame Erdos957Cases24.Case2.b hbA
  let secondaryV := actualVertex N.frame s hsA
  have hsourceVertex : actualVertex N.frame Erdos957Cases24.Case2.u huA =
      source.1 := by
    apply Subtype.ext
    exact N.source_actual
  have houterPath : WithinTwoUnitEdges source.1 outerV := by
    rw [← hsourceVertex]
    exact Or.inl (actualVertex_adj N.frame huA hbA
      Erdos957Cases24.Case2.dist_u_b)
  have hbImage : N.frame.actual Erdos957Cases24.Case2.b ∈ A := hbA
  have hsecondaryPath : WithinTwoUnitEdges source.1 secondaryV := by
    rw [← hsourceVertex]
    exact actual_case2_secondary_within_two N.frame huA hvA hbImage hsA
  have houterHorizontal : |(C.coord source outerV).1| ≤ (7 : ℝ) / 4 := by
    exact normalized_actual_horizontal_le_seven_four O L W source hs N
      Erdos957Cases24.Case2.b hbA houterPath (by
        norm_num [Erdos957Cases24.Case2.b])
  have hsecondaryHorizontal : |(C.coord source secondaryV).1| ≤
      (7 : ℝ) / 4 := by
    exact normalized_actual_horizontal_le_seven_four O L W source hs N
      s hsA hsecondaryPath (by
        exact secondaryRecipient_abs_fst_le_three_halves _ _)
  have houterNot : outerV ∉ P.H := by
    apply normalized_actual_not_mem_hull hA O L W source hs hwindow N
      Erdos957Cases24.Case2.b hbA houterPath houterHorizontal
    · norm_num [Erdos957Cases24.Case2.b, Erdos957Cases24.Case2.u,
        Erdos957Cases24.point_inj]
    · norm_num [Erdos957Cases24.Case2.b, Erdos957Cases24.Case2.uPrev,
        Erdos957Cases24.point_inj]
    · exact one_tenth_lt_case2_b_abs_snd
  have hsecondaryNot : secondaryV ∉ P.H := by
    apply normalized_actual_not_mem_hull hA O L W source hs hwindow N
      s hsA hsecondaryPath hsecondaryHorizontal
    · exact secondaryRecipient_ne_u _ _
    · exact secondaryRecipient_ne_uPrev _ _
    · exact one_tenth_lt_secondaryRecipient_abs_snd _ _
  obtain ⟨row⟩ := case2ActualRow_of_canonicalData P C source N.frame D
    N.source_actual hvA houterNot hsecondaryNot
      houterHorizontal hsecondaryHorizontal
  have hmiddleNot : middle ∉ P.H :=
    middle_not_mem_hull_of_local_window F source
      (source_isFlat P W source hs) hwindow middle hsourceMiddle hmiddleCone
  let R : RealizedSourceRow P C source :=
    .case2 middle hmiddleDegree htwo hmiddleNot T N row
  refine ⟨T, N, row, R, rfl, ?_⟩
  rfl

end Erdos957Case2RealizedRows
