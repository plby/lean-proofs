import ErdosProblems.Erdos957.Case4CommonAssociations
import ErdosProblems.Erdos957.Case4CollisionLeaves
import ErdosProblems.Erdos957.Case4SplitClassification
import ErdosProblems.Erdos957.DirectSameSide
import ErdosProblems.Erdos957.EdgeConeTransport

noncomputable section

namespace Erdos957Case4DirectSameSide

open Erdos957GeometryCore
open Erdos957GeometryLocalRows
open Erdos957CaseClassification
open Erdos957CoherentRealizedRows
open Erdos957CollisionInstantiation
open Erdos957RoleCollisions
open Erdos957Case4CollisionLeaves
open Erdos957Case4CommonAssociations
open Erdos957Case4SplitClassification
open Erdos957Case4NoThree

abbrev Point := Erdos957GeometryCore.Point

variable {A : Finset Point} {P : CyclicHullData A}
variable {W : DiameterWitnessData P} {F : P.FlatAlignedFrameData}

lemma polar_unit_displacement_bounds
    {a b : ℝ × ℝ} {r theta : ℝ}
    (hpolar : Erdos957Locality.IsPolarEdge a b r theta)
    (hr : 1 ≤ r) (hangle : |theta| ≤ Real.pi / 45)
    (hunit : Erdos957Cases13.sqDist a b = 1) :
    (399 / 400 : ℝ) ≤ b.1 - a.1 ∧
      |b.2 - a.2| ≤ (7 / 100 : ℝ) := by
  have htrig := Real.sin_sq_add_cos_sq theta
  have hrSq : r ^ 2 = 1 := by
    rcases hpolar with ⟨hx, hy⟩
    simp only [Erdos957Cases13.sqDist] at hunit
    calc
      r ^ 2 = r ^ 2 * (Real.sin theta ^ 2 + Real.cos theta ^ 2) := by
        rw [htrig]
        ring
      _ = (b.1 - a.1) ^ 2 + (b.2 - a.2) ^ 2 := by
        rw [hx, hy]
        ring
      _ = 1 := by nlinarith [hunit]
  have hrOne : r = 1 := by nlinarith
  have hx := Erdos957Locality.horizontal_increment_gt_three_nine_nine_div_four_hundred
    hr hangle hpolar.1
  constructor
  · exact hx.le
  · rw [hpolar.2, hrOne, one_mul]
    exact (Real.abs_sin_le_abs.trans hangle).trans (by
      nlinarith [Real.pi_lt_d2] : Real.pi / 45 ≤ (7 / 100 : ℝ))

/-- Exact change of coordinates between a literal unit-edge chart and the
aligned chart based at the competing source. -/
lemma edgePairDisplacement_eq_aligned
    (C : P.AlignedChartData) (source : {p // p ∈ P.H})
    (p o q : Vertex A) (hunit : dist (p : Point) (o : Point) = 1) :
    let e := CyclicHullData.pairSub (C.coord source o) (C.coord source p)
    let x := C.coord source q
    let z := CyclicHullData.pairSub
      (Erdos957EdgeFrame.edgePairCoord (o : Point) ((o : Point) - p) q)
      (Erdos957EdgeFrame.edgePairCoord (o : Point) ((o : Point) - p) source.1)
    z = pairEdgeTransform e x := by
  let e := CyclicHullData.pairSub (C.coord source o) (C.coord source p)
  let x := C.coord source q
  let z := CyclicHullData.pairSub
    (Erdos957EdgeFrame.edgePairCoord (o : Point) ((o : Point) - p) q)
    (Erdos957EdgeFrame.edgePairCoord (o : Point) ((o : Point) - p) source.1)
  have hs := C.coord_source source
  have hdot : z.1 = pairDot e x := by
    have hpo := C.sqDist_coord source p o
    have hps := C.sqDist_coord source p source.1
    have hos := C.sqDist_coord source o source.1
    have hpq := C.sqDist_coord source p q
    have hoq := C.sqDist_coord source o q
    rw [Erdos957Cases24.dist_sq_eq_coordinates] at hps hos hpq hoq
    simp only [z, Erdos957EdgeFrame.edgePairCoord,
      CyclicHullData.pairSub, PiLp.sub_apply, pairDot, e, x,
      Erdos957Cases13.sqDist, hs] at hpo hps hos hpq hoq ⊢
    ring_nf at hps hos hpq hoq ⊢
    nlinarith [hps, hos, hpq, hoq]
  have hcross : z.2 = CyclicHullData.pairCross e x := by
    have hcq := C.cross_displacements source p o q
    have hcs := C.cross_displacements source p o source.1
    simp only [z, Erdos957EdgeFrame.edgePairCoord,
      CyclicHullData.pairSub, CyclicHullData.pairCross,
      PiLp.sub_apply, e, x, hs,
      Erdos957GeometryCore.cross] at hcq hcs ⊢
    ring_nf at hcq hcs ⊢
    linarith
  apply Prod.ext
  · simpa [pairEdgeTransform] using hdot
  · simpa [pairEdgeTransform] using hcross

/-- At either source position left by `DirectNearTwo`, the common Case-4
edge is still almost horizontal in that source's aligned chart. -/
lemma commonPairEdge_direction_bounds_at_near_source
    (F : P.FlatAlignedFrameData) (source t : {p // p ∈ P.H})
    (middle : Vertex A) (T : TwoExtremeCyclicWitness P source middle)
    (E : ActualCase24Rows.TwoExtremeCommonPairFrame source middle T)
    (htFlat : P.IsFlat t)
    (hnear : t = incidentContinuationHullVertex P source T.side 1 ∨
      t = Erdos957Case4NoThree.awayHullVertex P source T.side 0) :
    let p := ActualCase24Rows.case4PairEdgeBase T
    let o := P.next p
    let e := CyclicHullData.pairSub
      (F.chart.coord t o.1) (F.chart.coord t p.1)
    (399 / 400 : ℝ) ≤ e.1 ∧ |e.2| ≤ (7 / 100 : ℝ) := by
  let p := ActualCase24Rows.case4PairEdgeBase T
  let o := P.next p
  let e := CyclicHullData.pairSub
    (F.chart.coord t o.1) (F.chart.coord t p.1)
  have rightAngleOne : |F.rightAngle t 1| ≤ Real.pi / 45 := by
    obtain ⟨h0, h1, -, -⟩ := F.rightFlatAngles t htFlat
    have h := abs_add_le (F.rightAngle t 1 - F.rightAngle t 0)
      (F.rightAngle t 0)
    have heq : F.rightAngle t 1 =
        (F.rightAngle t 1 - F.rightAngle t 0) + F.rightAngle t 0 := by ring
    rw [← heq] at h
    nlinarith [Real.pi_pos]
  have leftAngleOne : |F.leftAngle t 1| ≤ Real.pi / 45 := by
    obtain ⟨h0, h1, -, -⟩ := F.leftFlatAngles t htFlat
    have h := abs_add_le (F.leftAngle t 1 - F.leftAngle t 0)
      (F.leftAngle t 0)
    have heq : F.leftAngle t 1 =
        (F.leftAngle t 1 - F.leftAngle t 0) + F.leftAngle t 0 := by ring
    rw [← heq] at h
    nlinarith [Real.pi_pos]
  cases hside : T.side with
  | previous =>
      rcases hnear with hincident | haway
      · have ht : t = (P.next⁻¹ ^ 2) source := by
          simpa [incidentContinuationHullVertex, hside] using hincident
        have hunit : Erdos957Cases13.sqDist
            (F.chart.rightOrbitCoord P t 1)
            (F.chart.rightOrbitCoord P t 2) = 1 := by
          simp only [CyclicHullData.AlignedChartData.rightOrbitCoord]
          rw [F.chart.sqDist_coord]
          have hd : dist (((P.next ^ 1) t).1 : Point)
              (((P.next ^ 2) t).1 : Point) = 1 := by
            rw [ht]
            simpa [p, o, ActualCase24Rows.case4PairEdgeBase, hside,
              pow_succ] using E.edge_unit
          rw [hd]
          norm_num
        have hb := polar_unit_displacement_bounds
          (F.rightPolar t 1) (F.rightRadius_ge_one t 1)
          rightAngleOne hunit
        simpa [e, p, o, ActualCase24Rows.case4PairEdgeBase, hside,
          CyclicHullData.AlignedChartData.rightOrbitCoord, ht, pow_succ,
          CyclicHullData.pairSub] using hb
      · have ht : t = P.next source := by
          simpa [Erdos957Case4NoThree.awayHullVertex, hside] using haway
        have hunit : Erdos957Cases13.sqDist
            (F.chart.leftOrbitReflectedCoord P t 1)
            (F.chart.leftOrbitReflectedCoord P t 2) = 1 := by
          have hd : dist (((P.next⁻¹ ^ 1) t).1 : Point)
              (((P.next⁻¹ ^ 2) t).1 : Point) = 1 := by
            rw [ht]
            simpa [p, o, ActualCase24Rows.case4PairEdgeBase, hside,
              pow_succ, dist_comm] using E.edge_unit
          have hC := F.chart.sqDist_coord t
            (((P.next⁻¹ ^ 1) t).1) (((P.next⁻¹ ^ 2) t).1)
          rw [hd] at hC
          simp only [CyclicHullData.AlignedChartData.leftOrbitReflectedCoord,
            Erdos957Cases13.sqDist, one_pow] at hC ⊢
          nlinarith
        have hb := polar_unit_displacement_bounds
          (F.leftPolar t 1) (F.leftRadius_ge_one t 1)
          leftAngleOne hunit
        change (399 / 400 : ℝ) ≤ e.1 ∧ |e.2| ≤ (7 / 100 : ℝ)
        rcases hb with ⟨hbx, hby⟩
        constructor
        · simp [e, p, o, ActualCase24Rows.case4PairEdgeBase, hside,
            CyclicHullData.AlignedChartData.leftOrbitReflectedCoord, ht,
            pow_succ, CyclicHullData.pairSub] at hbx ⊢
          linarith
        · have hp : p = P.next⁻¹ source := by
            simp [p, ActualCase24Rows.case4PairEdgeBase, hside]
          have ho : o = source := by
            rw [show o = P.next p from rfl, hp]
            simp
          have hk1 : (P.next⁻¹ ^ 1) t = o := by rw [ho, ht]; simp
          have hk2 : (P.next⁻¹ ^ 2) t = p := by
            rw [hp, ht]
            simp [pow_succ]
          norm_num at hby
          have hby' :
              |(F.chart.coord t p.1).2 - (F.chart.coord t o.1).2| ≤
                (7 / 100 : ℝ) := by
            simpa only [CyclicHullData.AlignedChartData.leftOrbitReflectedCoord,
              hk1, hk2] using hby
          change |(F.chart.coord t o.1).2 - (F.chart.coord t p.1).2| ≤
            (7 / 100 : ℝ)
          simpa only [abs_sub_comm] using hby'
  | next =>
      rcases hnear with hincident | haway
      · have ht : t = (P.next ^ 2) source := by
          simpa [incidentContinuationHullVertex, hside] using hincident
        have hunit : Erdos957Cases13.sqDist
            (F.chart.leftOrbitReflectedCoord P t 1)
            (F.chart.leftOrbitReflectedCoord P t 2) = 1 := by
          have hd : dist (((P.next⁻¹ ^ 1) t).1 : Point)
              (((P.next⁻¹ ^ 2) t).1 : Point) = 1 := by
            rw [ht]
            simpa [p, o, ActualCase24Rows.case4PairEdgeBase, hside,
              pow_succ, dist_comm] using E.edge_unit
          have hC := F.chart.sqDist_coord t
            (((P.next⁻¹ ^ 1) t).1) (((P.next⁻¹ ^ 2) t).1)
          rw [hd] at hC
          simp only [CyclicHullData.AlignedChartData.leftOrbitReflectedCoord,
            Erdos957Cases13.sqDist, one_pow] at hC ⊢
          nlinarith
        have hb := polar_unit_displacement_bounds
          (F.leftPolar t 1) (F.leftRadius_ge_one t 1)
          leftAngleOne hunit
        change (399 / 400 : ℝ) ≤ e.1 ∧ |e.2| ≤ (7 / 100 : ℝ)
        rcases hb with ⟨hbx, hby⟩
        constructor
        · simp [e, p, o, ActualCase24Rows.case4PairEdgeBase, hside,
            CyclicHullData.AlignedChartData.leftOrbitReflectedCoord, ht,
            pow_succ, CyclicHullData.pairSub] at hbx ⊢
          linarith
        · have hp : p = source := by
            simp [p, ActualCase24Rows.case4PairEdgeBase, hside]
          have ho : o = P.next source := by rw [show o = P.next p from rfl, hp]
          have hk1 : (P.next⁻¹ ^ 1) t = o := by
            rw [ho, ht]
            simp [pow_succ]
          have hk2 : (P.next⁻¹ ^ 2) t = p := by
            rw [hp, ht]
            simp [pow_succ]
          norm_num at hby
          have hby' :
              |(F.chart.coord t p.1).2 - (F.chart.coord t o.1).2| ≤
                (7 / 100 : ℝ) := by
            simpa only [CyclicHullData.AlignedChartData.leftOrbitReflectedCoord,
              hk1, hk2] using hby
          change |(F.chart.coord t o.1).2 - (F.chart.coord t p.1).2| ≤
            (7 / 100 : ℝ)
          simpa only [abs_sub_comm] using hby'
      · have ht : t = P.next⁻¹ source := by
          simpa [Erdos957Case4NoThree.awayHullVertex, hside] using haway
        have hunit : Erdos957Cases13.sqDist
            (F.chart.rightOrbitCoord P t 1)
            (F.chart.rightOrbitCoord P t 2) = 1 := by
          simp only [CyclicHullData.AlignedChartData.rightOrbitCoord]
          rw [F.chart.sqDist_coord]
          have hd : dist (((P.next ^ 1) t).1 : Point)
              (((P.next ^ 2) t).1 : Point) = 1 := by
            rw [ht]
            simpa [p, o, ActualCase24Rows.case4PairEdgeBase, hside,
              pow_succ] using E.edge_unit
          rw [hd]
          norm_num
        have hb := polar_unit_displacement_bounds
          (F.rightPolar t 1) (F.rightRadius_ge_one t 1)
          rightAngleOne hunit
        simpa [e, p, o, ActualCase24Rows.case4PairEdgeBase, hside,
          CyclicHullData.AlignedChartData.rightOrbitCoord, ht, pow_succ,
          CyclicHullData.pairSub] using hb

lemma residual_unit_from_right_shallow_forces_pos
    {q p : Point}
    (hqLower : q 1 ≤ Erdos957Cases24.Case2.v 1)
    (hpx : (399 / 400 : ℝ) < p 0)
    (hpy : -p 1 ≤ p 0 / 10)
    (hdist : dist p q = 1) :
    0 < q 0 := by
  by_contra hnot
  have hqx : q 0 ≤ 0 := le_of_not_gt hnot
  have hsqrt : (3 / 2 : ℝ) < Erdos957Cases24.sqrtThree := by
    nlinarith only [Erdos957Cases24.sqrtThree_pos,
      Erdos957Cases24.sqrtThree_sq]
  have hqY : q 1 < -(3 / 4 : ℝ) := by
    simp only [Erdos957Cases24.Case2.v,
      Erdos957Cases24.point_apply_one] at hqLower
    linarith only [hqLower, hsqrt]
  have hdistSq := Erdos957Cases24.dist_sq_eq_coordinates p q
  rw [hdist] at hdistSq
  by_cases hpLarge : (3 / 2 : ℝ) ≤ p 0
  · have hx : 1 < (p 0 - q 0) ^ 2 := by
      nlinarith only [hpLarge, hqx, sq_nonneg (p 0 - q 0 - 1)]
    nlinarith only [hdistSq, hx, sq_nonneg (p 1 - q 1)]
  · have hpUpper : p 0 < 3 / 2 := lt_of_not_ge hpLarge
    have hpY : -(3 / 20 : ℝ) < p 1 := by
      linarith only [hpy, hpUpper]
    have hx : (399 / 400 : ℝ) < p 0 - q 0 := by
      linarith only [hpx, hqx]
    have hy : (3 / 5 : ℝ) < p 1 - q 1 := by
      linarith only [hpY, hqY]
    have hxSq : (399 / 400 : ℝ) ^ 2 < (p 0 - q 0) ^ 2 := by
      nlinarith only [hx, sq_nonneg (p 0 - q 0 - 399 / 400)]
    have hySq : (3 / 5 : ℝ) ^ 2 < (p 1 - q 1) ^ 2 := by
      nlinarith only [hy, sq_nonneg (p 1 - q 1 - 3 / 5)]
    norm_num at hxSq hySq
    nlinarith only [hdistSq, hxSq, hySq]

lemma residual_unit_from_left_shallow_forces_neg
    {q p : Point}
    (hqLower : q 1 ≤ Erdos957Cases24.Case2.v 1)
    (hpx : (399 / 400 : ℝ) < -p 0)
    (hpy : -p 1 ≤ (-p 0) / 10)
    (hdist : dist p q = 1) :
    q 0 < 0 := by
  let reflect : Point → Point := fun z ↦ Erdos957Cases24.point (-z 0) (z 1)
  have hdistEq : dist (reflect p) (reflect q) = dist p q := by
    have hs : dist (reflect p) (reflect q) ^ 2 = dist p q ^ 2 := by
      rw [Erdos957Cases24.dist_sq_eq_coordinates,
        Erdos957Cases24.dist_sq_eq_coordinates]
      simp [reflect, Erdos957Cases24.point_apply_zero,
        Erdos957Cases24.point_apply_one]
      ring
    nlinarith [dist_nonneg (x := reflect p) (y := reflect q),
      dist_nonneg (x := p) (y := q)]
  have hdistReflect : dist (reflect p) (reflect q) = 1 := by
    rw [hdistEq, hdist]
  have hpos := residual_unit_from_right_shallow_forces_pos
    (q := reflect q) (p := reflect p)
    (by simpa [reflect, Erdos957Cases24.point_apply_one] using hqLower)
    (by simpa [reflect, Erdos957Cases24.point_apply_zero] using hpx)
    (by simpa [reflect, Erdos957Cases24.point_apply_zero,
      Erdos957Cases24.point_apply_one] using hpy)
    hdistReflect
  simpa [reflect, Erdos957Cases24.point_apply_zero] using hpos

/-- A unit direct hit in either remaining near slot determines the selected
Case-4 recipient's endpoint-sensitive association in the normalized frame. -/
lemma current_secondary_association_of_adj_near_source
    {C : P.AlignedChartData} {rows : HasRealizedSourceRows P W C}
    {u : Vertex A} {hu : u ∈ sourceVertices P W}
    (hA : IsOneSeparated A) (F : P.FlatAlignedFrameData)
    (Q : CommonPairedCase4Rows rows u hu)
    (hi : P.IsFlat (sourceIndex P W u hu))
    {t : {p // p ∈ P.H}}
    (hadj : (unitDistanceGraph A).Adj t.1
      Q.currentSecondaryTarget.vertex)
    (hnear : t = incidentContinuationHullVertex P
        (sourceIndex P W u hu) Q.twoExtreme.side 1 ∨
      t = Erdos957Case4NoThree.awayHullVertex P
        (sourceIndex P W u hu) Q.twoExtreme.side 0) :
    (t = incidentContinuationHullVertex P
          (sourceIndex P W u hu) Q.twoExtreme.side 1 ∧
        (rows u hu).roleAssociation .case4SplitRight =
          cyclicSideAssociation Q.twoExtreme.side) ∨
      (t = Erdos957Case4NoThree.awayHullVertex P
          (sourceIndex P W u hu) Q.twoExtreme.side 0 ∧
        (rows u hu).roleAssociation .case4SplitRight =
          oppositeCyclicSideAssociation Q.twoExtreme.side) := by
  let q := Q.normalized.frame.toCanonical Q.currentSecondaryTarget.vertex
  have hqMem := CommonPairedCase4Rows.normalized_currentSecondary_mem_residual Q
  have huPrev : Erdos957Cases24.Case2.uPrev ∈
      Q.normalized.frame.image A := by
    apply Q.normalized.frame.mem_image_iff.mpr
    rw [Q.normalized.side_actual]
    exact (cyclicSideVertex P (sourceIndex P W u hu)
      Q.twoExtreme.side).property
  have huCanon : Erdos957Cases24.Case2.u ∈
      Q.normalized.frame.image A := by
    apply Q.normalized.frame.mem_image_iff.mpr
    rw [Q.normalized.source_actual]
    exact (sourceIndex P W u hu).1.property
  have hqLower : q 1 ≤ Erdos957Cases24.Case2.v 1 := by
    have h := residual_centered_snd_nonpos
      (Q.normalized.frame.image_oneSeparated hA) huPrev huCanon hqMem
    change q 1 - Erdos957Cases24.Case4.v 1 ≤ 0 at h
    simpa [Erdos957Cases24.Case4.v] using (sub_nonpos.mp h)
  have hdist : dist (Q.normalized.frame.toCanonical t.1) q = 1 := by
    dsimp [q]
    rw [Q.normalized.frame.dist_eq]
    simpa [unitDistanceGraph] using hadj
  rcases hnear with hincident | haway
  · left
    refine ⟨hincident, ?_⟩
    change t = Erdos957Case4NoThree.incidentHullVertex P
      (sourceIndex P W u hu) Q.twoExtreme.side 1 at hincident
    apply (CommonPairedCase4Rows.current_secondary_association_eq_side_iff Q).mpr
    have hp := Erdos957Case4NoThree.normalizedFrame_incident_prefix_metric_bounds
      F (sourceIndex P W u hu) Q.middle Q.twoExtreme Q.normalized hi 1
    have hneg := residual_unit_from_left_shallow_forces_neg
      (q := q) (p := Q.normalized.frame.toCanonical t.1) hqLower
      (by
        have hx := hp.1
        rw [← hincident] at hx
        norm_num at hx ⊢
        linarith)
      (by
        have hy := hp.2
        rw [← hincident] at hy
        exact hy) hdist
    exact hneg.le
  · right
    refine ⟨haway, ?_⟩
    have hp := Erdos957Case4NoThree.normalizedFrame_away_prefix_bounds
      F (sourceIndex P W u hu) Q.middle Q.twoExtreme Q.normalized hi 0
    have hpos := residual_unit_from_right_shallow_forces_pos
      (q := q) (p := Q.normalized.frame.toCanonical t.1) hqLower
      (by rw [haway]; norm_num at hp ⊢; linarith [hp.2.1])
      (by rw [haway]; exact hp.2.2) hdist
    have hne : (rows u hu).roleAssociation .case4SplitRight ≠
        cyclicSideAssociation Q.twoExtreme.side := by
      intro heq
      have hqNonpos :=
        (CommonPairedCase4Rows.current_secondary_association_eq_side_iff Q).mp heq
      linarith
    cases hs : Q.twoExtreme.side <;>
      cases ha : (rows u hu).roleAssociation .case4SplitRight <;>
      simp [hs, ha, cyclicSideAssociation,
        oppositeCyclicSideAssociation] at hne ⊢

lemma paired_direct_near_two_associations_ne
    (Q : CommonCoherentRealizedSourceRows P W F.chart)
    {s t : Source P W} {v middle : Vertex A}
    (S : RealizedArrivalAt (F := F) Q.rows s v)
    (T : RealizedArrivalAt (F := F) Q.rows t v)
    (hsRole : S.target.role = PairCases.TargetRoleName.case4SplitRight)
    (twoExtreme : TwoExtremeCyclicWitness P
      (sourceIndex P W t.1 t.property) middle)
    (htarget : v = middle)
    (htAssociation : T.descriptor.association =
      cyclicSideAssociation twoExtreme.side)
    (hnear :
      let Qs := Q.case4_pair s.1 s.property
        ⟨S.target.target, by simpa [hsRole] using S.target.target_at_role⟩
      sourceIndex P W t.1 t.property =
          incidentContinuationHullVertex P
            (sourceIndex P W s.1 s.property) Qs.twoExtreme.side 1 ∨
        sourceIndex P W t.1 t.property =
          Erdos957Case4NoThree.awayHullVertex P
            (sourceIndex P W s.1 s.property) Qs.twoExtreme.side 0) :
    S.descriptor.association ≠ T.descriptor.association := by
  let Qs := Q.case4_pair s.1 s.property
    ⟨S.target.target, by simpa [hsRole] using S.target.target_at_role⟩
  change sourceIndex P W t.1 t.property =
        incidentContinuationHullVertex P
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
      _ = Qs.currentSecondaryTarget.vertex :=
        congrArg LocalTarget.vertex hslot
  have htSideAdj : (unitDistanceGraph A).Adj
      (cyclicSideVertex P (sourceIndex P W t.1 t.property)
        twoExtreme.side) v := by
    rw [htarget]
    exact (unitDistanceGraph A).adj_symm twoExtreme.side_adjacent
  have hsDescriptor : S.descriptor.association =
      (Q.rows s.1 s.property).roleAssociation
        PairCases.TargetRoleName.case4SplitRight := by
    calc
      S.descriptor.association =
          (Q.rows s.1 s.property).roleAssociation S.target.role :=
        S.descriptor.association_eq
      _ = _ := by rw [hsRole]
  rcases hnear with hincident | haway
  · cases hs : Qs.twoExtreme.side with
    | previous =>
        cases ht : twoExtreme.side with
        | previous =>
            have hend : cyclicSideVertex P
                (sourceIndex P W t.1 t.property) twoExtreme.side =
                incidentContinuationHullVertex P
                  (sourceIndex P W s.1 s.property) Qs.twoExtreme.side 2 := by
              rw [ht, hincident]
              simp [cyclicSideVertex, incidentContinuationHullVertex, hs,
                pow_succ]
            rw [hend, hv] at htSideAdj
            exact (Erdos957Case4CollisionLeaves.CommonPairedCase4Rows.not_direct_incident_third F Qs
              (Erdos957GeometryLocalityBridge.sourceIndex_isFlat W s)
              htSideAdj).elim
        | next =>
            have hend : cyclicSideVertex P
                (sourceIndex P W t.1 t.property) twoExtreme.side =
                cyclicSideVertex P (sourceIndex P W s.1 s.property)
                  Qs.twoExtreme.side := by
              rw [ht, hincident]
              simp [cyclicSideVertex, incidentContinuationHullVertex, hs,
                pow_succ]
            have hadjPartner : (unitDistanceGraph A).Adj
                (cyclicSideVertex P (sourceIndex P W s.1 s.property)
                  Qs.twoExtreme.side) Qs.currentSecondaryTarget.vertex := by
              rw [← hend, ← hv]
              exact htSideAdj
            have hsAssociation : S.descriptor.association =
                cyclicSideAssociation Qs.twoExtreme.side := by
              rw [hsDescriptor]
              exact Erdos957Case4CommonAssociations.CommonPairedCase4Rows.secondary_association_eq_side_of_adj_partner
                Qs hadjPartner
            rw [hsAssociation, htAssociation, hs, ht]
            decide
    | next =>
        cases ht : twoExtreme.side with
        | previous =>
            have hend : cyclicSideVertex P
                (sourceIndex P W t.1 t.property) twoExtreme.side =
                cyclicSideVertex P (sourceIndex P W s.1 s.property)
                  Qs.twoExtreme.side := by
              rw [ht, hincident]
              simp [cyclicSideVertex, incidentContinuationHullVertex, hs,
                pow_succ]
            have hadjPartner : (unitDistanceGraph A).Adj
                (cyclicSideVertex P (sourceIndex P W s.1 s.property)
                  Qs.twoExtreme.side) Qs.currentSecondaryTarget.vertex := by
              rw [← hend, ← hv]
              exact htSideAdj
            have hsAssociation : S.descriptor.association =
                cyclicSideAssociation Qs.twoExtreme.side := by
              rw [hsDescriptor]
              exact Erdos957Case4CommonAssociations.CommonPairedCase4Rows.secondary_association_eq_side_of_adj_partner
                Qs hadjPartner
            rw [hsAssociation, htAssociation, hs, ht]
            decide
        | next =>
            have hend : cyclicSideVertex P
                (sourceIndex P W t.1 t.property) twoExtreme.side =
                incidentContinuationHullVertex P
                  (sourceIndex P W s.1 s.property) Qs.twoExtreme.side 2 := by
              rw [ht, hincident]
              simp [cyclicSideVertex, incidentContinuationHullVertex, hs,
                pow_succ]
            rw [hend, hv] at htSideAdj
            exact (Erdos957Case4CollisionLeaves.CommonPairedCase4Rows.not_direct_incident_third F Qs
              (Erdos957GeometryLocalityBridge.sourceIndex_isFlat W s)
              htSideAdj).elim
  · cases hs : Qs.twoExtreme.side with
    | previous =>
        cases ht : twoExtreme.side with
        | previous =>
            have hend : cyclicSideVertex P
                (sourceIndex P W t.1 t.property) twoExtreme.side =
                sourceIndex P W s.1 s.property := by
              rw [ht, haway]
              simp [cyclicSideVertex, Erdos957Case4NoThree.awayHullVertex, hs,
                pow_succ]
            have hadjSource : (unitDistanceGraph A).Adj s.1
                Qs.currentSecondaryTarget.vertex := by
              rw [hend, hv] at htSideAdj
              simpa [sourceIndex] using htSideAdj
            have hsAssociation : S.descriptor.association =
                oppositeCyclicSideAssociation Qs.twoExtreme.side := by
              rw [hsDescriptor]
              exact Erdos957Case4CommonAssociations.CommonPairedCase4Rows.secondary_association_eq_opposite_of_adj_source
                Qs hadjSource
            rw [hsAssociation, htAssociation, hs, ht]
            decide
        | next =>
            have hend : cyclicSideVertex P
                (sourceIndex P W t.1 t.property) twoExtreme.side =
                Erdos957Case4NoThree.awayHullVertex P
                  (sourceIndex P W s.1 s.property) Qs.twoExtreme.side 1 := by
              rw [ht, haway]
              simp [cyclicSideVertex, Erdos957Case4NoThree.awayHullVertex, hs,
                pow_succ]
            rw [hend, hv] at htSideAdj
            exact (Erdos957Case4CollisionLeaves.CommonPairedCase4Rows.not_direct_away_second F Qs
              (Erdos957GeometryLocalityBridge.sourceIndex_isFlat W s)
              htSideAdj).elim
    | next =>
        cases ht : twoExtreme.side with
        | previous =>
            have hend : cyclicSideVertex P
                (sourceIndex P W t.1 t.property) twoExtreme.side =
                Erdos957Case4NoThree.awayHullVertex P
                  (sourceIndex P W s.1 s.property) Qs.twoExtreme.side 1 := by
              rw [ht, haway]
              simp [cyclicSideVertex, Erdos957Case4NoThree.awayHullVertex, hs,
                pow_succ]
            rw [hend, hv] at htSideAdj
            exact (Erdos957Case4CollisionLeaves.CommonPairedCase4Rows.not_direct_away_second F Qs
              (Erdos957GeometryLocalityBridge.sourceIndex_isFlat W s)
              htSideAdj).elim
        | next =>
            have hend : cyclicSideVertex P
                (sourceIndex P W t.1 t.property) twoExtreme.side =
                sourceIndex P W s.1 s.property := by
              rw [ht, haway]
              simp [cyclicSideVertex, Erdos957Case4NoThree.awayHullVertex, hs,
                pow_succ]
            have hadjSource : (unitDistanceGraph A).Adj s.1
                Qs.currentSecondaryTarget.vertex := by
              rw [hend, hv] at htSideAdj
              simpa [sourceIndex] using htSideAdj
            have hsAssociation : S.descriptor.association =
                oppositeCyclicSideAssociation Qs.twoExtreme.side := by
              rw [hsDescriptor]
              exact Erdos957Case4CommonAssociations.CommonPairedCase4Rows.secondary_association_eq_opposite_of_adj_source
                Qs hadjSource
            rw [hsAssociation, htAssociation, hs, ht]
            decide

end Erdos957Case4DirectSameSide

#print axioms Erdos957Case4DirectSameSide.paired_direct_near_two_associations_ne
