import ErdosProblems.Erdos957.CoherentRealizedRows
import ErdosProblems.Erdos957.RoleCollisions
import ErdosProblems.Erdos957.ExceptionalWindowDispatch
import ErdosProblems.Erdos957.Case3SameSide

/-!
# Same-side uniqueness for direct Erdős 957 recipients

This file proves the direct/direct leaf of the role-anchored collision
interface.  It uses only the formula data retained by the produced rows.
In particular, the two-step exclusion below is a metric consequence of the
two almost-horizontal hull edges and one-separation at their intermediate
vertex; it is not a collision or capacity assumption.
-/

open scoped RealInnerProductSpace

noncomputable section

namespace Erdos957DirectSameSide

open Erdos957GeometryCore
open Erdos957GeometryLocalRows
open Erdos957CollisionInstantiation
open Erdos957CaseClassification
open Erdos957CaseClassification.PairCases
open Erdos957RoleCollisions

abbrev Point := Erdos957GeometryCore.Point
abbrev PairPoint := Erdos957Cases13.Point

/-! ## The two-edge metric exclusion -/

private lemma abs_sin_le_cos_div_ten_of_abs_le_pi_div_forty_five
    {theta : ℝ} (h : |theta| ≤ Real.pi / 45) :
    |Real.sin theta| ≤ Real.cos theta / 10 := by
  have hlo :=
    Erdos957Locality.neg_sin_le_cos_div_ten_of_abs_le_pi_div_forty_five h
  have hn : |-theta| ≤ Real.pi / 45 := by simpa using h
  have hhi :=
    Erdos957Locality.neg_sin_le_cos_div_ten_of_abs_le_pi_div_forty_five hn
  rw [Real.sin_neg, Real.cos_neg, neg_neg] at hhi
  rw [abs_le]
  constructor
  · linarith
  · exact hhi

private lemma midpoint_height_sq_lt_one_hundredth
    {x y w : ℝ} (hw : w = 1 - (x ^ 2 + y ^ 2) / 4)
    (hx : (399 / 200 : ℝ) < x) : w < 1 / 100 := by
  have hxpos : 0 < x := by linarith
  have hsq : (399 / 200 : ℝ) ^ 2 < x ^ 2 :=
    (sq_lt_sq₀ (by norm_num) hxpos.le).2 hx
  rw [hw]
  norm_num at hsq ⊢
  nlinarith [sq_nonneg y]

/-- A point cannot be unit from both ends of two consecutive flat hull
edges while remaining one-separated from their intermediate vertex. -/
lemma no_common_unit_target_of_two_flat_polar_edges
    {p0 p1 p2 v : PairPoint} {r0 r1 theta0 theta1 : ℝ}
    (hp0 : p0 = Erdos957Cases13.origin)
    (he0 : Erdos957Locality.IsPolarEdge p0 p1 r0 theta0)
    (he1 : Erdos957Locality.IsPolarEdge p1 p2 r1 theta1)
    (hr0 : 1 ≤ r0) (hr1 : 1 ≤ r1)
    (ha0 : |theta0| ≤ Real.pi / 45)
    (ha1 : |theta1| ≤ Real.pi / 45)
    (hv0 : Erdos957Cases13.sqDist v p0 = 1)
    (hv2 : Erdos957Cases13.sqDist v p2 = 1)
    (hv1 : 1 ≤ Erdos957Cases13.sqDist v p1) : False := by
  subst p0
  rcases he0 with ⟨hx0, hy0⟩
  rcases he1 with ⟨hx1, hy1⟩
  have hdx0 : (399 / 400 : ℝ) < p1.1 := by
    have h := Erdos957Locality.horizontal_increment_gt_three_nine_nine_div_four_hundred
      hr0 ha0 hx0
    simpa [Erdos957Cases13.origin] using h
  have hdx1 : (399 / 400 : ℝ) < p2.1 - p1.1 :=
    Erdos957Locality.horizontal_increment_gt_three_nine_nine_div_four_hundred
      hr1 ha1 hx1
  have hslope0 := abs_sin_le_cos_div_ten_of_abs_le_pi_div_forty_five ha0
  have hslope1 := abs_sin_le_cos_div_ten_of_abs_le_pi_div_forty_five ha1
  have hr0nonneg : 0 ≤ r0 := by linarith
  have hr1nonneg : 0 ≤ r1 := by linarith
  have hy0abs : |p1.2| ≤ p1.1 / 10 := by
    have hm := mul_le_mul_of_nonneg_left hslope0 hr0nonneg
    calc
      |p1.2| = r0 * |Real.sin theta0| := by
        rw [show p1.2 = r0 * Real.sin theta0 by
          simpa [Erdos957Cases13.origin] using hy0]
        simp [abs_mul, abs_of_nonneg hr0nonneg]
      _ ≤ r0 * (Real.cos theta0 / 10) := hm
      _ = p1.1 / 10 := by
        rw [show p1.1 = r0 * Real.cos theta0 by
          simpa [Erdos957Cases13.origin] using hx0]
        ring
  have hy1abs : |p2.2 - p1.2| ≤ (p2.1 - p1.1) / 10 := by
    have hm := mul_le_mul_of_nonneg_left hslope1 hr1nonneg
    calc
      |p2.2 - p1.2| = r1 * |Real.sin theta1| := by
        rw [hy1]
        simp [abs_mul, abs_of_nonneg hr1nonneg]
      _ ≤ r1 * (Real.cos theta1 / 10) := hm
      _ = (p2.1 - p1.1) / 10 := by rw [hx1]; ring
  have hv0' : (v.1 : ℝ) ^ 2 + v.2 ^ 2 = 1 := by
    simpa [Erdos957Cases13.sqDist, Erdos957Cases13.origin] using hv0
  have hv2' : (v.1 - p2.1) ^ 2 + (v.2 - p2.2) ^ 2 = 1 := by
    simpa [Erdos957Cases13.sqDist] using hv2
  have hdot : v.1 * p2.1 + v.2 * p2.2 =
      (p2.1 ^ 2 + p2.2 ^ 2) / 2 := by
    nlinarith [hv0', hv2']
  have hp2norm : p2.1 ^ 2 + p2.2 ^ 2 ≤ 4 := by
    have hcs : (v.1 * p2.1 + v.2 * p2.2) ^ 2 ≤
        (v.1 ^ 2 + v.2 ^ 2) * (p2.1 ^ 2 + p2.2 ^ 2) := by
      nlinarith [sq_nonneg (v.1 * p2.2 - v.2 * p2.1)]
    nlinarith [sq_nonneg p2.1, sq_nonneg p2.2]
  have hp2xUpper : p2.1 ≤ 2 := by
    have hp2xPos : 0 < p2.1 := by linarith
    nlinarith [sq_nonneg p2.2]
  have hp1xUpper : p1.1 < (401 / 400 : ℝ) := by linarith
  have hdx1Upper : p2.1 - p1.1 < (401 / 400 : ℝ) := by linarith
  have hmxLower : -(1 / 100 : ℝ) < p1.1 - p2.1 / 2 := by linarith
  have hmxUpper : p1.1 - p2.1 / 2 < (1 / 100 : ℝ) := by linarith
  have hy0bounds := (abs_le.mp hy0abs)
  have hy1bounds := (abs_le.mp hy1abs)
  have hmyLower : -(1 / 5 : ℝ) < p1.2 - p2.2 / 2 := by linarith
  have hmyUpper : p1.2 - p2.2 / 2 < (1 / 5 : ℝ) := by linarith
  let wx := v.1 - p2.1 / 2
  let wy := v.2 - p2.2 / 2
  let mx := p1.1 - p2.1 / 2
  let my := p1.2 - p2.2 / 2
  have hwNorm : wx ^ 2 + wy ^ 2 =
      1 - (p2.1 ^ 2 + p2.2 ^ 2) / 4 := by
    calc
      wx ^ 2 + wy ^ 2 =
          (v.1 ^ 2 + v.2 ^ 2) -
            (v.1 * p2.1 + v.2 * p2.2) +
              (p2.1 ^ 2 + p2.2 ^ 2) / 4 := by
        dsimp [wx, wy]
        ring
      _ = 1 - (p2.1 ^ 2 + p2.2 ^ 2) / 4 := by
        rw [hv0', hdot]
        ring
  have hp2xLower : (399 / 200 : ℝ) < p2.1 := by linarith
  have hwSmall : wx ^ 2 + wy ^ 2 < (1 / 100 : ℝ) := by
    exact midpoint_height_sq_lt_one_hundredth hwNorm hp2xLower
  have hmxSq : mx ^ 2 < (1 / 100 : ℝ) ^ 2 := by
    have hprod : 0 < ((1 / 100 : ℝ) - mx) * ((1 / 100 : ℝ) + mx) := by
      apply mul_pos
      · dsimp [mx]; linarith only [hmxUpper]
      · dsimp [mx]; linarith only [hmxLower]
    nlinarith only [hprod]
  have hmySq : my ^ 2 < (1 / 5 : ℝ) ^ 2 := by
    have hprod : 0 < ((1 / 5 : ℝ) - my) * ((1 / 5 : ℝ) + my) := by
      apply mul_pos
      · dsimp [my]; linarith only [hmyUpper]
      · dsimp [my]; linarith only [hmyLower]
    nlinarith only [hprod]
  have htargetExpand : Erdos957Cases13.sqDist v p1 =
      (wx - mx) ^ 2 + (wy - my) ^ 2 := by
    simp only [Erdos957Cases13.sqDist]
    dsimp [wx, wy, mx, my]
    ring
  have hyoungX : -2 * wx * mx ≤ wx ^ 2 + mx ^ 2 := by
    nlinarith only [sq_nonneg (wx + mx)]
  have hyoungY : -2 * wy * my ≤ wy ^ 2 + my ^ 2 := by
    nlinarith only [sq_nonneg (wy + my)]
  rw [htargetExpand] at hv1
  norm_num at hv1 hmxSq hmySq hwSmall
  nlinarith only [hv1, hmxSq, hmySq, hwSmall, hyoungX, hyoungY]

private lemma sqDist_coord_of_adj
    {A : Finset Point} {P : CyclicHullData A}
    (C : P.AlignedChartData) (i : {p // p ∈ P.H})
    (a b : Vertex A) (h : (unitDistanceGraph A).Adj a b) :
    Erdos957Cases13.sqDist (C.coord i a) (C.coord i b) = 1 := by
  rw [C.sqDist_coord]
  have hd : dist (a : Point) (b : Point) = 1 := by
    simpa [unitDistanceGraph] using h
  rw [hd]
  norm_num

private lemma sqDist_reflect (p q : PairPoint) :
    Erdos957Cases13.sqDist (-p.1, p.2) (-q.1, q.2) =
      Erdos957Cases13.sqDist p q := by
  simp [Erdos957Cases13.sqDist]
  ring

/-- A direct non-hull target cannot be unit-adjacent to a flat source and
its second successor. -/
lemma no_common_unit_target_second_successor
    {A : Finset Point} (hA : IsOneSeparated A)
    {P : CyclicHullData A} (F : P.FlatAlignedFrameData)
    (i : {p // p ∈ P.H}) (hi : P.IsFlat i)
    (t : {p // p ∈ P.H}) (v : Vertex A) (hvNotHull : v ∉ P.H)
    (hiv : (unitDistanceGraph A).Adj i.1 v)
    (htv : (unitDistanceGraph A).Adj t.1 v)
    (hit : t = (P.next ^ 2) i) : False := by
  let p0 := F.chart.rightOrbitCoord P i 0
  let p1 := F.chart.rightOrbitCoord P i 1
  let p2 := F.chart.rightOrbitCoord P i 2
  let q := F.chart.coord i v
  obtain ⟨h0, h1, h2, h3⟩ := F.rightFlatAngles i hi
  obtain ⟨ha0, ha1, _ha2, _ha3⟩ :=
    Erdos957Locality.four_edge_angles_near_horizontal h0 h1 h2 h3
  apply no_common_unit_target_of_two_flat_polar_edges
      (p0 := p0) (p1 := p1) (p2 := p2) (v := q)
      (r0 := F.rightRadius i 0) (r1 := F.rightRadius i 1)
      (theta0 := F.rightAngle i 0) (theta1 := F.rightAngle i 1)
  · exact F.chart.rightOrbitCoord_zero P i
  · exact F.rightPolar i 0
  · exact F.rightPolar i 1
  · exact F.rightRadius_ge_one i 0
  · exact F.rightRadius_ge_one i 1
  · exact ha0
  · exact ha1
  · change Erdos957Cases13.sqDist (F.chart.coord i v)
      (F.chart.coord i i.1) = 1
    exact sqDist_coord_of_adj F.chart i v i.1
      ((unitDistanceGraph A).adj_symm hiv)
  · change Erdos957Cases13.sqDist (F.chart.coord i v)
      (F.chart.coord i ((P.next ^ 2) i).1) = 1
    rw [← hit]
    exact sqDist_coord_of_adj F.chart i v t.1
      ((unitDistanceGraph A).adj_symm htv)
  · have hvNe : v ≠ (P.next i).1 := by
      intro h
      apply hvNotHull
      simpa [h] using (P.next i).property
    have hsep : 1 ≤ dist (v : Point) ((P.next i).1 : Point) :=
      hA v v.property (P.next i).1 (P.next i).1.property
        (fun h ↦ hvNe (Subtype.ext h))
    change 1 ≤ Erdos957Cases13.sqDist (F.chart.coord i v)
      (F.chart.coord i (P.next i).1)
    rw [F.chart.sqDist_coord]
    nlinarith [dist_nonneg (x := (v : Point))
      (y := ((P.next i).1 : Point))]

/-- Reflected predecessor counterpart of
`no_common_unit_target_second_successor`. -/
lemma no_common_unit_target_second_predecessor
    {A : Finset Point} (hA : IsOneSeparated A)
    {P : CyclicHullData A} (F : P.FlatAlignedFrameData)
    (i : {p // p ∈ P.H}) (hi : P.IsFlat i)
    (t : {p // p ∈ P.H}) (v : Vertex A) (hvNotHull : v ∉ P.H)
    (hiv : (unitDistanceGraph A).Adj i.1 v)
    (htv : (unitDistanceGraph A).Adj t.1 v)
    (hit : t = ((P.next⁻¹) ^ 2) i) : False := by
  let reflect : PairPoint → PairPoint := fun z ↦ (-z.1, z.2)
  let p0 := F.chart.leftOrbitReflectedCoord P i 0
  let p1 := F.chart.leftOrbitReflectedCoord P i 1
  let p2 := F.chart.leftOrbitReflectedCoord P i 2
  let q := reflect (F.chart.coord i v)
  obtain ⟨h0, h1, h2, h3⟩ := F.leftFlatAngles i hi
  obtain ⟨ha0, ha1, _ha2, _ha3⟩ :=
    Erdos957Locality.four_edge_angles_near_horizontal h0 h1 h2 h3
  apply no_common_unit_target_of_two_flat_polar_edges
      (p0 := p0) (p1 := p1) (p2 := p2) (v := q)
      (r0 := F.leftRadius i 0) (r1 := F.leftRadius i 1)
      (theta0 := F.leftAngle i 0) (theta1 := F.leftAngle i 1)
  · exact F.chart.leftOrbitReflectedCoord_zero P i
  · exact F.leftPolar i 0
  · exact F.leftPolar i 1
  · exact F.leftRadius_ge_one i 0
  · exact F.leftRadius_ge_one i 1
  · exact ha0
  · exact ha1
  · change Erdos957Cases13.sqDist
      (-(F.chart.coord i v).1, (F.chart.coord i v).2)
      (-(F.chart.coord i i.1).1, (F.chart.coord i i.1).2) = 1
    rw [sqDist_reflect]
    exact sqDist_coord_of_adj F.chart i v i.1
      ((unitDistanceGraph A).adj_symm hiv)
  · change Erdos957Cases13.sqDist
      (-(F.chart.coord i v).1, (F.chart.coord i v).2)
      (-(F.chart.coord i (((P.next⁻¹) ^ 2) i).1).1,
        (F.chart.coord i (((P.next⁻¹) ^ 2) i).1).2) = 1
    rw [sqDist_reflect, ← hit]
    exact sqDist_coord_of_adj F.chart i v t.1
      ((unitDistanceGraph A).adj_symm htv)
  · have hvNe : v ≠ (P.next⁻¹ i).1 := by
      intro h
      apply hvNotHull
      simpa [h] using (P.next⁻¹ i).property
    have hsep : 1 ≤ dist (v : Point) ((P.next⁻¹ i).1 : Point) :=
      hA v v.property (P.next⁻¹ i).1 (P.next⁻¹ i).1.property
        (fun h ↦ hvNe (Subtype.ext h))
    change 1 ≤ Erdos957Cases13.sqDist
      (-(F.chart.coord i v).1, (F.chart.coord i v).2)
      (-(F.chart.coord i (P.next⁻¹ i).1).1,
        (F.chart.coord i (P.next⁻¹ i).1).2)
    rw [sqDist_reflect]
    rw [F.chart.sqDist_coord]
    nlinarith [dist_nonneg (x := (v : Point))
      (y := ((P.next⁻¹ i).1 : Point))]

/-! ## Formula classification for direct arrivals -/

private lemma adj_of_sqDist_coord_eq_one
    {A : Finset Point} {P : CyclicHullData A}
    (C : P.AlignedChartData) (i : {p // p ∈ P.H})
    (a b : Vertex A)
    (h : Erdos957Cases13.sqDist (C.coord i a) (C.coord i b) = 1) :
    (unitDistanceGraph A).Adj a b := by
  change dist (a : Point) (b : Point) = 1
  have hs : dist (a : Point) (b : Point) ^ 2 = 1 := by
    rw [← C.sqDist_coord]
    exact h
  nlinarith [dist_nonneg (x := (a : Point)) (y := (b : Point))]

private lemma adj_of_rigid_coordinate_dist
    {A : Finset Point} (F : Erdos957Case24Bridge.Framed.RigidChart)
    (a b : Vertex A) (p q : Point)
    (ha : F.toCanonical a = p) (hb : F.toCanonical b = q)
    (hpq : dist p q = 1) : (unitDistanceGraph A).Adj a b := by
  change dist (a : Point) (b : Point) = 1
  rw [← F.dist_eq, ha, hb, hpq]

/-- The common non-hull equilateral proxy retained by every direct role
except a singleton Case-3 middle and a two-extreme Case-4 middle. -/
structure OuterDirectFormula
    {A : Finset Point} {P : CyclicHullData A}
    (C : P.AlignedChartData) (source : {p // p ∈ P.H})
    (target : Vertex A) (association : ArrivalAssociation) where
  proxy : Vertex A
  source_proxy : (unitDistanceGraph A).Adj source.1 proxy
  target_proxy : (unitDistanceGraph A).Adj target proxy
  proxy_not_hull : proxy ∉ P.H
  association_side :
    (Erdos957Case3General.crossFrom
        (C.coord source source.1) (C.coord source proxy)
        (C.coord source target) ≤ 0 ∧ association = .fromPrevious) ∨
      (0 < Erdos957Case3General.crossFrom
        (C.coord source source.1) (C.coord source proxy)
        (C.coord source target) ∧ association = .fromNext)

/-- Exhaustive genuine geometry behind a direct realized arrival. -/
inductive DirectArrivalFormula
    {A : Finset Point} {P : CyclicHullData A}
    (C : P.AlignedChartData) (source : {p // p ∈ P.H})
    (target : Vertex A) (association : ArrivalAssociation) : Type
  | singleton
      (one_hull_neighbor : (hullUnitNeighbors P target).card = 1)
      (middleCoord : PairPoint)
      (target_coordinate : C.coord source target = middleCoord)
      (association_eq : association = horizontalAssociation middleCoord.1)
  | outer (data : OuterDirectFormula C source target association)
  | paired (middle : Vertex A)
      (twoExtreme : TwoExtremeCyclicWitness P source middle)
      (target_eq : target = middle)
      (association_eq : association = cyclicSideAssociation twoExtreme.side)

private lemma case1Left_cross_negative (m : PairPoint)
    (hunit : Erdos957Cases13.sqDist Erdos957Cases13.origin m = 1) :
    Erdos957Case3General.crossFrom Erdos957Cases13.origin m
        (Erdos957Cases13.case1Left m) < 0 := by
  have hs := Erdos957Cases13.sqrtThree_pos
  have hsq : m.1 ^ 2 + m.2 ^ 2 = 1 := by
    simpa [Erdos957Cases13.sqDist, Erdos957Cases13.origin] using hunit
  simp only [Erdos957Case3General.crossFrom, Erdos957Cases13.origin,
    Erdos957Cases13.case1Left]
  nlinarith

private lemma case1Right_cross_positive (m : PairPoint)
    (hunit : Erdos957Cases13.sqDist Erdos957Cases13.origin m = 1) :
    0 < Erdos957Case3General.crossFrom Erdos957Cases13.origin m
        (Erdos957Cases13.case1Right m) := by
  have hs := Erdos957Cases13.sqrtThree_pos
  have hsq : m.1 ^ 2 + m.2 ^ 2 = 1 := by
    simpa [Erdos957Cases13.sqDist, Erdos957Cases13.origin] using hunit
  simp only [Erdos957Case3General.crossFrom, Erdos957Cases13.origin,
    Erdos957Cases13.case1Right]
  nlinarith

private def pairOfPoint (z : Point) : PairPoint := (z 0, z 1)

lemma crossFrom_terminalUnitEdgeRigidChart
    (p o a b c : Point) (hunit : dist p o = 1) :
    Erdos957Case3General.crossFrom
        (pairOfPoint ((Erdos957EdgeFrame.terminalUnitEdgeRigidChart
          p o hunit).toCanonical a))
        (pairOfPoint ((Erdos957EdgeFrame.terminalUnitEdgeRigidChart
          p o hunit).toCanonical b))
        (pairOfPoint ((Erdos957EdgeFrame.terminalUnitEdgeRigidChart
          p o hunit).toCanonical c)) =
      -Erdos957GeometryCore.cross (b - a) (c - a) := by
  have he := Erdos957EdgeFrame.coordinate_sq_sum_eq_one_of_dist_eq_one hunit
  have h := Erdos957EdgeFrame.pairCross_edgePairCoord_displacements_of_sq
    (o := o) (e := o - p) he a b c
  simpa only [Erdos957EdgeFrame.terminalUnitEdgeRigidChart_toCanonical,
    pairOfPoint,
    Erdos957Case3General.crossFrom,
    Erdos957GeometryCore.CyclicHullData.pairCross,
    Erdos957GeometryCore.CyclicHullData.pairSub,
    Erdos957EdgeFrame.edgePointCoord_apply_zero,
    Erdos957EdgeFrame.edgePointCoord_apply_one] using h

lemma crossFrom_reflectedSuccessorUnitEdgeRigidChart
    {A : Finset Point} (P : CyclicHullData A)
    (source : {p // p ∈ P.H})
    (hunit : dist (source.1.1 : Point) (P.next source).1.1 = 1)
    (a b c : Point) :
    Erdos957Case3General.crossFrom
        (pairOfPoint ((Erdos957TwoExtremeAligned.reflectedSuccessorUnitEdgeRigidChart
          P source hunit).toCanonical a))
        (pairOfPoint ((Erdos957TwoExtremeAligned.reflectedSuccessorUnitEdgeRigidChart
          P source hunit).toCanonical b))
        (pairOfPoint ((Erdos957TwoExtremeAligned.reflectedSuccessorUnitEdgeRigidChart
          P source hunit).toCanonical c)) =
      Erdos957GeometryCore.cross (b - a) (c - a) := by
  have h := Erdos957EdgeFrame.pairCross_edgePairCoord_displacements
    hunit a b c
  rw [Erdos957TwoExtremeAligned.reflectedSuccessorUnitEdgeRigidChart_toCanonical,
    Erdos957TwoExtremeAligned.reflectedSuccessorUnitEdgeRigidChart_toCanonical,
    Erdos957TwoExtremeAligned.reflectedSuccessorUnitEdgeRigidChart_toCanonical]
  simp only [Erdos957Case3General.crossFrom,
    pairOfPoint,
    Erdos957Cases24.point_apply_zero, Erdos957Cases24.point_apply_one,
    Erdos957EdgeFrame.edgePointCoord_apply_zero,
    Erdos957EdgeFrame.edgePointCoord_apply_one] at h ⊢
  simp only [Erdos957GeometryCore.CyclicHullData.pairCross,
    Erdos957GeometryCore.CyclicHullData.pairSub] at h
  linarith

private lemma case2Outer_association_side
    {A : Finset Point} {P : CyclicHullData A}
    (C : P.AlignedChartData) (source : {p // p ∈ P.H})
    (middle target : Vertex A) (T : TwoExtremeCyclicWitness P source middle)
    (N : ActualCase24Rows.TwoExtremeNormalizedFrame source middle T)
    (htarget : N.frame.toCanonical target = Erdos957Cases24.Case2.b) :
    (Erdos957Case3General.crossFrom
        (C.coord source source.1) (C.coord source middle)
        (C.coord source target) ≤ 0 ∧
          oppositeCyclicSideAssociation T.side = .fromPrevious) ∨
      (0 < Erdos957Case3General.crossFrom
        (C.coord source source.1) (C.coord source middle)
        (C.coord source target) ∧
          oppositeCyclicSideAssociation T.side = .fromNext) := by
  have hsource : N.frame.toCanonical source.1 = Erdos957Cases24.Case2.u := by
    rw [← N.source_actual, N.frame.toCanonical_actual]
  have hmiddle : N.frame.toCanonical middle = Erdos957Cases24.Case2.v := by
    rw [← N.middle_actual, N.frame.toCanonical_actual]
  have hcanonical : 0 < Erdos957Case3General.crossFrom
      (pairOfPoint (N.frame.toCanonical source.1))
      (pairOfPoint (N.frame.toCanonical middle))
      (pairOfPoint (N.frame.toCanonical target)) := by
    rw [hsource, hmiddle, htarget]
    simp only [pairOfPoint, Erdos957Case3General.crossFrom,
      Erdos957Cases24.Case2.u, Erdos957Cases24.Case2.v,
      Erdos957Cases24.Case2.b, Erdos957Cases24.point_apply_zero,
      Erdos957Cases24.point_apply_one]
    nlinarith [Erdos957Cases24.sqrtThree_pos]
  have haligned := Erdos957Case3SameSide.crossFrom_coord_eq_neg_cross
    C source source.1 middle target
  cases N.frame_spec with
  | previous hside hunit hframe =>
      right
      constructor
      · have hrigid := crossFrom_terminalUnitEdgeRigidChart
          (P.next⁻¹ source).1.1 source.1.1 source.1.1 middle target hunit
        rw [← hframe] at hrigid
        rw [haligned]
        linarith [hcanonical, hrigid]
      · simp [oppositeCyclicSideAssociation, hside]
  | next hside hunit hframe =>
      left
      constructor
      · have hrigid := crossFrom_reflectedSuccessorUnitEdgeRigidChart
          P source hunit source.1.1 middle target
        rw [← hframe] at hrigid
        rw [haligned]
        linarith [hcanonical, hrigid]
      · simp [oppositeCyclicSideAssociation, hside]

/-- Every direct target selected from an enriched row has exactly one of
the three geometric forms used in the adjacent-source argument. -/
def directArrivalFormula
    {A : Finset Point} {P : CyclicHullData A}
    {C : P.AlignedChartData} {source : {p // p ∈ P.H}}
    {R : RealizedSourceRow P C source} {v : Vertex A}
    (D : RealizedPositiveTarget R v)
    (Arr : RealizedArrivalDescriptor R D.role D.target)
    (hdirect : IsDirectTargetRole D.role) :
    DirectArrivalFormula C source v Arr.association := by
  rcases D with ⟨role, target, hrole, hv⟩
  subst v
  cases R with
  | case1 middle hdegree hone middleCoord hmiddleCoord hmiddleNotHull hunit row =>
      cases role <;>
        simp [IsDirectTargetRole, RealizedSourceRow.targetAtRole] at hdirect hrole
      · subst target
        have hassoc : Arr.association = .fromPrevious := by
          simpa [RealizedSourceRow.ArrivalCertificate] using Arr.certificate.1
        refine .outer ⟨middle, ?_, ?_, hmiddleNotHull, Or.inl ⟨?_, hassoc⟩⟩
        · apply adj_of_sqDist_coord_eq_one C source source.1 middle
          rw [C.coord_source, hmiddleCoord]
          exact hunit
        · apply (unitDistanceGraph A).adj_symm
          apply adj_of_sqDist_coord_eq_one C source middle row.left.vertex
          rw [hmiddleCoord]
          rw [show C.coord source row.left.vertex =
            Erdos957Cases13.case1Left middleCoord by
              simpa [Erdos957GeometryLocalRows.sourceCoordinates] using
                row.left_coordinate]
          exact (Erdos957Cases13.case1Left_common_unit hunit).2
        · rw [C.coord_source, hmiddleCoord]
          rw [show C.coord source row.left.vertex =
            Erdos957Cases13.case1Left middleCoord by
              simpa [Erdos957GeometryLocalRows.sourceCoordinates] using
                row.left_coordinate]
          exact (case1Left_cross_negative middleCoord hunit).le
      · subst target
        have hassoc : Arr.association = .fromNext := by
          simpa [RealizedSourceRow.ArrivalCertificate] using Arr.certificate.1
        refine .outer ⟨middle, ?_, ?_, hmiddleNotHull, Or.inr ⟨?_, hassoc⟩⟩
        · apply adj_of_sqDist_coord_eq_one C source source.1 middle
          rw [C.coord_source, hmiddleCoord]
          exact hunit
        · apply (unitDistanceGraph A).adj_symm
          apply adj_of_sqDist_coord_eq_one C source middle row.right.vertex
          rw [hmiddleCoord]
          rw [show C.coord source row.right.vertex =
            Erdos957Cases13.case1Right middleCoord by
              simpa [Erdos957GeometryLocalRows.sourceCoordinates] using
                row.right_coordinate]
          exact (Erdos957Cases13.case1Right_common_unit hunit).2
        · rw [C.coord_source, hmiddleCoord]
          rw [show C.coord source row.right.vertex =
            Erdos957Cases13.case1Right middleCoord by
              simpa [Erdos957GeometryLocalRows.sourceCoordinates] using
                row.right_coordinate]
          exact case1Right_cross_positive middleCoord hunit
  | case2 middle hdegree htwo hmiddleNotHull T N row =>
      cases role <;>
        simp [IsDirectTargetRole, RealizedSourceRow.targetAtRole] at hdirect hrole
      subst target
      have hsource : N.frame.toCanonical source.1 = Erdos957Cases24.Case2.u := by
        rw [← N.source_actual, N.frame.toCanonical_actual]
      have hmiddle : N.frame.toCanonical middle = Erdos957Cases24.Case2.v := by
        rw [← N.middle_actual, N.frame.toCanonical_actual]
      have hassoc : Arr.association = oppositeCyclicSideAssociation T.side := by
        simpa [RealizedSourceRow.ArrivalCertificate] using Arr.certificate.1
      refine .outer ⟨middle, ?_, ?_, hmiddleNotHull, ?_⟩
      · exact adj_of_rigid_coordinate_dist N.frame source.1 middle
          Erdos957Cases24.Case2.u Erdos957Cases24.Case2.v
          hsource hmiddle Erdos957Cases24.Case2.dist_u_v
      · exact adj_of_rigid_coordinate_dist N.frame row.outer.vertex middle
          Erdos957Cases24.Case2.b Erdos957Cases24.Case2.v
          row.outer_edge_coordinate hmiddle
          (by simpa [dist_comm] using Erdos957Cases24.Case2.dist_v_b)
      · rcases case2Outer_association_side C source middle row.outer.vertex T N
          row.outer_edge_coordinate with h | h
        · exact Or.inl ⟨h.1, by simpa [hassoc] using h.2⟩
        · exact Or.inr ⟨h.1, by simpa [hassoc] using h.2⟩
  | case3 middle hdegree hone middleCoord row hmiddleVertex =>
      cases row with
      | low middleTarget hm hu hfour =>
          cases role <;>
            simp [IsDirectTargetRole, RealizedSourceRow.targetAtRole] at hdirect hrole
          subst target
          change middleTarget.vertex = middle at hmiddleVertex
          have hassoc := Arr.certificate
          simp only [RealizedSourceRow.ArrivalCertificate] at hassoc
          refine .singleton (by rw [hmiddleVertex]; exact hone)
            middleCoord hm ?_
          rcases hassoc.2.2.2.2 with h | h
          · rw [h.2]
            simp [horizontalAssociation, h.1]
          · rw [h.2]
            simp [horizontalAssociation, not_le.mpr h.1]
      | high secondaryCoord middleTarget secondaryTarget hm hs hu hsu hmu hne =>
          cases role <;>
            simp [IsDirectTargetRole, RealizedSourceRow.targetAtRole] at hdirect hrole
          · subst target
            change middleTarget.vertex = middle at hmiddleVertex
            have hassoc := Arr.certificate
            simp only [RealizedSourceRow.ArrivalCertificate] at hassoc
            refine .singleton (by rw [hmiddleVertex]; exact hone)
              middleCoord hm ?_
            rcases hassoc.2.2.2.2 with h | h
            · rw [h.2]
              simp [horizontalAssociation, h.1]
            · rw [h.2]
              simp [horizontalAssociation, not_le.mpr h.1]
          · subst target
            have hsourceMiddle : (unitDistanceGraph A).Adj source.1
                middleTarget.vertex := by
              apply adj_of_sqDist_coord_eq_one C source source.1 middleTarget.vertex
              rw [C.coord_source, hm]
              exact hu
            have htargetMiddle : (unitDistanceGraph A).Adj secondaryTarget.vertex
                middleTarget.vertex := by
              apply adj_of_sqDist_coord_eq_one C source secondaryTarget.vertex
                middleTarget.vertex
              rw [hs, hm]
              simpa [Erdos957Cases13.sqDist_comm] using hmu
            have hassoc := Arr.certificate
            simp only [RealizedSourceRow.ArrivalCertificate] at hassoc
            refine .outer ⟨middleTarget.vertex, hsourceMiddle, htargetMiddle,
              middleTarget.not_hull, ?_⟩
            rcases hassoc.2.2 with h | h
            · exact Or.inl ⟨by
                simpa only [C.coord_source, hm, hs, Erdos957Cases13.origin]
                  using h.1, h.2⟩
            · exact Or.inr ⟨by
                simpa only [C.coord_source, hm, hs, Erdos957Cases13.origin]
                  using h.1, h.2⟩
  | case4 middle hdegree htwo T N row hmiddleVertex =>
      cases row with
      | whole middleTarget hm hfour =>
          cases role <;>
            simp [IsDirectTargetRole, RealizedSourceRow.targetAtRole] at hdirect hrole
          subst target
          change middleTarget.vertex = middle at hmiddleVertex
          have ha : Arr.association = cyclicSideAssociation T.side := by
            simpa [RealizedSourceRow.ArrivalCertificate,
              orientedHorizontalAssociation_case2_v] using Arr.certificate.1
          exact .paired middle T hmiddleVertex ha
      | orderedLow farthest hfive middleTarget lowTarget hm hl hne =>
          cases role <;>
            simp [IsDirectTargetRole, RealizedSourceRow.targetAtRole] at hdirect hrole
          subst target
          change middleTarget.vertex = middle at hmiddleVertex
          have ha : Arr.association = cyclicSideAssociation T.side := by
            simpa [RealizedSourceRow.ArrivalCertificate,
              orientedHorizontalAssociation_case2_v] using Arr.certificate.1
          exact .paired middle T hmiddleVertex ha
      | orderedHigh farthest hsix recipients middleTarget sideTarget hm hs hne =>
          cases role <;>
            simp [IsDirectTargetRole, RealizedSourceRow.targetAtRole] at hdirect hrole
          subst target
          change middleTarget.vertex = middle at hmiddleVertex
          have ha : Arr.association = cyclicSideAssociation T.side := by
            simpa [RealizedSourceRow.ArrivalCertificate,
              orientedHorizontalAssociation_case2_v] using Arr.certificate.1
          exact .paired middle T hmiddleVertex ha
      | pairedSplit commonFrame farthest branch right hright middleTarget
          secondaryTarget hsource hm hs hne =>
          cases role <;>
            simp [IsDirectTargetRole, RealizedSourceRow.targetAtRole] at hdirect hrole
          subst target
          change middleTarget.vertex = middle at hmiddleVertex
          have ha : Arr.association = cyclicSideAssociation T.side := by
            simpa [RealizedSourceRow.ArrivalCertificate, hright,
              pairedMiddleHorizontalAssociation T] using Arr.certificate.1
          exact .paired middle T hmiddleVertex ha

private lemma twoExtreme_side_eq_next_of_next_adj
    {A : Finset Point} (hA : IsOneSeparated A)
    (P : CyclicHullData A) (W : DiameterWitnessData P)
    (source : {p // p ∈ P.H})
    (hs : source.1 ∈ sourceVertices P W) (middle : Vertex A)
    (hsource : (unitDistanceGraph A).Adj source.1 middle)
    (T : TwoExtremeCyclicWitness P source middle)
    (hnext : (unitDistanceGraph A).Adj (P.next source).1 middle) :
    T.side = .next := by
  cases hside : T.side with
  | next => rfl
  | previous =>
      exfalso
      exact not_both_cyclic_neighbors_adjacent_to_middle hA P W source hs
        middle hsource
        (by simpa [cyclicSideVertex, hside] using T.side_adjacent)
        ((unitDistanceGraph A).adj_symm hnext)

private lemma twoExtreme_side_eq_previous_of_previous_adj
    {A : Finset Point} (hA : IsOneSeparated A)
    (P : CyclicHullData A) (W : DiameterWitnessData P)
    (source : {p // p ∈ P.H})
    (hs : source.1 ∈ sourceVertices P W) (middle : Vertex A)
    (hsource : (unitDistanceGraph A).Adj source.1 middle)
    (T : TwoExtremeCyclicWitness P source middle)
    (hprevious : (unitDistanceGraph A).Adj (P.next⁻¹ source).1 middle) :
    T.side = .previous := by
  cases hside : T.side with
  | previous => rfl
  | next =>
      exfalso
      exact not_both_cyclic_neighbors_adjacent_to_middle hA P W source hs
        middle hsource ((unitDistanceGraph A).adj_symm hprevious)
        (by simpa [cyclicSideVertex, hside] using T.side_adjacent)

/-- Consecutive distinct sources cannot send direct arrivals with the same
formula-derived association. -/
theorem adjacent_direct_associations_ne
    {A : Finset Point} (hA : IsOneSeparated A)
    {P : CyclicHullData A} (W : DiameterWitnessData P)
    (C : P.AlignedChartData) (s : {p // p ∈ P.H})
    (hs : s.1 ∈ sourceVertices P W) (ht : (P.next s).1 ∈ sourceVertices P W)
    {v : Vertex A} {as assT : ArrivalAssociation}
    (hsv : (unitDistanceGraph A).Adj s.1 v)
    (htv : (unitDistanceGraph A).Adj (P.next s).1 v)
    (Fs : DirectArrivalFormula C s v as)
    (Ft : DirectArrivalFormula C (P.next s) v assT) :
    as ≠ assT := by
  cases Fs with
  | singleton hone _ _ _ =>
      exfalso
      have hEq := Erdos957Case3SameSide.hull_source_eq_of_singleton_unit_neighbors
        hone hsv.symm htv.symm
      exact P.next_ne_self s hEq.symm
  | outer Os =>
      cases Ft with
      | singleton hone _ _ _ =>
          exfalso
          have hEq := Erdos957Case3SameSide.hull_source_eq_of_singleton_unit_neighbors
            hone hsv.symm htv.symm
          exact P.next_ne_self s hEq.symm
      | outer Ot =>
          obtain ⟨hsPos, htNonpos⟩ :=
            Erdos957Case3SameSide.case3_equilateral_orientations_opposite_across_next_edge
              hA P C s hsv htv Os.source_proxy Os.target_proxy
                Ot.source_proxy Ot.target_proxy Os.proxy_not_hull Ot.proxy_not_hull
          have has : as = .fromNext := by
            rcases Os.association_side with ⟨hle, ha⟩ | ⟨_, ha⟩
            · exact (not_lt_of_ge hle hsPos).elim
            · exact ha
          have hat : assT = .fromPrevious := by
            rcases Ot.association_side with ⟨_, ha⟩ | ⟨hpos, ha⟩
            · exact ha
            · exact (not_lt_of_ge htNonpos hpos).elim
          rw [has, hat]
          decide
      | paired mt Tt hvt hat =>
          subst mt
          have htSide := twoExtreme_side_eq_previous_of_previous_adj hA P W
            (P.next s) ht v htv Tt (by simpa using hsv)
          have hsPos :=
            Erdos957Case3SameSide.predecessor_equilateral_orientation_positive_across_next_edge
              hA P C s hsv htv Os.source_proxy Os.target_proxy Os.proxy_not_hull
          have has : as = .fromNext := by
            rcases Os.association_side with ⟨hle, ha⟩ | ⟨_, ha⟩
            · exact (not_lt_of_ge hle hsPos).elim
            · exact ha
          have hat' : assT = .fromPrevious := by
            rw [hat, htSide]
            rfl
          rw [has, hat']
          decide
  | paired ms Ts hvs has =>
      subst ms
      have hsSide := twoExtreme_side_eq_next_of_next_adj hA P W s hs v hsv Ts htv
      cases Ft with
      | singleton hone _ _ _ =>
          exfalso
          have hEq := Erdos957Case3SameSide.hull_source_eq_of_singleton_unit_neighbors
            hone hsv.symm htv.symm
          exact P.next_ne_self s hEq.symm
      | outer Ot =>
          have htNonpos :=
            Erdos957Case3SameSide.successor_equilateral_orientation_nonpositive_across_next_edge
              hA P C s hsv htv Ot.source_proxy Ot.target_proxy Ot.proxy_not_hull
          have has' : as = .fromNext := by rw [has, hsSide]; rfl
          have hat' : assT = .fromPrevious := by
            rcases Ot.association_side with ⟨_, ha⟩ | ⟨hpos, ha⟩
            · exact ha
            · exact (not_lt_of_ge htNonpos hpos).elim
          rw [has', hat']
          decide
      | paired mt Tt hvt hat =>
          subst mt
          have htSide := twoExtreme_side_eq_previous_of_previous_adj hA P W
            (P.next s) ht v htv Tt (by simpa using hsv)
          rw [has, hsSide, hat, htSide]
          decide

/-- Transported form of the consecutive-source theorem. -/
private theorem adjacent_direct_associations_ne_of_eq_next
    {A : Finset Point} (hA : IsOneSeparated A)
    {P : CyclicHullData A} (W : DiameterWitnessData P)
    (C : P.AlignedChartData) (s t : {p // p ∈ P.H})
    (hs : s.1 ∈ sourceVertices P W) (ht : t.1 ∈ sourceVertices P W)
    {v : Vertex A} {as assT : ArrivalAssociation}
    (hsv : (unitDistanceGraph A).Adj s.1 v)
    (htv : (unitDistanceGraph A).Adj t.1 v)
    (Fs : DirectArrivalFormula C s v as)
    (Ft : DirectArrivalFormula C t v assT)
    (hst : t = P.next s) : as ≠ assT := by
  subst t
  exact adjacent_direct_associations_ne hA W C s hs ht hsv htv Fs Ft

/-- Direct realized arrivals in one seven-source window have distinct
formula-derived sides unless their emitting sources are equal.  This is a
standalone source-uniqueness leaf; it does not assert a capacity bound. -/
theorem direct_direct_source_eq
    {A : Finset Point} (hA : IsOneSeparated A)
    {P : CyclicHullData A} (W : DiameterWitnessData P)
    (F : P.FlatAlignedFrameData)
    (rows : HasRealizedSourceRows P W F.chart)
    {s t : Source P W} {v : Vertex A}
    (S : RealizedArrivalAt (F := F) rows s v)
    (T : RealizedArrivalAt (F := F) rows t v)
    (hsDirect : IsDirectTargetRole S.target.role)
    (htDirect : IsDirectTargetRole T.target.role)
    (htWindow : t.1 ∈ Finset.univ.image (fun j : Fin 7 ↦
      (sevenShift P.next j (sourceIndex P W s.1 s.property)).1))
    (hassociation : S.descriptor.association = T.descriptor.association) :
    s = t := by
  by_contra hst
  have hsAdj := S.target.adj_source_of_directRole hsDirect
  have htAdj := T.target.adj_source_of_directRole htDirect
  have hvNotHull : v ∉ P.H := by
    rw [S.target.vertex_eq]
    exact S.target.target.not_hull
  let Fs := directArrivalFormula S.target S.descriptor hsDirect
  let Ft := directArrivalFormula T.target T.descriptor htDirect
  rcases Erdos957ExceptionalWindowDispatch.sourceIndex_orbit_cases_of_mem_seven_window
      htWindow hst with hprev3 | hprev2 | hprev1 | hnext1 | hnext2 | hnext3
  · exact Erdos957RoleCollisions.no_common_unit_target_third_predecessor
      F hsAdj htAdj hprev3
  · exact no_common_unit_target_second_predecessor hA F
      (sourceIndex P W s.1 s.property)
      (Erdos957GeometryLocalityBridge.sourceIndex_isFlat W s)
      (sourceIndex P W t.1 t.property) v hvNotHull hsAdj htAdj hprev2
  · have hnext : sourceIndex P W s.1 s.property =
        P.next (sourceIndex P W t.1 t.property) := by
      rw [hprev1]
      simp
    have hne := adjacent_direct_associations_ne_of_eq_next hA W F.chart
      (sourceIndex P W t.1 t.property) (sourceIndex P W s.1 s.property)
      t.property s.property htAdj hsAdj Ft Fs hnext
    exact hne hassociation.symm
  · have hne := adjacent_direct_associations_ne_of_eq_next hA W F.chart
      (sourceIndex P W s.1 s.property) (sourceIndex P W t.1 t.property)
      s.property t.property hsAdj htAdj Fs Ft hnext1
    exact hne hassociation
  · exact no_common_unit_target_second_successor hA F
      (sourceIndex P W s.1 s.property)
      (Erdos957GeometryLocalityBridge.sourceIndex_isFlat W s)
      (sourceIndex P W t.1 t.property) v hvNotHull hsAdj htAdj hnext2
  · exact Erdos957RoleCollisions.no_common_unit_target_third_successor
      F hsAdj htAdj hnext3

/-- The hull selected from a radial order and its lifted cyclic order. -/
abbrev ProducedHull
    {A : Finset Point} (R : Erdos957.RadiallySortedCyclicHullOrder A)
    (L : Erdos957TurnSum.HullOrderBridge.LiftedCyclicHullOrder R.order) :
    CyclicHullData A :=
  Erdos957HullGeometryBridge.cyclicHullDataOfOrder R.order L

/-- The canonical flat bisector frame used by the produced row family. -/
abbrev ProducedFrame
    {A : Finset Point} (hA : IsOneSeparated A)
    (R : Erdos957.RadiallySortedCyclicHullOrder A)
    (L : Erdos957TurnSum.HullOrderBridge.LiftedCyclicHullOrder R.order) :
    (ProducedHull R L).FlatAlignedFrameData :=
  Erdos957BisectorPolar.bisectorFlatAlignedFrameData R.order L hA

/-- The exact dependent rows selected by the coherent produced family. -/
noncomputable abbrev ProducedRows
    {A : Finset Point} (hA : IsOneSeparated A)
    (R : Erdos957.RadiallySortedCyclicHullOrder A)
    (L : Erdos957TurnSum.HullOrderBridge.LiftedCyclicHullOrder R.order)
    (W : DiameterWitnessData (ProducedHull R L)) :
    HasRealizedSourceRows (ProducedHull R L) W (ProducedFrame hA R L).chart :=
  (Erdos957CoherentRealizedRows.producedCommonCoherentRealizedSourceRows
    hA R L W).rows

/-- No-residual specialization of `direct_direct_source_eq` to the
canonical produced hull, frame, and dependent realized-row selector. -/
theorem produced_direct_direct
    {A : Finset Point} (hA : IsOneSeparated A)
    (R : Erdos957.RadiallySortedCyclicHullOrder A)
    (L : Erdos957TurnSum.HullOrderBridge.LiftedCyclicHullOrder R.order)
    (W : DiameterWitnessData (ProducedHull R L))
    {s t : Source (ProducedHull R L) W} {v : Vertex A}
    (S : RealizedArrivalAt (F := ProducedFrame hA R L)
      (ProducedRows hA R L W) s v)
    (T : RealizedArrivalAt (F := ProducedFrame hA R L)
      (ProducedRows hA R L W) t v)
    (hsDirect : IsDirectTargetRole S.target.role)
    (htDirect : IsDirectTargetRole T.target.role)
    (htWindow : t.1 ∈ Finset.univ.image (fun j : Fin 7 ↦
      (sevenShift (ProducedHull R L).next j
        (sourceIndex (ProducedHull R L) W s.1 s.property)).1))
    (hassociation : S.descriptor.association = T.descriptor.association) :
    s = t :=
  direct_direct_source_eq hA W (ProducedFrame hA R L)
    (ProducedRows hA R L W) S T hsDirect htDirect htWindow hassociation
end Erdos957DirectSameSide

#print axioms Erdos957DirectSameSide.direct_direct_source_eq
#print axioms Erdos957DirectSameSide.produced_direct_direct
