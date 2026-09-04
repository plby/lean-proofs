import ErdosProblems.Erdos957.GeometryCore
import ErdosProblems.Erdos957.TurnSum
import ErdosProblems.Erdos957.HullGeometryBridge

/-!
# Tangent-bisector charts for the Erdős 957 locality argument

`CyclicHullData.frame` is an arbitrary strict exposing frame, which is
enough for the hull degree bound but has no canonical horizontal direction.
This module constructs the separate chart needed by locality from the
unwrapped directions of the two incident hull edges.  The chart is a
rotation followed by reflection in the horizontal axis.  Consequently it
preserves distance, reverses signed area, and puts the supporting half-plane
strictly below the horizontal axis.
-/

open Set
open scoped BigOperators RealInnerProductSpace

noncomputable section

namespace Erdos957BisectorFrame

open Erdos957
open Erdos957GeometryCore
open Erdos957HullGeometryBridge
open Erdos957TurnSum
open Erdos957TurnSum.HullOrderBridge

abbrev Point := Erdos957.Point
abbrev Vertex (A : Finset Point) := Erdos957GeometryCore.Vertex A

/-- Rotation by `-θ`, followed by reflection in the horizontal axis. -/
def anglePairCoord (θ : ℝ) (o q : Point) : ℝ × ℝ :=
  let v := q - o
  (Real.cos θ * v 0 + Real.sin θ * v 1,
    Real.sin θ * v 0 - Real.cos θ * v 1)

@[simp]
theorem anglePairCoord_self (θ : ℝ) (o : Point) :
    anglePairCoord θ o o = (0, 0) := by
  simp [anglePairCoord]

/-- The chart is an exact Euclidean isometry in pair coordinates. -/
theorem sqDist_anglePairCoord (θ : ℝ) (o q r : Point) :
    Erdos957Cases13.sqDist (anglePairCoord θ o q)
        (anglePairCoord θ o r) = dist q r ^ 2 := by
  rw [Erdos957Cases24.dist_sq_eq_coordinates]
  simp only [anglePairCoord, Erdos957Cases13.sqDist, PiLp.sub_apply]
  have htrig : Real.cos θ ^ 2 + Real.sin θ ^ 2 = 1 := by
    nlinarith [Real.sin_sq_add_cos_sq θ]
  calc
    _ = (Real.cos θ ^ 2 + Real.sin θ ^ 2) *
        ((q 0 - r 0) ^ 2 + (q 1 - r 1) ^ 2) := by ring
    _ = _ := by rw [htrig]; ring

/-- Its determinant is the negative of ambient signed area. -/
theorem pairCross_anglePairCoord_displacements (θ : ℝ)
    (o p q r : Point) :
    CyclicHullData.pairCross
        (CyclicHullData.pairSub (anglePairCoord θ o q) (anglePairCoord θ o p))
        (CyclicHullData.pairSub (anglePairCoord θ o r) (anglePairCoord θ o p)) =
      -Erdos957GeometryCore.cross (q - p) (r - p) := by
  simp only [anglePairCoord, CyclicHullData.pairCross,
    CyclicHullData.pairSub, Erdos957GeometryCore.cross, PiLp.sub_apply]
  have htrig : Real.cos θ ^ 2 + Real.sin θ ^ 2 = 1 := by
    nlinarith [Real.sin_sq_add_cos_sq θ]
  calc
    _ = -(Real.cos θ ^ 2 + Real.sin θ ^ 2) *
        ((q 0 - p 0) * (r 1 - p 1) -
          (q 1 - p 1) * (r 0 - p 0)) := by ring
    _ = _ := by rw [htrig]; ring

/-- Coordinates of a vector whose unwrapped direction is `α`. -/
theorem anglePairCoord_smul_unitDirection (θ α r : ℝ) (o : Point) :
    anglePairCoord θ o (o + r • unitDirection α) =
      (r * Real.cos (α - θ), -r * Real.sin (α - θ)) := by
  apply Prod.ext
  · simp [anglePairCoord, unitDirection, Real.cos_sub]
    ring
  · simp [anglePairCoord, unitDirection, Real.sin_sub]
    ring

/-! ## The actual incident-edge bisector -/

variable {A : Finset Point} {P : CyclicHullOrder A}

abbrev HullIndex (A : Finset Point) := Fin (hullVertexCount A)

/-- The index of the directed edge entering `i`. -/
def previousIndex (i : HullIndex A) : HullIndex A :=
  (finRotate (hullVertexCount A)).symm i

/-- The genuine exterior turn at `i`, read from the edge-direction lift. -/
def incidentTurn (L : LiftedCyclicHullOrder P) (i : HullIndex A) : ℝ :=
  L.lift.turn (previousIndex i)

/-- The unwrapped tangent direction halfway between the incoming and
outgoing directed hull edges. -/
def bisectorAngle (L : LiftedCyclicHullOrder P) (i : HullIndex A) : ℝ :=
  L.lift.angle (previousIndex i).1 + incidentTurn L i / 2

theorem incidentTurn_pos (L : LiftedCyclicHullOrder P) (i : HullIndex A) :
    0 < incidentTurn L i := by
  have hs := L.sin_lift_turn_pos (previousIndex i)
  have hn := L.lift.turn_nonneg (previousIndex i)
  by_contra h
  have hz : L.lift.turn (previousIndex i) = 0 := le_antisymm (not_lt.mp h) hn
  rw [hz] at hs
  simpa using hs

theorem incidentTurn_lt_pi (L : LiftedCyclicHullOrder P) (i : HullIndex A) :
    incidentTurn L i < Real.pi := by
  have hs := L.sin_lift_turn_pos (previousIndex i)
  have hle := L.lift_turn_le_pi (previousIndex i)
  apply lt_of_le_of_ne hle
  intro h
  rw [h] at hs
  simpa using hs

theorem cos_incidentTurn_half_pos (L : LiftedCyclicHullOrder P)
    (i : HullIndex A) : 0 < Real.cos (incidentTurn L i / 2) := by
  apply Real.cos_pos_of_mem_Ioo
  constructor
  · nlinarith [Real.pi_pos, incidentTurn_pos L i]
  · nlinarith [incidentTurn_lt_pi L i]

/-- Elementary vector form of the angle-bisector identity. -/
theorem two_cos_half_smul_unitDirection_midpoint (α δ : ℝ) :
    (2 * Real.cos (δ / 2)) • unitDirection (α + δ / 2) =
      unitDirection α + unitDirection (α + δ) := by
  have hcos : Real.cos δ =
      2 * Real.cos (δ / 2) ^ 2 - 1 := by
    rw [show δ = 2 * (δ / 2) by ring, Real.cos_two_mul]
    ring_nf
  have hsin : Real.sin δ =
      2 * Real.sin (δ / 2) * Real.cos (δ / 2) := by
    calc
      Real.sin δ = Real.sin (2 * (δ / 2)) := by congr 1 <;> ring
      _ = 2 * Real.sin (δ / 2) * Real.cos (δ / 2) := by
        rw [Real.sin_two_mul]
  ext j
  fin_cases j
  · simp [unitDirection, Real.cos_add, hcos, hsin]
    ring
  · simp [unitDirection, Real.sin_add, hcos, hsin]
    ring

theorem det_unitDirection_midpoint_nonneg {α δ : ℝ} {v : Point}
    (hcos : 0 < Real.cos (δ / 2))
    (hin : 0 ≤ det (unitDirection α) v)
    (hout : 0 ≤ det (unitDirection (α + δ)) v) :
    0 ≤ det (unitDirection (α + δ / 2)) v := by
  have hmid := congrArg (fun u : Point ↦ det u v)
    (two_cos_half_smul_unitDirection_midpoint α δ)
  have heq :
      (2 * Real.cos (δ / 2)) *
          det (unitDirection (α + δ / 2)) v =
        det (unitDirection α) v + det (unitDirection (α + δ)) v := by
    calc
      _ = det ((2 * Real.cos (δ / 2)) •
          unitDirection (α + δ / 2)) v := by simp [det]; ring
      _ = det (unitDirection α + unitDirection (α + δ)) v := hmid
      _ = _ := by simp [det]; ring
  have hfactor : 0 < 2 * Real.cos (δ / 2) := mul_pos (by norm_num) hcos
  nlinarith

theorem det_smul_left (s : ℝ) (u v : Point) :
    det (s • u) v = s * det u v := by
  calc
    det (s • u) v = det (s • u) (1 • v) := by simp
    _ = s * 1 * det u v := det_smul_smul s 1 u v
    _ = _ := by ring

/-- Two linearly independent determinant equations force a planar vector to
vanish.  This is the algebraic strictness step for the bisector support. -/
theorem eq_zero_of_two_det_eq_zero {u w v : Point}
    (huw : det u w ≠ 0) (huv : det u v = 0) (hwv : det w v = 0) :
    v = 0 := by
  have hx : det u w * v 0 = 0 := by
    change u 0 * v 1 - u 1 * v 0 = 0 at huv
    change w 0 * v 1 - w 1 * v 0 = 0 at hwv
    change (u 0 * w 1 - u 1 * w 0) * v 0 = 0
    linear_combination w 0 * huv - u 0 * hwv
  have hy : det u w * v 1 = 0 := by
    change u 0 * v 1 - u 1 * v 0 = 0 at huv
    change w 0 * v 1 - w 1 * v 0 = 0 at hwv
    change (u 0 * w 1 - u 1 * w 0) * v 1 = 0
    linear_combination w 1 * huv - u 1 * hwv
  have hv0 : v 0 = 0 := (mul_eq_zero.mp hx).resolve_left huw
  have hv1 : v 1 = 0 := (mul_eq_zero.mp hy).resolve_left huw
  ext j
  fin_cases j
  · exact hv0
  · exact hv1

/-- Strict form of the midpoint support lemma.  Nonnegative support by two
nonparallel rays is strict away from their common origin. -/
theorem det_unitDirection_midpoint_pos {α δ : ℝ} {v : Point}
    (hcos : 0 < Real.cos (δ / 2)) (hsin : 0 < Real.sin δ)
    (hin : 0 ≤ det (unitDirection α) v)
    (hout : 0 ≤ det (unitDirection (α + δ)) v) (hv : v ≠ 0) :
    0 < det (unitDirection (α + δ / 2)) v := by
  have hmid := congrArg (fun u : Point ↦ det u v)
    (two_cos_half_smul_unitDirection_midpoint α δ)
  have heq :
      (2 * Real.cos (δ / 2)) *
          det (unitDirection (α + δ / 2)) v =
        det (unitDirection α) v + det (unitDirection (α + δ)) v := by
    calc
      _ = det ((2 * Real.cos (δ / 2)) •
          unitDirection (α + δ / 2)) v := by simp [det]; ring
      _ = det (unitDirection α + unitDirection (α + δ)) v := hmid
      _ = _ := by simp [det]; ring
  have hsum : 0 <
      det (unitDirection α) v + det (unitDirection (α + δ)) v := by
    have hnonneg : 0 ≤
        det (unitDirection α) v + det (unitDirection (α + δ)) v :=
      add_nonneg hin hout
    apply lt_of_le_of_ne hnonneg
    intro hzero
    have hin0 : det (unitDirection α) v = 0 := by nlinarith
    have hout0 : det (unitDirection (α + δ)) v = 0 := by nlinarith
    apply hv
    apply eq_zero_of_two_det_eq_zero
      (u := unitDirection α) (w := unitDirection (α + δ))
    · rw [det_unitDirection]
      simpa using ne_of_gt hsin
    · exact hin0
    · exact hout0
  have hfactor : 0 < 2 * Real.cos (δ / 2) :=
    mul_pos (by norm_num) hcos
  nlinarith

/-- The tangent chart at an actual hull source. -/
def bisectorCoord (L : LiftedCyclicHullOrder P) (i : HullIndex A)
    (q : Point) : ℝ × ℝ :=
  anglePairCoord (bisectorAngle L i) (P.vertex i) q

@[simp]
theorem bisectorCoord_source (L : LiftedCyclicHullOrder P)
    (i : HullIndex A) : bisectorCoord L i (P.vertex i) = (0, 0) := by
  exact anglePairCoord_self _ _

theorem sqDist_bisectorCoord (L : LiftedCyclicHullOrder P)
    (i : HullIndex A) (q r : Point) :
    Erdos957Cases13.sqDist (bisectorCoord L i q) (bisectorCoord L i r) =
      dist q r ^ 2 :=
  sqDist_anglePairCoord _ _ _ _

theorem pairCross_bisectorCoord_displacements
    (L : LiftedCyclicHullOrder P) (i : HullIndex A) (p q r : Point) :
    CyclicHullData.pairCross
        (CyclicHullData.pairSub (bisectorCoord L i q) (bisectorCoord L i p))
        (CyclicHullData.pairSub (bisectorCoord L i r) (bisectorCoord L i p)) =
      -Erdos957GeometryCore.cross (q - p) (r - p) :=
  pairCross_anglePairCoord_displacements _ _ _ _ _

/-- Weak supporting-half-plane statement for the true incident-edge
bisector.  It is derived from the two genuine oriented hull-edge support
inequalities, not assumed as chart data. -/
theorem det_bisector_nonneg (L : LiftedCyclicHullOrder P)
    (i : HullIndex A) {q : Point} (hq : q ∈ A) :
    0 ≤ det (unitDirection (bisectorAngle L i)) (q - P.vertex i) := by
  let b : HullIndex A := previousIndex i
  have hbi : finRotate (hullVertexCount A) b = i := by
    exact (finRotate (hullVertexCount A)).apply_symm_apply i
  have hprevRaw := cyclic_edge_cross_nonneg P b hq
  have houtRaw := cyclic_edge_cross_nonneg P i hq
  have hprevEdge := L.edge_eq b
  have houtEdge := L.successor_edge_eq b
  rw [hbi] at hprevRaw hprevEdge houtEdge
  have htranslate :
      crossVec (P.vertex i - P.vertex b) (q - P.vertex b) =
        crossVec (P.vertex i - P.vertex b) (q - P.vertex i) := by
    simp only [crossVec, PiLp.sub_apply]
    ring
  rw [htranslate, hprevEdge] at hprevRaw
  rw [houtEdge] at houtRaw
  have hprevScaled :
      0 ≤ L.edgeScale b *
        det (unitDirection (L.lift.angle b.1)) (q - P.vertex i) := by
    rw [← det_eq_crossVec, det_smul_left] at hprevRaw
    exact hprevRaw
  have houtScaled :
      0 ≤ L.edgeScale i *
        det (unitDirection (L.lift.angle (b.1 + 1)))
          (q - P.vertex i) := by
    rw [← det_eq_crossVec, det_smul_left] at houtRaw
    exact houtRaw
  have hprev :
      0 ≤ det (unitDirection (L.lift.angle b.1)) (q - P.vertex i) :=
    nonneg_of_mul_nonneg_right hprevScaled (L.edgeScale_pos b)
  have hout :
      0 ≤ det (unitDirection (L.lift.angle (b.1 + 1)))
        (q - P.vertex i) :=
    nonneg_of_mul_nonneg_right houtScaled (L.edgeScale_pos i)
  have hangle :
      L.lift.angle b.1 + incidentTurn L i = L.lift.angle (b.1 + 1) := by
    simp only [incidentTurn, previousIndex, b, DirectionLift.turn]
    ring
  apply det_unitDirection_midpoint_nonneg
    (cos_incidentTurn_half_pos L i) hprev
  rwa [hangle]

/-- The incident-edge bisector strictly supports every actual point other
than the source.  Strictness is derived from the positive incident turn:
the two incident directions are linearly independent, so their two weak
support determinants cannot both vanish away from the source. -/
theorem det_bisector_pos (L : LiftedCyclicHullOrder P)
    (i : HullIndex A) {q : Point} (hq : q ∈ A) (hqi : q ≠ P.vertex i) :
    0 < det (unitDirection (bisectorAngle L i)) (q - P.vertex i) := by
  let b : HullIndex A := previousIndex i
  have hbi : finRotate (hullVertexCount A) b = i := by
    exact (finRotate (hullVertexCount A)).apply_symm_apply i
  have hprevRaw := cyclic_edge_cross_nonneg P b hq
  have houtRaw := cyclic_edge_cross_nonneg P i hq
  have hprevEdge := L.edge_eq b
  have houtEdge := L.successor_edge_eq b
  rw [hbi] at hprevRaw hprevEdge houtEdge
  have htranslate :
      crossVec (P.vertex i - P.vertex b) (q - P.vertex b) =
        crossVec (P.vertex i - P.vertex b) (q - P.vertex i) := by
    simp only [crossVec, PiLp.sub_apply]
    ring
  rw [htranslate, hprevEdge] at hprevRaw
  rw [houtEdge] at houtRaw
  have hprevScaled :
      0 ≤ L.edgeScale b *
        det (unitDirection (L.lift.angle b.1)) (q - P.vertex i) := by
    rw [← det_eq_crossVec, det_smul_left] at hprevRaw
    exact hprevRaw
  have houtScaled :
      0 ≤ L.edgeScale i *
        det (unitDirection (L.lift.angle (b.1 + 1)))
          (q - P.vertex i) := by
    rw [← det_eq_crossVec, det_smul_left] at houtRaw
    exact houtRaw
  have hprev :
      0 ≤ det (unitDirection (L.lift.angle b.1)) (q - P.vertex i) :=
    nonneg_of_mul_nonneg_right hprevScaled (L.edgeScale_pos b)
  have hout :
      0 ≤ det (unitDirection (L.lift.angle (b.1 + 1)))
        (q - P.vertex i) :=
    nonneg_of_mul_nonneg_right houtScaled (L.edgeScale_pos i)
  have hangle :
      L.lift.angle b.1 + incidentTurn L i = L.lift.angle (b.1 + 1) := by
    simp only [incidentTurn, previousIndex, b, DirectionLift.turn]
    ring
  have hsin : 0 < Real.sin (incidentTurn L i) := by
    exact L.sin_lift_turn_pos (previousIndex i)
  apply det_unitDirection_midpoint_pos
    (cos_incidentTurn_half_pos L i) hsin hprev
  · rwa [hangle]
  · exact sub_ne_zero.mpr hqi

/-- Pair-coordinate form of the supporting-half-plane conclusion. -/
theorem bisectorCoord_snd_nonpos (L : LiftedCyclicHullOrder P)
    (i : HullIndex A) {q : Point} (hq : q ∈ A) :
    (bisectorCoord L i q).2 ≤ 0 := by
  have h := det_bisector_nonneg L i hq
  simpa [bisectorCoord, anglePairCoord, det, bisectorAngle,
    unitDirection] using neg_nonpos.mpr h

/-- Strict pair-coordinate support away from the source. -/
theorem bisectorCoord_snd_neg (L : LiftedCyclicHullOrder P)
    (i : HullIndex A) {q : Point} (hq : q ∈ A) (hqi : q ≠ P.vertex i) :
    (bisectorCoord L i q).2 < 0 := by
  have h := det_bisector_pos L i hq hqi
  simpa [bisectorCoord, anglePairCoord, det, bisectorAngle,
    unitDirection] using neg_neg_of_pos h

/-! ## Transport to the production `CyclicHullData` index type -/

/-- The source chart transported through the exact hull-index equivalence
used by `cyclicHullDataOfOrder`. -/
def producedBisectorCoord (P : CyclicHullOrder A)
    (L : LiftedCyclicHullOrder P)
    (i : {p // p ∈ (cyclicHullDataOfOrder P L).H})
    (q : Vertex A) : ℝ × ℝ :=
  bisectorCoord L ((indexEquivLiftedHull P).symm i) (q : Point)

@[simp]
theorem producedBisectorCoord_source (P : CyclicHullOrder A)
    (L : LiftedCyclicHullOrder P)
    (i : {p // p ∈ (cyclicHullDataOfOrder P L).H}) :
    producedBisectorCoord P L i i.1 = (0, 0) := by
  let e := indexEquivLiftedHull P
  let a := e.symm i
  have hi : i = e a := (e.apply_symm_apply i).symm
  rw [hi]
  simp only [producedBisectorCoord, Equiv.symm_apply_apply]
  simpa [e] using bisectorCoord_source L a

theorem sqDist_producedBisectorCoord (P : CyclicHullOrder A)
    (L : LiftedCyclicHullOrder P)
    (i : {p // p ∈ (cyclicHullDataOfOrder P L).H})
    (q r : Vertex A) :
    Erdos957Cases13.sqDist (producedBisectorCoord P L i q)
        (producedBisectorCoord P L i r) =
      dist (q : Point) (r : Point) ^ 2 :=
  sqDist_bisectorCoord L _ _ _

theorem producedBisectorCoord_snd_nonpos (P : CyclicHullOrder A)
    (L : LiftedCyclicHullOrder P)
    (i : {p // p ∈ (cyclicHullDataOfOrder P L).H})
    (q : Vertex A) : (producedBisectorCoord P L i q).2 ≤ 0 := by
  exact bisectorCoord_snd_nonpos L _ q.property

/-- Strict support for the produced bisector chart, in the exact transported
hull-index type consumed by case classification. -/
theorem producedBisectorCoord_snd_neg (P : CyclicHullOrder A)
    (L : LiftedCyclicHullOrder P)
    (i : {p // p ∈ (cyclicHullDataOfOrder P L).H})
    (q : Vertex A) (hqi : q ≠ i.1) :
    (producedBisectorCoord P L i q).2 < 0 := by
  let e := indexEquivLiftedHull P
  let a := e.symm i
  have hi : i = e a := (e.apply_symm_apply i).symm
  rw [hi] at hqi ⊢
  simp only [producedBisectorCoord, Equiv.symm_apply_apply]
  have hqraw : (q : Point) ≠ P.vertex a := by
    intro hq
    apply hqi
    apply Subtype.ext
    simpa [e] using hq
  simpa [e] using bisectorCoord_snd_neg L a q.property hqraw

theorem pairCross_producedBisectorCoord_displacements
    (P : CyclicHullOrder A) (L : LiftedCyclicHullOrder P)
    (i : {p // p ∈ (cyclicHullDataOfOrder P L).H})
    (p q r : Vertex A) :
    CyclicHullData.pairCross
        (CyclicHullData.pairSub (producedBisectorCoord P L i q)
          (producedBisectorCoord P L i p))
        (CyclicHullData.pairSub (producedBisectorCoord P L i r)
          (producedBisectorCoord P L i p)) =
      -Erdos957GeometryCore.cross
        ((q : Point) - (p : Point)) ((r : Point) - (p : Point)) :=
  pairCross_bisectorCoord_displacements L _ _ _ _

/-- The genuine incident-edge bisector chart, packaged in the exact generic
interface consumed by local cases and locality. -/
noncomputable def bisectorAlignedChartData (P : CyclicHullOrder A)
    (L : LiftedCyclicHullOrder P) :
    (cyclicHullDataOfOrder P L).AlignedChartData where
  coord := producedBisectorCoord P L
  coord_source := producedBisectorCoord_source P L
  sqDist_coord := sqDist_producedBisectorCoord P L
  coord_snd_nonpos := producedBisectorCoord_snd_nonpos P L
  cross_displacements :=
    pairCross_producedBisectorCoord_displacements P L

/-- Strict-support projection phrased directly through the packaged chart. -/
theorem bisectorAlignedChartData_coord_snd_neg (P : CyclicHullOrder A)
    (L : LiftedCyclicHullOrder P)
    (i : {p // p ∈ (cyclicHullDataOfOrder P L).H})
    (q : Vertex A) (hqi : q ≠ i.1) :
    ((bisectorAlignedChartData P L).coord i q).2 < 0 :=
  producedBisectorCoord_snd_neg P L i q hqi

end Erdos957BisectorFrame
