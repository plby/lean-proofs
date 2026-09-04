import ErdosProblems.Erdos957.BisectorFrame

/-!
# Polar data for the genuine hull-edge bisector chart

This module isolates the angle bookkeeping needed to construct
`FlatAlignedFrameData` from a genuine lifted cyclic hull order.  It does not
modify either the generic geometry interface or the bisector-chart module.
-/

open Set
open scoped BigOperators RealInnerProductSpace

noncomputable section

namespace Erdos957BisectorPolar

open Erdos957
open Erdos957GeometryCore
open Erdos957HullGeometryBridge
open Erdos957BisectorFrame
open Erdos957TurnSum
open Erdos957TurnSum.HullOrderBridge

abbrev Point := Erdos957.Point

variable {A : Finset Point} {P : CyclicHullOrder A}

/-! ## Elementary coordinate and phase transport -/

/-- Equality of unit directions is preserved after adding the same phase. -/
theorem unitDirection_add_congr {a b : ℝ}
    (h : unitDirection a = unitDirection b) (c : ℝ) :
    unitDirection (a + c) = unitDirection (b + c) := by
  have hc := congrArg (fun u : Point ↦ u 0) h
  have hs := congrArg (fun u : Point ↦ u 1) h
  ext j
  fin_cases j <;>
    simp only [Fin.mk_one, Fin.isValue, Fin.zero_eta] at hc hs ⊢ <;>
    rw [hc, hs]

/-- A translated bisector chart sends a represented ambient vector to the
expected reflected polar angle `θ - α`. -/
theorem anglePairCoord_isPolarEdge {o p q : Point} {θ α r : ℝ}
    (hqp : q - p = r • unitDirection α) :
    Erdos957Locality.IsPolarEdge
      (anglePairCoord θ o p) (anglePairCoord θ o q) r (θ - α) := by
  have hx : q 0 - p 0 = r * Real.cos α := by
    simpa [unitDirection] using congrArg (fun u : Point ↦ u 0) hqp
  have hy : q 1 - p 1 = r * Real.sin α := by
    simpa [unitDirection] using congrArg (fun u : Point ↦ u 1) hqp
  constructor
  · simp only [anglePairCoord, Real.cos_sub]
    simp only [PiLp.sub_apply]
    linear_combination Real.cos θ * hx + Real.sin θ * hy
  · simp only [anglePairCoord, Real.sin_sub]
    simp only [PiLp.sub_apply]
    linear_combination Real.sin θ * hx - Real.cos θ * hy

/-- After additionally reflecting the horizontal coordinate, traversing an
edge backwards gives polar angle `α - θ`, where `α` is the direction of
the corresponding forward edge. -/
theorem reflected_anglePairCoord_backward_isPolarEdge
    {o p q : Point} {θ α r : ℝ}
    (hpq : p - q = r • unitDirection α) :
    Erdos957Locality.IsPolarEdge
      (let z := anglePairCoord θ o p; (-z.1, z.2))
      (let z := anglePairCoord θ o q; (-z.1, z.2)) r (α - θ) := by
  have hx : p 0 - q 0 = r * Real.cos α := by
    simpa [unitDirection] using congrArg (fun u : Point ↦ u 0) hpq
  have hy : p 1 - q 1 = r * Real.sin α := by
    simpa [unitDirection] using congrArg (fun u : Point ↦ u 1) hpq
  constructor
  · simp only [anglePairCoord, Real.cos_sub]
    simp only [PiLp.sub_apply]
    linear_combination Real.cos θ * hx + Real.sin θ * hy
  · simp only [anglePairCoord, Real.sin_sub]
    simp only [PiLp.sub_apply]
    linear_combination -Real.sin θ * hx + Real.cos θ * hy

/-! ## Unwrapped edge phases along the two source orbits -/

def forwardIndex (a : Fin (hullVertexCount A)) : ℕ →
    Fin (hullVertexCount A)
  | 0 => a
  | k + 1 => finRotate (hullVertexCount A) (forwardIndex a k)

def backwardVertexIndex (a : Fin (hullVertexCount A)) : ℕ →
    Fin (hullVertexCount A)
  | 0 => a
  | k + 1 => (finRotate (hullVertexCount A)).symm (backwardVertexIndex a k)

/-- The forward edge traversed by the `k`-th backward orbit step starts at
the `(k+1)`-st predecessor. -/
def backwardIndex (a : Fin (hullVertexCount A)) (k : ℕ) :
    Fin (hullVertexCount A) := backwardVertexIndex a (k + 1)

@[simp] theorem forwardIndex_zero (a : Fin (hullVertexCount A)) :
    forwardIndex a 0 = a := rfl

@[simp] theorem forwardIndex_succ (a : Fin (hullVertexCount A)) (k : ℕ) :
    forwardIndex a (k + 1) =
      finRotate (hullVertexCount A) (forwardIndex a k) := rfl

@[simp] theorem backwardVertexIndex_zero (a : Fin (hullVertexCount A)) :
    backwardVertexIndex a 0 = a := rfl

@[simp] theorem backwardVertexIndex_succ
    (a : Fin (hullVertexCount A)) (k : ℕ) :
    backwardVertexIndex a (k + 1) =
      (finRotate (hullVertexCount A)).symm (backwardVertexIndex a k) := rfl

@[simp] theorem backwardIndex_zero (a : Fin (hullVertexCount A)) :
    backwardIndex a 0 = previousIndex a := rfl

theorem finRotate_backwardIndex_succ (a : Fin (hullVertexCount A)) (k : ℕ) :
    finRotate (hullVertexCount A) (backwardIndex a (k + 1)) =
      backwardIndex a k := by
  simp only [backwardIndex, backwardVertexIndex]
  exact (finRotate (hullVertexCount A)).apply_symm_apply _

theorem finRotate_backwardIndex (a : Fin (hullVertexCount A)) (k : ℕ) :
    finRotate (hullVertexCount A) (backwardIndex a k) =
      backwardVertexIndex a k := by
  change finRotate (hullVertexCount A)
      ((finRotate (hullVertexCount A)).symm (backwardVertexIndex a k)) = _
  exact (finRotate (hullVertexCount A)).apply_symm_apply _

/-- A once-unwrapped direction of the `k`-th forward orbit edge. -/
def rightAbsoluteAngle (L : LiftedCyclicHullOrder P)
    (a : Fin (hullVertexCount A)) : ℕ → ℝ
  | 0 => L.lift.angle (previousIndex a).1 + incidentTurn L a
  | k + 1 => rightAbsoluteAngle L a k +
      L.lift.turn (forwardIndex a k)

/-- A once-unwrapped forward direction for the edge traversed backwards at
the `k`-th step of the predecessor orbit. -/
def leftAbsoluteAngle (L : LiftedCyclicHullOrder P)
    (a : Fin (hullVertexCount A)) : ℕ → ℝ
  | 0 => L.lift.angle (previousIndex a).1
  | k + 1 => leftAbsoluteAngle L a k -
      L.lift.turn (backwardIndex a (k + 1))

def rightPolarAngle (L : LiftedCyclicHullOrder P)
    (a : Fin (hullVertexCount A)) (k : ℕ) : ℝ :=
  bisectorAngle L a - rightAbsoluteAngle L a k

def leftPolarAngle (L : LiftedCyclicHullOrder P)
    (a : Fin (hullVertexCount A)) (k : ℕ) : ℝ :=
  leftAbsoluteAngle L a k - bisectorAngle L a

@[simp] theorem rightPolarAngle_zero (L : LiftedCyclicHullOrder P)
    (a : Fin (hullVertexCount A)) :
    rightPolarAngle L a 0 = -incidentTurn L a / 2 := by
  simp [rightPolarAngle, rightAbsoluteAngle, bisectorAngle]
  ring

@[simp] theorem leftPolarAngle_zero (L : LiftedCyclicHullOrder P)
    (a : Fin (hullVertexCount A)) :
    leftPolarAngle L a 0 = -incidentTurn L a / 2 := by
  simp [leftPolarAngle, leftAbsoluteAngle, bisectorAngle]
  ring

theorem rightPolarAngle_succ_sub (L : LiftedCyclicHullOrder P)
    (a : Fin (hullVertexCount A)) (k : ℕ) :
    rightPolarAngle L a (k + 1) - rightPolarAngle L a k =
      -L.lift.turn (forwardIndex a k) := by
  simp [rightPolarAngle, rightAbsoluteAngle]

theorem leftPolarAngle_succ_sub (L : LiftedCyclicHullOrder P)
    (a : Fin (hullVertexCount A)) (k : ℕ) :
    leftPolarAngle L a (k + 1) - leftPolarAngle L a k =
      -L.lift.turn (backwardIndex a (k + 1)) := by
  simp [leftPolarAngle, leftAbsoluteAngle]

/-- The recursively unwrapped forward phase represents the concrete edge
at the corresponding forward orbit index, including every seam crossing. -/
theorem unitDirection_rightAbsoluteAngle (L : LiftedCyclicHullOrder P)
    (a : Fin (hullVertexCount A)) (k : ℕ) :
    unitDirection (rightAbsoluteAngle L a k) =
      unitDirection (L.lift.angle (forwardIndex a k).1) := by
  induction k with
  | zero =>
      let b := previousIndex a
      have hba : finRotate (hullVertexCount A) b = a :=
        (finRotate (hullVertexCount A)).apply_symm_apply a
      have hs := L.lift.unitDirection_angle_succ_eq_finRotate b
      rw [hba] at hs
      simpa [rightAbsoluteAngle, incidentTurn, DirectionLift.turn, b] using hs
  | succ k ih =>
      let j := forwardIndex a k
      have hadd := unitDirection_add_congr ih (L.lift.turn j)
      have hs := L.lift.unitDirection_angle_succ_eq_finRotate j
      rw [show L.lift.angle j.1 + L.lift.turn j =
          L.lift.angle (j.1 + 1) by
        simp [DirectionLift.turn]] at hadd
      rw [hs] at hadd
      simpa [rightAbsoluteAngle, forwardIndex, j] using hadd

/-- The recursively unwrapped left phase represents the concrete forward
edge whose reverse is traversed by the predecessor orbit. -/
theorem unitDirection_leftAbsoluteAngle (L : LiftedCyclicHullOrder P)
    (a : Fin (hullVertexCount A)) (k : ℕ) :
    unitDirection (leftAbsoluteAngle L a k) =
      unitDirection (L.lift.angle (backwardIndex a k).1) := by
  induction k with
  | zero => simp [leftAbsoluteAngle]
  | succ k ih =>
      let d := backwardIndex a (k + 1)
      let j := backwardIndex a k
      have hdj : finRotate (hullVertexCount A) d = j := by
        exact finRotate_backwardIndex_succ a k
      have hs := L.lift.unitDirection_angle_succ_eq_finRotate d
      rw [hdj] at hs
      have hphase :
          unitDirection (leftAbsoluteAngle L a k) =
            unitDirection (L.lift.angle (d.1 + 1)) := ih.trans hs.symm
      have hsub := unitDirection_add_congr hphase (-L.lift.turn d)
      have hrhs : L.lift.angle (d.1 + 1) + -L.lift.turn d =
          L.lift.angle d.1 := by
        simp [DirectionLift.turn]
      rw [hrhs] at hsub
      simpa only [leftAbsoluteAngle, sub_eq_add_neg, d] using hsub

/-! ## Reduction of the transported chart orbits -/

theorem forwardIndex_eq_pow (a : Fin (hullVertexCount A)) (k : ℕ) :
    forwardIndex a k = (finRotate (hullVertexCount A) ^ k) a := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [forwardIndex_succ, ih, pow_succ, Equiv.Perm.mul_apply]
      rw [← Equiv.Perm.mul_apply, ← Equiv.Perm.mul_apply,
        (Commute.self_pow (finRotate (hullVertexCount A)) k).eq]

theorem backwardVertexIndex_eq_pow
    (a : Fin (hullVertexCount A)) (k : ℕ) :
    backwardVertexIndex a k =
      ((finRotate (hullVertexCount A)).symm ^ k) a := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [backwardVertexIndex_succ, ih, pow_succ, Equiv.Perm.mul_apply]
      rw [← Equiv.Perm.mul_apply, ← Equiv.Perm.mul_apply,
        (Commute.self_pow (finRotate (hullVertexCount A)).symm k).eq]

theorem hullNext_symm_pow_indexEquiv (L : LiftedCyclicHullOrder P)
    (a : Fin (hullVertexCount A)) (k : ℕ) :
    ((hullNext P).symm ^ k) (indexEquivLiftedHull P a) =
      indexEquivLiftedHull P (backwardVertexIndex a k) := by
  have hthree := L.hull_has_three
  have hpos : 0 < hullVertexCount A := by omega
  induction k generalizing a with
  | zero => simp
  | succ k ih =>
      rw [pow_succ, Equiv.Perm.mul_apply,
        hullNext_symm_indexEquiv P hpos, ih]
      rw [backwardVertexIndex_eq_pow, backwardVertexIndex_eq_pow,
        pow_succ, Equiv.Perm.mul_apply]

theorem produced_rightOrbitCoord_indexEquiv
    (L : LiftedCyclicHullOrder P) (a : Fin (hullVertexCount A)) (k : ℕ) :
    (bisectorAlignedChartData P L).rightOrbitCoord
        (cyclicHullDataOfOrder P L) (indexEquivLiftedHull P a) k =
      bisectorCoord L a (P.vertex (forwardIndex a k)) := by
  unfold CyclicHullData.AlignedChartData.rightOrbitCoord
  change producedBisectorCoord P L (indexEquivLiftedHull P a)
      ((((hullNext P ^ k) (indexEquivLiftedHull P a)).1 :
        Erdos957GeometryCore.Vertex A)) = _
  unfold producedBisectorCoord
  rw [hullNext_pow_indexEquiv, forwardIndex_eq_pow]
  simp

theorem produced_leftOrbitReflectedCoord_indexEquiv
    (L : LiftedCyclicHullOrder P) (a : Fin (hullVertexCount A)) (k : ℕ) :
    (bisectorAlignedChartData P L).leftOrbitReflectedCoord
        (cyclicHullDataOfOrder P L) (indexEquivLiftedHull P a) k =
      let z := bisectorCoord L a (P.vertex (backwardVertexIndex a k))
      (-z.1, z.2) := by
  unfold CyclicHullData.AlignedChartData.leftOrbitReflectedCoord
  change (let z := (producedBisectorCoord P L (indexEquivLiftedHull P a)
      (((hullNext P).symm ^ k) (indexEquivLiftedHull P a)).1)
    (-z.1, z.2)) = _
  unfold producedBisectorCoord
  rw [hullNext_symm_pow_indexEquiv L]
  simp

/-! ## Polar edge and radius data -/

theorem edgeScale_eq_norm (L : LiftedCyclicHullOrder P)
    (j : Fin (hullVertexCount A)) :
    L.edgeScale j =
      ‖P.vertex (finRotate (hullVertexCount A) j) - P.vertex j‖ := by
  have h := congrArg norm (L.edge_eq j)
  rw [norm_smul, norm_unitDirection, mul_one,
    Real.norm_of_nonneg (L.edgeScale_pos j).le] at h
  exact h.symm

theorem edgeScale_ge_one (L : LiftedCyclicHullOrder P)
    (hA : IsOneSeparated A) (j : Fin (hullVertexCount A)) :
    1 ≤ L.edgeScale j := by
  rw [edgeScale_eq_norm]
  have hsep := hA (P.vertex j) (P.vertex_mem j)
    (P.vertex (finRotate (hullVertexCount A) j))
    (P.vertex_mem (finRotate (hullVertexCount A) j))
    (P.consecutive_ne j)
  rw [dist_eq_norm] at hsep
  simpa [norm_sub_rev] using hsep

/-- Radius of the `k`-th forward orbit edge at a transported source. -/
def producedRightRadius (L : LiftedCyclicHullOrder P)
    (i : {p // p ∈ (cyclicHullDataOfOrder P L).H}) (k : ℕ) : ℝ :=
  L.edgeScale (forwardIndex ((indexEquivLiftedHull P).symm i) k)

/-- Polar angle of the `k`-th forward orbit edge in the bisector chart. -/
def producedRightAngle (L : LiftedCyclicHullOrder P)
    (i : {p // p ∈ (cyclicHullDataOfOrder P L).H}) (k : ℕ) : ℝ :=
  rightPolarAngle L ((indexEquivLiftedHull P).symm i) k

/-- Radius of the `k`-th reflected predecessor-orbit edge. -/
def producedLeftRadius (L : LiftedCyclicHullOrder P)
    (i : {p // p ∈ (cyclicHullDataOfOrder P L).H}) (k : ℕ) : ℝ :=
  L.edgeScale (backwardIndex ((indexEquivLiftedHull P).symm i) k)

/-- Polar angle of the `k`-th reflected predecessor-orbit edge. -/
def producedLeftAngle (L : LiftedCyclicHullOrder P)
    (i : {p // p ∈ (cyclicHullDataOfOrder P L).H}) (k : ℕ) : ℝ :=
  leftPolarAngle L ((indexEquivLiftedHull P).symm i) k

theorem producedRightPolar (L : LiftedCyclicHullOrder P)
    (i : {p // p ∈ (cyclicHullDataOfOrder P L).H}) (k : ℕ) :
    Erdos957Locality.IsPolarEdge
      ((bisectorAlignedChartData P L).rightOrbitCoord
        (cyclicHullDataOfOrder P L) i k)
      ((bisectorAlignedChartData P L).rightOrbitCoord
        (cyclicHullDataOfOrder P L) i (k + 1))
      (producedRightRadius L i k) (producedRightAngle L i k) := by
  let e := indexEquivLiftedHull P
  let a := e.symm i
  have hi : i = e a := (e.apply_symm_apply i).symm
  rw [hi, produced_rightOrbitCoord_indexEquiv,
    produced_rightOrbitCoord_indexEquiv]
  rw [forwardIndex_succ]
  have hedge := L.edge_eq (forwardIndex a k)
  rw [← unitDirection_rightAbsoluteAngle L a k] at hedge
  simpa [producedRightRadius, producedRightAngle, rightPolarAngle,
    bisectorCoord, e, a] using
    (anglePairCoord_isPolarEdge
      (o := P.vertex a) (θ := bisectorAngle L a) hedge)

theorem producedLeftPolar (L : LiftedCyclicHullOrder P)
    (i : {p // p ∈ (cyclicHullDataOfOrder P L).H}) (k : ℕ) :
    Erdos957Locality.IsPolarEdge
      ((bisectorAlignedChartData P L).leftOrbitReflectedCoord
        (cyclicHullDataOfOrder P L) i k)
      ((bisectorAlignedChartData P L).leftOrbitReflectedCoord
        (cyclicHullDataOfOrder P L) i (k + 1))
      (producedLeftRadius L i k) (producedLeftAngle L i k) := by
  let e := indexEquivLiftedHull P
  let a := e.symm i
  have hi : i = e a := (e.apply_symm_apply i).symm
  rw [hi, produced_leftOrbitReflectedCoord_indexEquiv,
    produced_leftOrbitReflectedCoord_indexEquiv]
  have hedge := L.edge_eq (backwardIndex a k)
  rw [finRotate_backwardIndex] at hedge
  rw [← unitDirection_leftAbsoluteAngle L a k] at hedge
  simpa [producedLeftRadius, producedLeftAngle, leftPolarAngle,
    bisectorCoord, backwardIndex, backwardVertexIndex, e, a] using
    (reflected_anglePairCoord_backward_isPolarEdge
      (o := P.vertex a) (θ := bisectorAngle L a) hedge)

theorem producedRightRadius_ge_one (L : LiftedCyclicHullOrder P)
    (hA : IsOneSeparated A)
    (i : {p // p ∈ (cyclicHullDataOfOrder P L).H}) (k : ℕ) :
    1 ≤ producedRightRadius L i k := by
  exact edgeScale_ge_one L hA _

theorem producedLeftRadius_ge_one (L : LiftedCyclicHullOrder P)
    (hA : IsOneSeparated A)
    (i : {p // p ∈ (cyclicHullDataOfOrder P L).H}) (k : ℕ) :
    1 ≤ producedLeftRadius L i k := by
  exact edgeScale_ge_one L hA _

theorem incidentTurn_eq_producedTurn (L : LiftedCyclicHullOrder P)
    (a : Fin (hullVertexCount A)) :
    incidentTurn L a =
      (cyclicHullDataOfOrder P L).turn (indexEquivLiftedHull P a) := by
  rw [cyclicHullDataOfOrder_turn_indexEquiv]
  unfold incidentTurn previousIndex
  have hthree := L.hull_has_three
  let : NeZero (hullVertexCount A) := ⟨by omega⟩
  have h := L.lift_turn_eq_exteriorTurn_finRotate
    ((finRotate (hullVertexCount A)).symm a)
  simpa using h

theorem producedRightAngle_zero (L : LiftedCyclicHullOrder P)
    (i : {p // p ∈ (cyclicHullDataOfOrder P L).H}) :
    producedRightAngle L i 0 =
      -(cyclicHullDataOfOrder P L).turn i / 2 := by
  let e := indexEquivLiftedHull P
  let a := e.symm i
  have hi : i = e a := (e.apply_symm_apply i).symm
  rw [hi]
  unfold producedRightAngle
  rw [Equiv.symm_apply_apply]
  change rightPolarAngle L a 0 =
    -(cyclicHullDataOfOrder P L).turn (e a) / 2
  rw [rightPolarAngle_zero]
  rw [incidentTurn_eq_producedTurn]

theorem producedLeftAngle_zero (L : LiftedCyclicHullOrder P)
    (i : {p // p ∈ (cyclicHullDataOfOrder P L).H}) :
    producedLeftAngle L i 0 =
      -(cyclicHullDataOfOrder P L).turn i / 2 := by
  let e := indexEquivLiftedHull P
  let a := e.symm i
  have hi : i = e a := (e.apply_symm_apply i).symm
  rw [hi]
  unfold producedLeftAngle
  rw [Equiv.symm_apply_apply]
  change leftPolarAngle L a 0 =
    -(cyclicHullDataOfOrder P L).turn (e a) / 2
  rw [leftPolarAngle_zero]
  rw [incidentTurn_eq_producedTurn]

theorem producedRightAngle_succ_sub (L : LiftedCyclicHullOrder P)
    (i : {p // p ∈ (cyclicHullDataOfOrder P L).H}) (k : ℕ) :
    producedRightAngle L i (k + 1) - producedRightAngle L i k =
      -L.lift.turn
        (forwardIndex ((indexEquivLiftedHull P).symm i) k) := by
  exact rightPolarAngle_succ_sub L _ k

theorem producedLeftAngle_succ_sub (L : LiftedCyclicHullOrder P)
    (i : {p // p ∈ (cyclicHullDataOfOrder P L).H}) (k : ℕ) :
    producedLeftAngle L i (k + 1) - producedLeftAngle L i k =
      -L.lift.turn
        (backwardIndex ((indexEquivLiftedHull P).symm i) (k + 1)) := by
  exact leftPolarAngle_succ_sub L _ k

/-! ## Identification with the seven-window turns -/

theorem producedTurn_forward (L : LiftedCyclicHullOrder P)
    (i : {p // p ∈ (cyclicHullDataOfOrder P L).H}) (k : ℕ) :
    (cyclicHullDataOfOrder P L).turn
        (((cyclicHullDataOfOrder P L).next ^ (k + 1)) i) =
      L.lift.turn (forwardIndex ((indexEquivLiftedHull P).symm i) k) := by
  let e := indexEquivLiftedHull P
  let a := e.symm i
  have hi : i = e a := (e.apply_symm_apply i).symm
  rw [hi]
  change (cyclicHullDataOfOrder P L).turn
      ((hullNext P ^ (k + 1)) (e a)) = _
  rw [hullNext_pow_indexEquiv, ← forwardIndex_eq_pow,
    forwardIndex_succ]
  simpa [a, e] using
    cyclicHullDataOfOrder_turn_successor_indexEquiv P L (forwardIndex a k)

theorem producedTurn_backward (L : LiftedCyclicHullOrder P)
    (i : {p // p ∈ (cyclicHullDataOfOrder P L).H}) (k : ℕ) :
    (cyclicHullDataOfOrder P L).turn
        ((((cyclicHullDataOfOrder P L).next).symm ^ (k + 1)) i) =
      L.lift.turn
        (backwardIndex ((indexEquivLiftedHull P).symm i) (k + 1)) := by
  let e := indexEquivLiftedHull P
  let a := e.symm i
  have hi : i = e a := (e.apply_symm_apply i).symm
  rw [hi]
  change (cyclicHullDataOfOrder P L).turn
      (((hullNext P).symm ^ (k + 1)) (e a)) = _
  rw [hullNext_symm_pow_indexEquiv L]
  rw [Equiv.symm_apply_apply]
  change (cyclicHullDataOfOrder P L).turn
      (indexEquivLiftedHull P (backwardIndex a k)) =
        L.lift.turn (backwardIndex a (k + 1))
  have hrot := finRotate_backwardIndex_succ a k
  rw [← hrot]
  exact cyclicHullDataOfOrder_turn_successor_indexEquiv P L
    (backwardIndex a (k + 1))

theorem sevenShift_zero_apply {ι : Type*} (σ : Equiv.Perm ι) (i : ι) :
    sevenShift σ (0 : Fin 7) i = (σ⁻¹ ^ 3) i := by
  simp [sevenShift]

theorem sevenShift_one_apply {ι : Type*} (σ : Equiv.Perm ι) (i : ι) :
    sevenShift σ (1 : Fin 7) i = (σ⁻¹ ^ 2) i := by
  change (σ ^ 1 * σ⁻¹ ^ 3) i = _
  congr 1
  group

theorem sevenShift_two_apply {ι : Type*} (σ : Equiv.Perm ι) (i : ι) :
    sevenShift σ (2 : Fin 7) i = σ⁻¹ i := by
  change (σ ^ 2 * σ⁻¹ ^ 3) i = _
  congr 1
  group

theorem sevenShift_four_apply {ι : Type*} (σ : Equiv.Perm ι) (i : ι) :
    sevenShift σ (4 : Fin 7) i = σ i := by
  change (σ ^ 4 * σ⁻¹ ^ 3) i = _
  congr 1
  group

theorem sevenShift_five_apply {ι : Type*} (σ : Equiv.Perm ι) (i : ι) :
    sevenShift σ (5 : Fin 7) i = (σ ^ 2) i := by
  change (σ ^ 5 * σ⁻¹ ^ 3) i = _
  congr 1
  group

theorem sevenShift_six_apply {ι : Type*} (σ : Equiv.Perm ι) (i : ι) :
    sevenShift σ (6 : Fin 7) i = (σ ^ 3) i := by
  change (σ ^ 6 * σ⁻¹ ^ 3) i = _
  congr 1
  group

/-! ## Flat-window estimates and the packaged constructor -/

theorem producedRightFlatAngles (L : LiftedCyclicHullOrder P)
    (i : {p // p ∈ (cyclicHullDataOfOrder P L).H})
    (hi : (cyclicHullDataOfOrder P L).IsFlat i) :
    |producedRightAngle L i 0| ≤ Real.pi / 180 ∧
    |producedRightAngle L i 1 - producedRightAngle L i 0| ≤ Real.pi / 180 ∧
    |producedRightAngle L i 2 - producedRightAngle L i 1| ≤ Real.pi / 180 ∧
    |producedRightAngle L i 3 - producedRightAngle L i 2| ≤ Real.pi / 180 := by
  let D := cyclicHullDataOfOrder P L
  have hzero := D.turn_lt_of_isFlat i hi
  have hzero_nonneg := D.turn_nonneg i
  have h4 := D.turn_sevenShift_lt i hi (4 : Fin 7)
  have h5 := D.turn_sevenShift_lt i hi (5 : Fin 7)
  have h6 := D.turn_sevenShift_lt i hi (6 : Fin 7)
  rw [sevenShift_four_apply] at h4
  rw [sevenShift_five_apply] at h5
  rw [sevenShift_six_apply] at h6
  have ht0 : L.lift.turn
      (forwardIndex ((indexEquivLiftedHull P).symm i) 0) < Real.pi / 180 := by
    calc
      L.lift.turn (forwardIndex ((indexEquivLiftedHull P).symm i) 0) =
          D.turn ((D.next ^ (0 + 1)) i) := (producedTurn_forward L i 0).symm
      _ = D.turn (D.next i) := by simp
      _ < Real.pi / 180 := h4
  have ht1 : L.lift.turn
      (forwardIndex ((indexEquivLiftedHull P).symm i) 1) < Real.pi / 180 := by
    calc
      L.lift.turn (forwardIndex ((indexEquivLiftedHull P).symm i) 1) =
          D.turn ((D.next ^ (1 + 1)) i) := (producedTurn_forward L i 1).symm
      _ < Real.pi / 180 := h5
  have ht2 : L.lift.turn
      (forwardIndex ((indexEquivLiftedHull P).symm i) 2) < Real.pi / 180 := by
    calc
      L.lift.turn (forwardIndex ((indexEquivLiftedHull P).symm i) 2) =
          D.turn ((D.next ^ (2 + 1)) i) := (producedTurn_forward L i 2).symm
      _ < Real.pi / 180 := h6
  constructor
  · rw [producedRightAngle_zero, abs_div, abs_neg,
      abs_of_nonneg hzero_nonneg]
    norm_num
    linarith [Real.pi_pos]
  constructor
  · rw [producedRightAngle_succ_sub, abs_neg,
      abs_of_nonneg (L.lift.turn_nonneg _)]
    exact ht0.le
  constructor
  · rw [producedRightAngle_succ_sub, abs_neg,
      abs_of_nonneg (L.lift.turn_nonneg _)]
    exact ht1.le
  · rw [producedRightAngle_succ_sub, abs_neg,
      abs_of_nonneg (L.lift.turn_nonneg _)]
    exact ht2.le

theorem producedLeftFlatAngles (L : LiftedCyclicHullOrder P)
    (i : {p // p ∈ (cyclicHullDataOfOrder P L).H})
    (hi : (cyclicHullDataOfOrder P L).IsFlat i) :
    |producedLeftAngle L i 0| ≤ Real.pi / 180 ∧
    |producedLeftAngle L i 1 - producedLeftAngle L i 0| ≤ Real.pi / 180 ∧
    |producedLeftAngle L i 2 - producedLeftAngle L i 1| ≤ Real.pi / 180 ∧
    |producedLeftAngle L i 3 - producedLeftAngle L i 2| ≤ Real.pi / 180 := by
  let D := cyclicHullDataOfOrder P L
  have hzero := D.turn_lt_of_isFlat i hi
  have hzero_nonneg := D.turn_nonneg i
  have h2 := D.turn_sevenShift_lt i hi (2 : Fin 7)
  have h1 := D.turn_sevenShift_lt i hi (1 : Fin 7)
  have h0 := D.turn_sevenShift_lt i hi (0 : Fin 7)
  rw [sevenShift_two_apply] at h2
  rw [sevenShift_one_apply] at h1
  rw [sevenShift_zero_apply] at h0
  have ht0 : L.lift.turn
      (backwardIndex ((indexEquivLiftedHull P).symm i) 1) < Real.pi / 180 := by
    calc
      L.lift.turn (backwardIndex ((indexEquivLiftedHull P).symm i) 1) =
          D.turn ((D.next.symm ^ (0 + 1)) i) :=
        (producedTurn_backward L i 0).symm
      _ = D.turn (D.next.symm i) := by simp
      _ < Real.pi / 180 := h2
  have ht1 : L.lift.turn
      (backwardIndex ((indexEquivLiftedHull P).symm i) 2) < Real.pi / 180 := by
    calc
      L.lift.turn (backwardIndex ((indexEquivLiftedHull P).symm i) 2) =
          D.turn ((D.next.symm ^ (1 + 1)) i) :=
        (producedTurn_backward L i 1).symm
      _ < Real.pi / 180 := h1
  have ht2 : L.lift.turn
      (backwardIndex ((indexEquivLiftedHull P).symm i) 3) < Real.pi / 180 := by
    calc
      L.lift.turn (backwardIndex ((indexEquivLiftedHull P).symm i) 3) =
          D.turn ((D.next.symm ^ (2 + 1)) i) :=
        (producedTurn_backward L i 2).symm
      _ < Real.pi / 180 := h0
  constructor
  · rw [producedLeftAngle_zero, abs_div, abs_neg,
      abs_of_nonneg hzero_nonneg]
    norm_num
    linarith [Real.pi_pos]
  constructor
  · rw [producedLeftAngle_succ_sub, abs_neg,
      abs_of_nonneg (L.lift.turn_nonneg _)]
    exact ht0.le
  constructor
  · rw [producedLeftAngle_succ_sub, abs_neg,
      abs_of_nonneg (L.lift.turn_nonneg _)]
    exact ht1.le
  · rw [producedLeftAngle_succ_sub, abs_neg,
      abs_of_nonneg (L.lift.turn_nonneg _)]
    exact ht2.le

/-- The genuine bisector chart, its seam-safe polar orbit descriptions,
and one-separation package every field of the flat aligned-frame interface. -/
noncomputable def bisectorFlatAlignedFrameData
    (P : CyclicHullOrder A) (L : LiftedCyclicHullOrder P)
    (hA : IsOneSeparated A) :
    (cyclicHullDataOfOrder P L).FlatAlignedFrameData where
  chart := bisectorAlignedChartData P L
  rightRadius i k := producedRightRadius L i k.1
  rightAngle i k := producedRightAngle L i k.1
  rightPolar i k := producedRightPolar L i k.1
  rightRadius_ge_one i k := producedRightRadius_ge_one L hA i k.1
  rightFlatAngles i hi := producedRightFlatAngles L i hi
  leftRadius i k := producedLeftRadius L i k.1
  leftAngle i k := producedLeftAngle L i k.1
  leftPolar i k := producedLeftPolar L i k.1
  leftRadius_ge_one i k := producedLeftRadius_ge_one L hA i k.1
  leftFlatAngles i hi := producedLeftFlatAngles L i hi

end Erdos957BisectorPolar
