/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos957.GeometryCore
import ErdosProblems.Erdos957.HullAngleLift
import ErdosProblems.Erdos957.StrictFrame
import ErdosProblems.Erdos957.TurnSum

/-!
# Bridge from cyclic hull orders to the charging geometry record

This module transports a genuine cyclic hull order to the exact vertex
subtype used by the shortest-distance graph.  The local orthogonal frame is
constructed from a strictly exposing functional at each hull vertex.  The
stronger angle-bisector alignment used by locality is deliberately a
separate structure.
-/

open Set
open scoped EuclideanGeometry RealInnerProductSpace BigOperators

noncomputable section

namespace Erdos957HullGeometryBridge

open Erdos957
open Erdos957TurnSum
open Erdos957TurnSum.HullOrderBridge
open Erdos957GeometryCore
open Erdos957StrictFrame

abbrev Point := Erdos957.Point
abbrev Vertex (A : Finset Point) := Erdos957GeometryCore.Vertex A

/-- Convex-hull vertices lifted to the ambient finite vertex subtype. -/
def liftedHullVertices (A : Finset Point) : Finset (Vertex A) := by
  classical
  exact A.attach.filter fun x ↦ (x : Point) ∈ hullVertices A

@[simp] theorem mem_liftedHullVertices {A : Finset Point} {x : Vertex A} :
    x ∈ liftedHullVertices A ↔ (x : Point) ∈ hullVertices A := by
  simp [liftedHullVertices]

theorem liftedHullVertices_hull_exact (A : Finset Point) (x : Vertex A) :
    x ∈ liftedHullVertices A ↔
      (x : Point) ∈ (convexHull ℝ (A : Set Point)).extremePoints ℝ := by
  rw [mem_liftedHullVertices, mem_hullVertices]

/-- The cyclic hull enumeration, with its proof of membership in `A`, is an
equivalence onto the exactly lifted hull finset. -/
noncomputable def indexEquivLiftedHull {A : Finset Point}
    (P : CyclicHullOrder A) :
    Fin (hullVertexCount A) ≃ {p // p ∈ liftedHullVertices A} := by
  let f : Fin (hullVertexCount A) → {p // p ∈ liftedHullVertices A} :=
    fun i ↦ ⟨⟨P.vertex i, P.vertex_mem i⟩,
      mem_liftedHullVertices.mpr (P.vertex_mem_hullVertices i)⟩
  apply Equiv.ofBijective f
  constructor
  · intro i j hij
    exact P.vertex.injective (congrArg (fun x ↦ ((x.1 : Vertex A) : Point)) hij)
  · rintro ⟨⟨x, hxA⟩, hxH⟩
    obtain ⟨i, hi, -⟩ := P.existsUnique_vertex_eq (mem_liftedHullVertices.mp hxH)
    refine ⟨i, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    exact hi

@[simp] theorem indexEquivLiftedHull_point {A : Finset Point}
    (P : CyclicHullOrder A) (i : Fin (hullVertexCount A)) :
    (((indexEquivLiftedHull P i).1 : Vertex A) : Point) = P.vertex i := rfl

/-- The cyclic successor transported from `Fin` to the exact lifted hull. -/
noncomputable def hullNext {A : Finset Point} (P : CyclicHullOrder A) :
    Equiv.Perm {p // p ∈ liftedHullVertices A} :=
  (indexEquivLiftedHull P).symm |>.trans
    ((finRotate (hullVertexCount A)).trans (indexEquivLiftedHull P))

@[simp] theorem hullNext_indexEquiv {A : Finset Point}
    (P : CyclicHullOrder A) (i : Fin (hullVertexCount A)) :
    hullNext P (indexEquivLiftedHull P i) =
      indexEquivLiftedHull P (finRotate (hullVertexCount A) i) := by
  simp [hullNext]

@[simp] theorem hullNext_symm_indexEquiv {A : Finset Point}
    (P : CyclicHullOrder A) (hpos : 0 < hullVertexCount A)
    (i : Fin (hullVertexCount A)) :
    (hullNext P).symm (indexEquivLiftedHull P i) =
      indexEquivLiftedHull P ((finRotate (hullVertexCount A)).symm i) := by
  let : NeZero (hullVertexCount A) := ⟨hpos.ne'⟩
  apply (hullNext P).injective
  simp

theorem card_liftedHullVertices {A : Finset Point} (P : CyclicHullOrder A) :
    (liftedHullVertices A).card = hullVertexCount A := by
  classical
  rw [← Fintype.card_coe]
  simpa using Fintype.card_congr (indexEquivLiftedHull P).symm

theorem hullNext_pow_indexEquiv {A : Finset Point} (P : CyclicHullOrder A)
    (k : ℕ) (i : Fin (hullVertexCount A)) :
    (hullNext P ^ k) (indexEquivLiftedHull P i) =
      indexEquivLiftedHull P ((finRotate (hullVertexCount A) ^ k) i) := by
  induction k generalizing i with
  | zero => simp
  | succ k ih =>
      rw [pow_succ, Equiv.Perm.mul_apply, hullNext_indexEquiv, ih]
      rw [pow_succ, Equiv.Perm.mul_apply]

/-- The transported successor has one orbit containing every lifted hull
vertex. -/
theorem hullNext_is_cyclic {A : Finset Point} (P : CyclicHullOrder A)
    (hthree : 3 ≤ hullVertexCount A) :
    ∀ i j, ∃ k < (liftedHullVertices A).card, (hullNext P ^ k) i = j := by
  let : NeZero (hullVertexCount A) := ⟨by omega⟩
  intro i j
  let e := indexEquivLiftedHull P
  let ii : Fin (hullVertexCount A) := e.symm i
  let jj : Fin (hullVertexCount A) := e.symm j
  let kfin : Fin (hullVertexCount A) := jj - ii
  refine ⟨kfin.1, ?_, ?_⟩
  · rw [card_liftedHullVertices P]
    exact kfin.isLt
  · have hrot : (finRotate (hullVertexCount A) ^ kfin.1) ii = jj := by
      rw [← Equiv.Perm.iterate_eq_pow, ← finCycle_eq_finRotate_iterate]
      change ii + (jj - ii) = jj
      simpa [add_comm] using sub_add_cancel jj ii
    have hi : i = e ii := by simp [ii, e]
    have hj : j = e jj := by simp [jj, e]
    rw [hi, hj, hullNext_pow_indexEquiv, hrot]

/-- Every point of `A` lies weakly to the left of each oriented cyclic hull
edge.  The strict turn fixes which of the two possible orientations of the
supporting line is the left side. -/
theorem cyclic_edge_cross_nonneg {A : Finset Point} (P : CyclicHullOrder A)
    (i : Fin (hullVertexCount A)) {x : Point} (hx : x ∈ A) :
    0 ≤ crossVec
      (P.vertex (finRotate (hullVertexCount A) i) - P.vertex i)
      (x - P.vertex i) := by
  let j := finRotate (hullVertexCount A) i
  let k := finRotate (hullVertexCount A) j
  obtain ⟨hab, l, hl, hlab, hmax, hstrict⟩ := P.edge_support i
  let u := P.vertex j - P.vertex i
  let v := P.vertex k - P.vertex i
  let w := x - P.vertex i
  have hlu : l u = 0 := by
    dsimp only [u, j]
    rw [map_sub, sub_eq_zero]
    exact hlab.symm
  have hturn : 0 < crossVec u v := by
    simpa [u, v, j, k, orientedTurn_eq_crossVec] using P.strict_turn i
  have hki : P.vertex k ≠ P.vertex i := by
    intro hki
    have := hturn
    have hv : v = 0 := by simp [v, hki]
    rw [hv] at this
    simp [crossVec] at this
  have hkj : P.vertex k ≠ P.vertex j := by
    intro hkj
    have := hturn
    have hv : v = u := by simp [v, u, hkj]
    rw [hv, crossVec] at this
    nlinarith
  have hlv : l v < 0 := by
    dsimp only [v]
    rw [map_sub]
    exact sub_neg.mpr (hstrict (P.vertex k) (P.vertex_mem_hullVertices k)
      hki hkj)
  have hcoef : 0 <
      l (planeBasisVector 0) ^ 2 + l (planeBasisVector 1) ^ 2 :=
    support_coefficient_sq_pos hl
  have hquarter : 0 < quarterTurnFunctional l u := by
    have hdet := support_turn_coordinate_det l u v
    rw [hlu, zero_mul, zero_sub] at hdet
    nlinarith
  have hlw : l w ≤ 0 := by
    dsimp only [w]
    rw [map_sub]
    exact sub_nonpos.mpr (hmax x hx)
  have hdetw := support_turn_coordinate_det l u w
  rw [hlu, zero_mul, zero_sub] at hdetw
  nlinarith

/-- Ambient form of the oriented supporting-half-plane field required by
`CyclicHullData`. -/
theorem hullNext_edge_support {A : Finset Point} (P : CyclicHullOrder A)
    (i : {p // p ∈ liftedHullVertices A}) (q : Vertex A) :
    0 ≤ Erdos957GeometryCore.cross
      (((hullNext P i).1.1 : Point) - (i.1.1 : Point))
      ((q : Point) - (i.1.1 : Point)) := by
  let e := indexEquivLiftedHull P
  let a : Fin (hullVertexCount A) := e.symm i
  have hi : i = e a := by simp [a, e]
  rw [hi]
  simpa [e, Erdos957GeometryCore.cross, crossVec] using
    cyclic_edge_cross_nonneg P a q.property

/-- A strictly exposing functional chosen at a transported hull index. -/
noncomputable def hullExposingFunctional {A : Finset Point}
    (P : CyclicHullOrder A) (i : {p // p ∈ liftedHullVertices A}) :
    Point →L[ℝ] ℝ :=
  Classical.choose (hullVertex_exists_strict_support A
    (mem_liftedHullVertices.mp i.property))

theorem hullExposingFunctional_spec {A : Finset Point}
    (P : CyclicHullOrder A) (i : {p // p ∈ liftedHullVertices A}) :
    (∀ y ∈ A, hullExposingFunctional P i y ≤ hullExposingFunctional P i i.1.1) ∧
    (∀ y ∈ A, y ≠ i.1.1 →
      hullExposingFunctional P i y < hullExposingFunctional P i i.1.1) :=
  Classical.choose_spec (hullVertex_exists_strict_support A
    (mem_liftedHullVertices.mp i.property))

theorem hullNext_ne {A : Finset Point} (P : CyclicHullOrder A)
    (i : {p // p ∈ liftedHullVertices A}) :
    (hullNext P i).1 ≠ i.1 := by
  let e := indexEquivLiftedHull P
  let a : Fin (hullVertexCount A) := e.symm i
  have hi : i = e a := by simp [a, e]
  rw [hi]
  intro h
  have hp := congrArg (fun z : Vertex A ↦ (z : Point)) h
  have hp' : P.vertex (finRotate (hullVertexCount A) a) = P.vertex a := by
    simpa [e] using hp
  exact P.consecutive_ne a hp'.symm

theorem hullExposingFunctional_ne_zero {A : Finset Point}
    (P : CyclicHullOrder A) (i : {p // p ∈ liftedHullVertices A}) :
    hullExposingFunctional P i ≠ 0 := by
  intro hzero
  have hlt := (hullExposingFunctional_spec P i).2
    ((hullNext P i).1 : Point) (hullNext P i).1.property
    (fun h ↦ hullNext_ne P i (Subtype.ext h))
  rw [hzero] at hlt
  simp at hlt

/-- The strict exposing orthogonal frame at a transported hull vertex. -/
noncomputable def hullFrame {A : Finset Point} (P : CyclicHullOrder A)
    (i : {p // p ∈ liftedHullVertices A}) : Point ≃ₗᵢ[ℝ] Point :=
  supportFrame (hullExposingFunctional P i)
    (hullExposingFunctional_ne_zero P i)

theorem hullFrame_strict_support {A : Finset Point} (P : CyclicHullOrder A)
    (i : {p // p ∈ liftedHullVertices A}) (q : Vertex A) (hq : q ≠ i.1) :
    0 < hullFrame P i ((q : Point) - (i.1 : Point)) 1 := by
  apply supportFrame_apply_one_pos
  rw [map_sub]
  exact sub_neg.mpr ((hullExposingFunctional_spec P i).2 q q.property
    (fun h ↦ hq (Subtype.ext h)))

/-- Exterior turn transported to the lifted hull-index type. -/
noncomputable def hullTurn {A : Finset Point} (P : CyclicHullOrder A)
    (i : {p // p ∈ liftedHullVertices A}) : ℝ :=
  exteriorTurn P ((indexEquivLiftedHull P).symm i)

@[simp] theorem hullTurn_indexEquiv {A : Finset Point}
    (P : CyclicHullOrder A) (i : Fin (hullVertexCount A)) :
    hullTurn P (indexEquivLiftedHull P i) = exteriorTurn P i := by
  simp [hullTurn]

theorem hullTurn_nonneg {A : Finset Point} {P : CyclicHullOrder A}
    (L : LiftedCyclicHullOrder P)
    (i : {p // p ∈ liftedHullVertices A}) :
    0 ≤ hullTurn P i := by
  exact L.exteriorTurn_nonneg ((indexEquivLiftedHull P).symm i)

theorem hullTurn_eq {A : Finset Point} {P : CyclicHullOrder A}
    (L : LiftedCyclicHullOrder P)
    (i : {p // p ∈ liftedHullVertices A}) :
    hullTurn P i = Real.pi - InnerProductGeometry.angle
      ((((hullNext P)⁻¹ i).1.1 : Point) - (i.1.1 : Point))
      (((hullNext P i).1.1 : Point) - (i.1.1 : Point)) := by
  let e := indexEquivLiftedHull P
  let a : Fin (hullVertexCount A) := e.symm i
  have hi : i = e a := by simp [a, e]
  rw [hi]
  change hullTurn P (e a) = Real.pi - InnerProductGeometry.angle
    (((hullNext P).symm (e a)).1.1 - (e a).1.1)
    (((hullNext P (e a)).1.1 : Point) - (e a).1.1)
  have hthree : 3 ≤ hullVertexCount A := L.hull_has_three
  have hpos : 0 < hullVertexCount A := by omega
  rw [hullNext_symm_indexEquiv P hpos, hullNext_indexEquiv]
  simp [hullTurn, e, exteriorTurn]

theorem hullTurn_sum {A : Finset Point} {P : CyclicHullOrder A}
    (L : LiftedCyclicHullOrder P) :
    ∑ i : {p // p ∈ liftedHullVertices A}, hullTurn P i = 2 * Real.pi := by
  let e := indexEquivLiftedHull P
  calc
    ∑ i : {p // p ∈ liftedHullVertices A}, hullTurn P i =
        ∑ a : Fin (hullVertexCount A), hullTurn P (e a) :=
      (Equiv.sum_comp e (hullTurn P)).symm
    _ = ∑ a : Fin (hullVertexCount A), exteriorTurn P a := by
      apply Finset.sum_congr rfl
      intro a _
      simp [hullTurn, e]
    _ = 2 * Real.pi := L.exteriorTurn_sum

/-- A genuine cyclic hull order with an honest once-around direction lift
produces every field of the charging geometry interface. -/
noncomputable def cyclicHullDataOfOrder {A : Finset Point}
    (P : CyclicHullOrder A) (L : LiftedCyclicHullOrder P) :
    CyclicHullData A where
  H := liftedHullVertices A
  hull_exact := liftedHullVertices_hull_exact A
  next := hullNext P
  next_is_cyclic := hullNext_is_cyclic P L.hull_has_three
  edge_support := hullNext_edge_support P
  frame := hullFrame P
  strict_support := hullFrame_strict_support P
  turn := hullTurn P
  turn_nonneg := hullTurn_nonneg L
  turn_eq := hullTurn_eq L
  turn_sum := hullTurn_sum L

@[simp] theorem cyclicHullDataOfOrder_H {A : Finset Point}
    (P : CyclicHullOrder A) (L : LiftedCyclicHullOrder P) :
    (cyclicHullDataOfOrder P L).H = liftedHullVertices A := rfl

@[simp] theorem cyclicHullDataOfOrder_next {A : Finset Point}
    (P : CyclicHullOrder A) (L : LiftedCyclicHullOrder P) :
    (cyclicHullDataOfOrder P L).next = hullNext P := rfl

@[simp] theorem cyclicHullDataOfOrder_turn_indexEquiv {A : Finset Point}
    (P : CyclicHullOrder A) (L : LiftedCyclicHullOrder P)
    (i : Fin (hullVertexCount A)) :
    (cyclicHullDataOfOrder P L).turn (indexEquivLiftedHull P i) =
      exteriorTurn P i := by
  exact hullTurn_indexEquiv P i

/-- In the transported hull record, the turn at the successor of index `i`
is exactly the corresponding increment of the once-around direction lift. -/
theorem cyclicHullDataOfOrder_turn_successor_indexEquiv {A : Finset Point}
    (P : CyclicHullOrder A) (L : LiftedCyclicHullOrder P)
    (i : Fin (hullVertexCount A)) :
    (cyclicHullDataOfOrder P L).turn
        (indexEquivLiftedHull P (finRotate (hullVertexCount A) i)) =
      L.lift.turn i := by
  rw [cyclicHullDataOfOrder_turn_indexEquiv]
  exact (L.lift_turn_eq_exteriorTurn_finRotate i).symm

/-- Every finite planar configuration with at least three convex-hull
vertices has the complete cyclic hull geometry interface. -/
theorem nonempty_cyclicHullData (A : Finset Point)
    (hthree : 3 ≤ hullVertexCount A) :
    Nonempty (CyclicHullData A) := by
  obtain ⟨P, ⟨L⟩⟩ := Erdos957HullAngleLift.exists_liftedCyclicHullOrder A hthree
  exact ⟨cyclicHullDataOfOrder P L⟩

end Erdos957HullGeometryBridge
