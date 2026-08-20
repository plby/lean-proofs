import ErdosProblems.Erdos957.CollisionGlue
import ErdosProblems.Erdos957.BisectorPolar
import ErdosProblems.Erdos957.WindowIndex

open scoped RealInnerProductSpace

noncomputable section

namespace Erdos957CyclicWindowConstructor

open Erdos957
open Erdos957GeometryCore
open Erdos957GeometryLocalRows
open Erdos957GeometryLocalityBridge
open Erdos957HullGeometryBridge
open Erdos957BisectorFrame
open Erdos957BisectorPolar
open Erdos957TurnSum.HullOrderBridge
open Erdos957WindowIndex

lemma ofNat_eq_nsmul_one {n : ℕ} [NeZero n] (m : ℕ) :
    Fin.ofNat n m = m • (1 : Fin n) := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [succ_nsmul, ← ih]
      apply Fin.ext
      simp [Fin.ofNat, Fin.add_def, Nat.add_mod]

lemma finRotate_pow_four {n : ℕ} [NeZero n] (a : Fin n) :
    (finRotate n ^ 4) a = a + Fin.ofNat n 4 := by
  rw [ofNat_eq_nsmul_one]
  simp [pow_succ, Equiv.Perm.mul_apply, finRotate_apply]
  abel

lemma finRotate_symm_pow_four {n : ℕ} [NeZero n] (a : Fin n) :
    ((finRotate n)⁻¹ ^ 4) a = a - Fin.ofNat n 4 := by
  rw [ofNat_eq_nsmul_one]
  simp [pow_succ, Equiv.Perm.mul_apply, finRotate_symm_apply]
  abel

lemma exterior_of_orientedTurn_nonpos
    {A : Finset Erdos957.Point} {P : CyclicHullData A}
    (C : P.AlignedChartData) (i : {p // p ∈ P.H})
    (p q z : Erdos957GeometryCore.Vertex A)
    (h : Erdos957.orientedTurn
      (p : Erdos957.Point) (q : Erdos957.Point) (z : Erdos957.Point) ≤ 0) :
    Erdos957Locality.ExteriorOfRightChord
      (C.coord i p) (C.coord i q) (C.coord i z) := by
  have hc := C.cross_displacements i p q z
  rw [Erdos957.orientedTurn_eq_crossVec] at h
  simp only [Erdos957Locality.ExteriorOfRightChord, Erdos957Locality.cross,
    CyclicHullData.pairCross, CyclicHullData.pairSub] at hc ⊢
  have heq : Erdos957.crossVec
      ((q : Erdos957.Point) - p) ((z : Erdos957.Point) - p) =
      Erdos957GeometryCore.cross ((q : Erdos957.Point) - p)
        ((z : Erdos957.Point) - p) := rfl
  rw [heq] at h
  linarith

lemma reflected_exterior_of_orientedTurn_nonneg
    {A : Finset Erdos957.Point} {P : CyclicHullData A}
    (C : P.AlignedChartData) (i : {p // p ∈ P.H})
    (p q z : Erdos957GeometryCore.Vertex A)
    (h : 0 ≤ Erdos957.orientedTurn
      (p : Erdos957.Point) (q : Erdos957.Point) (z : Erdos957.Point)) :
    let pc := C.coord i p
    let qc := C.coord i q
    let zc := C.coord i z
    Erdos957Locality.ExteriorOfRightChord
      (-pc.1, pc.2) (-qc.1, qc.2) (-zc.1, zc.2) := by
  have hc := C.cross_displacements i p q z
  rw [Erdos957.orientedTurn_eq_crossVec] at h
  simp only [Erdos957Locality.ExteriorOfRightChord, Erdos957Locality.cross,
    CyclicHullData.pairCross, CyclicHullData.pairSub] at hc ⊢
  have heq : Erdos957.crossVec
      ((q : Erdos957.Point) - p) ((z : Erdos957.Point) - p) =
      Erdos957GeometryCore.cross ((q : Erdos957.Point) - p)
        ((z : Erdos957.Point) - p) := rfl
  rw [heq] at h
  linarith

lemma sevenShift_indexEquiv
    {A : Finset Erdos957.Point} (O : CyclicHullOrder A)
    (j : Fin 7) (a : Fin (hullVertexCount A)) :
    indexEquivLiftedHull O (sevenShift (finRotate (hullVertexCount A)) j a) =
      sevenShift (hullNext O) j (indexEquivLiftedHull O a) := by
  have hpos : 0 < hullVertexCount A := Fin.pos a
  fin_cases j <;>
    simp [sevenShift, hullNext_indexEquiv, hullNext_symm_indexEquiv, hpos,
      pow_succ, Equiv.Perm.mul_apply]

/-- The actual radial hull order, its genuine bisector chart, and convex
closed-arc signs construct all cyclic-window geometry required by locality. -/
noncomputable def cyclicWindowGeometry
    {A : Finset Erdos957.Point} (hA : IsOneSeparated A)
    (R : RadiallySortedCyclicHullOrder A)
    (L : LiftedCyclicHullOrder R.order)
    (W : DiameterWitnessData (cyclicHullDataOfOrder R.order L)) :
    CyclicWindowGeometry W
      (bisectorFlatAlignedFrameData R.order L hA) where
  outside_window_arc s z hzHull hzWindow := by
    let P := cyclicHullDataOfOrder R.order L
    let F := bisectorFlatAlignedFrameData R.order L hA
    let i := sourceIndex P W s.1 s.property
    let e := indexEquivLiftedHull R.order
    let a := e.symm i
    letI : NeZero (hullVertexCount A) := ⟨(Fin.pos a).ne'⟩
    let zi : {p // p ∈ P.H} := ⟨z, hzHull⟩
    let b := e.symm zi
    let qv := W.opposite s.1 (source_mem_diameter W s)
    let qi := W.oppositeIndex s.1 (source_mem_diameter W s)
    let c := e.symm qi
    have hi : e a = i := e.apply_symm_apply i
    have hzidx : e b = zi := e.apply_symm_apply zi
    have hqidx : e c = qi := e.apply_symm_apply qi
    have hzout : ∀ j : Fin 7,
        b ≠ sevenShift (finRotate (hullVertexCount A)) j a := by
      intro j hb
      apply hzWindow
      apply Finset.mem_image.mpr
      refine ⟨j, Finset.mem_univ _, ?_⟩
      have hsub : zi = sevenShift P.next j i := by
        change zi = sevenShift (hullNext R.order) j i
        rw [← hi, ← sevenShift_indexEquiv R.order j a, ← hb]
        exact hzidx.symm
      exact (congrArg Subtype.val hsub).symm
    have harc := Erdos957WindowIndex.outside_sevenShift_arc_partition_any_q
      a c b hzout
    let rightIndex := a + Fin.ofNat (hullVertexCount A) 4
    let leftIndex := a - Fin.ofNat (hullVertexCount A) 4
    let prv : Erdos957GeometryCore.Vertex A := (e rightIndex).1
    let plv : Erdos957GeometryCore.Vertex A := (e leftIndex).1
    have hrightHull : (P.next ^ 4) i = e rightIndex := by
      dsimp only [P, cyclicHullDataOfOrder_next]
      rw [← hi]
      calc
        (hullNext R.order ^ 4) (e a) =
            e ((finRotate (hullVertexCount A) ^ 4) a) := by
          simpa [e] using hullNext_pow_indexEquiv R.order 4 a
        _ = e rightIndex := by
          apply congrArg e
          exact Fin.ext (congrArg Fin.val (finRotate_pow_four a))
    have hleftHull : ((P.next⁻¹) ^ 4) i = e leftIndex := by
      dsimp only [P, cyclicHullDataOfOrder_next]
      rw [← hi]
      calc
        ((hullNext R.order).symm ^ 4) (e a) =
            e (backwardVertexIndex a 4) := by
          simpa [e] using hullNext_symm_pow_indexEquiv L a 4
        _ = e leftIndex := by
          apply congrArg e
          rw [backwardVertexIndex_eq_pow]
          exact Fin.ext (congrArg Fin.val (finRotate_symm_pow_four a))
    have hprCoord : F.chart.rightOrbitCoord P i 4 = F.chart.coord i prv := by
      change F.chart.coord i ((P.next ^ 4) i).1 = F.chart.coord i prv
      rw [hrightHull]
    have hplCoord : F.chart.leftOrbitReflectedCoord P i 4 =
        let pc := F.chart.coord i plv; (-pc.1, pc.2) := by
      change (let pc := F.chart.coord i (((P.next⁻¹) ^ 4) i).1
        (-pc.1, pc.2)) = _
      rw [hleftHull]
    rcases harc with hright | hleft
    · left
      have ht := R.orientedTurn_chord_le_zero_of_mem_closedCCWArc hright
      have hprPoint : R.order.vertex rightIndex = (prv : Erdos957.Point) := by
        simpa [prv, e] using indexEquivLiftedHull_point R.order rightIndex
      have hqPoint : R.order.vertex c = (qv : Erdos957.Point) := by
        calc
          R.order.vertex c = (((e c).1 : Erdos957GeometryCore.Vertex A) :
              Erdos957.Point) := (indexEquivLiftedHull_point R.order c).symm
          _ = (qv : Erdos957.Point) := by
            exact congrArg (fun x ↦ ((x.1 : Erdos957GeometryCore.Vertex A) :
              Erdos957.Point)) hqidx
      have hzPoint : R.order.vertex b = (z : Erdos957.Point) := by
        calc
          R.order.vertex b = (((e b).1 : Erdos957GeometryCore.Vertex A) :
              Erdos957.Point) := (indexEquivLiftedHull_point R.order b).symm
          _ = (z : Erdos957.Point) := by
            simpa [zi] using congrArg (fun x ↦ ((x.1 :
              Erdos957GeometryCore.Vertex A) : Erdos957.Point)) hzidx
      have ht' : Erdos957.orientedTurn (prv : Erdos957.Point)
          (qv : Erdos957.Point) (z : Erdos957.Point) ≤ 0 := by
        have ht0 : Erdos957.orientedTurn (R.order.vertex rightIndex)
            (R.order.vertex c) (R.order.vertex b) ≤ 0 := by
          simpa [rightIndex] using ht
        rw [hprPoint, hqPoint, hzPoint] at ht0
        exact ht0
      have hex := exterior_of_orientedTurn_nonpos F.chart i prv qv z ht'
      change Erdos957Locality.ExteriorOfRightChord
        (F.chart.rightOrbitCoord P i 4) (F.chart.coord i qv) (F.chart.coord i z)
      rw [hprCoord]
      exact hex
    · right
      have ht := R.orientedTurn_chord_le_zero_of_mem_closedCCWArc hleft
      have hplPoint : R.order.vertex leftIndex = (plv : Erdos957.Point) := by
        simpa [plv, e] using indexEquivLiftedHull_point R.order leftIndex
      have hqPoint : R.order.vertex c = (qv : Erdos957.Point) := by
        calc
          R.order.vertex c = (((e c).1 : Erdos957GeometryCore.Vertex A) :
              Erdos957.Point) := (indexEquivLiftedHull_point R.order c).symm
          _ = (qv : Erdos957.Point) := by
            exact congrArg (fun x ↦ ((x.1 : Erdos957GeometryCore.Vertex A) :
              Erdos957.Point)) hqidx
      have hzPoint : R.order.vertex b = (z : Erdos957.Point) := by
        calc
          R.order.vertex b = (((e b).1 : Erdos957GeometryCore.Vertex A) :
              Erdos957.Point) := (indexEquivLiftedHull_point R.order b).symm
          _ = (z : Erdos957.Point) := by
            simpa [zi] using congrArg (fun x ↦ ((x.1 :
              Erdos957GeometryCore.Vertex A) : Erdos957.Point)) hzidx
      have ht' : 0 ≤ Erdos957.orientedTurn (plv : Erdos957.Point)
          (qv : Erdos957.Point) (z : Erdos957.Point) := by
        have ht0 : Erdos957.orientedTurn (R.order.vertex c)
            (R.order.vertex leftIndex) (R.order.vertex b) ≤ 0 := by
          simpa [leftIndex] using ht
        rw [hqPoint, hplPoint, hzPoint] at ht0
        rw [Erdos957.orientedTurn_swap_first] at ht0
        linarith
      have hex := reflected_exterior_of_orientedTurn_nonneg F.chart i plv qv z ht'
      change Erdos957Locality.ExteriorOfRightChord
        (F.chart.leftOrbitReflectedCoord P i 4)
        (-(F.chart.coord i qv).1, (F.chart.coord i qv).2)
        (-(F.chart.coord i z).1, (F.chart.coord i z).2)
      rw [hplCoord]
      exact hex

end Erdos957CyclicWindowConstructor
