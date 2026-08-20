import ErdosProblems.Erdos957.HullGeometryBridge
import ErdosProblems.Erdos957.EdgeFrame

/-!
# Strict-turn bridge for produced hull data

`CyclicHullData` retains only the nonnegative supporting-edge orientation.
The concrete hull order used by the produced Erdős 957 construction carries
the stronger strict consecutive-turn fact.  This leaf exposes that fact on
the transported hull-vertex subtype without adding it to the generic cyclic
interface.
-/

noncomputable section

namespace Erdos957ProducedStrictTurn

open Erdos957
open Erdos957GeometryCore
open Erdos957HullGeometryBridge

abbrev Point := Erdos957.Point

/-- Consecutive transported hull edges make the same strict
counterclockwise turn as their underlying `Fin`-indexed hull order. -/
theorem hullNext_strict_turn
    {A : Finset Point} (P : CyclicHullOrder A)
    (i : {p // p ∈ liftedHullVertices A}) :
    0 < cross
      (((hullNext P i).1.1 : Point) - i.1.1)
      (((hullNext P (hullNext P i)).1.1 : Point) -
        (hullNext P i).1.1) := by
  let e := indexEquivLiftedHull P
  let a : Fin (hullVertexCount A) := e.symm i
  have hi : i = e a := by simp [a, e]
  rw [hi]
  dsimp only [e]
  simp only [hullNext_indexEquiv, indexEquivLiftedHull_point]
  change 0 < orientedTurn (P.vertex a)
    (P.vertex (cyclicSucc a))
    (P.vertex (cyclicSucc (cyclicSucc a)))
  exact P.strict_turn a

/-- Re-express the canonical Case-2 `wNext` point in an arbitrary later
terminal unit-edge chart.  This is the exact affine identity used to compare
the Case-2 target height with the selected Case-4 farthest point. -/
lemma terminalCharts_wNext_snd
    (p s t o q : Point)
    (hps : dist p s = 1) (hto : dist t o = 1)
    (hq : (Erdos957EdgeFrame.terminalUnitEdgeRigidChart p s hps).toCanonical q =
      Erdos957Cases24.Case2.wNext) :
    let E := Erdos957EdgeFrame.terminalUnitEdgeRigidChart t o hto
    (E.toCanonical q) 1 =
      (E.toCanonical s) 1 +
        ((E.toCanonical s) 1 - (E.toCanonical p) 1) -
        Erdos957Cases24.sqrtThree *
          ((E.toCanonical s) 0 - (E.toCanonical p) 0) := by
  let T := Erdos957EdgeFrame.terminalUnitEdgeRigidChart p s hps
  let E := Erdos957EdgeFrame.terminalUnitEdgeRigidChart t o hto
  have hqActual : q = T.actual Erdos957Cases24.Case2.wNext := by
    apply T.toCanonical.injective
    rw [hq, T.toCanonical_actual]
  rw [hqActual]
  change
    (Erdos957EdgeFrame.edgePointCoord o (o - t)
      (Erdos957EdgeFrame.edgePointActual s (s - p)
        Erdos957Cases24.Case2.wNext)) 1 =
      (Erdos957EdgeFrame.edgePointCoord o (o - t) s) 1 +
        ((Erdos957EdgeFrame.edgePointCoord o (o - t) s) 1 -
          (Erdos957EdgeFrame.edgePointCoord o (o - t) p) 1) -
        Erdos957Cases24.sqrtThree *
          ((Erdos957EdgeFrame.edgePointCoord o (o - t) s) 0 -
            (Erdos957EdgeFrame.edgePointCoord o (o - t) p) 0)
  simp only [Erdos957EdgeFrame.edgePointCoord_apply_zero,
    Erdos957EdgeFrame.edgePointCoord_apply_one,
    Erdos957EdgeFrame.edgePointActual,
    Erdos957EdgeFrame.edgePairCoord,
    Erdos957Cases24.Case2.wNext,
    Erdos957Cases24.point_apply_zero,
    Erdos957Cases24.point_apply_one,
    PiLp.add_apply, PiLp.sub_apply]
  ring

/-- Coordinate kernel behind the final strict Case-2/Case-4 boundary.
Two positively oriented unit edge directions with a strict turn have
strictly ordered transverse components.  Consequently the canonical
`wNext` displacement, expressed in the later edge chart, lies strictly
above the lower `60°` latitude. -/
lemma wNext_snd_gt_neg_sqrtThree_of_strict_unit_turn
    {px py ex ey : ℝ}
    (hpunit : px ^ 2 + py ^ 2 = 1)
    (heunit : ex ^ 2 + ey ^ 2 = 1)
    (hpx : 0 < px) (hpy : 0 < py) (hex : 0 < ex)
    (hturn : ex * py - ey * px < 0) :
    -py + ey - Erdos957Cases24.sqrtThree * ex >
      -Erdos957Cases24.sqrtThree := by
  have hey : 0 < ey := by
    have hleft : 0 < ex * py := mul_pos hex hpy
    have hright : ex * py < ey * px := by linarith only [hturn]
    have : 0 < ey * px := hleft.trans hright
    rcases mul_pos_iff.mp this with hpos | hneg
    · exact hpos.1
    · linarith only [hpx, hneg.2]
  have heyp : py < ey := by
    by_contra h
    have heyLe : ey ≤ py := le_of_not_gt h
    have hsum : 0 ≤ ey + py := by linarith only [hey, hpy]
    have heySqLe : ey ^ 2 ≤ py ^ 2 := by
      nlinarith only [hey, hpy, heyLe,
        mul_nonneg (sub_nonneg.mpr heyLe) hsum]
    have hpxSqLe : px ^ 2 ≤ ex ^ 2 := by
      nlinarith only [hpunit, heunit, heySqLe]
    have hpxLe : px ≤ ex := by
      nlinarith only [hpx, hex, hpxSqLe,
        sq_nonneg (px + ex)]
    have h₁ : px * ey ≤ px * py :=
      mul_le_mul_of_nonneg_left heyLe hpx.le
    have h₂ : px * py ≤ ex * py :=
      mul_le_mul_of_nonneg_right hpxLe hpy.le
    linarith only [hturn, h₁, h₂]
  have hexLe : ex ≤ 1 := by
    nlinarith only [heunit, hex, sq_nonneg ey, sq_nonneg (ex - 1)]
  have hsqrt := Erdos957Cases24.sqrtThree_pos
  nlinarith only [heyp, hexLe, hsqrt]

end Erdos957ProducedStrictTurn

#print axioms Erdos957ProducedStrictTurn.hullNext_strict_turn
#print axioms Erdos957ProducedStrictTurn.terminalCharts_wNext_snd
#print axioms Erdos957ProducedStrictTurn.wNext_snd_gt_neg_sqrtThree_of_strict_unit_turn
