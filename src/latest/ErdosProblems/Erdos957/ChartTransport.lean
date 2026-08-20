import ErdosProblems.Erdos957.BisectorFrame
import ErdosProblems.Erdos957.EdgeFrame

/-!
# Small-angle transport between the charts used for Erdős 957

This module isolates the elementary analytic estimate which permits a
unit-edge chart to replace the tangent-bisector chart at a two-extreme
source.  Both charts are represented by `anglePairCoord`; only the direction
of the horizontal axis changes.
-/

open scoped RealInnerProductSpace

noncomputable section

namespace Erdos957ChartTransport

open Erdos957
open Erdos957BisectorFrame
open Erdos957EdgeFrame
open Erdos957TurnSum

abbrev Point := Erdos957.Point

/-- A deliberately coarse rational estimate for a one-degree rotation. -/
theorem two_mul_abs_sin_le_three_twentieth {φ : ℝ}
    (hφ : |φ| ≤ Real.pi / 180) :
    2 * |Real.sin φ| ≤ (3 : ℝ) / 20 := by
  have hsmall : |φ| ≤ (1 : ℝ) / 45 := by
    calc
      |φ| ≤ Real.pi / 180 := hφ
      _ ≤ (1 : ℝ) / 45 := by nlinarith [Real.pi_le_four]
  have hsin : |Real.sin φ| ≤ |φ| := Real.abs_sin_le_abs
  nlinarith [abs_nonneg (Real.sin φ)]

/-- Changing the axis angle from `θ` to `ψ` rotates pair coordinates by
`ψ - θ`. -/
theorem anglePairCoord_fst_change (θ ψ : ℝ) (o q : Point) :
    (anglePairCoord ψ o q).1 =
      Real.cos (ψ - θ) * (anglePairCoord θ o q).1 -
        Real.sin (ψ - θ) * (anglePairCoord θ o q).2 := by
  simp only [anglePairCoord, Prod.fst, Prod.snd]
  rw [Real.cos_sub, Real.sin_sub]
  have hθ : Real.cos θ ^ 2 + Real.sin θ ^ 2 = 1 := by
    nlinarith [Real.sin_sq_add_cos_sq θ]
  calc
    Real.cos ψ * (q - o) 0 + Real.sin ψ * (q - o) 1 =
        (Real.cos θ ^ 2 + Real.sin θ ^ 2) *
          (Real.cos ψ * (q - o) 0 + Real.sin ψ * (q - o) 1) := by
            rw [hθ]
            ring
    _ = _ := by ring

/-- Each component in an angle chart is bounded by the ambient distance from
the chart source. -/
theorem abs_anglePairCoord_snd_le_dist (θ : ℝ) (o q : Point) :
    |(anglePairCoord θ o q).2| ≤ dist o q := by
  have hsquare := sqDist_anglePairCoord θ o q o
  rw [anglePairCoord_self] at hsquare
  simp only [Erdos957Cases13.sqDist, sub_zero, Prod.fst, Prod.snd] at hsquare
  rw [dist_comm q o] at hsquare
  have hdist : 0 ≤ dist o q := dist_nonneg
  have habs : 0 ≤ |(anglePairCoord θ o q).2| := abs_nonneg _
  nlinarith [sq_nonneg (anglePairCoord θ o q).1,
    sq_abs (anglePairCoord θ o q).2]

/-- The first coordinate changes by at most `dist o q * |sin (ψ-θ)|`.
The unused cosine term can only contract the old first coordinate. -/
theorem abs_anglePairCoord_fst_le_add_sin (θ ψ : ℝ) (o q : Point) :
    |(anglePairCoord ψ o q).1| ≤
      |(anglePairCoord θ o q).1| +
        dist o q * |Real.sin (ψ - θ)| := by
  rw [anglePairCoord_fst_change θ ψ o q]
  calc
    |Real.cos (ψ - θ) * (anglePairCoord θ o q).1 -
        Real.sin (ψ - θ) * (anglePairCoord θ o q).2| ≤
        |Real.cos (ψ - θ) * (anglePairCoord θ o q).1| +
          |Real.sin (ψ - θ) * (anglePairCoord θ o q).2| := abs_sub _ _
    _ = |Real.cos (ψ - θ)| * |(anglePairCoord θ o q).1| +
          |Real.sin (ψ - θ)| * |(anglePairCoord θ o q).2| := by
          rw [abs_mul, abs_mul]
    _ ≤ 1 * |(anglePairCoord θ o q).1| +
          |Real.sin (ψ - θ)| * dist o q := by
          gcongr
          · exact Real.abs_cos_le_one _
          · exact abs_anglePairCoord_snd_le_dist θ o q
    _ = |(anglePairCoord θ o q).1| +
          dist o q * |Real.sin (ψ - θ)| := by ring

/-- The chart-transport bound used by the two-extreme cases of the proof.
An edge-chart horizontal bound `3/2` remains below `7/4` in a bisector chart
whose axis differs by at most one degree, for targets at distance at most two.
-/
theorem abs_anglePairCoord_fst_le_seven_four
    (θEdge θBis : ℝ) (o q : Point)
    (hangle : |θBis - θEdge| ≤ Real.pi / 180)
    (hradius : dist o q ≤ 2)
    (hedge : |(anglePairCoord θEdge o q).1| ≤ (3 : ℝ) / 2) :
    |(anglePairCoord θBis o q).1| ≤ (7 : ℝ) / 4 := by
  have hsin : 2 * |Real.sin (θBis - θEdge)| ≤ (3 : ℝ) / 20 :=
    two_mul_abs_sin_le_three_twentieth hangle
  have hsin_nonneg : 0 ≤ |Real.sin (θBis - θEdge)| := abs_nonneg _
  have hdist_nonneg : 0 ≤ dist o q := dist_nonneg
  have hperturb : dist o q * |Real.sin (θBis - θEdge)| ≤ (3 : ℝ) / 20 := by
    calc
      dist o q * |Real.sin (θBis - θEdge)| ≤
          2 * |Real.sin (θBis - θEdge)| := by gcongr
      _ ≤ (3 : ℝ) / 20 := hsin
  have htransport := abs_anglePairCoord_fst_le_add_sin θEdge θBis o q
  nlinarith

/-- A unit-direction edge chart is definitionally the corresponding
`anglePairCoord`.  This is the adapter from `successorCoord`/`edgePairCoord`
to the angle-based transport estimate above. -/
theorem edgePairCoord_unitDirection (θ : ℝ) (o q : Point) :
    edgePairCoord o (unitDirection θ) q = anglePairCoord θ o q := by
  apply Prod.ext <;>
    simp [edgePairCoord, anglePairCoord, unitDirection]

/-- Adapter-friendly form: the old chart may be presented as an edge chart
whose edge vector is certified to have unwrapped direction `θEdge`. -/
theorem abs_anglePairCoord_fst_le_seven_four_of_edgePairCoord
    (θEdge θBis : ℝ) (o e q : Point)
    (hedirection : e = unitDirection θEdge)
    (hangle : |θBis - θEdge| ≤ Real.pi / 180)
    (hradius : dist o q ≤ 2)
    (hedge : |(edgePairCoord o e q).1| ≤ (3 : ℝ) / 2) :
    |(anglePairCoord θBis o q).1| ≤ (7 : ℝ) / 4 := by
  subst e
  rw [edgePairCoord_unitDirection] at hedge
  exact abs_anglePairCoord_fst_le_seven_four
    θEdge θBis o q hangle hradius hedge

/-! ## Wrappers for the production bisector chart -/

variable {A : Finset Point} {P : CyclicHullOrder A}

/-- Direct wrapper for a genuine hull source before transport to
`CyclicHullData`. -/
theorem abs_bisectorCoord_fst_le_seven_four_of_edgePairCoord
    (L : Erdos957TurnSum.HullOrderBridge.LiftedCyclicHullOrder P)
    (i : Fin (hullVertexCount A)) (q e : Point) (θEdge : ℝ)
    (hedirection : e = unitDirection θEdge)
    (hangle : |bisectorAngle L i - θEdge| ≤ Real.pi / 180)
    (hradius : dist (P.vertex i) q ≤ 2)
    (hedge : |(edgePairCoord (P.vertex i) e q).1| ≤ (3 : ℝ) / 2) :
    |(bisectorCoord L i q).1| ≤ (7 : ℝ) / 4 := by
  exact abs_anglePairCoord_fst_le_seven_four_of_edgePairCoord
    θEdge (bisectorAngle L i) (P.vertex i) e q
    hedirection hangle hradius hedge

/-- Adapter whose conclusion is stated literally in the aligned-chart API
used by `LocalTarget.ofPath`. -/
theorem abs_bisectorAlignedChartData_coord_fst_le_seven_four_of_edgePairCoord
    (L : Erdos957TurnSum.HullOrderBridge.LiftedCyclicHullOrder P)
    (i : {p // p ∈
      (Erdos957HullGeometryBridge.cyclicHullDataOfOrder P L).H})
    (q : Erdos957GeometryCore.Vertex A) (e : Point) (θEdge : ℝ)
    (hedirection : e = unitDirection θEdge)
    (hangle :
      |bisectorAngle L
          ((Erdos957HullGeometryBridge.indexEquivLiftedHull P).symm i) -
        θEdge| ≤ Real.pi / 180)
    (hradius :
      dist (P.vertex
          ((Erdos957HullGeometryBridge.indexEquivLiftedHull P).symm i))
        (q : Point) ≤ 2)
    (hedge :
      |(edgePairCoord
          (P.vertex
            ((Erdos957HullGeometryBridge.indexEquivLiftedHull P).symm i))
          e (q : Point)).1| ≤ (3 : ℝ) / 2) :
    |((bisectorAlignedChartData P L).coord i q).1| ≤ (7 : ℝ) / 4 := by
  change |(bisectorCoord L
    ((Erdos957HullGeometryBridge.indexEquivLiftedHull P).symm i)
    (q : Point)).1| ≤ (7 : ℝ) / 4
  exact abs_bisectorCoord_fst_le_seven_four_of_edgePairCoord
    L _ (q : Point) e θEdge hedirection hangle hradius hedge

end Erdos957ChartTransport
