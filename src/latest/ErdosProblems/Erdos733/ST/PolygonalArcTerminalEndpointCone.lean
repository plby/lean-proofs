import Mathlib.Tactic
import ErdosProblems.Erdos733.ST.PlanarRot90
import ErdosProblems.Erdos733.ST.PolygonalArc

open Classical
noncomputable section

-- [TABLET NODE: PolygonalArcTerminalEndpointCone]
def PolygonalArcTerminalEndpointCone (γ : PolygonalArc) (r K : ℝ) :
    Set (EuclideanSpace ℝ (Fin 2)) :=
-- BODY
  let hprev : γ.vertices.length - 2 < γ.vertices.length := by
    have hlen := γ.length_ge_two
    omega
  let p0 : EuclideanSpace ℝ (Fin 2) := γ.target
  let p1 : EuclideanSpace ℝ (Fin 2) := γ.vertices[γ.vertices.length - 2]'hprev
  let d : EuclideanSpace ℝ (Fin 2) := p1 - p0
  let chart : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2) :=
    fun z => p0 + z 0 • d + z 1 • PlanarRot90 d
  let a : ℝ := r / dist p0 p1
  chart ''
    {z | 0 < z 0 ∧ z 0 ^ 2 + z 1 ^ 2 < a ^ 2 ∧ -K * z 0 < z 1 ∧
      z 1 < K * z 0}
