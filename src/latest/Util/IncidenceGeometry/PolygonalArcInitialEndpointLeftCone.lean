import Mathlib.Tactic
import Util.IncidenceGeometry.PlanarRot90
import Util.IncidenceGeometry.PolygonalArc

open Classical
noncomputable section

def PolygonalArcInitialEndpointLeftCone (γ : PolygonalArc) (r K : ℝ) :
    Set (EuclideanSpace ℝ (Fin 2)) :=
  let hfirst : 1 < γ.vertices.length := Nat.lt_of_succ_le γ.length_ge_two
  let p0 : EuclideanSpace ℝ (Fin 2) := γ.source
  let p1 : EuclideanSpace ℝ (Fin 2) := γ.vertices[1]'hfirst
  let d : EuclideanSpace ℝ (Fin 2) := p1 - p0
  let chart : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2) :=
    fun z => p0 + z 0 • d + z 1 • PlanarRot90 d
  let a : ℝ := r / dist p0 p1
  chart ''
    {z | 0 < z 0 ∧ z 0 ^ 2 + z 1 ^ 2 < a ^ 2 ∧ 0 < z 1 ∧
      z 1 < K * z 0}
