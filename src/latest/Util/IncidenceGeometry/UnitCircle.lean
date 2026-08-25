import Util.IncidenceGeometry.Basic

def UnitCircle (p : EuclideanSpace ℝ (Fin 2)) : Set (EuclideanSpace ℝ (Fin 2)) :=
  {x | dist x p = 1}
