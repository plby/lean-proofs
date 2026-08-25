import Util.IncidenceGeometry.Basic

open Classical
noncomputable section

def PlanarRot90 (v : EuclideanSpace ℝ (Fin 2)) : EuclideanSpace ℝ (Fin 2) :=
  WithLp.toLp 2 (fun k : Fin 2 => if k = 0 then -(v 1) else v 0)
