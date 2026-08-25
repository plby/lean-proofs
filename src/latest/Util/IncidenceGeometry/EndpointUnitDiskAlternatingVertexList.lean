import Util.IncidenceGeometry.Basic

open Classical
noncomputable section

def EndpointUnitDiskAlternatingVertexList
    (A B : EuclideanSpace ℝ (Fin 2))
    (blocks : List (List (EuclideanSpace ℝ (Fin 2)))) :
    List (EuclideanSpace ℝ (Fin 2)) :=
  A :: (blocks.flatten ++ [B])
