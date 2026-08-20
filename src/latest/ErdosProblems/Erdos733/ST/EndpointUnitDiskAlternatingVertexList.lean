import ErdosProblems.Erdos733.ST.Preamble

open Classical
noncomputable section

-- [TABLET NODE: EndpointUnitDiskAlternatingVertexList]
def EndpointUnitDiskAlternatingVertexList
    (A B : EuclideanSpace ℝ (Fin 2))
    (blocks : List (List (EuclideanSpace ℝ (Fin 2)))) :
    List (EuclideanSpace ℝ (Fin 2)) :=
-- BODY
  A :: (blocks.flatten ++ [B])
