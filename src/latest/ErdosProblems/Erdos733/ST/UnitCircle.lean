import ErdosProblems.Erdos733.ST.Preamble

-- [TABLET NODE: UnitCircle]
def UnitCircle (p : EuclideanSpace ℝ (Fin 2)) : Set (EuclideanSpace ℝ (Fin 2)) :=
-- BODY
  {x | dist x p = 1}
