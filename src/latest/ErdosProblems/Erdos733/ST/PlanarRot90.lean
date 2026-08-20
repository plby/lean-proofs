import ErdosProblems.Erdos733.ST.Preamble

open Classical
noncomputable section

-- [TABLET NODE: PlanarRot90]
def PlanarRot90 (v : EuclideanSpace ℝ (Fin 2)) : EuclideanSpace ℝ (Fin 2) :=
-- BODY
  WithLp.toLp 2 (fun k : Fin 2 => if k = 0 then -(v 1) else v 0)
