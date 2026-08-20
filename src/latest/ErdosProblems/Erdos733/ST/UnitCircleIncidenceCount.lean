import ErdosProblems.Erdos733.ST.UnitCircle

open Classical
noncomputable section

-- [TABLET NODE: UnitCircleIncidenceCount]
noncomputable def UnitCircleIncidenceCount (P : Finset (EuclideanSpace ℝ (Fin 2))) : ℕ :=
-- BODY
  ((P.product P).filter (fun pq => pq.2 ∈ UnitCircle pq.1)).card
