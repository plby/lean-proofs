import ErdosProblems.Erdos733.ST.Preamble

open Classical
noncomputable section

-- [TABLET NODE: unitDist]
noncomputable def unitDist (P : Finset (EuclideanSpace ℝ (Fin 2))) : ℕ :=
-- BODY
  (P.offDiag.filter (fun pq => dist pq.1 pq.2 = 1)).card / 2
