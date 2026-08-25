import Util.IncidenceGeometry.Basic

open Classical
noncomputable section

noncomputable def IncidenceGeometry.unitDistanceCount (P : Finset (EuclideanSpace ℝ (Fin 2))) : ℕ :=
  (P.offDiag.filter (fun pq => dist pq.1 pq.2 = 1)).card / 2
