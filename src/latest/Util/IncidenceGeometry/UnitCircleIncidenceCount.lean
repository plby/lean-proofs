import Util.IncidenceGeometry.UnitCircle

open Classical
noncomputable section

noncomputable def UnitCircleIncidenceCount (P : Finset (EuclideanSpace ℝ (Fin 2))) : ℕ :=
  ((P.product P).filter (fun pq => pq.2 ∈ UnitCircle pq.1)).card
