import Util.IncidenceGeometry.IsAffineLine

open Classical
noncomputable section

noncomputable def LineIncidences
    (P : Finset (EuclideanSpace ℝ (Fin 2)))
    (L : Finset {ℓ : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2)) // IsAffineLine ℓ}) : ℕ :=
  ((P.product L).filter (fun pℓ =>
    pℓ.1 ∈ (pℓ.2 : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2))))).card
