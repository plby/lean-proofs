import ErdosProblems.Erdos733.ST.Preamble

-- [TABLET NODE: IsAffineLine]
def IsAffineLine (ℓ : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2))) : Prop :=
-- BODY
  (ℓ : Set (EuclideanSpace ℝ (Fin 2))).Nonempty ∧ Module.finrank ℝ ℓ.direction = 1
