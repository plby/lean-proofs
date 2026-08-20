import ErdosProblems.Erdos733.ST.PlanarRot90

open Classical
noncomputable section

-- [TABLET NODE: PlanarRot90LinearCombination]
lemma PlanarRot90LinearCombination (u : EuclideanSpace ℝ (Fin 2)) (A B : ℝ) :
    PlanarRot90 (A • u + B • PlanarRot90 u) =
      (-B) • u + A • PlanarRot90 u := by
-- BODY
  apply PiLp.ext
  intro k
  fin_cases k
  · simp [PlanarRot90]
  · simp [PlanarRot90]
    ring
