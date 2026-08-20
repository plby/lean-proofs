import ErdosProblems.Erdos733.ST.PlanarRot90

open Classical
noncomputable section

-- [TABLET NODE: PlanarRot90Orthogonal]
lemma PlanarRot90Orthogonal (d : EuclideanSpace ℝ (Fin 2)) :
    inner ℝ d (PlanarRot90 d) = 0 := by
-- BODY
  dsimp [PlanarRot90]
  rw [PiLp.inner_apply]
  simp
  ring
