import ErdosProblems.Erdos733.ST.PlanarRot90

open Classical
noncomputable section

-- [TABLET NODE: PlanarRot90Norm]
lemma PlanarRot90Norm (d : EuclideanSpace ℝ (Fin 2)) :
    ‖PlanarRot90 d‖ = ‖d‖ := by
-- BODY
  dsimp [PlanarRot90]
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq]
  rw [PiLp.inner_apply, PiLp.inner_apply]
  simp
  ring
