import Util.IncidenceGeometry.PlanarRot90

open Classical
noncomputable section

lemma PlanarRot90Orthogonal (d : EuclideanSpace ℝ (Fin 2)) :
    inner ℝ d (PlanarRot90 d) = 0 := by
  dsimp [PlanarRot90]
  rw [PiLp.inner_apply]
  simp
  ring
