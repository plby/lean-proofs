import Util.IncidenceGeometry.PlanarRot90

open Classical
noncomputable section

lemma PlanarRot90LinearCombination (u : EuclideanSpace ℝ (Fin 2)) (A B : ℝ) :
    PlanarRot90 (A • u + B • PlanarRot90 u) =
      (-B) • u + A • PlanarRot90 u := by
  apply PiLp.ext
  intro k
  fin_cases k
  · simp [PlanarRot90]
  · simp [PlanarRot90]
    ring
