import ErdosProblems.Erdos633b.Similarity

/-! The law of cosines in the project's ordered side and angle conventions. -/

namespace Erdos633b.Triangle

theorem cosine_law (T : Triangle) (i : Fin 3) :
    T.side i ^ 2 = T.side (i + 1) ^ 2 + T.side (i + 2) ^ 2 -
      2 * T.side (i + 1) * T.side (i + 2) * Real.cos (T.angle i) := by
  have h := EuclideanGeometry.law_cos (T.points (i + 1)) (T.points i) (T.points (i + 2))
  have h1 : T.side (i + 1) = dist (T.points (i + 2)) (T.points i) := by fin_cases i <;> rfl
  have h2 : T.side (i + 2) = dist (T.points i) (T.points (i + 1)) := by fin_cases i <;> rfl
  rw [h1, h2]
  change dist (T.points (i + 1)) (T.points (i + 2)) ^ 2 =
    dist (T.points (i + 2)) (T.points i) ^ 2 + dist (T.points i) (T.points (i + 1)) ^ 2 -
      2 * dist (T.points (i + 2)) (T.points i) * dist (T.points i) (T.points (i + 1)) *
        Real.cos (EuclideanGeometry.angle (T.points (i + 1)) (T.points i) (T.points (i + 2)))
  rw [dist_comm (T.points (i + 1)) (T.points i)] at h
  nlinarith

end Erdos633b.Triangle
