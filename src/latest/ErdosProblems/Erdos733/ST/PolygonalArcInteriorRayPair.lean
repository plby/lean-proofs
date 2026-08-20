import ErdosProblems.Erdos733.ST.PolygonalArc

open Classical
noncomputable section

-- [TABLET NODE: PolygonalArcInteriorRayPair]
structure PolygonalArcInteriorRayPair
    (gamma : PolygonalArc) (p : EuclideanSpace ℝ (Fin 2)) where
-- BODY
  firstIndex : ℕ
  secondIndex : ℕ
  firstIndex_valid : firstIndex + 1 < gamma.vertices.length
  secondIndex_valid : secondIndex + 1 < gamma.vertices.length
  firstVector : EuclideanSpace ℝ (Fin 2)
  secondVector : EuclideanSpace ℝ (Fin 2)
  firstVector_ne_zero : firstVector ≠ 0
  secondVector_ne_zero : secondVector ≠ 0
  firstScale : ℝ
  secondScale : ℝ
  firstScale_ne_zero : firstScale ≠ 0
  secondScale_ne_zero : secondScale ≠ 0
  firstVector_eq :
    firstVector = firstScale •
      (gamma.vertices[firstIndex + 1] - gamma.vertices[firstIndex])
  secondVector_eq :
    secondVector = secondScale •
      (gamma.vertices[secondIndex + 1] - gamma.vertices[secondIndex])
  firstRay_subset :
    segment ℝ p (p + firstVector) ⊆
      segment ℝ gamma.vertices[firstIndex] gamma.vertices[firstIndex + 1]
  secondRay_subset :
    segment ℝ p (p + secondVector) ⊆
      segment ℝ gamma.vertices[secondIndex] gamma.vertices[secondIndex + 1]
  rays_not_same_positive :
    ¬ ∃ a : ℝ, 0 < a ∧ secondVector = a • firstVector
