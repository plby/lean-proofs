import ErdosProblems.Erdos633b.TriquadraticComparison
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-! Area of actual triangles under a linear vertex map. This is Lebesgue
measure scaling by the absolute determinant, not a new definition of area. -/

namespace Erdos633b

open MeasureTheory

namespace Triangle

theorem support_eq_linear_image (R U : Triangle) (L : Plane →ₗ[ℝ] Plane)
    (h : ∀ i, U.points i = L (R.points i)) : U.support = L '' R.support := by
  have he : U.points = L ∘ R.points := funext h
  rw [support, he, Set.range_comp]
  exact (L.toAffineMap.image_convexHull (Set.range R.points)).symm

theorem area_eq_abs_det_mul (R U : Triangle) (L : Plane →ₗ[ℝ] Plane)
    (h : ∀ i, U.points i = L (R.points i)) :
    U.area = |LinearMap.det L| * R.area := by
  have hv := Measure.addHaar_image_linearMap (volume : Measure Plane) L R.support
  rw [← R.support_eq_linear_image U L h] at hv
  have ha := congrArg ENNReal.toReal hv
  simpa only [area, ENNReal.toReal_mul, ENNReal.toReal_ofReal (abs_nonneg _)] using ha

end Triangle

theorem det_plane_matrix (M : Matrix (Fin 2) (Fin 2) ℝ) :
    LinearMap.det (Matrix.toEuclideanLin M) = Matrix.det M := by
  rw [← LinearMap.det_toMatrix (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis]
  simp only [Matrix.toEuclideanLin_eq_toLin_orthonormal, LinearMap.toMatrix_toLin]

end Erdos633b
