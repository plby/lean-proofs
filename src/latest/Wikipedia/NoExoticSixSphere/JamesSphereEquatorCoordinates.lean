import Wikipedia.NoExoticSixSphere.JamesSphereClockCoordinates
import Wikipedia.NoExoticSixSphere.StereographicEquatorCoordinates
import Wikipedia.NoExoticSixSphere.EuclideanBlockInner

/-!
# The James middle slice is the actual orthogonal equator

The last finite coordinate defines a unit axis. The stereographic
hyperplane formula identifies the entire middle-slice image, including
the original compactification pole, with its orthogonal sphere equator.
-/

noncomputable section

open scoped unitInterval OnePoint InnerProductSpace

namespace NoExoticSixSphere.JamesSphere

abbrev V (n : ℕ) := EuclideanSpace ℝ (Fin n)

theorem inner_linePoint (r : ℝ) (x : CubicalProductSuspension.Line) :
    inner ℝ (linePoint r) x = r * x 0 := by
  rw [PiLp.inner_apply, Fin.sum_univ_one]
  change x 0 * r = r * x 0
  ring

theorem inner_product_axis (n : ℕ) (a : V n) (z : CubicalProductSuspension.Line) :
    inner ℝ (EuclideanFactorProduct.productCoordinates n 1 (0, linePoint 1))
      (EuclideanFactorProduct.productCoordinates n 1 (a, z)) = z 0 := by
  change inner ℝ (EuclideanSpace.finAddEquivProd.symm (0, linePoint 1))
    (EuclideanSpace.finAddEquivProd.symm (a, z)) = _
  rw [inner_finAdd_symm, inner_zero_left, zero_add, inner_linePoint, one_mul]

def coordinateAxis (n : ℕ) : UnitSphere (V (n + 1)) :=
  ⟨EuclideanFactorProduct.productCoordinates n 1 (0, linePoint 1), by
    have hi := inner_product_axis n 0 (linePoint 1)
    rw [real_inner_self_eq_norm_sq] at hi
    change ‖EuclideanFactorProduct.productCoordinates n 1 (0, linePoint 1)‖ ^ 2 = 1 at hi
    have hn : ‖EuclideanFactorProduct.productCoordinates n 1 (0, linePoint 1)‖ = 1 := by
      nlinarith [norm_nonneg (EuclideanFactorProduct.productCoordinates n 1 (0, linePoint 1))]
    simpa only [Metric.mem_sphere, dist_zero_right] using hn⟩

def equatorPole (n : ℕ) : Sphere (n + 1) := StereographicEquator.axis (n + 1) (coordinateAxis n)

theorem product_linePoint (n : ℕ) (r : ℝ) :
    EuclideanFactorProduct.productCoordinates n 1 (0, linePoint r) =
      r • (coordinateAxis n).val := by
  have he : ((0 : V n), linePoint r) = r • ((0 : V n), linePoint 1) := by
    apply Prod.ext
    · simp
    · ext i
      change r = r * 1
      ring
  change EuclideanSpace.finAddEquivProd.symm (0, linePoint r) =
    r • EuclideanSpace.finAddEquivProd.symm (0, linePoint 1)
  rw [he, map_smul]

theorem coordinate_hyperplane (n : ℕ) (z : V (n + 1)) :
    inner ℝ (coordinateAxis n).val z = 0 ↔
      ∃ a : V n, EuclideanFactorProduct.productCoordinates n 1 (a, 0) = z := by
  obtain ⟨⟨a, b⟩, rfl⟩ := (EuclideanFactorProduct.productCoordinates n 1).surjective z
  change inner ℝ (EuclideanFactorProduct.productCoordinates n 1 (0, linePoint 1))
    (EuclideanFactorProduct.productCoordinates n 1 (a, b)) = 0 ↔ _
  rw [inner_product_axis]
  constructor
  · intro hb
    have he : b = 0 := by
      ext i
      have hi : i = 0 := Subsingleton.elim _ _
      change b i = 0
      rw [hi]
      exact hb
    exact ⟨a, he ▸ rfl⟩
  · rintro ⟨c, hc⟩
    have he := (EuclideanFactorProduct.productCoordinates n 1).injective hc
    have hb : b = 0 := (congrArg Prod.snd he).symm
    rw [hb]
    rfl

theorem middle_pole (n : ℕ) : middle n (spherePole n) = spherePole (n + 1) :=
  loopEvaluation_pole n middleTime

theorem middle_range_eq_equator (n : ℕ) : Set.range (middle n) = equator (equatorPole n) := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    obtain ⟨z, rfl⟩ := (euclideanOnePointSphere n).surjective x
    induction z using OnePoint.rec with
    | infty =>
      rw [euclideanOnePointSphere_infty, middle_pole]
      exact StereographicEquator.inner_axis_pole (n + 1) (coordinateAxis n)
    | coe a =>
      rw [middle_finite]
      apply (StereographicEquator.finite_mem_equator_iff (n + 1) (coordinateAxis n) _).mpr
      exact (coordinate_hyperplane n _).mpr ⟨a, rfl⟩
  · intro hy
    obtain ⟨z, rfl⟩ := (euclideanOnePointSphere (n + 1)).surjective y
    induction z using OnePoint.rec with
    | infty => exact ⟨spherePole n, middle_pole n⟩
    | coe z =>
      have hz := (StereographicEquator.finite_mem_equator_iff (n + 1)
        (coordinateAxis n) z).mp hy
      obtain ⟨a, ha⟩ := (coordinate_hyperplane n z).mp hz
      refine ⟨euclideanOnePointSphere n (a : OnePoint _), ?_⟩
      rw [middle_finite, ha]

end NoExoticSixSphere.JamesSphere
