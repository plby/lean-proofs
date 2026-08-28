import Wikipedia.NoExoticSixSphere.SphereEquationChartChange
import Wikipedia.NoExoticSixSphere.SphereSuspensionFiber
import Wikipedia.NoExoticSixSphere.PartialDiffeomorphProduct

/-!
# A genuine product target chart for the original suspension

The punctured-sphere cylinder chart, the original target chart, and the
fixed ordered Euclidean coordinates compose to an actual partial
diffeomorphism. In this chart, the original suspension's centered
coordinates are exactly its height and the old centered coordinates.
-/

noncomputable section

open scoped Manifold ContDiff

namespace NoExoticSixSphere.SphereMapSuspension

open GLOrthonormalization Wikipedia.HopfProblem.DegreeCollapse

variable {n : ℕ}
  (c : PartialDiffeomorph (𝓡 n) (𝓡 n) (Sphere n) (Vector n) ∞)

def orderedProductDiffeomorph (n : ℕ) :
    (ℝ × Vector n) ≃ₘ⟮(𝓘(ℝ, ℝ)).prod (𝓡 n), 𝓡 (n + 1)⟯ Vector (n + 1) where
  toEquiv := (EuclideanProduct.coordinates n).toEquiv
  contMDiff_toFun := by
    rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod]
    exact (EuclideanProduct.coordinates n).contDiff.contMDiff
  contMDiff_invFun := by
    rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod]
    exact (EuclideanProduct.coordinates n).symm.contDiff.contMDiff

def targetCylinderChart :
    PartialDiffeomorph (𝓡 (n + 1)) (𝓡 (n + 1)) (Sphere (n + 1)) (Vector (n + 1)) ∞ :=
  (SphereCylinder.chart n).symm.trans
    ((partialDiffeomorphProd (Diffeomorph.refl 𝓘(ℝ, ℝ) ℝ ∞).toPartialDiffeomorph c).trans
      (orderedProductDiffeomorph n).toPartialDiffeomorph)

theorem targetCylinderChart_apply (y : Sphere (n + 1)) :
    targetCylinderChart c y = EuclideanProduct.coordinates n
      ((SphereCylinder.inverse n y).1, c (SphereCylinder.inverse n y).2) := rfl

theorem targetCylinderChart_equator (b : Sphere n) :
    targetCylinderChart c (equator n b) = EuclideanProduct.coordinates n (0, c b) := by
  rw [targetCylinderChart_apply, inverse_equator]

theorem equator_mem_targetCylinderChart (b : Sphere n) (hb : b ∈ c.source) :
    equator n b ∈ (targetCylinderChart c).source := by
  change equator n b ∈ SphereCylinder.band n ∧
    ((True ∧ (SphereCylinder.inverse n (equator n b)).2 ∈ c.source) ∧ True)
  rw [inverse_equator]
  exact ⟨equator_mem_band n b, ⟨⟨trivial, hb⟩, trivial⟩⟩

theorem targetCylinderChart_point (p : ℝ × Sphere n) :
    targetCylinderChart c (SphereCylinder.point n p) =
      EuclideanProduct.coordinates n (p.1, c p.2) := by
  rw [targetCylinderChart_apply, SphereCylinder.inverse_point]

theorem centered_coordinates_map_point {m : ℕ} (f : C(Sphere m, Sphere n))
    (b : Sphere n) (p : ℝ × Sphere m) :
    CenteredChartCoordinates.coordinates (map f) (targetCylinderChart c) (equator n b)
        (SphereCylinder.point m p) =
      EuclideanProduct.coordinates n
        (p.1, CenteredChartCoordinates.coordinates f c b p.2) := by
  rw [CenteredChartCoordinates.coordinates, map_cylinder_point,
    targetCylinderChart_point, targetCylinderChart_equator, ← map_sub]
  simp only [Prod.mk_sub_mk, sub_zero]
  rfl

theorem centered_coordinates_map_band {m : ℕ} (f : C(Sphere m, Sphere n))
    (b : Sphere n) (y : Sphere (m + 1)) (hy : y ∈ SphereCylinder.band m) :
    CenteredChartCoordinates.coordinates (map f) (targetCylinderChart c) (equator n b) y =
      EuclideanProduct.coordinates n ((SphereCylinder.inverse m y).1,
        CenteredChartCoordinates.coordinates f c b (SphereCylinder.inverse m y).2) := by
  have h := centered_coordinates_map_point c f b (SphereCylinder.inverse m y)
  rwa [SphereCylinder.point_inverse m y hy] at h

end NoExoticSixSphere.SphereMapSuspension
