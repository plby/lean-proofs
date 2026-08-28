import Wikipedia.NoExoticSixSphere.PartialFrameEquatorialFactor

/-!
# The actual equatorial frame-factor map has even third-homology image

The proved comparison uses the original orthogonal-complement sphere and
the actual one-column evaluation homeomorphism. Quaternion coordinates are
only an isometry used in the proved reflection theorem. Under any integral
marking of the target fiber, the actual induced image is exactly `2ℤ`.
-/

noncomputable section

open scoped Quaternion

namespace NoExoticSixSphere.Stiefel.ColumnBundle

open GLOrthonormalization ColumnCoordinates
open Wikipedia.HopfProblem.SingularMayerVietoris
open Wikipedia.HopfProblem.PeriodTorusHigherHomology

local instance ambientDimension :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (4 + 1))) = 4 + 1) :=
  ⟨finrank_euclideanSpace_fin⟩

def complementQuaternionIsometry (c : Sphere 4) : (ℝ ∙ c.val)ᗮ ≃ₗᵢ[ℝ] ℍ :=
  (complement (r := 4) c).trans Quaternion.linearIsometryEquivTuple.symm

theorem equatorialFactor_homology_range (c : Sphere 4) (v : UnitSphere (Vector 2))
    (q : Space 4 1) (u : UnitSphere (Vector 1)) (e : SingularHomology (Space 4 1) 3 ≃ₗ[ℤ] ℤ) :
    Set.range (fun a ↦ e (singularHomologyMap (equatorialFactor c v q) 3 a)) =
      Set.range (fun z : ℤ ↦ 2 * z) := by
  let D := homeomorphHomologyEquiv (equatorOrthogonalHomeomorph c) 3
  let T := homeomorphHomologyEquiv (frameSphereHomeomorph c u) 3
  let marking := T.symm.trans e
  have hmap : (fun a ↦ e (singularHomologyMap (equatorialFactor c v q) 3 a)) =
      (fun b ↦ marking
        (singularHomologyMap (SphereReflection.positive (fixedVector c q u)) 3 b)) ∘ D := by
    funext a
    rw [equatorialFactor_conjugacy c v q u, singularHomologyMap_comp, LinearMap.comp_apply,
      singularHomologyMap_comp, LinearMap.comp_apply]
    rfl
  rw [hmap, Set.range_comp, D.surjective.range_eq, Set.image_univ]
  exact SphereReflection.positive_homology_range (complementQuaternionIsometry c)
    (fixedVector c q u) marking

end NoExoticSixSphere.Stiefel.ColumnBundle
