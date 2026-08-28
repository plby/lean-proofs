import Wikipedia.NoExoticSixSphere.PartialFrameEquatorialFactorHomology
import Wikipedia.NoExoticSixSphere.SphereCoordinateEquator
import Wikipedia.NoExoticSixSphere.PartialFramePatchHomotopy

/-!
# Even image of the genuine base-factor map in the reduced sequence

The zero-latitude parametrization is the one used in the original overlap
homotopy inverse. Its homeomorphism onto the actual equator identifies the
base restriction of the actual reduced transition with the reflection factor
already computed. Its image under any fiber homology marking is exactly `2ℤ`.
-/

noncomputable section

namespace NoExoticSixSphere.Stiefel.ColumnBundle

open GLOrthonormalization ProductThirdHomology
open Wikipedia.HopfProblem.SingularMayerVietoris
open Wikipedia.HopfProblem.PeriodTorusHigherHomology

theorem equatorialTransition_left_eq (n : ℕ) (v : UnitSphere (Vector 2)) (q : Space (n + 1) 1) :
    (equatorialTransition n v).comp (leftSection q) =
      (equatorialFactor (antipode (spherePole (n + 1))) v q).comp
        (SphereCylinder.zeroEquatorHomeomorph n :
          C(Sphere n, Equator (antipode (spherePole (n + 1))))) := by
  apply ContinuousMap.ext
  intro x
  change transition v (antipode (spherePole (n + 1))) (spherePole (n + 1))
    (SphereCylinder.point n (0, x)) q =
      transition v (antipode (spherePole (n + 1))) (antipode (antipode (spherePole (n + 1))))
        (SphereCylinder.point n (0, x)) q
  have he : antipode (antipode (spherePole (n + 1))) = spherePole (n + 1) :=
    Subtype.ext (neg_neg _)
  rw [he]

theorem equatorialTransition_base_homology_range (v : UnitSphere (Vector 2)) (q : Space 4 1)
    (e : SingularHomology (Space 4 1) 3 ≃ₗ[ℤ] ℤ) :
    Set.range (fun a ↦ e
      (singularHomologyMap ((equatorialTransition 3 v).comp (leftSection q)) 3 a)) =
      Set.range (fun z : ℤ ↦ 2 * z) := by
  let D := homeomorphHomologyEquiv (SphereCylinder.zeroEquatorHomeomorph 3) 3
  have hmap :
      (fun a ↦ e (singularHomologyMap ((equatorialTransition 3 v).comp (leftSection q)) 3 a)) =
        (fun b ↦ e
          (singularHomologyMap (equatorialFactor (antipode (spherePole 4)) v q) 3 b)) ∘ D := by
    funext a
    rw [equatorialTransition_left_eq, singularHomologyMap_comp, LinearMap.comp_apply]
    rfl
  rw [hmap, Set.range_comp, D.surjective.range_eq, Set.image_univ]
  exact equatorialFactor_homology_range (antipode (spherePole 4)) v q (spherePole 0) e

end NoExoticSixSphere.Stiefel.ColumnBundle
