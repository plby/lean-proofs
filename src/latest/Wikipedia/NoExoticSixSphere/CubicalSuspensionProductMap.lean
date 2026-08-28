import Wikipedia.NoExoticSixSphere.CubicalSuspensionCoordinates
import Wikipedia.NoExoticSixSphere.BasedSphereConnectivity

/-!
# The cubical homomorphism represents the original product suspension map

The equality on the whole source cube identifies the new homomorphism's
representatives with the already constructed product-compactification map.
The actual meridian quotient comparison then gives the same nullity as
ordinary suspension, after every specified number of further suspensions.
This does not assert equality of the two native suspension maps.
-/

noncomputable section

open Set Function Topology
open scoped unitInterval OnePoint

namespace NoExoticSixSphere.CubicalSphereSuspension

open SmoothCube CubicalProductSuspension

variable {m n : ℕ} (f : BasedMap m (Sphere n) (spherePole n))

def compactMap : C(OnePoint (EuclideanSpace ℝ (Fin m)),
    OnePoint (EuclideanSpace ℝ (Fin n))) :=
  (euclideanOnePointSphere n).symm.toHomotopyEquiv.toFun.comp
    (f.val.comp (euclideanOnePointSphere m).toHomotopyEquiv.toFun)

theorem compactMap_infty : compactMap f ∞ = ∞ := by
  change (euclideanOnePointSphere n).symm (f.val (euclideanOnePointSphere m ∞)) = ∞
  rw [euclideanOnePointSphere_infty, f.property, inverseSphere_pole]

theorem sphereMap_compactMap : SuspensionProductComparison.sphereMap (compactMap f) = f.val := by
  apply ContinuousMap.ext
  intro y
  change euclideanOnePointSphere n ((euclideanOnePointSphere n).symm
    (f.val (euclideanOnePointSphere m ((euclideanOnePointSphere m).symm y)))) = f.val y
  rw [Homeomorph.apply_symm_apply, Homeomorph.apply_symm_apply]

theorem productSphereMap_pole :
    SuspensionProductComparison.productSphereMap (compactMap f) (compactMap_infty f)
      (spherePole (m + 1)) = spherePole (n + 1) := by
  have h := productSphereMap_product_formula (compactMap f) (compactMap_infty f)
    (∞ : OnePoint Line) (∞ : OnePoint (EuclideanSpace ℝ (Fin m)))
  simpa only [OnePointProduct.map_infty_left, sphereHomeomorph_infty] using h

def productBasedMap : BasedMap (m + 1) (Sphere (n + 1)) (spherePole (n + 1)) :=
  ⟨SuspensionProductComparison.productSphereMap (compactMap f) (compactMap_infty f),
    productSphereMap_pole f⟩

theorem loop_toGenLoop : loop (toGenLoop f) = toGenLoop (productBasedMap f) := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro u
  change sphereHomeomorph n (OnePointProduct.map
    (clock (u 0), (euclideanOnePointSphere n).symm (f.val (SmoothCube.quotient m (tail u))))) =
    SuspensionProductComparison.productSphereMap (compactMap f) (compactMap_infty f)
      (SmoothCube.quotient (m + 1) u)
  rw [← quotient_product m u, productSphereMap_product_formula]
  change sphereHomeomorph n (OnePointProduct.map
    (clock (u 0), (euclideanOnePointSphere n).symm (f.val (SmoothCube.quotient m (tail u))))) =
      sphereHomeomorph n (OnePointProduct.map
        (clock (u 0), (euclideanOnePointSphere n).symm (f.val
          (euclideanOnePointSphere m ((euclideanOnePointSphere m).symm
            (SmoothCube.quotient m (tail u)))))))
  rw [Homeomorph.apply_symm_apply]

theorem hom_sphereClass [Nonempty (Fin m)] :
    hom m n (sphereClass f) = sphereClass (productBasedMap f) := by
  change (⟦loop (toGenLoop f)⟧ :
    HomotopyGroup (Fin (m + 1)) (Sphere (n + 1)) (spherePole (n + 1))) =
      ⟦toGenLoop (productBasedMap f)⟧
  rw [loop_toGenLoop]

theorem iterate_product_nullhomotopic_iff (r : ℕ) :
    (SphereMapSuspension.iterate (productBasedMap f).val r).Nullhomotopic ↔
      (SphereMapSuspension.iterate (SphereMapSuspension.map f.val) r).Nullhomotopic := by
  have h := SuspensionProductComparison.iterate_suspension_nullhomotopic_iff_product
    (compactMap f) (compactMap_infty f) r
  rw [sphereMap_compactMap] at h
  exact h.symm

end NoExoticSixSphere.CubicalSphereSuspension

namespace NoExoticSixSphere.SmoothCube

theorem sphereClass_eq_one_iff_nullhomotopic {m n : ℕ} (hm : 0 < m)
    [Nonempty (Fin m)] (f : BasedMap m (Sphere n) (spherePole n)) :
    sphereClass f = 1 ↔ f.val.Nullhomotopic := by
  let c : BasedMap m (Sphere n) (spherePole n) :=
    ⟨ContinuousMap.const _ (spherePole n), rfl⟩
  have hc : sphereClass c = (1 : HomotopyGroup (Fin m) (Sphere n) (spherePole n)) := by
    rw [HomotopyGroup.one_def]
    rfl
  rw [← hc, sphereClass_eq_iff hm]
  constructor
  · intro H
    exact ⟨spherePole n, H.homotopic⟩
  · rintro ⟨b, ⟨H⟩⟩
    obtain ⟨K⟩ := sphere_nullhomotopicRel_point_of_nullhomotopic f.val (spherePole m) b H
    refine ⟨K.cast rfl ?_⟩
    apply ContinuousMap.ext
    intro x
    exact f.property

end NoExoticSixSphere.SmoothCube

namespace NoExoticSixSphere.CubicalSphereSuspension

open SmoothCube

theorem hom_sphereClass_eq_one_iff {m n : ℕ} [Nonempty (Fin m)]
    (f : BasedMap m (Sphere n) (spherePole n)) :
    hom m n (sphereClass f) = 1 ↔ (SphereMapSuspension.map f.val).Nullhomotopic := by
  rw [hom_sphereClass, sphereClass_eq_one_iff_nullhomotopic (Nat.succ_pos m)]
  exact iterate_product_nullhomotopic_iff f 0

end NoExoticSixSphere.CubicalSphereSuspension
