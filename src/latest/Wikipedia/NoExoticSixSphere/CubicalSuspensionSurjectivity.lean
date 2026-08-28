import Wikipedia.NoExoticSixSphere.OrdinarySuspensionSurjectivity
import Wikipedia.NoExoticSixSphere.StableSixFiniteDetection
import Wikipedia.NoExoticSixSphere.HomotopyEquivalenceSquare

/-!
# Surjectivity of the actual cubical suspension homomorphism

Conjugate an original target map by the constructed meridian homotopy
equivalences, desuspend it, and adjust the lower-dimensional map at its
basepoint. The original commuting square and both inverse homotopies
then give a product-suspension representative of the original map.
Native based comparison turns this into actual group-map surjectivity.
-/

noncomputable section

namespace NoExoticSixSphere.CubicalSphereSuspension

open SmoothCube SuspensionProductComparison

theorem exists_productBasedMap_homotopic {m n : ℕ} (hm : 0 < m)
    (hd : m + 2 < 2 * (n + 1)) (f : C(Sphere (m + 1), Sphere (n + 1))) :
    ∃ g : BasedMap m (Sphere n) (spherePole n), f.Homotopic (productBasedMap g).val := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  let E := sphereQuotientEquiv m
  let T := sphereQuotientEquiv (j + 1)
  let F := T.invFun.comp (f.comp E.toFun)
  obtain ⟨g₀, hg₀⟩ := SphereMapSuspension.exists_homotopic_suspension hd F
  obtain ⟨g, hg⟩ := exists_based_map_homotopic hm g₀ (spherePole (j + 1))
  have H : F.Homotopic (SphereMapSuspension.map g.val) :=
    hg₀.trans (SphereMapSuspension.map_homotopic hg)
  have hsquare : T.toFun.comp (SphereMapSuspension.map g.val) =
      (productBasedMap g).val.comp E.toFun := by
    have hs := sphereQuotient_suspension (compactMap g) (compactMap_infty g)
    rw [sphereMap_compactMap] at hs
    exact hs
  exact ⟨g, homotopic_of_equiv_square E T f (SphereMapSuspension.map g.val)
    (productBasedMap g).val H hsquare⟩

end NoExoticSixSphere.CubicalSphereSuspension

namespace NoExoticSixSphere.CubicalStableSix

open SmoothCube

theorem stepHom_surjective {k : ℕ} (hk : 5 ≤ k) : Function.Surjective (stepHom k) := by
  intro x
  induction x using Quotient.inductionOn with
  | h p =>
    let f : BasedStage (k + 1) := (basedEquiv (by omega : 0 < (k + 1) + 8)).symm p
    obtain ⟨g, hg⟩ := CubicalSphereSuspension.exists_productBasedMap_homotopic
      (by omega : 0 < k + 8) (by omega : (k + 8) + 2 < 2 * ((k + 2) + 1)) f.val
    have hrel := (sphere_homotopicRel_point_iff (spherePole ((k + 1) + 8))
      (f.property.trans (CubicalSphereSuspension.productBasedMap g).property.symm)).mpr hg
    have he := (sphereClass_eq_iff (by omega : 0 < (k + 1) + 8)
      f (CubicalSphereSuspension.productBasedMap g)).mpr hrel
    refine ⟨sphereClass g, ?_⟩
    change CubicalSphereSuspension.hom (k + 8) (k + 2) (sphereClass g) = _
    rw [CubicalSphereSuspension.hom_sphereClass]
    exact he.symm.trans (sphereClass_basedEquiv_symm _ p)

end NoExoticSixSphere.CubicalStableSix
