import Wikipedia.NoExoticSixSphere.CubicalSuspensionSurjectivity

/-!
# The actual native cubical suspension in the stable range

The already constructed product suspension supplies representatives for
surjectivity. The checked comparison with ordinary suspension reflects
nullhomotopy and therefore proves injectivity of the original homomorphism.
No equality of the ordinary and cubical native maps is presumed.
-/

noncomputable section

open scoped Topology

namespace NoExoticSixSphere.CubicalSphereSuspension

open SmoothCube

theorem hom_surjective {m n : ℕ} [NeZero m] (hd : m + 2 < 2 * (n + 1)) :
    Function.Surjective (hom m n) := by
  letI : SimplyConnectedSpace (Sphere (n + 1)) := by
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    infer_instance
  intro x
  induction x using Quotient.inductionOn with
  | h p =>
    let f : BasedMap (m + 1) (Sphere (n + 1)) (spherePole (n + 1)) :=
      (basedEquiv (Nat.succ_pos m)).symm p
    obtain ⟨g, hg⟩ := exists_productBasedMap_homotopic
      (Nat.pos_of_ne_zero (NeZero.ne m)) hd f.val
    have hrel := (sphere_homotopicRel_point_iff (spherePole (m + 1))
      (f.property.trans (productBasedMap g).property.symm)).mpr hg
    have he := (sphereClass_eq_iff (Nat.succ_pos m) f (productBasedMap g)).mpr hrel
    refine ⟨sphereClass g, ?_⟩
    rw [hom_sphereClass]
    exact he.symm.trans (sphereClass_basedEquiv_symm _ p)

theorem hom_eq_one_iff {m n : ℕ} [NeZero m] (hd : m + 3 < 2 * (n + 1))
    (x : π_ m (Sphere n) (spherePole n)) : hom m n x = 1 ↔ x = 1 := by
  induction x using Quotient.inductionOn with
  | h p =>
    let f : BasedMap m (Sphere n) (spherePole n) :=
      (basedEquiv (Nat.pos_of_ne_zero (NeZero.ne m))).symm p
    have hf := (hom_sphereClass_eq_one_iff f).trans
      ((SphereMapSuspension.map_nullhomotopic_iff hd f.val).trans
        (sphereClass_eq_one_iff_nullhomotopic (Nat.pos_of_ne_zero (NeZero.ne m)) f).symm)
    simpa only [f, sphereClass_basedEquiv_symm] using hf

theorem hom_injective {m n : ℕ} [NeZero m] (hd : m + 3 < 2 * (n + 1)) :
    Function.Injective (hom m n) := by
  intro x y hxy
  apply div_eq_one.mp
  apply (hom_eq_one_iff hd (x / y)).mp
  rw [map_div, hxy]
  exact div_self' _

theorem hom_bijective {m n : ℕ} [NeZero m] (hd : m + 3 < 2 * (n + 1)) :
    Function.Bijective (hom m n) :=
  ⟨hom_injective hd, hom_surjective (by omega)⟩

end NoExoticSixSphere.CubicalSphereSuspension
