import Wikipedia.HopfProblem.DegreeCollapseOrthogonalHopfNullhomotopy
import Wikipedia.HopfProblem.DegreeCollapseRankSixThirdVanishing

/-!
# Unconditional nullity of the Hopf construction on S4-to-O(16) families

The previously proved native fourth orthogonal group vanishes. Center
an arbitrary sphere family at its value on the pole, descend the native
cube nullhomotopy, and restore that value. The actual Hopf construction
therefore contracts, with no nullity hypothesis on the supplied family.
This does not yet identify it with the original iterated sphere suspensions.
-/

noncomputable section

open scoped Topology
open NoExoticSixSphere GLOrthonormalization SmoothCube

namespace Wikipedia.HopfProblem.DegreeCollapse.OrthogonalHopfMap

theorem four_family_based_nullhomotopic (f : C(Sphere 4, OrthogonalOperators 16))
    (hf : f (spherePole 4) = 1) : f.Homotopic (ContinuousMap.const _ 1) := by
  let := RankSixThirdVanishing.piFourOrthogonalSixteen_subsingleton
  have h := (sphereClass_eq_iff (by decide : 0 < 4)
    (⟨f, hf⟩ : BasedMap 4 (OrthogonalOperators 16) 1)
    ⟨ContinuousMap.const _ 1, rfl⟩).mp (Subsingleton.elim _ _)
  exact h.homotopic

theorem four_family_nullhomotopic (f : C(Sphere 4, OrthogonalOperators 16)) :
    f.Homotopic (ContinuousMap.const _ (f (spherePole 4))) := by
  let A := f (spherePole 4)
  let g : C(Sphere 4, OrthogonalOperators 16) :=
    ⟨fun x ↦ A⁻¹ * f x, continuous_const.mul f.continuous⟩
  have hg : g (spherePole 4) = 1 := inv_mul_cancel A
  obtain ⟨H⟩ := four_family_based_nullhomotopic g hg
  refine ⟨{
    toFun := fun z ↦ A * H z
    continuous_toFun := continuous_const.mul H.continuous
    map_zero_left := ?_
    map_one_left := ?_ }⟩
  · intro x
    rw [H.apply_zero]
    exact mul_inv_cancel_left A (f x)
  · intro x
    change A * H (1, x) = A
    rw [H.apply_one]
    exact mul_one A

theorem four_hopf_nullhomotopic (f : C(Sphere 4, OrthogonalOperators 16)) :
    (sphereMap f).Homotopic (ContinuousMap.const (Source (Vector 5) 16) (pole 16)) :=
  nullhomotopic_of_family (f (spherePole 4)) (four_family_nullhomotopic f)

theorem four_hopf_nullhomotopic_rel (f : C(Sphere 4, OrthogonalOperators 16))
    (x : Source (Vector 5) 16) :
    (sphereMap f).HomotopicRel (ContinuousMap.const _ (sphereMap f x)) {x} :=
  OrbitPair.SphereNullhomotopy.based_of_unbased (sphereMap f) x (pole 16)
    (four_hopf_nullhomotopic f)

end Wikipedia.HopfProblem.DegreeCollapse.OrthogonalHopfMap
