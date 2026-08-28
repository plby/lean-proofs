import Mathlib.Analysis.Quaternion
import Mathlib.Topology.Algebra.Star.Unitary
import Wikipedia.HopfProblem.SphereHomologySuspension

/-!
# The unit quaternion group as the literal Euclidean three-sphere

This identifies the existing topological group `unitary ℍ` with the
ordinary Euclidean unit three-sphere. It supplies the group model needed
for the power-map argument, without assigning a new topology to a sphere.
-/

noncomputable section

namespace Wikipedia.HopfProblem.UnitQuaternionSphere

local notation "ℍ" => Quaternion ℝ

abbrev UnitQuaternions := unitary ℍ

theorem mem_unitary_iff_norm_eq_one (q : ℍ) : q ∈ unitary ℍ ↔ ‖q‖ = 1 := by
  constructor
  · intro h
    exact CStarRing.norm_coe_unitary (⟨q, h⟩ : unitary ℍ)
  · intro h
    have hs : Quaternion.normSq q = 1 := by
      rw [Quaternion.normSq_eq_norm_mul_self, h, one_mul]
    exact ⟨by rw [Quaternion.star_mul_self, hs, Quaternion.coe_one],
      by rw [Quaternion.self_mul_star, hs, Quaternion.coe_one]⟩

/-- The usual four real quaternion coordinates give the sphere homeomorphism. -/
def sphereHomeomorph : UnitQuaternions ≃ₜ SphereHomology.UnitSphere 3 where
  toFun q := ⟨Quaternion.linearIsometryEquivTuple q,
    by simpa only [Metric.mem_sphere, dist_zero_right,
      Quaternion.linearIsometryEquivTuple.norm_map] using
        (mem_unitary_iff_norm_eq_one q).mp q.property⟩
  invFun v := ⟨Quaternion.linearIsometryEquivTuple.symm v,
    (mem_unitary_iff_norm_eq_one _).mpr (by
      simpa only [Quaternion.linearIsometryEquivTuple.symm.norm_map] using
        (mem_sphere_zero_iff_norm.mp v.property))⟩
  left_inv q := by apply Subtype.ext; exact Quaternion.linearIsometryEquivTuple.symm_apply_apply q
  right_inv v := by apply Subtype.ext; exact Quaternion.linearIsometryEquivTuple.apply_symm_apply v
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

instance : PathConnectedSpace UnitQuaternions :=
  sphereHomeomorph.symm.surjective.pathConnectedSpace sphereHomeomorph.symm.continuous

end Wikipedia.HopfProblem.UnitQuaternionSphere
