import Wikipedia.HopfProblem.DegreeCollapsePositiveSphereFillings

/-!
# Contract the boundary of an actual disk in every dimension

The original disk is precomposed with its explicit radial cone. This
retains the entire sphere map at time zero and gives its actual center
at time one. The construction uses no embedding or smoothness claim.
-/

noncomputable section

open Set Function Metric ContinuousMap
open scoped Topology
open Wikipedia.SmoothSixDPoincare

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

theorem sphere_nullhomotopy_of_disk {N : Type*} [TopologicalSpace N] {n : ℕ}
    (γ : C(Hemisphere.Sphere n, N)) (D : C(Hemisphere.Ball (n + 1), N))
    (hboundary : ∀ z : Hemisphere.Sphere n,
      D ⟨z.val, sphere_subset_closedBall z.property⟩ = γ z) :
    ∃ c : N, γ.Homotopic (ContinuousMap.const _ c) := by
  let c := D ⟨0, mem_closedBall_self zero_le_one⟩
  let H : γ.Homotopy (ContinuousMap.const _ c) := {
    toFun := fun p => D (DiskCone.point p)
    continuous_toFun := D.continuous.comp DiskCone.continuous_point
    map_zero_left := by
      intro z
      have he : DiskCone.point (0, z) =
          (⟨z.val, sphere_subset_closedBall z.property⟩ : Hemisphere.Ball (n + 1)) := by
        apply Subtype.ext
        simp [DiskCone.point]
      rw [he]
      exact hboundary z
    map_one_left := by
      intro z
      have he : DiskCone.point (1, z) =
          (⟨0, mem_closedBall_self zero_le_one⟩ : Hemisphere.Ball (n + 1)) := by
        apply Subtype.ext
        simp [DiskCone.point]
      exact congrArg D he }
  exact ⟨c, ⟨H⟩⟩

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
