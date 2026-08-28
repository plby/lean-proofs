import Wikipedia.SmoothSixDPoincare.SphereLinearDiffeomorph
import Wikipedia.HopfProblem.DegreeCollapseSphereDiskGluing

/-!
# Standard disk coordinates retaining the native linear isometry

The closed-disk homeomorphism is the literal restriction of a linear
isometry. Its boundary and center formulas retain the actual native
coordinates used by a Morse core, including the local smooth germ.
-/

noncomputable section

open Set Function Metric ContinuousMap
open Wikipedia.SmoothSixDPoincare

namespace Wikipedia.HopfProblem.DegreeCollapse.StandardDiskCoordinates

variable {n : ℕ} {N : Type*} [NormedAddCommGroup N] [InnerProductSpace ℝ N]

def coordinates [FiniteDimensional ℝ N] (hn : Module.finrank ℝ N = n) :
    Hemisphere.Ambient n ≃ₗᵢ[ℝ] N :=
  ((stdOrthonormalBasis ℝ N).reindex (finCongr hn)).repr.symm

variable (L : Hemisphere.Ambient n ≃ₗᵢ[ℝ] N)

def disk : Hemisphere.Ball n ≃ₜ closedBall (0 : N) 1 := {
  toFun := fun u => ⟨L u.val, by
    simpa only [mem_closedBall_zero_iff, L.norm_map] using u.property⟩
  invFun := fun v => ⟨L.symm v.val, by
    simpa only [mem_closedBall_zero_iff, L.symm.norm_map] using v.property⟩
  left_inv := fun u => Subtype.ext (L.symm_apply_apply u.val)
  right_inv := fun v => Subtype.ext (L.apply_symm_apply v.val)
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop }

theorem disk_val (u : Hemisphere.Ball n) : (disk L u).val = L u.val := rfl

theorem disk_zero : disk L ⟨0, mem_closedBall_self zero_le_one⟩ =
    ⟨0, mem_closedBall_self zero_le_one⟩ := Subtype.ext (map_zero L)

def boundary (z : DiskDouble.Boundary (Hemisphere.Ambient n)) : sphere (0 : N) 1 :=
  ⟨L z.val, by simpa only [mem_sphere_zero_iff_norm, L.norm_map] using z.property⟩

theorem disk_boundary (z : DiskDouble.Boundary (Hemisphere.Ambient n)) :
    disk L (DiskDouble.boundary _ z) =
      ⟨(boundary L z).val, sphere_subset_closedBall (boundary L z).property⟩ := rfl

variable {M : Type*} [TopologicalSpace M]

def reparametrize (K : C(closedBall (0 : N) 1, M)) : C(Hemisphere.Ball n, M) :=
  K.comp ⟨disk L, (disk L).continuous⟩

theorem reparametrize_apply (K : C(closedBall (0 : N) 1, M)) (u : Hemisphere.Ball n) :
    reparametrize L K u = K (disk L u) := rfl

theorem range_reparametrize (K : C(closedBall (0 : N) 1, M)) :
    range (reparametrize L K) = range K := by
  apply Set.Subset.antisymm
  · rintro x ⟨u, rfl⟩
    exact ⟨disk L u, rfl⟩
  · rintro x ⟨v, rfl⟩
    exact ⟨(disk L).symm v, congrArg K ((disk L).apply_symm_apply v)⟩

theorem boundary_agrees (A B : C(closedBall (0 : N) 1, M))
    (h : ∀ z : sphere (0 : N) 1,
      A ⟨z.val, sphere_subset_closedBall z.property⟩ =
        B ⟨z.val, sphere_subset_closedBall z.property⟩)
    (z : DiskDouble.Boundary (Hemisphere.Ambient n)) :
    reparametrize L A (DiskDouble.boundary _ z) =
      reparametrize L B (DiskDouble.boundary _ z) := h (boundary L z)

end Wikipedia.HopfProblem.DegreeCollapse.StandardDiskCoordinates
