import Wikipedia.SmoothSixDPoincare.ContinuousDiskExtension
import Wikipedia.SmoothSixDPoincare.SmoothHomotopyCollars
import Wikipedia.SmoothSixDPoincare.CollaredRadialExtension
import Wikipedia.SmoothSixDPoincare.EmbeddedDiskExtension

/-!
# Smooth embedded disk fillings from actual continuous disk fillings

Radial contraction of the supplied disk gives an actual boundary
nullhomotopy. Relative smoothing supplies smooth endpoint collars, and the
proved radial filling gives a smooth global extension. In target dimension
at least five, boundary derivative repair and general position produce an
embedded immersive disk with the original boundary fixed exactly.
-/

noncomputable section

open Set Function Filter Metric Manifold ContinuousMap
open scoped ContDiff Topology
open Wikipedia.SmoothSixDPoincare

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

theorem circle_nullhomotopy_of_disk {N : Type*} [TopologicalSpace N]
    (γ : C(Hemisphere.Sphere 1, N)) (D : C(Hemisphere.Ball 2, N))
    (hboundary : ∀ z : Hemisphere.Sphere 1, D ⟨z.val, sphere_subset_closedBall z.property⟩ = γ z) :
    ∃ c : N, γ.Homotopic (ContinuousMap.const _ c) := by
  let c := D ⟨0, mem_closedBall_self zero_le_one⟩
  let H : γ.Homotopy (ContinuousMap.const _ c) := {
    toFun := fun p => D (DiskCone.point p)
    continuous_toFun := D.continuous.comp DiskCone.continuous_point
    map_zero_left := by
      intro z
      have he : DiskCone.point (0, z) =
          (⟨z.val, sphere_subset_closedBall z.property⟩ : Hemisphere.Ball 2) := by
        apply Subtype.ext
        simp [DiskCone.point]
      rw [he]
      exact hboundary z
    map_one_left := by
      intro z
      have he : DiskCone.point (1, z) =
          (⟨0, mem_closedBall_self zero_le_one⟩ : Hemisphere.Ball 2) := by
        apply Subtype.ext
        simp [DiskCone.point]
      exact congrArg D he }
  exact ⟨c, ⟨H⟩⟩

theorem exists_smooth_embedded_disk_of_continuous_filling
    {G N : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
    [TopologicalSpace N] [ChartedSpace G N] [IsManifold 𝓘(ℝ, G) ∞ N] [T2Space N]
    (γ : C(Hemisphere.Sphere 1, N)) (hγ : ContMDiff (𝓡 1) 𝓘(ℝ, G) ∞ γ)
    (hγinj : Injective γ) (hγderiv : ∀ z, Injective (mfderiv (𝓡 1) 𝓘(ℝ, G) γ z))
    (hdim : 5 ≤ Module.finrank ℝ G) (D : C(Hemisphere.Ball 2, N))
    (hboundary : ∀ z : Hemisphere.Sphere 1, D ⟨z.val, sphere_subset_closedBall z.property⟩ = γ z) :
    ∃ g : C(Hemisphere.Ambient 2, N), ContMDiff 𝓘(ℝ, Hemisphere.Ambient 2) 𝓘(ℝ, G) ∞ g ∧
      (∀ z : Hemisphere.Sphere 1, g z.val = γ z) ∧
      Topology.IsClosedEmbedding (fun z : Hemisphere.Ball 2 => g z.val) ∧
      ∀ z : Hemisphere.Ball 2, Injective (mfderiv 𝓘(ℝ, Hemisphere.Ambient 2) 𝓘(ℝ, G) g z.val) := by
  obtain ⟨c, ⟨H⟩⟩ := circle_nullhomotopy_of_disk γ D hboundary
  obtain ⟨H', hH', hlo, hhi⟩ :=
    ManifoldSmoothing.exists_smooth_homotopy_with_collars hγ contMDiff_const H
  obtain ⟨v, hv⟩ : (sphere (0 : Hemisphere.Ambient 2) 1).Nonempty :=
    NormedSpace.sphere_nonempty.mpr zero_le_one
  let b : Hemisphere.Sphere 1 := ⟨v, hv⟩
  have hsmooth := RadialFilling.contMDiff_filling H' b hγ hH' hlo hhi
  have hext := RadialFilling.filling_on_sphere H' b hlo
  exact exists_embedded_disk_extension_of_smooth_extension hsmooth hext hγinj hγderiv hdim

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
