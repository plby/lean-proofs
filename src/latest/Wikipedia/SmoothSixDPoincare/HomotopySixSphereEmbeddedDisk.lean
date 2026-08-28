import Wikipedia.SmoothSixDPoincare.EmbeddedDiskExtension
import Wikipedia.SmoothSixDPoincare.SmoothDiskExtension

/-!
# Constructed embedded disk fillings in the original homotopy six-sphere

The original homotopy equivalence supplies a smooth circle filling. Its
boundary derivative is repaired with the boundary values fixed, and the
relative immersion and self-intersection constructions make the entire
closed disk embedded. No disk, collar, or extension is assumed as input.

This is an embedded filling theorem, not yet a framed Whitney-disk theorem
relative to the intersecting handles, or a handle-cancellation theorem.
-/

noncomputable section

open ContinuousMap
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare

variable {G M : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  [TopologicalSpace M] [ChartedSpace G M] [IsManifold 𝓘(ℝ, G) ∞ M] [T2Space M]

/-- Every smooth injective immersive circle in a six-dimensional smooth homotopy sphere bounds
an actual smoothly embedded closed Euclidean disk, with its boundary values fixed exactly. -/
theorem exists_embedded_disk_of_homotopySixSphere (e : M ≃ₕ SixSphere)
    (hdim : Module.finrank ℝ G = 6) (γ : C(Hemisphere.Sphere 1, M))
    (hγ : ContMDiff (𝓡 1) 𝓘(ℝ, G) ∞ γ) (hγinj : Function.Injective γ)
    (hγderiv : ∀ x, Function.Injective (mfderiv (𝓡 1) 𝓘(ℝ, G) γ x)) :
    ∃ g : C(Hemisphere.Ambient 2, M),
      ContMDiff 𝓘(ℝ, Hemisphere.Ambient 2) 𝓘(ℝ, G) ∞ g ∧
      (∀ x : Hemisphere.Sphere 1, g x.1 = γ x) ∧
      Topology.IsClosedEmbedding (fun x : Hemisphere.Ball 2 => g x.1) ∧
      ∀ x : Hemisphere.Ball 2,
        Function.Injective (mfderiv 𝓘(ℝ, Hemisphere.Ambient 2) 𝓘(ℝ, G) g x.1) := by
  obtain ⟨-, f, hf, hext, -⟩ :=
    exists_smooth_disk_extension_of_homotopySixSphere e (n := 1) (by decide) γ hγ
  exact exists_embedded_disk_extension_of_smooth_extension hf hext hγinj hγderiv (by omega)

end Wikipedia.SmoothSixDPoincare
