import Wikipedia.SmoothSixDPoincare.CollaredRadialExtension
import Wikipedia.SmoothSixDPoincare.SmoothNullhomotopy

/-!
# Actual smooth disk extensions in a homotopy six-sphere

Every smooth map from a sphere of dimension below six extends to a smooth
map defined on the entire ambient Euclidean space. The extension agrees
exactly on the unit-sphere boundary and is constant on a neighborhood of the
disk center. Its restriction to the actual closed unit disk is the required
disk map. Embeddedness is not asserted here.
-/

noncomputable section

open ContinuousMap
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare

variable {G M : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
  [TopologicalSpace M] [ChartedSpace G M] [IsManifold 𝓘(ℝ, G) ∞ M]

/-- Construct a smooth Euclidean extension of the original sphere map, constant near the center. -/
theorem exists_smooth_disk_extension_of_homotopySixSphere (e : M ≃ₕ SixSphere)
    {n : ℕ} (hn : n < 6) (f : C(Hemisphere.Sphere n, M)) (hf : ContMDiff (𝓡 n) 𝓘(ℝ, G) ∞ f) :
    ∃ (c : M) (F : Hemisphere.Ambient (n + 1) → M),
      ContMDiff 𝓘(ℝ, Hemisphere.Ambient (n + 1)) 𝓘(ℝ, G) ∞ F ∧
      (∀ v : Hemisphere.Sphere n, F v.1 = f v) ∧
      ∀ v, ‖v‖ ≤ 1 / 4 → F v = c := by
  have hd : Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) < 6 := by
    simpa only [finrank_euclideanSpace_fin] using hn
  obtain ⟨c, H, hH, hlo, hhi⟩ :=
    exists_smooth_nullhomotopy_of_homotopySixSphere e hd f hf
  obtain ⟨v, hv⟩ : (Hemisphere.Sphere n).Nonempty := NormedSpace.sphere_nonempty.mpr zero_le_one
  let b : Hemisphere.Sphere n := ⟨v, hv⟩
  exact ⟨c, RadialFilling.filling H b, RadialFilling.contMDiff_filling H b hf hH hlo hhi,
    RadialFilling.filling_on_sphere H b hlo, fun _ hv => RadialFilling.filling_eq_center H b hhi hv⟩

end Wikipedia.SmoothSixDPoincare
