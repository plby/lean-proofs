import Wikipedia.NoExoticSixSphere.LocalInverse
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

/-!
# Centered target coordinates at points inside the chart

Smoothness and regularity of these total coordinate functions are asserted
only at points mapped into the chart source. No assertion identifies their
zero set outside that source with the original fiber.
-/

open scoped Manifold ContDiff

namespace NoExoticSixSphere.CenteredChartCoordinates

variable {B H M C K N F : Type*}
  [NormedAddCommGroup B] [NormedSpace ℝ B] [TopologicalSpace H]
  {I : ModelWithCorners ℝ B H} [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup C] [NormedSpace ℝ C] [TopologicalSpace K]
  {J : ModelWithCorners ℝ C K} [TopologicalSpace N] [ChartedSpace K N]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def coordinates (f : M → N) (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞) (b : N) : M → F :=
  fun x ↦ c (f x) - c b

omit [TopologicalSpace M] in
theorem coordinates_eq_zero (f : M → N) (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞)
    (b : N) {x : M} (hx : f x = b) : coordinates f c b x = 0 := by
  simp only [coordinates, hx, sub_self]

theorem contMDiffAt_coordinates (f : M → N) (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞)
    (b : N) {x : M} (hf : ContMDiffAt I J ∞ f x) (hx : f x ∈ c.source) :
    ContMDiffAt I 𝓘(ℝ, F) ∞ (coordinates f c b) x := by
  have ht : ContDiff ℝ ∞ (fun y : F ↦ y - c b) := contDiff_id.sub contDiff_const
  exact ht.contMDiff.contMDiffAt.comp x
    ((c.contMDiffOn_toFun.contMDiffAt (c.open_source.mem_nhds hx)).comp x hf)

theorem surjective_mfderiv_coordinates (f : M → N)
    (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞) (b : N) {x : M}
    (hf : ContMDiffAt I J ∞ f x) (hx : f x ∈ c.source)
    (hreg : Function.Surjective (mfderiv I J f x)) :
    Function.Surjective (mfderiv I 𝓘(ℝ, F) (coordinates f c b) x) := by
  have hc : IsLocalDiffeomorphAt J 𝓘(ℝ, F) ∞ c (f x) := ⟨c, hx, fun _ _ ↦ rfl⟩
  have hdc := hc.mdifferentiableAt (by simp)
  have hdf := hf.mdifferentiableAt (by simp)
  change Function.Surjective (mfderiv I 𝓘(ℝ, F) ((c ∘ f) - fun _ ↦ c b) x)
  rw [mfderiv_sub (hdc.comp x hdf) mdifferentiableAt_const, mfderiv_const]
  let D : B →L[ℝ] F := mfderiv I 𝓘(ℝ, F) (c ∘ f) x
  change Function.Surjective (D - (0 : B →L[ℝ] F))
  rw [sub_zero]
  change Function.Surjective (mfderiv I 𝓘(ℝ, F) (c ∘ f) x)
  rw [mfderiv_comp x hdc hdf]
  exact (hc.mfderivToContinuousLinearEquiv (by simp)).surjective.comp hreg

end NoExoticSixSphere.CenteredChartCoordinates
