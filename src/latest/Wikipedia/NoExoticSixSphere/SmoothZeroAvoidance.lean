import Wikipedia.NoExoticSixSphere.ManifoldImageDimension
import Mathlib.Geometry.Manifold.SmoothApprox

/-!
# Small smooth zero-avoiding approximations in higher dimension

Smooth approximation followed by a small constant translation avoids zero:
the complement of the smooth image is dense when the target dimension is
strictly larger than the source dimension.
-/

open Set Module
open scoped Manifold ContDiff Topology

namespace NoExoticSixSphere

variable {B H M F : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
  [FiniteDimensional ℝ B] [TopologicalSpace H] {I : ModelWithCorners ℝ B H}
  [I.Boundaryless] [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

theorem exists_smooth_nonzero_approx (f : C(M, F)) (ε : ℝ) (hε : 0 < ε)
    (hd : finrank ℝ B < finrank ℝ F) :
    ∃ g : C(M, F), ContMDiff I 𝓘(ℝ, F) ∞ g ∧
      (∀ x, g x ≠ 0) ∧ ∀ x, dist (g x) (f x) < ε := by
  have hhalf : 0 < ε / 2 := by linarith
  obtain ⟨h, hh, -⟩ := f.continuous.exists_contMDiff_approx I (⊤ : ℕ∞)
    (ε := fun _ ↦ ε / 2) continuous_const (fun _ ↦ hhalf)
  have hdense : Dense (range h)ᶜ := by
    simpa only [image_univ] using
      dense_compl_manifold_image isOpen_univ h.contMDiff.contMDiffOn hd
  obtain ⟨a, ha, hdist⟩ := Metric.mem_closure_iff.mp (hdense (0 : F)) (ε / 2) hhalf
  have haNorm : ‖a‖ < ε / 2 := by simpa only [dist_zero_left, dist_zero_right] using hdist
  let g : C(M, F) := ⟨fun x ↦ h x - a, h.contMDiff.continuous.sub continuous_const⟩
  refine ⟨g, h.contMDiff.sub contMDiff_const, ?_, ?_⟩
  · intro x hx
    have he : h x = a := sub_eq_zero.mp hx
    exact ha ⟨x, he⟩
  · intro x
    have hnorm : ‖h x - a - f x‖ ≤ ‖h x - f x‖ + ‖a‖ := by
      have he : h x - a - f x = (h x - f x) - a := by abel
      rw [he]
      exact norm_sub_le _ _
    change dist (h x - a) (f x) < ε
    rw [dist_eq_norm]
    have hhx : ‖h x - f x‖ < ε / 2 := by simpa only [dist_eq_norm] using hh x
    linarith

end NoExoticSixSphere
