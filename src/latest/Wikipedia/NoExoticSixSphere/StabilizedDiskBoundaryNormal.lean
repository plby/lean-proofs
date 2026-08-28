import Wikipedia.NoExoticSixSphere.StabilizedDiskBoundaryFrame
import Wikipedia.NoExoticSixSphere.SphereExtensionDerivative

/-!
# The stabilized boundary frame is normal to the actual disk derivative

The retained collar has no graph-coordinate derivative. Its old-coordinate
derivative lies in the original sphere tangent image. These exact facts show
that the old normal frame plus the five graph axes is perpendicular to the
disk's actual derivative, not merely to a separately specified plane family.
-/

noncomputable section

open Function Set Filter
open scoped Manifold ContDiff Topology
open Wikipedia.SmoothSixDPoincare.SphereBoundary

namespace NoExoticSixSphere.StabilizedSpanningDisk

open GLOrthonormalization Stiefel

theorem fderiv_collar_apply {N : ℕ} (b : Sphere 3) (f : Sphere 3 → Vector N)
    (hf : ContMDiff (𝓡 3) (𝓡 N) ∞ f) (s : Sphere 3) (v : Vector 4) :
    fderiv ℝ (collar b f) s.val v = coordinates N 4
      ((fderiv ℝ (SmoothSphereAmbient.extension b f) s.val v,
        fderiv ℝ (definingFunction (E := Vector 4)) s.val v), 0) := by
  have he : DifferentiableAt ℝ (SmoothSphereAmbient.extension b f) s.val :=
    (SmoothSphereAmbient.contDiff_extension b f hf).contDiffAt.differentiableAt (by simp)
  have hρ : DifferentiableAt ℝ (definingFunction (E := Vector 4)) s.val :=
    contDiff_definingFunction.contDiffAt.differentiableAt (by simp)
  have hd := (coordinates N 4).hasFDerivAt.comp s.val
    ((he.hasFDerivAt.prodMk hρ.hasFDerivAt).prodMk
      (hasFDerivAt_const (0 : ℝ × Vector 4) s.val))
  rw [show fderiv ℝ (collar b f) s.val = _ from hd.fderiv]
  rfl

theorem boundaryFrame_normal_collar {N k : ℕ} (b : Sphere 3) (f : Sphere 3 → Vector N)
    (hf : ContMDiff (𝓡 3) (𝓡 N) ∞ f) (s : Sphere 3) (a : Space N k)
    (ha : a.val.range ≤ (mfderiv (𝓡 3) (𝓡 N) f s).rangeᗮ) :
    (boundaryFrame a).val.range ≤ (fderiv ℝ (collar b f) s.val).rangeᗮ := by
  rintro _ ⟨w, rfl⟩
  apply (Submodule.mem_orthogonal _ _).mpr
  rintro _ ⟨v, rfl⟩
  change inner ℝ (fderiv ℝ (collar b f) s.val v) (boundaryFrameOperator a.val w) = 0
  rw [fderiv_collar_apply b f hf, boundaryFrameOperator_apply, inner_coordinates]
  simp only [inner_zero_right, inner_zero_left, add_zero, Prod.fst_zero, Prod.snd_zero]
  apply Submodule.inner_right_of_mem_orthogonal
    ((SmoothSphereAmbient.range_fderiv_extension_le b f hf s) ⟨v, rfl⟩)
  exact ha ⟨_, rfl⟩

/-- Any disk retaining this open collar has exactly the required normal boundary columns. -/
theorem boundaryFrame_normal_disk {N k : ℕ} (b : Sphere 3) (f : Sphere 3 → Vector N)
    (hf : ContMDiff (𝓡 3) (𝓡 N) ∞ f) (a : Sphere 3 → Space N k)
    (ha : ∀ s, (a s).val.range ≤ (mfderiv (𝓡 3) (𝓡 N) f s).rangeᗮ)
    {G : Vector 4 → Vector (N + 6)} {V : Set (Vector 4)} (hV : IsOpen V)
    (hSV : Metric.sphere 0 1 ⊆ V) (heq : EqOn G (collar b f) V) (s : Sphere 3) :
    (boundaryFrame (a s)).val.range ≤ (fderiv ℝ G s.val).rangeᗮ := by
  have he : G =ᶠ[𝓝 s.val] collar b f :=
    Filter.mem_of_superset (hV.mem_nhds (hSV s.property)) heq
  rw [he.fderiv_eq]
  exact boundaryFrame_normal_collar b f hf s (a s) (ha s)

end NoExoticSixSphere.StabilizedSpanningDisk
