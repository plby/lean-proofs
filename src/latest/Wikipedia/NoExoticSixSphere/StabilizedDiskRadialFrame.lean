import Wikipedia.NoExoticSixSphere.StabilizedDiskRadialNormal

/-!
# Smooth ambient data for the stabilized radial boundary frame

The cutoff extension is globally smooth as an operator family, agrees with
the original boundary columns, and is an actual orthonormal normal frame on
the retained collar outside the cutoff support.
-/

noncomputable section

open Set Metric
open scoped Manifold ContDiff

namespace NoExoticSixSphere.StabilizedSpanningDisk

open GLOrthonormalization Stiefel

variable {N k : ℕ} (b : Sphere 3) (a : Sphere 3 → Space N k)
  (has : ContMDiff (𝓡 3) 𝓘(ℝ, Vector k →L[ℝ] Vector N) ∞ (fun s ↦ (a s).val))

def boundaryFrameExtension : C(Vector 4, Vector (k + 5) →L[ℝ] Vector (N + 6)) :=
  ⟨SmoothSphereAmbient.extension b (fun s ↦ boundaryFrameOperator (a s).val),
    (SmoothSphereAmbient.contDiff_extension b _
      (contMDiff_boundaryFrameOperator has)).continuous⟩

theorem contDiff_boundaryFrameExtension : ContDiff ℝ ∞ (boundaryFrameExtension b a has) :=
  SmoothSphereAmbient.contDiff_extension b _ (contMDiff_boundaryFrameOperator has)

theorem boundaryFrameExtension_coe (s : Sphere 3) :
    boundaryFrameExtension b a has s.val = boundaryFrameOperator (a s).val :=
  SmoothSphereAmbient.extension_coe b (fun s ↦ boundaryFrameOperator (a s).val) s

theorem boundaryFrameExtension_eq_radial {x : Vector 4} (hx : (1 / 2 : ℝ) < ‖x‖) :
    boundaryFrameExtension b a has x =
      boundaryFrameOperator (a (SphereRadialRetraction.retract b x)).val :=
  SmoothSphereAmbient.extension_eq_radial_of_half_le b
    (fun s ↦ boundaryFrameOperator (a s).val) hx.le

theorem norm_boundaryFrameExtension {x : Vector 4} (hx : (1 / 2 : ℝ) < ‖x‖)
    (w : Vector (k + 5)) : ‖boundaryFrameExtension b a has x w‖ = ‖w‖ := by
  rw [boundaryFrameExtension_eq_radial b a has hx]
  exact norm_boundaryFrameOperator _ w

theorem boundaryFrameExtension_normal_disk (f : Sphere 3 → Vector N)
    (hf : ContMDiff (𝓡 3) (𝓡 N) ∞ f)
    (ha : ∀ s, (a s).val.range ≤ (mfderiv (𝓡 3) (𝓡 N) f s).rangeᗮ)
    {G : Vector 4 → Vector (N + 6)} {V : Set (Vector 4)} (hV : IsOpen V)
    (heq : EqOn G (collar b f) V) {x : Vector 4} (hxV : x ∈ V)
    (hx : (1 / 2 : ℝ) < ‖x‖) :
    (boundaryFrameExtension b a has x).range ≤ (fderiv ℝ G x).rangeᗮ := by
  rw [boundaryFrameExtension_eq_radial b a has hx]
  exact boundaryFrame_normal_disk_radial b f hf a ha hV heq hxV hx

end NoExoticSixSphere.StabilizedSpanningDisk
