import Wikipedia.HopfProblem.DegreeCollapseLowSurgeryBoundaryFrame
import Wikipedia.NoExoticSixSphere.SmoothSphereRadialCollar

/-!

# Original low-surgery normal columns on the whole radial collar

Differentiate the actual radial collar at every point of its open annulus.
The original normal columns and graph axes remain normal there, not merely
at the boundary. The smooth ambient frame extension agrees exactly with
these radial columns throughout the annulus outside its cutoff support.
-/

noncomputable section

open Function Set Filter Metric
open scoped Manifold ContDiff Topology
open Wikipedia.SmoothSixDPoincare.SphereBoundary

namespace Wikipedia.HopfProblem.DegreeCollapse.LowSurgery

open NoExoticSixSphere GLOrthonormalization Stiefel StabilizedSpanningDisk

theorem fderiv_collar_apply_at {d N : ℕ} (b : NoExoticSixSphere.Sphere d)
    (f : NoExoticSixSphere.Sphere d → Vector N)
    (hf : ContMDiff (𝓡 d) (𝓡 N) ∞ f) (x v : Vector (d + 1)) :
    fderiv ℝ (collar b f) x v = coordinates N (d + 1)
      ((fderiv ℝ (SmoothSphereAmbient.extension b f) x v,
        fderiv ℝ (definingFunction (E := Vector (d + 1))) x v), 0) := by
  have he : DifferentiableAt ℝ (SmoothSphereAmbient.extension b f) x :=
    (SmoothSphereAmbient.contDiff_extension b f hf).contDiffAt.differentiableAt (by simp)
  have hρ : DifferentiableAt ℝ (definingFunction (E := Vector (d + 1))) x :=
    contDiff_definingFunction.contDiffAt.differentiableAt (by simp)
  have hd := (coordinates N (d + 1)).hasFDerivAt.comp x
    ((he.hasFDerivAt.prodMk hρ.hasFDerivAt).prodMk
      (hasFDerivAt_const (0 : ℝ × Vector (d + 1)) x))
  rw [show fderiv ℝ (collar b f) x = _ from hd.fderiv]
  rfl

theorem boundaryFrame_normal_collar_radial {d N k : ℕ}
    (b : NoExoticSixSphere.Sphere d) (f : NoExoticSixSphere.Sphere d → Vector N)
    (hf : ContMDiff (𝓡 d) (𝓡 N) ∞ f)
    (a : NoExoticSixSphere.Sphere d → Space N k)
    (ha : ∀ s, (a s).val.range ≤ (mfderiv (𝓡 d) (𝓡 N) f s).rangeᗮ)
    {x : Vector (d + 1)} (hx : (1 / 2 : ℝ) < ‖x‖) :
    (boundaryFrame d (a (SphereRadialRetraction.retract b x))).val.range ≤
      (fderiv ℝ (collar b f) x).rangeᗮ := by
  rintro _ ⟨w, rfl⟩
  apply (Submodule.mem_orthogonal _ _).mpr
  rintro _ ⟨v, rfl⟩
  change inner ℝ (fderiv ℝ (collar b f) x v)
    (boundaryFrameOperator d (a (SphereRadialRetraction.retract b x)).val w) = 0
  rw [fderiv_collar_apply_at b f hf, boundaryFrameOperator_apply, inner_coordinates]
  simp only [inner_zero_right, inner_zero_left, add_zero, Prod.fst_zero, Prod.snd_zero]
  apply Submodule.inner_right_of_mem_orthogonal
    ((SmoothSphereAmbient.range_fderiv_extension_le_radial b f hf hx) ⟨v, rfl⟩)
  exact ha _ ⟨_, rfl⟩

theorem boundaryFrame_normal_disk_radial {d N k : ℕ}
    (b : NoExoticSixSphere.Sphere d) (f : NoExoticSixSphere.Sphere d → Vector N)
    (hf : ContMDiff (𝓡 d) (𝓡 N) ∞ f)
    (a : NoExoticSixSphere.Sphere d → Space N k)
    (ha : ∀ s, (a s).val.range ≤ (mfderiv (𝓡 d) (𝓡 N) f s).rangeᗮ)
    {G : Vector (d + 1) → Vector (N + (1 + (1 + (d + 1))))}
    {V : Set (Vector (d + 1))} (hV : IsOpen V)
    (heq : EqOn G (collar b f) V) {x : Vector (d + 1)} (hxV : x ∈ V)
    (hx : (1 / 2 : ℝ) < ‖x‖) :
    (boundaryFrame d (a (SphereRadialRetraction.retract b x))).val.range ≤
      (fderiv ℝ G x).rangeᗮ := by
  have he : G =ᶠ[𝓝 x] collar b f := Filter.mem_of_superset (hV.mem_nhds hxV) heq
  rw [he.fderiv_eq]
  exact boundaryFrame_normal_collar_radial b f hf a ha hx


variable {d N k : ℕ} (b : NoExoticSixSphere.Sphere d) (a : NoExoticSixSphere.Sphere d → Space N k)
  (has : ContMDiff (𝓡 d) 𝓘(ℝ, Vector k →L[ℝ] Vector N) ∞ (fun s ↦ (a s).val))

def boundaryFrameExtension : C(Vector (d + 1),
    Vector (k + (1 + (d + 1))) →L[ℝ] Vector (N + (1 + (1 + (d + 1))))) :=
  ⟨SmoothSphereAmbient.extension b (fun s ↦ boundaryFrameOperator d (a s).val),
    (SmoothSphereAmbient.contDiff_extension b _
      (contMDiff_boundaryFrameOperator d has)).continuous⟩

theorem contDiff_boundaryFrameExtension : ContDiff ℝ ∞ (boundaryFrameExtension b a has) :=
  SmoothSphereAmbient.contDiff_extension b _ (contMDiff_boundaryFrameOperator d has)

theorem boundaryFrameExtension_coe (s : NoExoticSixSphere.Sphere d) :
    boundaryFrameExtension b a has s.val = boundaryFrameOperator d (a s).val :=
  SmoothSphereAmbient.extension_coe b (fun s ↦ boundaryFrameOperator d (a s).val) s

theorem boundaryFrameExtension_eq_radial {x : Vector (d + 1)} (hx : (1 / 2 : ℝ) < ‖x‖) :
    boundaryFrameExtension b a has x =
      boundaryFrameOperator d (a (SphereRadialRetraction.retract b x)).val :=
  SmoothSphereAmbient.extension_eq_radial_of_half_le b
    (fun s ↦ boundaryFrameOperator d (a s).val) hx.le

theorem norm_boundaryFrameExtension {x : Vector (d + 1)} (hx : (1 / 2 : ℝ) < ‖x‖)
    (w : Vector (k + (1 + (d + 1)))) : ‖boundaryFrameExtension b a has x w‖ = ‖w‖ := by
  rw [boundaryFrameExtension_eq_radial b a has hx]
  exact norm_boundaryFrameOperator d _ w

theorem boundaryFrameExtension_normal_disk (f : NoExoticSixSphere.Sphere d → Vector N)
    (hf : ContMDiff (𝓡 d) (𝓡 N) ∞ f)
    (ha : ∀ s, (a s).val.range ≤ (mfderiv (𝓡 d) (𝓡 N) f s).rangeᗮ)
    {G : Vector (d + 1) → Vector (N + (1 + (1 + (d + 1))))}
    {V : Set (Vector (d + 1))} (hV : IsOpen V)
    (heq : EqOn G (collar b f) V) {x : Vector (d + 1)} (hxV : x ∈ V)
    (hx : (1 / 2 : ℝ) < ‖x‖) :
    (boundaryFrameExtension b a has x).range ≤ (fderiv ℝ G x).rangeᗮ := by
  rw [boundaryFrameExtension_eq_radial b a has hx]
  exact boundaryFrame_normal_disk_radial b f hf a ha hV heq hxV hx

end Wikipedia.HopfProblem.DegreeCollapse.LowSurgery
