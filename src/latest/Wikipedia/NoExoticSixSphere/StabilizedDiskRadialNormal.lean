import Wikipedia.NoExoticSixSphere.FramedSpanningDisk
import Wikipedia.NoExoticSixSphere.SmoothSphereRadialCollar

/-!
# Radial normal frames on the entire retained disk collar

The old normal columns at the radial sphere point, together with the five
graph axes, remain normal to the actual disk derivative on its open collar.
The proof uses the derivative of the retained collar formula throughout that
neighborhood; it does not extrapolate boundary normality by continuity.
-/

noncomputable section

open Function Set Filter Metric
open scoped Manifold ContDiff Topology
open Wikipedia.SmoothSixDPoincare.SphereBoundary

namespace NoExoticSixSphere.StabilizedSpanningDisk

open GLOrthonormalization Stiefel

theorem fderiv_collar_apply_at {N : ℕ} (b : Sphere 3) (f : Sphere 3 → Vector N)
    (hf : ContMDiff (𝓡 3) (𝓡 N) ∞ f) (x v : Vector 4) :
    fderiv ℝ (collar b f) x v = coordinates N 4
      ((fderiv ℝ (SmoothSphereAmbient.extension b f) x v,
        fderiv ℝ (definingFunction (E := Vector 4)) x v), 0) := by
  have he : DifferentiableAt ℝ (SmoothSphereAmbient.extension b f) x :=
    (SmoothSphereAmbient.contDiff_extension b f hf).contDiffAt.differentiableAt (by simp)
  have hρ : DifferentiableAt ℝ (definingFunction (E := Vector 4)) x :=
    contDiff_definingFunction.contDiffAt.differentiableAt (by simp)
  have hd := (coordinates N 4).hasFDerivAt.comp x
    ((he.hasFDerivAt.prodMk hρ.hasFDerivAt).prodMk
      (hasFDerivAt_const (0 : ℝ × Vector 4) x))
  rw [show fderiv ℝ (collar b f) x = _ from hd.fderiv]
  rfl

theorem boundaryFrame_normal_collar_radial {N k : ℕ}
    (b : Sphere 3) (f : Sphere 3 → Vector N) (hf : ContMDiff (𝓡 3) (𝓡 N) ∞ f)
    (a : Sphere 3 → Space N k)
    (ha : ∀ s, (a s).val.range ≤ (mfderiv (𝓡 3) (𝓡 N) f s).rangeᗮ)
    {x : Vector 4} (hx : (1 / 2 : ℝ) < ‖x‖) :
    (boundaryFrame (a (SphereRadialRetraction.retract b x))).val.range ≤
      (fderiv ℝ (collar b f) x).rangeᗮ := by
  rintro _ ⟨w, rfl⟩
  apply (Submodule.mem_orthogonal _ _).mpr
  rintro _ ⟨v, rfl⟩
  change inner ℝ (fderiv ℝ (collar b f) x v)
    (boundaryFrameOperator (a (SphereRadialRetraction.retract b x)).val w) = 0
  rw [fderiv_collar_apply_at b f hf, boundaryFrameOperator_apply, inner_coordinates]
  simp only [inner_zero_right, inner_zero_left, add_zero, Prod.fst_zero, Prod.snd_zero]
  apply Submodule.inner_right_of_mem_orthogonal
    ((SmoothSphereAmbient.range_fderiv_extension_le_radial b f hf hx) ⟨v, rfl⟩)
  exact ha _ ⟨_, rfl⟩

theorem boundaryFrame_normal_disk_radial {N k : ℕ}
    (b : Sphere 3) (f : Sphere 3 → Vector N) (hf : ContMDiff (𝓡 3) (𝓡 N) ∞ f)
    (a : Sphere 3 → Space N k)
    (ha : ∀ s, (a s).val.range ≤ (mfderiv (𝓡 3) (𝓡 N) f s).rangeᗮ)
    {G : Vector 4 → Vector (N + 6)} {V : Set (Vector 4)} (hV : IsOpen V)
    (heq : EqOn G (collar b f) V) {x : Vector 4} (hxV : x ∈ V)
    (hx : (1 / 2 : ℝ) < ‖x‖) :
    (boundaryFrame (a (SphereRadialRetraction.retract b x))).val.range ≤
      (fderiv ℝ G x).rangeᗮ := by
  have he : G =ᶠ[𝓝 x] collar b f := Filter.mem_of_superset (hV.mem_nhds hxV) heq
  rw [he.fderiv_eq]
  exact boundaryFrame_normal_collar_radial b f hf a ha hx

end NoExoticSixSphere.StabilizedSpanningDisk
