import Wikipedia.NoExoticSixSphere.SphereExtensionWithHeight

/-!
# Joint smoothness of the radial extension and normal-height collar

A smoothly varying sphere map gives a jointly smooth ambient extension. At
the zero vector the cutoff vanishes on one neighborhood in the entire
parameter--vector product, not merely on each parameter slice.
-/

noncomputable section

open Function Filter Topology
open scoped Manifold ContDiff

namespace NoExoticSixSphere

variable {P F : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {n : ℕ}

namespace SmoothSphereAmbient

theorem contDiff_extension_family (b : Sphere n) (f : P → Sphere n → F)
    (hf : ContMDiff (𝓘(ℝ, P).prod (𝓡 n)) 𝓘(ℝ, F) ∞ (uncurry f)) :
    ContDiff ℝ ∞ (fun q : P × EuclideanSpace ℝ (Fin (n + 1)) ↦ extension b (f q.1) q.2) := by
  let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) = n + 1) :=
    ⟨finrank_euclideanSpace_fin⟩
  have hχ : ContDiff ℝ ∞ (fun q : P × EuclideanSpace ℝ (Fin (n + 1)) ↦ cutoff n q.2) :=
    (cutoff n).contDiff.comp contDiff_snd
  rw [contDiff_iff_contDiffAt]
  rintro ⟨t, x⟩
  by_cases hx : x = 0
  · subst x
    have he : (fun q : P × EuclideanSpace ℝ (Fin (n + 1)) ↦ extension b (f q.1) q.2)
        =ᶠ[𝓝 (t, 0)] (fun _ ↦ (0 : F)) := by
      filter_upwards [continuous_snd.continuousAt.tendsto.eventually
        (cutoff n).eventuallyEq_one] with q hq
      simp only [extension, hq, Pi.one_apply, sub_self, zero_smul]
    exact contDiffAt_const.congr_of_eventuallyEq he
  · have hr : ContMDiffAt 𝓘(ℝ, P × EuclideanSpace ℝ (Fin (n + 1))) (𝓡 n) ∞
        (fun q ↦ SphereRadialRetraction.retract b q.2) (t, x) :=
      (SphereRadialRetraction.contMDiffAt_retract b hx).comp (t, x)
        contDiffAt_snd.contMDiffAt
    have hs : ContDiffAt ℝ ∞
        (fun q : P × EuclideanSpace ℝ (Fin (n + 1)) ↦
          f q.1 (SphereRadialRetraction.retract b q.2)) (t, x) :=
      (hf.contMDiffAt.comp (t, x) (contDiffAt_fst.contMDiffAt.prodMk hr)).contDiffAt
    exact (contDiffAt_const.sub hχ.contDiffAt).smul hs

end SmoothSphereAmbient

namespace SphereExtensionWithHeight

theorem contDiff_map_family (b : Sphere n) (f : P → Sphere n → F)
    (hf : ContMDiff (𝓘(ℝ, P).prod (𝓡 n)) 𝓘(ℝ, F) ∞ (uncurry f)) :
    ContDiff ℝ ∞ (fun q : P × EuclideanSpace ℝ (Fin (n + 1)) ↦ map b (f q.1) q.2) :=
  (SmoothSphereAmbient.contDiff_extension_family b f hf).prodMk
    (Wikipedia.SmoothSixDPoincare.SphereBoundary.contDiff_definingFunction.comp
      contDiff_snd)

end SphereExtensionWithHeight

end NoExoticSixSphere
