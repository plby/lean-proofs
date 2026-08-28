import Wikipedia.NoExoticSixSphere.SmoothSphereAmbientExtension

/-!
# The radial extension's derivative along the original sphere

Near a unit-sphere point the cutoff vanishes, so the extension factors
through the actual radial retraction. Its derivative therefore lands in
the range of the original native sphere-map derivative.
-/

noncomputable section

open Set Filter Metric
open scoped Manifold ContDiff Topology

namespace NoExoticSixSphere.SmoothSphereAmbient

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem extension_eventuallyEq_radial (b : Sphere n) (f : Sphere n → F) (s : Sphere n) :
    extension b f =ᶠ[𝓝 s.val] (f ∘ SphereRadialRetraction.retract b) := by
  have hs : (1 / 2 : ℝ) < ‖s.val‖ := by
    rw [ClosedHemisphere.unit_norm]
    norm_num
  filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hs] with x hx
  have hz : cutoff n x = 0 := (cutoff n).zero_of_le_dist (by
    change (1 / 2 : ℝ) ≤ dist x 0
    simpa only [dist_zero_right] using hx.le)
  simp only [extension, hz, sub_zero, one_smul, Function.comp_apply]

theorem range_fderiv_extension_le (b : Sphere n) (f : Sphere n → F)
    (hf : ContMDiff (𝓡 n) 𝓘(ℝ, F) ∞ f) (s : Sphere n) :
    (fderiv ℝ (extension b f) s.val).range ≤ (mfderiv (𝓡 n) 𝓘(ℝ, F) f s).range := by
  let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) = n + 1) :=
    ⟨finrank_euclideanSpace_fin⟩
  have hr := SphereRadialRetraction.contMDiffAt_retract (n := n) b
    (ne_zero_of_mem_unit_sphere s)
  have he := extension_eventuallyEq_radial b f s
  have hd : mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) 𝓘(ℝ, F) (extension b f) s.val =
      (mfderiv (𝓡 n) 𝓘(ℝ, F) f s).comp
        (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) (𝓡 n)
          (SphereRadialRetraction.retract b) s.val) := by
    rw [he.mfderiv_eq, mfderiv_comp s.val (hf.mdifferentiableAt (by simp))
      (hr.mdifferentiableAt (by simp)), SphereRadialRetraction.retract_coe]
  rw [mfderiv_eq_fderiv] at hd
  rw [hd]
  rintro _ ⟨v, rfl⟩
  exact ⟨_, rfl⟩

end NoExoticSixSphere.SmoothSphereAmbient
