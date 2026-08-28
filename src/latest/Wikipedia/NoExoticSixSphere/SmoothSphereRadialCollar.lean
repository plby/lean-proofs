import Wikipedia.NoExoticSixSphere.SphereExtensionDerivative

/-!
# The actual radial derivative throughout a sphere collar

Outside the cutoff's support the smooth ambient extension is the original
sphere map composed with radial retraction. This identifies its derivative's
range at every collar point, not only at points of the unit sphere.
-/

noncomputable section

open Set Filter Metric
open scoped Manifold ContDiff Topology

namespace NoExoticSixSphere.SmoothSphereAmbient

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem extension_eq_radial_of_half_le (b : Sphere n) (f : Sphere n → F)
    {x : EuclideanSpace ℝ (Fin (n + 1))} (hx : (1 / 2 : ℝ) ≤ ‖x‖) :
    extension b f x = f (SphereRadialRetraction.retract b x) := by
  have hz : cutoff n x = 0 := (cutoff n).zero_of_le_dist (by
    change (1 / 2 : ℝ) ≤ dist x 0
    simpa only [dist_zero_right] using hx)
  simp only [extension, hz, sub_zero, one_smul]

theorem extension_eventuallyEq_radial_of_half_lt (b : Sphere n) (f : Sphere n → F)
    {x : EuclideanSpace ℝ (Fin (n + 1))} (hx : (1 / 2 : ℝ) < ‖x‖) :
    extension b f =ᶠ[𝓝 x] (f ∘ SphereRadialRetraction.retract b) := by
  filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hx] with y hy
  exact extension_eq_radial_of_half_le b f hy.le

theorem range_fderiv_extension_le_radial (b : Sphere n) (f : Sphere n → F)
    (hf : ContMDiff (𝓡 n) 𝓘(ℝ, F) ∞ f)
    {x : EuclideanSpace ℝ (Fin (n + 1))} (hx : (1 / 2 : ℝ) < ‖x‖) :
    (fderiv ℝ (extension b f) x).range ≤
      (mfderiv (𝓡 n) 𝓘(ℝ, F) f (SphereRadialRetraction.retract b x)).range := by
  let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) = n + 1) :=
    ⟨finrank_euclideanSpace_fin⟩
  have hx0 : x ≠ 0 := by
    intro heq
    norm_num [heq] at hx
  have hr := SphereRadialRetraction.contMDiffAt_retract (n := n) b hx0
  have he := extension_eventuallyEq_radial_of_half_lt b f hx
  have hd : mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) 𝓘(ℝ, F) (extension b f) x =
      (mfderiv (𝓡 n) 𝓘(ℝ, F) f (SphereRadialRetraction.retract b x)).comp
        (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) (𝓡 n)
          (SphereRadialRetraction.retract b) x) := by
    rw [he.mfderiv_eq, mfderiv_comp x (hf.mdifferentiableAt (by simp))
      (hr.mdifferentiableAt (by simp))]
  rw [mfderiv_eq_fderiv] at hd
  rw [hd]
  rintro _ ⟨v, rfl⟩
  exact ⟨_, rfl⟩

end NoExoticSixSphere.SmoothSphereAmbient
