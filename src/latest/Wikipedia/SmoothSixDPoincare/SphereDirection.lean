import Wikipedia.SmoothSixDPoincare.Hemisphere
import Wikipedia.NoExoticSixSphere.SphereNormalization

/-!
# Smooth radial direction away from the origin

The total direction map uses an arbitrary sphere point at zero. Its actual
values away from zero are normalized Euclidean vectors. Smoothness there is
proved on the open punctured space using the native sphere manifold structure.
-/

noncomputable section

open Set
open scoped ContDiff Manifold Topology

namespace Wikipedia.SmoothSixDPoincare.RadialFilling

variable {n : ℕ}

/-- Euclidean normalization into the actual sphere, with an irrelevant default value at zero. -/
def direction (b : Hemisphere.Sphere n) (v : Hemisphere.Ambient (n + 1)) : Hemisphere.Sphere n := by
  classical
  exact if hv : v = 0 then b else
    ⟨NormedSpace.normalize v, by
      simpa only [Metric.mem_sphere, dist_zero_right] using NormedSpace.norm_normalize hv⟩

theorem direction_coe (b : Hemisphere.Sphere n) {v : Hemisphere.Ambient (n + 1)} (hv : v ≠ 0) :
    (direction b v : Hemisphere.Ambient (n + 1)) = NormedSpace.normalize v := by
  classical
  simp only [direction, dif_neg hv]

/-- On the unit sphere, the direction map is exactly the identity. -/
theorem direction_of_mem_sphere (b v : Hemisphere.Sphere n) : direction b v.1 = v := by
  have hn : ‖v.1‖ = 1 := mem_sphere_zero_iff_norm.mp v.2
  have hv : v.1 ≠ 0 := by intro h; simp [h] at hn
  apply Subtype.ext
  rw [direction_coe b hv, NormedSpace.normalize_eq_self_of_norm_eq_one hn]

/-- The sphere-valued direction map is natively smooth at every nonzero vector. -/
theorem contMDiffAt_direction (b : Hemisphere.Sphere n) {v : Hemisphere.Ambient (n + 1)}
    (hv : v ≠ 0) : ContMDiffAt 𝓘(ℝ, Hemisphere.Ambient (n + 1)) (𝓡 n) ∞ (direction b) v := by
  let V : TopologicalSpace.Opens (Hemisphere.Ambient (n + 1)) :=
    ⟨{w | w ≠ 0}, isOpen_ne_fun continuous_id continuous_const⟩
  have : Fact (Module.finrank ℝ (Hemisphere.Ambient (n + 1)) = n + 1) :=
    ⟨finrank_euclideanSpace_fin⟩
  have hnorm : ContMDiff 𝓘(ℝ, Hemisphere.Ambient (n + 1))
      𝓘(ℝ, Hemisphere.Ambient (n + 1)) ∞
      (fun w : V => NormedSpace.normalize (w : Hemisphere.Ambient (n + 1))) :=
    NoExoticSixSphere.contMDiff_normalize contMDiff_subtype_val (fun w => w.2)
  have hmem (w : V) : NormedSpace.normalize (w : Hemisphere.Ambient (n + 1)) ∈
      Metric.sphere (0 : Hemisphere.Ambient (n + 1)) 1 := by
    simpa only [Metric.mem_sphere, dist_zero_right] using NormedSpace.norm_normalize w.2
  have hsphere := hnorm.codRestrict_sphere (n := n) hmem
  have hs : ContMDiff 𝓘(ℝ, Hemisphere.Ambient (n + 1)) (𝓡 n) ∞
      (fun w : V => direction b w.1) := by
    apply hsphere.congr
    intro w
    exact Subtype.ext (direction_coe b w.2)
  exact (contMDiffAt_subtype_iff (U := V) (f := direction b) (x := ⟨v, hv⟩)).mp (hs ⟨v, hv⟩)

end Wikipedia.SmoothSixDPoincare.RadialFilling
