import Wikipedia.NoExoticSixSphere.SphereExtensionDerivative

/-!
# The actual smooth sphere extension has zero radial derivative on the sphere

Positive rays have constant radial retraction. The extension agrees locally
with that retraction, so differentiating an actual ray gives zero in its
radial direction. No extension of the tangent frame over the disk is assumed.
-/

noncomputable section

open Set Filter Metric
open scoped Manifold ContDiff Topology

namespace NoExoticSixSphere.SphereRadialRetraction

theorem retract_pos_smul {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (b s : UnitSphere E) {t : ℝ} (ht : 0 < t) : retract b (t • s.val) = s := by
  have hn : t • s.val ≠ 0 := smul_ne_zero ht.ne' (ne_zero_of_mem_unit_sphere s)
  apply Subtype.ext
  simp only [retract, dif_neg hn, NormedSpace.normalize_smul_of_pos ht]
  exact NormedSpace.normalize_eq_self_of_norm_eq_one (ClosedHemisphere.unit_norm s)

end NoExoticSixSphere.SphereRadialRetraction

namespace NoExoticSixSphere.SmoothSphereAmbient

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem fderiv_extension_radial_zero (b : Sphere n) (f : Sphere n → F)
    (hf : ContMDiff (𝓡 n) 𝓘(ℝ, F) ∞ f) (s : Sphere n) :
    fderiv ℝ (extension b f) s.val s.val = 0 := by
  have ht : Tendsto (fun t : ℝ ↦ t • s.val) (𝓝 1) (𝓝 s.val) := by
    have hc : ContinuousAt (fun t : ℝ ↦ t • s.val) 1 :=
      (continuous_id.smul continuous_const).continuousAt
    change Tendsto (fun t : ℝ ↦ t • s.val) (𝓝 1) (𝓝 ((1 : ℝ) • s.val)) at hc
    simpa only [one_smul] using hc
  have he : (fun t : ℝ ↦ extension b f (t • s.val)) =ᶠ[𝓝 1] fun _ ↦ f s := by
    filter_upwards [(extension_eventuallyEq_radial b f s).comp_tendsto ht,
      Ioi_mem_nhds (by norm_num : (0 : ℝ) < 1)] with t hE hpos
    exact hE.trans (congrArg f (SphereRadialRetraction.retract_pos_smul b s hpos))
  have hzero : HasDerivAt (fun t : ℝ ↦ extension b f (t • s.val)) 0 1 :=
    (hasDerivAt_const (1 : ℝ) (f s)).congr_of_eventuallyEq he
  have hdiff := (contDiff_extension b f hf).differentiable (by simp) s.val
  have hline : HasDerivAt (fun t : ℝ ↦ t • s.val) s.val 1 := by
    simpa only [one_smul, id_eq] using! (hasDerivAt_id (1 : ℝ)).smul_const s.val
  have hd : HasFDerivAt (extension b f) (fderiv ℝ (extension b f) s.val)
      ((1 : ℝ) • s.val) := by simpa only [one_smul] using hdiff.hasFDerivAt
  have hchain := hd.comp_hasDerivAt 1 hline
  simpa only [one_smul] using hchain.unique hzero

end NoExoticSixSphere.SmoothSphereAmbient
