import Wikipedia.NoExoticSixSphere.SphereLevelEquations
import Wikipedia.NoExoticSixSphere.SmoothSphereRadialDerivative

/-!
# The actual uncut radial extension has zero radial derivative

Local smoothness at the original sphere point suffices. Along a positive
ray the actual retraction is constant, so differentiating that ray gives
zero in the radial direction. No global smoothness of the sphere map
or any choice of ambient derivative is assumed.
-/

noncomputable section

open Filter Topology
open scoped Manifold ContDiff

namespace NoExoticSixSphere.SphereLevelEquations

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {m : ℕ} [Fact (Module.finrank ℝ E = m + 1)]

theorem fderiv_extend_radial_zero (a : UnitSphere E) (g : UnitSphere E → F)
    (x : UnitSphere E) (hg : ContMDiffAt (𝓡 m) 𝓘(ℝ, F) ∞ g x) :
    fderiv ℝ (extend a g) x.val x.val = 0 := by
  have he : (fun t : ℝ ↦ extend a g (t • x.val)) =ᶠ[𝓝 1] fun _ ↦ g x := by
    filter_upwards [Ioi_mem_nhds (by norm_num : (0 : ℝ) < 1)] with t ht
    exact congrArg g (SphereRadialRetraction.retract_pos_smul a x ht)
  have hzero : HasDerivAt (fun t : ℝ ↦ extend a g (t • x.val)) 0 1 :=
    (hasDerivAt_const (1 : ℝ) (g x)).congr_of_eventuallyEq he
  have hdiff := (contDiffAt_extend a hg).differentiableAt (by simp)
  have hline : HasDerivAt (fun t : ℝ ↦ t • x.val) x.val 1 := by
    simpa only [one_smul, id_eq] using! (hasDerivAt_id (1 : ℝ)).smul_const x.val
  have hd : HasFDerivAt (extend a g) (fderiv ℝ (extend a g) x.val)
      ((1 : ℝ) • x.val) := by simpa only [one_smul] using hdiff.hasFDerivAt
  have hchain := hd.comp_hasDerivAt 1 hline
  simpa only [one_smul] using hchain.unique hzero

end NoExoticSixSphere.SphereLevelEquations
