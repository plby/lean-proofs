import Wikipedia.HopfProblem.DegreeCollapseFlowBandHeight
import Wikipedia.HopfProblem.DegreeCollapseLogarithmicCutoff

/-!
# Restoring a full boundary germ while retaining strict native descent

The logarithmic cutoff controls the derivative of the blending coefficient.
The error in function values need only vanish linearly in a signed flow
time. The construction retains the old function on a whole neighborhood
of the zero level and the new function outside a prescribed time collar.
-/

noncomputable section

open Set Function Filter Manifold
open scoped Topology ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.FlowCancellation

/-- A nonnegative differentiable function has zero derivative wherever it vanishes. -/
theorem deriv_eq_zero_of_nonneg_zero {χ : ℝ → ℝ} (hχ : Differentiable ℝ χ)
    (hnonneg : ∀ t, 0 ≤ χ t) {t : ℝ} (ht : χ t = 0) : deriv χ t = 0 := by
  have hm : IsLocalMin χ t := Filter.Eventually.of_forall (fun s => by
    change χ t ≤ χ s
    rw [ht]
    exact hnonneg s)
  exact hm.hasDerivAt_eq_zero (hχ t).hasDerivAt

theorem weighted_blend_neg {α a b r s z μ C δ : ℝ}
    (hα : α ∈ Icc (0 : ℝ) 1) (ha : a ≤ -μ) (hb : b ≤ -μ)
    (hC : 0 ≤ C) (hr : |r| ≤ C * |s|) (hz : |s * z| ≤ δ)
    (hsmall : C * δ < μ) : b + α * (a - b) - z * r < 0 := by
  have hbase : b + α * (a - b) ≤ -μ := by
    nlinarith [mul_nonneg hα.1 (sub_nonneg.mpr ha),
      mul_nonneg (sub_nonneg.mpr hα.2) (sub_nonneg.mpr hb)]
  have herr : |z * r| ≤ C * δ := calc
    |z * r| = |z| * |r| := abs_mul _ _
    _ ≤ |z| * (C * |s|) := mul_le_mul_of_nonneg_left hr (abs_nonneg _)
    _ = C * |s * z| := by rw [abs_mul]; ring
    _ ≤ C * δ := mul_le_mul_of_nonneg_left hz hC
  linarith [neg_abs_le (z * r)]

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]
  {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}

theorem hasDerivAt_flow_height_zero {f : M → ℝ} {x : M}
    (hf : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) f x)
    (F : Flow ℝ M) (hcurve : IsMIntegralCurve (fun t => F t x) V) :
    HasDerivAt (fun t => f (F t x)) (mvfderiv 𝓘(ℝ, E) f x (V x)) 0 := by
  have hf0 : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) f (F 0 x) := by
    rw [F.map_zero_apply]
    exact hf
  have hh := hasDerivAt_comp_native_integralCurve_at hf0 hcurve
  have he := congrArg (fun y : M => mvfderiv 𝓘(ℝ, E) f y (V y)) (F.map_zero_apply x)
  exact he ▸ hh

def descentBlend (χ : ℝ → ℝ) (θ f g : M → ℝ) (x : M) : ℝ :=
  g x + χ (θ x) * (f x - g x)

/-- The exact native derivative of the smooth blend along a complete flow. -/
theorem mvfderiv_descentBlend {χ : ℝ → ℝ} {θ f g : M → ℝ} {x : M}
    (hχ : ContDiff ℝ ∞ χ)
    (hθ : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ θ x)
    (hf : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f x)
    (hg : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g x)
    (F : Flow ℝ M) (hcurve : IsMIntegralCurve (fun t => F t x) V)
    (htime : mvfderiv 𝓘(ℝ, E) θ x (V x) = -1) :
    mvfderiv 𝓘(ℝ, E) (descentBlend χ θ f g) x (V x) =
      mvfderiv 𝓘(ℝ, E) g x (V x) + χ (θ x) *
        (mvfderiv 𝓘(ℝ, E) f x (V x) - mvfderiv 𝓘(ℝ, E) g x (V x)) -
        deriv χ (θ x) * (f x - g x) := by
  have dθ := hasDerivAt_flow_height_zero (hθ.mdifferentiableAt (by simp)) F hcurve
  have df := hasDerivAt_flow_height_zero (hf.mdifferentiableAt (by simp)) F hcurve
  have dg := hasDerivAt_flow_height_zero (hg.mdifferentiableAt (by simp)) F hcurve
  rw [htime] at dθ
  have dχ := ((hχ.differentiable (by simp)) (θ (F 0 x))).hasDerivAt.comp 0 dθ
  have db := dg.add (dχ.mul (df.sub dg))
  have hb : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (descentBlend χ θ f g) x :=
    hg.add ((hχ.contMDiff.contMDiffAt.comp x hθ).mul (hf.sub hg))
  have dn := hasDerivAt_flow_height_zero (hb.mdifferentiableAt (by simp)) F hcurve
  have he := dn.unique db
  simp only [Pi.sub_apply, Function.comp_apply, F.map_zero_apply] at he
  exact he.trans (by ring)

/-- Construct a smooth, strictly descending blend on an actual open native domain.
The stated quantitative collar hypotheses are not silently inferred from boundary values. -/
theorem exists_native_descent_blend {U : Set M} (hU : IsOpen U) {θ f g : M → ℝ}
    (hθ : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ θ U)
    (hf : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f U)
    (hg : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g U)
    (F : Flow ℝ M) (hcurve : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    (htime : ∀ x ∈ U, mvfderiv 𝓘(ℝ, E) θ x (V x) = -1)
    (hgneg : ∀ x ∈ U, mvfderiv 𝓘(ℝ, E) g x (V x) < 0)
    {ε μ C : ℝ} (hε : 0 < ε) (hμ : 0 < μ) (hC : 0 ≤ C)
    (hcollar : ∀ x ∈ U, |θ x| < ε →
      mvfderiv 𝓘(ℝ, E) f x (V x) ≤ -μ ∧
      mvfderiv 𝓘(ℝ, E) g x (V x) ≤ -μ ∧ |f x - g x| ≤ C * |θ x|) :
    ∃ b : M → ℝ, ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ b U ∧
      (∀ x ∈ U, mvfderiv 𝓘(ℝ, E) b x (V x) < 0) ∧
      (∀ x ∈ U, θ x = 0 → b =ᶠ[𝓝 x] f) ∧
      (∀ x, ε ≤ |θ x| → b x = g x) ∧
      ∀ x ∈ U, ε < |θ x| → b =ᶠ[𝓝 x] g := by
  let δ := μ / (C + 1)
  have hδ : 0 < δ := div_pos hμ (by positivity)
  have hsmall : C * δ < μ := by
    dsimp [δ]
    rw [← mul_div_assoc, div_lt_iff₀ (by positivity : 0 < C + 1)]
    nlinarith
  obtain ⟨χ, hχ, -, hone, hzero, hrange, hweight⟩ := exists_logarithmic_cutoff hε hδ
  let b := descentBlend χ θ f g
  have hb : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ b U :=
    hg.add ((hχ.contMDiff.comp_contMDiffOn hθ).mul (hf.sub hg))
  have hout (x : M) (hx : ε ≤ |θ x|) : b x = g x := by
    simp only [b, descentBlend, hzero _ hx, zero_mul, add_zero]
  refine ⟨b, hb, ?_, ?_, hout, ?_⟩
  · intro x hx
    have hder := mvfderiv_descentBlend hχ
      ((hθ x hx).contMDiffAt (hU.mem_nhds hx))
      ((hf x hx).contMDiffAt (hU.mem_nhds hx))
      ((hg x hx).contMDiffAt (hU.mem_nhds hx)) F (hcurve x) (htime x hx)
    change mvfderiv 𝓘(ℝ, E) (descentBlend χ θ f g) x (V x) < 0
    rw [hder]
    by_cases hnear : |θ x| < ε
    · obtain ⟨hdf, hdg, hdiff⟩ := hcollar x hx hnear
      exact weighted_blend_neg (hrange _) hdf hdg hC hdiff (hweight _).le hsmall
    · have hz := hzero (θ x) (le_of_not_gt hnear)
      have hdχ := deriv_eq_zero_of_nonneg_zero (hχ.differentiable (by simp))
        (fun t => (hrange t).1) hz
      simpa only [hz, hdχ, zero_mul, add_zero, sub_zero] using hgneg x hx
  · intro x hx hxzero
    have ht : ContinuousAt θ x := (hθ x hx).continuousWithinAt.continuousAt (hU.mem_nhds hx)
    have hone' : ∀ᶠ t in 𝓝 (θ x), χ t = 1 := by simpa only [hxzero] using hone
    filter_upwards [ht.eventually hone'] with y hy
    change g y + χ (θ y) * (f y - g y) = f y
    rw [hy]
    ring
  · intro x hx hxout
    have ht : ContinuousAt (fun y => |θ y|) x :=
      ((hθ x hx).continuousWithinAt.continuousAt (hU.mem_nhds hx)).abs
    filter_upwards [ht (eventually_gt_nhds hxout)] with y hy
    exact hout y hy.le

end Wikipedia.HopfProblem.DegreeCollapse.FlowCancellation
