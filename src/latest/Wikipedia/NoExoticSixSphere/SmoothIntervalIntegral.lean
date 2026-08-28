import Wikipedia.NoExoticSixSphere.TwoParameterCalculus
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Differentiating a smooth family of integrals on a compact interval

Joint continuity of the integrand and its parameter derivative supplies all
measurability and domination hypotheses. The bound comes from a compact
rectangle around the parameter, not from an added analytic assumption.
-/

open scoped Topology ContDiff Interval
open MeasureTheory Set Filter

namespace NoExoticSixSphere.SmoothIntervalIntegral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem hasDerivAt_integral_of_continuous {f g : ℝ × ℝ → E}
    (hf : Continuous f) (hg : Continuous g)
    (hd : ∀ s t, HasDerivAt (fun r ↦ f (r, t)) (g (s, t)) s)
    (s l u : ℝ) :
    HasDerivAt (fun r ↦ ∫ t in l..u, f (r, t)) (∫ t in l..u, g (s, t)) s := by
  have hfc (r : ℝ) : Continuous (fun t ↦ f (r, t)) :=
    hf.comp (continuous_const.prodMk continuous_id)
  have hgc (r : ℝ) : Continuous (fun t ↦ g (r, t)) :=
    hg.comp (continuous_const.prodMk continuous_id)
  have hK : IsCompact (Icc (s - 1) (s + 1) ×ˢ uIcc l u) :=
    isCompact_Icc.prod isCompact_uIcc
  obtain ⟨B, hB⟩ := hK.bddAbove_image hg.norm.continuousOn
  have hs : Icc (s - 1) (s + 1) ∈ 𝓝 s := Icc_mem_nhds (by linarith) (by linarith)
  refine (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun r t ↦ f (r, t)) (F' := fun r t ↦ g (r, t))
    (bound := fun _ ↦ B) hs ?_ ((hfc s).intervalIntegrable l u) ?_ ?_
    intervalIntegrable_const ?_).2
  · exact Filter.Eventually.of_forall (fun r ↦ (hfc r).aestronglyMeasurable)
  · exact (hgc s).aestronglyMeasurable
  · exact Filter.Eventually.of_forall (fun t ht r hr ↦
      hB (mem_image_of_mem (fun p ↦ ‖g p‖) ⟨hr, uIoc_subset_uIcc ht⟩))
  · exact Filter.Eventually.of_forall (fun t _ r _ ↦ hd r t)

theorem hasDerivAt_integral {f : ℝ × ℝ → E} (hf : ContDiff ℝ ∞ f)
    (s l u : ℝ) :
    HasDerivAt (fun r ↦ ∫ t in l..u, f (r, t))
      (∫ t in l..u, TwoParameterCalculus.first f (s, t)) s :=
  hasDerivAt_integral_of_continuous hf.continuous
    (TwoParameterCalculus.contDiff_first hf).continuous
    (fun r t ↦ TwoParameterCalculus.hasDerivAt_first
      ((hf.differentiable (by simp)) (r, t))) s l u

end NoExoticSixSphere.SmoothIntervalIntegral
