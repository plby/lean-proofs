import Wikipedia.HopfProblem.DegreeCollapseNativeDescentBlend
import Wikipedia.HopfProblem.DegreeCollapseCompactFlowTube
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Constructed uniform bounds on a native signed-time collar

The compact boundary level and continuity of both actual directional
derivatives construct a uniform negative margin on a whole time tube.
A compact bound on the derivative of the difference, followed by the
mean value theorem along the original flow, constructs the required
linear value-error bound. No quantitative collar estimate is assumed.
-/

noncomputable section

open Set Function Filter Manifold
open scoped Topology ContDiff
open Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationTransport

namespace Wikipedia.HopfProblem.DegreeCollapse.FlowCancellation

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}

/-- Directional differentiation is smooth on an open native domain. -/
theorem contMDiffOn_directionalDerivative {U : Set M} (hU : IsOpen U) {g : M → ℝ}
    (hg : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g U)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞
      (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M))) :
    ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞
      (fun x => mvfderiv 𝓘(ℝ, E) g x (V x)) U := by
  have ht := (hg.contMDiffOn_tangentMapWithin (m := ∞) (by simp) hU.uniqueMDiffOn).comp
    hV.contMDiffOn (fun x hx => hx)
  have hh := (contMDiff_snd_tangentBundle_modelSpace ℝ 𝓘(ℝ, ℝ)).comp_contMDiffOn ht
  apply hh.congr
  intro x hx
  change (NormedSpace.fromTangentSpace (g x)) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) g x (V x)) =
    (NormedSpace.fromTangentSpace (g x)) (mfderivWithin 𝓘(ℝ, E) 𝓘(ℝ, ℝ) g U x (V x))
  rw [mfderivWithin_of_isOpen hU hx]

variable [CompactSpace M]

/-- Boundary values, boundary descent, and compactness construct all the
quantitative estimates required by the logarithmic native blend. -/
theorem exists_native_time_collar_bounds {U : Set M} (hU : IsOpen U) {f g : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hg : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g U)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞
      (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hcurve : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    {c : ℝ} (hlevel : {x | f x = c} ⊆ U) (hbasin : U ⊆ levelBasin F f c)
    (heq : ∀ x, f x = c → g x = f x)
    (hfc : ∀ x, f x = c → mvfderiv 𝓘(ℝ, E) f x (V x) < 0)
    (hgc : ∀ x, f x = c → mvfderiv 𝓘(ℝ, E) g x (V x) < 0) :
    ∃ ε μ C : ℝ, 0 < ε ∧ 0 < μ ∧ 0 ≤ C ∧
      ∀ x ∈ U, |signedLevelTime F f c x| < ε →
        mvfderiv 𝓘(ℝ, E) f x (V x) ≤ -μ ∧
        mvfderiv 𝓘(ℝ, E) g x (V x) ≤ -μ ∧
        |f x - g x| ≤ C * |signedLevelTime F f c x| := by
  let S : Set M := {x | f x = c}
  have hS : IsCompact S := (isClosed_eq hf.continuous continuous_const).isCompact
  let Df (x : M) := mvfderiv 𝓘(ℝ, E) f x (V x)
  let Dg (x : M) := mvfderiv 𝓘(ℝ, E) g x (V x)
  have hDf : Continuous Df := (MorseCancellation.contMDiff_directionalDerivative hf hV).continuous
  have hDg : ContinuousOn Dg U := (contMDiffOn_directionalDerivative hU hg hV).continuousOn
  have hmax : ContinuousOn (fun x => max (Df x) (Dg x)) U :=
    continuous_max.comp_continuousOn (hDf.continuousOn.prodMk hDg)
  obtain ⟨μ, hμ, hmargin⟩ := exists_compact_negative_margin hS (hmax.mono hlevel)
    (fun x hx => max_lt (hfc x hx) (hgc x hx))
  let N : Set M := U ∩ (fun x => max (Df x) (Dg x)) ⁻¹' Iio (-μ)
  have hN : IsOpen N := hmax.isOpen_inter_preimage hU isOpen_Iio
  have hSN : S ⊆ N := fun x hx => ⟨hlevel hx, hmargin x hx⟩
  obtain ⟨ε, hε, htube⟩ := exists_flowTube_subset F hS hN hSN
  let K := flowTube F S ε
  have hK : IsCompact K := isCompact_flowTube F hS ε
  have hKU : K ⊆ U := fun x hx => (htube hx).1
  obtain ⟨C₀, hC₀⟩ := hK.exists_bound_of_continuousOn
    (hDf.continuousOn.sub (hDg.mono hKU))
  let C : ℝ := max C₀ 0
  have hC : 0 ≤ C := le_max_right _ _
  have hbound (x : M) (hx : x ∈ K) : ‖Df x - Dg x‖ ≤ C :=
    (hC₀ x hx).trans (le_max_left _ _)
  refine ⟨ε, μ, C, hε, hμ, hC, ?_⟩
  intro x hx hxε
  have hxK : x ∈ K := mem_flowTube_of_signedTime F f c (hbasin hx) hxε.le
  have hxN := htube hxK
  have hneg : max (Df x) (Dg x) < -μ := hxN.2
  refine ⟨(lt_of_le_of_lt (le_max_left _ _) hneg).le,
    (lt_of_le_of_lt (le_max_right _ _) hneg).le, ?_⟩
  let θ := signedLevelTime F f c x
  let y := F θ x
  have hy : f y = c := signedLevelTime_hits F f c (hbasin hx)
  have hpoint (t : ℝ) (ht : t ∈ Icc (-ε) ε) : F t y ∈ K :=
    ⟨(t, y), ⟨ht, hy⟩, rfl⟩
  let ℓ (t : ℝ) := f (F t y) - g (F t y)
  have hd (t : ℝ) (ht : t ∈ Icc (-ε) ε) :
      HasDerivAt ℓ (Df (F t y) - Dg (F t y)) t := by
    have hgpoint := ((hg (F t y) (hKU (hpoint t ht))).contMDiffAt
      (hU.mem_nhds (hKU (hpoint t ht)))).mdifferentiableAt (by simp)
    exact (hasDerivAt_comp_native_integralCurve_at
      (hf.mdifferentiableAt (by simp)) (hcurve y)).sub
      (hasDerivAt_comp_native_integralCurve_at hgpoint (hcurve y))
  have h0 : (0 : ℝ) ∈ Icc (-ε) ε := ⟨by linarith, hε.le⟩
  have hθ : -θ ∈ Icc (-ε) ε := by
    constructor <;> linarith [(abs_lt.mp hxε).1, (abs_lt.mp hxε).2]
  have hmvt := (convex_Icc (-ε) ε).norm_image_sub_le_of_norm_deriv_le
    (fun t ht => (hd t ht).differentiableAt)
    (fun t ht => by rw [(hd t ht).deriv]; exact hbound _ (hpoint t ht)) h0 hθ
  have hreturn : F (-θ) y = x := by
    dsimp [y]
    rw [← F.map_add, neg_add_cancel, F.map_zero_apply]
  simpa only [ℓ, F.map_zero_apply, hreturn, heq y hy, sub_self, sub_zero,
    Real.norm_eq_abs, abs_neg] using hmvt

end Wikipedia.HopfProblem.DegreeCollapse.FlowCancellation
