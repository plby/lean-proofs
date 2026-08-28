import Wikipedia.HopfProblem.DegreeCollapseSignedLevelTime
import Wikipedia.HopfProblem.DegreeCollapseNativeImplicitTime
import Wikipedia.HopfProblem.DegreeCollapseGlobalFlowSmoothness
import Wikipedia.HopfProblem.DegreeCollapseAdaptedHeightField

/-!
# Smooth signed hitting time on the actual open level basin

The genuine joint flow is smooth. A transverse crossing constructs a
native implicit root germ at each point of the basin, proving that the
basin is open. Uniqueness identifies the chosen signed time with that
smooth germ. Its exact affine translation law is retained.
-/

noncomputable section

open Set Function Filter Manifold
open scoped Topology ContDiff
open Wikipedia.SmoothSixDPoincare

namespace Wikipedia.HopfProblem.DegreeCollapse.FlowCancellation

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M]
  {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}

/-- The actual level basin is open and its signed hitting time is smooth in the original atlas. -/
theorem smooth_signed_level_time {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞
      (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hcurve : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    {c : ℝ} (hboundary : ∀ x, f x = c → mvfderiv 𝓘(ℝ, E) f x (V x) < 0) :
    IsOpen (levelBasin F f c) ∧
      ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (signedLevelTime F f c) (levelBasin F f c) ∧
      ∀ x ∈ levelBasin F f c, ∀ s : ℝ,
        signedLevelTime F f c (F s x) = signedLevelTime F f c x - s := by
  let D (x : M) := mvfderiv 𝓘(ℝ, E) f x (V x)
  have hD : Continuous D := (MorseCancellation.contMDiff_directionalDerivative hf hV).continuous
  have hder (x : M) (t : ℝ) : HasDerivAt (fun s => f (F s x)) (D (F t x)) t :=
    FlowConstruction.hasDerivAt_comp_integralCurve hf (hcurve x) t
  have hH : ContMDiff (𝓘(ℝ, E).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun q : M × ℝ => f (F q.2 q.1)) :=
    hf.comp (SmoothODE.contMDiff_native_flow hV F hcurve)
  have hgerm (p : M) (hp : p ∈ levelBasin F f c) :
      ∃ θ : M → ℝ, ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ θ p ∧
        ∀ᶠ q in 𝓝 p, f (F (θ q) q) = c := by
    let t := signedLevelTime F f c p
    have hhit : f (F t p) = c := signedLevelTime_hits F f c hp
    obtain ⟨θ, -, hθ, heq⟩ := exists_native_smooth_time_germ hH.contMDiffAt hhit
      (hder p t) (hboundary (F t p) hhit).ne
    exact ⟨θ, hθ, heq⟩
  have hB : IsOpen (levelBasin F f c) := by
    apply isOpen_iff_mem_nhds.mpr
    intro p hp
    obtain ⟨θ, -, heq⟩ := hgerm p hp
    exact heq.mono (fun q hq => ⟨θ q, hq⟩)
  refine ⟨hB, ?_, ?_⟩
  · intro p hp
    obtain ⟨θ, hθ, heq⟩ := hgerm p hp
    apply ContMDiffAt.contMDiffWithinAt
    apply hθ.congr_of_eventuallyEq
    filter_upwards [heq] with q hq
    exact signedLevelTime_eq_of_level F hf.continuous hD hder hboundary hq
  · intro x hx s
    exact signedLevelTime_flow F hf.continuous hD hder hboundary hx s

end Wikipedia.HopfProblem.DegreeCollapse.FlowCancellation
