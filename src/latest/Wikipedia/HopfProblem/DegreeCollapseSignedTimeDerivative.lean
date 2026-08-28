import Wikipedia.HopfProblem.DegreeCollapseSmoothSignedTime

/-!
# The actual derivative of signed hitting time along the native field

The affine translation law gives derivative minus one. A local manifold
chain rule identifies this with the actual native directional derivative,
without assuming the signed time is smooth outside its open basin.
-/

noncomputable section

open Set Function Manifold
open scoped Topology ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.FlowCancellation

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]

/-- The native height chain rule needs differentiability only at the curve point. -/
theorem hasDerivAt_comp_native_integralCurve_at {f : M → ℝ}
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x} {γ : ℝ → M} {t : ℝ}
    (hf : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) f (γ t)) (hγ : IsMIntegralCurve γ V) :
    HasDerivAt (f ∘ γ) (mvfderiv 𝓘(ℝ, E) f (γ t) (V (γ t))) t := by
  have hd := hf.hasMFDerivAt.comp t (hγ t)
  rw [hasDerivAt_iff_hasFDerivAt]
  apply hasMFDerivAt_iff_hasFDerivAt.mp
  apply hd.congr_mfderiv
  apply ContinuousLinearMap.ext
  intro r
  change (mvfderiv 𝓘(ℝ, E) f (γ t))
    ((NormedSpace.fromTangentSpace t r) • V (γ t)) =
    (NormedSpace.fromTangentSpace t r) • (mvfderiv 𝓘(ℝ, E) f (γ t)) (V (γ t))
  exact map_smul _ _ _

variable [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M]
  {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}

/-- Signed time has native directional derivative exactly minus one throughout its basin. -/
theorem mvfderiv_signedLevelTime {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞
      (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hcurve : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    {c : ℝ} (hboundary : ∀ x, f x = c → mvfderiv 𝓘(ℝ, E) f x (V x) < 0)
    {x : M} (hx : x ∈ levelBasin F f c) :
    mvfderiv 𝓘(ℝ, E) (signedLevelTime F f c) x (V x) = -1 := by
  obtain ⟨hB, hsmooth, hshift⟩ := smooth_signed_level_time hf hV F hcurve hboundary
  have hlocal := (hsmooth x hx).contMDiffAt (hB.mem_nhds hx)
  have hlocal0 : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) (signedLevelTime F f c) (F 0 x) := by
    rw [F.map_zero_apply]
    exact hlocal.mdifferentiableAt (by simp)
  have hd := hasDerivAt_comp_native_integralCurve_at hlocal0 (hcurve x)
  have heq : (signedLevelTime F f c ∘ (fun t => F t x)) =
      fun t : ℝ => signedLevelTime F f c x - t := funext (hshift x hx)
  rw [heq] at hd
  have hh := hd.unique ((hasDerivAt_id (0 : ℝ)).const_sub (signedLevelTime F f c x))
  have he := congrArg
    (fun y : M => mvfderiv 𝓘(ℝ, E) (signedLevelTime F f c) y (V y))
    (F.map_zero_apply x)
  exact he.symm.trans hh

end Wikipedia.HopfProblem.DegreeCollapse.FlowCancellation
