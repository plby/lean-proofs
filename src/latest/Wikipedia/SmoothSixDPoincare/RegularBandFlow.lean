import Wikipedia.SmoothSixDPoincare.PrescribedDerivativeField
import Wikipedia.SmoothSixDPoincare.CompactFlow
import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationTransportCutoff

/-!
# A constructed flow with controlled height on a regular band

For a compact band containing no critical points, choose a smooth real cutoff
equal to one near the band and supported away from all critical values.
The resulting genuine global field and flow satisfy the scalar equation
`d/dt f(F(t,x)) = φ(f(F(t,x)))`, with `φ = 1` near the band.
-/

noncomputable section

open Set Manifold
open Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationTransport
open scoped ContDiff Topology

namespace Wikipedia.SmoothSixDPoincare.FlowConstruction

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] in
/-- Differentiate the original function along a native integral curve. -/
theorem hasDerivAt_comp_integralCurve {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    {v : (x : M) → TangentSpace 𝓘(ℝ, E) x} {γ : ℝ → M}
    (hγ : IsMIntegralCurve γ v) (t : ℝ) :
    HasDerivAt (f ∘ γ) (mvfderiv 𝓘(ℝ, E) f (γ t) (v (γ t))) t := by
  have hc := (hf.mdifferentiableAt (by simp)).hasMFDerivAt.comp t (hγ t)
  rw [hasDerivAt_iff_hasFDerivAt]
  apply hasMFDerivAt_iff_hasFDerivAt.mp
  apply hc.congr_mfderiv
  apply ContinuousLinearMap.ext
  intro r
  change (mvfderiv 𝓘(ℝ, E) f (γ t))
      ((NormedSpace.fromTangentSpace t r) • v (γ t)) =
    (NormedSpace.fromTangentSpace t r) • (mvfderiv 𝓘(ℝ, E) f (γ t)) (v (γ t))
  exact map_smul _ _ _

variable [T2Space M] [CompactSpace M]

/-- A regular band admits a global smooth field whose derivative of `f` is a scalar cutoff. -/
theorem exists_regularBandField {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) {a b : ℝ}
    (hband : ∀ x, f x ∈ Icc a b → x ∉ ManifoldMorse.criticalPoints E f) :
    ∃ (φ : ℝ → ℝ) (W : Set ℝ), ContDiff ℝ ∞ φ ∧ IsOpen W ∧ Icc a b ⊆ W ∧
      EqOn φ (fun _ => 1) W ∧ ∃ V : (x : M) → TangentSpace 𝓘(ℝ, E) x,
        ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞
          (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)) ∧
        ∀ x, mvfderiv 𝓘(ℝ, E) f x (V x) = φ (f x) := by
  let B := f '' ManifoldMorse.criticalPoints E f
  have hB : IsClosed B :=
    ((ManifoldMorse.criticalPoints_isClosed hf).isCompact.image hf.continuous).isClosed
  have hAB : Icc a b ⊆ Bᶜ := by
    intro y hy
    rintro ⟨x, hx, rfl⟩
    exact hband x hy hx
  obtain ⟨φ, hφ, hφB, W, hW, hAW, -, hφW⟩ :=
    exists_smooth_cutoff_near_closed isClosed_Icc hB.isOpen_compl hAB
  have hχ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (φ ∘ f) := hφ.contMDiff.comp hf
  have hsupp : tsupport (φ ∘ f) ⊆ (ManifoldMorse.criticalPoints E f)ᶜ := by
    intro x hx hcrit
    have hxφ := tsupport_comp_subset_preimage φ hf.continuous hx
    exact hφB hxφ ⟨x, hcrit, rfl⟩
  obtain ⟨V, hV, hVφ⟩ := exists_prescribedDerivativeField hf hχ hsupp
  exact ⟨φ, W, hφ, hW, hAW, hφW, V, hV, hVφ⟩

/-- Construct a global continuous flow with a unit-speed scalar height equation near the band. -/
theorem exists_regularBandFlow {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) {a b : ℝ}
    (hband : ∀ x, f x ∈ Icc a b → x ∉ ManifoldMorse.criticalPoints E f) :
    ∃ (φ : ℝ → ℝ) (W : Set ℝ) (F : Flow ℝ M),
      ContDiff ℝ ∞ φ ∧ IsOpen W ∧ Icc a b ⊆ W ∧ EqOn φ (fun _ => 1) W ∧
      ∀ x t, HasDerivAt (fun s => f (F s x)) (φ (f (F t x))) t := by
  obtain ⟨φ, W, hφ, hW, hAW, hφW, V, hV, hVφ⟩ := exists_regularBandField hf hband
  have hV₁ : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1
      (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)) := hV.of_le (by simp)
  refine ⟨φ, W, compactFlow hV₁, hφ, hW, hAW, hφW, ?_⟩
  intro x t
  have hd := hasDerivAt_comp_integralCurve hf (isMIntegralCurve_compactFlow hV₁ x) t
  rw [hVφ] at hd
  exact hd

end Wikipedia.SmoothSixDPoincare.FlowConstruction
