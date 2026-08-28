import Wikipedia.HopfProblem.DegreeCollapseAdaptedHeightField
import Wikipedia.SmoothSixDPoincare.DescentResidence

/-!
# Native residence with descent required only on the compact region

The field may increase the original height elsewhere. This local form is
needed for the field after cancellation, whose descent outside the inner
neighborhood is retained but whose new global Lyapunov function has not
yet been constructed.
-/

noncomputable section

open Set Function Manifold
open scoped ContDiff Topology
open Wikipedia.SmoothSixDPoincare

namespace Wikipedia.HopfProblem.DegreeCollapse.FlowCancellation

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {f : M → ℝ} {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}

/-- Strict descent on a compact region alone gives a uniform native residence bound. -/
theorem exists_native_lyapunov_residence
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞
      (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    {C : Set M} (hC : IsCompact C)
    (hneg : ∀ x ∈ C, mvfderiv 𝓘(ℝ, E) f x (V x) < 0) :
    ∃ T : ℝ, 0 < T ∧ ∀ γ : ℝ → M, IsMIntegralCurve γ V →
      ∃ t ∈ Icc (0 : ℝ) T, γ t ∉ C := by
  by_cases hne : C.Nonempty
  swap
  · exact ⟨1, zero_lt_one, fun γ _ =>
      ⟨0, ⟨le_rfl, zero_le_one⟩, fun h => hne ⟨γ 0, h⟩⟩⟩
  have hspeed := (MorseCancellation.contMDiff_directionalDerivative hf hV).continuous
  obtain ⟨v, hv, hmaxspeed⟩ := hC.exists_isMaxOn hne hspeed.continuousOn
  let δ := -mvfderiv 𝓘(ℝ, E) f v (V v)
  have hδ : 0 < δ := neg_pos.mpr (hneg v hv)
  have hbound (x : M) (hx : x ∈ C) : mvfderiv 𝓘(ℝ, E) f x (V x) ≤ -δ := by
    have hh : mvfderiv 𝓘(ℝ, E) f x (V x) ≤ mvfderiv 𝓘(ℝ, E) f v (V v) := hmaxspeed hx
    simpa only [δ, neg_neg] using hh
  obtain ⟨p, hp, hmin⟩ := hC.exists_isMinOn hne hf.continuous.continuousOn
  obtain ⟨q, hq, hmax⟩ := hC.exists_isMaxOn hne hf.continuous.continuousOn
  let T := (f q - f p + 1) / δ
  have hpq : f p ≤ f q := hmax hp
  have hT : 0 < T := div_pos (by linarith) hδ
  have hδT : δ * T = f q - f p + 1 := by
    dsimp [T]
    field_simp [hδ.ne']
  refine ⟨T, hT, ?_⟩
  intro γ hγ
  by_contra! hstay
  have hd (t : ℝ) : HasDerivAt (f ∘ γ) (mvfderiv 𝓘(ℝ, E) f (γ t) (V (γ t))) t :=
    FlowConstruction.hasDerivAt_comp_integralCurve hf hγ t
  have hdiff : Differentiable ℝ (f ∘ γ) := fun t => (hd t).differentiableAt
  have h0 : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, hT.le⟩
  have hlast : T ∈ Icc (0 : ℝ) T := ⟨hT.le, le_rfl⟩
  have hdrop := (convex_Icc (0 : ℝ) T).image_sub_le_mul_sub_of_deriv_le
    hdiff.continuous.continuousOn hdiff.differentiableOn
    (fun t ht => by
      rw [(hd t).deriv]
      exact hbound (γ t) (hstay t (interior_subset ht))) 0 h0 T hlast hT.le
  simp only [comp_apply, sub_zero, neg_mul] at hdrop
  rw [hδT] at hdrop
  have hlo : f p ≤ f (γ T) := hmin (hstay T hlast)
  have hhi : f (γ 0) ≤ f q := hmax (hstay 0 h0)
  linarith

end Wikipedia.HopfProblem.DegreeCollapse.FlowCancellation
