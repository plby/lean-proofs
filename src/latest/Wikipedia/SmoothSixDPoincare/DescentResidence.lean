import Wikipedia.SmoothSixDPoincare.DescendingFlow
import Mathlib.Topology.Order.Compact

/-!
# Uniform bounded residence in a compact regular region

For a smooth descending field, its derivative of the original function is
continuous. Compactness bounds that negative derivative away from zero on
any compact subset of the regular locus. The mean value theorem then gives
a uniform time by which every integral curve must leave that subset.
-/

noncomputable section

open Set Manifold
open scoped ContDiff Topology

namespace Wikipedia.SmoothSixDPoincare.FlowConstruction

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {f : M → ℝ} {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}

/-- The actual directional derivative along a smooth native field is continuous. -/
theorem continuous_mvfderiv_field
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞
      (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M))) :
    Continuous (fun x => mvfderiv 𝓘(ℝ, E) f x (V x)) := by
  have ht := (hf.continuous_tangentMap (by simp)).comp hV.continuous
  have hp := (tangentBundleModelSpaceHomeomorph 𝓘(ℝ, ℝ)).continuous.comp ht
  convert hp.snd using 1
  rfl

/-- On a compact regular region the descent speed has a uniform strictly negative bound. -/
theorem exists_uniform_negative_speed
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞
      (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (hdesc : ∀ x, x ∉ ManifoldMorse.criticalPoints E f → mvfderiv 𝓘(ℝ, E) f x (V x) < 0)
    {K : Set M} (hK : IsCompact K) (hreg : K ⊆ (ManifoldMorse.criticalPoints E f)ᶜ) :
    ∃ δ > (0 : ℝ), ∀ x ∈ K, mvfderiv 𝓘(ℝ, E) f x (V x) ≤ -δ := by
  by_cases hne : K.Nonempty
  · obtain ⟨p, hp, hmax⟩ := hK.exists_isMaxOn hne (continuous_mvfderiv_field hf hV).continuousOn
    refine ⟨-mvfderiv 𝓘(ℝ, E) f p (V p), neg_pos.mpr (hdesc p (hreg hp)), ?_⟩
    intro x hx
    have hle : mvfderiv 𝓘(ℝ, E) f x (V x) ≤ mvfderiv 𝓘(ℝ, E) f p (V p) := hmax hx
    simpa only [neg_neg] using hle
  · exact ⟨1, zero_lt_one, fun x hx => False.elim (hne ⟨x, hx⟩)⟩

/-- Every integral curve leaves a compact regular region within one uniform positive time. -/
theorem exists_uniform_residence_bound
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞
      (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (hdesc : ∀ x, x ∉ ManifoldMorse.criticalPoints E f → mvfderiv 𝓘(ℝ, E) f x (V x) < 0)
    {K : Set M} (hK : IsCompact K) (hreg : K ⊆ (ManifoldMorse.criticalPoints E f)ᶜ) :
    ∃ T > (0 : ℝ), ∀ γ : ℝ → M, IsMIntegralCurve γ V →
      ∃ t ∈ Icc (0 : ℝ) T, γ t ∉ K := by
  by_cases hne : K.Nonempty
  · obtain ⟨δ, hδ, hspeed⟩ := exists_uniform_negative_speed hf hV hdesc hK hreg
    obtain ⟨p, hp, hmin⟩ := hK.exists_isMinOn hne hf.continuous.continuousOn
    obtain ⟨q, hq, hmax⟩ := hK.exists_isMaxOn hne hf.continuous.continuousOn
    let T := (f q - f p + 1) / δ
    have hpq : f p ≤ f q := hmax hp
    have hgap : 0 < f q - f p + 1 := by linarith
    have hT : 0 < T := div_pos hgap hδ
    have hδT : δ * T = f q - f p + 1 := by
      dsimp [T]
      field_simp [hδ.ne']
    refine ⟨T, hT, ?_⟩
    intro γ hγ
    by_contra! hstay
    have hd (t : ℝ) : HasDerivAt (f ∘ γ) (mvfderiv 𝓘(ℝ, E) f (γ t) (V (γ t))) t :=
      hasDerivAt_comp_integralCurve hf hγ t
    have hdiff : Differentiable ℝ (f ∘ γ) := fun t => (hd t).differentiableAt
    have hzero : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, hT.le⟩
    have hlast : T ∈ Icc 0 T := ⟨hT.le, le_rfl⟩
    have hbound := (convex_Icc (0 : ℝ) T).image_sub_le_mul_sub_of_deriv_le
      hdiff.continuous.continuousOn hdiff.differentiableOn
      (fun t ht => by
        rw [(hd t).deriv]
        exact hspeed (γ t) (hstay t (interior_subset ht)))
      0 hzero T hlast hT.le
    simp only [Function.comp_apply, sub_zero, neg_mul] at hbound
    rw [hδT] at hbound
    have hlo : f p ≤ f (γ T) := hmin (hstay T hlast)
    have hhi : f (γ 0) ≤ f q := hmax (hstay 0 hzero)
    linarith
  · refine ⟨1, zero_lt_one, ?_⟩
    intro γ _
    exact ⟨0, ⟨le_rfl, zero_le_one⟩, fun h => hne ⟨γ 0, h⟩⟩

/-- In uniform time a descending trajectory from the upper sublevel either passes below the lower
level or enters the chosen open neighborhood of the band's critical points. -/
theorem exists_uniform_criticalNeighborhood_entry [CompactSpace M]
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞
      (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (hdesc : ∀ x, x ∉ ManifoldMorse.criticalPoints E f → mvfderiv 𝓘(ℝ, E) f x (V x) < 0)
    (F : Flow ℝ M) (hcurve : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    (hmono : ∀ x, Antitone (fun t => f (F t x)))
    {a b : ℝ} {U : Set M} (hU : IsOpen U)
    (hcover : ∀ x ∈ ManifoldMorse.criticalPoints E f, f x ∈ Icc a b → x ∈ U) :
    ∃ T > (0 : ℝ), ∀ x, f x ≤ b →
      ∃ t ∈ Icc (0 : ℝ) T, f (F t x) < a ∨ F t x ∈ U := by
  let K := f ⁻¹' Icc a b ∩ Uᶜ
  have hK : IsCompact K :=
    ((isClosed_Icc.preimage hf.continuous).inter hU.isClosed_compl).isCompact
  have hreg : K ⊆ (ManifoldMorse.criticalPoints E f)ᶜ := by
    intro x hx hcrit
    exact hx.2 (hcover x hcrit hx.1)
  obtain ⟨T, hT, hexit⟩ := exists_uniform_residence_bound hf hV hdesc hK hreg
  refine ⟨T, hT, ?_⟩
  intro x hx
  obtain ⟨t, ht, hout⟩ := hexit (fun s => F s x) (hcurve x)
  have hupper : f (F t x) ≤ b := by
    have hle : f (F t x) ≤ f x := by
      simpa only [F.map_zero_apply] using hmono x ht.1
    exact hle.trans hx
  refine ⟨t, ht, ?_⟩
  by_cases hlow : f (F t x) < a
  · exact Or.inl hlow
  · right
    by_contra hnot
    exact hout ⟨⟨le_of_not_gt hlow, hupper⟩, hnot⟩

end Wikipedia.SmoothSixDPoincare.FlowConstruction
