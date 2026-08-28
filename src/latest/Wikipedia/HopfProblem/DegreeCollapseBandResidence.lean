import Wikipedia.HopfProblem.DegreeCollapsePerturbedNoReturn
import Wikipedia.HopfProblem.DegreeCollapseNativeLyapunovResidence

/-!
# Finite passage from local residence and no-return

If a trajectory remains in a band, the exterior residence bound forces
two visits to the inner neighborhood. No-return traps the intervening
segment in the outer neighborhood, where the interior residence bound
gives a contradiction. This constructs a uniform time, rather than merely
excluding periodic trajectories.
-/

noncomputable section

open Set Function Manifold
open scoped ContDiff Topology

namespace Wikipedia.HopfProblem.DegreeCollapse.FlowCancellation

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]
  {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}

/-- Two residence estimates and no-return give a uniform residence bound for the whole band. -/
theorem combine_native_residence_bounds {B N U : Set M}
    (houter : ∃ T : ℝ, 0 < T ∧ ∀ γ : ℝ → M, IsMIntegralCurve γ V →
      ∃ t ∈ Icc (0 : ℝ) T, γ t ∉ B \ N)
    (hinner : ∃ T : ℝ, 0 < T ∧ ∀ γ : ℝ → M, IsMIntegralCurve γ V →
      ∃ t ∈ Icc (0 : ℝ) T, γ t ∉ U)
    (hnoreturn : ∀ γ : ℝ → M, IsMIntegralCurve γ V →
      ∀ a b : ℝ, γ a ∈ N → γ b ∈ N → ∀ t ∈ Icc a b, γ t ∈ U) :
    ∃ T : ℝ, 0 < T ∧ ∀ γ : ℝ → M, IsMIntegralCurve γ V →
      ∃ t ∈ Icc (0 : ℝ) T, γ t ∉ B := by
  obtain ⟨T₀, hT₀, hout⟩ := houter
  obtain ⟨T₁, hT₁, hin⟩ := hinner
  refine ⟨2 * T₀ + T₁, by linarith, ?_⟩
  intro γ hγ
  by_contra! hstay
  obtain ⟨a, ha, haout⟩ := hout γ hγ
  have haN : γ a ∈ N := by
    by_contra haN
    exact haout ⟨hstay a ⟨ha.1, by linarith [ha.2]⟩, haN⟩
  obtain ⟨b, hb, hbout⟩ := hout (γ ∘ (· + (T₀ + T₁))) (hγ.comp_add (T₀ + T₁))
  have hbN : γ (b + (T₀ + T₁)) ∈ N := by
    by_contra hbN
    exact hbout ⟨hstay (b + (T₀ + T₁))
      ⟨by linarith [hb.1], by linarith [hb.2]⟩, hbN⟩
  obtain ⟨t, ht, htout⟩ := hin (γ ∘ (· + T₀)) (hγ.comp_add T₀)
  exact htout (hnoreturn γ hγ a (b + (T₀ + T₁)) haN hbN (t + T₀)
    ⟨by linarith [ha.2, ht.1], by linarith [hb.1, ht.2]⟩)

variable [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M] [T2Space M]
  {V' : (x : M) → TangentSpace 𝓘(ℝ, E) x}

/-- A supported native perturbation with local residence has uniform finite band passage. -/
theorem exists_perturbed_band_residence {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞
      (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (hV' : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞
      (fun x => (⟨x, V' x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hcurve : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    {c d : ℝ} {K N U : Set M} (hK : IsClosed K) (hN : IsOpen N)
    (hKN : K ⊆ N) (hNU : N ⊆ U) (hoff : ∀ x ∉ K, V' x = V x)
    (hneg : ∀ x, f x ∈ Icc c d → x ∉ N → mvfderiv 𝓘(ℝ, E) f x (V x) < 0)
    (hnoreturn : ∀ x ∈ N, ∀ t : ℝ, 0 ≤ t → F t x ∈ N →
      ∀ s ∈ Icc (0 : ℝ) t, F s x ∈ U)
    (hinner : ∃ T : ℝ, 0 < T ∧ ∀ γ : ℝ → M, IsMIntegralCurve γ V' →
      ∃ t ∈ Icc (0 : ℝ) T, γ t ∉ U) :
    ∃ T : ℝ, 0 < T ∧ ∀ γ : ℝ → M, IsMIntegralCurve γ V' →
      ∃ t ∈ Icc (0 : ℝ) T, f (γ t) ∉ Icc c d := by
  have hcompact : IsCompact (f ⁻¹' Icc c d \ N) :=
    ((isClosed_Icc.preimage hf.continuous).inter hN.isClosed_compl).isCompact
  have houter := exists_native_lyapunov_residence hf hV' hcompact (by
    intro x hx
    rw [hoff x (fun h => hx.2 (hKN h))]
    exact hneg x hx.1 hx.2)
  exact combine_native_residence_bounds houter hinner (fun γ hγ a b ha hb =>
    native_no_return_of_supported_perturbation (hV.of_le (by simp)) F hcurve
      hK hKN hNU hoff hnoreturn hγ ha hb)

end Wikipedia.HopfProblem.DegreeCollapse.FlowCancellation
