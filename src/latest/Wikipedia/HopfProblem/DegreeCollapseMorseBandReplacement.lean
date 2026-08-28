import Wikipedia.HopfProblem.DegreeCollapseGlobalBandLyapunov
import Wikipedia.HopfProblem.DegreeCollapseNativeBandCrossing
import Wikipedia.HopfProblem.DegreeCollapseMorseCancellationPreservation

/-!
# Native Morse critical-pair removal from finite passage

The global Lyapunov construction removes every critical point in the
closed band. Every surviving point retains its entire old function germ,
so the Morse property is preserved in the original atlas. If the band
contains precisely two original critical points, the actual finite count
decreases by two. No replacement function or collar estimate is supplied.
-/

noncomputable section

open Set Function Filter Manifold
open scoped Topology ContDiff
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.FlowCancellation

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M]
  {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] in
/-- Strict native descent rules out a critical point using the actual derivative. -/
theorem not_critical_of_directional_neg {g : M → ℝ} {x : M}
    (hneg : mvfderiv 𝓘(ℝ, E) g x (V x) < 0) : x ∉ criticalPoints E g := by
  intro hx
  change mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) g x = 0 at hx
  unfold mvfderiv at hneg
  rw [hx] at hneg
  simp at hneg

omit [T2Space M] in
/-- The two-point count reduction is a consequence of actual global smooth
replacement and preserved native germs, not an extra cancellation premise. -/
theorem remove_morse_band_pair {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hm : IsMorse E f)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞
      (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hcurve : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    {c d : ℝ} (hcd : c < d)
    (hc : ∀ x, f x = c → mvfderiv 𝓘(ℝ, E) f x (V x) < 0)
    (hd : ∀ x, f x = d → mvfderiv 𝓘(ℝ, E) f x (V x) < 0)
    (hcross : ∃ T : ℝ, 0 < T ∧ (∀ x, f x ≤ d → f (F T x) < c) ∧
      ∀ x, c ≤ f x → d < f (F (-T) x))
    {p q : M} (hpq : p ≠ q) (hp : p ∈ criticalPoints E f) (hq : q ∈ criticalPoints E f)
    (hpc : f p ∈ Icc c d) (hqc : f q ∈ Icc c d)
    (hpair : ∀ x ∈ criticalPoints E f, f x ∈ Icc c d → x = p ∨ x = q) :
    ∃ g : M → ℝ, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g ∧ IsMorse E g ∧
      (criticalPoints E g).ncard + 2 = (criticalPoints E f).ncard ∧
      (∀ x, x ∈ criticalPoints E g ↔ x ∈ criticalPoints E f ∧ x ≠ p ∧ x ≠ q) ∧
      ∀ x, f x ∉ Ioo c d → g =ᶠ[𝓝 x] f := by
  obtain ⟨g, hg, hneg, hgerm⟩ := exists_global_band_lyapunov hf hV F hcurve hcd hc hd hcross
  have hreg (x : M) (hx : f x ∈ Icc c d) : x ∉ criticalPoints E g :=
    not_critical_of_directional_neg (hneg x hx)
  have hnew (x : M) : x ∈ criticalPoints E g ↔ x ∈ criticalPoints E f ∧ x ≠ p ∧ x ≠ q := by
    constructor
    · intro hx
      have hout : f x ∉ Icc c d := fun h => hreg x h hx
      have he := hgerm x (fun h => hout ⟨h.1.le, h.2.le⟩)
      have hcrit : x ∈ criticalPoints E f := by
        change mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) f x = 0
        rw [← he.mfderiv_eq]
        exact hx
      exact ⟨hcrit, fun h => hout (h ▸ hpc), fun h => hout (h ▸ hqc)⟩
    · rintro ⟨hx, hxp, hxq⟩
      have hout : f x ∉ Icc c d := fun h => (hpair x hx h).elim hxp hxq
      change mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) g x = 0
      rw [(hgerm x (fun h => hout ⟨h.1.le, h.2.le⟩)).mfderiv_eq]
      exact hx
  have hmg : IsMorse E g := by
    apply MorseCancellationPreservation.isMorse_of_critical_germs hm hg
    intro x hx
    apply hgerm x
    intro h
    exact hreg x ⟨h.1.le, h.2.le⟩ hx
  have heq : criticalPoints E g = criticalPoints E f \ {p, q} := by
    ext x
    simpa only [Set.mem_sdiff, mem_insert_iff, mem_singleton_iff, not_or] using hnew x
  have hsub : {p, q} ⊆ criticalPoints E f := by
    intro x hx
    rcases hx with rfl | hx
    · exact hp
    · exact mem_singleton_iff.mp hx ▸ hq
  refine ⟨g, hg, hmg, ?_, hnew, hgerm⟩
  rw [heq, ← ncard_pair hpq]
  exact ncard_sdiff_add_ncard_of_subset hsub (finite_criticalPoints hf hm)

/-- Uniform finite residence and strict boundary derivatives suffice: the
complete flow, directed crossing, and global replacement are all constructed. -/
theorem remove_morse_band_pair_of_finite_passage {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hm : IsMorse E f)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞
      (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    {c d : ℝ} (hcd : c < d)
    (hc : ∀ x, f x = c → mvfderiv 𝓘(ℝ, E) f x (V x) < 0)
    (hd : ∀ x, f x = d → mvfderiv 𝓘(ℝ, E) f x (V x) < 0)
    (hpass : ∃ T : ℝ, 0 < T ∧ ∀ γ : ℝ → M, IsMIntegralCurve γ V →
      ∃ t ∈ Icc (0 : ℝ) T, f (γ t) ∉ Icc c d)
    {p q : M} (hpq : p ≠ q) (hp : p ∈ criticalPoints E f) (hq : q ∈ criticalPoints E f)
    (hpc : f p ∈ Icc c d) (hqc : f q ∈ Icc c d)
    (hpair : ∀ x ∈ criticalPoints E f, f x ∈ Icc c d → x = p ∨ x = q) :
    ∃ g : M → ℝ, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g ∧ IsMorse E g ∧
      (criticalPoints E g).ncard + 2 = (criticalPoints E f).ncard ∧
      (∀ x, x ∈ criticalPoints E g ↔ x ∈ criticalPoints E f ∧ x ≠ p ∧ x ≠ q) ∧
      ∀ x, f x ∉ Ioo c d → g =ᶠ[𝓝 x] f := by
  obtain ⟨F, hcurve, hcross, -⟩ := exists_native_flow_band_crossing hf hV hc hd hpass
  exact remove_morse_band_pair hf hm hV F hcurve hcd hc hd hcross hpq hp hq hpc hqc hpair

end Wikipedia.HopfProblem.DegreeCollapse.FlowCancellation
