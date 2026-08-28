import Wikipedia.HopfProblem.DegreeCollapseCubicConnectionPassage
import Wikipedia.HopfProblem.DegreeCollapseMorseBandReplacement

/-!
# Actual Morse cancellation from a native cubic field and unique connection

This assembles thin-neighborhood field replacement, no-return, finite
passage, native smooth flow dependence, signed times, boundary-germ
correction, and global smooth gluing. The resulting function is Morse
and has exactly the original two critical points removed. The original
field's cubic normal form and geometric uniqueness remain explicit inputs.
-/

noncomputable section

open Set Function Manifold Filter
open scoped ContDiff Topology
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]

/-- Cancel an isolated unique native cubic connection, with no supplied
replacement function, wide chart domain, no-return neighborhood, finite
passage bound, smooth-flow axiom, hitting-time regularity, or collar estimate. -/
theorem cancel_unique_native_cubic_connection {m : ℕ} (σ : Fin m → ℝ)
    (hσ : ∀ i, σ i ≠ 0) {a : ℝ} (ha : 0 < a)
    (Φ : PartialDiffeomorph 𝓘(ℝ, Model m) 𝓘(ℝ, E) (Model m) M ∞)
    (haxis : Icc (-a) a ×ˢ {(0 : Fin m → ℝ)} ⊆ Φ.source)
    {f : M → ℝ} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hm : IsMorse E f)
    (V : (x : M) → TangentSpace 𝓘(ℝ, E) x)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞
      (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (hmodel : ∀ x ∈ Φ.target, V x = nativeCubicDescent σ Φ (-(a ^ 2)) x)
    (F : Flow ℝ M) (hcurve : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    (hzero : ∀ x ∈ criticalPoints E f, V x = 0)
    (hdesc : ∀ x, x ∉ criticalPoints E f → mvfderiv 𝓘(ℝ, E) f x (V x) < 0)
    (hinj : InjOn f (criticalPoints E f))
    (hp : Φ (a, 0) ∈ criticalPoints E f)
    (hq : Φ (-a, 0) ∈ criticalPoints E f)
    (hpq : f (Φ (a, 0)) < f (Φ (-a, 0)))
    {c d : ℝ} (hc : c < f (Φ (a, 0))) (hd : f (Φ (-a, 0)) < d)
    (hpair : ∀ x ∈ criticalPoints E f,
      f x ∈ Icc c d → x = Φ (a, 0) ∨ x = Φ (-a, 0))
    (hunique : ∀ x ∉ criticalPoints E f,
      Tendsto (fun t : ℝ => F t x) atBot (𝓝 (Φ (-a, 0))) →
      Tendsto (fun t : ℝ => F t x) atTop (𝓝 (Φ (a, 0))) →
        ∃ t : ℝ, F t (Φ (0, 0)) = x) :
    ∃ g : M → ℝ, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g ∧ IsMorse E g ∧
      (criticalPoints E g).ncard + 2 = (criticalPoints E f).ncard ∧
      (∀ x, x ∈ criticalPoints E g ↔
        x ∈ criticalPoints E f ∧ x ≠ Φ (a, 0) ∧ x ≠ Φ (-a, 0)) ∧
      ∀ x, f x ∉ Ioo c d → g =ᶠ[𝓝 x] f := by
  obtain ⟨K, V', -, hKsub, hV', -, hkeep, -, G, hGcurve, hcross, -⟩ :=
    exists_cubic_connection_finite_passage σ hσ ha Φ haxis hf V hV hmodel F hcurve
      hzero hdesc hinj hp hq hpq hc hd hpair hunique
  have hcd : c < d := lt_trans hc (lt_trans hpq hd)
  have hboundary (x : M) (hx : f x = c ∨ f x = d) :
      mvfderiv 𝓘(ℝ, E) f x (V' x) < 0 := by
    have hxK : x ∉ K := by
      intro hxK
      have hh : f x ∈ Ioo c d := (hKsub hxK).2
      rcases hx with hx | hx <;> rw [hx] at hh
      · exact (lt_irrefl c) hh.1
      · exact (lt_irrefl d) hh.2
    have hreg : x ∉ criticalPoints E f := by
      intro hcrit
      have hxb : f x ∈ Icc c d := by
        rcases hx with hx | hx <;> rw [hx]
        · exact ⟨le_rfl, hcd.le⟩
        · exact ⟨hcd.le, le_rfl⟩
      rcases hpair x hcrit hxb with he | he
      · rw [he] at hx
        rcases hx with hx | hx <;> linarith
      · rw [he] at hx
        rcases hx with hx | hx <;> linarith
    rw [(hkeep x hxK).self_of_nhds]
    exact hdesc x hreg
  have hneq : Φ (a, (0 : Fin m → ℝ)) ≠ Φ (-a, 0) := by
    intro h
    exact hpq.ne (congrArg f h)
  exact FlowCancellation.remove_morse_band_pair hf hm hV' G hGcurve hcd
    (fun x hx => hboundary x (Or.inl hx)) (fun x hx => hboundary x (Or.inr hx))
    hcross hneq hp hq ⟨hc.le, (hpq.trans hd).le⟩ ⟨(hc.trans hpq).le, hd.le⟩ hpair

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
