import Wikipedia.HopfProblem.DegreeCollapseGlobalBlendedHeight
import Wikipedia.HopfProblem.DegreeCollapseMorseBandReplacement

/-!
# Actual Morse-function rearrangement from a stationary separating weight

The two scalar diffeomorphisms are constructed with prescribed target
heights. Blending them with the actual extended weight produces a global
smooth Morse function, exactly the original critical set, the two requested
critical values, strict descent for the same field, and full exterior
function germs. The remaining geometric input is the separating weight;
this theorem does not assume an already rearranged function.
-/

noncomputable section

open Set Function Filter Manifold
open scoped Topology ContDiff
open Wikipedia.SmoothSixDPoincare ManifoldMorse
open Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseRearrangement

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

theorem exists_rearranged_morse_function_of_stationary_weight {f θ : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hm : IsMorse E f)
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (F : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    (hdesc : ∀ x, x ∉ criticalPoints E f → mvfderiv 𝓘(ℝ, E) f x (V x) < 0)
    {p q : M} {l u p' q' : ℝ}
    (hp : f p ∈ Ioo l u) (hq : f q ∈ Ioo l u)
    (hp' : p' ∈ Ioo l u) (hq' : q' ∈ Ioo l u)
    (hpair : ∀ x ∈ criticalPoints E f, f x ∈ Ioo l u → x = p ∨ x = q)
    (hθ : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ θ (f ⁻¹' Icc l u))
    (hθrange : ∀ x, θ x ∈ Icc (0 : ℝ) 1)
    (hθinv : ∀ x t, θ (F t x) = θ x)
    (hpgerm : θ =ᶠ[𝓝 p] fun _ => 1) (hqgerm : θ =ᶠ[𝓝 q] fun _ => 0) :
    ∃ g : M → ℝ,
      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g ∧ IsMorse E g ∧
      criticalPoints E g = criticalPoints E f ∧ g p = p' ∧ g q = q' ∧
      (∀ x, x ∉ criticalPoints E f → mvfderiv 𝓘(ℝ, E) g x (V x) < 0) ∧
      (∀ x, f x ∉ Ioo l u → g =ᶠ[𝓝 x] f) ∧
      (g =ᶠ[𝓝 p] fun x => f x + (p' - f p)) ∧
      (g =ᶠ[𝓝 q] fun x => f x + (q' - f q)) ∧
      (∀ x ∈ criticalPoints E f, x ≠ p → x ≠ q → g =ᶠ[𝓝 x] f) ∧
      (∀ x ∈ criticalPoints E f, ∃ k : ℝ, g =ᶠ[𝓝 x] fun y => f y + k) := by
  obtain ⟨P, -, hPtrans, -, -, hPpos, hPfix⟩ :=
    exists_increasing_interval_translation_with_exterior_germs hp hp'
  obtain ⟨Q, -, hQtrans, -, -, hQpos, hQfix⟩ :=
    exists_increasing_interval_translation_with_exterior_germs hq hq'
  let g : M → ℝ := fun x => blendHeight (θ x) P Q (f x)
  have hg : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g :=
    contMDiff_globally_blended_height hf hθ P.contMDiff.contDiff Q.contMDiff.contDiff hPfix hQfix
  have hgp : g =ᶠ[𝓝 p] fun x => f x + (p' - f p) :=
    blended_height_one_translation_germ hf.continuous.continuousAt hpgerm hPtrans
  have hgq : g =ᶠ[𝓝 q] fun x => f x + (q' - f q) :=
    blended_height_zero_translation_germ hf.continuous.continuousAt hqgerm hQtrans
  have hexterior (x : M) (hx : f x ∉ Ioo l u) : g =ᶠ[𝓝 x] f :=
    blended_height_exterior_germ hf.continuous hPfix hQfix hx
  have hothers (x : M) (hx : x ∈ criticalPoints E f) (hxp : x ≠ p) (hxq : x ≠ q) :
      g =ᶠ[𝓝 x] f := hexterior x (fun hb => (hpair x hx hb).elim hxp hxq)
  have hkeep (x : M) (hx : x ∈ criticalPoints E f) :
      ∃ k : ℝ, g =ᶠ[𝓝 x] fun y => f y + k := by
    by_cases hxp : x = p
    · subst x
      exact ⟨p' - f p, hgp⟩
    by_cases hxq : x = q
    · subst x
      exact ⟨q' - f q, hgq⟩
    exact ⟨0, by simpa only [add_zero] using hothers x hx hxp hxq⟩
  have hdescent (x : M) (hx : x ∉ criticalPoints E f) : mvfderiv 𝓘(ℝ, E) g x (V x) < 0 := by
    rw [blended_height_directional_derivative hf hg
      (P.contMDiff.contDiff.differentiable (by simp))
      (Q.contMDiff.contDiff.differentiable (by simp)) F hF hθinv x]
    exact mul_neg_of_pos_of_neg (positive_blended_slope (hθrange x) (hPpos _) (hQpos _)) (hdesc x hx)
  have hcrit : criticalPoints E g = criticalPoints E f := by
    ext x
    constructor
    · intro hx
      by_contra hnot
      exact FlowCancellation.not_critical_of_directional_neg (hdescent x hnot) hx
    · intro hx
      obtain ⟨k, hk⟩ := hkeep x hx
      change mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) g x = 0
      rw [mfderiv_of_add_const_germ (hf.mdifferentiableAt (by simp)) hk]
      exact hx
  have hmg : IsMorse E g := by
    intro x
    by_cases hx : x ∈ criticalPoints E f
    · obtain ⟨k, hk⟩ := hkeep x hx
      exact isMorseAt_of_add_const_germ (hm x) hk
    · have hreg : x ∉ criticalPoints E g := by rwa [hcrit]
      exact MorseCancellationPreservation.isMorseAt_of_regular hg hreg
  refine ⟨g, hg, hmg, hcrit, ?_, ?_, hdescent, hexterior, hgp, hgq, hothers, hkeep⟩
  · have hh := hgp.self_of_nhds
    dsimp only at hh
    linarith
  · have hh := hgq.self_of_nhds
    dsimp only at hh
    linarith

end Wikipedia.HopfProblem.DegreeCollapse.MorseRearrangement
