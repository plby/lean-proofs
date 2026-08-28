import Wikipedia.SmoothSixDPoincare.GlobalMorseFunction
import Wikipedia.SmoothSixDPoincare.ManifoldCriticalPoints
import Wikipedia.SmoothSixDPoincare.MorseNormalForm

/-!
# Global Morse functions with native critical points and genuine normal-form charts

The local Morse lemma is applied on an actual chart target and composed
with that chart. The resulting partial diffeomorphism has the original
manifold as its source, and its signed-square identities concern the
original function, not a substitute function on an abstract model.
-/

noncomputable section

open Set
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.ManifoldMorse

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]

/-- A smooth maximal-atlas chart regarded as a native partial diffeomorphism. -/
def chartPartialDiffeomorph (e : OpenPartialHomeomorph M E)
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M) :
    PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M E ∞ where
  toPartialEquiv := e.toPartialEquiv
  open_source := e.open_source
  open_target := e.open_target
  contMDiffOn_toFun := contMDiffOn_of_mem_maximalAtlas he
  contMDiffOn_invFun := contMDiffOn_symm_of_mem_maximalAtlas he

/-- Signed-square coordinates for the actual function on the original manifold. -/
structure SignedMorseChart (f : M → ℝ) (x : M) where
  weights : Fin (Module.finrank ℝ E) → ℝ
  signs : ∀ i, weights i = -1 ∨ weights i = 1
  chart : PartialDiffeomorph 𝓘(ℝ, E)
    𝓘(ℝ, Fin (Module.finrank ℝ E) → ℝ) M (Fin (Module.finrank ℝ E) → ℝ) ∞
  mem_source : x ∈ chart.source
  center : chart x = 0
  equation : ∀ y ∈ chart.source, f y = f x + ∑ i, weights i * (chart y i) ^ 2
  inverse_equation : ∀ y ∈ chart.target, f (chart.symm y) = f x + ∑ i, weights i * y i ^ 2

/-- Each native critical point has a genuine smooth signed-square chart on the manifold. -/
theorem nonempty_signedMorseChart {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hm : IsMorse E f)
    (x : M) (hx : x ∈ criticalPoints E f) : Nonempty (SignedMorseChart (E := E) f x) := by
  obtain ⟨e, he, hxS, hreg | hH⟩ := hm x
  · exact False.elim (hreg ((mem_criticalPoints_iff hf he hxS).mp hx))
  · have hc := (mem_criticalPoints_iff hf he hxS).mp hx
    obtain ⟨w, hw, d, hdx, -, hd₀, hdeq, hdinv⟩ :=
      Wikipedia.HopfProblem.SmoothMorseLemma.exists_signed_morse_chart_of_contDiffOn
        (contDiffOn_chartExpression hf he) e.open_target (e x) (e.map_source hxS) hc hH
    let c := (chartPartialDiffeomorph e he).trans d
    refine ⟨⟨w, hw, c, ⟨hxS, hdx⟩, hd₀, ?_, ?_⟩⟩
    · intro y hy
      have hyS : y ∈ e.source := hy.1
      have hyd : e y ∈ d.source := hy.2
      change f y = f x + ∑ i, w i * (d (e y) i) ^ 2
      simpa only [Function.comp_apply, e.left_inv hyS, e.left_inv hxS] using hdeq (e y) hyd
    · intro y hy
      have hyd : y ∈ d.target := hy.1
      change f (e.symm (d.symm y)) = f x + ∑ i, w i * y i ^ 2
      simpa only [Function.comp_apply, e.left_inv hxS] using hdinv y hyd

variable (E M) [T2Space M] [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M]

/-- Construct a global Morse function, its finite native critical set, and its normal forms. -/
theorem exists_morse_function_with_normalForms :
    ∃ f : M → ℝ, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f ∧ IsMorse E f ∧
      (criticalPoints E f).Finite ∧
      ∀ x ∈ criticalPoints E f, Nonempty (SignedMorseChart (E := E) f x) := by
  obtain ⟨f, hf, hm⟩ := exists_morse_function E M
  exact ⟨f, hf, hm, finite_criticalPoints hf hm, fun x hx => nonempty_signedMorseChart hf hm x hx⟩

end Wikipedia.SmoothSixDPoincare.ManifoldMorse
