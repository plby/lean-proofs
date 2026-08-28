import Wikipedia.SmoothSixDPoincare.MorseCriticalPoints
import Wikipedia.HopfProblem.SmoothMorseLemma

/-!
# Signed-square charts for the constructed Morse functions

The existing smooth Morse lemma is reused for its genuine smooth partial
diffeomorphism and exact function identities. Its dependency chain is audited
along with this interface; no normal form is an additional assumption.
-/

noncomputable section

open Set
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.MorsePerturbation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- An actual smooth coordinate chart in which the original function is a signed sum of squares. -/
structure SignedMorseChart (f : E → ℝ) (x : E) where
  weights : Fin (Module.finrank ℝ E) → ℝ
  signs : ∀ i, weights i = -1 ∨ weights i = 1
  chart : PartialDiffeomorph 𝓘(ℝ, E)
    𝓘(ℝ, Fin (Module.finrank ℝ E) → ℝ) E (Fin (Module.finrank ℝ E) → ℝ) ∞
  mem_source : x ∈ chart.source
  center : chart x = 0
  equation : ∀ y ∈ chart.source, f y = f x + ∑ i, weights i * (chart y i) ^ 2
  inverse_equation : ∀ y ∈ chart.target, f (chart.symm y) = f x + ∑ i, weights i * y i ^ 2

open Classical in
/-- The number of negative squares in this explicit Morse chart. -/
def SignedMorseChart.index {f : E → ℝ} {x : E} (c : SignedMorseChart f x) : ℕ :=
  (Finset.univ.filter (fun i => c.weights i = -1)).card

omit [FiniteDimensional ℝ E] in
theorem SignedMorseChart.index_le {f : E → ℝ} {x : E} (c : SignedMorseChart f x) :
    c.index ≤ Module.finrank ℝ E := by
  classical
  exact (Finset.card_filter_le _ _).trans (by simp)

/-- Every critical point of a smooth Morse function has a constructed signed-square chart. -/
theorem nonempty_signedMorseChart {f : E → ℝ} (hf : ContDiff ℝ ∞ f) (hm : IsMorse f)
    (x : E) (hx : x ∈ criticalPoints f) : Nonempty (SignedMorseChart f x) := by
  obtain ⟨w, hw, e, he, he₀, heq, hinv⟩ :=
    Wikipedia.HopfProblem.SmoothMorseLemma.exists_signed_morse_chart hf x hx (hm x hx)
  exact ⟨⟨w, hw, e, he, he₀, heq, hinv⟩⟩

end Wikipedia.SmoothSixDPoincare.MorsePerturbation
