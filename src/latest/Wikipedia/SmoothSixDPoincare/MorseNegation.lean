import Wikipedia.SmoothSixDPoincare.ManifoldMorseNormalForm

/-!
# Negating a Morse function and its actual charts

The native critical set is unchanged by negation. Negating every sign in
the same genuine chart gives the signed Morse normal form of the negative
function, allowing maximum-side disks to use the minimum-side construction.
-/

noncomputable section

open Set Manifold
open scoped ContDiff Topology

namespace Wikipedia.SmoothSixDPoincare.ManifoldMorse

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]

/-- Negation does not change the actual native critical points. -/
theorem criticalPoints_neg (f : M → ℝ) : criticalPoints E (fun x => -f x) = criticalPoints E f := by
  ext x
  change mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) (-f) x = 0 ↔
    mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) f x = 0
  rw [mfderiv_neg]
  exact neg_eq_zero

namespace SignedMorseChart

variable {f : M → ℝ} {p : M} (c : SignedMorseChart (E := E) f p)

/-- The same native chart, with all signs reversed, is a Morse chart for the negative function. -/
def neg : SignedMorseChart (E := E) (fun x => -f x) p where
  weights i := -c.weights i
  signs i := by
    rcases c.signs i with h | h
    · exact Or.inr (by rw [h]; ring)
    · exact Or.inl (by rw [h])
  chart := c.chart
  mem_source := c.mem_source
  center := c.center
  equation y hy := by
    rw [c.equation y hy]
    simp only [neg_mul, Finset.sum_neg_distrib, neg_add]
  inverse_equation y hy := by
    rw [c.inverse_equation y hy]
    simp only [neg_mul, Finset.sum_neg_distrib, neg_add]

end SignedMorseChart
end Wikipedia.SmoothSixDPoincare.ManifoldMorse
