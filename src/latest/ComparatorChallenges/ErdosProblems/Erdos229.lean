import Mathlib


open Complex Polynomial Set Filter Topology Metric

namespace Erdos229

open scoped Classical in
theorem erdos_229 :
    letI := Polynomial.algebraPi ℂ ℂ ℂ
    ∀ (S : ℕ → Set ℂ), (∀ n, derivedSet (S n) = ∅) →
      ∃ (f : ℂ → ℂ), Transcendental (Polynomial ℂ) f ∧ Differentiable ℂ f ∧
        ∀ n ≥ 1, ∃ k, ∀ z ∈ S n, iteratedDeriv k f z = 0 := by
  sorry

end Erdos229
