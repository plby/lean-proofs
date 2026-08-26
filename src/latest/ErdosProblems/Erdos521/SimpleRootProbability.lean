/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Exact multiple roots are rare uniformly over subintervals of the bulk.
Formal proof: Codex.
-/
import ErdosProblems.Erdos521.RootRepulsion

namespace Erdos521

open MeasureTheory Filter

theorem smallValueDerivativeEvent_subset (n : ℕ) {l u l' u' η η' : ℝ}
    (hl : l' ≤ l) (hu : u ≤ u') (hη : η ≤ η') :
    smallValueDerivativeEvent n l u η ⊆ smallValueDerivativeEvent n l' u' η' := by
  rintro ε ⟨x, hx, hv, hd⟩
  exact ⟨x, ⟨hl.trans hx.1, hx.2.trans hu⟩, hv.trans hη, hd.trans hη⟩

theorem simpleRoot_bulk_probability :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop, ∀ l u : ℝ,
      9 / 10 ≤ l → u ≤ endpointCenter C n →
      sequenceLaw.real (smallValueDerivativeEvent n l u 0) ≤ (n : ℝ) ^ (-1 : ℝ) := by
  obtain ⟨C, hC, B, _, hprob⟩ := root_repulsion_probability 1 (by norm_num)
  refine ⟨C, hC, ?_⟩
  filter_upwards [hprob] with n hn
  intro l u hl hu
  exact (measureReal_mono (μ := sequenceLaw) (smallValueDerivativeEvent_subset n hl hu
    (Real.rpow_nonneg (Nat.cast_nonneg n) (-B)))).trans hn

end Erdos521
