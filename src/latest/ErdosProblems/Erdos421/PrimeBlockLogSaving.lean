import ErdosProblems.Erdos421.PrimeBlockComparison
import ErdosProblems.Erdos421.ProperPrimePowerDecay

/-! # Unconditional logarithmic cancellation in prime Dirichlet blocks -/

namespace Erdos421

open Filter Topology

theorem primeDirichletBlock_log_saving (K : ℕ) {A ε : ℝ}
    (hA : 0 ≤ A) (hε : 0 < ε) :
    ∃ M₀ : ℕ, 2 ≤ M₀ ∧ ∀ M N : ℕ, M₀ ≤ M → N ≤ M → ∀ s : ℂ, 1 ≤ s.re →
      (Real.log M) ^ (2 * A + 9) ≤ |s.im| → |s.im| ≤ (M : ℝ) ^ K →
      ‖primeDirichletBlock M N s‖ ≤ ε / (Real.log M) ^ A := by
  have hhalf : 0 < ε / 2 := by positivity
  obtain ⟨M₁, hM₁, hsave⟩ := normalizedVonMangoldtBlock_log_saving K hA hhalf
  obtain ⟨M₂, herror⟩ := eventually_atTop.mp (properPrimePowers_log_error_eventually A hhalf)
  refine ⟨max M₁ M₂, hM₁.trans (le_max_left _ _), ?_⟩
  intro M N hM hNM s hs hlo hhi
  have hM1 : M₁ ≤ M := (le_max_left _ _).trans hM
  have hM2 : M₂ ≤ M := (le_max_right _ _).trans hM
  have hb := primeDirichletBlock_norm_le (by omega : 1 ≤ M) hNM s hs
  exact (hb.trans (add_le_add (hsave M N hM1 hNM s hs hlo hhi) (herror M hM2))).trans_eq
    (by ring)

end Erdos421
