import ErdosProblems.Erdos587.OneSixthLocator
import ErdosProblems.Erdos587.SqrtPhaseSum

/-! A square-root phase comes just below an integer under a seventh-power budget. -/

namespace Erdos587

theorem exists_sqrtAffinePhase_locator {A : ℝ} (hA : 1 ≤ A) :
    ∃ K : ℝ, 0 < K ∧ ∀ (a b L δ : ℝ) (N : ℕ),
      0 < N → 0 < L → 0 < δ → δ ≤ 1 →
      L ^ 2 / (A * N) ≤ b → b ≤ L ^ 2 / N →
      (∀ x ∈ Set.Icc (0 : ℝ) N, L ^ 2 / A ≤ a + b * x ∧ a + b * x ≤ L ^ 2) →
      (N : ℝ) ≤ L / (8 * A ^ 3) → K * L < (N : ℝ) ^ 3 * δ ^ 7 →
      ∃ n < N, ∃ k : ℤ, 0 < (k : ℝ) - sqrtAffinePhase a b n ∧
        (k : ℝ) - sqrtAffinePhase a b n < δ := by
  obtain ⟨K, hK, hlocator⟩ := exists_integer_above_of_difference_bounds
  have hApos : 0 < A := by linarith
  refine ⟨K * (8 * A ^ 6) ^ 6 / (8 * A ^ 3), by positivity, ?_⟩
  intro a b L δ N hN hL hδ hδ1 hblo hbhi hscale hF hbudget
  obtain ⟨h₂, h₃⟩ := sqrtAffinePhase_sample_difference_bounds hN hL hA hblo hbhi hscale
  have hC : 1 ≤ 8 * A ^ 6 := by nlinarith [one_le_pow₀ hA (n := 6)]
  apply hlocator (fun n => sqrtAffinePhase a b n) N (L / (8 * A ^ 3)) (8 * A ^ 6) δ
    hN hF hC hδ hδ1
    (fun n hn => (h₂ n hn).1) (fun n hn => (h₂ n hn).2)
    (fun n hn => (h₃ n hn).1) (fun n hn => (h₃ n hn).2)
  convert hbudget using 1
  ring

end Erdos587
