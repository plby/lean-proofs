import ErdosProblems.Erdos587.SqrtPhaseBounds
import ErdosProblems.Erdos587.DerivativeDifferences
import ErdosProblems.Erdos587.HarmonicOneSixth

/-! One-sixth harmonic bounds for square-root phases on a fixed scale. -/

open scoped BigOperators

namespace Erdos587

theorem sqrtAffinePhase_sample_difference_bounds {a b L A : ℝ} {N : ℕ}
    (hN : 0 < N) (hL : 0 < L) (hA : 1 ≤ A)
    (hblo : L ^ 2 / (A * N) ≤ b) (hbhi : b ≤ L ^ 2 / N)
    (hscale : ∀ x ∈ Set.Icc (0 : ℝ) N, L ^ 2 / A ≤ a + b * x ∧ a + b * x ≤ L ^ 2) :
    (∀ n, n + 1 < N →
      -(8 * A ^ 6 * ((L / (8 * A ^ 3)) / (N : ℝ) ^ 2)) ≤
        phaseIncrement (phaseIncrement (fun n : ℕ => sqrtAffinePhase a b n)) n ∧
      phaseIncrement (phaseIncrement (fun n : ℕ => sqrtAffinePhase a b n)) n ≤
        -((L / (8 * A ^ 3)) / (N : ℝ) ^ 2)) ∧
    (∀ n, n + 2 < N →
      (L / (8 * A ^ 3)) / (N : ℝ) ^ 3 ≤
        phaseIncrement (phaseIncrement (phaseIncrement (fun n : ℕ => sqrtAffinePhase a b n))) n ∧
      phaseIncrement (phaseIncrement (phaseIncrement (fun n : ℕ => sqrtAffinePhase a b n))) n ≤
        8 * A ^ 6 * ((L / (8 * A ^ 3)) / (N : ℝ) ^ 3)) := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hApos : 0 < A := by linarith
  have hpos (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) N) : 0 < a + b * x :=
    (sqrt_scale_bounds hL hA (hscale x hx).1 (hscale x hx).2).1
  have hderiv (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) N) :=
    sqrtAffinePhase_scaled_derivative_bounds hL hNR hA hblo hbhi (hscale x hx).1 (hscale x hx).2
  have hnorm (j : ℕ) : 8 * A ^ 6 * ((L / (8 * A ^ 3)) / (N : ℝ) ^ j) =
      A ^ 3 * L / (N : ℝ) ^ j := by field_simp
  have hnorm' (j : ℕ) : (L / (8 * A ^ 3)) / (N : ℝ) ^ j =
      L / (8 * A ^ 3 * (N : ℝ) ^ j) := by ring
  constructor
  · intro n hn
    have hsub : Set.Icc (n : ℝ) (n + 2) ⊆ Set.Icc (0 : ℝ) N := by
      intro x hx
      have hnR : (n : ℝ) + 2 ≤ N := by exact_mod_cast (show n + 2 ≤ N by omega)
      exact ⟨(Nat.cast_nonneg n).trans hx.1, hx.2.trans hnR⟩
    rw [hnorm 2, hnorm' 2]
    apply second_sample_difference_bounds (sqrtAffinePhase a b) (sqrtAffinePhaseD1 a b)
      (sqrtAffinePhaseD2 a b) n
    · intro x hx
      exact hasDerivAt_sqrtAffinePhase a b x (hpos x (hsub hx))
    · intro x hx
      exact hasDerivAt_sqrtAffinePhaseD1 a b x (hpos x (hsub hx))
    · intro x hx
      exact ⟨(hderiv x (hsub hx)).1, (hderiv x (hsub hx)).2.1⟩
  · intro n hn
    have hsub : Set.Icc (n : ℝ) (n + 3) ⊆ Set.Icc (0 : ℝ) N := by
      intro x hx
      have hnR : (n : ℝ) + 3 ≤ N := by exact_mod_cast (show n + 3 ≤ N by omega)
      exact ⟨(Nat.cast_nonneg n).trans hx.1, hx.2.trans hnR⟩
    rw [hnorm 3, hnorm' 3]
    apply third_sample_difference_bounds (sqrtAffinePhase a b) (sqrtAffinePhaseD1 a b)
      (sqrtAffinePhaseD2 a b) (sqrtAffinePhaseD3 a b) n
    · intro x hx
      exact hasDerivAt_sqrtAffinePhase a b x (hpos x (hsub hx))
    · intro x hx
      exact hasDerivAt_sqrtAffinePhaseD1 a b x (hpos x (hsub hx))
    · intro x hx
      exact hasDerivAt_sqrtAffinePhaseD2 a b x (hpos x (hsub hx))
    · intro x hx
      exact (hderiv x (hsub hx)).2.2

theorem norm_sqrtAffinePhase_harmonic_sum_le {a b L A : ℝ} {N : ℕ}
    (hN : 0 < N) (hL : 0 < L) (hA : 1 ≤ A)
    (hblo : L ^ 2 / (A * N) ≤ b) (hbhi : b ≤ L ^ 2 / N)
    (hscale : ∀ x ∈ Set.Icc (0 : ℝ) N, L ^ 2 / A ≤ a + b * x ∧ a + b * x ≤ L ^ 2)
    (hF : (N : ℝ) ≤ L / (8 * A ^ 3)) (m : ℤ) (hm : m ≠ 0) :
    ‖∑ n ∈ Finset.range N, phase ((m : ℝ) * sqrtAffinePhase a b n)‖ ≤
      (100 * (8 * A ^ 6) * (L / (8 * A ^ 3)) ^ (1 / 6 : ℝ) * Real.sqrt N) *
        |(m : ℝ)| ^ (1 / 6 : ℝ) := by
  obtain ⟨h₂, h₃⟩ := sqrtAffinePhase_sample_difference_bounds hN hL hA hblo hbhi hscale
  have hC : 1 ≤ 8 * A ^ 6 := by nlinarith [one_le_pow₀ hA (n := 6)]
  exact norm_phase_integer_harmonic_sum_le (fun n => sqrtAffinePhase a b n) hN hF hC
    (fun n hn => (h₂ n hn).1) (fun n hn => (h₂ n hn).2)
    (fun n hn => (h₃ n hn).1) (fun n hn => (h₃ n hn).2) m hm

end Erdos587
