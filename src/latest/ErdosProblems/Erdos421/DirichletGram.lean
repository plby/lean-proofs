import ErdosProblems.Erdos421.TimeRows
import ErdosProblems.Erdos421.HilbertLargeValues
import Mathlib.Analysis.InnerProductSpace.PiL2

/-! # Dirichlet polynomial large values from explicit Gram-row bounds -/

namespace Erdos421

noncomputable def dirichletBlock (M N : ℕ) (c : ℕ → ℂ) (t : ℝ) : ℂ :=
  ∑ n ∈ Finset.range N, c n * oscillatoryPhase (Real.log (M + n : ℕ)) t

noncomputable def coefficientEnergy (N : ℕ) (c : ℕ → ℂ) : ℝ :=
  ∑ n ∈ Finset.range N, ‖c n‖ ^ 2

theorem coefficientEnergy_nonneg (N : ℕ) (c : ℕ → ℂ) : 0 ≤ coefficientEnergy N c :=
  Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _)

noncomputable def coefficientVector (N : ℕ) (c : ℕ → ℂ) : EuclideanSpace ℂ (Fin N) :=
  WithLp.toLp 2 (fun n ↦ c n)

noncomputable def dirichletPhaseVector (M N : ℕ) (t : ℝ) : EuclideanSpace ℂ (Fin N) :=
  WithLp.toLp 2 (fun n ↦ oscillatoryPhase (Real.log (M + n : ℕ)) (-t))

theorem coefficientVector_norm_sq (N : ℕ) (c : ℕ → ℂ) :
    ‖coefficientVector N c‖ ^ 2 = coefficientEnergy N c := by
  rw [EuclideanSpace.norm_sq_eq]
  change (∑ n : Fin N, ‖c n‖ ^ 2) = ∑ n ∈ Finset.range N, ‖c n‖ ^ 2
  exact Fin.sum_univ_eq_sum_range (fun n : ℕ ↦ ‖c n‖ ^ 2) N

theorem oscillatoryPhase_conj_neg_time (ω t : ℝ) :
    starRingEnd ℂ (oscillatoryPhase ω (-t)) = oscillatoryPhase ω t := by
  simpa only [neg_neg] using (oscillatoryPhase_neg_time ω (-t)).symm

theorem oscillatoryPhase_mul_time (ω s t : ℝ) :
    oscillatoryPhase ω s * oscillatoryPhase ω t = oscillatoryPhase ω (s + t) := by
  unfold oscillatoryPhase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem dirichletPhaseVector_inner_coefficient (M N : ℕ) (c : ℕ → ℂ) (t : ℝ) :
    inner ℂ (dirichletPhaseVector M N t) (coefficientVector N c) = dirichletBlock M N c t := by
  rw [PiLp.inner_apply]
  change (∑ n : Fin N, inner ℂ (oscillatoryPhase (Real.log (M + n : ℕ)) (-t)) (c n)) = _
  simp only [RCLike.inner_apply, oscillatoryPhase_conj_neg_time]
  exact Fin.sum_univ_eq_sum_range
    (fun n : ℕ ↦ c n * oscillatoryPhase (Real.log (M + n : ℕ)) t) N

theorem dirichletPhaseVector_inner (M N : ℕ) (s t : ℝ) :
    inner ℂ (dirichletPhaseVector M N s) (dirichletPhaseVector M N t) =
      logarithmicSum M N (s - t) := by
  rw [PiLp.inner_apply]
  change (∑ n : Fin N, inner ℂ (oscillatoryPhase (Real.log (M + n : ℕ)) (-s))
    (oscillatoryPhase (Real.log (M + n : ℕ)) (-t))) = _
  simp only [RCLike.inner_apply, oscillatoryPhase_conj_neg_time, oscillatoryPhase_mul_time]
  have heq : -t + s = s - t := by ring
  rw [heq]
  exact Fin.sum_univ_eq_sum_range
    (fun n : ℕ ↦ oscillatoryPhase (Real.log (M + n : ℕ)) (s - t)) N

/-- An unconditional Gram estimate for arbitrary complex coefficients and
arbitrary one-separated real sampling times in a finite interval. -/
theorem dirichletBlock_gram_bound {M N : ℕ} (hM : 0 < M) (hN : N ≤ M)
    (S : Finset ℕ) (c : ℕ → ℂ) (t : ℕ → ℝ) {A B : ℝ}
    (hAB : A ≤ B) (ht : ∀ i ∈ S, A ≤ t i ∧ t i ≤ B)
    (hsep : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → 1 ≤ |t i - t j|) :
    (∑ i ∈ S, ‖dirichletBlock M N c (t i)‖ ^ 2) ≤
      (2560 * M * Real.log (B - A + 2) + 640 * S.card * Real.sqrt (B - A)) *
        coefficientEnergy N c := by
  let R := 2560 * (M : ℝ) * Real.log (B - A + 2) + 640 * S.card * Real.sqrt (B - A)
  have hlog : 0 ≤ Real.log (B - A + 2) := Real.log_nonneg (by linarith)
  have hR : 0 ≤ R := by dsimp only [R]; positivity
  have hrow : ∀ i ∈ S, (∑ j ∈ S,
      ‖inner ℂ (dirichletPhaseVector M N (t i)) (dirichletPhaseVector M N (t j))‖) ≤ R := by
    intro i hi
    simp only [dirichletPhaseVector_inner]
    exact logarithmic_kernel_row_bound hM hN S t ht hsep hi
  have h := hilbert_large_values_bound S (fun i ↦ dirichletPhaseVector M N (t i))
    (coefficientVector N c) hR hrow
  simpa only [dirichletPhaseVector_inner_coefficient, coefficientVector_norm_sq, R] using h

theorem dirichletBlock_large_values_gram {M N : ℕ} (hM : 0 < M) (hN : N ≤ M)
    (S : Finset ℕ) (c : ℕ → ℂ) (t : ℕ → ℝ) {A B V : ℝ}
    (hAB : A ≤ B) (ht : ∀ i ∈ S, A ≤ t i ∧ t i ≤ B)
    (hsep : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → 1 ≤ |t i - t j|)
    (hV : 0 ≤ V) (hlarge : ∀ i ∈ S, V ≤ ‖dirichletBlock M N c (t i)‖) :
    S.card * V ^ 2 ≤
      (2560 * M * Real.log (B - A + 2) + 640 * S.card * Real.sqrt (B - A)) *
        coefficientEnergy N c := by
  calc
    _ = ∑ _i ∈ S, V ^ 2 := by simp
    _ ≤ ∑ i ∈ S, ‖dirichletBlock M N c (t i)‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro i hi
      exact pow_le_pow_left₀ hV (hlarge i hi) 2
    _ ≤ _ := dirichletBlock_gram_bound hM hN S c t hAB ht hsep

theorem dirichletBlock_large_values_short_window {M N : ℕ} (hM : 0 < M) (hN : N ≤ M)
    (S : Finset ℕ) (c : ℕ → ℂ) (t : ℕ → ℝ) {A B V : ℝ}
    (hAB : A ≤ B) (ht : ∀ i ∈ S, A ≤ t i ∧ t i ≤ B)
    (hsep : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → 1 ≤ |t i - t j|)
    (hV : 0 ≤ V) (hlarge : ∀ i ∈ S, V ≤ ‖dirichletBlock M N c (t i)‖)
    (hwindow : 1280 * Real.sqrt (B - A) * coefficientEnergy N c ≤ V ^ 2) :
    S.card * V ^ 2 ≤ 5120 * M * Real.log (B - A + 2) * coefficientEnergy N c := by
  have h := dirichletBlock_large_values_gram hM hN S c t hAB ht hsep hV hlarge
  have hm := mul_le_mul_of_nonneg_left hwindow (Nat.cast_nonneg S.card)
  nlinarith

end Erdos421
