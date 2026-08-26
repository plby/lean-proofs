import ErdosProblems.Erdos421.LogarithmicSpacing
import ErdosProblems.Erdos421.PhasePartition

/-! # A second-derivative bound for logarithmic exponential sums -/

namespace Erdos421

theorem logarithmic_phase_increment_eq (M n : ℕ) (τ : ℝ) :
    phaseIncrement (fun k ↦ τ * Real.log (M + k : ℕ)) n =
      τ * (Real.log ((M : ℝ) + n + 1) - Real.log ((M : ℝ) + n)) := by
  simp only [phaseIncrement, Nat.cast_add, Nat.cast_one]
  rw [add_assoc]
  ring

theorem logarithmic_phase_increment_antitone {M : ℕ} {τ : ℝ}
    (hM : 0 < M) (hτ : 0 ≤ τ) :
    Antitone (phaseIncrement (fun n ↦ τ * Real.log (M + n : ℕ))) := by
  intro i j hij
  rw [logarithmic_phase_increment_eq, logarithmic_phase_increment_eq]
  apply mul_le_mul_of_nonneg_left _ hτ
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  apply log_increment_antitone (by positivity)
  exact_mod_cast Nat.add_le_add_left hij M

theorem logarithmic_phase_increment_nonneg {M : ℕ} {τ : ℝ}
    (hM : 0 < M) (hτ : 0 ≤ τ) (n : ℕ) :
    0 ≤ phaseIncrement (fun k ↦ τ * Real.log (M + k : ℕ)) n := by
  rw [logarithmic_phase_increment_eq]
  apply mul_nonneg hτ
  apply sub_nonneg.mpr
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  exact Real.log_le_log (by positivity) (by linarith)

theorem logarithmic_phase_increment_upper {M : ℕ} {τ : ℝ}
    (hM : 0 < M) (hτ : 0 ≤ τ) (n : ℕ) :
    phaseIncrement (fun k ↦ τ * Real.log (M + k : ℕ)) n ≤ τ / M := by
  have ha := logarithmic_phase_increment_antitone hM hτ (Nat.zero_le n)
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  have h := mul_le_mul_of_nonneg_left (log_increment_upper hM') hτ
  rw [logarithmic_phase_increment_eq M 0 τ] at ha
  simp only [Nat.cast_zero, add_zero] at ha
  simpa only [mul_one_div] using ha.trans h

theorem logarithmicSum_eq_phase_sum (M N : ℕ) (τ : ℝ) :
    logarithmicSum M N τ =
      ∑ n ∈ Finset.range N, oscillatoryPhase 1 (τ * Real.log (M + n : ℕ)) := by
  apply Finset.sum_congr rfl
  intro n _
  unfold oscillatoryPhase
  congr 1
  simp only [Complex.ofReal_mul, Complex.ofReal_one, mul_one]
  ring

/-- The free-parameter bound obtained from the discrete increment partition.
It applies at every positive frequency, without an upper frequency restriction. -/
theorem logarithmicSum_spacing_bound {M : ℕ} (hM : 0 < M) (N : ℕ) {τ δ : ℝ}
    (hτ : 0 < τ) (hδ : 0 < δ) :
    ‖logarithmicSum M N τ‖ ≤
      ((⌈τ / M⌉₊ : ℕ) + 2 : ℝ) * (2 + 12 / δ + 2 * δ * (M + N + 1 : ℝ) ^ 2 / τ) := by
  let f : ℕ → ℝ := fun n ↦ τ * Real.log (M + n : ℕ)
  let K := ⌈τ / M⌉₊
  let η := τ / (M + N + 1 : ℝ) ^ 2
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  have hη : 0 < η := by dsimp only [η]; positivity
  have ha := logarithmic_phase_increment_antitone hM hτ.le
  have hrange : ∀ n < N, 0 ≤ phaseIncrement f n ∧ phaseIncrement f n ≤ 2 * Real.pi * K := by
    intro n _
    refine ⟨logarithmic_phase_increment_nonneg hM hτ.le n, ?_⟩
    have hupper := logarithmic_phase_increment_upper hM hτ.le n
    have hceil : τ / (M : ℝ) ≤ K := Nat.le_ceil _
    have hK : (0 : ℝ) ≤ K := Nat.cast_nonneg K
    have hpi := Real.one_le_pi_div_two
    change phaseIncrement (fun k ↦ τ * Real.log (M + k : ℕ)) n ≤ _
    nlinarith
  have hsep : ∀ i < N, ∀ j < N, i ≤ j →
      η * ((j : ℝ) - i) ≤ phaseIncrement f i - phaseIncrement f j := by
    intro i _ j hj hij
    exact logarithmic_phase_increment_spacing hM hτ.le hij hj.le
  have h := separated_increment_sum_bound f N K (fun _ _ _ _ hij ↦ ha hij) hδ hη hrange hsep
  rw [logarithmicSum_eq_phase_sum]
  change ‖∑ n ∈ Finset.range N, oscillatoryPhase 1 (f n)‖ ≤ _
  have heq : 2 * δ / η = 2 * δ * (M + N + 1 : ℝ) ^ 2 / τ := by
    dsimp only [η]
    rw [div_div_eq_mul_div]
  rwa [heq] at h

end Erdos421
