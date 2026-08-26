import ErdosProblems.Erdos421.FirstDerivativeSum

/-! # A small-frequency bound for logarithmic exponential sums -/

namespace Erdos421

theorem log_increment_eq {x : ℝ} (hx : 0 < x) :
    Real.log (x + 1) - Real.log x = Real.log (1 + x⁻¹) := by
  rw [← Real.log_div (by linarith : x + 1 ≠ 0) hx.ne']
  congr 1
  field_simp

theorem log_increment_antitone {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) :
    Real.log (y + 1) - Real.log y ≤ Real.log (x + 1) - Real.log x := by
  rw [log_increment_eq hx, log_increment_eq (hx.trans_le hxy)]
  have hy := hx.trans_le hxy
  exact Real.log_le_log (by positivity) (add_le_add le_rfl (inv_anti₀ hx hxy))

theorem log_increment_upper {x : ℝ} (hx : 0 < x) :
    Real.log (x + 1) - Real.log x ≤ 1 / x := by
  rw [log_increment_eq hx]
  have h := Real.log_le_sub_one_of_pos (show 0 < 1 + x⁻¹ by positivity)
  simpa only [add_sub_cancel_left, one_div] using h

noncomputable def logarithmicSum (M N : ℕ) (τ : ℝ) : ℂ :=
  ∑ n ∈ Finset.range N, oscillatoryPhase (Real.log (M + n : ℕ)) τ

theorem logarithmicSum_small_frequency_bound {M : ℕ} (hM : 0 < M) (N : ℕ)
    {τ : ℝ} (hτ : 0 < τ) (hτM : τ ≤ M) :
    ‖logarithmicSum M N τ‖ ≤ 8 * (M + N + 1 : ℝ) / τ := by
  let f : ℕ → ℝ := fun n ↦ τ * Real.log (M + n : ℕ)
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  have hxpos : ∀ n : ℕ, (0 : ℝ) < M + n := fun n ↦ by positivity
  have hinc : ∀ n, phaseIncrement f n =
      τ * (Real.log ((M : ℝ) + n + 1) - Real.log ((M : ℝ) + n)) := by
    intro n
    simp only [phaseIncrement, f, Nat.cast_add, Nat.cast_one]
    rw [add_assoc]
    ring
  have hanti : Antitone (phaseIncrement f) := by
    intro i j hij
    rw [hinc, hinc]
    apply mul_le_mul_of_nonneg_left _ hτ.le
    exact log_increment_antitone (hxpos i) (by exact_mod_cast Nat.add_le_add_left hij M)
  have hlow : τ / ((M : ℝ) + N + 1) ≤ phaseIncrement f N := by
    have h := log_difference_lower (hxpos N) (show (M : ℝ) + N < M + N + 1 by linarith)
    simp only [add_sub_cancel_left] at h
    rw [hinc]
    have hmul := mul_le_mul_of_nonneg_left h hτ.le
    simpa only [mul_one_div] using hmul
  have hpos : 0 < phaseIncrement f N :=
    (div_pos hτ (by positivity)).trans_le hlow
  have hone : phaseIncrement f 0 ≤ 1 := by
    rw [hinc, Nat.cast_zero, add_zero]
    have h := mul_le_mul_of_nonneg_left (log_increment_upper hM') hτ.le
    have hdiv : τ / (M : ℝ) ≤ 1 := (div_le_one hM').mpr hτM
    calc
      _ ≤ τ * (1 / (M : ℝ)) := h
      _ = τ / (M : ℝ) := by ring
      _ ≤ 1 := hdiv
  have hsum := monotone_increment_sum_bound f N hanti hpos hone
  have heq : logarithmicSum M N τ =
      ∑ n ∈ Finset.range N, oscillatoryPhase 1 (f n) := by
    apply Finset.sum_congr rfl
    intro n _
    unfold oscillatoryPhase
    congr 1
    simp only [f, Complex.ofReal_mul, Complex.ofReal_one, mul_one]
    ring
  rw [heq]
  apply hsum.trans
  apply (div_le_div_iff₀ hpos hτ).mpr
  have hden : (0 : ℝ) < (M : ℝ) + N + 1 := by positivity
  have hmul : τ ≤ phaseIncrement f N * ((M : ℝ) + N + 1) := (div_le_iff₀ hden).mp hlow
  nlinarith

end Erdos421
