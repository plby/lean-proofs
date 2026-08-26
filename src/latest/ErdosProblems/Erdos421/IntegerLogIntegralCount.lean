import ErdosProblems.Erdos421.PrimeFreeWindows

/-! # Counting integer starts by disjoint logarithmic integration intervals -/

namespace Erdos421

open MeasureTheory

theorem log_integer_step_lower {m : ℕ} (hm : 0 < m) :
    1 / ((m : ℝ) + 1) ≤ Real.log (m + 1 : ℝ) - Real.log m := by
  have hmp : (0 : ℝ) < m := by exact_mod_cast hm
  have hm1 : 0 < (m : ℝ) + 1 := by positivity
  have h := Real.one_sub_inv_le_log_of_pos (div_pos hm1 hmp)
  rw [Real.log_div hm1.ne' hmp.ne'] at h
  have heq : 1 - (((m : ℝ) + 1) / m)⁻¹ = 1 / ((m : ℝ) + 1) := by field_simp; ring
  rwa [heq] at h

theorem integer_log_integral_step_lower {f : ℝ → ℝ} (hf : Continuous f)
    {X m : ℕ} (hX : 1 ≤ X) (hm : m ∈ Finset.Ico X (2 * X)) {c : ℝ} (hc : 0 ≤ c)
    (hpoint : ∀ y ∈ Set.Icc (Real.log (m : ℝ)) (Real.log (m + 1 : ℝ)), c ≤ f y) :
    c / (2 * X : ℝ) ≤ ∫ y in Real.log (m : ℝ)..Real.log (m + 1 : ℝ), f y := by
  obtain ⟨hXm, hmX⟩ := Finset.mem_Ico.mp hm
  have hmn : 0 < m := hX.trans hXm
  have hmp : (0 : ℝ) < m := by exact_mod_cast hmn
  have hmx : (m : ℝ) + 1 ≤ 2 * X := by exact_mod_cast (show m + 1 ≤ 2 * X by omega)
  have hab : Real.log (m : ℝ) ≤ Real.log (m + 1 : ℝ) := Real.log_le_log hmp (by linarith)
  have hmono := intervalIntegral.integral_mono_on (μ := volume) hab
    (intervalIntegrable_const (c := c)) (hf.intervalIntegrable _ _) hpoint
  rw [intervalIntegral.integral_const, smul_eq_mul] at hmono
  calc
    _ = c * (1 / (2 * X : ℝ)) := by ring
    _ ≤ c * (1 / ((m : ℝ) + 1)) := mul_le_mul_of_nonneg_left
      (one_div_le_one_div_of_le (by positivity) hmx) hc
    _ ≤ c * (Real.log (m + 1 : ℝ) - Real.log m) :=
      mul_le_mul_of_nonneg_left (log_integer_step_lower hmn) hc
    _ = (Real.log (m + 1 : ℝ) - Real.log m) * c := by ring
    _ ≤ _ := hmono

theorem integer_log_integral_card_le {f : ℝ → ℝ} (hf : Continuous f)
    (hf0 : ∀ y, 0 ≤ f y) {X : ℕ} (hX : 1 ≤ X) (S : Finset ℕ)
    (hS : S ⊆ Finset.Ico X (2 * X)) {c : ℝ} (hc : 0 ≤ c)
    (hpoint : ∀ m ∈ S, ∀ y ∈ Set.Icc (Real.log (m : ℝ)) (Real.log (m + 1 : ℝ)), c ≤ f y) :
    (S.card : ℝ) * c / (2 * X : ℝ) ≤
      ∫ y in Real.log (X : ℝ)..Real.log (2 * X : ℝ), f y := by
  have htel := intervalIntegral.sum_integral_adjacent_intervals_Ico (f := f) (μ := volume)
    (a := fun m : ℕ ↦ Real.log m) (show X ≤ 2 * X by omega)
    (fun m _ ↦ hf.intervalIntegrable _ _)
  calc
    _ = ∑ _m ∈ S, c / (2 * X : ℝ) := by
      rw [Finset.sum_const, nsmul_eq_mul]
      ring
    _ ≤ ∑ m ∈ S, ∫ y in Real.log (m : ℝ)..Real.log (m + 1 : ℝ), f y :=
      Finset.sum_le_sum (fun m hm ↦ integer_log_integral_step_lower hf hX (hS hm) hc (hpoint m hm))
    _ ≤ ∑ m ∈ Finset.Ico X (2 * X),
        ∫ y in Real.log (m : ℝ)..Real.log (m + 1 : ℝ), f y := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hS
      intro m hm hnot
      have hmn : 0 < m := hX.trans (Finset.mem_Ico.mp hm).1
      have hmp : (0 : ℝ) < m := by exact_mod_cast hmn
      exact intervalIntegral.integral_nonneg_of_forall (Real.log_le_log hmp (by linarith)) hf0
    _ = _ := by
      simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_mul, Nat.cast_ofNat] using htel

end Erdos421
