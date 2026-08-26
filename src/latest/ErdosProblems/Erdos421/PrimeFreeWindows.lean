import ErdosProblems.Erdos421.PrimeMinorantTransfer
import ErdosProblems.Erdos421.LongGaps

/-! # A prime-free integer interval forces the short prime minorant to be nonpositive -/

namespace Erdos421

theorem logarithmicPrimeWindow_eq_zero_of_primeFree (B m H : ℕ) {δ y : ℝ}
    (hδ : 0 < δ) (hfree : ∀ p ∈ Finset.Icc m (m + H), ¬ p.Prime)
    (hlo : (m : ℝ) ≤ Real.exp y) (hhi : Real.exp (y + δ) ≤ (m + H : ℕ)) :
    logarithmicPrimeWindow B δ y = 0 := by
  apply Finset.sum_eq_zero
  intro p hp
  obtain ⟨_, hpp⟩ := Finset.mem_filter.mp hp
  by_contra hne
  have hc : logarithmicIntegerWeight δ y p ≠ 0 := by
    intro hzero
    exact hne (by rw [hzero, Complex.zero_re])
  obtain ⟨hpl, hph⟩ := logarithmicIntegerWeight_nonzero hδ hpp.pos hc
  have hmp : m ≤ p := by exact_mod_cast (hlo.trans hpl.le)
  have hpH : p ≤ m + H := by exact_mod_cast (hph.le.trans hhi)
  exact hfree p (Finset.mem_Icc.mpr ⟨hmp, hpH⟩) hpp

theorem integer_log_interval_subset {X m : ℕ} (hX : 1 ≤ X) (hm : m ∈ Finset.Ico X (2 * X)) :
    Set.Icc (Real.log (m : ℝ)) (Real.log (m + 1 : ℝ)) ⊆
      Set.Icc (Real.log (X : ℝ)) (Real.log (2 * X : ℝ)) := by
  obtain ⟨hXm, hmX⟩ := Finset.mem_Ico.mp hm
  have hXp : (0 : ℝ) < X := by exact_mod_cast hX
  have hmx : (m : ℝ) + 1 ≤ 2 * X := by exact_mod_cast (show m + 1 ≤ 2 * X by omega)
  intro y hy
  exact ⟨(Real.log_le_log hXp (by exact_mod_cast hXm)).trans hy.1,
    hy.2.trans (Real.log_le_log (by positivity) hmx)⟩

theorem integer_log_window_endpoint {X m H : ℕ} (hX : 1 ≤ X)
    (hm : m ∈ Finset.Ico X (2 * X)) {δ y : ℝ} (hδ : 0 ≤ δ) (hδhi : δ ≤ 1 / 2)
    (hH : 1 + 4 * δ * X ≤ (H : ℝ))
    (hy : y ∈ Set.Icc (Real.log (m : ℝ)) (Real.log (m + 1 : ℝ))) :
    (m : ℝ) ≤ Real.exp y ∧ Real.exp (y + δ) ≤ (m + H : ℕ) := by
  obtain ⟨hXm, hmX⟩ := Finset.mem_Ico.mp hm
  have hmp : (0 : ℝ) < m := by exact_mod_cast (hX.trans hXm)
  have hmx : (m : ℝ) + 1 ≤ 2 * X := by exact_mod_cast (show m + 1 ≤ 2 * X by omega)
  have hlo := Real.exp_le_exp.mpr hy.1
  rw [Real.exp_log hmp] at hlo
  have hhi := Real.exp_le_exp.mpr hy.2
  rw [Real.exp_log (by positivity : 0 < (m : ℝ) + 1)] at hhi
  have hE := exp_le_one_add_two_mul_half hδ hδhi
  refine ⟨hlo, ?_⟩
  calc
    _ = Real.exp y * Real.exp δ := Real.exp_add _ _
    _ ≤ ((m : ℝ) + 1) * (1 + 2 * δ) :=
      mul_le_mul hhi hE (Real.exp_pos δ).le (by positivity)
    _ ≤ _ := by
      have hmul := mul_le_mul_of_nonneg_left hmx (show 0 ≤ 2 * δ by positivity)
      push_cast
      nlinarith

theorem primeMinorant_nonpos_on_primeFree {X m H : ℕ} (hX : 1 ≤ X)
    (hm : m ∈ Finset.Ico X (2 * X))
    (hfree : ∀ p ∈ Finset.Icc m (m + H), ¬ p.Prime) {δ y : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1 / 2) (hδlog : δ ≤ Real.log (3 / 2))
    (hH : 1 + 4 * δ * X ≤ (H : ℝ))
    (hy : y ∈ Set.Icc (Real.log (m : ℝ)) (Real.log (m + 1 : ℝ))) :
    intermediatePrimeMinorant X δ y ≤ 0 := by
  obtain ⟨hlo, hhi⟩ := integer_log_window_endpoint hX hm hδ.le hδhi hH hy
  have hzero := logarithmicPrimeWindow_eq_zero_of_primeFree (3 * X) m H hδ hfree hlo hhi
  have h := intermediatePrimeMinorant_le_primeWindow hX hδ hδlog
    (integer_log_interval_subset hX hm hy)
  exact h.trans_eq hzero

end Erdos421
