import ErdosProblems.Erdos587.HooleyConcentration

/-!
# Averaging local divisor moments by unit-window smoothing

For any finite nonnegative weighted collection of shifts, control of its
mass in every unit interval controls the shifted divisor moments. The
loss `2^q` is independent of the integer, the shifts, and their number.
-/

open MeasureTheory
open scoped BigOperators

namespace Erdos587

theorem sum_weight_mul_deltaCount_pow_le {α : Type*} (S : Finset α)
    (w t : α → ℝ) (hw : ∀ a ∈ S, 0 ≤ w a) (n : ℕ) {q : ℕ} (hq : q ≠ 0)
    (u H : ℝ)
    (hmass : ∀ v : ℝ, (∑ a ∈ S,
      (Set.Icc (u - t a - 1) (u - t a)).indicator (fun _ : ℝ => w a) v) ≤ H) :
    (∑ a ∈ S, w a * deltaCount n (u - t a) ^ q) ≤
      H * 2 ^ q * deltaMoment n q := by
  classical
  let F (a : α) : ℝ → ℝ :=
    (Set.Icc (u - t a - 1) (u - t a)).indicator
      (fun _ => w a * deltaCount n (u - t a) ^ q)
  let G : ℝ → ℝ := fun v => (2 : ℝ) ^ (q - 1) *
    (deltaCount n v ^ q + deltaCount n (v + 1) ^ q)
  have hF (a : α) : Integrable (F a) := by
    apply IntegrableOn.integrable_indicator
    · exact integrableOn_const (by simp)
    · exact measurableSet_Icc
  have hIF (a : α) : (∫ v : ℝ, F a v) = w a * deltaCount n (u - t a) ^ q := by
    rw [show F a = (Set.Icc (u - t a - 1) (u - t a)).indicator
        (fun _ : ℝ => w a * deltaCount n (u - t a) ^ q) from rfl,
      integral_indicator_const _ measurableSet_Icc, Real.volume_real_Icc]
    simp
  have hi := integrable_deltaCount_pow (n := n) hq
  have hG : Integrable G := (hi.add (hi.comp_add_right 1)).const_mul _
  have hGpos (v : ℝ) : 0 ≤ G v :=
    mul_nonneg (by positivity) (add_nonneg
      (pow_nonneg (deltaCount_nonneg n v) q)
      (pow_nonneg (deltaCount_nonneg n (v + 1)) q))
  have hpoint (v : ℝ) : (∑ a ∈ S, F a v) ≤ H * G v := by
    calc
      (∑ a ∈ S, F a v) ≤ ∑ a ∈ S,
          (Set.Icc (u - t a - 1) (u - t a)).indicator (fun _ : ℝ => w a) v * G v := by
        apply Finset.sum_le_sum
        intro a ha
        by_cases hv : v ∈ Set.Icc (u - t a - 1) (u - t a)
        · rw [show F a v = w a * deltaCount n (u - t a) ^ q from
            Set.indicator_of_mem hv _, Set.indicator_of_mem hv]
          apply mul_le_mul_of_nonneg_left _ (hw a ha)
          exact (pow_le_pow_left₀ (deltaCount_nonneg n (u - t a))
            (deltaCount_le_two_windows n hv.2 (by linarith [hv.1])) q).trans
              (add_pow_le (deltaCount_nonneg n v) (deltaCount_nonneg n (v + 1)) q)
        · rw [show F a v = 0 from Set.indicator_of_notMem hv _,
            Set.indicator_of_notMem hv, zero_mul]
      _ = (∑ a ∈ S, (Set.Icc (u - t a - 1) (u - t a)).indicator
          (fun _ : ℝ => w a) v) * G v := (Finset.sum_mul _ _ _).symm
      _ ≤ H * G v := mul_le_mul_of_nonneg_right (hmass v) (hGpos v)
  calc
    (∑ a ∈ S, w a * deltaCount n (u - t a) ^ q) = ∑ a ∈ S, ∫ v : ℝ, F a v := by
      apply Finset.sum_congr rfl
      intro a ha
      exact (hIF a).symm
    _ = ∫ v : ℝ, ∑ a ∈ S, F a v := (integral_finsetSum S (fun a _ => hF a)).symm
    _ ≤ ∫ v : ℝ, H * G v :=
      integral_mono (integrable_finsetSum S (fun a _ => hF a)) (hG.const_mul H) hpoint
    _ = H * 2 ^ q * deltaMoment n q := by
      rw [integral_const_mul]
      change H * (∫ v : ℝ, (2 : ℝ) ^ (q - 1) *
        (deltaCount n v ^ q + deltaCount n (v + 1) ^ q)) = _
      rw [integral_const_mul, integral_add hi (hi.comp_add_right 1),
        integral_add_right_eq_self (fun v : ℝ => deltaCount n v ^ q) 1]
      change H * ((2 : ℝ) ^ (q - 1) * (deltaMoment n q + deltaMoment n q)) = _
      rw [← two_mul, ← mul_assoc ((2 : ℝ) ^ (q - 1)), ← pow_succ,
        Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hq)]
      ring

end Erdos587
