/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTConditionedState

/-! # Finite event unions and averaging over good and bad states -/

namespace Erdos4b.FGKMT

noncomputable section

open scoped BigOperators

variable {α Ξ : Type*} [Fintype Ξ]

theorem finite_event_union_mass_le (μ : Ξ → ℝ) (hμ : ∀ s, 0 ≤ μ s)
    (e : Finset α) (B : α → Ξ → Prop) [∀ v s, Decidable (B v s)] :
    (∑ s, if ∃ v ∈ e, B v s then μ s else 0) ≤
      ∑ v ∈ e, ∑ s, if B v s then μ s else 0 := by
  classical
  calc
    _ ≤ ∑ s, ∑ v ∈ e, if B v s then μ s else 0 := by
      apply Finset.sum_le_sum
      intro s _hs
      have hn (v : α) : 0 ≤ (if B v s then μ s else 0) := ite_nonneg (hμ s) le_rfl
      by_cases hh : ∃ v ∈ e, B v s
      · rw [if_pos hh]
        obtain ⟨v, hv, hB⟩ := hh
        have h := Finset.single_le_sum (fun u _hu => hn u) hv
        simpa only [if_pos hB] using h
      · rw [if_neg hh]
        exact Finset.sum_nonneg fun v _hv => hn v
    _ = _ := Finset.sum_comm

theorem finite_good_bad_mean_error (μ Y : Ξ → ℝ) (hμ : ∀ s, 0 ≤ μ s)
    (hμsum : ∑ s, μ s = 1) (B : Ξ → Prop) [DecidablePred B]
    {T E : ℝ} (hT0 : 0 ≤ T) (hT1 : T ≤ 1) (hE : 0 ≤ E)
    (hY0 : ∀ s, 0 ≤ Y s) (hY1 : ∀ s, Y s ≤ 1)
    (hgood : ∀ s, ¬B s → |Y s - T| ≤ E) :
    |(∑ s, μ s * Y s) - T| ≤ E + ∑ s, if B s then μ s else 0 := by
  have hid : (∑ s, μ s * Y s) - T = ∑ s, μ s * (Y s - T) := by
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hμsum, one_mul]
  rw [hid]
  calc
    _ ≤ ∑ s, |μ s * (Y s - T)| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ s, μ s * |Y s - T| := by
      apply Finset.sum_congr rfl
      intro s _hs
      rw [abs_mul, abs_of_nonneg (hμ s)]
    _ ≤ ∑ s, (μ s * E + if B s then μ s else 0) := by
      apply Finset.sum_le_sum
      intro s _hs
      by_cases hB : B s
      · rw [if_pos hB]
        have hmax : |Y s - T| ≤ 1 := abs_le.mpr ⟨by linarith [hY0 s], by linarith [hY1 s]⟩
        calc
          _ ≤ μ s * 1 := mul_le_mul_of_nonneg_left hmax (hμ s)
          _ ≤ _ := by nlinarith [mul_nonneg (hμ s) hE]
      · rw [if_neg hB, add_zero]
        exact mul_le_mul_of_nonneg_left (hgood s hB) (hμ s)
    _ = _ := by rw [Finset.sum_add_distrib, ← Finset.sum_mul, hμsum, one_mul]

theorem relative_mass_times_mean_error {q p Y T η E : ℝ}
    (hq : 0 ≤ q) (hE : 0 ≤ E)
    (hcont : |q - p| ≤ η * p) (hmean : |Y - Real.exp (-T)| ≤ E) :
    |q * Y - p * Real.exp (-T)| ≤
      (η + (1 + η) * Real.exp T * E) * (p * Real.exp (-T)) := by
  have he := (Real.exp_pos (-T)).le
  have hqupper : q ≤ (1 + η) * p := by linarith [(abs_le.mp hcont).2]
  have hid : q * Y - p * Real.exp (-T) =
      q * (Y - Real.exp (-T)) + (q - p) * Real.exp (-T) := by ring
  rw [hid]
  calc
    _ ≤ |q * (Y - Real.exp (-T))| + |(q - p) * Real.exp (-T)| := abs_add_le _ _
    _ = q * |Y - Real.exp (-T)| + |q - p| * Real.exp (-T) := by
      rw [abs_mul, abs_mul, abs_of_nonneg hq, abs_of_nonneg he]
    _ ≤ q * E + (η * p) * Real.exp (-T) :=
      add_le_add (mul_le_mul_of_nonneg_left hmean hq)
        (mul_le_mul_of_nonneg_right hcont he)
    _ ≤ ((1 + η) * p) * E + (η * p) * Real.exp (-T) :=
      add_le_add (mul_le_mul_of_nonneg_right hqupper hE) le_rfl
    _ = _ := by
      rw [Real.exp_neg]
      field_simp
      ring

end

end Erdos4b.FGKMT
