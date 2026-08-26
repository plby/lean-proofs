import ErdosProblems.Erdos67.StationaryContradiction

/-! # Returning from Boolean colorings to the original sign-sequence statement -/

open scoped BigOperators
open Finset

namespace Erdos67

open StationaryModel

theorem real_sign_unbounded_discrepancy (f : ℕ → ℝ)
    (hf : ∀ n, f n = -1 ∨ f n = 1) (C : ℝ) (hC : 0 ≤ C) :
    ∃ d m : ℕ, 1 ≤ d ∧ 1 ≤ m ∧ C < |∑ k ∈ range m, f ((k + 1) * d)| := by
  classical
  let b : ℕ → Bool := fun n ↦ decide (f n = 1)
  have hb (n : ℕ) : signValue (b n) = f n := by
    rcases hf n with hn | hn
    · simp only [b, hn, neg_ne_self.mpr (by norm_num : (1 : ℝ) ≠ 0), decide_false,
        signValue, Bool.false_eq_true, if_false]
    · simp only [b, hn, decide_true, signValue, if_true]
  obtain ⟨d, m, hd, hm, hgt⟩ := boolean_unbounded_discrepancy b C hC
  refine ⟨d, m, hd, hm, ?_⟩
  simpa only [homogeneousSum, hb] using hgt

theorem int_sign_unbounded_discrepancy (f : ℕ → ℤ)
    (hf : ∀ n, f n = -1 ∨ f n = 1) (C : ℝ) (hC : 0 ≤ C) :
    ∃ d m : ℕ, 1 ≤ d ∧ 1 ≤ m ∧ C < |((∑ k ∈ range m, f ((k + 1) * d) : ℤ) : ℝ)| := by
  have hfR (n : ℕ) : (f n : ℝ) = -1 ∨ (f n : ℝ) = 1 := by
    rcases hf n with hn | hn <;> simp only [hn, Int.cast_neg, Int.cast_one] <;> tauto
  obtain ⟨d, m, hd, hm, hgt⟩ := real_sign_unbounded_discrepancy (fun n ↦ (f n : ℝ)) hfR C hC
  refine ⟨d, m, hd, hm, ?_⟩
  simpa only [Int.cast_sum] using hgt

end Erdos67
