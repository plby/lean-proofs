import ErdosProblems.Erdos4.FGKMTFiniteLaw

/-! Weighted normalizer concentration: bad sources are charged by their target incidence. -/

namespace Erdos4.FGKMT.FiniteLaw

variable {Ω : Type*} [Fintype Ω] (ν : Erdos4.FGKMT.FiniteLaw Ω)

theorem mean_weighted_sq_sub_one (X Z : Ω → ℝ) :
    ν.mean (fun o => (X o - 1) ^ 2 * Z o) =
      ν.mean (fun o => X o ^ 2 * Z o) - 2 * ν.mean (fun o => X o * Z o) + ν.mean Z := by
  have heq : (fun o => (X o - 1) ^ 2 * Z o) =
      (fun o => (X o ^ 2 * Z o - 2 * (X o * Z o)) + Z o) := by
    funext o
    ring
  rw [heq, mean_add, mean_sub, mean_const_mul]

theorem weighted_normalizer_deviation (X Z : Ω → ℝ) {β ε δ : ℝ}
    (hfirst : ν.mean Z ≤ (1 + ε) * β)
    (hmixed : (1 - ε - δ) * β ≤ ν.mean (fun o => X o * Z o))
    (hthird : ν.mean (fun o => X o ^ 2 * Z o) ≤ (1 + ε + 3 * δ) * β) :
    ν.mean (fun o => (X o - 1) ^ 2 * Z o) ≤ (4 * ε + 5 * δ) * β := by
  rw [mean_weighted_sq_sub_one]
  linarith

theorem bad_normalizer_weighted_loss (X Z : Ω → ℝ) (hZ : ∀ o, 0 ≤ Z o)
    {A : ℝ} (hA : ν.mean (fun o => (X o - 1) ^ 2 * Z o) ≤ A) :
    ν.mean (fun o => if (1 / 2 : ℝ) < |X o - 1| then Z o else 0) ≤ 4 * A := by
  classical
  calc
    _ ≤ ν.mean (fun o => 4 * ((X o - 1) ^ 2 * Z o)) := by
      apply ν.mean_mono
      intro o
      by_cases ho : (1 / 2 : ℝ) < |X o - 1|
      · rw [if_pos ho]
        have hs : (1 / 4 : ℝ) ≤ (X o - 1) ^ 2 := by
          nlinarith [sq_abs (X o - 1)]
        have hh := mul_le_mul_of_nonneg_right hs (hZ o)
        nlinarith
      · rw [if_neg ho]
        exact mul_nonneg (by norm_num) (mul_nonneg (sq_nonneg _) (hZ o))
    _ = 4 * ν.mean (fun o => (X o - 1) ^ 2 * Z o) := ν.mean_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left hA (by norm_num)

theorem mean_div_const (f : Ω → ℝ) (s : ℝ) :
    ν.mean (fun o => f o / s) = ν.mean f / s := by
  simp only [div_eq_mul_inv, mean_mul_const]

theorem normalized_weighted_deviation (U V : Ω → ℝ) {s t β ε δ : ℝ}
    (hs : 0 < s) (ht : 0 < t)
    (hfirst : ν.mean V ≤ (1 + ε) * t * β)
    (hmixed : (1 - ε - δ) * (s * t) * β ≤ ν.mean (fun o => U o * V o))
    (hthird : ν.mean (fun o => U o ^ 2 * V o) ≤ (1 + ε + 3 * δ) * (s ^ 2 * t) * β) :
    ν.mean (fun o => (U o / s - 1) ^ 2 * (V o / t)) ≤ (4 * ε + 5 * δ) * β := by
  apply ν.weighted_normalizer_deviation (fun o => U o / s) (fun o => V o / t)
  · rw [mean_div_const]
    apply (div_le_iff₀ ht).mpr
    exact hfirst.trans_eq (by ring)
  · simp only [div_mul_div_comm, mean_div_const]
    apply (le_div_iff₀ (mul_pos hs ht)).mpr
    exact (show (1 - ε - δ) * β * (s * t) = (1 - ε - δ) * (s * t) * β by ring).le.trans hmixed
  · simp only [div_pow, div_mul_div_comm, mean_div_const]
    apply (div_le_iff₀ (mul_pos (sq_pos_of_pos hs) ht)).mpr
    exact hthird.trans_eq (by ring)

end Erdos4.FGKMT.FiniteLaw
