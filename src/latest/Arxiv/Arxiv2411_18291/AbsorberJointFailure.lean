import Arxiv.Arxiv2411_18291.FailedOutputComposition
import Arxiv.Arxiv2411_18291.ExplicitAbsorberGreedyTail

/-! # The joint error budget for four dependent absorber stages -/

namespace Arxiv2411_18291

theorem four_absorber_stage_errors_lt {q r n : ℕ} (hqr : r + 1 < q)
    (hn : paperSizeThreshold q (r + 1) ≤ n) :
    4 * Real.exp (-((n : ℝ) ^ (2 / 5 : ℝ))) <
      Real.exp (-((n : ℝ) ^ (1 / 10 : ℝ))) := by
  have hn1 : (1 : ℝ) ≤ n := by
    exact_mod_cast (paperSizeThreshold_one_lt hqr).le.trans hn
  have hn0 : (0 : ℝ) < n := lt_of_lt_of_le zero_lt_one hn1
  have hqR : (2 : ℝ) ≤ q := by exact_mod_cast (show 2 ≤ q by omega)
  have hg := boost_threshold_rpow_lower (s := 1) (by omega : 2 ≤ q)
    ((boost_threshold_le_paper_threshold hqr).trans hn)
    (by norm_num : (0 : ℝ) ≤ 1 / 10) (by linarith only [hqR])
  simp only [pow_one] at hg
  have hx : (8 : ℝ) ≤ (n : ℝ) ^ (1 / 10 : ℝ) := by linarith only [hg, hqR]
  have hxx : ((n : ℝ) ^ (1 / 10 : ℝ)) ^ 2 ≤ (n : ℝ) ^ (2 / 5 : ℝ) := by
    calc
      _ = (n : ℝ) ^ (1 / 5 : ℝ) := by
        rw [pow_two, ← Real.rpow_add hn0]
        norm_num
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num)
  have hgap : (n : ℝ) ^ (1 / 10 : ℝ) + 4 ≤ (n : ℝ) ^ (2 / 5 : ℝ) := by
    nlinarith only [hx, hxx]
  have hfour : (4 : ℝ) < Real.exp 4 := by
    have he := Real.add_one_le_exp (4 : ℝ)
    linarith only [he]
  calc
    _ < Real.exp 4 * Real.exp (-((n : ℝ) ^ (2 / 5 : ℝ))) :=
      mul_lt_mul_of_pos_right hfour (Real.exp_pos _)
    _ = Real.exp (4 - (n : ℝ) ^ (2 / 5 : ℝ)) := by rw [← Real.exp_add]; rfl
    _ ≤ _ := Real.exp_le_exp.mpr (by linarith only [hgap])

theorem fourStageOutput_absorber_failure_lt {q r n : ℕ} (hqr : r + 1 < q)
    (hn : paperSizeThreshold q (r + 1) ≤ n)
    {A : Type*} [Finite A] {B : A → Type*} [∀ a, Finite (B a)]
    {C : (a : A) → B a → Type*} [∀ a b, Finite (C a b)]
    {D : (a : A) → (b : B a) → C a b → Type*}
    (p : PMF (Option A)) (s₂ : ∀ a, PMF (Option (B a)))
    (s₃ : ∀ a b, PMF (Option (C a b))) (s₄ : ∀ a b c, PMF (Option (D a b c)))
    (h₁ : (p none).toReal ≤ Real.exp (-((n : ℝ) ^ (2 / 5 : ℝ))))
    (h₂ : ∀ a, (s₂ a none).toReal ≤ Real.exp (-((n : ℝ) ^ (2 / 5 : ℝ))))
    (h₃ : ∀ a b, (s₃ a b none).toReal ≤ Real.exp (-((n : ℝ) ^ (2 / 5 : ℝ))))
    (h₄ : ∀ a b c, (s₄ a b c none).toReal ≤ Real.exp (-((n : ℝ) ^ (2 / 5 : ℝ)))) :
    (FiniteHistoryProcess.fourStageOutput p s₂ s₃ s₄ none).toReal <
      Real.exp (-((n : ℝ) ^ (1 / 10 : ℝ))) := by
  have h := FiniteHistoryProcess.fourStageOutput_failure_real_le p s₂ s₃ s₄
    (Real.exp_pos _).le (Real.exp_pos _).le (Real.exp_pos _).le (Real.exp_pos _).le
    h₁ h₂ h₃ h₄
  have hb := four_absorber_stage_errors_lt hqr hn
  linarith only [h, hb]

end Arxiv2411_18291
