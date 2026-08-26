/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
The concentration exponent at the chosen window and cap scales.
Formal proof: Codex.
-/
import ErdosProblems.Erdos521.WindowCapBounds
import ErdosProblems.Erdos521.CentralIntervalMoments

namespace Erdos521

theorem mainBinSet_card_pos {j : ℕ} (hj : 9 ≤ j) : 0 < (mainBinSet j).card :=
  Finset.card_pos.mpr ⟨Nat.sqrt j, Finset.mem_Ico.mpr ⟨le_rfl, central_bin_endpoints_strict hj⟩⟩

theorem window_concentration_ratio_lower {j : ℕ} (hj : 9 ≤ j) (η : ℝ) :
    (η ^ 2 / 18) * (windowWidthScale j : ℝ) ≤
      (η * (j : ℝ)) ^ 2 / (2 * ((2 * windowWidthScale j + 1 : ℕ) : ℝ) ^ 2 *
        ((mainBinSet j).card : ℝ) * ((windowCapScale j : ℝ) / 2) ^ 2) := by
  let D := 2 * ((2 * windowWidthScale j + 1 : ℕ) : ℝ) ^ 2 *
    ((mainBinSet j).card : ℝ) * ((windowCapScale j : ℝ) / 2) ^ 2
  have hcard : (0 : ℝ) < (mainBinSet j).card := by exact_mod_cast mainBinSet_card_pos hj
  have hcap : (0 : ℝ) < windowCapScale j := by
    exact_mod_cast (show 0 < windowCapScale j by dsimp [windowCapScale]; omega)
  have hD : 0 < D := by dsimp [D]; positivity
  have hupper : D ≤ 18 * (j : ℝ) * (windowWidthScale j : ℝ) ^ 3 := by
    calc
      D = (((2 * windowWidthScale j + 1 : ℕ) : ℝ) ^ 2 * (windowCapScale j : ℝ) ^ 2) *
          ((mainBinSet j).card : ℝ) / 2 := by dsimp [D]; ring
      _ ≤ (36 * (windowWidthScale j : ℝ) ^ 3) * (j : ℝ) / 2 := by
        apply div_le_div_of_nonneg_right _ (by norm_num)
        exact mul_le_mul (window_group_cap_parameter_le (by omega))
          (by exact_mod_cast mainBinSet_card_le j) (Nat.cast_nonneg _) (by positivity)
      _ = _ := by ring
  have hq : (windowWidthScale j : ℝ) ^ 4 ≤ j := by exact_mod_cast windowWidthScale_pow_four_le j
  apply (le_div_iff₀ hD).mpr
  calc
    ((η ^ 2 / 18) * (windowWidthScale j : ℝ)) * D ≤
        ((η ^ 2 / 18) * (windowWidthScale j : ℝ)) * (18 * j * (windowWidthScale j : ℝ) ^ 3) :=
      mul_le_mul_of_nonneg_left hupper (by positivity)
    _ = η ^ 2 * j * (windowWidthScale j : ℝ) ^ 4 := by ring
    _ ≤ η ^ 2 * j * j := mul_le_mul_of_nonneg_left hq (by positivity)
    _ = (η * (j : ℝ)) ^ 2 := by ring

theorem window_concentration_exponent_le {j : ℕ} (hj : 9 ≤ j) (η : ℝ) :
    -(η * (j : ℝ)) ^ 2 / (2 * ((2 * windowWidthScale j + 1 : ℕ) : ℝ) ^ 2 *
      ((mainBinSet j).card : ℝ) * ((windowCapScale j : ℝ) / 2) ^ 2) ≤
      -(η ^ 2 / 36) * (j : ℝ) ^ (1 / 4 : ℝ) := by
  have hratio := window_concentration_ratio_lower hj η
  have hscale := mul_le_mul_of_nonneg_left (windowWidthScale_lower_half (by omega : 1 ≤ j))
    (show 0 ≤ η ^ 2 / 18 by positivity)
  rw [neg_div]
  nlinarith

end Erdos521
