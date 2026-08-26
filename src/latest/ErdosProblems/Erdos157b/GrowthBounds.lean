import ErdosProblems.Erdos157b.LocalChoiceCounts
import ErdosProblems.Erdos157b.TargetWindows
import ErdosProblems.Erdos157.GoodFibers

/-! The logarithmic tag cost is negligible compared with the quadratic prime supply. -/

namespace Erdos157.Binary

open Elementary Elementary.AuxiliaryModuli Filter
open scoped Topology

theorem eventually_tagCost_linear (C D ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ k : ℕ in atTop, C * (tagDimension k : ℝ) + D ≤ ε * k := by
  have hc : Tendsto (fun k : ℕ => D / k) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have ht : Tendsto (fun k : ℕ => (C * (tagDimension k : ℝ) + D) / k) atTop (𝓝 0) := by
    convert (tendsto_tagDimension_div_level.const_mul C).add hc using 1
    · ext k
      ring
    · simp
  filter_upwards [ht.eventually (gt_mem_nhds hε), eventually_ge_atTop 1] with k hk hk1
  have hp : (0 : ℝ) < k := by exact_mod_cast hk1
  exact ((div_lt_iff₀ hp).mp hk).le

theorem blockRadix_dyadic (i : ℕ) :
    blockRadix CoefficientField i ≤ 2 ^ (2 * i + 8 + 20 * tagDimension i) := by
  have hunit : Nat.card (ResidueField CoefficientField i)ˣ ≤
      Fintype.card CoefficientField ^ (2 * i + 1) := by
    rw [residueField_units_natCard, Nat.card_eq_fintype_card]
    exact Nat.sub_le _ _
  calc
    _ ≤ (2 ^ 7 * Fintype.card CoefficientField ^ (2 * i + 1)) *
        (2 ^ 10) ^ (2 * tagDimension i) :=
      Nat.mul_le_mul (Nat.mul_le_mul (by decide) hunit) (Nat.pow_le_pow_left (by decide) _)
    _ = _ := by
      rw [card_coefficientField, ← pow_mul, ← pow_add, ← pow_add]
      congr 1
      ring

theorem initialPlace_dyadic (k : ℕ) :
    blockPlace CoefficientField 0 k ≤ 2 ^ (k ^ 2 + 7 * k + 20 * k * tagDimension k) := by
  induction k with
  | zero => simp [blockPlace]
  | succ k ih =>
    rw [blockPlace_snoc]
    calc
      _ ≤ 2 ^ (k ^ 2 + 7 * k + 20 * k * tagDimension k) *
          2 ^ (2 * k + 8 + 20 * tagDimension k) := Nat.mul_le_mul ih (blockRadix_dyadic k)
      _ ≤ _ := by
        rw [← pow_add]
        apply Nat.pow_le_pow_right (by decide)
        have hd := tagDimension_mono (Nat.le_succ k)
        have hm := Nat.mul_le_mul_left (20 * (k + 1)) hd
        nlinarith

theorem eventually_topCapacity :
    ∀ᶠ k in atTop, 2 * blockRadix CoefficientField k ≤ Fintype.card CoefficientField ^ (3 * k) := by
  filter_upwards [eventually_tagCost_linear 20 9 1 (by norm_num)] with k hk
  have hn : 20 * tagDimension k + 9 ≤ k := by
    simp only [one_mul] at hk
    exact_mod_cast hk
  rw [card_coefficientField]
  calc
    _ ≤ 2 ^ 1 * 2 ^ (2 * k + 8 + 20 * tagDimension k) :=
      Nat.mul_le_mul_left 2 (blockRadix_dyadic k)
    _ = 2 ^ (1 + (2 * k + 8 + 20 * tagDimension k)) := (pow_add _ _ _).symm
    _ ≤ _ := Nat.pow_le_pow_right (by decide) (by omega)

theorem window_exponent_bound (k r : ℕ) (hk : 2 ≤ k) (hr : 20 * r + 7 ≤ k + 1) :
    3 + ((k + 1) ^ 2 + 7 * (k + 1) + 20 * (k + 1) * r) ≤ 10 * k ^ 2 := by
  have hm := Nat.mul_le_mul_left (k + 1) hr
  nlinarith

theorem eventually_windowCount_dyadic :
    ∀ᶠ k in atTop, 6 * blockPlace CoefficientField 0 (k + 1) ≤ 2 ^ (10 * k ^ 2) := by
  have hb := (tendsto_add_atTop_nat 1).eventually
    (eventually_tagCost_linear 20 7 1 (by norm_num))
  filter_upwards [hb, eventually_ge_atTop 2] with k hk hk2
  have hn : 20 * tagDimension (k + 1) + 7 ≤ k + 1 := by
    simp only [one_mul, Nat.cast_add, Nat.cast_one] at hk
    exact_mod_cast hk
  have hm := Nat.mul_le_mul_left (k + 1) hn
  calc
    _ ≤ 2 ^ 3 * 2 ^ ((k + 1) ^ 2 + 7 * (k + 1) + 20 * (k + 1) * tagDimension (k + 1)) :=
      Nat.mul_le_mul (by decide) (initialPlace_dyadic (k + 1))
    _ = 2 ^ (3 + ((k + 1) ^ 2 + 7 * (k + 1) + 20 * (k + 1) * tagDimension (k + 1))) :=
      (pow_add _ _ _).symm
    _ ≤ _ := Nat.pow_le_pow_right (by decide) (window_exponent_bound k _ hk2 hn)

theorem excess_degree_lower (k : ℕ) : k ^ 2 ≤ 20 * (3 * levelDegree k - k ^ 2) := by
  have hr := levelDegree_lower k
  have hn : 7 * k ^ 2 ≤ 20 * levelDegree k := by
    exact_mod_cast (show (7 : ℝ) * (k : ℝ) ^ 2 ≤ 20 * (levelDegree k : ℝ) by linarith)
  have hs := Nat.sub_add_cancel (square_le_triple_levelDegree k)
  nlinarith

theorem eventually_choice_exponent_small :
    ∀ᶠ k in atTop, 10 + 7 * k + 3 * choiceExponent k ≤ 3 * levelDegree k - k ^ 2 := by
  filter_upwards [eventually_tagCost_linear 660 760 1 (by norm_num),
    eventually_ge_atTop 1] with k hk hk1
  have hn : 660 * tagDimension k + 760 ≤ k := by
    simp only [one_mul] at hk
    exact_mod_cast hk
  have hm := Nat.mul_le_mul_left k hn
  have he := excess_degree_lower k
  unfold choiceExponent
  nlinarith

theorem eventually_coverage_mass_nat :
    ∀ᶠ k in atTop, 1024 * levelDegree k ^ 3 *
      Fintype.card (LocalChoice CoefficientField k) ^ 3 * 2 ^ k ≤ 2 ^ (3 * levelDegree k - k ^ 2) := by
  filter_upwards [eventually_choice_exponent_small, eventually_ge_atTop 4] with k hk hk4
  have hd : levelDegree k ≤ k ^ 2 := by
    have := double_levelDegree_lt_square k hk4
    omega
  have hdpow : levelDegree k ^ 3 ≤ 2 ^ (6 * k) := by
    calc
      _ ≤ (k ^ 2) ^ 3 := Nat.pow_le_pow_left hd _
      _ = k ^ 6 := by rw [← pow_mul]
      _ ≤ (2 ^ k) ^ 6 := Nat.pow_le_pow_left Nat.lt_two_pow_self.le _
      _ = _ := by rw [← pow_mul, mul_comm k 6]
  have hchoice : Fintype.card (LocalChoice CoefficientField k) ^ 3 ≤ 2 ^ (3 * choiceExponent k) := by
    calc
      _ ≤ (2 ^ choiceExponent k) ^ 3 := Nat.pow_le_pow_left (card_localChoice_binary_le k) 3
      _ = _ := by rw [← pow_mul, mul_comm]
  calc
    _ ≤ (2 ^ 10 * 2 ^ (6 * k)) * 2 ^ (3 * choiceExponent k) * 2 ^ k :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul (Nat.mul_le_mul_left 1024 hdpow) hchoice)
    _ = 2 ^ (10 + 7 * k + 3 * choiceExponent k) := by
      rw [← pow_add, ← pow_add, ← pow_add]
      congr 1
      ring
    _ ≤ _ := Nat.pow_le_pow_right (by decide) hk

theorem eventually_coverage_trial_mass :
    ∀ᶠ k in atTop, (2 : ℝ) ^ k ≤ fiberThreshold (K := CoefficientField) k /
      (Fintype.card (LocalChoice CoefficientField k) : ℝ) ^ 3 := by
  filter_upwards [eventually_coverage_mass_nat, eventually_ge_atTop 4] with k hk hk4
  have hdpos : (0 : ℝ) < levelDegree k := by
    have h := levelDegree_lower k
    have hk' : (4 : ℝ) ≤ k := by exact_mod_cast hk4
    nlinarith
  have hcpos : (0 : ℝ) < Fintype.card (LocalChoice CoefficientField k) := by
    exact_mod_cast Fintype.card_pos (α := LocalChoice CoefficientField k)
  have hr : (1024 : ℝ) * (levelDegree k : ℝ) ^ 3 *
      (Fintype.card (LocalChoice CoefficientField k) : ℝ) ^ 3 * (2 : ℝ) ^ k ≤
        (2 : ℝ) ^ (3 * levelDegree k - k ^ 2) := by exact_mod_cast hk
  unfold fiberThreshold
  conv_rhs => lhs; lhs; rw [card_coefficientField]
  apply (le_div_iff₀ (pow_pos hcpos 3)).mpr
  apply (le_div_iff₀ (by positivity)).mpr
  calc
    _ = (1024 : ℝ) * (levelDegree k : ℝ) ^ 3 *
        (Fintype.card (LocalChoice CoefficientField k) : ℝ) ^ 3 * (2 : ℝ) ^ k := by ring
    _ ≤ _ := hr

end Erdos157.Binary
