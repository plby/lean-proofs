/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Explicit bounds on the exceptional coordinates of a generalized frame member.
Informal source: BBMST Lemma 7.1.
Formal author: OpenAI Codex.
-/

import ErdosProblems.Erdos1189.GeneralizedFrame

namespace Erdos1189.Grid

open Finset

variable {ι : Type*} {q : ι → ℕ} [Fintype ι] [DecidableEq ι]

lemma boxMeasureOn_le_half_pow (hq : ∀ i, 2 ≤ q i) (J : Finset ι) (H : Box q) :
    boxMeasureOn J H ≤ (1 / 2 : ℝ) ^ (J ∩ fixed H).card := by
  classical
  rw [boxMeasureOn_eq_fixed]
  calc
    _ ≤ ∏ _i ∈ J ∩ fixed H, (1 / 2 : ℝ) := by
      apply prod_le_prod
      · intro i _
        positivity
      · intro i _
        exact one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast hq i)
    _ = _ := by simp

lemma boxMeasureOn_le_inv_card (hq : ∀ i, 2 ≤ q i) (J : Finset ι) (H : Box q) :
    boxMeasureOn J H ≤ 1 / ((J ∩ fixed H).card + 1 : ℝ) := by
  have hpow : ((J ∩ fixed H).card : ℝ) + 1 ≤ 2 ^ (J ∩ fixed H).card := by
    exact_mod_cast Nat.succ_le_of_lt (Nat.lt_two_pow_self (n := (J ∩ fixed H).card))
  calc
    _ ≤ (1 / 2 : ℝ) ^ (J ∩ fixed H).card := boxMeasureOn_le_half_pow hq J H
    _ = 1 / (2 : ℝ) ^ (J ∩ fixed H).card := by rw [div_pow, one_pow]
    _ ≤ _ := one_div_le_one_div_of_le (by positivity) hpow

lemma fixed_card_lt_inverse_of_measure {δ : ℝ} (hδ : 0 < δ) (hq : ∀ i, 2 ≤ q i)
    (J : Finset ι) (H : Box q) (hm : δ < boxMeasureOn J H) :
    ((J ∩ fixed H).card : ℝ) < 1 / δ := by
  have h := hm.trans_le (boxMeasureOn_le_inv_card hq J H)
  have hprod := (lt_div_iff₀ (by positivity)).mp h
  apply (lt_div_iff₀ hδ).mpr
  nlinarith

omit [DecidableEq ι] in
lemma coordinate_not_fixed_of_large_measure {δ : ℝ} (hδ : 0 < δ) (hq : ∀ i, 1 ≤ q i)
    (J : Finset ι) (H : Box q) (hm : δ < boxMeasureOn J H)
    {j : ι} (hj : j ∈ J) (hsize : 1 / δ ≤ (q j : ℝ)) : j ∉ fixed H := by
  intro hfixed
  have h := hm.trans_le (boxMeasureOn_le_coordinate hq J H hj hfixed)
  have hq0 : (0 : ℝ) < q j := lt_of_lt_of_le (by norm_num)
    (by exact_mod_cast hq j : (1 : ℝ) ≤ q j)
  have hprod := (lt_div_iff₀ hq0).mp h
  have hlarge := (div_le_iff₀ hδ).mp hsize
  nlinarith

end Erdos1189.Grid
