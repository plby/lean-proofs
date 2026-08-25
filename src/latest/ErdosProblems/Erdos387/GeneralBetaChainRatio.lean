/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

/-!
# Rosser chain ratios with a variable beta parameter

This is the parameter-generic version of `Erdos851.BetaChainRatio`.  Writing
`c = beta + 1`, two consecutive selected primes consume at most two copies
of the later logarithm.  The backward budget therefore inflates by

`rho(c) = c / (c - 2) = (beta + 1) / (beta - 1)`.
-/

namespace Erdos387.GeneralBetaChainRatio

open scoped BigOperators

noncomputable def inflation (c : ℝ) : ℝ := c / (c - 2)

lemma inflation_pos {c : ℝ} (hc : 2 < c) : 0 < inflation c := by
  exact div_pos (by linarith) (by linarith)

lemma inflation_one_le {c : ℝ} (hc : 2 < c) : 1 ≤ inflation c := by
  rw [inflation, le_div_iff₀ (by linarith)]
  linarith

lemma inflation_mul_sub_two {c : ℝ} (hc : 2 < c) :
    inflation c * (c - 2) = c := by
  rw [inflation, div_mul_cancel₀]
  linarith

lemma c_mul_inflation {c : ℝ} (hc : 2 < c) :
    c * inflation c = c + 2 * inflation c := by
  have h := inflation_mul_sub_two hc
  nlinarith

/-- Abstract backwards-budget induction, now with symbolic stopping
coefficient `c`. -/
theorem backward_budget_bound
    (c : ℝ) (a B : ℕ → ℝ) (m : ℕ)
    (hc : 2 < c)
    (ha0 : 0 < a 0)
    (hterminal : B 0 < c * a 0)
    (hpass : ∀ k < m, c * a (k + 1) ≤ B (k + 1))
    (hstep : ∀ k < m, B (k + 1) ≤ B k + 2 * a (k + 1)) :
    B m < c * inflation c ^ m * a 0 ∧
      a m ≤ inflation c ^ m * a 0 := by
  induction m with
  | zero =>
      simpa using And.intro hterminal (le_refl (a 0))
  | succ m ih =>
      have hm : m < m + 1 := by omega
      have ih' := ih (fun k hk => hpass k (by omega))
        (fun k hk => hstep k (by omega))
      have hbudget := hstep m hm
      have hpassing := hpass m hm
      have hden : 0 < c - 2 := by linarith
      have hcm : 0 < inflation c ^ m * a 0 :=
        mul_pos (pow_pos (inflation_pos hc) _) ha0
      have hdenBound : (c - 2) * a (m + 1) ≤ B m := by linarith
      have hlog : a (m + 1) < inflation c ^ (m + 1) * a 0 := by
        have hquot : a (m + 1) <
            (c * inflation c ^ m * a 0) / (c - 2) :=
          (lt_div_iff₀ hden).2 (by
            simpa [mul_comm] using hdenBound.trans_lt ih'.1)
        rw [pow_succ]
        have hid := inflation_mul_sub_two hc
        field_simp [ne_of_gt hden] at hquot ⊢
        nlinarith
      constructor
      · have htarget :
            c * inflation c ^ (m + 1) * a 0 =
              c * inflation c ^ m * a 0 +
                2 * (inflation c ^ (m + 1) * a 0) := by
          rw [pow_succ]
          have hid := c_mul_inflation hc
          nlinarith
        rw [htarget]
        linarith
      · exact hlog.le

noncomputable def functional (c : ℝ) (a : ℕ → ℝ) (j : ℕ) : ℝ :=
  (∑ i ∈ Finset.range j, a i) + c * a j

theorem even_terminal_ratio
    (c : ℝ) (a : ℕ → ℝ) (L S : ℝ) (m : ℕ)
    (hc : 2 < c) (hS : c ≤ S)
    (hpos : ∀ i ≤ 2 * m, 0 < a i)
    (hcap : ∀ i ≤ 2 * m, a i ≤ L)
    (hdesc : ∀ i < 2 * m, a (i + 1) ≤ a i)
    (hproper : ∀ j < 2 * m, j % 2 = 0 → functional c a j ≤ S * L)
    (hterminal : S * L < functional c a (2 * m)) :
    L / a (2 * m) < inflation c ^ m := by
  let ar : ℕ → ℝ := fun k => a (2 * (m - k))
  let B : ℕ → ℝ := fun k =>
    S * L - ∑ i ∈ Finset.range (2 * (m - k)), a i
  have har0 : ar 0 = a (2 * m) := by simp [ar]
  have hB0 : B 0 < c * ar 0 := by
    simp only [B, ar, Nat.sub_zero]
    unfold functional at hterminal
    linarith
  have hpass : ∀ k < m, c * ar (k + 1) ≤ B (k + 1) := by
    intro k hk
    have hjlt : 2 * (m - (k + 1)) < 2 * m := by omega
    have hp := hproper (2 * (m - (k + 1))) hjlt (by omega)
    simp only [functional, ar, B] at hp ⊢
    linarith
  have hstep : ∀ k < m, B (k + 1) ≤ B k + 2 * ar (k + 1) := by
    intro k hk
    have hidx : 2 * (m - k) = 2 * (m - (k + 1)) + 2 := by omega
    let j := 2 * (m - (k + 1))
    have hmono : a (j + 1) ≤ a j := hdesc j (by dsimp [j]; omega)
    have hsum :
        (∑ i ∈ Finset.range (j + 2), a i) =
          (∑ i ∈ Finset.range j, a i) + a j + a (j + 1) := by
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
    simp only [B, ar]
    rw [hidx, hsum]
    dsimp [j] at hmono ⊢
    linarith
  have hback := backward_budget_bound c ar B m hc
    (by simpa [har0] using hpos (2 * m) (by omega)) hB0 hpass hstep
  have hBm : B m = S * L := by simp [B]
  have hL0 : 0 < L := lt_of_lt_of_le (hpos (2 * m) (by omega))
    (hcap (2 * m) (by omega))
  have hcL : c * L ≤ S * L := mul_le_mul_of_nonneg_right hS hL0.le
  have hmain : L < inflation c ^ m * a (2 * m) := by
    rw [hBm, har0] at hback
    nlinarith
  exact (div_lt_iff₀ (hpos (2 * m) (by omega))).2 (by
    simpa [mul_comm] using hmain)

theorem odd_terminal_ratio
    (c : ℝ) (a : ℕ → ℝ) (L S : ℝ) (m : ℕ)
    (hc : 2 < c) (hS : c ≤ S)
    (hpos : ∀ i ≤ 2 * m + 1, 0 < a i)
    (hcap : ∀ i ≤ 2 * m + 1, a i ≤ L)
    (hdesc : ∀ i < 2 * m + 1, a (i + 1) ≤ a i)
    (hproper : ∀ j < 2 * m + 1, j % 2 = 1 → functional c a j ≤ S * L)
    (hterminal : S * L < functional c a (2 * m + 1)) :
    L / a (2 * m + 1) < inflation c ^ (m + 1) := by
  let ar : ℕ → ℝ := fun k => a (2 * (m - k) + 1)
  let B : ℕ → ℝ := fun k =>
    S * L - ∑ i ∈ Finset.range (2 * (m - k) + 1), a i
  have har0 : ar 0 = a (2 * m + 1) := by simp [ar]
  have hB0 : B 0 < c * ar 0 := by
    simp only [B, ar, Nat.sub_zero]
    unfold functional at hterminal
    linarith
  have hpass : ∀ k < m, c * ar (k + 1) ≤ B (k + 1) := by
    intro k hk
    have hjlt : 2 * (m - (k + 1)) + 1 < 2 * m + 1 := by omega
    have hp := hproper (2 * (m - (k + 1)) + 1) hjlt (by omega)
    simp only [functional, ar, B] at hp ⊢
    linarith
  have hstep : ∀ k < m, B (k + 1) ≤ B k + 2 * ar (k + 1) := by
    intro k hk
    have hidx :
        2 * (m - k) + 1 = 2 * (m - (k + 1)) + 1 + 2 := by omega
    let j := 2 * (m - (k + 1)) + 1
    have hmono : a (j + 1) ≤ a j := hdesc j (by dsimp [j]; omega)
    have hsum :
        (∑ i ∈ Finset.range (j + 2), a i) =
          (∑ i ∈ Finset.range j, a i) + a j + a (j + 1) := by
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
    simp only [B, ar]
    rw [hidx, hsum]
    dsimp [j] at hmono ⊢
    linarith
  have hback := backward_budget_bound c ar B m hc
    (by simpa [har0] using hpos (2 * m + 1) (by omega)) hB0 hpass hstep
  have hBm : B m = S * L - a 0 := by simp [B]
  have hL0 : 0 < L := lt_of_lt_of_le (hpos (2 * m + 1) (by omega))
    (hcap (2 * m + 1) (by omega))
  have ha0cap : a 0 ≤ L := hcap 0 (by omega)
  have hcL : c * L ≤ S * L := mul_le_mul_of_nonneg_right hS hL0.le
  have hcm1 : 0 < c - 1 := by linarith
  have hpre : (c - 1) * L < c * inflation c ^ m * a (2 * m + 1) := by
    rw [hBm, har0] at hback
    nlinarith
  have hZpos : 0 < inflation c ^ m * a (2 * m + 1) :=
    mul_pos (pow_pos (inflation_pos hc) _) (hpos (2 * m + 1) (by omega))
  have hratio : c / (c - 1) < inflation c := by
    rw [inflation]
    apply (div_lt_div_iff₀ hcm1 (by linarith)).2
    nlinarith
  have hL : L < (c / (c - 1)) *
      (inflation c ^ m * a (2 * m + 1)) := by
    rw [div_mul_eq_mul_div]
    exact (lt_div_iff₀ hcm1).2 (by nlinarith)
  have hmain : L < inflation c ^ (m + 1) * a (2 * m + 1) := by
    rw [pow_succ]
    calc
      L < (c / (c - 1)) *
          (inflation c ^ m * a (2 * m + 1)) := hL
      _ < inflation c *
          (inflation c ^ m * a (2 * m + 1)) :=
        mul_lt_mul_of_pos_right hratio hZpos
      _ = inflation c ^ m * inflation c * a (2 * m + 1) := by ring
  exact (div_lt_iff₀ (hpos (2 * m + 1) (by omega))).2 (by
    simpa [mul_comm] using hmain)

/-- Parity-unified variable-beta terminal ratio. -/
theorem terminal_ratio
    (c : ℝ) (a : ℕ → ℝ) (L S : ℝ) (r : ℕ)
    (hc : 2 < c) (hS : c ≤ S)
    (hpos : ∀ i ≤ r, 0 < a i)
    (hcap : ∀ i ≤ r, a i ≤ L)
    (hdesc : ∀ i < r, a (i + 1) ≤ a i)
    (hproper : ∀ j < r, j % 2 = r % 2 → functional c a j ≤ S * L)
    (hterminal : S * L < functional c a r) :
    L / a r < inflation c ^ r := by
  rcases r.even_or_odd' with ⟨m, hr | hr⟩
  · subst r
    have hstrong := even_terminal_ratio c a L S m hc hS hpos hcap hdesc
      (fun j hj hpar => hproper j hj (by omega)) hterminal
    exact hstrong.trans_le
      (pow_le_pow_right₀ (inflation_one_le hc) (by omega))
  · subst r
    have hstrong := odd_terminal_ratio c a L S m hc hS hpos hcap hdesc
      (fun j hj hpar => hproper j hj (by omega)) hterminal
    exact hstrong.trans_le
      (pow_le_pow_right₀ (inflation_one_le hc) (by omega))

end Erdos387.GeneralBetaChainRatio
