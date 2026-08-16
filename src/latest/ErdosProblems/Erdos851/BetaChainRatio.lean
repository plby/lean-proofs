/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

/-!
# The beta-100 ratio along a Rosser stopping chain

This file isolates the real-variable inequality behind the least-prime
estimate for a beta-100 boundary chain.  The proof is most transparent in
terms of the unused stopping ``budget``

`B j = S * L - ∑ i < j, a i`.

Moving backwards by two places adds at most twice the earlier logarithm to
the budget.  A passing prefix says that this new budget is at least `101`
times that logarithm.  Thus the factor lost at each backwards two-step is
exactly `101 / 99`.
-/

namespace Erdos851.BetaChainRatio

open scoped BigOperators

/-- The beta-100 inflation factor. -/
noncomputable def inflation : ℝ := 101 / 99

lemma inflation_pos : 0 < inflation := by
  norm_num [inflation]

lemma inflation_one_le : 1 ≤ inflation := by
  norm_num [inflation]

/-- Abstract backwards-budget induction.  Index `0` is the terminal failed
prefix, and increasing indices move backwards through the tested prefixes.
The two conclusions are proved simultaneously because the budget estimate
at the next step uses the logarithm estimate at that step. -/
theorem backward_budget_bound
    (a B : ℕ → ℝ) (m : ℕ)
    (ha0 : 0 < a 0)
    (hterminal : B 0 < 101 * a 0)
    (hpass : ∀ k < m, 101 * a (k + 1) ≤ B (k + 1))
    (hstep : ∀ k < m, B (k + 1) ≤ B k + 2 * a (k + 1)) :
    B m < 101 * inflation ^ m * a 0 ∧
      a m ≤ inflation ^ m * a 0 := by
  induction m with
  | zero =>
      simpa using And.intro hterminal (le_refl (a 0))
  | succ m ih =>
      have hm : m < m + 1 := by omega
      have ih' := ih (fun k hk => hpass k (by omega))
        (fun k hk => hstep k (by omega))
      have hbudget := hstep m hm
      have hpassing := hpass m hm
      have hlog : a (m + 1) < inflation ^ (m + 1) * a 0 := by
        have h99 : 99 * a (m + 1) ≤ B m := by linarith
        have hpow0 : 0 < inflation ^ m * a 0 :=
          mul_pos (pow_pos inflation_pos _) ha0
        rw [pow_succ]
        norm_num [inflation] at *
        nlinarith
      constructor
      · rw [pow_succ]
        norm_num [inflation] at *
        nlinarith
      · exact hlog.le

/-- The stopping functional at depth `j`. -/
noncomputable def functional (a : ℕ → ℝ) (j : ℕ) : ℝ :=
  (∑ i ∈ Finset.range j, a i) + 101 * a j

/-- The beta-100 chain inequality when the failed depth is even.  In fact the
proof gives the stronger exponent `m`, one inflation factor for each
two-position backwards move. -/
theorem even_terminal_ratio
    (a : ℕ → ℝ) (L S : ℝ) (m : ℕ)
    (hS : 101 ≤ S)
    (hpos : ∀ i ≤ 2 * m, 0 < a i)
    (hcap : ∀ i ≤ 2 * m, a i ≤ L)
    (hdesc : ∀ i < 2 * m, a (i + 1) ≤ a i)
    (hproper : ∀ j < 2 * m, j % 2 = 0 → functional a j ≤ S * L)
    (hterminal : S * L < functional a (2 * m)) :
    L / a (2 * m) < inflation ^ m := by
  let ar : ℕ → ℝ := fun k => a (2 * (m - k))
  let B : ℕ → ℝ := fun k =>
    S * L - ∑ i ∈ Finset.range (2 * (m - k)), a i
  have har0 : ar 0 = a (2 * m) := by simp [ar]
  have hB0 : B 0 < 101 * ar 0 := by
    simp only [B, ar, Nat.sub_zero]
    unfold functional at hterminal
    linarith
  have hpass : ∀ k < m, 101 * ar (k + 1) ≤ B (k + 1) := by
    intro k hk
    have hsub : m - (k + 1) < m := by omega
    have hjlt : 2 * (m - (k + 1)) < 2 * m := by omega
    have hp := hproper (2 * (m - (k + 1))) hjlt (by omega)
    simp only [functional, ar, B] at hp ⊢
    linarith
  have hstep : ∀ k < m, B (k + 1) ≤ B k + 2 * ar (k + 1) := by
    intro k hk
    have hidx : 2 * (m - k) = 2 * (m - (k + 1)) + 2 := by omega
    let j := 2 * (m - (k + 1))
    have hj : j + 1 < 2 * m := by
      dsimp [j]
      omega
    have hmono : a (j + 1) ≤ a j := hdesc j (by omega)
    have hsum :
        (∑ i ∈ Finset.range (j + 2), a i) =
          (∑ i ∈ Finset.range j, a i) + a j + a (j + 1) := by
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
    simp only [B, ar]
    rw [hidx, hsum]
    dsimp [j] at hmono ⊢
    linarith
  have hback := backward_budget_bound ar B m
    (by simpa [har0] using hpos (2 * m) (by omega)) hB0 hpass hstep
  have hBm : B m = S * L := by simp [B]
  have hL0 : 0 < L := lt_of_lt_of_le (hpos (2 * m) (by omega))
    (hcap (2 * m) (by omega))
  have hSL : 101 * L ≤ S * L :=
    mul_le_mul_of_nonneg_right hS hL0.le
  have hmain : L < inflation ^ m * a (2 * m) := by
    rw [hBm, har0] at hback
    nlinarith
  exact (div_lt_iff₀ (hpos (2 * m) (by omega))).2 (by
    simpa [mul_comm] using hmain)

/-- The beta-100 chain inequality when the failed depth is odd.  The untested
index-zero logarithm costs a factor `101 / 100`, which is smaller than
`inflation`; hence the displayed exponent is `m + 1`. -/
theorem odd_terminal_ratio
    (a : ℕ → ℝ) (L S : ℝ) (m : ℕ)
    (hS : 101 ≤ S)
    (hpos : ∀ i ≤ 2 * m + 1, 0 < a i)
    (hcap : ∀ i ≤ 2 * m + 1, a i ≤ L)
    (hdesc : ∀ i < 2 * m + 1, a (i + 1) ≤ a i)
    (hproper : ∀ j < 2 * m + 1, j % 2 = 1 → functional a j ≤ S * L)
    (hterminal : S * L < functional a (2 * m + 1)) :
    L / a (2 * m + 1) < inflation ^ (m + 1) := by
  let ar : ℕ → ℝ := fun k => a (2 * (m - k) + 1)
  let B : ℕ → ℝ := fun k =>
    S * L - ∑ i ∈ Finset.range (2 * (m - k) + 1), a i
  have har0 : ar 0 = a (2 * m + 1) := by simp [ar]
  have hB0 : B 0 < 101 * ar 0 := by
    simp only [B, ar, Nat.sub_zero]
    unfold functional at hterminal
    linarith
  have hpass : ∀ k < m, 101 * ar (k + 1) ≤ B (k + 1) := by
    intro k hk
    have hjlt : 2 * (m - (k + 1)) + 1 < 2 * m + 1 := by omega
    have hp := hproper (2 * (m - (k + 1)) + 1) hjlt (by omega)
    simp only [functional, ar, B] at hp ⊢
    linarith
  have hstep : ∀ k < m, B (k + 1) ≤ B k + 2 * ar (k + 1) := by
    intro k hk
    have hidx :
        2 * (m - k) + 1 = 2 * (m - (k + 1)) + 1 + 2 := by
      omega
    let j := 2 * (m - (k + 1)) + 1
    have hj : j + 1 < 2 * m + 1 := by
      dsimp [j]
      omega
    have hmono : a (j + 1) ≤ a j := hdesc j (by omega)
    have hsum :
        (∑ i ∈ Finset.range (j + 2), a i) =
          (∑ i ∈ Finset.range j, a i) + a j + a (j + 1) := by
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
    simp only [B, ar]
    rw [hidx, hsum]
    dsimp [j] at hmono ⊢
    linarith
  have hback := backward_budget_bound ar B m
    (by simpa [har0] using hpos (2 * m + 1) (by omega)) hB0 hpass hstep
  have hBm : B m = S * L - a 0 := by simp [B]
  have hL0 : 0 < L := lt_of_lt_of_le (hpos (2 * m + 1) (by omega))
    (hcap (2 * m + 1) (by omega))
  have ha0cap : a 0 ≤ L := hcap 0 (by omega)
  have h100 : 100 * L < 101 * inflation ^ m * a (2 * m + 1) := by
    rw [hBm, har0] at hback
    have hSL : 101 * L ≤ S * L :=
      mul_le_mul_of_nonneg_right hS hL0.le
    nlinarith
  have hpow0 : 0 < inflation ^ m * a (2 * m + 1) :=
    mul_pos (pow_pos inflation_pos _) (hpos (2 * m + 1) (by omega))
  have hmain : L < inflation ^ (m + 1) * a (2 * m + 1) := by
    rw [pow_succ]
    norm_num [inflation] at *
    nlinarith
  exact (div_lt_iff₀ (hpos (2 * m + 1) (by omega))).2 (by
    simpa [mul_comm] using hmain)

/-- Parity-unified form of the beta-100 least-logarithm bound.  The assumptions
say precisely that every proper prefix tested at the same parity as the
terminal prefix passes, while the terminal prefix fails. -/
theorem terminal_ratio
    (a : ℕ → ℝ) (L S : ℝ) (r : ℕ)
    (hS : 101 ≤ S)
    (hpos : ∀ i ≤ r, 0 < a i)
    (hcap : ∀ i ≤ r, a i ≤ L)
    (hdesc : ∀ i < r, a (i + 1) ≤ a i)
    (hproper : ∀ j < r, j % 2 = r % 2 → functional a j ≤ S * L)
    (hterminal : S * L < functional a r) :
    L / a r < inflation ^ r := by
  rcases r.even_or_odd' with ⟨m, hr | hr⟩
  · subst r
    have hstrong := even_terminal_ratio a L S m hS hpos hcap hdesc
      (fun j hj hpar => hproper j hj (by omega)) hterminal
    exact hstrong.trans_le
      (pow_le_pow_right₀ inflation_one_le (by omega))
  · subst r
    have hstrong := odd_terminal_ratio a L S m hS hpos hcap hdesc
      (fun j hj hpar => hproper j hj (by omega)) hterminal
    exact hstrong.trans_le
      (pow_le_pow_right₀ inflation_one_le (by omega))

end Erdos851.BetaChainRatio
