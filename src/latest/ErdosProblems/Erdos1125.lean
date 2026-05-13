/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
/- Original license: Apache 2.0. Note: This file has been modified. -/
/-
This is a Lean formalization of a solution to Erdős Problem 1125.
https://www.erdosproblems.com/forum/thread/1125

Informal authors:
- Miklós Laczkovich

Formal authors:
- Aristotle
- Stefano Rocca

URLs:
- https://www.erdosproblems.com/forum/thread/1125#post-5332
- https://gist.githubusercontent.com/ster-oc/18384e6202ffe054cbc76ff2d0b1afde/raw/4d89f4dce1b6ae4aedde501bfbcbc4f9f81a8549/Erdos1125.lean
-/
/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefano Rocca, Aristotle (Harmonic)
-/
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Tactic.Cases
import Mathlib.Tactic.LinearCombination'

set_option linter.style.longLine false
set_option linter.style.induction false
set_option linter.style.multiGoal false
set_option linter.style.setOption false
set_option linter.flexible false
set_option linter.style.cases false

namespace Erdos1125

/-!
# Erdős Problem 1125

We prove that any function `f : ℝ → ℝ` satisfying the midpoint-convexity inequality
`2 f(x) ≤ f(x+h) + f(x+2h)` for all `x` and all `h > 0` is monotone non-decreasing.
The proof uses dyadic induction, a covering lemma on `I(α)`, interpolation estimates,
and Pell sequence approximants for `√2`.
-/

noncomputable section
open Filter Topology Set Real

/-! ## Definitions -/

/-- The set `I(α) = {nα + k : n, k ∈ ℤ}`. -/
def I (α : ℝ) : Set ℝ := {x : ℝ | ∃ n : ℤ, ∃ k : ℤ, x = ↑n * α + ↑k}

/-- `α` has controlled integer approximants with appropriate constants and sequences. -/
def HasControlledIntegerApproximants (α : ℝ) : Prop :=
  ∃ (A C : ℝ) (p : ℕ → ℤ) (q : ℕ → ℕ),
    A > 0 ∧ C > 1 ∧
    (∀ j, 0 < q j) ∧
    Tendsto (fun j ↦ (q j : ℝ)) atTop atTop ∧
    (∀ j, (q (j + 1) : ℝ) ≤ C * ↑(q j)) ∧
    (∀ j, 0 < |↑(q j) * α - ↑(p j)| ∧ |↑(q j) * α - ↑(p j)| ≤ A / ↑(q j)) ∧
    (∀ j, (↑(q j) * α - ↑(p j)) * (↑(q (j + 1)) * α - ↑(p (j + 1))) < 0)

/-- `IsF`: the class of functions on `{0,...,n}` satisfying `2f(i) ≤ f(i+h) + f(i+2h)`. -/
def IsF (n : ℕ) (f : ℕ → ℝ) : Prop :=
  ∀ i h : ℕ, 0 < h → i + 2 * h ≤ n → 2 * f i ≤ f (i + h) + f (i + 2 * h)

/-- `H^(N)`: smallest set containing `H` and closed under `N`-step backward extension. -/
inductive HSetPow (N : ℕ) (H : Set ℝ) : Set ℝ where
  | base {x : ℝ} (hx : x ∈ H) : HSetPow N H x
  | step {x : ℝ} (h : ℝ) (hh : h > 0)
      (hmem : ∀ i : ℕ, 1 ≤ i → i ≤ N → HSetPow N H (x + ↑i * h)) : HSetPow N H x

/-! ## Section 1: Auxiliary facts for Lemma 1 -/

/-- Translating a function in `IsF` gives a function in `F_{b-a}`. -/
private lemma isF_translate {n : ℕ} {f : ℕ → ℝ} (hf : IsF n f)
    {a b : ℕ} (hab : a ≤ b) (hbn : b ≤ n) :
    IsF (b - a) (fun i ↦ f (i + a)) := by
  intro i h h_pos h_le; convert hf (i + a) h h_pos (by omega) using 1; ring_nf

/-- One-step average bound for `IsF` functions. -/
private lemma one_step_average {n : ℕ} {f : ℕ → ℝ} (hf : IsF n f)
    {i : ℕ} (hi : i + 2 ≤ n) :
    f i ≤ (f (i + 1) + f (i + 2)) / 2 := by
  linarith [hf i 1 (by norm_num) hi]

/-- Dyadic endpoint step for the power-of-two bound. -/
private lemma dyadic_endpoint_step {k : ℕ} (hk : 2 ≤ k) {f : ℕ → ℝ} {K : ℝ}
    (hf : IsF (2 ^ k) f)
    (hbound : ∀ i, i ≤ 2 ^ k → |f i| ≤ K)
    (ih : ∀ g : ℕ → ℝ, IsF (2 ^ (k - 1)) g →
      (∀ i, i ≤ 2 ^ (k - 1) → |g i| ≤ K) →
      g 0 ≤ g (2 ^ (k - 1)) + 2 * K / (2 : ℝ) ^ (k - 1)) :
    f 0 ≤ f (2 ^ k) + 2 * K / (2 : ℝ) ^ k := by
  contrapose! ih with ih
  refine ⟨fun i ↦ f (i + 2 ^ (k - 1)), ?_, ?_, ?_⟩
  · convert isF_translate hf (show 2 ^ (k - 1) ≤ 2 ^ k from pow_le_pow_right₀ (by norm_num) (Nat.pred_le _)) (show 2 ^ k ≤ 2 ^ k from le_rfl) using 1
    exact eq_tsub_of_add_eq (by cases k <;> norm_num [pow_succ'] at *; linarith)
  · exact fun i hi ↦ hbound _ (by cases k <;> norm_num [pow_succ'] at *; linarith)
  · rcases k with (_ | _ | k) <;> norm_num [pow_succ'] at *
    have := hf 0 (2 * 2 ^ k) (by positivity) (by linarith [pow_pos (zero_lt_two' ℕ) k])
    ring_nf at *; linarith

/-- Power-of-two bound: `f(0) ≤ f(2^k) + 2K/2^k` for `F_{2^k}` functions bounded by `K`. -/
private lemma lemma1_power_of_two {k : ℕ} (hk : 1 ≤ k) {f : ℕ → ℝ} {K : ℝ}
    (hf : IsF (2 ^ k) f) (hbound : ∀ i, i ≤ 2 ^ k → |f i| ≤ K) :
    f 0 ≤ f (2 ^ k) + 2 * K / (2 : ℝ) ^ k := by
  induction' hk with k ih generalizing f K
  · linarith [abs_le.mp (hbound 0 (by norm_num)), abs_le.mp (hbound 1 (by norm_num)), abs_le.mp (hbound 2 (by norm_num)), one_step_average hf (by norm_num : 0 + 2 ≤ 2)]
  · have := dyadic_endpoint_step (show 2 ≤ k.succ from Nat.succ_le_succ ih) hf hbound
    grind +qlia

/-- Shifted dyadic estimate: `f(a) ≤ f(a + 2^k) + 2K/2^k`. -/
private lemma shifted_dyadic_estimate {k : ℕ} (hk : 1 ≤ k) {n : ℕ} {f : ℕ → ℝ} {K : ℝ}
    (hf : IsF n f) (hbound : ∀ i, i ≤ n → |f i| ≤ K) {a : ℕ} (ha : a + 2 ^ k ≤ n) :
    f a ≤ f (a + 2 ^ k) + 2 * K / (2 : ℝ) ^ k := by
  convert lemma1_power_of_two hk (hf := ?_) (hbound := ?_) using 1
  rotate_left; rotate_left
  exact fun i ↦ f (a + i); exact K
  · grind +locals
  · exact fun i hi ↦ hbound _ (by linarith)
  · norm_num
  · rfl

/-- Estimate at position 1 for power-of-two-plus-one. -/
private lemma estimate_at_one_for_power_of_two_plus_one {k : ℕ} (hk : 1 ≤ k) {f : ℕ → ℝ} {K : ℝ}
    (hf : IsF (2 ^ k + 1) f) (hbound : ∀ i, i ≤ 2 ^ k + 1 → |f i| ≤ K) :
    f 1 ≤ f (2 ^ k + 1) + 2 * K / (2 : ℝ) ^ k := by
  have h_shifted : f 1 ≤ f (1 + 2^k) + 2 * K / 2^k := by
    convert shifted_dyadic_estimate hk hf hbound _ using 1; ring_nf; aesop
  grobner

/-- Backward propagation from two consecutive bounds. -/
private lemma backward_propagation_from_two_consecutive_bounds {n : ℕ} {f : ℕ → ℝ} (hf : IsF n f)
    {r : ℕ} {M : ℝ} (hr : r + 2 ≤ n) (hfr : f r ≤ M) (hfr1 : f (r + 1) ≤ M) :
    ∀ i, i ≤ r → f i ≤ M := by
  intro i hi; induction' hi with i hi ih <;> cases lt_trichotomy i r <;> norm_num at *; linarith
  · linarith
  · contrapose! ih
    exact ⟨ by linarith, by have := hf i 1 zero_lt_one (by linarith); norm_num at this; linarith, hfr, ih ⟩
  · exact ih (by linarith) (by linarith [one_step_average hf (by linarith : i + 2 ≤ n)]) hfr |> fun x ↦ x.trans (by linarith)

/-- Part B of the combined bound: given Part A at `k`, derive Part B at `k`. -/
private lemma combined_partb_from_parta (k : ℕ) (hk : 1 ≤ k)
    (hA : ∀ (f : ℕ → ℝ) (K : ℝ), IsF (2 ^ k + 1) f → 0 < K →
      (∀ i, i ≤ 2 ^ k + 1 → |f i| ≤ K) → f 0 ≤ f (2 ^ k + 1) + 6 * K / (2 : ℝ) ^ k) :
    ∀ (nn : ℕ), 2 ^ k + 2 ≤ nn → nn < 2 ^ (k + 1) → ∀ (f : ℕ → ℝ) (K : ℝ),
      IsF nn f → 0 < K → (∀ i, i ≤ nn → |f i| ≤ K) →
      f 0 ≤ f nn + 5 * K / (2 : ℝ) ^ k := by
  intro nn hnk hn2k f K hf hK hbound
  have h1 : f ((nn : ℕ) - 2^k - 1) ≤ f nn + 6 * K / (2 : ℝ) ^ k := by
    convert hA (fun i ↦ f (i + (nn - 2 ^ k - 1))) K ?_ hK ?_ using 1 <;> norm_num [pow_succ'] at *
    · exact congr_arg f (by omega)
    · intro i h hi hi2; convert hf (i + (nn - 2 ^ k - 1)) h (by omega) (by omega) using 1; ring_nf
    · exact fun i hi ↦ hbound _ (by omega)
  have h2 : f ((nn : ℕ) - 2^k) ≤ f nn + 2 * K / (2 : ℝ) ^ k := by
    convert shifted_dyadic_estimate hk hf hbound _ using 1
    · rw [Nat.sub_add_cancel (by linarith)]
    · rw [Nat.sub_add_cancel (by linarith)]
  have h3 : f ((nn : ℕ) - 2^k - 2) ≤ f nn + 4 * K / (2 : ℝ) ^ k := by
    have h3 : 2 * f (nn - 2^k - 2) ≤ f (nn - 2^k - 1) + f (nn - 2^k) := by
      convert hf (nn - 2 ^ k - 2) 1 (by norm_num) _ using 1; norm_num [Nat.sub_sub]
      · rw [show nn - (2 ^ k + 2) + 1 = nn - (2 ^ k + 1) by omega, show nn - (2 ^ k + 2) + 2 = nn - 2 ^ k by omega]
      · omega
    ring_nf at *; linarith
  have h4 : f 0 ≤ f nn + 5 * K / (2 : ℝ) ^ k := by
    by_cases hnn : nn = 2^k + 2
    · simp_all
      exact h3.trans (by gcongr; norm_num)
    · have h4 : f ((nn : ℕ) - 2^k - 3) ≤ f nn + 5 * K / (2 : ℝ) ^ k := by
        have := hf (nn - 2 ^ k - 3) 1; simp_all +decide [Nat.sub_sub]
        rw [show nn - (2 ^ k + 3) + 1 = nn - (2 ^ k + 2) by omega, show nn - (2 ^ k + 3) + 2 = nn - (2 ^ k + 1) by omega] at this; ring_nf at *; linarith [this (by omega)]
      have h5 : ∀ i, i ≤ (nn : ℕ) - 2^k - 3 → f i ≤ f nn + 5 * K / (2 : ℝ) ^ k := by
        apply backward_propagation_from_two_consecutive_bounds hf
        · omega
        · exact h4
        · convert h3.trans _ using 1
          · exact congr_arg f (by omega)
          · gcongr; norm_num
      exact h5 0 bot_le
  exact h4

/-- Combined bound for `2^k+1` and intermediate `n` by induction on `k` (auxiliary). -/
private lemma combined_isF_bound (k : ℕ) (hk : 1 ≤ k) :
    (∀ (f : ℕ → ℝ) (K : ℝ), IsF (2 ^ k + 1) f → 0 < K →
      (∀ i, i ≤ 2 ^ k + 1 → |f i| ≤ K) → f 0 ≤ f (2 ^ k + 1) + 6 * K / (2 : ℝ) ^ k) ∧
    (∀ (nn : ℕ), 2 ^ k + 2 ≤ nn → nn < 2 ^ (k + 1) → ∀ (f : ℕ → ℝ) (K : ℝ),
      IsF nn f → 0 < K → (∀ i, i ≤ nn → |f i| ≤ K) →
      f 0 ≤ f nn + 5 * K / (2 : ℝ) ^ k) := by
  refine ⟨?_, fun nn hnn₁ hnn₂ f K hf hK hK' ↦ ?_⟩
  · induction' k using Nat.strong_induction_on with k ih
    intro f K hf hK hbound
    by_cases hk2 : k = 1 ∨ k = 2
    · rcases hk2 with (rfl | rfl) <;> norm_num at *
      · linarith [abs_le.mp (hbound 0 (by norm_num)), abs_le.mp (hbound 3 (by norm_num))]
      · linarith [abs_le.mp (hbound 0 (by norm_num)), abs_le.mp (hbound 1 (by norm_num)), abs_le.mp (hbound 2 (by norm_num)), abs_le.mp (hbound 3 (by norm_num)), abs_le.mp (hbound 4 (by norm_num)), abs_le.mp (hbound 5 (by norm_num)), hf 0 1 (by norm_num) (by norm_num), hf 1 1 (by norm_num) (by norm_num), hf 2 1 (by norm_num) (by norm_num), hf 3 1 (by norm_num) (by norm_num)]
    · have ih_step : f 1 ≤ f (2 ^ k + 1) + 2 * K / 2 ^ k ∧ f 2 ≤ f (2 ^ k + 1) + 10 * K / 2 ^ k := by
        constructor
        · apply estimate_at_one_for_power_of_two_plus_one hk hf hbound
        · have ih_step : f 2 ≤ f (2 ^ k + 1) + 5 * K / 2 ^ (k - 1) := by
            have ih_step : ∀ (nn : ℕ), 2 ^ (k - 1) + 2 ≤ nn → nn < 2 ^ k → ∀ (f : ℕ → ℝ) (K : ℝ), IsF nn f → 0 < K → (∀ i, i ≤ nn → |f i| ≤ K) → f 0 ≤ f nn + 5 * K / 2 ^ (k - 1) := by
              intros nn hnn1 hnn2 f K hf hK hbound
              have := combined_partb_from_parta (k - 1) (Nat.le_sub_one_of_lt (lt_of_le_of_ne hk (Ne.symm (by tauto)))) (ih (k - 1) (Nat.sub_lt hk zero_lt_one) (Nat.le_sub_one_of_lt (lt_of_le_of_ne hk (Ne.symm (by tauto)))))
              exact this nn hnn1 (by cases k <;> trivial) f K hf hK hbound
            specialize ih_step (2 ^ k - 1) (by
            rcases k with (_ | _ | _ | k) <;> norm_num [pow_succ'] at *
            exact le_tsub_of_add_le_left (by linarith [Nat.one_le_pow k 2 zero_lt_two])) (by
            exact Nat.sub_lt (by positivity) (by positivity)) (fun i ↦ f (i + 2)) K (by
            convert isF_translate hf (show 2 ≤ 2 ^ k + 1 from by linarith [Nat.pow_le_pow_right two_pos hk]) (show 2 ^ k + 1 ≤ 2 ^ k + 1 from by linarith) using 1) hK (by
            exact fun i hi ↦ hbound _ (by linarith [Nat.sub_add_cancel (Nat.one_le_pow k 2 zero_lt_two)]))
            convert ih_step using 2; rw [show 2 ^ k - 1 + 2 = 2 ^ k + 1 by linarith [Nat.sub_add_cancel (Nat.one_le_pow k 2 zero_lt_two)]]
          rcases k with (_ | _ | k) <;> simp_all +decide [pow_succ']; ring_nf at *; linarith
      have := hf 0 1; norm_num at *
      ring_nf at *; linarith [this (by linarith [Nat.pow_le_pow_right two_pos hk])]
  · induction' k with k ih generalizing nn f K
    · contradiction
    · convert combined_partb_from_parta (k + 1) (by linarith) _ nn hnn₁ hnn₂ f K hf hK hK' using 1
      intro f K hf hK hK'; rcases k with (_ | k) <;> simp_all +decide [pow_succ']
      · interval_cases nn
      · have h_ind : f 2 ≤ f (2 * (2 * 2 ^ k) + 1) + 5 * K / (2 * 2 ^ k) := by
          have h_ind : IsF (2 * (2 * 2 ^ k) + 1 - 2) (fun i ↦ f (i + 2)) := by
            convert isF_translate hf (show 2 ≤ 2 * (2 * 2 ^ k) + 1 from by linarith [Nat.one_le_pow k 2 zero_lt_two]) (show 2 * (2 * 2 ^ k) + 1 ≤ 2 * (2 * 2 ^ k) + 1 from by linarith) using 1
          rcases k with (_ | k) <;> simp_all +decide [Nat.pow_succ']
          · linarith [abs_le.mp (hK' 2 (by norm_num)), abs_le.mp (hK' 5 (by norm_num))]
          · grind
        have h_ind : f 1 ≤ f (2 * (2 * 2 ^ k) + 1) + 2 * K / (2 * (2 * 2 ^ k)) := by
          convert estimate_at_one_for_power_of_two_plus_one (show 1 ≤ k + 2 by linarith) (show IsF (2 ^ (k + 2) + 1) f from ?_) (show ∀ i ≤ 2 ^ (k + 2) + 1, |f i| ≤ K from ?_) using 1 <;> ring_nf
          · convert hf using 1; ring
          · exact fun i hi ↦ hK' i <| by linarith
        have := hf 0 1; norm_num at *
        ring_nf at *
        linarith [this (by linarith [pow_pos (zero_lt_two' ℕ) k])]

/-- `f(0) ≤ f(2^k+1) + 6K/2^k` for `F_{2^k+1}` functions bounded by `K > 0`. -/
private lemma lemma1_power_of_two_plus_one {k : ℕ} (hk : 1 ≤ k) {f : ℕ → ℝ} {K : ℝ}
    (hf : IsF (2 ^ k + 1) f) (hK : 0 < K) (hbound : ∀ i, i ≤ 2 ^ k + 1 → |f i| ≤ K) :
    f 0 ≤ f (2 ^ k + 1) + 6 * K / (2 : ℝ) ^ k :=
  (combined_isF_bound k hk).1 f K hf hK hbound

/-- Intermediate range bound for `IsF` functions. -/
private lemma lemma1_intermediate_range {k : ℕ} (hk : 1 ≤ k) {n : ℕ}
    (hn1 : 2 ^ k + 2 ≤ n) (hn2 : n < 2 ^ (k + 1))
    {f : ℕ → ℝ} {K : ℝ} (hf : IsF n f) (hK : 0 < K)
    (hbound : ∀ i, i ≤ n → |f i| ≤ K) :
    f 0 ≤ f n + 5 * K / (2 : ℝ) ^ k :=
  (combined_isF_bound k hk).2 n hn1 hn2 f K hf hK hbound

/-- Lemma 1: `f(0) ≤ f(n) + 10K/n` for `IsF` functions bounded by `K > 0`. -/
lemma lemma1 {n : ℕ} (hn : 0 < n) {f : ℕ → ℝ} {K : ℝ} (hf : IsF n f) (hK : 0 < K)
    (hbound : ∀ i, i ≤ n → |f i| ≤ K) :
    f 0 ≤ f n + 10 * K / ↑n := by
  by_cases hn2 : n = 1
  · subst hn2; have := hbound 0; have := hbound 1; norm_num at *; linarith [abs_le.mp this, abs_le.mp (hbound 0 (by norm_num))]
  · obtain ⟨k, hk⟩ : ∃ k : ℕ, 2^k ≤ n ∧ n < 2^(k+1) := by
      exact ⟨ Nat.log 2 n, Nat.pow_le_of_le_log (by linarith) (by linarith), Nat.lt_pow_of_log_lt (by linarith) (by linarith) ⟩
    by_cases hn3 : n = 2^k + 1
    · have := lemma1_power_of_two_plus_one (show 1 ≤ k from Nat.pos_of_ne_zero (by aesop)) (show IsF (2 ^ k + 1) f from by simpa only [hn3] using hf) hK (by simpa only [hn3] using hbound)
      simp_all +decide [pow_succ']
      rw [add_div', le_div_iff₀] at * <;> nlinarith [pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (show k ≥ 1 by contrapose! hk; interval_cases k; norm_num at *)]
    · by_cases hn4 : 2^k + 2 ≤ n ∧ n < 2^(k+1)
      · have := lemma1_intermediate_range (show 1 ≤ k from Nat.pos_of_ne_zero fun h ↦ by subst h; norm_num at *; omega) hn4.1 hn4.2 hf hK hbound
        refine le_trans this ?_
        norm_num [pow_succ'] at *
        rw [div_le_div_iff₀] <;> nlinarith [show (n : ℝ) ≥ 2 ^ k + 2 by exact_mod_cast hn4.1, show (n : ℝ) < 2 * 2 ^ k by exact_mod_cast hn4.2]
      · have hn5 : n = 2^k := by omega
        have h_lemma1 : f 0 ≤ f n + 2 * K / n := by
          have := lemma1_power_of_two (show 1 ≤ k from Nat.pos_of_ne_zero (by aesop)) (show IsF (2 ^ k) f from by aesop) (show ∀ i ≤ 2 ^ k, |f i| ≤ K from by aesop); aesop
        exact h_lemma1.trans (by gcongr; linarith)

/-! ## Section 2: Covering lemma on `I(α)` -/

/-- `q_{j+2} ≤ C²q_j` for controlled approximants. -/
private lemma controlled_growth_two_steps {C : ℝ} {q : ℕ → ℕ}
    (hq_growth : ∀ j, (q (j + 1) : ℝ) ≤ C * ↑(q j)) (j : ℕ) :
    (q (j + 2) : ℝ) ≤ C ^ 2 * ↑(q j) := by
  by_cases hC : 0 ≤ C
  · nlinarith [hq_growth j, hq_growth (j + 1)]
  · nlinarith [hq_growth j, hq_growth (j + 1), show (q (j + 1) : ℝ) ≥ 0 by positivity, show (q (j + 2) : ℝ) ≥ 0 by positivity]

/-- The seed set with bounded `α`-coefficients in a bounded real interval is finite. -/
private lemma seed_set_finite (α : ℝ) (D : ℝ) (N : ℕ) (b : ℝ) :
    Set.Finite {x : ℝ | ∃ n : ℤ, ∃ k : ℤ,
      x = ↑n * α + ↑k ∧ (↑(Int.natAbs n) : ℝ) ≤ D * ↑N ∧
      b - ↑N ≤ x ∧ x ≤ b + D * (↑N) ^ 2} := by
  by_contra h_inf
  have h_pairs_finite : Set.Finite {p : ℤ × ℤ | abs p.1 ≤ D * N ∧ b - N ≤ p.1 * α + p.2 ∧ p.1 * α + p.2 ≤ b + D * N ^ 2} := by
    have h_pairs_finite : Set.Finite {n : ℤ | abs n ≤ D * N} := by
      exact Set.Finite.subset (Set.finite_Icc (-⌈D * N⌉₊ : ℤ) ⌈D * N⌉₊) fun x hx ↦ ⟨ neg_le_of_abs_le <| by exact_mod_cast hx.out.trans <| Nat.le_ceil _, le_of_abs_le <| by exact_mod_cast hx.out.trans <| Nat.le_ceil _ ⟩
    exact Set.Finite.subset (h_pairs_finite.prod (Set.Finite.biUnion h_pairs_finite fun n hn ↦ Set.finite_Icc (⌈b - ↑N - ↑n * α⌉) (⌊b + D * ↑N ^ 2 - ↑n * α⌋))) fun p hp ↦ by obtain ⟨ hp₁, hp₂, hp₃ ⟩ := hp; exact ⟨ hp₁, Set.mem_biUnion hp₁ ⟨ Int.ceil_le.mpr <| by linarith, Int.le_floor.mpr <| by linarith ⟩ ⟩
  exact h_inf <| Set.Finite.subset (h_pairs_finite.image fun p : ℤ × ℤ ↦ (p.1 : ℝ) * α + p.2) fun x hx ↦ by aesop

/-- Existence and bounds for the largest opposite-sign approximation index. -/
private lemma largest_opposite_sign_index_exists_and_is_bounded
    {α : ℝ} {C : ℝ} {p : ℕ → ℤ} {q : ℕ → ℕ} {N : ℕ}
    (hC : C > 1)
    (hq_pos : ∀ j, 0 < q j)
    (hq_tendsto : Tendsto (fun j ↦ (q j : ℝ)) atTop atTop)
    (hq_growth : ∀ j, (q (j + 1) : ℝ) ≤ C * ↑(q j))
    (h_alt_sign : ∀ j, (↑(q j) * α - ↑(p j)) * (↑(q (j + 1)) * α - ↑(p (j + 1))) < 0)
    (hN : 2 ≤ N) (n : ℤ) (hn : n ≠ 0)
    (hn_large : C * (q 0 : ℝ) * ↑N < (↑(Int.natAbs n) : ℝ)) :
    ∃ j, (↑(q j) : ℝ) < (↑(Int.natAbs n) : ℝ) / ↑N ∧
         (↑(q j) * α - ↑(p j)) * ↑n < 0 ∧
         (↑(Int.natAbs n) : ℝ) / (C ^ 2 * ↑N) ≤ ↑(q j) ∧
         ∀ j', j < j' → ¬((↑(q j') : ℝ) < (↑(Int.natAbs n) : ℝ) / ↑N ∧
           (↑(q j') * α - ↑(p j')) * ↑n < 0) := by
  obtain ⟨j_star, hj_star⟩ : ∃ j_star : ℕ, (q j_star : ℝ) < |n| / N ∧ (q j_star * α - p j_star) * n < 0 ∧ ∀ j : ℕ, (q j : ℝ) < |n| / N ∧ (q j * α - p j) * n < 0 → j ≤ j_star := by
    have h_unbounded : ∃ j_star : ℕ, (q j_star : ℝ) < |n| / N ∧ (q j_star * α - p j_star) * n < 0 := by
      by_cases h0 : (q 0 * α - p 0) * n < 0
      · refine ⟨0, ?_, ?_⟩ <;> simp_all +decide [mul_assoc]
        rw [lt_div_iff₀] <;> nlinarith [show (N : ℝ) ≥ 2 by norm_cast, show (q 0 : ℝ) ≥ 1 by exact_mod_cast hq_pos 0, mul_le_mul_of_nonneg_left (show (N : ℝ) ≥ 2 by norm_cast) (show (0 : ℝ) ≤ q 0 by exact_mod_cast Nat.zero_le _)]
      · refine ⟨1, ?_, ?_⟩ <;> norm_num at *
        · rw [lt_div_iff₀ (by positivity)]
          nlinarith [hq_growth 0, show (N : ℝ) ≥ 2 by norm_cast]
        · cases lt_or_gt_of_ne (show (n : ℝ) ≠ 0 from mod_cast hn) <;> cases lt_or_gt_of_ne (show (q 0 * α - p 0 : ℝ) ≠ 0 from fun h ↦ by simpa [*] using h_alt_sign 0) <;> nlinarith [h_alt_sign 0]
    have h_finite : Set.Finite {j : ℕ | (q j : ℝ) < |n| / N ∧ (q j * α - p j) * n < 0} := by
      exact Set.finite_iff_bddAbove.mpr <| Filter.eventually_atTop.mp (hq_tendsto.eventually_gt_atTop <| |n| / N) |> fun ⟨ j, hj ⟩ ↦ ⟨ j, fun k hk ↦ not_lt.1 fun hk' ↦ not_lt_of_ge (le_of_lt <| hj k hk'.le) hk.1 ⟩
    exact ⟨ Finset.max' (h_finite.toFinset) ⟨ h_unbounded.choose, h_finite.mem_toFinset.mpr h_unbounded.choose_spec ⟩, h_finite.mem_toFinset.mp (Finset.max'_mem _ _) |>.1, h_finite.mem_toFinset.mp (Finset.max'_mem _ _) |>.2, fun j hj ↦ Finset.le_max' _ _ (h_finite.mem_toFinset.mpr hj) ⟩
  refine ⟨j_star, ?_, ?_, ?_, ?_⟩ <;> simp_all +decide [div_eq_mul_inv]
  · contrapose! hj_star
    refine fun h₁ h₂ ↦ ⟨j_star + 2, ?_, ?_, ?_⟩ <;> norm_num at *
    · refine lt_of_le_of_lt (controlled_growth_two_steps hq_growth j_star) ?_
      nlinarith [show (0 : ℝ) < C ^ 2 by positivity, mul_inv_cancel_left₀ (show (C ^ 2 : ℝ) ≠ 0 by positivity) (|↑n| * (N : ℝ) ⁻¹)]
    · have := h_alt_sign j_star; have := h_alt_sign (j_star + 1); norm_num at *; cases abs_cases (n : ℝ) <;> cases lt_or_ge 0 ((q j_star : ℝ) * α - p j_star) <;> cases lt_or_ge 0 ((q (j_star + 1) : ℝ) * α - p (j_star + 1)) <;> nlinarith
  · grind

/-- `natAbs` decreases when subtracting from a positive integer. -/
private lemma int_natAbs_sub_pos_lt (n : ℤ) (k : ℕ) (hn : 0 < n) (hk : 0 < k)
    (hkn : (k : ℤ) < n) :
    Int.natAbs (n - k) < Int.natAbs n := by
  have h1 : (n - (k : ℤ)).natAbs = n.toNat - k := by omega
  have h2 : n.natAbs = n.toNat := by omega
  omega

/-- `natAbs` decreases when adding to a negative integer. -/
private lemma int_natAbs_add_neg_lt (n : ℤ) (k : ℕ) (hn : n < 0) (hk : 0 < k)
    (hkn : (k : ℤ) < Int.natAbs n) :
    Int.natAbs (n + k) < Int.natAbs n := by
  have h1 : (n + (k : ℤ)).natAbs = n.natAbs - k := by omega
  omega

/-- Each step `x + ih` has `α`-coefficient `m` with `|m| < |n|`. -/
private lemma step_reduces_alpha_coefficient
    {α : ℝ} {p : ℕ → ℤ} {q : ℕ → ℕ} {j : ℕ} {N : ℕ}
    {n : ℤ} (hqn : (↑(q j) : ℝ) < (↑(Int.natAbs n) : ℝ) / ↑N)
    (hN : 2 ≤ N) (hsign : (↑(q j) * α - ↑(p j)) * ↑n < 0)
    (hq_pos_j : 0 < q j)
    (i : ℕ) (hi1 : 1 ≤ i) (hi2 : i ≤ N) :
    let h := |↑(q j) * α - ↑(p j)|
    let m := n + (if 0 < ↑(q j) * α - ↑(p j) then (1 : ℤ) else (-1 : ℤ)) * ↑i * ↑(q j)
    ∃ l : ℤ, ↑n * α + ↑(0 : ℤ) + ↑i * h = ↑m * α + ↑l ∧
      Int.natAbs m < Int.natAbs n := by
  simp only [Int.cast_zero, add_zero]
  have hiq_pos : 0 < i * q j := Nat.mul_pos (by omega) hq_pos_j
  have hiq_lt : (i * q j : ℤ) < ↑(Int.natAbs n) := by
    have h1 : (i : ℝ) * ↑(q j) < ↑(Int.natAbs n) := by
      calc (i : ℝ) * ↑(q j) ≤ ↑N * ↑(q j) := by exact_mod_cast Nat.mul_le_mul_right _ hi2
        _ < ↑(Int.natAbs n) := by rw [lt_div_iff₀ (by positivity : (0:ℝ) < ↑N)] at hqn; linarith
    exact_mod_cast h1
  split_ifs with heps
  · have hn_neg : n < 0 := by
      by_contra h; push Not at h
      have : (0 : ℝ) ≤ (↑(q j) * α - ↑(p j)) * ↑n := mul_nonneg (le_of_lt heps) (by exact_mod_cast h)
      linarith
    refine ⟨-(↑i : ℤ) * ↑(p j), ?_, ?_⟩
    · rw [abs_of_pos heps]; push_cast; ring
    · rw [show n + 1 * ↑i * ↑(q j) = n + ↑(i * q j) from by push_cast; ring]
      exact int_natAbs_add_neg_lt n (i * q j) hn_neg hiq_pos (by exact_mod_cast hiq_lt)
  · have hn_pos : (0 : ℤ) < n := by
      by_contra h; push Not at h
      have heps_le : (↑(q j) * α - ↑(p j) : ℝ) ≤ 0 := not_lt.mp heps
      have : (0 : ℝ) ≤ (↑(q j) * α - ↑(p j)) * ↑n := by nlinarith [show (↑n : ℝ) ≤ 0 from by exact_mod_cast h]
      linarith
    refine ⟨(↑i : ℤ) * ↑(p j), ?_, ?_⟩
    · rw [abs_of_nonpos (not_lt.mp heps)]; push_cast; ring
    · rw [show n + -1 * ↑i * ↑(q j) = n - ↑(i * q j) from by push_cast; ring]
      exact int_natAbs_sub_pos_lt n (i * q j) hn_pos hiq_pos (by omega)

/-- Block inclusion for integer translates. -/
private lemma fixed_line_block_inclusion {N : ℕ} {H : Set ℝ} {y : ℝ}
    (hmem : ∀ i : ℕ, 1 ≤ i → i ≤ N → HSetPow N H (y + ↑i)) :
    HSetPow N H y := by
  convert HSetPow.step 1 zero_lt_one _
  aesop

/-- Downward induction along integer translates in `H^(N)`. -/
private lemma fixed_line_backward_induction {N : ℕ} {H : Set ℝ} {y : ℝ} {J : ℤ}
    (hblock : ∀ t : ℤ, J - ↑N + 1 ≤ t → t ≤ J → HSetPow N H (y + ↑t)) :
    ∀ t : ℤ, t ≤ J → HSetPow N H (y + ↑t) := by
  suffices h_ind : ∀ t : ℤ, t ≤ J → (∀ s : ℤ, t < s → s ≤ J → HSetPow N H (y + s)) → HSetPow N H (y + t) by
    contrapose! h_ind
    have h_max : ∃ t ∈ {t : ℤ | t ≤ J ∧ ¬HSetPow N H (y + t)}, ∀ s ∈ {t : ℤ | t ≤ J ∧ ¬HSetPow N H (y + t)}, t ≥ s := by
      apply_rules [Int.exists_greatest_of_bdd]
      exact ⟨ J, fun z hz ↦ hz.1 ⟩
    obtain ⟨ t, ht₁, ht₂ ⟩ := h_max; exact ⟨ t, ht₁.1, fun s hs₁ hs₂ ↦ Classical.not_not.1 fun hs₃ ↦ not_lt_of_ge (ht₂ s ⟨ hs₂, hs₃ ⟩) hs₁, ht₁.2 ⟩
  intros t ht h_ind_step
  by_cases h_case : t + N ≤ J
  · convert fixed_line_block_inclusion _ using 1
    exact fun i hi₁ hi₂ ↦ by simpa [add_assoc] using h_ind_step (t + i) (by linarith) (by linarith)
  · exact hblock t (by linarith) ht

/-- If `|n| ≤ DN` and `x ≤ b + DN²/|n|`, then `x ∈ H^(N)`. -/
private lemma small_coefficient_case
    {α : ℝ} {D : ℝ} {N : ℕ} {b : ℝ} (hN : 2 ≤ N) (hD : 0 < D)
    {H : Set ℝ} (hH : ∀ (n' : ℤ) (k' : ℤ),
      (↑(Int.natAbs n') : ℝ) ≤ D * ↑N → b - ↑N ≤ ↑n' * α + ↑k' →
      ↑n' * α + ↑k' ≤ b + D * (↑N) ^ 2 → ↑n' * α + ↑k' ∈ H)
    {n : ℤ} {k : ℤ} (hn : n ≠ 0) (hn_small : (↑(Int.natAbs n) : ℝ) ≤ D * ↑N)
    (hx : ↑n * α + ↑k ≤ b + D * (↑N) ^ 2 / (↑(Int.natAbs n) : ℝ)) :
    HSetPow N H (↑n * α + ↑k) := by
  set y := (n : ℝ) * α
  set J := ⌊b + D * (N : ℝ) ^ 2 - (n : ℝ) * α⌋
  have h_ind : ∀ t : ℤ, t ≤ J → HSetPow N H (y + t) := by
    apply fixed_line_backward_induction
    intros t ht1 ht2
    have h_bounds : b - N ≤ y + t ∧ y + t ≤ b + D * (N : ℝ) ^ 2 := by
      constructor <;> nlinarith [Int.floor_le (b + D * N ^ 2 - (n : ℝ) * α), Int.lt_floor_add_one (b + D * N ^ 2 - (n : ℝ) * α), show (t : ℝ) ≥ J - N + 1 by exact_mod_cast ht1, show (t : ℝ) ≤ J by exact_mod_cast ht2]
    exact HSetPow.base (hH n t hn_small h_bounds.1 h_bounds.2)
  refine h_ind k (Int.le_floor.mpr ?_)
  simp +zetaDelta at *
  nlinarith [show (1 : ℝ) ≤ |↑n| by exact mod_cast abs_pos.mpr hn, show (0 : ℝ) ≤ D * (N : ℝ) ^ 2 by positivity, mul_div_cancel₀ (D * (N : ℝ) ^ 2) (show (|↑n| : ℝ) ≠ 0 by exact mod_cast ne_of_gt (abs_pos.mpr hn))]

/-- Generalized transfer bound using any `D ≥ AC⁴` instead of `AC⁴`. -/
private lemma transfer_increment_bound_gen
    {α : ℝ} {A C : ℝ} {p : ℕ → ℤ} {q : ℕ → ℕ} {j : ℕ} {N : ℕ} {n : ℤ} {k : ℤ} {b : ℝ}
    (hA : A > 0) (hC : C > 1) (hq_pos : 0 < q j)
    (h_approx : |↑(q j) * α - ↑(p j)| ≤ A / ↑(q j))
    (hqn_lower : (↑(Int.natAbs n) : ℝ) / (C ^ 2 * ↑N) ≤ ↑(q j))
    (hn : n ≠ 0) (hN : 2 ≤ N)
    {D : ℝ} (hD : D ≥ A * C ^ 4)
    (hx : ↑n * α + ↑k ≤ b + D * (↑N) ^ 2 / (↑(Int.natAbs n) : ℝ))
    (i : ℕ) (_ : 1 ≤ i) (_ : i ≤ N)
    (m : ℤ) (hm : Int.natAbs m = Int.natAbs n - i * q j) (hm0 : m ≠ 0)
    (l : ℤ) (hml : ↑n * α + ↑k + ↑i * |↑(q j) * α - ↑(p j)| = ↑m * α + ↑l) :
    ↑m * α + ↑l ≤ b + D * (↑N) ^ 2 / (↑(Int.natAbs m) : ℝ) := by
  have h_mul : D * N^2 * m.natAbs ≤ D * N^2 * n.natAbs - i * A / q j * m.natAbs * n.natAbs := by
    have h_mul : A * m.natAbs * n.natAbs ≤ D * N^2 * q j^2 := by
      have h_mul : m.natAbs ≤ C^2 * N * q j ∧ n.natAbs ≤ C^2 * N * q j := by
        rw [div_le_iff₀] at hqn_lower <;> norm_cast at *
        · exact ⟨ by rw [hm]; exact le_trans (Nat.cast_le.mpr (Nat.sub_le _ _)) (by push_cast at *; linarith), by push_cast at *; linarith ⟩
        · positivity
      refine le_trans (mul_le_mul (mul_le_mul_of_nonneg_left h_mul.1 hA.le) h_mul.2 ?_ ?_) ?_
      · positivity
      · positivity
      · nlinarith [show 0 < (N : ℝ) ^ 2 * q j ^ 2 by positivity]
    field_simp
    rw [eq_tsub_iff_add_eq_of_le] at hm
    · rw [← @Nat.cast_inj ℝ] at *; push_cast at *; nlinarith [show 0 < (q j : ℝ) * D * N ^ 2 by exact mul_pos (mul_pos (Nat.cast_pos.mpr hq_pos) (show 0 < D by exact lt_of_lt_of_le (by positivity) hD)) (by positivity)]
    · exact le_of_lt (Nat.lt_of_sub_ne_zero (by aesop))
  rw [← hml]
  refine le_trans (add_le_add hx <| mul_le_mul_of_nonneg_left h_approx <| Nat.cast_nonneg _) ?_
  field_simp
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div, sub_div', le_div_iff₀] at h_mul <;> first | positivity | nlinarith

/-- Main induction: `x = nα + k` with `n ≠ 0` and `x ≤ b + DN²/|n|` implies `x ∈ H^(N)`. -/
private lemma lemma2_induction_claim
    {α : ℝ} {A C : ℝ} {p : ℕ → ℤ} {q : ℕ → ℕ}
    (hA : A > 0) (hC : C > 1) (hq_pos : ∀ j, 0 < q j)
    (hq_tendsto : Tendsto (fun j ↦ (q j : ℝ)) atTop atTop)
    (hq_growth : ∀ j, (q (j + 1) : ℝ) ≤ C * ↑(q j))
    (h_approx : ∀ j, 0 < |↑(q j) * α - ↑(p j)| ∧ |↑(q j) * α - ↑(p j)| ≤ A / ↑(q j))
    (h_alt_sign : ∀ j, (↑(q j) * α - ↑(p j)) * (↑(q (j + 1)) * α - ↑(p (j + 1))) < 0)
    {N : ℕ} (hN : 2 ≤ N) {b : ℝ} {D : ℝ} (hD1 : D ≥ A * C ^ 4) (hD2 : D > C * ↑(q 0))
    {H : Set ℝ} (hH : ∀ (n' : ℤ) (k' : ℤ),
      (↑(Int.natAbs n') : ℝ) ≤ D * ↑N → b - ↑N ≤ ↑n' * α + ↑k' →
      ↑n' * α + ↑k' ≤ b + D * (↑N) ^ 2 → ↑n' * α + ↑k' ∈ H)
    {n : ℤ} (hn : n ≠ 0) {k : ℤ}
    (hx : ↑n * α + ↑k ≤ b + D * (↑N) ^ 2 / (↑(Int.natAbs n) : ℝ)) :
    HSetPow N H (↑n * α + ↑k) := by
  suffices h : ∀ (nn : ℕ), ∀ (n : ℤ), n ≠ 0 → n.natAbs = nn → ∀ (k : ℤ),
      ↑n * α + ↑k ≤ b + D * ↑N ^ 2 / ↑n.natAbs → HSetPow N H (↑n * α + ↑k) from
    h n.natAbs n hn rfl k hx
  intro nn
  induction nn using Nat.strongRecOn with
  | _ nn ih =>
  intro n hn hnn k hx
  by_cases hn_small : (↑n.natAbs : ℝ) ≤ D * ↑N
  · exact small_coefficient_case hN
      (by nlinarith [mul_pos (show (0:ℝ) < C by linarith) (show (0:ℝ) < ↑(q 0) by exact_mod_cast hq_pos 0), pow_pos (show (0:ℝ) < C by linarith) 4])
      hH hn hn_small hx
  · push Not at hn_small
    have hN_pos : (0 : ℝ) < ↑N := by exact_mod_cast show 0 < N by omega
    have hn_large : C * (q 0 : ℝ) * ↑N < (↑n.natAbs : ℝ) := by
      have : C * ↑(q 0) * ↑N < D * ↑N := by nlinarith
      linarith
    obtain ⟨j, hj_lt, hj_sign, hj_lower, _⟩ := largest_opposite_sign_index_exists_and_is_bounded
      hC hq_pos hq_tendsto hq_growth h_alt_sign hN n hn hn_large
    apply HSetPow.step (|↑(q j) * α - ↑(p j)|) (h_approx j).1
    intro i hi1 hi2
    obtain ⟨l, hml, hm_lt⟩ := step_reduces_alpha_coefficient hj_lt hN hj_sign (hq_pos j) i hi1 hi2
    simp only [Int.cast_zero, add_zero] at hml
    set m := n + (if 0 < ↑(q j) * α - ↑(p j) then (1 : ℤ) else (-1 : ℤ)) * ↑i * ↑(q j) with m_def
    have hiq_nat : i * q j < n.natAbs := by
      have h1 : (↑i * ↑(q j) : ℝ) < ↑n.natAbs := by
        calc (↑i : ℝ) * ↑(q j) ≤ ↑N * ↑(q j) := by
              exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hi2) (Nat.cast_nonneg _)
          _ < ↑n.natAbs := by have := (lt_div_iff₀ hN_pos).mp hj_lt; linarith
      exact_mod_cast h1
    have hm_eq : m.natAbs = n.natAbs - i * q j := by
      simp only [m_def]
      split_ifs with heps
      · have hn_neg : n < 0 := by
          by_contra h; push Not at h
          have : (0 : ℝ) ≤ (↑(q j) * α - ↑(p j)) * ↑n :=
            mul_nonneg (le_of_lt heps) (by exact_mod_cast h)
          linarith
        have h1 : n + 1 * ↑i * ↑(q j) = n + ↑(i * q j) := by push_cast; ring
        rw [h1]
        rcases Int.natAbs_eq n with h | h <;> omega
      · have hn_pos : 0 < n := by
          by_contra h; push Not at h
          have heps_le : (↑(q j) * α - ↑(p j) : ℝ) ≤ 0 := not_lt.mp heps
          have : (0 : ℝ) ≤ (↑(q j) * α - ↑(p j)) * ↑n := by
            nlinarith [show (↑n : ℝ) ≤ 0 from by exact_mod_cast h]
          linarith
        have h1 : n + -1 * ↑i * ↑(q j) = n - ↑(i * q j) := by push_cast; ring
        rw [h1]
        rcases Int.natAbs_eq n with h | h <;> omega
    have hm0 : m ≠ 0 := by
      intro heq; simp [heq] at hm_eq; omega
    have hml2 : ↑n * α + ↑k + ↑i * |↑(q j) * α - ↑(p j)| = ↑m * α + ↑(l + k) := by
      push_cast; linarith
    have hm_lt2 : m.natAbs < nn := hnn ▸ hm_lt
    have hm_bound : ↑m * α + ↑(l + k) ≤ b + D * ↑N ^ 2 / ↑m.natAbs := by
      exact transfer_increment_bound_gen hA hC (hq_pos j) (h_approx j).2
        hj_lower hn hN hD1 hx i hi1 hi2 m hm_eq hm0 (l + k) hml2
    rw [hml2]
    exact ih m.natAbs hm_lt2 m hm0 rfl (l + k) hm_bound

/-- Every integer `m ≤ b+1` belongs to `H^(N)` if `H` contains all integers in `[b-N, b+1]`. -/
private lemma integers_below_are_in_closure {N : ℕ} {b : ℝ}
    {H : Set ℝ} (hH : ∀ (m : ℤ), (b - ↑N ≤ ↑m ∧ ↑m ≤ b + 1) → (↑m : ℝ) ∈ H) :
    ∀ (m : ℤ), (↑m : ℝ) ≤ b + 1 → HSetPow N H (↑m : ℝ) := by
  intro m hm; by_cases hm' : b - N ≤ m <;> simp_all +decide
  · exact HSetPow.base (hH m hm' hm)
  · by_contra h_contra
    obtain ⟨m, hm₁, hm₂⟩ : ∃ m : ℤ, m ≤ b + 1 ∧ ¬HSetPow N H m ∧ ∀ n : ℤ, m < n → n ≤ b + 1 → HSetPow N H n := by
      have h_exists_m : ∃ m : ℤ, m ≤ b + 1 ∧ ¬HSetPow N H m := by use m
      obtain ⟨m, hm₁, hm₂⟩ : ∃ m : ℤ, m ≤ b + 1 ∧ ¬HSetPow N H m ∧ ∀ n : ℤ, n ≤ b + 1 → ¬HSetPow N H n → n ≤ m := by
        have h_exists_m : ∃ m ∈ {n : ℤ | n ≤ b + 1 ∧ ¬HSetPow N H n}, ∀ n ∈ {n : ℤ | n ≤ b + 1 ∧ ¬HSetPow N H n}, n ≤ m := by
          apply_rules [Int.exists_greatest_of_bdd]
          exact ⟨ ⌊b + 1⌋, fun z hz ↦ Int.le_floor.2 hz.1 ⟩
        aesop
      grind +splitImp
    have hm₃ : ∀ i : ℕ, 1 ≤ i → i ≤ N → HSetPow N H (m + i) := by
      intros i hi₁ hi₂; exact (by
      convert hm₂.2 (m + i) (by linarith) _ using 1; norm_num
      by_cases hi₃ : m + i ≤ b + 1 <;> simp_all +decide
      exact False.elim <| hm₂.1 <| HSetPow.base <| hH m (by linarith [show (i : ℝ) ≤ N by norm_cast]) hm₁ |> fun h ↦ by simpa using h)
    apply hm₂.left; exact (by
    apply HSetPow.step
    exacts [zero_lt_one, fun i hi₁ hi₂ ↦ by simpa using hm₃ i hi₁ hi₂])

/-- Covering lemma: there exists finite `H ⊆ I(α)` with `H^(N) ⊃ I(α) ∩ (-∞, b]`. -/
lemma lemma2 (α : ℝ) (hα : HasControlledIntegerApproximants α) (N : ℕ) (hN : 2 ≤ N) (b : ℝ) :
    ∃ H : Set ℝ, H.Finite ∧ H ⊆ I α ∧ I α ∩ Iic b ⊆ HSetPow N H := by
  revert b; intro b
  obtain ⟨A, C, p, q, hA_pos, hC_gt1, hq_pos, hq_tendsto, hq_growth, h_approx, h_alt_sign⟩ := hα
  set D := A * C^4 + C * (q 0 : ℝ) + 1 with hD_def
  have hD1 : D ≥ A * C^4 := le_add_of_le_of_nonneg (le_add_of_nonneg_right (by positivity)) zero_le_one
  have hD2 : D > C * (q 0 : ℝ) := lt_add_of_le_of_pos (le_add_of_nonneg_left <| by positivity) zero_lt_one
  refine ⟨{ x : ℝ | ∃ n k : ℤ, x = n * α + k ∧ (Int.natAbs n : ℝ) ≤ D * N ∧ b - N ≤ x ∧ x ≤ b + D * N ^ 2 }, ?_, ?_, ?_⟩
  · convert seed_set_finite α D N b using 1
  · exact fun x hx ↦ by obtain ⟨ n, k, rfl, hn, hk₁, hk₂ ⟩ := hx; exact ⟨ n, k, rfl ⟩
  · rintro x ⟨ ⟨ n, k, rfl ⟩, hx ⟩
    by_cases hn : n = 0
    · have h_integers_below_are_in_closure : ∀ m : ℤ, (m : ℝ) ≤ b + 1 → HSetPow N {x : ℝ | ∃ n k : ℤ, x = n * α + k ∧ (Int.natAbs n : ℝ) ≤ D * N ∧ b - N ≤ x ∧ x ≤ b + D * N ^ 2} (m : ℝ) := by
        apply integers_below_are_in_closure
        intro m hm; use 0, m; simp [hm]
        exact ⟨ by positivity, by nlinarith [show (N : ℝ) ≥ 2 by norm_cast, show (D : ℝ) ≥ 1 by exact le_add_of_le_of_nonneg (le_add_of_nonneg_of_le (by positivity) (by nlinarith [show (q 0 : ℝ) ≥ 1 by exact_mod_cast hq_pos 0])) zero_le_one, pow_two (N - 1 : ℝ)] ⟩
      simpa [hn] using h_integers_below_are_in_closure k (by simpa [hn] using hx.out.trans (by linarith))
    · apply lemma2_induction_claim hA_pos hC_gt1 hq_pos hq_tendsto hq_growth h_approx h_alt_sign hN hD1 hD2
      exact fun n' k' hn' hk' hk'' ↦ ⟨ n', k', rfl, hn', hk', hk'' ⟩
      · assumption
      · exact le_add_of_le_of_nonneg hx (by positivity)

/-! ## Section 3: Monotonicity on `I(α)` -/

/-- If `f ≤ M` on `H` and `f` satisfies the Kemperman inequality on `H^(N)`,
then `f ≤ M` on `H^(N)`. -/
private lemma closure_boundedness_principle {N : ℕ} (hN : 2 ≤ N) {H : Set ℝ}
    {f : ℝ → ℝ} {M : ℝ}
    (hf_ineq : ∀ x h : ℝ, x ∈ HSetPow N H → h > 0 → (x + h) ∈ HSetPow N H →
      (x + 2 * h) ∈ HSetPow N H → 2 * f x ≤ f (x + h) + f (x + 2 * h))
    (hf_bound : ∀ y, y ∈ H → f y ≤ M) :
    ∀ x, x ∈ HSetPow N H → f x ≤ M := by
  intro x hx
  induction' hx with x h hx ih
  · exact hf_bound x h
  · have h_ind : f (hx + ih) ≤ M ∧ f (hx + 2 * ih) ≤ M := ⟨ by simpa using ‹∀ i : ℕ, 1 ≤ i → i ≤ N → f (hx + i * ih) ≤ M› 1 (by norm_num) (by linarith), by simpa using ‹∀ i : ℕ, 1 ≤ i → i ≤ N → f (hx + i * ih) ≤ M› 2 (by norm_num) (by linarith) ⟩
    contrapose! hf_ineq
    have hx_in_H_pow : hx ∈ HSetPow N H := by
      apply HSetPow.step
      exacts [by assumption, by assumption]
    exact ⟨ _, _, hx_in_H_pow, ‹_›, by simpa using ‹∀ i : ℕ, 1 ≤ i → i ≤ N → HSetPow N H (hx + i * ih) › 1 le_rfl (by linarith), by simpa using ‹∀ i : ℕ, 1 ≤ i → i ≤ N → HSetPow N H (hx + i * ih) › 2 (by linarith) (by linarith), by linarith ⟩

/-- `f` is bounded above on `I(α) ∩ (-∞, b]` under controlled approximants. -/
private lemma bounded_on_left_ray_in_I {α : ℝ} (hα : HasControlledIntegerApproximants α)
    {f : ℝ → ℝ}
    (hf : ∀ x ∈ I α, ∀ h : ℝ, h > 0 → (x + h) ∈ I α → (x + 2 * h) ∈ I α →
      2 * f x ≤ f (x + h) + f (x + 2 * h))
    (b : ℝ) :
    BddAbove (f '' (I α ∩ Iic b)) := by
  obtain ⟨H, hH⟩ := lemma2 α hα 2 (by norm_num) b
  obtain ⟨M, hM⟩ : ∃ M, ∀ y ∈ H, f y ≤ M := by
    exact ⟨ ∑ y ∈ hH.1.toFinset, |f y|, fun y hy ↦ le_trans (le_abs_self _) (Finset.single_le_sum (fun x _ ↦ abs_nonneg (f x)) (hH.1.mem_toFinset.mpr hy)) ⟩
  have h_closure_bounded : ∀ x ∈ HSetPow 2 H, f x ≤ M := by
    apply closure_boundedness_principle (by norm_num)
    · intros x h hx hh hx' hx''
      apply hf x
      · have h_closure_subset_I : ∀ x ∈ HSetPow 2 H, x ∈ I α := by
          intros x hx; induction hx; aesop
          rename_i k hk₁ hk₂ hk₃
          obtain ⟨ n₁, k₁, hn₁ ⟩ := hk₃ 1 (by norm_num) (by norm_num); obtain ⟨ n₂, k₂, hn₂ ⟩ := hk₃ 2 (by norm_num) (by norm_num); exact ⟨ n₁ * 2 - n₂, k₁ * 2 - k₂, by push_cast at *; linarith ⟩
        exact h_closure_subset_I x hx
      · exact hh
      · have h_closure : ∀ x ∈ HSetPow 2 H, x ∈ I α := by
          intros x hx; induction hx; aesop
          rename_i k hk₁ hk₂ hk₃
          obtain ⟨ n₁, k₁, hn₁ ⟩ := hk₃ 1 (by norm_num) (by norm_num); obtain ⟨ n₂, k₂, hn₂ ⟩ := hk₃ 2 (by norm_num) (by norm_num); exact ⟨ n₁ * 2 - n₂, k₁ * 2 - k₂, by push_cast at *; linarith ⟩
        exact h_closure _ hx'
      · have h_closure : ∀ x ∈ HSetPow 2 H, x ∈ I α := by
          intros x hx; induction hx; aesop
          rename_i k hk₁ hk₂ hk₃
          obtain ⟨ n₁, k₁, hn₁ ⟩ := hk₃ 1 (by norm_num) (by norm_num); obtain ⟨ n₂, k₂, hn₂ ⟩ := hk₃ 2 (by norm_num) (by norm_num); exact ⟨ n₁ * 2 - n₂, k₁ * 2 - k₂, by push_cast at *; linarith ⟩
        exact h_closure _ hx''
    · assumption
  exact ⟨ M, Set.forall_mem_image.2 fun x hx ↦ h_closure_bounded x <| hH.2.2 hx ⟩

/-- `f` is bounded above on `[a,b] ∩ I(α)`. -/
private lemma bounded_on_compact_piece_of_I {α : ℝ} (hα : HasControlledIntegerApproximants α)
    {f : ℝ → ℝ}
    (hf : ∀ x ∈ I α, ∀ h : ℝ, h > 0 → (x + h) ∈ I α → (x + 2 * h) ∈ I α →
      2 * f x ≤ f (x + h) + f (x + 2 * h))
    {a b : ℝ} :
    BddAbove (f '' (I α ∩ Icc a b)) := by
  obtain ⟨ M, hM ⟩ := bounded_on_left_ray_in_I hα hf b
  exact ⟨ M, fun x hx ↦ hM <| by obtain ⟨ y, hy, rfl ⟩ := hx; exact ⟨ y, ⟨ hy.1, hy.2.2 ⟩, rfl ⟩ ⟩

/-- `I(α)` is dense in `ℝ` when `α` is irrational. -/
private lemma I_dense {α : ℝ} (hα : Irrational α) : Dense (I α) := by
  refine fun x ↦ Metric.mem_closure_iff.2 fun ε εpos ↦ ?_
  obtain ⟨n, m, hnm⟩ : ∃ n : ℤ, ∃ m : ℤ, |n * α - m| < ε ∧ 0 < n := by
    obtain ⟨n1, n2, hn1n2, h_interval⟩ : ∃ n1 n2 : ℕ, n1 < n2 ∧ |Int.fract (n1 * α) - Int.fract (n2 * α)| < ε := by
      have h_pigeonhole : ∃ n1 n2 : ℕ, n1 < n2 ∧ ⌊Int.fract (n1 * α) / ε⌋ = ⌊Int.fract (n2 * α) / ε⌋ := by
        by_contra! h
        exact absurd (Set.infinite_range_of_injective (fun n m hnm ↦ le_antisymm (not_lt.mp fun contra ↦ h _ _ contra hnm.symm) (not_lt.mp fun contra ↦ h _ _ contra hnm))) (Set.not_infinite.mpr <| Set.Finite.subset (Set.finite_Ico (0 : ℤ) (⌈ε⁻¹⌉₊ : ℤ)) <| Set.range_subset_iff.mpr fun n ↦ ⟨ Int.floor_nonneg.mpr <| div_nonneg (Int.fract_nonneg _) εpos.le, Int.floor_lt.mpr <| by simpa using div_lt_iff₀ εpos |>.2 <| by nlinarith [Nat.le_ceil (ε⁻¹), Int.fract_lt_one ((n : ℝ) * α), mul_inv_cancel₀ εpos.ne'] ⟩)
      obtain ⟨ n1, n2, h1, h2 ⟩ := h_pigeonhole
      rw [Int.floor_eq_iff] at h2
      exact ⟨ n1, n2, h1, abs_lt.mpr ⟨ by nlinarith [Int.floor_le (Int.fract (n2 * α) / ε), Int.lt_floor_add_one (Int.fract (n2 * α) / ε), mul_div_cancel₀ (Int.fract (n1 * α)) εpos.ne', mul_div_cancel₀ (Int.fract (n2 * α)) εpos.ne'], by nlinarith [Int.floor_le (Int.fract (n2 * α) / ε), Int.lt_floor_add_one (Int.fract (n2 * α) / ε), mul_div_cancel₀ (Int.fract (n1 * α)) εpos.ne', mul_div_cancel₀ (Int.fract (n2 * α)) εpos.ne'] ⟩ ⟩
    exact ⟨ n2 - n1, ⌊ (n2 : ℝ) * α⌋ - ⌊ (n1 : ℝ) * α⌋, by push_cast; rw [abs_lt]; constructor <;> linarith [abs_lt.mp h_interval, Int.fract_add_floor ((n2 : ℝ) * α), Int.fract_add_floor ((n1 : ℝ) * α)], by linarith ⟩
  obtain ⟨k, hk⟩ : ∃ k : ℤ, |k * (n * α - m) - x| < ε := by
    exact ⟨ ⌊x / (n * α - m) ⌋, by rw [abs_lt]; constructor <;> nlinarith [Int.floor_le (x / (n * α - m)), Int.lt_floor_add_one (x / (n * α - m)), mul_div_cancel₀ x (show (n * α - m : ℝ) ≠ 0 from sub_ne_zero_of_ne <| by intro h; exact hα <| ⟨ m / n, by push_cast; rw [div_eq_iff (by norm_cast; linarith)]; linarith ⟩), abs_lt.mp hnm.1] ⟩
  exact ⟨ _, ⟨ k * n, -k * m, rfl ⟩, by simpa [mul_sub, mul_assoc, mul_left_comm] using abs_lt.mpr ⟨ by linarith [abs_lt.mp hk], by linarith [abs_lt.mp hk] ⟩ ⟩

/-- Existence of positive `c, d ∈ I(α)` with `Nc + (N+1)d = b - a`. -/
private lemma choose_positive_c_d_in_I {α : ℝ} (hα : Irrational α)
    {a b : ℝ} (hab : a < b) (ha : a ∈ I α) (hb : b ∈ I α) {N : ℕ} (hN : 2 ≤ N) :
    ∃ c d : ℝ, c ∈ I α ∧ d ∈ I α ∧ c > 0 ∧ d > 0 ∧
      ↑N * c + ↑(N + 1) * d = b - a := by
  obtain ⟨t, u, ht⟩ : ∃ t u : ℤ, (b - a) / (N + 1 : ℝ) < (t : ℝ) * α + u ∧ (t : ℝ) * α + u < (b - a) / (N : ℝ) := by
    have h_dense : Dense (Set.range (fun p : ℤ × ℤ ↦ (p.1 : ℝ) * α + p.2)) := by
      convert I_dense hα using 1
      exact Set.ext fun x ↦ ⟨ fun ⟨ p, hp ⟩ ↦ ⟨ p.1, p.2, hp.symm ⟩, fun ⟨ n, k, hk ⟩ ↦ ⟨ ⟨ n, k ⟩, hk.symm ⟩ ⟩
    have := h_dense.exists_between (show (b - a) / (N + 1 : ℝ) < (b - a) / N from by rw [div_lt_div_iff₀] <;> nlinarith [show (N : ℝ) ≥ 2 by norm_cast]); aesop
  obtain ⟨n_coeff, k_coeff, hn_coeff⟩ : ∃ n_coeff k_coeff : ℤ, b - a = n_coeff * α + k_coeff := by
    rcases ha with ⟨ n₁, k₁, rfl ⟩; rcases hb with ⟨ n₂, k₂, rfl ⟩; exact ⟨ n₂ - n₁, k₂ - k₁, by push_cast; ring ⟩
  obtain ⟨p, r, q, s, hpqr⟩ : ∃ p r q s : ℤ, N * p + (N + 1) * r = n_coeff ∧ N * q + (N + 1) * s = k_coeff ∧ (p : ℝ) * α + q > 0 ∧ (r : ℝ) * α + s > 0 := by
    use (N + 1) * t - n_coeff, -N * t + n_coeff, (N + 1) * u - k_coeff, -N * u + k_coeff
    field_simp at ht
    exact ⟨ by ring, by ring, by push_cast; linarith, by push_cast; linarith ⟩
  refine ⟨p * α + q, r * α + s, ?_, ?_, ?_, ?_, ?_⟩ <;> norm_num at *
  · exact ⟨ p, q, rfl ⟩
  · exact ⟨ r, s, by ring ⟩
  · linarith
  · linarith
  · push_cast [← @Int.cast_inj ℝ] at *; linear_combination' hn_coeff.symm + hpqr.1 * α + hpqr.2.1

/-- Restricting `g` to an arithmetic progression in `[a,b] ∩ I(α)` gives a function in `F_N`. -/
private lemma arithmetic_progression_restriction_in_isF {α : ℝ}
    {g : ℝ → ℝ} {a b : ℝ} {c : ℝ} {NN : ℕ}
    (hg : ∀ x ∈ I α ∩ Icc a b, ∀ h : ℝ, h > 0 → (x + h) ∈ I α ∩ Icc a b →
      (x + 2 * h) ∈ I α ∩ Icc a b → 2 * g x ≤ g (x + h) + g (x + 2 * h))
    (hc : c > 0) (hpts : ∀ i : ℕ, i ≤ NN → a + ↑i * c ∈ I α ∩ Icc a b) :
    IsF NN (fun i ↦ g (a + ↑i * c)) := by
  intro i h hh h2h
  convert hg (a + i * c) (hpts i (by linarith)) (h * c) (by positivity) _ _ using 1 <;> push_cast <;> ring_nf
  · convert hpts (i + h) (by linarith) using 1; push_cast; ring
  · convert hpts (i + 2 * h) h2h using 1; push_cast; ring

/-- First interpolation bound: `g(a) ≤ g(a + Nc) + 10K/N`. -/
private lemma first_interpolation_bound {α : ℝ}
    {g : ℝ → ℝ} {a b : ℝ} {c : ℝ} {K : ℝ} {N : ℕ} (hN : 2 ≤ N)
    (hg : ∀ x ∈ I α ∩ Icc a b, ∀ h : ℝ, h > 0 → (x + h) ∈ I α ∩ Icc a b →
      (x + 2 * h) ∈ I α ∩ Icc a b → 2 * g x ≤ g (x + h) + g (x + 2 * h))
    (hK : 0 < K) (hbound : ∀ i : ℕ, i ≤ N → |g (a + ↑i * c)| ≤ K)
    (hc : c > 0) (hpts : ∀ i : ℕ, i ≤ N → a + ↑i * c ∈ I α ∩ Icc a b) :
    g a ≤ g (a + ↑N * c) + 10 * K / ↑N := by
  set φ : ℕ → ℝ := fun i ↦ g (a + i * c)
  have hφ_in_Fn : IsF N φ := by
    apply arithmetic_progression_restriction_in_isF hg hc hpts
  have := lemma1 (by positivity) hφ_in_Fn hK hbound; aesop

/-- Second interpolation bound: `g(a + Nc) ≤ g(b) + 10K/(N+1)`. -/
private lemma second_interpolation_bound {α : ℝ}
    {g : ℝ → ℝ} {a b : ℝ} {c d : ℝ} {K : ℝ} {N : ℕ} (_ : 2 ≤ N)
    (hg : ∀ x ∈ I α ∩ Icc a b, ∀ h : ℝ, h > 0 → (x + h) ∈ I α ∩ Icc a b →
      (x + 2 * h) ∈ I α ∩ Icc a b → 2 * g x ≤ g (x + h) + g (x + 2 * h))
    (hK : 0 < K)
    (hbound : ∀ i : ℕ, i ≤ N + 1 → |g (a + ↑N * c + ↑i * d)| ≤ K)
    (hd : d > 0) (hpts : ∀ i : ℕ, i ≤ N + 1 → a + ↑N * c + ↑i * d ∈ I α ∩ Icc a b)
    (heq : a + ↑N * c + ↑(N + 1) * d = b) :
    g (a + ↑N * c) ≤ g b + 10 * K / ↑(N + 1) := by
  have h_lemma1 : ∀ (f : ℕ → ℝ) (K : ℝ), IsF (N + 1) f → 0 < K → (∀ i, i ≤ N + 1 → |f i| ≤ K) → f 0 ≤ f (N + 1) + 10 * K / (N + 1) := by
    intros f K hf hK hbound
    have h_lemma1 : f 0 ≤ f (N + 1) + 10 * K / (N + 1) := by
      convert lemma1 _ _ _ _ using 1 <;> norm_cast; aesop (simp_config := {singlePass := true})
    exact h_lemma1
  contrapose! h_lemma1
  refine ⟨fun i ↦ g (a + ↑N * c + ↑i * d), K, ?_, hK, hbound, ?_⟩
  · intro i h hi₁ hi₂
    convert hg (a + N * c + i * d) (hpts i (by linarith)) (h * d) (by positivity) _ _ using 1 <;> push_cast <;> ring_nf
    · convert hpts (i + h) (by linarith) using 1; push_cast; ring
    · convert hpts (i + h * 2) (by linarith) using 1; push_cast; ring
  · grind

/-- Interpolation estimate: `g(a) ≤ g(b) + 10K(1/N + 1/(N+1))`. -/
private lemma interpolation_estimate {α : ℝ} (hα : Irrational α)
    {g : ℝ → ℝ} {a b : ℝ} {K : ℝ}
    (hab : a < b) (ha : a ∈ I α) (hb : b ∈ I α) (hK : 0 < K)
    (hg : ∀ x ∈ I α ∩ Icc a b, ∀ h : ℝ, h > 0 → (x + h) ∈ I α ∩ Icc a b →
      (x + 2 * h) ∈ I α ∩ Icc a b → 2 * g x ≤ g (x + h) + g (x + 2 * h))
    (hbound : ∀ x ∈ I α ∩ Icc a b, |g x| ≤ K)
    {N : ℕ} (hN : 2 ≤ N) :
    g a ≤ g b + 10 * K * (1 / ↑N + 1 / ↑(N + 1)) := by
  obtain ⟨c, d, hc, hd, ceq⟩ := choose_positive_c_d_in_I hα hab ha hb hN
  have hpts : ∀ i : ℕ, i ≤ N → a + ↑i * c ∈ I α ∩ Icc a b := by
    intros i hi; exact ⟨by
    obtain ⟨ n, k, rfl ⟩ := ha; obtain ⟨ n', k', rfl ⟩ := hc; exact ⟨ n + i * n', k + i * k', by push_cast; ring ⟩, by
      constructor <;> push_cast at * <;> nlinarith [show (i : ℝ) ≤ N by norm_cast]⟩
  have hpts2 : ∀ i : ℕ, i ≤ N + 1 → a + ↑N * c + ↑i * d ∈ I α ∩ Icc a b := by
    intro i hi
    have h_mem : a + ↑N * c + ↑i * d ∈ I α := by
      rcases hc with ⟨ n₁, k₁, rfl ⟩; rcases hd with ⟨ n₂, k₂, rfl ⟩; rcases ha with ⟨ n₃, k₃, rfl ⟩; exact ⟨ n₃ + N * n₁ + i * n₂, k₃ + N * k₁ + i * k₂, by push_cast; ring ⟩
    have h_bounds : a ≤ a + ↑N * c + ↑i * d ∧ a + ↑N * c + ↑i * d ≤ b := by
      constructor <;> push_cast at * <;> nlinarith [show (i : ℝ) ≤ N + 1 by norm_cast]
    exact ⟨h_mem, h_bounds⟩
  have := first_interpolation_bound hN hg hK (fun i hi ↦ hbound _ (hpts i hi)) ceq.1 hpts
  have := second_interpolation_bound hN hg hK (fun i hi ↦ hbound _ (hpts2 i hi)) ceq.2.1 hpts2 (by push_cast at *; linarith)
  grind

/-- `f` is monotone on `I(α)` under controlled approximants and the Kemperman inequality. -/
theorem monotoneOn_I {α : ℝ}
    (hα_irr : Irrational α) (hα : HasControlledIntegerApproximants α)
    {f : ℝ → ℝ}
    (hf : ∀ x ∈ I α, ∀ h : ℝ, h > 0 → (x + h) ∈ I α → (x + 2 * h) ∈ I α →
      2 * f x ≤ f (x + h) + f (x + 2 * h)) :
    ∀ a ∈ I α, ∀ b ∈ I α, a ≤ b → f a ≤ f b := by
  intro a ha b hb hab
  by_contra h_contra
  obtain ⟨M, hM⟩ : ∃ M, ∀ x ∈ I α ∩ Set.Icc a b, f x ≤ M := by
    have := @bounded_on_compact_piece_of_I α hα
    exact this hf |> fun ⟨ M, hM ⟩ ↦ ⟨ M, fun x hx ↦ hM ⟨ x, hx, rfl ⟩ ⟩
  set g : ℝ → ℝ := fun x ↦ max (f x) (f b)
  have h_interpolation : ∀ N : ℕ, 2 ≤ N → g a ≤ g b + 10 * max M |f b| * (1 / (N : ℝ) + 1 / (N + 1)) := by
    intros N hN
    have hg_kemperman : ∀ x ∈ I α ∩ Set.Icc a b, ∀ h : ℝ, h > 0 → (x + h) ∈ I α ∩ Set.Icc a b → (x + 2 * h) ∈ I α ∩ Set.Icc a b → 2 * g x ≤ g (x + h) + g (x + 2 * h) := by
      grind
    have hg_bound : ∀ x ∈ I α ∩ Set.Icc a b, |g x| ≤ max M |f b| := by
      grind
    by_cases h_cases : a < b
    · convert interpolation_estimate hα_irr h_cases ha hb (show 0 < max M |f b| from ?_) hg_kemperman hg_bound hN using 1
      · norm_cast
      · grind +splitImp
    · norm_num [show a = b by linarith] at *
  have h_limit : Filter.Tendsto (fun N : ℕ ↦ g b + 10 * max M |f b| * (1 / (N : ℝ) + 1 / (N + 1))) Filter.atTop (nhds (g b)) := by
    exact le_trans (tendsto_const_nhds.add <| tendsto_const_nhds.mul <| Filter.Tendsto.add (tendsto_one_div_atTop_nhds_zero_nat) <| tendsto_one_div_add_atTop_nhds_zero_nat) <| by norm_num
  exact absurd (le_of_tendsto_of_tendsto tendsto_const_nhds h_limit <| Filter.eventually_atTop.mpr ⟨ 2, fun N hN ↦ h_interpolation N hN ⟩) (by aesop)

/-! ## Section 4: Pell sequences and existence of controlled approximants -/

/-- The Pell Q-sequence (denominators of convergents of `√2`). -/
private def PellQ : ℕ → ℕ
  | 0 => 1
  | 1 => 2
  | (n + 2) => 2 * PellQ (n + 1) + PellQ n

/-- The Pell P-sequence (numerators of convergents of `√2`). -/
private def PellP : ℕ → ℕ
  | 0 => 1
  | 1 => 3
  | (n + 2) => 2 * PellP (n + 1) + PellP n

/-- `PellQ n` is always positive. -/
private lemma pellQ_pos (n : ℕ) : 0 < PellQ n := by
  induction n using PellQ.induct with
  | case1 => simp [PellQ]
  | case2 => simp [PellQ]
  | case3 n ih1 ih2 => simp [PellQ]; omega

/-- `PellQ n ≥ n + 1`. -/
private lemma pellQ_ge (n : ℕ) : n + 1 ≤ PellQ n := by
  induction n using PellQ.induct with
  | case1 => simp [PellQ]
  | case2 => simp [PellQ]
  | case3 n ih1 ih2 => simp [PellQ]; omega

/-- `PellQ` tends to infinity. -/
private lemma pellQ_tendsto : Tendsto (fun j ↦ (PellQ j : ℝ)) atTop atTop := by
  apply Filter.tendsto_atTop_atTop.mpr
  intro b; use ⌈b⌉₊; intro n hn
  calc b ≤ ↑⌈b⌉₊ := Nat.le_ceil b
    _ ≤ (n : ℝ) := by exact_mod_cast hn
    _ ≤ (n : ℝ) + 1 := by linarith
    _ ≤ (PellQ n : ℝ) := by exact_mod_cast pellQ_ge n

/-- `PellQ` has growth bounded by factor 3. -/
private lemma pellQ_growth (j : ℕ) : (PellQ (j + 1) : ℝ) ≤ 3 * ↑(PellQ j) := by
  induction j using PellQ.induct with
  | case1 => simp [PellQ]; norm_num
  | case2 => simp [PellQ]; norm_num
  | case3 n ih1 ih2 => simp only [PellQ]; push_cast; nlinarith [pellQ_pos n, pellQ_pos (n + 1)]

/-- `PellQ n ≤ PellP n`. -/
private lemma pellP_ge_pellQ (n : ℕ) : PellQ n ≤ PellP n := by
  induction n using PellP.induct with
  | case1 => simp [PellP, PellQ]
  | case2 => simp [PellP, PellQ]
  | case3 n ih1 ih2 => simp [PellP, PellQ]; omega

/-- `(-1)^(n+2) = (-1)^n`. -/
private lemma neg_one_pow_add_two' (n : ℕ) : (-1 : ℤ)^(n+2) = (-1)^n := by rw [pow_add]; norm_num

/-- The Pell identity and cross-product identity. -/
private lemma pell_both (n : ℕ) :
    ((PellP n : ℤ)^2 - 2 * (PellQ n : ℤ)^2 = (-1)^(n+1)) ∧
    ((PellP (n+1) : ℤ) * PellP n - 2 * (PellQ (n+1) : ℤ) * PellQ n = (-1)^(n+1)) := by
  induction n using PellP.induct with
  | case1 => constructor <;> simp [PellP, PellQ]
  | case2 => constructor <;> simp [PellP, PellQ]
  | case3 n ih_succ ih_n =>
    obtain ⟨d1, c1⟩ := ih_succ; obtain ⟨d0, c0⟩ := ih_n
    have pow_n3 : (-1 : ℤ)^(n+2+1) = (-1)^(n+1) := by
      rw [show n+2+1 = (n+1)+2 from by omega]; exact neg_one_pow_add_two' (n+1)
    have pow_n2 : (-1 : ℤ)^(n+1+1) = -(-1)^(n+1) := by rw [pow_succ]; ring
    rw [pow_n2] at d1 c1; simp only [PellP, PellQ] at c1 ⊢; push_cast at d0 d1 c0 c1 ⊢
    exact ⟨by rw [pow_n3]; nlinarith [d0, d1, c0], by rw [pow_n3]; nlinarith [d0, d1, c0, c1]⟩

/-- The Pell identity over `ℝ`. -/
private lemma pell_identity_real (n : ℕ) : (PellP n : ℝ)^2 - 2 * (PellQ n : ℝ)^2 = (-1 : ℝ)^(n+1) := by
  have h := (pell_both n).1
  have : ((PellP n : ℤ) : ℝ)^2 - 2 * ((PellQ n : ℤ) : ℝ)^2 = ((-1 : ℤ) : ℝ)^(n+1) := by exact_mod_cast h
  push_cast at this; linarith

/-- Sum lower bound for Pell sequences. -/
private lemma pell_sum_ge_q (n : ℕ) : (PellQ n : ℝ) ≤ (PellP n : ℝ) + (PellQ n : ℝ) * √2 := by
  have : (PellQ n : ℝ) ≤ (PellP n : ℝ) := by exact_mod_cast pellP_ge_pellQ n
  have : (0 : ℝ) ≤ (PellQ n : ℝ) * √2 := by positivity
  linarith

/-- `√2` has controlled integer approximants, using Pell convergents. -/
private lemma sqrt2_has_controlled_approximants : HasControlledIntegerApproximants (√2) := by
  use 1, 3, fun n ↦ PellP n, fun n ↦ PellQ n
  refine ⟨by norm_num, by norm_num, pellQ_pos, mod_cast pellQ_tendsto, ?_, ?_, ?_⟩
  · exact pellQ_growth
  · have h_abs : ∀ j, |(PellQ j : ℝ) * Real.sqrt 2 - (PellP j : ℝ)| = 1 / ((PellP j : ℝ) + (PellQ j : ℝ) * Real.sqrt 2) := by
      intro j
      have h_abs_eq : (PellQ j : ℝ) * Real.sqrt 2 - (PellP j : ℝ) = (-1 : ℝ)^(j + 2) / ((PellP j : ℝ) + (PellQ j : ℝ) * Real.sqrt 2) := by
        rw [eq_div_iff]
        · have := pell_identity_real j
          grind +extAll
        · exact ne_of_gt <| add_pos_of_nonneg_of_pos (Nat.cast_nonneg _) <| mul_pos (Nat.cast_pos.mpr <| pellQ_pos _) <| Real.sqrt_pos.mpr zero_lt_two
      norm_num [h_abs_eq, abs_div, abs_mul, abs_of_nonneg, add_nonneg, Real.sqrt_nonneg]
    exact fun j ↦ ⟨ h_abs j ▸ by exact one_div_pos.mpr (by exact add_pos_of_nonneg_of_pos (Nat.cast_nonneg _) (mul_pos (Nat.cast_pos.mpr (pellQ_pos _)) (Real.sqrt_pos.mpr zero_lt_two))), h_abs j ▸ by exact one_div_le_one_div_of_le (Nat.cast_pos.mpr (pellQ_pos _)) (by nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt zero_le_two, pell_sum_ge_q j]) ⟩
  · intro j
    have h_factor : (PellP j : ℝ) - (PellQ j : ℝ) * Real.sqrt 2 = (-1 : ℝ)^(j+1) / ((PellP j : ℝ) + (PellQ j : ℝ) * Real.sqrt 2) ∧ (PellP (j + 1) : ℝ) - (PellQ (j + 1) : ℝ) * Real.sqrt 2 = (-1 : ℝ)^(j+2) / ((PellP (j + 1) : ℝ) + (PellQ (j + 1) : ℝ) * Real.sqrt 2) := by
      constructor <;> rw [eq_div_iff]
      · have := pell_identity_real j
        convert this using 1; ring_nf; norm_num
      · exact ne_of_gt <| add_pos_of_nonneg_of_pos (Nat.cast_nonneg _) <| mul_pos (Nat.cast_pos.mpr <| pellQ_pos _) <| Real.sqrt_pos.mpr zero_lt_two
      · convert pell_identity_real (j + 1) using 1; ring_nf; norm_num
      · exact ne_of_gt (add_pos_of_nonneg_of_pos (Nat.cast_nonneg _) (mul_pos (Nat.cast_pos.mpr (pellQ_pos _)) (Real.sqrt_pos.mpr zero_lt_two)))
    simp_all +decide [pow_succ, div_eq_mul_inv]
    cases' Nat.even_or_odd j with h h <;> rw [h.neg_one_pow] at * <;> nlinarith [show 0 < (PellP j + PellQ j * Real.sqrt 2) ⁻¹ from inv_pos.mpr (by exact add_pos_of_nonneg_of_pos (Nat.cast_nonneg _) (mul_pos (Nat.cast_pos.mpr (pellQ_pos _)) (Real.sqrt_pos.mpr zero_lt_two))), show 0 < (PellP (j + 1) + PellQ (j + 1) * Real.sqrt 2) ⁻¹ from inv_pos.mpr (by exact add_pos_of_nonneg_of_pos (Nat.cast_nonneg _) (mul_pos (Nat.cast_pos.mpr (pellQ_pos _)) (Real.sqrt_pos.mpr zero_lt_two)))]

/-- There exists an irrational number with controlled integer approximants. -/
private lemma exists_irrational_controlled : ∃ α : ℝ, Irrational α ∧ HasControlledIntegerApproximants α :=
  ⟨√2, irrational_sqrt_two, sqrt2_has_controlled_approximants⟩

/-! ## Section 5: Final theorem -/

/-- If `f : ℝ → ℝ` satisfies `2f(x) ≤ f(x+h) + f(x+2h)` for all `x` and `h > 0`,
then `f` is monotone. -/
theorem erdos_1125 {f : ℝ → ℝ}
    (hf : ∀ x : ℝ, ∀ h : ℝ, h > 0 → 2 * f x ≤ f (x + h) + f (x + 2 * h)) :
    Monotone f := by
  obtain ⟨α, hα_irr, hα⟩ := exists_irrational_controlled
  intro a b hab
  by_cases h_cases : b - a = 0
  · rw [sub_eq_zero.mp h_cases]
  · have := @monotoneOn_I α hα_irr hα (fun x ↦ f (a + (b - a) * x)) ?_
    · convert this 0 ?_ 1 ?_ ?_ using 1 <;> norm_num
      · exact ⟨ 0, 0, by norm_num ⟩
      · exact ⟨ 0, 1, by norm_num ⟩
    · exact fun x hx h hh hx' hx'' ↦ by convert hf (a + (b - a) * x) ((b - a) * h) (mul_pos (lt_of_le_of_ne (sub_nonneg.mpr hab) (Ne.symm h_cases)) hh) using 1; ring_nf

#print axioms erdos_1125
-- 'Erdos1125.erdos_1125' depends on axioms: [propext, Classical.choice, Quot.sound]

end

end Erdos1125
