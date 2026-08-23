/- leanprover/lean4:v4.32.0  mathlib v4.32.0 -/
/-
This is a Lean formalization of a solution to Erdős Problem 333.
https://www.erdosproblems.com/forum/thread/333

Informal authors:
- Paul Erdős
- Donald J. Newman
- GPT-5.2 Pro

Formal authors:
- Claude Opus 4.5
- Liam Price
- Kevin Barreto

URLs:
- https://www.erdosproblems.com/forum/thread/333#post-2403
- https://chatgpt.com/s/t_69467152e8808191b9140d006994f284
- https://chatgpt.com/s/t_694c90df3c908191a192f6233c2b14b9
-/
/-
Proven by GPT-5.2 Pro and formalised by Claude Opus 4.5
-/

import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Cast.Field
import Std.Tactic.BVDecide.LRAT.Internal.Clause

/-!
# Erdős Problem #333

## Problem Statement

Let $A \subseteq \mathbb{N}$ be a set of natural density 0. Does there exist a set
$B \subseteq \mathbb{N}$ such that $A \subseteq B + B$ and $|B \cap [0,N]| = o(\sqrt{N})$?

## Answer

**No.** We construct a set $A$ of density 0 such that for every $B$ with $A \subseteq B + B$,
we have $|B \cap [0,N]| \geq c\sqrt{N}$ for infinitely many $N$.

## Proof Outline

1. **Finite obstruction (Lemma 4.1-4.2)**: For each dyadic $N = 2^n$, we construct a
   "hard set" $A_N \subseteq (N/2, N]$ using a greedy hitting set argument. Any $B$ with
   $A_N \subseteq B + B$ must have $|B \cap [0,N]| \geq \varepsilon\sqrt{N}$ where
   $\varepsilon = 1/10$.

2. **Greedy hitting set (Lemma 2)**: Given a family $\mathcal{F}$ of sets, each covering
   a $\delta$-fraction of a universe $U$, we can find a hitting set $H$ with
   $|H| \leq O(\log|\mathcal{F}|)$.

3. **Infinite construction (Section 5)**: Define $A = \bigcup_{n \geq 3} A_{2^n}$.
   The sets $A_{2^n}$ are disjoint (living in disjoint dyadic intervals), and each
   contributes $O(n \cdot 2^{n/2})$ elements, giving $A$ density 0.

4. **Main theorem (Section 7)**: For any $B$ with $A \subseteq B + B$, infinitely many
   dyadic levels force $|B \cap [0,N]| \geq c\sqrt{N}$.

## References

* Erdős Problem #333: https://www.erdosproblems.com/333
-/

open scoped Pointwise
open Finset Filter Real

namespace Erdos333

noncomputable section

/-! ## Basic Definitions -/

/-- The fixed constant ε = 1/10. -/
def epsilon : ℝ := 1 / 10

lemma epsilon_pos : epsilon > 0 := by norm_num [epsilon]

lemma epsilon_sq : epsilon ^ 2 = 1 / 100 := by norm_num [epsilon]

/-- For N even, the "top half" interval J_N = (N/2, N] as a Finset ℕ. -/
def J (N : ℕ) : Finset ℕ := Finset.Ioc (N / 2) N

lemma J_card (N : ℕ) (_ : 2 ≤ N) : (J N).card = N - N / 2 := by
  simp only [J]
  rw [Nat.card_Ioc]

lemma J_card_eq_half (N : ℕ) (hN : Even N) (hN_pos : 0 < N) : (J N).card = N / 2 := by
  simp only [J]
  rw [Nat.card_Ioc]
  have : N / 2 ≤ N := Nat.div_le_self N 2
  have h2 : N = 2 * (N / 2) := (Nat.two_mul_div_two_of_even hN).symm
  omega

/-- m(N) = ⌊ε√N⌋, the threshold for "small" sets. -/
def m (N : ℕ) : ℕ := ⌊epsilon * Real.sqrt N⌋₊

lemma m_le_sqrt (N : ℕ) : (m N : ℝ) ≤ epsilon * Real.sqrt N :=
  Nat.floor_le (by
    apply mul_nonneg
    · exact le_of_lt epsilon_pos
    · exact Real.sqrt_nonneg _)

/-- The family 𝓑_N of subsets B ⊆ [0,N] with |B| ≤ m(N). -/
def 𝓑 (N : ℕ) : Finset (Finset ℕ) :=
  (Finset.Icc 0 N).powerset.filter (fun B => B.card ≤ m N)

/-- For B ⊆ [0,N], S_B = (B + B) ∩ J_N. -/
def S (B : Finset ℕ) (N : ℕ) : Finset ℕ := (B + B) ∩ J N

/-- For B ⊆ [0,N], C_B = J_N \ S_B (elements of J_N not representable as sums from B). -/
def C (B : Finset ℕ) (N : ℕ) : Finset ℕ := J N \ S B N

/-! ## Greedy Hitting Set Lemma -/

/-- Lemma 2 (greedy hitting set) with logarithmic bound.
    The greedy algorithm produces a hitting set H with
    |H| ≤ ⌈log|𝓕| / log(1/(1-δ))⌉.

    Proof: At each step, we hit at least δ fraction of remaining sets.
    After t steps, at most (1-δ)^t · |𝓕| sets remain.
    When (1-δ)^T · |𝓕| < 1, all sets are hit.
    Taking T = ⌈log|𝓕| / log(1/(1-δ))⌉ suffices. -/
theorem exists_hitting_set_log_bound
    (U : Finset ℕ) (δ : ℝ) (hδ_pos : 0 < δ) (hδ_lt : δ < 1)
    (𝓕 : Finset (Finset ℕ))
    (hU_ne : 𝓕.Nonempty → U.Nonempty)
    (h𝓕_sub : ∀ F ∈ 𝓕, F ⊆ U)
    (hF_size : ∀ F ∈ 𝓕, δ * U.card ≤ F.card) :
    ∃ H : Finset ℕ, H ⊆ U ∧ (∀ F ∈ 𝓕, (H ∩ F).Nonempty) ∧
      (H.card : ℝ) ≤ Real.log 𝓕.card / Real.log (1 / (1 - δ)) + 1 := by
  classical
  -- Key constants
  let r := 1 - δ  -- the decay factor, 0 < r < 1
  have hr_pos : 0 < r := by simp only [r]; linarith
  have hr_lt : r < 1 := by simp only [r]; linarith
  have h_log_denom_pos : Real.log (1 / r) > 0 := by
    rw [one_div, Real.log_inv]
    exact neg_pos.mpr (Real.log_neg hr_pos hr_lt)
  -- Base case: empty family
  by_cases h𝓕_empty : 𝓕 = ∅
  · refine ⟨∅, Finset.empty_subset U, fun F hF => by simp [h𝓕_empty] at hF, ?_⟩
    simp only [h𝓕_empty, Finset.card_empty, Nat.cast_zero, Real.log_zero, zero_div, zero_add]
    norm_num
  -- Strong induction on |𝓕|, tracking the bound
  -- We prove: for all n, if |𝓕| = n, then ∃ H with |H| ≤ log(n)/log(1/r) + 1
  have h𝓕_pos : 0 < 𝓕.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr h𝓕_empty)
  -- We use strong induction, but track a real-valued "potential" (1-δ)^{-t} · |𝓕|
  -- After t steps with the greedy algorithm, remaining family has size ≤ (1-δ)^t · |𝓕|
  -- The algorithm terminates when this is < 1
  -- We prove termination happens within log|𝓕|/log(1/(1-δ)) + 1 steps

  -- Alternative: induct on n = |𝓕| and show the bound holds
  induction hn : 𝓕.card using Nat.strong_induction_on generalizing 𝓕 with
  | h n ih =>
  cases n with
  | zero =>
    simp only [Finset.card_eq_zero] at hn
    rw [hn] at h𝓕_empty
    exact absurd rfl h𝓕_empty
  | succ k =>
    have hU_nonempty : U.Nonempty := hU_ne (Finset.nonempty_iff_ne_empty.mpr h𝓕_empty)
    -- Double counting to find u hitting ≥ δ|𝓕| sets
    have h_double_count : ∑ u ∈ U, (𝓕.filter (fun F => u ∈ F)).card =
        ∑ F ∈ 𝓕, (F.filter (· ∈ U)).card := by
      simp_rw [Finset.card_filter]
      rw [Finset.sum_comm]
      congr 1; ext F
      simp only [Finset.sum_boole, Nat.cast_id]
      congr 1; ext u
      simp only [Finset.mem_filter, and_comm]
    have h_filter_eq : ∀ F ∈ 𝓕, (F.filter (· ∈ U)) = F := by
      intros F hF; ext x
      simp only [Finset.mem_filter]
      exact ⟨fun ⟨hx, _⟩ => hx, fun hx => ⟨hx, h𝓕_sub F hF hx⟩⟩
    have h_sum_eq : ∑ F ∈ 𝓕, (F.filter (· ∈ U)).card = ∑ F ∈ 𝓕, F.card := by
      apply Finset.sum_congr rfl; intros F hF; rw [h_filter_eq F hF]
    rw [h_sum_eq] at h_double_count
    have h_sum_ge : (∑ F ∈ 𝓕, F.card : ℝ) ≥ 𝓕.card * (δ * U.card) := by
      calc (∑ F ∈ 𝓕, F.card : ℝ) = ∑ F ∈ 𝓕, (F.card : ℝ) := by norm_cast
        _ ≥ ∑ F ∈ 𝓕, (δ * U.card) := Finset.sum_le_sum (fun F hF => hF_size F hF)
        _ = 𝓕.card * (δ * U.card) := by simp [Finset.sum_const]
    -- There exists u hitting ≥ δ|𝓕| sets
    have h_avg : ∃ u ∈ U, (𝓕.filter (fun F => u ∈ F)).card ≥ δ * 𝓕.card := by
      by_contra h
      push Not at h
      have h_sum_lt : (∑ u ∈ U, (𝓕.filter (fun F => u ∈ F)).card : ℝ) < U.card * (δ * 𝓕.card) := by
        calc (∑ u ∈ U, (𝓕.filter (fun F => u ∈ F)).card : ℝ)
            = ∑ u ∈ U, ((𝓕.filter (fun F => u ∈ F)).card : ℝ) := by norm_cast
          _ < ∑ u ∈ U, (δ * 𝓕.card) := by
              apply Finset.sum_lt_sum
              · intros u hu; exact le_of_lt (h u hu)
              · exact ⟨hU_nonempty.choose, hU_nonempty.choose_spec, h _ hU_nonempty.choose_spec⟩
          _ = U.card * (δ * 𝓕.card) := by simp [Finset.sum_const]
      have h_sum_cast : ((∑ u ∈ U, (𝓕.filter (fun F => u ∈ F)).card) : ℝ) =
          (∑ F ∈ 𝓕, F.card : ℝ) := by exact_mod_cast h_double_count
      rw [h_sum_cast] at h_sum_lt
      have h_comm : U.card * (δ * 𝓕.card) = 𝓕.card * (δ * U.card) := by ring
      rw [h_comm] at h_sum_lt; linarith
    obtain ⟨u, hu_mem, hu_hits⟩ := h_avg
    -- Let 𝓕' = sets not containing u (the remaining unhit sets after adding u)
    let 𝓕' := 𝓕.filter (fun F => u ∉ F)
    -- Key: |𝓕'| ≤ (1-δ)|𝓕| = r|𝓕|
    have h𝓕'_bound : (𝓕'.card : ℝ) ≤ r * 𝓕.card := by
      have h_disjoint : Disjoint 𝓕' (𝓕.filter (fun F => u ∈ F)) := by
        -- Elementwise disjointness: a set cannot both contain and not contain `u`.
        refine Finset.disjoint_left.2 ?_
        intro F hF' hFhit
        have hu_not : u ∉ F := (Finset.mem_filter.mp hF').2
        have hu_in  : u ∈ F := (Finset.mem_filter.mp hFhit).2
        exact hu_not hu_in
      have h_union : 𝓕' ∪ 𝓕.filter (fun F => u ∈ F) = 𝓕 := by
        ext F; simp only [Finset.mem_union, Finset.mem_filter, 𝓕']
        constructor
        · intro h; cases h with | inl h => exact h.1 | inr h => exact h.1
        · intro hF; by_cases hu : u ∈ F
          · exact Or.inr ⟨hF, hu⟩
          · exact Or.inl ⟨hF, hu⟩
      have h_card_sum : 𝓕'.card + (𝓕.filter (fun F => u ∈ F)).card = 𝓕.card := by
        rw [← Finset.card_union_of_disjoint h_disjoint, h_union]
      -- |𝓕'| = |𝓕| - |{F : u ∈ F}| ≤ |𝓕| - δ|𝓕| = (1-δ)|𝓕| = r|𝓕|
      have h_filter_ge : (𝓕.filter (fun F => u ∈ F)).card ≥ δ * 𝓕.card := hu_hits
      have h_sub_card : 𝓕'.card = 𝓕.card - (𝓕.filter (fun F => u ∈ F)).card := by omega
      have h_le_card : (𝓕.filter (fun F => u ∈ F)).card ≤ 𝓕.card := by omega
      calc (𝓕'.card : ℝ) = 𝓕.card - (𝓕.filter (fun F => u ∈ F)).card := by
              rw [h_sub_card]; exact Nat.cast_sub h_le_card
        _ ≤ 𝓕.card - δ * 𝓕.card := by linarith
        _ = (1 - δ) * 𝓕.card := by ring
        _ = r * 𝓕.card := rfl
    have h𝓕'_card_lt : 𝓕'.card < k + 1 := by
      have h1 : (𝓕'.card : ℝ) ≤ r * 𝓕.card := h𝓕'_bound
      have h𝓕_card_pos : (0 : ℝ) < 𝓕.card := by exact_mod_cast h𝓕_pos
      have h2 : r * 𝓕.card < 𝓕.card := by nlinarith
      have h3 : (𝓕'.card : ℝ) < 𝓕.card := lt_of_le_of_lt h1 h2
      have h4 : 𝓕'.card < 𝓕.card := by exact_mod_cast h3
      omega
    by_cases h𝓕'_empty : 𝓕' = ∅
    · -- All sets contain u, so {u} hits everything
      refine ⟨{u}, Finset.singleton_subset_iff.mpr hu_mem, ?_, ?_⟩
      · intros F hF
        rw [Finset.singleton_inter_of_mem]
        · exact Finset.singleton_nonempty u
        · by_contra hu'
          have : F ∈ 𝓕' := by simp only [Finset.mem_filter, 𝓕']; exact ⟨hF, hu'⟩
          simp [h𝓕'_empty] at this
      · simp only [Finset.card_singleton, Nat.cast_one]
        have h_log_nonneg : Real.log (𝓕.card : ℝ) ≥ 0 := by
          apply Real.log_nonneg; rw [hn]
          have : (1 : ℕ) ≤ k + 1 := by omega
          exact_mod_cast this
        have h_div_nonneg : Real.log (𝓕.card : ℝ) / Real.log (1 / r) ≥ 0 :=
          div_nonneg h_log_nonneg (le_of_lt h_log_denom_pos)
        have h_bound : Real.log (𝓕.card : ℝ) / Real.log (1 / r) + 1 ≥ 1 := by linarith
        -- Goal: 1 ≤ log ↑(k + 1) / log (1 / (1 - δ)) + 1
        -- Since 𝓕.card = k + 1 (from hn), log ↑(k + 1) ≥ 0 and div is nonneg
        have h_k1_pos : (0 : ℝ) < (k + 1 : ℕ) := by exact_mod_cast Nat.succ_pos k
        have h_log_k1 : Real.log ((k + 1 : ℕ) : ℝ) ≥ 0 := by
          apply Real.log_nonneg
          have : (1 : ℕ) ≤ k + 1 := by omega
          exact_mod_cast this
        have h_div' : Real.log ((k + 1 : ℕ) : ℝ) / Real.log (1 / (1 - δ)) ≥ 0 := by
          apply div_nonneg h_log_k1
          simp only [r] at h_log_denom_pos
          exact le_of_lt h_log_denom_pos
        linarith
    · -- Recurse on 𝓕'
      have h𝓕'_sub : ∀ F ∈ 𝓕', F ⊆ U := fun F hF => h𝓕_sub F (Finset.mem_filter.mp hF).1
      have hF'_size : ∀ F ∈ 𝓕', δ * U.card ≤ F.card :=
        fun F hF => hF_size F (Finset.mem_filter.mp hF).1
      have hU'_ne : 𝓕'.Nonempty → U.Nonempty := fun _ => hU_nonempty
      have h𝓕'_pos : 0 < 𝓕'.card :=
        Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr h𝓕'_empty)
      obtain ⟨H', hH'_sub, hH'_hits, hH'_bound⟩ :=
        ih 𝓕'.card h𝓕'_card_lt 𝓕' hU'_ne h𝓕'_sub hF'_size h𝓕'_empty h𝓕'_pos rfl
      refine ⟨insert u H', Finset.insert_subset hu_mem hH'_sub, ?_, ?_⟩
      · -- H hits all sets in 𝓕
        intros F hF
        by_cases hu_F : u ∈ F
        · exact ⟨u, Finset.mem_inter.mpr ⟨Finset.mem_insert_self u H', hu_F⟩⟩
        · have hF' : F ∈ 𝓕' := by simp only [Finset.mem_filter, 𝓕']; exact ⟨hF, hu_F⟩
          obtain ⟨x, hx⟩ := hH'_hits F hF'
          exact ⟨x, Finset.mem_inter.mpr ⟨Finset.mem_insert_of_mem (Finset.mem_inter.mp hx).1,
                                          (Finset.mem_inter.mp hx).2⟩⟩
      · -- The logarithmic bound: |insert u H'| ≤ log|𝓕|/log(1/r) + 1
        -- We have: |H'| ≤ log|𝓕'|/log(1/r) + 1
        -- And: |𝓕'| ≤ r|𝓕|
        -- So: log|𝓕'| ≤ log(r|𝓕|) = log r + log|𝓕|
        -- Thus: log|𝓕'|/log(1/r) ≤ (log r + log|𝓕|)/log(1/r)
        --     = log r / log(1/r) + log|𝓕|/log(1/r)
        --     = -1 + log|𝓕|/log(1/r)   [since log r / log(1/r) = log r / (-log r) = -1]
        -- Hence: |H'| ≤ -1 + log|𝓕|/log(1/r) + 1 = log|𝓕|/log(1/r)
        -- And: |insert u H'| ≤ |H'| + 1 ≤ log|𝓕|/log(1/r) + 1
        have h_insert_le : ((insert u H').card : ℝ) ≤ H'.card + 1 := by
          exact_mod_cast Finset.card_insert_le u H'
        have h𝓕'_pos : 0 < 𝓕'.card :=
          Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr h𝓕'_empty)
        have h𝓕_pos' : (0 : ℝ) < 𝓕.card := by rw [hn]; exact_mod_cast Nat.succ_pos k
        have h𝓕'_pos_real : (0 : ℝ) < 𝓕'.card := by exact_mod_cast h𝓕'_pos
        -- log|𝓕'| ≤ log(r|𝓕|) = log r + log|𝓕|
        have h_log_bound : Real.log 𝓕'.card ≤ Real.log r + Real.log 𝓕.card := by
          calc Real.log 𝓕'.card ≤ Real.log (r * 𝓕.card) := by
                apply Real.log_le_log h𝓕'_pos_real h𝓕'_bound
            _ = Real.log r + Real.log 𝓕.card := by
                rw [Real.log_mul (ne_of_gt hr_pos) (ne_of_gt h𝓕_pos')]
        -- log r / log(1/r) = -1
        -- Since 0 < r < 1, we have log r < 0
        have h_log_r_neg : Real.log r < 0 := Real.log_neg hr_pos hr_lt
        have h_log_ratio : Real.log r / Real.log (1 / r) = -1 := by
          rw [one_div, Real.log_inv, div_neg, div_self (ne_of_lt h_log_r_neg)]
        calc ((insert u H').card : ℝ) ≤ H'.card + 1 := h_insert_le
          _ ≤ (Real.log 𝓕'.card / Real.log (1 / r) + 1) + 1 := by linarith [hH'_bound]
          _ = Real.log 𝓕'.card / Real.log (1 / r) + 2 := by ring
          _ ≤ (Real.log r + Real.log 𝓕.card) / Real.log (1 / r) + 2 := by
              have h_div : Real.log 𝓕'.card / Real.log (1 / r) ≤
                  (Real.log r + Real.log 𝓕.card) / Real.log (1 / r) :=
                div_le_div_of_nonneg_right h_log_bound (le_of_lt h_log_denom_pos)
              linarith
          _ = Real.log r / Real.log (1 / r) + Real.log 𝓕.card / Real.log (1 / r) + 2 := by
              rw [add_div]
          _ = -1 + Real.log 𝓕.card / Real.log (1 / r) + 2 := by rw [h_log_ratio]
          _ = Real.log 𝓕.card / Real.log (1 / r) + 1 := by ring
          _ = Real.log ((k + 1 : ℕ) : ℝ) / Real.log (1 / (1 - δ)) + 1 := by rw [hn]

/-! ## Finite Dyadic Obstruction -/

/-- Lemma 4.1: For B ∈ 𝓑_N (dyadic N), |C_B| ≥ (1/2 - ε²)N -/
lemma C_card_lower_bound (N : ℕ) (hN : 8 ≤ N) (hN_even : Even N)
    (B : Finset ℕ) (hB : B ∈ 𝓑 N) :
    ((1 / 2 - epsilon ^ 2) * N : ℝ) ≤ (C B N).card := by
  simp only [𝓑, Finset.mem_filter, Finset.mem_powerset] at hB
  obtain ⟨hB_sub, hB_card⟩ := hB
  have h_sumset_card : (B + B).card ≤ B.card ^ 2 := by
    have h1 : (B + B).card ≤ B.card * B.card := Finset.card_add_le
    calc (B + B).card ≤ B.card * B.card := h1
      _ = B.card ^ 2 := (sq B.card).symm
  -- |S_B| ≤ |B+B| ≤ m²
  have h_S_card : (S B N).card ≤ (m N) ^ 2 := by
    calc (S B N).card ≤ (B + B).card := Finset.card_le_card Finset.inter_subset_left
      _ ≤ B.card ^ 2 := h_sumset_card
      _ ≤ (m N) ^ 2 := Nat.pow_le_pow_left hB_card 2
  have h_C_eq : (C B N).card = (J N).card - (S B N).card := by
    simp only [C]
    have h_sub : S B N ⊆ J N := by
      intro x hx
      simp only [S, Finset.mem_inter] at hx
      exact hx.2
    rw [Finset.card_sdiff_of_subset h_sub]
  -- |J_N| = N/2
  have hN_pos : 0 < N := by omega
  have h_J_card : (J N).card = N / 2 := J_card_eq_half N hN_even hN_pos
  -- m² ≤ ε²N
  have h_m_sq_bound : ((m N) ^ 2 : ℝ) ≤ epsilon ^ 2 * N := by
    have hm := m_le_sqrt N
    calc ((m N) ^ 2 : ℝ) = (m N : ℝ) ^ 2 := by norm_cast
      _ ≤ (epsilon * Real.sqrt N) ^ 2 := by
          apply sq_le_sq' _ hm
          calc -(epsilon * Real.sqrt N) ≤ 0 := by nlinarith [epsilon_pos, Real.sqrt_nonneg N]
            _ ≤ (m N : ℝ) := Nat.cast_nonneg _
      _ = epsilon ^ 2 * N := by
          rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg N)]
  -- Now the main calculation
  have h_half : (N / 2 : ℕ) = N / 2 := rfl
  calc (((1 : ℝ) / 2 - epsilon ^ 2) * N : ℝ)
      = N / 2 - epsilon ^ 2 * N := by ring
    _ ≤ N / 2 - (m N) ^ 2 := by linarith [h_m_sq_bound]
    _ ≤ (J N).card - (S B N).card := by
        rw [h_J_card]
        have h_div : ((N / 2 : ℕ) : ℝ) = (N : ℝ) / 2 := by
          have h_two_dvd : 2 ∣ N := even_iff_two_dvd.mp hN_even
          rw [Nat.cast_div h_two_dvd (by norm_num : (2 : ℝ) ≠ 0)]
          norm_num
        rw [← h_div]
        have h2 : ((m N) ^ 2 : ℝ) ≥ (S B N).card := by
          have : (S B N).card ≤ (m N) ^ 2 := h_S_card
          exact_mod_cast this
        linarith
    _ = (C B N).card := by
        have h_sub : S B N ⊆ J N := by
          intro x hx
          simp only [S, Finset.mem_inter] at hx
          exact hx.2
        rw [← Nat.cast_sub (Finset.card_le_card h_sub), h_C_eq]

/-- δ = 1 - 2ε² = 49/50 -/
def delta : ℝ := 1 - 2 * epsilon ^ 2

lemma delta_val : delta = 49 / 50 := by norm_num [delta, epsilon]

lemma delta_pos : delta > 0 := by rw [delta_val]; norm_num

lemma delta_le_one : delta ≤ 1 := by rw [delta_val]; norm_num

lemma delta_lt_one : delta < 1 := by rw [delta_val]; norm_num

/-- The family of complement sets {C_B : B ∈ 𝓑_N}. -/
def 𝓒 (N : ℕ) : Finset (Finset ℕ) := (𝓑 N).image (fun B => C B N)

/-- Lemma 4.2: Existence of finite hard set A_N ⊆ J_N for dyadic N.
    Also provides a logarithmic size bound from the hitting set theorem. -/
theorem exists_hard_set (N : ℕ) (hN : 8 ≤ N) (hN_even : Even N) :
    ∃ A_N : Finset ℕ, A_N ⊆ J N ∧
      (∀ B : Finset ℕ, B ⊆ Finset.Icc 0 N → B.card ≤ m N → ¬(A_N ⊆ B + B)) ∧
      ((A_N.card : ℝ) ≤ Real.log (𝓒 N).card / Real.log (1 / (1 - delta)) + 1) := by
  -- Each C_B ⊆ J_N
  have h𝓒_sub : ∀ F ∈ 𝓒 N, F ⊆ J N := by
    intros F hF
    simp only [𝓒, Finset.mem_image] at hF
    obtain ⟨B, _, hF_eq⟩ := hF
    rw [← hF_eq]
    exact Finset.sdiff_subset
  -- Each C_B has |C_B| ≥ δ|J_N|
  have hF_size : ∀ F ∈ 𝓒 N, delta * (J N).card ≤ F.card := by
    intros F hF
    simp only [𝓒, Finset.mem_image] at hF
    obtain ⟨B, hB, hF_eq⟩ := hF
    rw [← hF_eq]
    have h_lower := C_card_lower_bound N hN hN_even B hB
    -- (1/2 - ε²)N ≤ |C_B|
    -- Need: δ * |J_N| ≤ |C_B|
    -- δ = 49/50, |J_N| = N/2
    -- δ * N/2 = 49N/100 = (1/2 - 1/100)N
    have hN_pos : 0 < N := by omega
    have h_J_card : (J N).card = N / 2 := J_card_eq_half N hN_even hN_pos
    calc (delta * (J N).card : ℝ)
        = delta * ((N / 2 : ℕ) : ℝ) := by rw [h_J_card]
      _ = (49 / 50) * ((N / 2 : ℕ) : ℝ) := by rw [delta_val]
      _ = (49 / 50) * ((N : ℝ) / 2) := by
          congr 1
          have h_two_dvd : 2 ∣ N := even_iff_two_dvd.mp hN_even
          rw [Nat.cast_div h_two_dvd (by norm_num : (2 : ℝ) ≠ 0)]
          norm_num
      _ = 49 * N / 100 := by ring
      _ = (1 / 2 - 1 / 100) * N := by ring
      _ = (1 / 2 - epsilon ^ 2) * N := by rw [epsilon_sq]
      _ ≤ (C B N).card := h_lower
  -- J N is nonempty for N ≥ 8
  have hJ_nonempty : (J N).Nonempty := by
    have hN_pos : 0 < N := by omega
    have h_J_card : (J N).card = N / 2 := J_card_eq_half N hN_even hN_pos
    rw [← Finset.card_pos, h_J_card]
    omega
  have hU_ne : (𝓒 N).Nonempty → (J N).Nonempty := fun _ => hJ_nonempty
  -- Apply exists_hitting_set_log_bound to get H with logarithmic bound
  obtain ⟨H, hH_sub, hH_hits, hH_card⟩ :=
    exists_hitting_set_log_bound (J N) delta delta_pos delta_lt_one (𝓒 N) hU_ne h𝓒_sub hF_size
  refine ⟨H, hH_sub, ?_, hH_card⟩
  intros B hB_sub hB_card hA_sub
  -- H ⊆ B + B contradicts H hitting C_B
  have hB_mem : B ∈ 𝓑 N := by
    simp only [𝓑, Finset.mem_filter, Finset.mem_powerset]
    exact ⟨hB_sub, hB_card⟩
  have hC_mem : C B N ∈ 𝓒 N := by
    simp only [𝓒, Finset.mem_image]
    exact ⟨B, hB_mem, rfl⟩
  obtain ⟨x, hx⟩ := hH_hits (C B N) hC_mem
  rw [Finset.mem_inter] at hx
  -- x ∈ H and x ∈ C_B = J_N \ S_B
  have hx_H := hx.1
  have hx_C := hx.2
  -- C B N = J N \ S B N = J N \ ((B + B) ∩ J N)
  -- So x ∈ J N and x ∉ (B + B) ∩ J N
  simp only [C, Finset.mem_sdiff] at hx_C
  obtain ⟨hx_J, hx_not_S⟩ := hx_C
  -- hx_not_S : x ∉ S B N = (B + B) ∩ J N
  -- This means ¬(x ∈ B + B ∧ x ∈ J N)
  -- Since x ∈ J N (from hx_J), we must have x ∉ B + B
  have hx_not_sum : x ∉ B + B := by
    intro hx_in
    apply hx_not_S
    simp only [S, Finset.mem_inter]
    exact ⟨hx_in, hx_J⟩
  -- Since H = A_N ⊆ B + B, we have x ∈ B + B
  have hx_sum := hA_sub hx_H
  exact hx_not_sum hx_sum

/-- Bound on the size of the family 𝓒_N -/
lemma card_𝓒_le_card_𝓑 (N : ℕ) : (𝓒 N).card ≤ (𝓑 N).card := by
  calc (𝓒 N).card
      ≤ (𝓑 N).card := Finset.card_image_le

/-- Bound on the size of the family 𝓑_N.
    Trivial bound: |𝓑_N| ≤ 2^{N+1} since 𝓑_N ⊆ powerset([0,N]). -/
lemma card_𝓑_le_pow (N : ℕ) : (𝓑 N).card ≤ 2 ^ (N + 1) := by
  calc (𝓑 N).card
      ≤ ((Finset.Icc 0 N).powerset).card := by
          have : 𝓑 N ⊆ (Finset.Icc 0 N).powerset := by
            intros B hB
            simp only [𝓑, Finset.mem_filter, Finset.mem_powerset] at hB ⊢
            exact hB.1
          exact Finset.card_le_card this
    _ = 2 ^ (Finset.Icc 0 N).card := Finset.card_powerset (Finset.Icc 0 N)
    _ = 2 ^ (N + 1) := by
        congr 1
        rw [Nat.card_Icc]
        have : 0 ≤ N := Nat.zero_le N
        omega

/-! ## The Infinite Dyadic Construction -/

/-- Helper: 2^n ≥ 8 for n ≥ 3 -/
lemma two_pow_ge_eight (n : ℕ) (hn : 3 ≤ n) : 8 ≤ 2 ^ n := by
  calc 8 = 2 ^ 3 := by norm_num
    _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) hn

/-- Helper: 2^n is even for n ≥ 1 -/
lemma two_pow_even (n : ℕ) (hn : 1 ≤ n) : Even (2 ^ n) := by
  exact Even.pow_of_ne_zero (even_two) (Nat.one_le_iff_ne_zero.mp hn)

/-- For each dyadic N = 2^n with n ≥ 3, we have a hard set A_N ⊆ J_N.
    We use Classical.choose to select such a set. -/
def A_dyadic (n : ℕ) (hn : 3 ≤ n) : Finset ℕ :=
  Classical.choose (exists_hard_set (2^n) (two_pow_ge_eight n hn) (two_pow_even n (by omega)))

lemma A_dyadic_subset (n : ℕ) (hn : 3 ≤ n) : A_dyadic n hn ⊆ J (2^n) :=
  (Classical.choose_spec
    (exists_hard_set (2^n) (two_pow_ge_eight n hn) (two_pow_even n (by omega)))).1

lemma A_dyadic_hard (n : ℕ) (hn : 3 ≤ n) :
    ∀ B : Finset ℕ, B ⊆ Finset.Icc 0 (2^n) → B.card ≤ m (2^n) → ¬(A_dyadic n hn ⊆ B + B) :=
  (Classical.choose_spec
    (exists_hard_set (2^n) (two_pow_ge_eight n hn) (two_pow_even n (by omega)))).2.1

/-- Size bound on A_{2^n} from the hitting set theorem. -/
lemma A_dyadic_card_bound (n : ℕ) (hn : 3 ≤ n) :
    ((A_dyadic n hn).card : ℝ) ≤
      Real.log (𝓒 (2^n)).card / Real.log (1 / (1 - delta)) + 1 :=
  (Classical.choose_spec
    (exists_hard_set (2^n) (two_pow_ge_eight n hn) (two_pow_even n (by omega)))).2.2

/-- The infinite hard set A = ⋃_{n≥3} A_{2^n} as a Set ℕ. -/
def A : Set ℕ := {x | ∃ n : ℕ, ∃ hn : 3 ≤ n, x ∈ A_dyadic n hn}

/-- B(N) = |B ∩ [0,N]| -/
def countingFn (B : Set ℕ) (N : ℕ) : ℕ :=
  @Finset.card ℕ
    (@Finset.filter ℕ (fun x => x ∈ B) (Classical.decPred _) (Finset.Icc 0 N))

end

end Erdos333

attribute [local instance] Classical.propDecidable

theorem Erdos333.main_obstruction :
    And
      (@Filter.Tendsto.{0, 0} Nat Real
        (fun (N : Nat) ↦
          @HDiv.hDiv.{0, 0, 0} Real Real Real
            (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
            (@Nat.cast.{0} Real Real.instNatCast
              (@Finset.card.{0} Nat
                (@Finset.filter.{0} Nat
                  (fun (x : Nat) ↦
                    @Membership.mem.{0, 0} Nat (Set.{0} Nat) (@Set.instMembership.{0} Nat) Erdos333.A x)
                  (@Classical.decPred.{1} Nat fun (x : Nat) ↦
                    @Membership.mem.{0, 0} Nat (Set.{0} Nat) (@Set.instMembership.{0} Nat) Erdos333.A x)
                  (@Finset.Icc.{0} Nat Nat.instPreorder Nat.instLocallyFiniteOrder
                    (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) N))))
            (@Nat.cast.{0} Real Real.instNatCast N))
        (@Filter.atTop.{0} Nat Nat.instPreorder)
        (@nhds.{0} Real
          (@UniformSpace.toTopologicalSpace.{0} Real
            (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
          (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))))
      (Not
        (@Exists.{1} (Set.{0} Nat) fun (B : Set.{0} Nat) ↦
          And
            (@LE.le.{0} (Set.{0} Nat) (@Set.instLE.{0} Nat) Erdos333.A
              (@setOf.{0} Nat fun (x : Nat) ↦
                @Exists.{1} Nat fun (b : Nat) ↦
                  @Exists.{1} Nat fun (b' : Nat) ↦
                    And (@Membership.mem.{0, 0} Nat (Set.{0} Nat) (@Set.instMembership.{0} Nat) B b)
                      (And (@Membership.mem.{0, 0} Nat (Set.{0} Nat) (@Set.instMembership.{0} Nat) B b')
                        (@Eq.{1} Nat x
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) b b')))))
            (@Filter.Tendsto.{0, 0} Nat Real
              (fun (N : Nat) ↦
                @HDiv.hDiv.{0, 0, 0} Real Real Real
                  (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                  (@Nat.cast.{0} Real Real.instNatCast (Erdos333.countingFn B N))
                  (@Nat.cast.{0} Real Real.instNatCast N).sqrt)
              (@Filter.atTop.{0} Nat Nat.instPreorder)
              (@nhds.{0} Real
                (@UniformSpace.toTopologicalSpace.{0} Real
                  (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))))))
  := by
  sorry
