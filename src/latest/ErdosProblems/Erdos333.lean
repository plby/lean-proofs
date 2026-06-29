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

import Mathlib

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

/-- A_dyadic n is contained in the interval (2^{n-1}, 2^n]. -/
lemma A_dyadic_in_interval (n : ℕ) (hn : 3 ≤ n) :
    ∀ x ∈ A_dyadic n hn, 2^(n-1) < x ∧ x ≤ 2^n := by
  intros x hx
  have h_sub := A_dyadic_subset n hn
  have hx_J := h_sub hx
  simp only [J, Finset.mem_Ioc] at hx_J
  constructor
  · have h_div : 2 ^ n / 2 = 2 ^ (n - 1) := by
      rw [Nat.pow_div (by omega : 1 ≤ n) (by norm_num : 0 < 2)]
    rw [← h_div]
    exact hx_J.1
  · exact hx_J.2

/-! ## Density of A -/

/-- Helper: count of elements in A up to 2^n -/
def A_count (n : ℕ) : ℕ :=
  @Finset.card ℕ (@Finset.filter ℕ (fun x => x ∈ A) (Classical.decPred _) (Finset.Icc 0 (2^n)))

/-- Crude bound on |𝓑_N| -/
lemma card_𝓑_bound (N : ℕ) : (𝓑 N).card ≤ 2 ^ (N + 1) := by
  simp only [𝓑]
  calc (Finset.filter (fun B => B.card ≤ m N) (Finset.Icc 0 N).powerset).card
      ≤ (Finset.Icc 0 N).powerset.card := Finset.card_filter_le _ _
    _ = 2 ^ (Finset.Icc 0 N).card := by rw [Finset.card_powerset]
    _ = 2 ^ (N + 1) := by rw [Nat.card_Icc]; simp

/-- For dyadic N = 2^n, |A_{2^n}| ≤ |J(2^n)| = 2^{n-1} (trivial bound) -/
lemma A_dyadic_size_trivial_bound (n : ℕ) (hn : 3 ≤ n) :
    (A_dyadic n hn).card ≤ 2 ^ n / 2 := by
  have h_sub := A_dyadic_subset n hn
  have hN_even : Even (2 ^ n) := two_pow_even n (by omega)
  have hN_pos : 0 < 2 ^ n := Nat.pow_pos (by norm_num : 0 < 2)
  calc (A_dyadic n hn).card
      ≤ (J (2 ^ n)).card := Finset.card_le_card h_sub
    _ = 2 ^ n / 2 := J_card_eq_half (2 ^ n) hN_even hN_pos

/-- Key asymptotic fact: n / √(2^n) → 0 as n → ∞
    This follows from the fact that exponential growth dominates polynomial growth -/
lemma polynomial_over_exponential_tendsto_zero :
    Filter.Tendsto (fun n : ℕ => (n : ℝ) / Real.sqrt (2 ^ n))
      Filter.atTop (nhds 0) := by
  -- Use the Mathlib result that n^k / r^n → 0 when r > 1
  -- We have n / √(2^n) = n / 2^{n/2}, and 2^{1/2} = √2 > 1
  have h_sqrt_two_gt_one : (1 : ℝ) < Real.sqrt 2 := Real.one_lt_sqrt_two
  -- Rewrite √(2^n) = (√2)^n by induction
  have h_sqrt_pow : ∀ n : ℕ, Real.sqrt ((2 : ℝ) ^ n) = Real.sqrt 2 ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ, Real.sqrt_mul (by positivity), ih, pow_succ]
  -- Simplify the expression
  have h_eq : (fun n : ℕ => (n : ℝ) / Real.sqrt (2 ^ n)) =
              (fun n : ℕ => (n : ℝ) / (Real.sqrt 2 ^ n)) := by
    ext n
    congr 1
    calc Real.sqrt ((2 : ℕ) ^ n : ℝ)
        = Real.sqrt (((2 : ℕ) : ℝ) ^ n) := by
            have : ((2 : ℕ) ^ n : ℝ) = ((2 : ℕ) : ℝ) ^ n := by norm_cast
            rw [this]
      _ = Real.sqrt ((2 : ℝ) ^ n) := by rfl
      _ = Real.sqrt 2 ^ n := h_sqrt_pow n
  rw [h_eq]
  -- Now apply the standard asymptotic result
  have h_result := tendsto_pow_const_div_const_pow_of_one_lt 1 h_sqrt_two_gt_one
  simp only [pow_one] at h_result
  exact h_result

/-- Each A_{2^i} is finite and bounded in size by J(2^i).card = 2^{i-1} (trivial bound) -/
lemma A_dyadic_card_le (n : ℕ) (hn : 3 ≤ n) : (A_dyadic n hn).card ≤ 2^(n-1) := by
  have h := A_dyadic_subset n hn
  calc (A_dyadic n hn).card
      ≤ (J (2^n)).card := Finset.card_le_card h
    _ = 2^n - 2^n / 2 := by simp only [J]; rw [Nat.card_Ioc]
    _ = 2^n - 2^(n-1) := by rw [Nat.pow_div (by omega : 1 ≤ n) (by norm_num : 0 < 2)]
    _ = 2^(n-1) := by
        have h1 : 2^n = 2 * 2^(n-1) := by
          conv_lhs => rw [← Nat.sub_add_cancel (show 1 ≤ n by omega)]
          rw [Nat.pow_succ']
        omega

/-- Crude bound on log|𝓑_N|.
    We have |𝓑_N| = ∑_{i=0}^{m} C(N+1,i) where m = ⌊ε√N⌋.
    This is at most (m+1) · C(N+1, m) ≤ (m+1) · (N+1)^m.
    So log|𝓑_N| ≤ log(m+1) + m · log(N+1).
    With m ≤ ε√N, this is O(√N · log N). -/
lemma log_card_𝓑_bound (N : ℕ) (hN : 8 ≤ N) :
    Real.log (𝓑 N).card ≤ (m N + 1) * Real.log (N + 1) + Real.log (m N + 1) := by
  -- The family 𝓑_N consists of subsets of [0,N] with at most m elements
  have hN_pos : 0 < N := by omega
  have h𝓑_nonempty : (𝓑 N).Nonempty := by
    use ∅
    simp only [𝓑, Finset.mem_filter, Finset.mem_powerset, Finset.empty_subset,
               Finset.card_empty, true_and]
    exact Nat.zero_le _
  have h𝓑_pos : 0 < (𝓑 N).card := Finset.card_pos.mpr h𝓑_nonempty
  have h_base_card : (Finset.Icc 0 N).card = N + 1 := by rw [Nat.card_Icc]; omega
  -- Bound each binomial coefficient: C(n, k) ≤ n^k
  have h_choose_bound : ∀ k ≤ m N, (N + 1).choose k ≤ (N + 1) ^ (m N) := by
    intros k hk
    calc (N + 1).choose k ≤ (N + 1) ^ k := Nat.choose_le_pow (N + 1) k
      _ ≤ (N + 1) ^ (m N) := Nat.pow_le_pow_right (by omega : 1 ≤ N + 1) hk
  -- Bound |𝓑_N| ≤ (m+1) · (N+1)^m using sum of binomial coefficients
  have h_card_bound : (𝓑 N).card ≤ (m N + 1) * (N + 1) ^ (m N) := by
    -- 𝓑_N = {B ⊆ [0,N] : |B| ≤ m} = ⋃_{k=0}^{m} {B ⊆ [0,N] : |B| = k}
    -- |𝓑_N| = ∑_{k=0}^{m} C(N+1, k) ≤ (m+1) · (N+1)^m
    have h_eq : (𝓑 N).card = ∑ k ∈ Finset.range (m N + 1),
        (Finset.powersetCard k (Finset.Icc 0 N)).card := by
      simp only [𝓑]
      -- Group subsets by cardinality
      have h_union : (Finset.Icc 0 N).powerset.filter (fun B => B.card ≤ m N) =
          (Finset.range (m N + 1)).biUnion
            (fun k => Finset.powersetCard k (Finset.Icc 0 N)) := by
        ext B
        simp only [Finset.mem_filter, Finset.mem_biUnion, Finset.mem_range,
                   Finset.mem_powerset, Finset.mem_powersetCard]
        constructor
        · intro ⟨hB_sub, hB_card⟩
          exact ⟨B.card, Nat.lt_succ_of_le hB_card, hB_sub, rfl⟩
        · intro ⟨k, hk, hB_sub, hB_eq⟩
          exact ⟨hB_sub, by omega⟩
      rw [h_union]
      -- The biUnion is disjoint (subsets with different cardinalities are disjoint)
      have h_disj : Set.PairwiseDisjoint (Finset.range (m N + 1) : Set ℕ)
          (fun k => Finset.powersetCard k (Finset.Icc 0 N)) := by
        intro i _ j _ hij
        rw [Function.onFun]
        rw [Finset.disjoint_iff_ne]
        intros B hB_i C hC_j hBC
        rw [Finset.mem_powersetCard] at hB_i hC_j
        rw [hBC] at hB_i
        omega
      rw [Finset.card_biUnion h_disj]
    rw [h_eq]
    -- Each term |powersetCard k [0,N]| = C(N+1, k)
    have h_term : ∀ k ∈ Finset.range (m N + 1),
        (Finset.powersetCard k (Finset.Icc 0 N)).card = (N + 1).choose k := by
      intros k _
      rw [Finset.card_powersetCard, h_base_card]
    calc ∑ k ∈ Finset.range (m N + 1),
          (Finset.powersetCard k (Finset.Icc 0 N)).card
        = ∑ k ∈ Finset.range (m N + 1), (N + 1).choose k := by
            apply Finset.sum_congr rfl h_term
      _ ≤ ∑ _ ∈ Finset.range (m N + 1), (N + 1) ^ (m N) := by
            apply Finset.sum_le_sum
            intros k hk
            apply h_choose_bound k
            rw [Finset.mem_range] at hk
            omega
      _ = (m N + 1) * (N + 1) ^ (m N) := by
            rw [Finset.sum_const, Finset.card_range, smul_eq_mul]
  -- Take logarithms
  calc Real.log (𝓑 N).card
      ≤ Real.log ((m N + 1) * (N + 1) ^ (m N)) := by
        apply Real.log_le_log (by exact_mod_cast h𝓑_pos)
        exact_mod_cast h_card_bound
    _ = Real.log (m N + 1) + Real.log ((N + 1) ^ (m N)) := by
        rw [Real.log_mul (by positivity) (by positivity)]
    _ = Real.log (m N + 1) + (m N) * Real.log (N + 1) := by
        rw [Real.log_pow]
    _ ≤ (m N + 1) * Real.log (N + 1) + Real.log (m N + 1) := by
        -- log(m+1) + m * log(N+1) ≤ (m+1) * log(N+1) + log(m+1)
        -- This simplifies to: m * log(N+1) ≤ (m+1) * log(N+1)
        -- i.e., 0 ≤ log(N+1), which is true for N ≥ 1
        have h_log_pos : 0 ≤ Real.log (N + 1) := by
          apply Real.log_nonneg; exact_mod_cast (by omega : 1 ≤ N + 1)
        have hm_nonneg : (0 : ℝ) ≤ m N := Nat.cast_nonneg (m N)
        have hm1_nonneg : (0 : ℝ) ≤ (m N : ℝ) + 1 := by positivity
        nlinarith [mul_nonneg hm_nonneg h_log_pos, mul_nonneg hm1_nonneg h_log_pos]

/-- Bound on |A_{2^n}| using the logarithmic bound from the hitting set theorem.
    From exists_hitting_set_log_bound:
    |A_{2^n}| ≤ log|𝓒_{2^n}| / log(1/(1-δ)) + 1
             ≤ log|𝓑_{2^n}| / log(50) + 1
             ≤ C · n · 2^{n/2} for some constant C. -/
lemma A_dyadic_card_log_bound (n : ℕ) (hn : 3 ≤ n) :
    ((A_dyadic n hn).card : ℝ) ≤ Real.log (𝓒 (2^n)).card / Real.log 50 + 1 := by
  -- From A_dyadic_card_bound:
  -- |A_{2^n}| ≤ log|𝓒_{2^n}| / log(1/(1-δ)) + 1
  -- And 1/(1-δ) = 1/(1-49/50) = 50
  have h_log_eq : Real.log (1 / (1 - delta)) = Real.log 50 := by
    rw [delta_val]
    norm_num
  rw [← h_log_eq]
  exact A_dyadic_card_bound n hn

/-- `ε ≤ 1` for `ε = 1/10`. -/
lemma epsilon_le_one : epsilon ≤ 1 := by
  norm_num [epsilon]

/-- A very crude bound: `m(N) ≤ N` once `N ≥ 1`. -/
lemma m_le_self (N : ℕ) (hN : 1 ≤ N) : m N ≤ N := by
  -- Work in `ℝ` and then cast back.
  have hm : (m N : ℝ) ≤ epsilon * Real.sqrt N := m_le_sqrt N
  have hN_real : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hsqrt : Real.sqrt N ≤ (N : ℝ) := by
    -- `sqrt x ≤ x` for `x ≥ 1`: use `sqrt x ≤ x ↔ x ≤ x^2` for x ≥ 0, and x ≤ x^2 iff x ≥ 1.
    have h0 : (0 : ℝ) ≤ N := by positivity
    rw [Real.sqrt_le_iff]
    constructor
    · exact h0
    · nlinarith [hN_real]
  have h_eps_sqrt : epsilon * Real.sqrt N ≤ (N : ℝ) := by
    calc
      epsilon * Real.sqrt N ≤ 1 * Real.sqrt N := by
        have h0 : 0 ≤ Real.sqrt N := Real.sqrt_nonneg _
        nlinarith [epsilon_le_one, h0]
      _ = Real.sqrt N := by ring
      _ ≤ (N : ℝ) := hsqrt
  have hmN : (m N : ℝ) ≤ (N : ℝ) := le_trans hm h_eps_sqrt
  exact_mod_cast hmN

/-- A convenient logarithmic bound for dyadic arguments: `log(2^n + 1) ≤ (n+1) log 2`. -/
lemma log_two_pow_succ_bound (n : ℕ) :
    Real.log ((2 ^ n : ℕ) + 1) ≤ (n + 1) * Real.log 2 := by
  -- First show: `2^n + 1 ≤ 2^(n+1)`.
  have h_one_le : (1 : ℕ) ≤ 2 ^ n := by
    have : 0 < 2 ^ n := Nat.pow_pos (by norm_num : 0 < 2)
    exact Nat.succ_le_iff.mp this
  have h_le_nat : (2 ^ n : ℕ) + 1 ≤ 2 ^ (n + 1) := by
    have h' : (2 ^ n : ℕ) + 1 ≤ (2 ^ n : ℕ) + 2 ^ n :=
      Nat.add_le_add_left h_one_le (2 ^ n)
    -- Rewrite RHS as `2^(n+1)`.
    -- `2^(n+1) = 2^n * 2 = 2 * 2^n = 2^n + 2^n`.
    simpa [Nat.pow_succ, Nat.two_mul, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using h'
  have hpos : (0 : ℝ) < ((2 ^ n : ℕ) + 1 : ℝ) := by
    exact_mod_cast Nat.succ_pos (2 ^ n)
  have hlog_le : Real.log ((2 ^ n : ℕ) + 1) ≤ Real.log (2 ^ (n + 1) : ℕ) := by
    -- `Real.log` is monotone on `ℝ_{>0}`.
    exact Real.log_le_log hpos (by exact_mod_cast h_le_nat)
  -- Evaluate `log(2^(n+1))`.
  have hlog_pow : Real.log (2 ^ (n + 1) : ℕ) = (n + 1) * Real.log 2 := by
    -- Cast to `ℝ` and use `Real.log_pow`.
    -- `((2^(n+1) : ℕ) : ℝ) = (2 : ℝ)^(n+1)`.
    have : ((2 ^ (n + 1) : ℕ) : ℝ) = (2 : ℝ) ^ (n + 1) := by
      norm_cast
    -- Now `log((2:ℝ)^(n+1)) = (n+1) * log 2`.
    simp [this, Real.log_pow]
  exact le_trans hlog_le (by rw [hlog_pow])

/-- A uniform "dyadic block" cardinality upper bound:
`|A_{2^n}| ≤ C * (n+1) * sqrt(2^n)` for the explicit constant `C = ((ε+2) * log 2) / log 50 + 1`. -/
lemma A_dyadic_card_le_uniform (n : ℕ) (hn : 3 ≤ n) :
    ((A_dyadic n hn).card : ℝ) ≤
      (((epsilon + 2) * Real.log 2) / Real.log 50 + 1) * (n + 1) * Real.sqrt (2 ^ n) := by
  -- Start from the already-proved log hitting-set bound:
  have hA : ((A_dyadic n hn).card : ℝ) ≤ Real.log (𝓒 (2 ^ n)).card / Real.log 50 + 1 :=
    A_dyadic_card_log_bound n hn
  -- Bound `log |𝓒| ≤ log |𝓑|` using `card_𝓒_le_card_𝓑`.
  have hB_nonempty : (𝓑 (2 ^ n)).Nonempty := by
    refine ⟨∅, ?_⟩
    simp [𝓑]
  have hB_pos : 0 < (𝓑 (2 ^ n)).card := Finset.card_pos.mpr hB_nonempty
  have hC_pos : 0 < (𝓒 (2 ^ n)).card := by
    -- `𝓒` is an image of the nonempty `𝓑`.
    have : (𝓒 (2 ^ n)).Nonempty := by
      refine ⟨C ∅ (2 ^ n), ?_⟩
      simp only [𝓒, Finset.mem_image]
      refine ⟨∅, ?_, rfl⟩
      simp [𝓑]
    exact Finset.card_pos.mpr this
  have hlogC_le :
      Real.log (𝓒 (2 ^ n)).card ≤ Real.log (𝓑 (2 ^ n)).card := by
    apply Real.log_le_log (by exact_mod_cast hC_pos)
    exact_mod_cast card_𝓒_le_card_𝓑 (2 ^ n)
  -- Apply your crude binomial/log bound for `𝓑(2^n)`.
  have h8 : 8 ≤ 2 ^ n := two_pow_ge_eight n hn
  have hlogB_le :
      Real.log (𝓑 (2 ^ n)).card
        ≤ (m (2 ^ n) + 1) * Real.log ((2 ^ n : ℕ) + 1) + Real.log (m (2 ^ n) + 1) := by
    convert log_card_𝓑_bound (2 ^ n) h8
  -- Convert the last `log(m+1)` into a second `log(2^n+1)` using `m(2^n) ≤ 2^n`.
  have hm_le : m (2 ^ n) ≤ 2 ^ n := by
    -- `2^n ≥ 1` for all `n`.
    have h1 : 1 ≤ 2 ^ n := by
      have : 0 < 2 ^ n := by positivity
      omega
    exact m_le_self (2 ^ n) h1
  have hlogm_le :
      Real.log (m (2 ^ n) + 1) ≤ Real.log ((2 ^ n) + 1) := by
    have hpos : (0 : ℝ) < (m (2 ^ n) + 1 : ℝ) := by
      exact_mod_cast Nat.succ_pos (m (2 ^ n))
    apply Real.log_le_log hpos
    exact_mod_cast Nat.add_le_add_right hm_le 1
  -- Combine:
  have hlogB_le' :
      Real.log (𝓑 (2 ^ n)).card
        ≤ (m (2 ^ n) + 2) * Real.log ((2 ^ n : ℕ) + 1) := by
    -- `(m+1)*log + log(m+1) ≤ (m+1)*log + log(2^n+1) = (m+2)*log`.
    have hlog_nonneg : 0 ≤ Real.log ((2 ^ n : ℕ) + 1) := by
      apply Real.log_nonneg
      -- `1 ≤ 2^n + 1`
      exact_mod_cast (Nat.succ_le_succ (Nat.zero_le (2 ^ n)))
    have hm1 : (1 : ℝ) ≤ (m (2 ^ n) + 1 : ℝ) := by
      exact_mod_cast (Nat.succ_le_succ (Nat.zero_le (m (2 ^ n))))
    -- Now:
    calc
      Real.log (𝓑 (2 ^ n)).card
          ≤ (m (2 ^ n) + 1) * Real.log ((2 ^ n : ℕ) + 1) + Real.log (m (2 ^ n) + 1) := hlogB_le
      _ ≤ (m (2 ^ n) + 1) * Real.log ((2 ^ n : ℕ) + 1) + Real.log ((2 ^ n : ℕ) + 1) := by
            gcongr
      _ = (m (2 ^ n) + 2) * Real.log ((2 ^ n : ℕ) + 1) := by ring
  -- Bound `m(2^n)+2 ≤ (ε+2) * sqrt(2^n)` (using `sqrt(2^n) ≥ 1`).
  have hsqrt_ge_one : (1 : ℝ) ≤ Real.sqrt (2 ^ n) := by
    -- Since `1 ≤ 2^n`, and `sqrt` is monotone.
    have h1 : (1 : ℝ) ≤ (2 ^ n : ℝ) := by
      have : (1 : ℕ) ≤ 2 ^ n := by
        have : 0 < 2 ^ n := by positivity
        exact Nat.succ_le_iff.mp this
      exact_mod_cast this
    -- `sqrt 1 = 1` and `sqrt` monotone:
    have : Real.sqrt (1 : ℝ) ≤ Real.sqrt (2 ^ n : ℝ) := Real.sqrt_le_sqrt h1
    simpa using this
  have hm2_le :
      (m (2 ^ n) + 2 : ℝ) ≤ (epsilon + 2) * Real.sqrt (2 ^ n) := by
    have hm_real : (m (2 ^ n) : ℝ) ≤ epsilon * Real.sqrt ((2 ^ n : ℕ) : ℝ) := m_le_sqrt (2 ^ n)
    have hsqrt_eq : Real.sqrt ((2 ^ n : ℕ) : ℝ) = Real.sqrt (2 ^ n) := by norm_cast
    calc
      (m (2 ^ n) + 2 : ℝ) = (m (2 ^ n) : ℝ) + 2 := by norm_cast
      _ ≤ epsilon * Real.sqrt ((2 ^ n : ℕ) : ℝ) + 2 := by linarith
      _ = epsilon * Real.sqrt (2 ^ n) + 2 := by rw [hsqrt_eq]
      _ ≤ epsilon * Real.sqrt (2 ^ n) + 2 * Real.sqrt (2 ^ n) := by
            have h0 : 0 ≤ Real.sqrt (2 ^ n) := Real.sqrt_nonneg _
            nlinarith [hsqrt_ge_one]
      _ = (epsilon + 2) * Real.sqrt (2 ^ n) := by ring
  -- Bound `log(2^n+1) ≤ (n+1) log 2`.
  have hlog2n : Real.log ((2 ^ n : ℕ) + 1) ≤ (n + 1) * Real.log 2 := log_two_pow_succ_bound n
  -- Put everything together:
  have hlogC_final :
      Real.log (𝓒 (2 ^ n)).card ≤ ((epsilon + 2) * (n + 1) * Real.sqrt (2 ^ n)) * Real.log 2 := by
    calc
      Real.log (𝓒 (2 ^ n)).card
          ≤ Real.log (𝓑 (2 ^ n)).card := hlogC_le
      _ ≤ (m (2 ^ n) + 2) * Real.log ((2 ^ n : ℕ) + 1) := hlogB_le'
      _ ≤ ((epsilon + 2) * Real.sqrt (2 ^ n)) * ((n + 1) * Real.log 2) := by
            have h_log_nonneg : 0 ≤ Real.log ((2 ^ n : ℕ) + 1) := by
              apply Real.log_nonneg
              exact_mod_cast (Nat.succ_le_succ (Nat.zero_le (2 ^ n)))
            have h_eps_sqrt_nonneg : 0 ≤ (epsilon + 2) * Real.sqrt (2 ^ n) := by
              nlinarith [epsilon_pos, Real.sqrt_nonneg (2 ^ n : ℝ)]
            exact mul_le_mul hm2_le hlog2n h_log_nonneg h_eps_sqrt_nonneg
      _ = ((epsilon + 2) * (n + 1) * Real.sqrt (2 ^ n)) * Real.log 2 := by ring
  -- Finally go back to `|A_{2^n}|`.
  have hlog50_pos : 0 < Real.log 50 := by
    have : (1 : ℝ) < 50 := by norm_num
    exact Real.log_pos this
  have hsqrt_pos : 0 < Real.sqrt (2 ^ n : ℝ) := by
    have : (0 : ℝ) < (2 ^ n : ℝ) := by positivity
    exact Real.sqrt_pos.2 this
  -- Absorb the `+1` using `1 ≤ (n+1)*sqrt(2^n)`.
  have hone_le : (1 : ℝ) ≤ (n + 1 : ℝ) * Real.sqrt (2 ^ n) := by
    have hn1 : (1 : ℝ) ≤ (n + 1 : ℝ) := by
      exact_mod_cast (Nat.succ_le_succ (Nat.zero_le n))
    nlinarith [hn1, hsqrt_ge_one]
  -- Now algebra:
  calc
    ((A_dyadic n hn).card : ℝ)
        ≤ Real.log (𝓒 (2 ^ n)).card / Real.log 50 + 1 := hA
    _ ≤ (((epsilon + 2) * (n + 1) * Real.sqrt (2 ^ n)) * Real.log 2) / Real.log 50 + 1 := by
          gcongr
    _ = (((epsilon + 2) * Real.log 2) / Real.log 50) * (n + 1) * Real.sqrt (2 ^ n) + 1 := by
          ring
    _ ≤ ((((epsilon + 2) * Real.log 2) / Real.log 50) + 1) * (n + 1) * Real.sqrt (2 ^ n) := by
          -- use `1 ≤ (n+1)*sqrt(2^n)` to absorb `+1`
          nlinarith [hone_le]

/-- The set A has natural density 0. -/
theorem A_density_zero :
    Filter.Tendsto (fun N : ℕ => (@Finset.filter ℕ (fun x => x ∈ A) (Classical.decPred _)
      (Finset.Icc 0 N)).card / (N : ℝ)) Filter.atTop (nhds 0) := by
  classical
  -- We prove a stronger dyadic estimate and then pass to all `N` using `log₂`.
  rw [Metric.tendsto_atTop]
  intro ε hε
  -- Let `C` be the dyadic-block constant from `A_dyadic_card_le_uniform`.
  -- We only need one `C` (any positive one works).
  -- Take the explicit constant from the construction.
  let C := ((epsilon + 2) * Real.log 2) / Real.log 50 + 1
  have hCpos : 0 < C := by
    have hlog50 : 0 < Real.log 50 := by
      have : (1 : ℝ) < 50 := by norm_num
      exact Real.log_pos this
    have hlog2 : 0 < Real.log 2 := by
      have : (1 : ℝ) < 2 := by norm_num
      exact Real.log_pos this
    have heps2 : 0 < epsilon + 2 := by linarith [epsilon_pos]
    have : 0 ≤ ((epsilon + 2) * Real.log 2) / Real.log 50 := by
      have : 0 ≤ (epsilon + 2) * Real.log 2 := by
        nlinarith [le_of_lt heps2, le_of_lt hlog2]
      exact div_nonneg this (le_of_lt hlog50)
    linarith
  have hAblock : ∀ n : ℕ, ∀ hn : 3 ≤ n,
        ((A_dyadic n hn).card : ℝ) ≤ C * (n + 1) * Real.sqrt (2 ^ n) := by
    intro n hn
    -- A_dyadic_card_le_uniform now directly gives us the bound with the explicit C.
    exact A_dyadic_card_le_uniform n hn
  -- We will use the fact that `(n : ℝ)^2 / (sqrt 2)^n → 0`.
  have h_sqrt_two_gt_one : (1 : ℝ) < Real.sqrt 2 := Real.one_lt_sqrt_two
  have h_tendsto_sq :
      Filter.Tendsto (fun n : ℕ => (n : ℝ) ^ 2 / (Real.sqrt 2) ^ n)
        Filter.atTop (nhds 0) :=
    tendsto_pow_const_div_const_pow_of_one_lt 2 h_sqrt_two_gt_one
  -- Choose `k₀` so that for all `k ≥ k₀`, the dyadic density bound is `< ε/2`.
  -- We take a slightly overestimated coefficient `K := 4*C*sqrt 2`.
  let K : ℝ := 4 * C * Real.sqrt 2
  have hKpos : 0 < K := by nlinarith [hCpos, (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2))]
  -- Apply the tendsto statement to `ε / (2*K)`.
  have h_tendsto_sq' := h_tendsto_sq
  rw [Metric.tendsto_atTop] at h_tendsto_sq'
  have heps_div_pos : 0 < ε / (2 * K) := by positivity
  obtain ⟨k₀, hk₀⟩ := h_tendsto_sq' (ε / (2 * K)) heps_div_pos
  -- Now take `N₀ := 2^(k₀ + 3)` so that `log₂ N ≥ k₀` and also `N ≥ 8`.
  refine ⟨2 ^ (k₀ + 3), ?_⟩
  intro N hN
  rw [Real.dist_eq, sub_zero]
  have hNpos_prelim : (0 : ℝ) < (N : ℝ) := by
    have : 1 ≤ N := by
      have : 1 ≤ 2 ^ (k₀ + 3) := Nat.succ_le_iff.mp (Nat.pow_pos (by norm_num : 0 < 2))
      exact le_trans this hN
    exact_mod_cast (lt_of_lt_of_le (by norm_num : (0 : ℕ) < 1) this)
  rw [abs_of_nonneg (div_nonneg (by exact_mod_cast Nat.zero_le _) (le_of_lt hNpos_prelim))]
  -- From now on assume `N ≥ 1` so the division is well-defined and nonnegative.
  have hNpos : (0 : ℝ) < (N : ℝ) := by
    have : 1 ≤ N := by
      have : 1 ≤ 2 ^ (k₀ + 3) := by
        exact Nat.succ_le_iff.mp (Nat.pow_pos (by norm_num : 0 < 2))
      exact le_trans this hN
    exact_mod_cast (lt_of_lt_of_le (by norm_num : (0 : ℕ) < 1) this)
  -- Let `k := Nat.log 2 N`. Then `2^k ≤ N < 2^(k+1)`.
  set k : ℕ := Nat.log 2 N with hk_def
  have hk_lower : k₀ ≤ k := by
    -- monotonicity of `Nat.log` and the explicit evaluation on powers
    have hlog_mono : Nat.log 2 (2 ^ (k₀ + 3)) ≤ Nat.log 2 N :=
      Nat.log_mono_right (b := 2) hN
    -- `log_2(2^(k₀+3)) = k₀+3`
    have hlog_pow : Nat.log 2 (2 ^ (k₀ + 3)) = k₀ + 3 := by
      simp [Nat.log_pow (by norm_num : (1 : ℕ) < 2) (k₀ + 3)]
    -- so `k₀ + 3 ≤ k`
    have : k₀ + 3 ≤ k := by simpa [hk_def, hlog_pow] using hlog_mono
    exact le_trans (Nat.le_add_right k₀ 3) this
  -- We bound `|A ∩ [0,N]|` by the dyadic cutoff at `2^(k+1)`.
  have hN_lt_pow : N < 2 ^ (k + 1) := by
    -- standard `Nat.log` property
    simpa [hk_def] using (Nat.lt_pow_succ_log_self (b := 2) (by norm_num : (1 : ℕ) < 2) N)
  have hcard_mono :
      (@Finset.filter ℕ (fun x => x ∈ A) (Classical.decPred _) (Finset.Icc 0 N)).card
        ≤ (@Finset.filter ℕ (fun x => x ∈ A) (Classical.decPred _)
            (Finset.Icc 0 (2 ^ (k + 1)))).card := by
    -- monotonicity of `Icc` in the right endpoint
    have hIcc : Finset.Icc 0 N ⊆ Finset.Icc 0 (2 ^ (k + 1)) := by
      intro x hx
      exact Finset.mem_Icc.mpr
        ⟨(Finset.mem_Icc.mp hx).1, le_trans (Finset.mem_Icc.mp hx).2 (le_of_lt hN_lt_pow)⟩
    exact Finset.card_le_card (Finset.filter_subset_filter _ hIcc)
  -- Prove k ≥ 2 for use throughout (needs to be in scope for hdyadic_bound and later)
  have hk_ge_2 : 2 ≤ k := by
    have h8N : 8 ≤ N := by
      have h8pow : 8 ≤ 2 ^ (k₀ + 3) := by
        have : 3 ≤ k₀ + 3 := Nat.le_add_left 3 k₀
        have : 2 ^ 3 ≤ 2 ^ (k₀ + 3) := Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) this
        norm_num at this; exact this
      exact Nat.le_trans h8pow hN
    have hN_pos : N ≠ 0 := by omega
    have hpow_le : 2 ^ k ≤ N := by simpa [hk_def] using (Nat.pow_log_le_self 2 hN_pos)
    by_contra hbad
    have hk_lt : k < 2 := Nat.lt_of_not_ge hbad
    have : 2 ^ k < 2 ^ 2 := Nat.pow_lt_pow_right (by norm_num) hk_lt
    omega
  -- Now bound the dyadic truncated count by summing the disjoint blocks.
  have hdyadic_bound :
      ((@Finset.filter ℕ (fun x => x ∈ A) (Classical.decPred _)
          (Finset.Icc 0 (2 ^ (k + 1)))).card : ℝ)
        ≤ C * (k + 2) ^ 2 * Real.sqrt (2 ^ (k + 1)) := by
    let I : Finset ℕ := (Finset.Icc 3 (k + 1))
    have hI_nonempty : I.Nonempty := by
      refine ⟨3, ?_⟩
      exact Finset.mem_Icc.mpr ⟨le_rfl, Nat.succ_le_succ hk_ge_2⟩
    -- Upper bound by summing block sizes:
    have hsum :
        ((@Finset.filter ℕ (fun x => x ∈ A) (Classical.decPred _)
            (Finset.Icc 0 (2 ^ (k + 1)))).card : ℝ)
          ≤ ∑ n ∈ I, (C * (n + 1) * Real.sqrt (2 ^ n)) := by
      -- Define a helper to avoid proof issues in lambdas
      have h_mem_I_bound : ∀ n ∈ I, 3 ≤ n := by
        intro n hn
        simp only [I, Finset.mem_Icc] at hn
        exact hn.1
      have hsub :
          (@Finset.filter ℕ (fun x => x ∈ A) (Classical.decPred _) (Finset.Icc 0 (2 ^ (k + 1))))
            ⊆ I.biUnion (fun n => if h : 3 ≤ n then A_dyadic n h else ∅) := by
        intro x hx
        simp only [Finset.mem_filter, Finset.mem_Icc] at hx
        obtain ⟨⟨hx_lo, hx_hi⟩, hxA⟩ := hx
        rcases hxA with ⟨n, hn3, hxmem⟩
        have hx_interval := A_dyadic_in_interval n hn3 x hxmem
        have hn_le : n ≤ k + 1 := by
          by_contra hbad
          have hn_ge : k + 2 ≤ n := Nat.lt_of_not_ge hbad
          have hn3' : 3 ≤ n := hn3
          have hpow : 2 ^ (k + 1) ≤ 2 ^ (n - 1) := by
            have hn3' : 3 ≤ n := hn3
            have hn_ge' : k + 2 ≤ n := hn_ge
            have h_le : k + 1 ≤ n - 1 := by omega
            exact Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) h_le
          have hx_le : x ≤ 2 ^ (k + 1) := hx_hi
          have hx_le' : x ≤ 2 ^ (n - 1) := le_trans hx_le hpow
          exact lt_irrefl _ (lt_of_lt_of_le hx_interval.1 hx_le')
        have hn_memI : n ∈ I := by
          simp only [I, Finset.mem_Icc]
          exact ⟨hn3, hn_le⟩
        refine Finset.mem_biUnion.2 ?_
        refine ⟨n, hn_memI, ?_⟩
        simp only [hn3, dite_true]
        exact hxmem
      have hcard_le :
          ((@Finset.filter ℕ (fun x => x ∈ A) (Classical.decPred _)
              (Finset.Icc 0 (2 ^ (k + 1)))).card : ℝ)
            ≤ ((I.biUnion (fun n => if h : 3 ≤ n then A_dyadic n h else ∅)).card : ℝ) := by
        exact_mod_cast (Finset.card_le_card hsub)
      have hcard_biUnion :
          ((I.biUnion (fun n => if h : 3 ≤ n then A_dyadic n h else ∅)).card : ℝ)
            ≤ (∑ n ∈ I, (if h : 3 ≤ n then A_dyadic n h else ∅).card : ℝ) := by
        exact_mod_cast
          Finset.card_biUnion_le (s := I) (t := fun n => if h : 3 ≤ n then A_dyadic n h else ∅)
      have hsum_le :
          (∑ n ∈ I, (if h : 3 ≤ n then A_dyadic n h else ∅).card : ℝ)
            ≤ ∑ n ∈ I, (C * (n + 1) * Real.sqrt (2 ^ n)) := by
        apply Finset.sum_le_sum
        intro n hnI
        have hn3 : 3 ≤ n := h_mem_I_bound n hnI
        simp only [hn3, dite_true]
        have := hAblock n hn3
        simpa using this
      exact le_trans (le_trans hcard_le hcard_biUnion) hsum_le
    have hsum' :
        (∑ n ∈ I, (C * (n + 1) * Real.sqrt (2 ^ n)))
          ≤ (∑ _n ∈ I, (C * (k + 2) * Real.sqrt (2 ^ (k + 1)))) := by
      apply Finset.sum_le_sum
      intro n hnI
      have hn_le : n ≤ k + 1 := by
        have : n ∈ Finset.Icc 3 (k + 1) := hnI
        exact (Finset.mem_Icc.mp this).2
      have hn1_le : (n + 1 : ℝ) ≤ (k + 2 : ℝ) := by
        exact_mod_cast Nat.succ_le_succ hn_le
      have hsqrt_le : Real.sqrt (2 ^ n) ≤ Real.sqrt (2 ^ (k + 1)) := by
        apply Real.sqrt_le_sqrt
        exact_mod_cast (Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) hn_le)
      have hC0 : 0 ≤ C := le_of_lt hCpos
      have h0n : 0 ≤ Real.sqrt (2 ^ n) := Real.sqrt_nonneg _
      have h0k : 0 ≤ Real.sqrt (2 ^ (k + 1)) := Real.sqrt_nonneg _
      calc C * (↑n + 1) * Real.sqrt (2 ^ n)
          ≤ C * (↑k + 2) * Real.sqrt (2 ^ n) := by
            apply mul_le_mul_of_nonneg_right _ h0n
            apply mul_le_mul_of_nonneg_left hn1_le hC0
        _ ≤ C * (↑k + 2) * Real.sqrt (2 ^ (k + 1)) := by
            apply mul_le_mul_of_nonneg_left hsqrt_le
            apply mul_nonneg hC0
            positivity
    have hcardI : (I.card : ℝ) ≤ (k + 2 : ℝ) := by
      have hk2 : 2 ≤ k := hk_ge_2
      have hcard_eq : I.card = k - 1 := by
        simp only [I, Nat.card_Icc]
        omega
      have : I.card ≤ k + 2 := by
        rw [hcard_eq]
        omega
      exact_mod_cast this
    have hsum_const :
        (∑ _n ∈ I, (C * (k + 2) * Real.sqrt (2 ^ (k + 1))))
          = (I.card : ℝ) * (C * (k + 2) * Real.sqrt (2 ^ (k + 1))) := by
      simp [Finset.sum_const, mul_assoc, mul_comm]
    calc
      ((@Finset.filter ℕ (fun x => x ∈ A) (Classical.decPred _)
          (Finset.Icc 0 (2 ^ (k + 1)))).card : ℝ)
          ≤ ∑ n ∈ I, (C * (n + 1) * Real.sqrt (2 ^ n)) := hsum
      _ ≤ ∑ _n ∈ I, (C * (k + 2) * Real.sqrt (2 ^ (k + 1))) := hsum'
      _ = (I.card : ℝ) * (C * (k + 2) * Real.sqrt (2 ^ (k + 1))) := hsum_const
      _ ≤ (k + 2 : ℝ) * (C * (k + 2) * Real.sqrt (2 ^ (k + 1))) := by
            gcongr
      _ = C * (k + 2) ^ 2 * Real.sqrt (2 ^ (k + 1)) := by ring
  have hden_nonneg :
      0 ≤ (@Finset.filter ℕ (fun x => x ∈ A) (Classical.decPred _)
          (Finset.Icc 0 N)).card / (N : ℝ) :=
    div_nonneg (by exact_mod_cast Nat.zero_le _) (le_of_lt hNpos)
  have hN_ne_zero : N ≠ 0 := by
    have : (0 : ℝ) < N := hNpos
    exact_mod_cast this.ne'
  have hpow_le_N : 2 ^ k ≤ N := by
    simpa [hk_def] using (Nat.pow_log_le_self 2 hN_ne_zero)
  have hratio_le :
      (@Finset.filter ℕ (fun x => x ∈ A) (Classical.decPred _) (Finset.Icc 0 N)).card / (N : ℝ)
        ≤ (2 : ℝ) *
            ((@Finset.filter ℕ (fun x => x ∈ A) (Classical.decPred _)
                (Finset.Icc 0 (2 ^ (k + 1)))).card / (2 ^ (k + 1) : ℝ)) := by
    have ha : (@Finset.filter ℕ (fun x => x ∈ A) (Classical.decPred _) (Finset.Icc 0 N)).card
                ≤ (@Finset.filter ℕ (fun x => x ∈ A) (Classical.decPred _)
                    (Finset.Icc 0 (2 ^ (k + 1)))).card :=
      hcard_mono
    have hdiv1 :
        (@Finset.filter ℕ (fun x => x ∈ A) (Classical.decPred _) (Finset.Icc 0 N)).card / (N : ℝ)
          ≤ (@Finset.filter ℕ (fun x => x ∈ A) (Classical.decPred _)
              (Finset.Icc 0 (2 ^ (k + 1)))).card / (2 ^ k : ℝ) := by
      have hnum : ((@Finset.filter ℕ (fun x => x ∈ A) (Classical.decPred _)
          (Finset.Icc 0 N)).card : ℝ)
          ≤ (@Finset.filter ℕ (fun x => x ∈ A) (Classical.decPred _)
              (Finset.Icc 0 (2 ^ (k + 1)))).card := by
        exact_mod_cast ha
      have hden : (2 ^ k : ℝ) ≤ (N : ℝ) := by exact_mod_cast hpow_le_N
      have h2k_pos : (0 : ℝ) < (2 ^ k : ℝ) := by positivity
      have hN_pos' : (0 : ℝ) < (N : ℝ) := hNpos
      have h1 : ((@Finset.filter ℕ (fun x => x ∈ A) (Classical.decPred _)
          (Finset.Icc 0 N)).card : ℝ) / N
          ≤ ((@Finset.filter ℕ (fun x => x ∈ A) (Classical.decPred _)
              (Finset.Icc 0 N)).card : ℝ) / (2 ^ k : ℝ) := by
        apply div_le_div_of_nonneg_left _ h2k_pos hden
        exact_mod_cast Nat.zero_le _
      have h2 : ((@Finset.filter ℕ (fun x => x ∈ A) (Classical.decPred _)
          (Finset.Icc 0 N)).card : ℝ) / (2 ^ k : ℝ)
          ≤ ((@Finset.filter ℕ (fun x => x ∈ A) (Classical.decPred _)
              (Finset.Icc 0 (2 ^ (k + 1)))).card : ℝ) / (2 ^ k : ℝ) := by
        apply div_le_div_of_nonneg_right hnum h2k_pos.le
      exact le_trans h1 h2
    have hdiv2 :
        (@Finset.filter ℕ (fun x => x ∈ A) (Classical.decPred _)
            (Finset.Icc 0 (2 ^ (k + 1)))).card / (2 ^ k : ℝ)
          = (2 : ℝ) * ((@Finset.filter ℕ (fun x => x ∈ A) (Classical.decPred _)
              (Finset.Icc 0 (2 ^ (k + 1)))).card / (2 ^ (k + 1) : ℝ)) := by
      field_simp
      ring
    simpa [hdiv2] using hdiv1
  have hk₀' : |(k : ℝ) ^ 2 / (Real.sqrt 2) ^ k| < ε / (2 * K) := by
    have := hk₀ k hk_lower
    rwa [Real.dist_eq, sub_zero] at this
  have : (@Finset.filter ℕ (fun x => x ∈ A) (Classical.decPred _)
      (Finset.Icc 0 N)).card / (N : ℝ) < ε := by
    have hdy :
        ((@Finset.filter ℕ (fun x => x ∈ A) (Classical.decPred _)
            (Finset.Icc 0 (2 ^ (k + 1)))).card : ℝ)
          / (2 ^ (k + 1) : ℝ)
          ≤ (K : ℝ) * ((k : ℝ) ^ 2 / (Real.sqrt 2) ^ k) := by
      have hdy0 := hdyadic_bound
      have hpow_pos : (0 : ℝ) < (2 ^ (k + 1) : ℝ) := by positivity
      have : ((@Finset.filter ℕ (fun x => x ∈ A) (Classical.decPred _)
            (Finset.Icc 0 (2 ^ (k + 1)))).card : ℝ)
            / (2 ^ (k + 1) : ℝ)
          ≤ (C * (k + 2) ^ 2 * Real.sqrt (2 ^ (k + 1))) / (2 ^ (k + 1) : ℝ) := by
        exact div_le_div_of_nonneg_right hdy0 (le_of_lt hpow_pos)
      have hk2_le : ((k + 2 : ℝ) ^ 2) ≤ 4 * (k : ℝ) ^ 2 := by
        have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast hk_ge_2
        nlinarith [sq_nonneg (k : ℝ), hk2]
      have hsqrt2_pos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2)
      have hC0 : 0 ≤ C := le_of_lt hCpos
      have hk_real : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
      have hsqrt2k_pos : 0 < Real.sqrt 2 ^ k := pow_pos hsqrt2_pos k
      -- Key identity: sqrt(2^(k+1)) / 2^(k+1) = 1 / sqrt(2^(k+1))
      have h_ratio :
          Real.sqrt ((2 : ℝ) ^ (k + 1)) / (2 ^ (k + 1) : ℝ) = 1 / Real.sqrt (2 ^ (k + 1)) := by
        rw [div_eq_div_iff (by positivity) (by positivity)]
        rw [one_mul]
        have hsq : Real.sqrt ((2 : ℝ) ^ (k + 1)) * Real.sqrt ((2 : ℝ) ^ (k + 1)) =
                   Real.sqrt ((2 : ℝ) ^ (k + 1)) ^ 2 := by ring
        rw [hsq, Real.sq_sqrt (by positivity)]
      have h_sqrt_pow : Real.sqrt ((2 : ℝ) ^ (k + 1)) = Real.sqrt 2 ^ (k + 1) := by
        induction (k + 1) with
        | zero => simp
        | succ n ih =>
          rw [pow_succ, Real.sqrt_mul (by positivity), ih, pow_succ]
      have h_bound : (C * (k + 2) ^ 2 * Real.sqrt (2 ^ (k + 1))) / (2 ^ (k + 1) : ℝ)
                   ≤ K * (k ^ 2 / Real.sqrt 2 ^ k) := by
        have h2k1_pos : (0 : ℝ) < 2 ^ (k + 1) := by positivity
        have hsqrt2k1_pos : 0 < Real.sqrt (2 ^ (k + 1)) := Real.sqrt_pos.mpr h2k1_pos
        -- Direct proof using nlinarith with the algebraic bounds
        -- We need: C * (k + 2)^2 * sqrt(2^(k+1)) / 2^(k+1) ≤ K * k^2 / sqrt(2)^k
        -- Equivalently: C * (k + 2)^2 * sqrt(2^(k+1)) * sqrt(2)^k ≤ K * k^2 * 2^(k+1)
        have h1 : C * (k + 2) ^ 2 ≤ C * (4 * k ^ 2) := by
          apply mul_le_mul_of_nonneg_left hk2_le hC0
        have h2 : C * (4 * k ^ 2) * Real.sqrt 2 ^ (2 * k + 1) ≤ K * k ^ 2 * (2 : ℝ) ^ (k + 1) := by
          -- sqrt(2)^(2k+1) = 2^k * sqrt(2)
          have hsq2 : Real.sqrt 2 ^ (2 * k + 1) = (2 : ℝ) ^ k * Real.sqrt 2 := by
            rw [pow_add, pow_mul, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), pow_one]
          rw [hsq2]
          have hpow : (2 : ℝ) ^ (k + 1) = 2 * 2 ^ k := by ring
          rw [hpow]
          have h2k_pos : (0 : ℝ) < 2 ^ k := by positivity
          have hk2_nonneg : 0 ≤ k ^ 2 := sq_nonneg _
          -- K = 4 * C * sqrt(2), so K * k^2 * (2 * 2^k) = 4 * C * sqrt(2) * k^2 * 2 * 2^k
          -- LHS = C * 4 * k^2 * 2^k * sqrt(2)
          -- RHS = 4 * C * sqrt(2) * k^2 * 2 * 2^k
          -- LHS / RHS = (C * 4 * k^2 * 2^k * sqrt(2)) / (4 * C * sqrt(2) * k^2 * 2 * 2^k) = 1/2 ≤ 1
          have hK_def : K = 4 * C * Real.sqrt 2 := rfl
          calc C * (4 * k ^ 2) * (2 ^ k * Real.sqrt 2)
              = 4 * C * Real.sqrt 2 * k ^ 2 * 2 ^ k := by ring
            _ ≤ 4 * C * Real.sqrt 2 * k ^ 2 * (2 * 2 ^ k) := by
                have h_le : (2 : ℝ) ^ k ≤ 2 * 2 ^ k :=
                  le_mul_of_one_le_left (le_of_lt h2k_pos) one_le_two
                have h_coef : 0 ≤ 4 * C * Real.sqrt 2 * k ^ 2 := by
                  apply mul_nonneg
                  · exact mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hC0)
                      (le_of_lt hsqrt2_pos)
                  · exact sq_nonneg _
                exact mul_le_mul_of_nonneg_left h_le h_coef
            _ = K * k ^ 2 * (2 * 2 ^ k) := by rw [hK_def]
        have hsqrt_prod :
            Real.sqrt ((2 : ℝ) ^ (k + 1)) * Real.sqrt 2 ^ k = Real.sqrt 2 ^ (2 * k + 1) := by
          rw [h_sqrt_pow]
          have heq : Real.sqrt 2 ^ (k + 1) * Real.sqrt 2 ^ k = Real.sqrt 2 ^ (k + 1 + k) := by
            rw [← pow_add]
          rw [heq]
          congr 1
          omega
        have h_lhs_bound :
            C * (k + 2) ^ 2 * Real.sqrt 2 ^ (2 * k + 1) ≤ K * k ^ 2 * (2 : ℝ) ^ (k + 1) := by
          calc C * (k + 2) ^ 2 * Real.sqrt 2 ^ (2 * k + 1)
              ≤ C * (4 * k ^ 2) * Real.sqrt 2 ^ (2 * k + 1) := by
                have hpow_pos : 0 ≤ Real.sqrt 2 ^ (2 * k + 1) :=
                  le_of_lt (pow_pos hsqrt2_pos (2 * k + 1))
                exact mul_le_mul_of_nonneg_right h1 hpow_pos
            _ ≤ K * k ^ 2 * (2 : ℝ) ^ (k + 1) := h2
        -- Now connect to the original goal
        rw [div_le_iff₀ h2k1_pos]
        calc C * (k + 2) ^ 2 * Real.sqrt (2 ^ (k + 1))
            = C * (k + 2) ^ 2 * Real.sqrt 2 ^ (k + 1) := by rw [h_sqrt_pow]
          _ ≤ K * (k ^ 2 / Real.sqrt 2 ^ k) * 2 ^ (k + 1) := by
              have h_expand : K * (k ^ 2 / Real.sqrt 2 ^ k) * 2 ^ (k + 1) =
                  K * k ^ 2 * (2 : ℝ) ^ (k + 1) / Real.sqrt 2 ^ k := by
                field_simp
              rw [h_expand, le_div_iff₀ hsqrt2k_pos]
              have hpow_sum :
                  Real.sqrt 2 ^ (k + 1) * Real.sqrt 2 ^ k = Real.sqrt 2 ^ (k + 1 + k) := by
                rw [← pow_add]
              have hexp_eq : k + 1 + k = 2 * k + 1 := by omega
              calc C * (k + 2) ^ 2 * Real.sqrt 2 ^ (k + 1) * Real.sqrt 2 ^ k
                  = C * (k + 2) ^ 2 * (Real.sqrt 2 ^ (k + 1) * Real.sqrt 2 ^ k) := by ring
                _ = C * (k + 2) ^ 2 * Real.sqrt 2 ^ (k + 1 + k) := by rw [hpow_sum]
                _ = C * (k + 2) ^ 2 * Real.sqrt 2 ^ (2 * k + 1) := by rw [hexp_eq]
                _ ≤ K * k ^ 2 * (2 : ℝ) ^ (k + 1) := h_lhs_bound
      exact le_trans this h_bound
    have habs : (k : ℝ) ^ 2 / (Real.sqrt 2) ^ k < ε / (2 * K) := by
      have hnonneg : 0 ≤ (k : ℝ) ^ 2 / (Real.sqrt 2) ^ k := by
        have : 0 ≤ (k : ℝ) ^ 2 := sq_nonneg _
        have : 0 < (Real.sqrt 2) ^ k := by
          have : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2)
          exact pow_pos this k
        exact div_nonneg (sq_nonneg _) (le_of_lt this)
      simpa [abs_of_nonneg hnonneg] using hk₀'
    have hmain :
        (@Finset.filter ℕ (fun x => x ∈ A) (Classical.decPred _) (Finset.Icc 0 N)).card / (N : ℝ)
          ≤ (2 : ℝ) *
              ((@Finset.filter ℕ (fun x => x ∈ A) (Classical.decPred _)
                  (Finset.Icc 0 (2 ^ (k + 1)))).card / (2 ^ (k + 1) : ℝ)) := hratio_le
    have : (2 : ℝ) * ((@Finset.filter ℕ (fun x => x ∈ A) (Classical.decPred _)
                (Finset.Icc 0 (2 ^ (k + 1)))).card / (2 ^ (k + 1) : ℝ))
          < ε := by
      -- From hdy: card / 2^(k+1) ≤ K * (k² / √2^k)
      -- From habs: k² / √2^k < ε / (2 * K)
      -- So: card / 2^(k+1) < K * (ε / (2 * K)) = ε / 2 * (K / K) = ε / 2 (when K > 0)
      -- Hence: 2 * (card / 2^(k+1)) < ε
      have h_card_bound : ((@Finset.filter ℕ (fun x => x ∈ A) (Classical.decPred _)
                (Finset.Icc 0 (2 ^ (k + 1)))).card : ℝ) / (2 ^ (k + 1) : ℝ)
            < ε / 2 := by
        have h1 : K * ((k : ℝ) ^ 2 / (Real.sqrt 2) ^ k) < K * (ε / (2 * K)) := by
          apply mul_lt_mul_of_pos_left habs hKpos
        have h2 : K * (ε / (2 * K)) = ε / 2 := by field_simp
        calc ((@Finset.filter ℕ (fun x => x ∈ A) (Classical.decPred _)
                  (Finset.Icc 0 (2 ^ (k + 1)))).card : ℝ) / (2 ^ (k + 1) : ℝ)
            ≤ K * ((k : ℝ) ^ 2 / (Real.sqrt 2) ^ k) := hdy
          _ < K * (ε / (2 * K)) := h1
          _ = ε / 2 := h2
      linarith
    exact lt_of_le_of_lt hmain this
  exact this

/-! ## Main Theorem -/

/-- B(N) = |B ∩ [0,N]| -/
def countingFn (B : Set ℕ) (N : ℕ) : ℕ :=
  @Finset.card ℕ (@Finset.filter ℕ (fun x => x ∈ B) (Classical.decPred _) (Finset.Icc 0 N))

/-- Sum representation for elements of A -/
lemma A_covered_by_B_implies_local
    (B : Set ℕ) (hA_sub : A ⊆ {x | ∃ b b' : ℕ, b ∈ B ∧ b' ∈ B ∧ x = b + b'})
    (n : ℕ) (hn : 3 ≤ n) (a : ℕ) (ha : a ∈ A_dyadic n hn) :
    ∃ b b' : ℕ, b ∈ B ∧ b' ∈ B ∧ b ≤ a ∧ b' ≤ a ∧ a = b + b' := by
  have ha_A : a ∈ A := ⟨n, hn, ha⟩
  obtain ⟨b, b', hb, hb', hab⟩ := hA_sub ha_A
  have ha_pos : 0 < a := by
    have := (A_dyadic_in_interval n hn a ha).1
    have h2n : 0 < 2^(n-1) := Nat.pow_pos (by norm_num : 0 < 2)
    omega
  have hb_le : b ≤ a := by omega
  have hb'_le : b' ≤ a := by omega
  exact ⟨b, b', hb, hb', hb_le, hb'_le, hab⟩

/-- Main Theorem: There exists a set A ⊆ ℕ of density 0 such that
    no B with A ⊆ B+B can have |B ∩ [0,N]| = o(√N).
    This negatively answers Erdős Problem 333. -/
theorem main_obstruction :
    (Filter.Tendsto (fun N : ℕ => (@Finset.filter ℕ (fun x => x ∈ A) (Classical.decPred _)
      (Finset.Icc 0 N)).card / (N : ℝ)) Filter.atTop (nhds 0)) ∧
    ¬∃ B : Set ℕ, (A ⊆ {x | ∃ b b' : ℕ, b ∈ B ∧ b' ∈ B ∧ x = b + b'}) ∧
      Filter.Tendsto (fun N : ℕ => (countingFn B N : ℝ) / Real.sqrt N)
        Filter.atTop (nhds 0) := by
  constructor
  · exact A_density_zero
  · intro ⟨B, hA_sub, hB_subroot⟩
    -- Since B(N)/√N → 0, there exists N₀ such that for all N ≥ N₀, B(N) ≤ ε√N
    rw [Metric.tendsto_atTop] at hB_subroot
    obtain ⟨N₀, hN₀⟩ := hB_subroot epsilon epsilon_pos
    -- Choose n so large that 2^n ≥ max(N₀, 8)
    set n := max 3 (Nat.clog 2 (N₀ + 1)) with hn_def
    have hn : 3 ≤ n := le_max_left 3 _
    have hn_ge_N₀ : N₀ ≤ 2^n := by
      have h_clog : N₀ + 1 ≤ 2^(Nat.clog 2 (N₀ + 1)) :=
        Nat.le_pow_clog (by norm_num : 1 < 2) (N₀ + 1)
      have h_le : N₀ < 2^(Nat.clog 2 (N₀ + 1)) := by omega
      have h_le2 : 2^(Nat.clog 2 (N₀ + 1)) ≤ 2^n :=
        Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) (le_max_right 3 _)
      omega
    have hn_large : 8 ≤ 2^n := two_pow_ge_eight n hn
    set N := 2^n with hN_def
    -- B(N) ≤ ε√N, so |B ∩ [0,N]| ≤ m(N)
    have hBN_bound : countingFn B N ≤ m N := by
      have hN_ge : N ≥ N₀ := hn_ge_N₀
      have h := hN₀ N hN_ge
      simp only [Real.dist_eq, sub_zero] at h
      have h_abs : |((countingFn B N : ℝ) / Real.sqrt N)| < epsilon := h
      rw [abs_lt] at h_abs
      have h_sqrt_pos : Real.sqrt N > 0 := Real.sqrt_pos.mpr (by positivity : (N : ℝ) > 0)
      have h_lt : (countingFn B N : ℝ) / Real.sqrt N < epsilon := h_abs.2
      have h_ineq : (countingFn B N : ℝ) < epsilon * Real.sqrt N := by
        calc (countingFn B N : ℝ) = (countingFn B N / Real.sqrt N) * Real.sqrt N := by field_simp
          _ < epsilon * Real.sqrt N := mul_lt_mul_of_pos_right h_lt h_sqrt_pos
      have h_floor : countingFn B N ≤ ⌊epsilon * Real.sqrt N⌋₊ := Nat.le_floor (le_of_lt h_ineq)
      exact h_floor
    -- Let B_N = B ∩ [0,N] as a Finset
    let B_N : Finset ℕ :=
      @Finset.filter ℕ (fun x => x ∈ B) (Classical.decPred _) (Finset.Icc 0 N)
    have hB_N_sub : B_N ⊆ Finset.Icc 0 N :=
      @Finset.filter_subset ℕ (fun x => x ∈ B) (Classical.decPred _) (Finset.Icc 0 N)
    have hB_N_card : B_N.card = countingFn B N := rfl
    have hB_N_card_le : B_N.card ≤ m N := by rw [hB_N_card]; exact hBN_bound
    -- A_dyadic n ⊆ A
    have hA_dyadic_sub : ∀ x ∈ A_dyadic n hn, x ∈ A := fun x hx => ⟨n, hn, hx⟩
    -- For any a ∈ A_dyadic n, a ∈ A, so a = b + b' for some b, b' ∈ B
    -- Since a ≤ 2^n and b, b' ≤ a, we have b, b' ∈ [0, 2^n], so b, b' ∈ B_N
    have hA_dyadic_in_sum : A_dyadic n hn ⊆ B_N + B_N := by
      intros a ha
      obtain ⟨b, b', hb, hb', hb_le, hb'_le, hab⟩ := A_covered_by_B_implies_local B hA_sub n hn a ha
      have ha_interval := A_dyadic_in_interval n hn a ha
      have ha_le_N : a ≤ N := ha_interval.2
      -- Key: from a = b + b' with b, b' ∈ ℕ and b, b' ≤ a ≤ N,
      -- we get b, b' ∈ [0,N], so b, b' ∈ B_N = B ∩ [0,N]
      have hb_in_range : b ∈ Finset.Icc 0 N := by
        simp only [Finset.mem_Icc]
        exact ⟨Nat.zero_le b, Nat.le_trans hb_le ha_le_N⟩
      have hb'_in_range : b' ∈ Finset.Icc 0 N := by
        simp only [Finset.mem_Icc]
        exact ⟨Nat.zero_le b', Nat.le_trans hb'_le ha_le_N⟩
      have hb_in_B_N : b ∈ B_N := by
        simp only [B_N, Finset.mem_filter, hb_in_range, hb, and_self]
      have hb'_in_B_N : b' ∈ B_N := by
        simp only [B_N, Finset.mem_filter, hb'_in_range, hb', and_self]
      rw [hab]
      exact Finset.add_mem_add hb_in_B_N hb'_in_B_N
    -- But A_dyadic n is hard: no B ⊆ [0,N] with |B| ≤ m(N) can have A_dyadic n ⊆ B + B
    have h_hard := A_dyadic_hard n hn B_N hB_N_sub hB_N_card_le
    exact h_hard hA_dyadic_in_sum

end

#print axioms main_obstruction
-- 'Erdos333.main_obstruction' depends on axioms: [propext, Classical.choice, Quot.sound]

end Erdos333
