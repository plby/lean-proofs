/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos48.PowerSieveBadRoots

/-!
# From dyadic bad-root bounds to prefix sparsity

This file contains the purely combinatorial summation step needed after a
power-sieve estimate on every interval `(Q,2Q]`.  The intervals are indexed
by powers of two.  If the exceptional set is empty through `2^J₀` and its
`j`-th dyadic block has cardinality at most `c 2^j`, then every prefix has
cardinality at most `2 c y`.  In particular the statement can be used with
`c = 1 / Real.sqrt n` without any analytic hypotheses in this module.
-/

namespace Erdos48

open scoped BigOperators

noncomputable section

/-- The portion of `E` in the half-open dyadic block `(2^j,2^(j+1)]`. -/
noncomputable def powerSieveDyadicShell (E : Finset ℕ) (j : ℕ) : Finset ℕ := by
  classical
  exact E ∩ Finset.Ioc (2 ^ j) (2 ^ (j + 1))

theorem mem_powerSieveDyadicShell {E : Finset ℕ} {j q : ℕ} :
    q ∈ powerSieveDyadicShell E j ↔
      q ∈ E ∧ 2 ^ j < q ∧ q ≤ 2 ^ (j + 1) := by
  classical
  simp [powerSieveDyadicShell]

/-- Every element strictly above `2^J₀` and at most `y` lies in one of the
dyadic shells with index between `J₀` and `log₂ y`. -/
theorem powerSieve_prefix_subset_biUnion_dyadicShell
    {E : Finset ℕ} {J₀ y : ℕ}
    (hbelow : ∀ q ∈ E, q ≤ 2 ^ J₀ → False) :
    E.filter (fun q ↦ q ≤ y) ⊆
      (Finset.Icc J₀ (Nat.log 2 y)).biUnion (powerSieveDyadicShell E) := by
  classical
  intro q hq
  have hqData := Finset.mem_filter.mp hq
  have hqCut : 2 ^ J₀ < q := by
    exact lt_of_not_ge (fun h ↦ hbelow q hqData.1 h)
  have hqTwo : 2 ≤ q := by
    have hpowPos : 0 < 2 ^ J₀ := pow_pos (by omega) _
    omega
  have hsubPos : 0 < q - 1 := by omega
  let j : ℕ := Nat.log 2 (q - 1)
  have hjLowerPow : 2 ^ J₀ ≤ q - 1 := by omega
  have hjLower : J₀ ≤ j := by
    dsimp [j]
    exact Nat.le_log_of_pow_le (by omega) hjLowerPow
  have hsubY : q - 1 ≤ y := by omega
  have hjUpper : j ≤ Nat.log 2 y := by
    dsimp [j]
    exact Nat.log_mono_right hsubY
  have hjMem : j ∈ Finset.Icc J₀ (Nat.log 2 y) :=
    Finset.mem_Icc.mpr ⟨hjLower, hjUpper⟩
  rw [Finset.mem_biUnion]
  refine ⟨j, hjMem, ?_⟩
  rw [mem_powerSieveDyadicShell]
  refine ⟨hqData.1, ?_, ?_⟩
  · have hpow : 2 ^ j ≤ q - 1 := by
      dsimp [j]
      exact Nat.pow_log_le_self 2 hsubPos.ne'
    omega
  · have hlt : q - 1 < 2 ^ (j + 1) := by
      dsimp [j]
      exact Nat.lt_pow_succ_log_self (by omega) (q - 1)
    omega

/-- The powers of two indexed by an interval ending at `K` sum to at most
the next power of two. -/
theorem sum_pow_two_Icc_le_next (J₀ K : ℕ) :
    ∑ j ∈ Finset.Icc J₀ K, 2 ^ j ≤ 2 ^ (K + 1) := by
  have hlt : ∑ j ∈ Finset.Icc J₀ K, 2 ^ j < 2 ^ (K + 1) :=
    Nat.geomSum_lt (m := 2) (n := K + 1)
      (s := Finset.Icc J₀ K) (by norm_num) (by
        intro j hj
        exact Nat.lt_succ_of_le (Finset.mem_Icc.mp hj).2)
  exact hlt.le

/-- A uniform real-valued density bound on every power-of-two block gives
an explicit uniform prefix bound.  The constant is exactly `2`.

The hypothesis `hblock` is the bound
`|E ∩ (2^j,2^(j+1)]| ≤ c 2^j`; `hbelow` says that `E` is empty through the
lower cutoff `2^J₀`. -/
theorem card_filter_le_two_mul_of_dyadicShell_bounds
    {E : Finset ℕ} {J₀ : ℕ} {c : ℝ}
    (hc : 0 ≤ c)
    (hbelow : ∀ q ∈ E, q ≤ 2 ^ J₀ → False)
    (hblock : ∀ j : ℕ, J₀ ≤ j →
      ((powerSieveDyadicShell E j).card : ℝ) ≤
        c * ((2 ^ j : ℕ) : ℝ)) :
    ∀ y : ℕ,
      ((E.filter (fun q ↦ q ≤ y)).card : ℝ) ≤ 2 * c * (y : ℝ) := by
  classical
  intro y
  by_cases hy : y = 0
  · subst y
    have hempty : E.filter (fun q ↦ q ≤ 0) = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro q hqE hq
      have hqZero : q = 0 := Nat.le_zero.mp hq
      subst q
      exact hbelow 0 hqE (by positivity)
    rw [hempty]
    simp
  let K : ℕ := Nat.log 2 y
  let U : Finset ℕ :=
    (Finset.Icc J₀ K).biUnion (powerSieveDyadicShell E)
  have hsubset : E.filter (fun q ↦ q ≤ y) ⊆ U := by
    simpa only [K, U] using
      powerSieve_prefix_subset_biUnion_dyadicShell
        (E := E) (J₀ := J₀) (y := y) hbelow
  have hcardUnion : (U.card : ℝ) ≤
      ∑ j ∈ Finset.Icc J₀ K, ((powerSieveDyadicShell E j).card : ℝ) := by
    exact_mod_cast (Finset.card_biUnion_le :
      U.card ≤ ∑ j ∈ Finset.Icc J₀ K,
        (powerSieveDyadicShell E j).card)
  have hcardBlocks :
      (∑ j ∈ Finset.Icc J₀ K,
          ((powerSieveDyadicShell E j).card : ℝ)) ≤
        ∑ j ∈ Finset.Icc J₀ K, c * ((2 ^ j : ℕ) : ℝ) := by
    apply Finset.sum_le_sum
    intro j hj
    exact hblock j (Finset.mem_Icc.mp hj).1
  have hpows :
      (∑ j ∈ Finset.Icc J₀ K, (((2 ^ j : ℕ) : ℝ))) ≤
        ((2 ^ (K + 1) : ℕ) : ℝ) := by
    exact_mod_cast sum_pow_two_Icc_le_next J₀ K
  have hpowY : ((2 ^ (K + 1) : ℕ) : ℝ) ≤ 2 * (y : ℝ) := by
    have hlog := Nat.pow_log_le_self 2 hy
    have hnat : 2 ^ (K + 1) ≤ 2 * y := by
      dsimp [K]
      rw [pow_succ]
      simpa only [Nat.mul_comm] using Nat.mul_le_mul_left 2 hlog
    exact_mod_cast hnat
  calc
    ((E.filter (fun q ↦ q ≤ y)).card : ℝ) ≤ (U.card : ℝ) := by
      exact_mod_cast Finset.card_le_card hsubset
    _ ≤ ∑ j ∈ Finset.Icc J₀ K,
        ((powerSieveDyadicShell E j).card : ℝ) := hcardUnion
    _ ≤ ∑ j ∈ Finset.Icc J₀ K, c * ((2 ^ j : ℕ) : ℝ) := hcardBlocks
    _ = c * ∑ j ∈ Finset.Icc J₀ K, (((2 ^ j : ℕ) : ℝ)) := by
      rw [Finset.mul_sum]
    _ ≤ c * ((2 ^ (K + 1) : ℕ) : ℝ) :=
      mul_le_mul_of_nonneg_left hpows hc
    _ ≤ c * (2 * (y : ℝ)) := mul_le_mul_of_nonneg_left hpowY hc
    _ = 2 * c * (y : ℝ) := by ring

/-- The same aggregation theorem stated with an arbitrary advertised
constant `C ≥ 2`, convenient for downstream parameter packages. -/
theorem card_filter_le_C_mul_of_dyadicShell_bounds
    {E : Finset ℕ} {J₀ : ℕ} {c C : ℝ}
    (hc : 0 ≤ c) (hC : 2 ≤ C)
    (hbelow : ∀ q ∈ E, q ≤ 2 ^ J₀ → False)
    (hblock : ∀ j : ℕ, J₀ ≤ j →
      ((powerSieveDyadicShell E j).card : ℝ) ≤
        c * ((2 ^ j : ℕ) : ℝ)) :
    ∀ y : ℕ,
      ((E.filter (fun q ↦ q ≤ y)).card : ℝ) ≤ C * c * (y : ℝ) := by
  intro y
  refine (card_filter_le_two_mul_of_dyadicShell_bounds hc hbelow hblock y).trans ?_
  have hy : (0 : ℝ) ≤ y := by positivity
  nlinarith [mul_nonneg hc hy]

end

end Erdos48
