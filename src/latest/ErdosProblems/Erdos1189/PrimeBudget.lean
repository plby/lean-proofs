/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Choosing the last prime block below a prescribed cardinality budget.
Informal source: Section 6 of Pickhardt and Omniscience Research Agent.
Formal author: OpenAI Codex.
-/

import ErdosProblems.Erdos1189.PrimeWeights

namespace Erdos1189

open Finset

lemma primeWeightPrefix_ge_index (s : ℕ) : s ≤ primeWeightPrefix s := by
  calc
    s = ∑ i ∈ range s, 1 := by simp
    _ ≤ primeWeightPrefix s := sum_le_sum fun i _ => by
      have := (primeAt_prime i).two_le
      omega

lemma primeWeightSum_primeAt (s : ℕ) : primeWeightSum (primeAt s) = primeWeightPrefix (s + 1) := by
  rw [primeWeightSum_eq_prefix]
  congr 1
  exact Nat.count_nth_succ_of_infinite Nat.infinite_setOfPred_prime s

lemma primeWeightSum_mono : Monotone primeWeightSum := by
  intro x y hxy
  apply sum_le_sum_of_subset_of_nonneg
  · intro p hp
    exact Nat.mem_primesLE.mpr ⟨(Nat.le_of_mem_primesLE hp).trans hxy, Nat.prime_of_mem_primesLE hp⟩
  · exact fun _ _ _ => Nat.zero_le _

lemma primeWeightSum_le_square (P : ℕ) : primeWeightSum P ≤ P ^ 2 := by
  have hcard : (Nat.primesLE P).card ≤ P := by
    have hsub : Nat.primesLE P ⊆ Icc 1 P := by
      intro p hp
      exact mem_Icc.mpr ⟨(Nat.prime_of_mem_primesLE hp).one_le, Nat.le_of_mem_primesLE hp⟩
    simpa using card_le_card hsub
  calc
    primeWeightSum P ≤ ∑ p ∈ Nat.primesLE P, P := sum_le_sum fun p hp =>
      (Nat.sub_le p 1).trans (Nat.le_of_mem_primesLE hp)
    _ = (Nat.primesLE P).card * P := by simp
    _ ≤ P * P := Nat.mul_le_mul_right P hcard
    _ = P ^ 2 := by ring

lemma prime_sub_one_le_weight {P : ℕ} (hP : P.Prime) : P - 1 ≤ primeWeightSum P :=
  single_le_sum (fun p _ => Nat.zero_le (p - 1)) (Nat.mem_primesLE.mpr ⟨le_rfl, hP⟩)

/-- The unused budget after the last full prime block is less than `2P`. -/
theorem exists_prime_budget {k : ℕ} (hk : 2 ≤ k) :
    ∃ P, P.Prime ∧ primeWeightSum P + 1 ≤ k ∧
      k - 1 - primeWeightSum P < 2 * P := by
  have hex : ∃ s, k < primeWeightPrefix (s + 1) + 1 := by
    refine ⟨k, ?_⟩
    have := primeWeightPrefix_ge_index (k + 1)
    omega
  let s := Nat.find hex
  have hs : k < primeWeightPrefix (s + 1) + 1 := Nat.find_spec hex
  have hs0 : s ≠ 0 := by
    intro hsz
    rw [hsz] at hs
    norm_num [primeWeightPrefix, primeAt_zero] at hs
    omega
  have hprev : primeWeightPrefix s + 1 ≤ k := by
    have hlt : s - 1 < Nat.find hex := Nat.sub_lt (Nat.pos_of_ne_zero hs0) Nat.zero_lt_one
    have hh := Nat.find_min hex hlt
    rw [Nat.sub_add_cancel (Nat.pos_of_ne_zero hs0)] at hh
    omega
  refine ⟨primeAt (s - 1), primeAt_prime _, ?_, ?_⟩
  · rw [primeWeightSum_primeAt, Nat.sub_add_cancel (Nat.pos_of_ne_zero hs0)]
    exact hprev
  · rw [primeWeightSum_primeAt, Nat.sub_add_cancel (Nat.pos_of_ne_zero hs0)]
    have hnext := primeAt_succ_lt_two_mul (s - 1)
    rw [Nat.sub_add_cancel (Nat.pos_of_ne_zero hs0)] at hnext
    rw [primeWeightPrefix_succ] at hs
    omega

lemma prime_budget_bounds {P k : ℕ} (hP : P.Prime) (hbudget : primeWeightSum P + 1 ≤ k)
    (hgap : k - 1 - primeWeightSum P < 2 * P) :
    P ≤ k ∧ k ≤ P ^ 2 + 2 * P := by
  have hlo := prime_sub_one_le_weight hP
  have hhi := primeWeightSum_le_square P
  have hp2 := hP.two_le
  omega

/-- Large budgets force the selected prime past any fixed threshold. -/
lemma prime_budget_large {P k B : ℕ} (hP : P.Prime)
    (hbudget : primeWeightSum P + 1 ≤ k) (hgap : k - 1 - primeWeightSum P < 2 * P)
    (hk : B ^ 2 + 2 * B < k) : B < P := by
  have hbound := (prime_budget_bounds hP hbudget hgap).2
  by_contra hBP
  have hPB : P ≤ B := by omega
  nlinarith

end Erdos1189
