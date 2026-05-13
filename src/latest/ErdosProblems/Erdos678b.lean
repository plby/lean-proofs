/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
/-

This is a Lean formalization of part of Erdős Problem 678.
https://www.erdosproblems.com/forum/thread/678

The actual problem was solved positively by: Stijn Cambie

[Ca24] S. Cambie, Resolution of an Erdős' problem on least common
multiples. arXiv:2410.09138 (2024).

This file contains a DISproof of a statement that appeared on the
Erdős Problems site above:

Let $M(n,k)=[n+1,\ldots,n+k]$ be the least common multiple of
$\{n+1,\ldots,n+k\}$.

Let $k\geq 3$. Are there infinitely many $m,n$ with $m\geq n+k$ such
that\[M(n,k)>M(m,k+1)?\]

Aristotle found this (dis)proof by itself, provided only with a formal
statement of the problem.


The proof is verified by Lean.  The following version numbers were
used:

Lean Toolchain version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7 (v4.24.0)

-/


import Mathlib

set_option linter.style.longLine false
set_option linter.style.show false
set_option linter.style.setOption false
set_option linter.flexible false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.style.refine false
set_option linter.style.multiGoal false

namespace Erdos678b

open Real
open Filter

/-- The least common multiple of ${n+1, \dotsc, n+k}$. -/
def lcmInterval {α : Type*} [AddMonoid α] [CommMonoidWithZero α] [IsCancelMulZero α] [NormalizedGCDMonoid α]
    [Preorder α] [LocallyFiniteOrder α] (n k : α) : α := (Finset.Ioc n (n + k)).lcm id

/-
Upper bound for LCM of 3 consecutive integers.
-/
lemma lcm_3_upper (n : ℕ) : lcmInterval n 3 ≤ (n + 1) * (n + 2) * (n + 3) := by
  -- By definition of lcmInterval, we know that lcmInterval n 3 = Finset.lcm {n+1, n+2, n+3} id.
  have h_lcm_def : lcmInterval n 3 = Finset.lcm {n + 1, n + 2, n + 3} id := by
    unfold lcmInterval;
    congr with ( _ | _ | _ | _ | i ) <;> simp +arith +decide;
    · rcases n with ( _ | _ | n ) <;> simp +arith +decide;
    · exact ⟨ fun h => by interval_cases n <;> trivial, fun h => by rcases h with ( rfl | rfl | rfl ) <;> trivial ⟩;
    · omega;
  norm_num [ h_lcm_def ];
  exact Nat.le_of_dvd ( by positivity ) ( Nat.lcm_dvd ( dvd_mul_of_dvd_left ( dvd_mul_right _ _ ) _ ) ( Nat.lcm_dvd ( dvd_mul_of_dvd_left ( dvd_mul_left _ _ ) _ ) ( dvd_mul_left _ _ ) ) )

lemma factorization_24_2_3 : Nat.factorization 24 2 ≥ 3 := by
  show 3 ≤ (24 : ℕ).factorization 2
  have hdiv : (2 : ℕ) ^ 3 ∣ 24 := by
    refine ⟨3, by norm_num⟩
  exact
    (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two (by decide : 24 ≠ 0)).1 hdiv

/-
The p-adic valuation of `choose n k` is at most the p-adic valuation of the LCM
of the interval `[n-k+1,n]`.
-/
lemma valuation_choose_le_valuation_lcm (n k : ℕ) (p : ℕ) (hp : p.Prime) :
    padicValNat p (Nat.choose n k) ≤ padicValNat p ((Finset.Icc (n - k + 1) n).lcm id) := by
  by_cases hk : k ≤ n
  · have h_val :
        padicValNat p (Nat.choose n k) =
          ∑ i ∈ Finset.Icc 1 (Nat.log p n),
            (Nat.floor ((n : ℝ) / (p ^ i)) - Nat.floor ((k : ℝ) / (p ^ i)) -
              Nat.floor (((n - k) : ℝ) / (p ^ i))) := by
      haveI := Fact.mk hp
      rw [padicValNat_choose]
      any_goals exact Nat.lt_succ_self _
      · have h_sum_eq :
            ∀ i ∈ Finset.Icc 1 (Nat.log p n),
              ⌊(n : ℝ) / p ^ i⌋₊ - ⌊(k : ℝ) / p ^ i⌋₊ - ⌊((n - k) : ℝ) / p ^ i⌋₊ =
                if p ^ i ≤ k % p ^ i + (n - k) % p ^ i then 1 else 0 := by
          intro i hi
          have h_floor :
              ⌊(n : ℝ) / p ^ i⌋₊ = n / p ^ i ∧ ⌊(k : ℝ) / p ^ i⌋₊ = k / p ^ i ∧
                ⌊((n - k) : ℝ) / p ^ i⌋₊ = (n - k) / p ^ i := by
            norm_cast
            exact ⟨by rw [Nat.floor_div_natCast, Nat.floor_natCast],
              by rw [Nat.floor_div_natCast, Nat.floor_natCast],
              by rw [Nat.floor_div_natCast, Nat.floor_natCast]⟩
          split_ifs <;> simp_all +decide [Nat.div_eq_of_lt, Nat.mod_eq_of_lt]
          · rw [show n = k + (n - k) by rw [Nat.add_sub_of_le hk]]
            norm_num [Nat.add_div, hp.pos]
            split_ifs <;> omega
          · rw [show n = k + (n - k) by rw [Nat.add_sub_of_le hk]]
            norm_num [Nat.add_div (pow_pos hp.pos _)]
            split_ifs <;> omega
        rw [Finset.sum_congr rfl h_sum_eq, Finset.sum_ite]
        aesop
      · linarith
    have h_carry :
        ∀ i ∈ Finset.Icc 1 (Nat.log p n),
          (Nat.floor ((n : ℝ) / (p ^ i)) - Nat.floor ((k : ℝ) / (p ^ i)) -
              Nat.floor (((n - k) : ℝ) / (p ^ i))) ≤
            if ∃ j ∈ Finset.Icc (n - k + 1) n, p ^ i ∣ j then 1 else 0 := by
      intro i hi
      set m := Nat.floor ((n : ℝ) / (p ^ i))
      set l := Nat.floor ((k : ℝ) / (p ^ i))
      set r := Nat.floor (((n - k) : ℝ) / (p ^ i))
      have h_floor : m = n / p ^ i ∧ l = k / p ^ i ∧ r = (n - k) / p ^ i := by
        norm_num +zetaDelta at *
        norm_cast
        exact ⟨by rw [Nat.floor_div_natCast, Nat.floor_natCast],
          by rw [Nat.floor_div_natCast, Nat.floor_natCast],
          by rw [Nat.floor_div_natCast, Nat.floor_natCast]⟩
      split_ifs <;> simp_all +decide [Nat.div_eq_of_lt]
      · rw [show n = n - k + k by rw [Nat.sub_add_cancel hk]]
        norm_num [Nat.add_div, hp.pos]
        grind
      · rw [Nat.sub_sub, tsub_eq_zero_iff_le.mpr]
        rw [Nat.le_iff_lt_or_eq]
        refine' lt_or_eq_of_le (Nat.le_of_lt_succ _)
        rw [Nat.div_lt_iff_lt_mul <| pow_pos hp.pos _]
        contrapose! h_floor
        exact fun _ _ =>
          False.elim <|
            ‹∀ x : ℕ, n - k + 1 ≤ x → x ≤ n → ¬p ^ i ∣ x›
              ((k / p ^ i + (n - k) / p ^ i + 1) * p ^ i)
              (by
                nlinarith [Nat.div_add_mod k (p ^ i), Nat.mod_lt k (pow_pos hp.pos i),
                  Nat.div_add_mod (n - k) (p ^ i), Nat.mod_lt (n - k) (pow_pos hp.pos i),
                  Nat.sub_add_cancel hk])
              (by
                nlinarith [Nat.div_add_mod k (p ^ i), Nat.mod_lt k (pow_pos hp.pos i),
                  Nat.div_add_mod (n - k) (p ^ i), Nat.mod_lt (n - k) (pow_pos hp.pos i),
                  Nat.sub_add_cancel hk])
              <| dvd_mul_left _ _
    have h_max_i :
        ∀ i ∈ Finset.Icc 1 (Nat.log p n),
          (∃ j ∈ Finset.Icc (n - k + 1) n, p ^ i ∣ j) →
            i ≤ Nat.factorization (Finset.lcm (Finset.Icc (n - k + 1) n) id) p := by
      intros i hi h_div
      obtain ⟨j, hj₁, hj₂⟩ := h_div
      have h_div_lcm : p ^ i ∣ Finset.lcm (Finset.Icc (n - k + 1) n) id := by
        exact dvd_trans hj₂ (Finset.dvd_lcm hj₁)
      rw [← Nat.factorization_le_iff_dvd] at h_div_lcm <;> aesop
    have h_sum_carry :
        ∑ i ∈ Finset.Icc 1 (Nat.log p n),
            (if ∃ j ∈ Finset.Icc (n - k + 1) n, p ^ i ∣ j then 1 else 0) ≤
          Nat.factorization (Finset.lcm (Finset.Icc (n - k + 1) n) id) p := by
      simp +zetaDelta
      exact le_trans
        (Finset.card_le_card fun x hx => by
          rcases Finset.mem_filter.mp hx with ⟨hxIcc, hxEx⟩
          rcases hxEx with ⟨j, hjIcc, hjdvd⟩
          exact Finset.mem_Icc.mpr
            ⟨(Finset.mem_Icc.mp hxIcc).1,
              h_max_i x hxIcc ⟨j, hjIcc, hjdvd⟩⟩)
        (by simp)
    convert h_sum_carry.trans' (Finset.sum_le_sum h_carry) using 1
    rw [Nat.factorization_def]
    aesop
  · simp +decide [Nat.choose_eq_zero_of_lt (not_le.mp hk)]

/-
The binomial coefficient `binom(y+k,k+1)` divides the LCM of `[y,y+k]`.
-/
lemma choose_dvd_lcm (y k : ℕ) : Nat.choose (y + k) (k + 1) ∣ (Finset.Icc y (y + k)).lcm id := by
  by_cases hy : y = 0
  · simp +decide [hy, Nat.choose_eq_zero_of_lt]
  · have h_val :
        ∀ p, p.Prime →
          padicValNat p (Nat.choose (y + k) (k + 1)) ≤
            padicValNat p ((Finset.Icc y (y + k)).lcm id) := by
      convert valuation_choose_le_valuation_lcm (y + k) (k + 1) using 1
      grind
    rw [← Nat.factorization_le_iff_dvd]
    · intro p
      by_cases hp : Nat.Prime p <;> simp_all +decide [Nat.factorization]
    · exact Nat.ne_of_gt <| Nat.choose_pos <| by linarith [Nat.pos_of_ne_zero hy]
    · norm_num [Finset.lcm_eq_zero_iff]
      assumption

set_option maxHeartbeats 1000000 in
/-
The binomial coefficient `choose (m+4) 4` divides `lcm(m+1, ..., m+4)`.
-/
lemma choose_dvd_lcm_4 (m : ℕ) : Nat.choose (m + 4) 4 ∣ lcmInterval m 4 := by
  have hset : Finset.Icc (m + 1) (m + 4) = Finset.Ioc m (m + 4) := by
    ext x
    simp [Finset.mem_Icc, Finset.mem_Ioc]
  rw [lcmInterval, ← hset]
  simpa [Nat.succ_eq_add_one, add_assoc] using choose_dvd_lcm (m + 1) 3

/-
Lower bound for LCM of 4 consecutive integers.
-/
lemma lcm_4_lower (m : ℕ) : lcmInterval m 4 * 24 ≥ (m + 1) * (m + 2) * (m + 3) * (m + 4) := by
  -- We have `Nat.choose (m + 4) 4 ∣ lcmInterval m 4` by `choose_dvd_lcm_4`.
  have h_choose_div_lcm : Nat.choose (m + 4) 4 ∣ lcmInterval m 4 := by
    exact choose_dvd_lcm_4 m;
  -- Since `Nat.choose (m + 4) 4` is equal to `(m + 1) * (m + 2) * (m + 3) * (m + 4) / 24`, we can substitute this into the inequality.
  have h_choose_eq : Nat.choose (m + 4) 4 = (m + 1) * (m + 2) * (m + 3) * (m + 4) / 24 := by
    rw [ Nat.choose_eq_factorial_div_factorial ] <;> norm_num [ Nat.factorial_succ ];
    norm_num [ ← mul_assoc, Nat.mul_div_mul_right, Nat.factorial_pos ] ; ring_nf;
  -- Since the binomial coefficient divides the LCM, we have that the binomial coefficient is less than or equal to the LCM.
  have h_binom_le_lcm : (m + 1) * (m + 2) * (m + 3) * (m + 4) / 24 ≤ lcmInterval m 4 := by
    exact h_choose_eq ▸ Nat.le_of_dvd ( Nat.pos_of_ne_zero ( mt Finset.lcm_eq_zero_iff.mp ( by aesop ) ) ) h_choose_div_lcm;
  linarith [ Nat.div_mul_cancel ( show 24 ∣ ( m + 1 ) * ( m + 2 ) * ( m + 3 ) * ( m + 4 ) from Nat.dvd_of_mod_eq_zero ( by norm_num [ Nat.add_mod, Nat.mod_mod, Nat.mul_mod ] ; have := Nat.mod_lt m ( by decide : 0 < 24 ) ; interval_cases m % 24 <;> trivial ) ) ]

/-
For n >= 21 and m >= n, lcm(m, 4) > lcm(n, 3).
-/
lemma lcm_ineq_large_n (n : ℕ) (hn : n ≥ 21) (m : ℕ) (hm : m ≥ n) :
    lcmInterval m 4 > lcmInterval n 3 := by
      have h_div : (m + 1) * (m + 2) * (m + 3) * (m + 4) > 24 * (n + 1) * (n + 2) * (n + 3) := by
        nlinarith [ Nat.mul_le_mul hm hm, Nat.mul_le_mul hm hn ];
      -- Apply the inequalities from `lcm_4_lower` and `lcm_3_upper`.
      have h_lcm_ineq : lcmInterval m 4 * 24 ≥ (m + 1) * (m + 2) * (m + 3) * (m + 4) ∧ lcmInterval n 3 ≤ (n + 1) * (n + 2) * (n + 3) := by
        apply And.intro;
        · exact lcm_4_lower m;
        · exact lcm_3_upper n;
      linarith

/-
lcm(m+1, ..., m+4) >= m+1.
-/
lemma lcm_4_ge_succ_m (m : ℕ) : lcmInterval m 4 ≥ m + 1 := by
  -- Since `m+1` is in the set, it divides the LCM.
  have h_div : (m + 1) ∣ lcmInterval m 4 := by
    exact Finset.dvd_lcm ( Finset.mem_Ioc.mpr ⟨ by linarith, by linarith ⟩ );
  exact Nat.le_of_dvd ( Nat.pos_of_ne_zero <| mt Finset.lcm_eq_zero_iff.mp <| by aesop ) h_div

/-
The set of pairs (m, n) satisfying the condition for k=3 is finite.
-/
lemma k_3_finite : {p : ℕ × ℕ | p.2 + 3 ≤ p.1 ∧ lcmInterval p.1 4 < lcmInterval p.2 3}.Finite := by
  -- The set is a subset of $\bigcup_{n < 21} \{m \mid m < \text{lcmInterval } n \ 3\} \times \{n\}$.
  have h_subset : {p : ℕ × ℕ | p.2 + 3 ≤ p.1 ∧ lcmInterval p.1 4 < lcmInterval p.2 3} ⊆
    Finset.biUnion (Finset.range 21) (fun n => Finset.image (fun m => (m, n)) (Finset.Ico 0 (lcmInterval n 3))) := by
      intro p hp
      rcases hp with ⟨hmn, hlt⟩
      have hn_lt_21 : p.2 < 21 := by
        -- If $n \geq 21$, then by `lcm_ineq_large_n`, $lcmInterval m 4 > lcmInterval n 3$, contradicting $hlt$.
        by_contra h_contra
        have h_contra' : lcmInterval p.1 4 > lcmInterval p.2 3 := by
          apply lcm_ineq_large_n; linarith; linarith;
        linarith;
      simp +zetaDelta at *;
      exact ⟨ p.2, hn_lt_21, p.1, by linarith [ show lcmInterval p.1 4 ≥ p.1 + 1 from lcm_4_ge_succ_m p.1 ], rfl ⟩;
  exact Set.Finite.subset ( Finset.finite_toSet _ ) h_subset

/-
The statement erdos_678 is false.
-/
theorem not_erdos_678 : ¬ (∀ k ≥ 3, {(m, n) | n + k ≤ m ∧ lcmInterval m (k + 1) < lcmInterval n k}.Infinite) := by
  push Not;
  use 3;
  -- Apply the lemma k_3_finite to conclude the proof.
  exact ⟨by norm_num, by simpa using k_3_finite⟩

#print axioms not_erdos_678
-- 'not_erdos_678' depends on axioms: [propext, Classical.choice, Quot.sound]

end Erdos678b
