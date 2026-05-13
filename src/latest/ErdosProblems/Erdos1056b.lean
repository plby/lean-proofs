/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
/- Original license: Apache 2.0. Note: This file has been modified. -/
/-
This is a Lean formalization of a solution to Erdős Problem 1056.
https://www.erdosproblems.com/forum/thread/1056

Formalization status:
- Partial

Informal authors:
- Lorenzo Luccioli
- Aristotle

Formal authors:
- Aristotle
- Lorenzo Luccioli

URLs:
- https://www.erdosproblems.com/forum/thread/1056#post-2713
- https://gist.githubusercontent.com/LorenzoLuccioli/62c1534cff0ae0268f4e5fb92f3f5ae2/raw/b5f2abd33e6a90bbd7693089f14babbddbefcdb7/1056_aristotle.lean
-/
/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: ae58cefd-5214-47b0-9caf-ce96b083801e

The following was proved by Aristotle:

- @[category research open, AMS 11]
theorem noll_simmons :
    (∀ᶠ k in Filter.atTop,
    ∃ (p : ℕ) (_ : p.Prime) (Q : Fin k → ℕ) (_ : StrictMono Q) (_ : ∀ i, Q i < p),
    ∀ i j : Fin k, (Q i)! ≡ (Q j)! [MOD p])
-/

/-
Copyright 2025 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import Mathlib

set_option linter.style.setOption false
set_option linter.style.longLine false
set_option linter.style.nativeDecide false
set_option linter.style.induction false
set_option linter.style.refine false
set_option linter.style.show false
set_option maxHeartbeats 0
set_option aesop.warn.nonterminal false

open Nat

/-!
# Erdős Problem 1056

*Reference:* [erdosproblems.com/1056](https://www.erdosproblems.com/1056)
-/

namespace Erdos1056b

/--
The proposition that the modular product of a collection of consecutive interval equals $1$ modulo $p$,
where intervals are defined by a function specifying the consecutive boundaries.
-/
def AllModProdEqualsOne (p : ℕ) {k : ℕ} (boundaries : Fin (k + 1) → ℕ) : Prop :=
  ∀ i : Fin k,
    (∏ n ∈ Finset.Ico (boundaries i.castSucc) (boundaries (i.castSucc + 1)), n) ≡ 1 [MOD p]

/- Aristotle failed to find a proof. -/
/--
Let $k ≥ 2$. Does there exist a prime $p$ and consecutive intervals $I_0,\dots,I_k$
such that $\prod\limits_{n{\in}I_i}n \equiv 1 \mod n$ for all $1 \le i \le k$?
-/
def erdos_1056 : Prop :=
    (∀ k ≥ 2, ∃ (p : ℕ) (_ : p.Prime) (boundaries : Fin (k + 1) → ℕ) (_ : StrictMono boundaries),
    AllModProdEqualsOne p boundaries)

/--
This is problem A15 in Guy's collection [Gu04], where he reports that in a letter in 1979
Erdős observed that $3 * 4 \equiv 5 * 6 * 7 \equiv 1 \mod 11$.
-/
theorem erdos_1056_k2 :
    AllModProdEqualsOne 11 ![3, 5, 8] := by
  unfold AllModProdEqualsOne
  decide

/--
Makowski [Ma83] found, for $k=3$:
$2 * 3 * 4 * 5 \equiv 6 * 7 * 8 * 9 * 10 * 11 \equiv 12 * 13 * 14 * 15 \equiv 1 \mod 17$.
-/
theorem erdos_1056_k3 :
    AllModProdEqualsOne 17 ![2, 6, 12, 16] := by
  unfold AllModProdEqualsOne
  decide

/-
There exists a prime $p$ and a strictly increasing sequence $Q$ of length 3 with elements less than $p$ such that their factorials are congruent modulo $p$.
-/
theorem noll_simmons_k3 :
    ∃ (p : ℕ) (_ : p.Prime) (Q : Fin 3 → ℕ) (_ : StrictMono Q) (_ : ∀ i, Q i < p),
    ∀ i j : Fin 3, (Q i)! ≡ (Q j)! [MOD p] := by
  refine ⟨7, by
    norm_num, ![0, 1, 5], by
    decide, by
    decide +kernel, by
    native_decide +revert⟩

/-
If an interval $[a, b)$ contains no multiple of $p$, then it is contained in some interval $[mp, (m+1)p]$.
-/
lemma exists_shift_of_no_dvd {a b p : ℕ} (_hab : a < b) (hp : p ≠ 0)
    (h : ∀ n ∈ Finset.Ico a b, ¬ p ∣ n) :
    ∃ m, m * p ≤ a ∧ b ≤ (m + 1) * p := by
      contrapose! h;
      exact ⟨ ( a / p + 1 ) * p, Finset.mem_Ico.mpr ⟨ by nlinarith [ Nat.div_add_mod a p, Nat.mod_lt a ( Nat.pos_of_ne_zero hp ) ], by nlinarith [ Nat.div_mul_le_self a p, h ( a / p ) ( Nat.div_mul_le_self a p ) ] ⟩, by norm_num ⟩

/-
If consecutive intervals have product 1 mod p, then there exists a sequence of factorials congruent mod p.
-/
theorem noll_simmons_reduction {k : ℕ} {p : ℕ} {boundaries : Fin (k + 1) → ℕ}
    (hk : k ≠ 0)
    (hp : p.Prime) (h_mono : StrictMono boundaries)
    (h_prod : Erdos1056b.AllModProdEqualsOne p boundaries) :
    ∃ Q : Fin (k + 1) → ℕ, StrictMono Q ∧ (∀ i, Q i < p) ∧ ∀ i j, (Q i)! ≡ (Q j)! [MOD p] := by
  have h_bk_gt : boundaries 0 < boundaries (Fin.last k) := by
    apply h_mono
    show (0 : Fin (k+1)) < Fin.last k
    rw [Fin.lt_def]
    simp [Nat.pos_of_ne_zero hk]
  have h_no_dvd : ∀ n ∈ Finset.Ico (boundaries 0) (boundaries (Fin.last k)), ¬ p ∣ n := by
    intro n hn
    rw [Finset.mem_Ico] at hn
    -- We claim n falls into some [boundaries i, boundaries (i+1))
    have : ∃ i : Fin k, boundaries (i.castSucc) ≤ n ∧ n < boundaries (i.succ) := by
      -- This is true because boundaries partition the interval
      contrapose! hn; aesop;
      -- By induction on $i$, we can show that $boundaries i \leq n$ for all $i$.
      have h_ind : ∀ i : Fin (k + 1), boundaries i ≤ n := by
        intro i; induction i using Fin.inductionOn <;> aesop;
      exact h_ind _
    obtain ⟨i, hi_le, hi_lt⟩ := this
    have h_prod_i := h_prod i
    -- The product on [boundaries i, boundaries (i+1)) is 1 mod p
    -- So no element is 0 mod p
    have h_mem : n ∈ Finset.Ico (boundaries i.castSucc) (boundaries (i.succ)) := by
      rw [Finset.mem_Ico]
      exact ⟨hi_le, hi_lt⟩
    intro h_dvd
    have h_mod_0 : n ≡ 0 [MOD p] := by
      rw [Nat.ModEq, Nat.mod_eq_zero_of_dvd h_dvd]
      rfl
    -- Contradiction with product being 1
    -- If `p` divides `n`, then `n ≡ 0 [MOD p]`, and since `n` is in the interval `[boundaries i, boundaries (i + 1))`, the product of this interval would also be `0` modulo `p`.
    have h_prod_zero : (∏ n ∈ Finset.Ico (boundaries i.castSucc) (boundaries (i.castSucc + 1)), n) ≡ 0 [MOD p] := by
      exact Nat.modEq_zero_iff_dvd.mpr ( dvd_trans h_dvd ( Finset.dvd_prod_of_mem _ ( by simpa using h_mem ) ) );
    exact absurd ( h_prod_zero.symm.trans h_prod_i ) ( by haveI := Fact.mk hp; simp +decide [ ← ZMod.natCast_eq_natCast_iff ] )
  obtain ⟨m, hm_le, hm_gt⟩ := exists_shift_of_no_dvd h_bk_gt (Nat.Prime.ne_zero hp) h_no_dvd
  let Q := fun i => boundaries i - m * p - 1
  use Q
  constructor
  · -- StrictMono Q
    intro i j hij
    dsimp [Q]
    apply Nat.sub_lt_sub_right
    · -- m * p + 1 <= boundaries i
      -- We know m * p <= boundaries 0 <= boundaries i
      -- If boundaries 0 = m * p, then m * p \in [boundaries 0, boundaries k) since k != 0
      -- But h_no_dvd says no multiple of p in that range.
      -- So boundaries 0 != m * p.
      -- Thus m * p < boundaries 0.
      -- Since $boundaries$ is strictly monotonic, we have $boundaries i \geq boundaries 0$.
      have h_boundaries_i_ge_boundaries_0 : boundaries i ≥ boundaries 0 := by
        exact h_mono.monotone ( Nat.zero_le _ );
      exact Nat.sub_pos_of_lt ( lt_of_le_of_ne ( by linarith ) ( Ne.symm ( by intro t; have := h_no_dvd ( boundaries i ) ( Finset.mem_Ico.mpr ⟨ by linarith, by linarith [ h_mono.monotone ( show i ≤ Fin.last k from Fin.le_last _ ) ] ⟩ ) ; simp_all +decide [ Nat.dvd_iff_mod_eq_zero ] ) ) )
    · apply Nat.sub_lt_sub_right
      · -- m * p <= boundaries i
        trans boundaries 0
        · exact hm_le
        · apply h_mono.monotone
          exact Fin.zero_le i
      · exact h_mono hij
  constructor
  · -- Q i < p
    intro i
    dsimp [Q]
    -- boundaries i <= boundaries k <= (m+1)p
    -- Q i = boundaries i - mp - 1 <= (m+1)p - mp - 1 = p - 1 < p
    -- Since boundaries are strictly increasing, we have boundaries i ≤ boundaries (Fin.last k).
    have h_boundaries_le_last : boundaries i ≤ boundaries (Fin.last k) := by
      exact h_mono.monotone ( Fin.le_last _ );
    grind
  · -- Factorials congruent
    intro i j
    -- Suffices to show (Q (i+1))! \equiv (Q i)! for all i
    -- Then use transitivity
    -- By induction on $i$, we can show that $(Q_i)! \equiv (Q_0)! \pmod p$ for all $i$.
    have h_ind : ∀ i : Fin (k + 1), (Q i)! ≡ (Q 0)! [MOD p] := by
      intro i_1
      simp_all only [ne_eq, Finset.mem_Ico, and_imp, Q]
      induction' i_1 using Fin.inductionOn with i IH;
      · rfl;
      · -- Since $\prod_{x=Q_i+1}^{Q_{i+1}} x \equiv \prod_{n=b_i}^{b_{i+1}-1} n \pmod p$, we have $(Q_{i+1})! \equiv (Q_i)! \pmod p$.
        have h_prod_cong : (∏ x ∈ Finset.Ico (boundaries i.castSucc) (boundaries i.succ), x) ≡ (∏ x ∈ Finset.Ico (Q i.castSucc + 1) (Q i.succ + 1), x) [MOD p] := by
          have h_prod_cong : Finset.Ico (boundaries i.castSucc) (boundaries i.succ) = Finset.image (fun x => x + m * p + 1) (Finset.Ico (Q i.castSucc) (Q i.succ)) := by
            ext ; aesop <;> try omega;
            refine' ⟨ a - m * p - 1, _, _ ⟩ <;> norm_num [ Nat.sub_sub ];
            · constructor <;> try omega;
              rw [ tsub_lt_tsub_iff_right ] <;> try linarith [ h_mono.monotone ( show 0 ≤ Fin.castSucc i from Nat.zero_le _ ) ];
              contrapose! h_no_dvd;
              use m * p;
              aesop;
              · linarith [ h_mono.monotone ( show 0 ≤ Fin.castSucc i from Nat.zero_le _ ) ];
              · linarith [ h_mono.monotone ( show Fin.last k ≥ Fin.castSucc i from Fin.le_last _ ) ];
            · linarith [ Nat.sub_add_cancel ( show m * p + 1 ≤ a from by linarith [ show boundaries i.castSucc ≥ m * p + 1 from Nat.succ_le_of_lt ( lt_of_lt_of_le ( show m * p < boundaries 0 from lt_of_le_of_ne hm_le ( Ne.symm <| by intro t; specialize h_no_dvd ( boundaries 0 ) ; simp_all +decide ) ) ( h_mono.monotone <| Nat.zero_le _ ) ) ] ) ];
          rw [ h_prod_cong, Finset.prod_image ] <;> aesop;
          simp +decide [ ← ZMod.natCast_eq_natCast_iff, Finset.prod_Ico_eq_prod_range ];
          ac_rfl;
        have h_prod_cong : (∏ x ∈ Finset.Ico (Q i.castSucc + 1) (Q i.succ + 1), x) * (Q i.castSucc)! ≡ (Q i.succ)! [MOD p] := by
          have h_prod_cong : (∏ x ∈ Finset.Ico (Q i.castSucc + 1) (Q i.succ + 1), x) * (Q i.castSucc)! = (Q i.succ)! := by
            rw [ Finset.prod_Ico_eq_prod_range ];
            rw [ ← Nat.add_sub_of_le ( show Q i.castSucc ≤ Q i.succ from _ ) ];
            · induction ( Q i.succ - Q i.castSucc ) <;> simp_all +decide [ Nat.factorial, Finset.prod_range_succ ];
              grind;
            · exact Nat.sub_le_sub_right ( Nat.sub_le_sub_right ( h_mono.monotone ( Nat.le_succ _ ) ) _ ) _;
          rw [h_prod_cong];
        have := h_prod i; simp_all +decide [ ← ZMod.natCast_eq_natCast_iff ] ;
        simp_all only [Q]
    exact Nat.ModEq.trans ( h_ind i ) ( Nat.ModEq.symm ( h_ind j ) )

/-
For any $k \ge 3$, there exists a solution to the Noll-Simmons problem of length $k$.
-/
theorem noll_simmons_aux (h1056 : erdos_1056) (k : ℕ) (hk : k ≥ 3) :
    ∃ (p : ℕ) (_ : p.Prime) (Q : Fin k → ℕ) (_ : StrictMono Q) (_ : ∀ i, Q i < p),
    ∀ i j : Fin k, (Q i)! ≡ (Q j)! [MOD p] := by
      have := h1056 ( k - 1 ) ( Nat.le_sub_one_of_lt hk );
      rcases k with ( _ | _ | k ) <;> aesop;
      -- By the Erdős problem 1056, there exists a sequence of factorials congruent modulo p.
      obtain ⟨Q, hQ_mono, hQ_lt_p, hQ_cong⟩ := noll_simmons_reduction (by linarith) left left_1 right;
      exact ⟨ w, left, Q, hQ_lt_p, hQ_mono, hQ_cong ⟩

/-
Noll and Simmons asked, more generally, whether there are solutions to
$q_1! \equiv \dots \equiv q_k! \mod p$ for arbitrarily large $k$ (with $q_1 < \dots < q_k$).
-/
theorem noll_simmons (h1056 : erdos_1056) :
    (∀ᶠ k in Filter.atTop,
    ∃ (p : ℕ) (_ : p.Prime) (Q : Fin k → ℕ) (_ : StrictMono Q) (_ : ∀ i, Q i < p),
    ∀ i j : Fin k, (Q i)! ≡ (Q j)! [MOD p]) := by
  refine Filter.eventually_atTop.mpr ?_;
  use 3;
  intro k hk
  apply noll_simmons_aux h1056 k hk

#print axioms noll_simmons
-- 'Erdos1056b.noll_simmons' depends on axioms: [propext, Classical.choice, Quot.sound]

end Erdos1056b
