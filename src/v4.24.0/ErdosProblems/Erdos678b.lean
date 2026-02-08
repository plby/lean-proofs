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

namespace Erdos678b

open Real
open Filter

/-- The least common multiple of ${n+1, \dotsc, n+k}$. -/
def lcmInterval {α : Type*} [AddMonoid α] [CancelCommMonoidWithZero α] [NormalizedGCDMonoid α]
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

set_option maxHeartbeats 1000000 in
/-
The binomial coefficient `choose (m+4) 4` divides `lcm(m+1, ..., m+4)`.
-/
lemma choose_dvd_lcm_4 (m : ℕ) : Nat.choose (m + 4) 4 ∣ lcmInterval m 4 := by
  -- Let $P = (m + 1)(m + 2)(m + 3)(m + 4)$.
  let P := (m + 1) * (m + 2) * (m + 3) * (m + 4);
  -- We need to show $P / 24$ divides $L = lcm(m+1, m+2, m+3, m+4)$.
  have h_div : ∀ p ∈ Nat.primeFactors 24, Nat.factorization P p ≤ Nat.factorization (lcmInterval m 4) p + Nat.factorization 24 p := by
    intro p hp
    have h_div : ∀ i ∈ Finset.Icc (m + 1) (m + 4), Nat.factorization i p ≤ Nat.factorization (lcmInterval m 4) p := by
      intro i hi
      have h_div : i ∣ lcmInterval m 4 := by
        exact Finset.dvd_lcm ( Finset.mem_Ioc.mpr ⟨ by linarith [ Finset.mem_Icc.mp hi ], by linarith [ Finset.mem_Icc.mp hi ] ⟩ );
      exact Nat.factorization_le_iff_dvd ( by aesop ) ( by exact Nat.ne_of_gt <| Nat.pos_of_ne_zero <| mt Finset.lcm_eq_zero_iff.mp <| by aesop ) |>.2 h_div p;
    rw [ show P = ( m + 1 ) * ( m + 2 ) * ( m + 3 ) * ( m + 4 ) by rfl, Nat.factorization_mul, Nat.factorization_mul, Nat.factorization_mul ] <;> simp_all
    have := Nat.le_of_dvd ( by decide ) hp.2; interval_cases p <;> norm_num at *;
    · rcases Nat.even_or_odd' m with ⟨ k, rfl | rfl ⟩ <;> simp +arith +decide [ Nat.factorization_eq_zero_of_not_dvd, ← even_iff_two_dvd, parity_simps ] at *;
      · norm_num [ show 2 * k + 2 = 2 * ( k + 1 ) by ring, show 2 * k + 4 = 2 * ( k + 2 ) by ring, Nat.factorization_mul ];
        rw [ show ( 24 : ℕ ) = 2 ^ 3 * 3 by norm_num, Nat.factorization_mul, Nat.factorization_pow ] <;> norm_num;
        rcases Nat.even_or_odd' k with ⟨ k, rfl | rfl ⟩ <;> simp +arith +decide [ Nat.factorization_eq_zero_of_not_dvd, ← even_iff_two_dvd, parity_simps ] at *;
        · have := h_div ( 4 * k + 1 ) ( by linarith ) ( by linarith ) ; have := h_div ( 4 * k + 2 ) ( by linarith ) ( by linarith ) ; have := h_div ( 4 * k + 3 ) ( by linarith ) ( by linarith ) ; have := h_div ( 4 * k + 4 ) ( by linarith ) ( by linarith ) ; norm_num [ show 4 * k + 2 = 2 * ( 2 * k + 1 ) by ring, show 4 * k + 4 = 2 * ( 2 * k + 2 ) by ring, Nat.factorization_eq_zero_of_not_dvd, ← even_iff_two_dvd, parity_simps ] at * ; linarith;
        · rw [ show 2 * k + 2 = 2 * ( k + 1 ) by ring, Nat.factorization_mul ] <;> norm_num;
          linarith [ h_div ( 4 * k + 4 ) ( by linarith ) ( by linarith ), show Nat.factorization ( 4 * k + 4 ) 2 ≥ Nat.factorization ( k + 1 ) 2 + 2 from by rw [ show 4 * k + 4 = 2 ^ 2 * ( k + 1 ) by ring, Nat.factorization_mul, Nat.factorization_pow ] <;> norm_num ; linarith ];
      · have := h_div ( 2 * k + 2 ) ( by linarith ) ( by linarith ) ; have := h_div ( 2 * k + 4 ) ( by linarith ) ( by linarith ) ; norm_num [ show 2 * k + 2 = 2 * ( k + 1 ) by ring, show 2 * k + 4 = 2 * ( k + 2 ) by ring, Nat.factorization_mul ] at * ; simp_all +arith +decide;
        rcases Nat.even_or_odd' k with ⟨ k, rfl | rfl ⟩ <;> simp +arith +decide [ Nat.factorization_eq_zero_of_not_dvd, ← even_iff_two_dvd, parity_simps ] at *;
        · exact le_trans ( by linarith ) ( add_le_add_right ( factorization_24_2_3 ) _ );
        · rw [ show ( 24 : ℕ ) = 2 ^ 3 * 3 by norm_num, Nat.factorization_mul, Nat.factorization_pow ] <;> norm_num ; linarith;
    · rw [ show ( 24 : ℕ ) = 2 ^ 3 * 3 by norm_num, Nat.factorization_mul, Nat.factorization_pow ] <;> norm_num;
      have := Nat.mod_lt m zero_lt_three; interval_cases _ : m % 3 <;> simp_all +decide [ Nat.factorization_eq_zero_of_not_dvd, Nat.dvd_iff_mod_eq_zero ] ;
      · have := h_div ( m + 3 ) ( by linarith ) ( by linarith ) ; simp_all +decide [ Nat.factorization_eq_zero_of_not_dvd, Nat.dvd_iff_mod_eq_zero, Nat.add_mod ] ;
        exact le_add_right ( h_div _ ( by linarith ) ( by linarith ) );
      · norm_num [ Nat.factorization_eq_zero_of_not_dvd, Nat.dvd_iff_mod_eq_zero, Nat.add_mod, ‹_› ];
        grind;
      · norm_num [ Nat.factorization_eq_zero_of_not_dvd, Nat.dvd_iff_mod_eq_zero, Nat.add_mod, ‹_› ];
        norm_num [ show m + 1 = 3 * ( m / 3 + 1 ) by linarith [ Nat.mod_add_div m 3 ], show m + 4 = 3 * ( m / 3 + 2 ) by linarith [ Nat.mod_add_div m 3 ] ];
        have := h_div ( m + 1 ) ( by linarith ) ( by linarith ) ; ( have := h_div ( m + 2 ) ( by linarith ) ( by linarith ) ; ( have := h_div ( m + 3 ) ( by linarith ) ( by linarith ) ; ( have := h_div ( m + 4 ) ( by linarith ) ( by linarith ) ; ( norm_num [ show m + 1 = 3 * ( m / 3 ) + 3 by linarith [ Nat.mod_add_div m 3 ], show m + 2 = 3 * ( m / 3 ) + 4 by linarith [ Nat.mod_add_div m 3 ], show m + 3 = 3 * ( m / 3 ) + 5 by linarith [ Nat.mod_add_div m 3 ], show m + 4 = 3 * ( m / 3 ) + 6 by linarith [ Nat.mod_add_div m 3 ] ] at * ; ) ) ) );
        norm_num [ show 3 * ( m / 3 ) + 3 = 3 * ( m / 3 + 1 ) by ring, show 3 * ( m / 3 ) + 6 = 3 * ( m / 3 + 2 ) by ring, Nat.factorization_mul ] at *;
        by_cases h : 3 ∣ m / 3 + 1 <;> by_cases h' : 3 ∣ m / 3 + 2 <;> simp_all +decide [ Nat.factorization_eq_zero_of_not_dvd ];
        · omega;
        · grind;
  -- This is equivalent to showing $P$ divides $24L$.
  have h_eqv : P ∣ 24 * lcmInterval m 4 := by
    rw [ ← Nat.factorization_le_iff_dvd ] <;> norm_num;
    · intro p; by_cases hp : Nat.Prime p <;> by_cases hp' : p ∣ 24 <;> simp_all +decide [ Nat.factorization_mul, show lcmInterval m 4 ≠ 0 from by exact Nat.ne_of_gt <| Nat.pos_of_ne_zero <| mt Finset.lcm_eq_zero_iff.mp <| by simp [ Finset.mem_Ioc ] ] ;
      · linarith [ h_div p hp hp' ];
      · -- For any prime $p$ not dividing $24$, we need to show $v_p(P) \le v_p(L)$.
        by_cases hp'' : p ∣ (m + 1) ∨ p ∣ (m + 2) ∨ p ∣ (m + 3) ∨ p ∣ (m + 4);
        · -- Since $p$ divides one of the factors of $P$, we have $v_p(P) = v_p(\text{that factor})$.
          have h_vp_P : Nat.factorization P p = Nat.factorization (if p ∣ (m + 1) then (m + 1) else if p ∣ (m + 2) then (m + 2) else if p ∣ (m + 3) then (m + 3) else (m + 4)) p := by
            split_ifs <;> simp_all
            · rw [ Nat.factorization_mul, Nat.factorization_mul, Nat.factorization_mul ] <;> simp_all
              rw [ Nat.factorization_eq_zero_of_not_dvd ( show ¬ p ∣ m + 2 from fun h => by have := Nat.dvd_sub h ‹p ∣ m + 1›; simp_all ), Nat.factorization_eq_zero_of_not_dvd ( show ¬ p ∣ m + 3 from fun h => by have := Nat.dvd_sub h ‹p ∣ m + 1›; simp_all +decide [ Nat.prime_dvd_prime_iff_eq ] ), Nat.factorization_eq_zero_of_not_dvd ( show ¬ p ∣ m + 4 from fun h => by have := Nat.dvd_sub h ‹p ∣ m + 1›; simp_all +decide [ Nat.prime_dvd_prime_iff_eq ] ) ] ; ring;
            · rw [ Nat.factorization_mul, Nat.factorization_mul, Nat.factorization_mul ] <;> simp_all
              simp_all +decide [ Nat.factorization_eq_zero_of_not_dvd ];
              rw [ Nat.factorization_eq_zero_of_not_dvd ( show ¬ p ∣ m + 3 from fun h => by have := Nat.dvd_sub h ‹p ∣ m + 2›; simp_all ), Nat.factorization_eq_zero_of_not_dvd ( show ¬ p ∣ m + 4 from fun h => by have := Nat.dvd_sub h ‹p ∣ m + 2›; simp_all +decide [ Nat.prime_dvd_prime_iff_eq ] ) ] ; ring;
            · rw [ Nat.factorization_mul, Nat.factorization_mul, Nat.factorization_mul ] <;> simp_all
              simp_all +decide [ Nat.factorization_eq_zero_of_not_dvd ];
              exact Nat.factorization_eq_zero_of_not_dvd fun h => hp' <| by have := Nat.dvd_sub h ‹p ∣ m + 3›; simp_all
            · rw [ Nat.factorization_mul, Nat.factorization_mul, Nat.factorization_mul ] <;> simp_all
              exact ⟨ ⟨ Nat.factorization_eq_zero_of_not_dvd ‹_›, Nat.factorization_eq_zero_of_not_dvd ‹_› ⟩, Nat.factorization_eq_zero_of_not_dvd ‹_› ⟩;
          -- Since $p$ divides one of the factors of $P$, we have $v_p(L) \ge v_p(\text{that factor})$.
          have h_vp_L : Nat.factorization (lcmInterval m 4) p ≥ Nat.factorization (if p ∣ (m + 1) then (m + 1) else if p ∣ (m + 2) then (m + 2) else if p ∣ (m + 3) then (m + 3) else (m + 4)) p := by
            have h_vp_L : ∀ {x : ℕ}, x ∈ Finset.Ioc m (m + 4) → Nat.factorization (lcmInterval m 4) p ≥ Nat.factorization x p := by
              intros x hx; exact (by
              have h_vp_L : x ∣ lcmInterval m 4 := by
                exact Finset.dvd_lcm hx;
              exact ( Nat.factorization_le_iff_dvd ( by aesop ) ( by exact Nat.ne_of_gt <| Nat.pos_of_ne_zero <| mt Finset.lcm_eq_zero_iff.mp <| by aesop ) ) |>.2 h_vp_L p);
            split_ifs <;> simp_all +decide [ Finset.mem_Ioc ];
          linarith;
        · simp +zetaDelta at *;
          simp_all +decide [ Nat.factorization_eq_zero_of_not_dvd ];
    · positivity;
    · exact Nat.ne_of_gt <| Nat.pos_of_ne_zero <| mt Finset.lcm_eq_zero_iff.mp <| by aesop;
  -- Since $P = 24 \cdot \binom{m+4}{4}$, we can conclude that $\binom{m+4}{4}$ divides $lcmInterval m 4$.
  have h_binom : P = 24 * Nat.choose (m + 4) 4 := by
    simp +zetaDelta at *;
    rw [ Nat.choose_eq_factorial_div_factorial ] <;> norm_num [ Nat.factorial_succ ];
    norm_num [ ← mul_assoc, Nat.mul_div_mul_right, Nat.factorial_pos ] ; ring_nf;
    rw [ Nat.div_mul_cancel ( Nat.dvd_of_mod_eq_zero ( by norm_num [ Nat.add_mod, Nat.mul_mod, Nat.pow_mod ] ; have := Nat.mod_lt m ( by decide : 0 < 24 ) ; interval_cases m % 24 <;> trivial ) ) ];
  exact Nat.dvd_of_mul_dvd_mul_left ( by decide ) ( h_binom ▸ h_eqv )

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
  push_neg;
  use 3;
  -- Apply the lemma k_3_finite to conclude the proof.
  apply And.intro (by norm_num) (by exact Set.not_infinite.mpr k_3_finite)

#print axioms not_erdos_678
-- 'not_erdos_678' depends on axioms: [propext, Classical.choice, Quot.sound]
