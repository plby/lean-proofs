/-

This is a Lean formalization of a solution to Erdős Problem 649.
https://www.erdosproblems.com/649


The results from the link above were auto-formalized by ChatGPT (from
OpenAI) and Aristotle (from Harmonic).


The proof is verified by Lean.  The following version numbers were
used:

Lean Toolchain version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7 (v4.24.0)

-/


/-
We have formalized and proved the following results regarding the greatest prime factor function P(n):
1. The conjecture that for any primes p, q there exists n such that P(n)=p and P(n+1)=q is false. Specifically, we proved `conjecture_false` for p=2, q=7.
2. We proved `tong_counterexamples` showing that for any prime p, there are infinitely many primes q such that the conjecture fails.
3. We formalized Tong's question about the existence of infinitely many p for a given q as `tong_question`.
4. We proved `sampaio_counterexample` showing there is no n with P(n)=19 and P(n+1)=2.
-/

/-
5. Solution to RMM 2020 Problem 6:

We formalize the proof that there exist infinitely many strange pairs of primes.
We define a strange pair $\{p, q\}$ as a pair of distinct primes such that no $n \ge 2$ satisfies $P(n)P(n+1) = pq$.
We prove that if $2 < q_1 < q_2$ are primes with $\text{ord}_{q_1}(2) = \text{ord}_{q_2}(2)$, then $\{2, q_1\}$ is a strange pair.
We then show that for any prime $p > 5$, $N = 2^{2p} + 1$ has at least two prime factors $q_1, q_2 > 5$, both satisfying $\text{ord}_{q}(2) = 4p$.
This allows us to construct infinitely many strange pairs of the form $\{2, q\}$.
-/

import Mathlib

namespace Erdos649

/-
Let $P(n)$ denote the greatest prime factor of $n$.
-/
def P (n : ℕ) : ℕ := (n.primeFactors).max.getD 0

/-
It is not true that for any two primes $p,q$, there exists some integer $n$ such that $P(n)=p$ and $P(n+1)=q$. Specifically, there is no solution for $p=2$ and $q=7$.
-/
theorem conjecture_false : ¬ ∀ (p q : ℕ), p.Prime → q.Prime → ∃ (n : ℕ), P n = p ∧ P (n + 1) = q := by
  simp +zetaDelta at *;
  use 2, Nat.prime_two, 7, by norm_num;
  unfold P;
  -- Suppose there exists some integer $n$ such that $P(n)=2$ and $P(n+1)=7$.
  intro x hx hx'
  have h_pow_2 : ∃ k : ℕ, x = 2 ^ k := by
    have h_pow_2 : ∀ p ∈ Nat.primeFactors x, p = 2 := by
      -- Since $p$ is a prime factor of $x$, we have $p \leq 2$.
      intros p hp
      have hp_le_2 : p ≤ 2 := by
        have h_le_two : p ≤ Finset.max x.primeFactors := by
          exact Finset.le_max hp;
        cases h : Finset.max x.primeFactors <;> aesop;
      interval_cases p <;> simp_all +decide;
    rw [ ← Nat.prod_primeFactorsList ( show x ≠ 0 from _ ) ] ; rw [ List.prod_eq_pow_single 2 ] ; aesop;
    · exact fun p hp h => False.elim <| hp <| h_pow_2 p <| by simpa using h;
    · aesop_cat;
  -- Then $P(x+1)=7$ implies that the greatest prime factor of $2^k+1$ is 7.
  obtain ⟨k, rfl⟩ := h_pow_2
  have h_max_prime_factor : (2 ^ k + 1).primeFactors.max = some 7 := by
    rw [ Option.getD_eq_iff ] at hx' ; aesop;
  -- This implies that $7$ divides $2^k+1$, so $2^k \equiv -1 \equiv 6 \pmod{7}$.
  have h_div : 7 ∣ (2 ^ k + 1) := by
    exact Nat.dvd_of_mem_primeFactors <| Finset.mem_of_max h_max_prime_factor;
  rw [ Nat.dvd_iff_mod_eq_zero ] at h_div; rw [ ← Nat.mod_add_div k 3 ] at *; norm_num [ Nat.pow_add, Nat.pow_mul, Nat.add_mod, Nat.mul_mod, Nat.pow_mod ] at *; have := Nat.mod_lt k zero_lt_three; interval_cases k % 3 <;> norm_num at *;

/-
Assuming Mahler's theorem (that the greatest prime factor of $n(n+1)$ tends to infinity), the number of solutions to $P(n)=p$ and $P(n+1)=q$ is finite for any fixed primes $p, q$.
-/
def mahler_theorem_statement : Prop := Filter.Tendsto (fun n => P (n * (n + 1))) Filter.atTop Filter.atTop

theorem solutions_finite_of_mahler (h : mahler_theorem_statement) (p q : ℕ) : {n | P n = p ∧ P (n + 1) = q}.Finite := by
  -- By Mahler's theorem, there exists an $N$ such that for all $n \geq N$, $P(n(n+1)) > \max(p, q)$.
  obtain ⟨N, hN⟩ : ∃ N, ∀ n ≥ N, P (n * (n + 1)) > max p q := by
    -- By Mahler's theorem, the greatest prime factor of $n(n+1)$ tends to infinity as $n$ tends to infinity.
    have h_mahler : Filter.Tendsto (fun n => P (n * (n + 1))) Filter.atTop Filter.atTop := by
      convert h using 1;
    exact Filter.eventually_atTop.mp ( h_mahler.eventually_gt_atTop ( Max.max p q ) );
  refine Set.finite_iff_bddAbove.mpr ⟨ N, fun n hn => le_of_not_gt fun hn' => ?_ ⟩ ; specialize hN n hn'.le ; simp_all +decide
  -- By definition of $P$, we know that $P(n(n+1)) = \max(P(n), P(n+1))$.
  have hP_prod : P (n * (n + 1)) = max (P n) (P (n + 1)) := by
    unfold P at *;
    rcases n with ( _ | _ | n ) <;> simp_all +decide [ Nat.primeFactors_mul ];
    rw [ ← hn.1, ← hn.2, Finset.max_eq_sup_coe ];
    simp +decide [ Finset.sup_union, Option.getD ];
    cases h : Finset.sup ( Nat.primeFactors ( n + 1 + 1 ) ) ( WithBot.some ) <;> cases h' : Finset.sup ( Nat.primeFactors ( n + 1 + 1 + 1 ) ) ( WithBot.some ) <;> simp_all +decide [ Finset.max ];
    · exact False.elim ( h ( Nat.minFac ( n + 1 + 1 ) ) ( Nat.minFac_prime ( by linarith ) ) ( Nat.minFac_dvd _ ) );
    · exact False.elim <| h ( Nat.minFac ( n + 1 + 1 ) ) ( Nat.minFac_prime <| by linarith ) <| Nat.minFac_dvd _;
    · exact False.elim <| h' ( Nat.minFac ( n + 1 + 1 + 1 ) ) ( Nat.minFac_prime <| by linarith ) <| Nat.minFac_dvd _;
  cases max_cases ( P n ) ( P ( n + 1 ) ) <;> linarith

/-
There are infinitely many primes congruent to -1 modulo k for k > 2.
-/
lemma infinite_primes_mod_neg_one (k : ℕ) (hk : 2 < k) : {p : ℕ | p.Prime ∧ (p : ℤ) ≡ -1 [ZMOD k]}.Infinite := by
  have h_dirichlet : Set.Infinite {p : ℕ | Nat.Prime p ∧ p ≡ k - 1 [MOD k]} := by
    have := @Nat.setOf_prime_and_eq_mod_infinite;
    convert @this k ?_ ( k - 1 : ZMod k ) ?_ using 1;
    · rcases k with ( _ | _ | k ) <;> simp_all +decide [ ← ZMod.natCast_eq_natCast_iff ];
      norm_cast;
    · exact ⟨ by linarith ⟩;
    · rcases k with ( _ | _ | k ) <;> norm_num at *;
  exact h_dirichlet.mono fun p hp => ⟨ hp.1, Int.ModEq.trans ( Int.natCast_modEq_iff.mpr hp.2 ) ( Int.modEq_iff_dvd.mpr ⟨ -1, by cases k <;> norm_num at * ; linarith ⟩ ) ⟩

/-
If l <= p and q = -1 mod 4p#, then q = -1 mod l.
-/
lemma q_mod_l_eq_neg_one (p q l : ℕ) (hl : l.Prime) (h_le : l ≤ p)
    (h_q_mod : (q : ℤ) ≡ -1 [ZMOD (4 * primorial p)]) : (q : ℤ) ≡ -1 [ZMOD l] := by
      -- Since $l \le p$, $l$ divides $4 * primorial p$.
      have h_div : l ∣ 4 * primorial p := by
        refine' dvd_mul_of_dvd_right _ _;
        exact Finset.dvd_prod_of_mem _ ( Finset.mem_filter.mpr ⟨ Finset.mem_range.mpr ( Nat.lt_succ_of_le h_le ), hl ⟩ );
      exact h_q_mod.of_dvd <| Int.natCast_dvd_natCast.mpr h_div

/-
If q = -1 mod 4, then (q-1)/2 is odd.
-/
lemma odd_div_two_of_mod_four_eq_neg_one (q : ℕ) (hq : (q : ℤ) ≡ -1 [ZMOD 4]) : Odd ((q - 1) / 2) := by
  rcases Nat.even_or_odd' q with ⟨ k, rfl | rfl ⟩ <;> ( ( have := hq.sub_right 1 ; norm_num [ Int.ModEq, Int.add_emod, Int.mul_emod ] at *; ) );
  · grind;
  · exact Nat.odd_iff.mpr ( by omega )

/-
If q = -1 mod l, then (q/l) = (-1)^((l-1)/2).
-/
lemma jacobi_q_l_eq_neg_one_pow (q l : ℕ) (hl : l.Prime) (hl_odd : l ≠ 2)
    (h_q_mod_l : (q : ℤ) ≡ -1 [ZMOD l]) :
    jacobiSym q l = (-1 : ℤ) ^ ((l - 1) / 2) := by
      -- Since $q \equiv -1 \pmod{l}$, we have $\left(\frac{q}{l}\right) = \left(\frac{-1}{l}\right)$.
      have h_jacobi_neg_one : jacobiSym (q : ℤ) l = jacobiSym (-1 : ℤ) l := by
        exact jacobiSym.mod_left' h_q_mod_l;
      rw [ h_jacobi_neg_one, jacobiSym.mod_right ];
      · rw [ ← Nat.mod_add_div l 4 ] ; have := Nat.mod_lt l zero_lt_four; interval_cases _ : l % 4 <;> norm_num [ Nat.even_div, Nat.add_mod, Nat.mul_mod ] ;
        simp_all +decide [ ← Nat.dvd_iff_mod_eq_zero, hl.dvd_iff_eq ];
      · exact hl.odd_of_ne_two hl_odd

/-
If q = -1 mod 4p#, then q = -1 mod 8.
-/
lemma q_mod_eight_eq_neg_one (p q : ℕ) (hp : p.Prime)
    (h_q_mod : (q : ℤ) ≡ -1 [ZMOD (4 * primorial p)]) : (q : ℤ) ≡ -1 [ZMOD 8] := by
      refine h_q_mod.of_dvd ?_;
      rcases p with ( _ | _ | _ | _ | p ) <;> simp_all +arith +decide [ primorial ];
      exact dvd_trans ( by norm_num ) ( Finset.dvd_prod_of_mem _ ( show 2 ∈ Finset.filter Nat.Prime ( Finset.range ( p + 5 ) ) from Finset.mem_filter.mpr ⟨ Finset.mem_range.mpr ( by linarith ), by norm_num ⟩ ) )

/-
If q = -1 mod 8, then (2/q) = 1.
-/
lemma jacobi_two_q_eq_one (q : ℕ) (hq : q.Prime) (hq_mod_8 : (q : ℤ) ≡ -1 [ZMOD 8]) :
    jacobiSym 2 q = 1 := by
      rw [ jacobiSym.mod_right ] ; norm_num [ hq_mod_8 ];
      · rw [ ← Nat.mod_add_div q 8, show q % 8 = 7 by exact Nat.cast_injective hq_mod_8 ] ; norm_num;
      · exact hq.odd_of_ne_two <| by rintro rfl; contradiction;

/-
If l <= p and q = -1 mod 4p#, then (l/q) = 1.
-/
lemma jacobi_of_factor_le_p (p q l : ℕ) (hp : p.Prime) (hq : q.Prime) (hl : l.Prime)
    (h_le : l ≤ p) (h_q_mod : (q : ℤ) ≡ -1 [ZMOD (4 * primorial p)]) :
    jacobiSym l q = 1 := by
      by_cases hl_two : l = 2;
      · -- Since $q \equiv -1 \pmod{8}$, we have $\left(\frac{2}{q}\right) = 1$ by `jacobi_two_q_eq_one`.
        have h_jacobi_two_q : jacobiSym 2 q = 1 := by
          apply jacobi_two_q_eq_one q hq (q_mod_eight_eq_neg_one p q hp h_q_mod);
        aesop;
      · -- Since $l$ is an odd prime, we can use the properties of the Jacobi symbol and quadratic reciprocity.
        have h_jacobi : jacobiSym q l = (-1 : ℤ) ^ ((l - 1) / 2) := by
          convert jacobi_q_l_eq_neg_one_pow q l hl hl_two _;
          exact q_mod_l_eq_neg_one p q l hl h_le h_q_mod;
        -- By quadratic reciprocity, we have $\left(\frac{l}{q}\right)\left(\frac{q}{l}\right) = (-1)^{\frac{l-1}{2} \frac{q-1}{2}}$.
        have h_reciprocity : jacobiSym l q * jacobiSym q l = (-1 : ℤ) ^ ((l - 1) / 2 * ((q - 1) / 2)) := by
          rw [ jacobiSym.quadratic_reciprocity ];
          · rcases Nat.even_or_odd' l with ⟨ k, rfl | rfl ⟩ <;> rcases Nat.even_or_odd' q with ⟨ m, rfl | rfl ⟩ <;> norm_num at *;
            · simp_all +decide [ Nat.prime_mul_iff ];
            · simp_all +decide [ Nat.prime_mul_iff ];
            · simp_all +decide [ Nat.prime_mul_iff ];
              norm_num [ Int.modEq_iff_dvd ] at h_q_mod;
              exact absurd ( Int.le_of_dvd ( by decide ) h_q_mod ) ( by linarith [ show ( primorial p : ℤ ) > 0 from Nat.cast_pos.mpr ( Nat.pos_of_ne_zero ( by aesop ) ) ] );
            · norm_num [ Nat.add_div, h_jacobi ];
              by_cases hk : Even k <;> simp_all +decide [ parity_simps ];
          · exact hl.odd_of_ne_two hl_two;
          · exact hq.odd_of_ne_two <| by rintro rfl; exact absurd ( h_q_mod.symm.dvd ) ( by norm_num; intros h; obtain ⟨ k, hk ⟩ := h; replace hk := congr_arg ( · % 4 ) hk ; norm_num [ Int.add_emod, Int.mul_emod ] at hk ) ;
        -- Since $q \equiv -1 \pmod{4}$, we have $\frac{q-1}{2}$ is odd.
        have h_q_mod_four : (q : ℤ) ≡ -1 [ZMOD 4] := by
          exact h_q_mod.of_dvd <| dvd_mul_right _ _
        have h_q_odd : Odd ((q - 1) / 2) := by
          exact odd_div_two_of_mod_four_eq_neg_one q h_q_mod_four;
        by_cases h : Even ( ( l - 1 ) / 2 ) <;> simp_all +decide

/-
If (l/q)=1 for all prime factors l of n, then (n/q)=1.
-/
lemma jacobi_eq_one_of_prime_factors_eq_one {n q : ℕ} (hn : n ≠ 0)
    (h : ∀ l, l.Prime → l ∣ n → jacobiSym l q = 1) : jacobiSym n q = 1 := by
      induction' n using Nat.strongRecOn with n ih;
      by_cases h₁ : n = 1;
      · aesop;
      · obtain ⟨ l, hl₁, hl₂ ⟩ := Nat.exists_prime_and_dvd h₁;
        obtain ⟨ k, rfl ⟩ := hl₂; simp_all +decide [ jacobiSym.mul_left ] ;
        exact ih k ( lt_mul_of_one_lt_left ( Nat.pos_of_ne_zero hn.2 ) hl₁.one_lt ) hn.2 fun p hp hpk => h p hp ( dvd_mul_of_dvd_right hpk _ )

/-
If P(n)=p and q = -1 mod 4p#, then (n/q) = 1.
-/
lemma jacobi_of_P_eq_p (p q n : ℕ) (hp : p.Prime) (hq : q.Prime) (hn : n ≠ 0)
    (h_max_prime : P n = p) (h_q_mod : (q : ℤ) ≡ -1 [ZMOD (4 * primorial p)]) :
    jacobiSym n q = 1 := by
      -- Since $P(n) = p$, all prime factors of $n$ are $\le p$.
      have h_factors_le_p : ∀ l, l.Prime → l ∣ n → l ≤ p := by
        intro l hl hl_div
        have h_prime_factor : l ∈ n.primeFactors := by
          aesop;
        -- Since $P(n) = p$, the greatest prime factor of $n$ is $p$. Therefore, any prime factor $l$ of $n$ must satisfy $l \leq p$.
        have h_max_prime_factor : ∀ l ∈ n.primeFactors, l ≤ (n.primeFactors).max.getD 0 := by
          exact fun x hx => by have := Finset.le_max hx; cases h : n.primeFactors.max <;> aesop;
        exact h_max_prime ▸ h_max_prime_factor l h_prime_factor;
      -- By `jacobi_of_factor_le_p`, for any prime factor $l$ of $n$, we have $\left(\frac{l}{q}\right) = 1$.
      have h_jacobi_l_q : ∀ l, l.Prime → l ∣ n → jacobiSym l q = 1 := by
        exact fun l a a_1 => jacobi_of_factor_le_p p q l hp hq a (h_factors_le_p l a a_1) h_q_mod;
      convert jacobi_eq_one_of_prime_factors_eq_one hn h_jacobi_l_q

/-
If P(n)=p and q = -1 mod 4p#, then n is not -1 mod q.
-/
lemma n_not_equiv_neg_one_mod_q (p q n : ℕ) (hp : p.Prime) (hq : q.Prime) (hn : n ≠ 0)
    (h_max_prime : P n = p) (h_q_mod : (q : ℤ) ≡ -1 [ZMOD (4 * primorial p)]) :
    ¬ ((n : ℤ) ≡ -1 [ZMOD q]) := by
      -- From `jacobi_of_P_eq_p`, we know that $\left(\frac{n}{q}\right) = 1$.
      have h_jacobi : jacobiSym n q = 1 := by
        exact jacobi_of_P_eq_p p q n hp hq hn h_max_prime h_q_mod;
      -- Since $q \equiv -1 \pmod{4p\#}$, we have that $\left(\frac{-1}{q}\right) = -1$.
      have h_jacobi_neg_one : jacobiSym (-1 : ℤ) q = -1 := by
        -- Since $q \equiv -1 \pmod{8}$, we have that $(q : ℤ) \equiv -1 \pmod{4}$.
        have h_q_mod_four : (q : ℤ) ≡ -1 [ZMOD 4] := by
          exact h_q_mod.of_dvd <| dvd_mul_right _ _;
        rw [ jacobiSym.mod_right ] ; norm_num;
        · rw [ ← Nat.mod_add_div q 4 ] at *; have := Nat.mod_lt q zero_lt_four; interval_cases q % 4 <;> norm_num [ Int.ModEq ] at *;
        · exact hq.odd_of_ne_two <| by rintro rfl; contradiction;
      by_contra h_contra;
      have h_jacobi_eq : jacobiSym (n : ℤ) q = jacobiSym (-1 : ℤ) q := by
        have h_cong : (n : ℤ) ≡ -1 [ZMOD q] := by
          exact h_contra
        exact jacobiSym.mod_left' h_contra;
      linarith

/-
For any prime p, there are infinitely many primes q such that no n satisfies P(n)=p and P(n+1)=q.
-/
theorem tong_counterexamples (p : ℕ) (hp : p.Prime) : {q | q.Prime ∧ ¬ ∃ n, P n = p ∧ P (n + 1) = q}.Infinite := by
  -- By `infinite_primes_mod_neg_one` with $k = 4m$, there are infinitely many primes $q \equiv -1 \pmod{4m}$.
  have h_inf : Set.Infinite {q : ℕ | Nat.Prime q ∧ (q : ℤ) ≡ -1 [ZMOD (4 * primorial p)]} := by
    -- Apply the lemma that states there are infinitely many primes congruent to -1 modulo k for k > 2.
    apply infinite_primes_mod_neg_one;
    linarith [ show 1 ≤ primorial p from Nat.pos_of_ne_zero ( by rw [ primorial ] ; exact Finset.prod_ne_zero_iff.mpr fun q hq => Nat.Prime.ne_zero <| by aesop ) ];
  refine Set.Infinite.mono ?_ h_inf;
  intro q hqaesop;
  refine' ⟨ hqaesop.1, _ ⟩;
  rintro ⟨ n, hn₁, hn₂ ⟩;
  -- Since $P(n+1)=q$, we have $q \mid n+1$.
  have hq_div_n1 : q ∣ n + 1 := by
    unfold P at hn₂;
    have := Finset.mem_of_max <| show ( n + 1 |> Nat.primeFactors |> Finset.max ) = some q from by { unfold Option.getD at hn₂; aesop } ; aesop;
  -- By `n_not_equiv_neg_one_mod_q`, $n \not\equiv -1 \pmod q$.
  have hq_not_equiv_neg_one : ¬((n : ℤ) ≡ -1 [ZMOD q]) := by
    apply n_not_equiv_neg_one_mod_q p q n hp hqaesop.left;
    · aesop;
    · assumption;
    · exact hqaesop.2;
  exact hq_not_equiv_neg_one <| Int.ModEq.symm <| Int.modEq_of_dvd <| by simpa [ ← Int.natCast_dvd_natCast ] using hq_div_n1;

/-
Tong's question: For any odd prime q, are there infinitely many primes p such that no n satisfies P(n)=p and P(n+1)=q?
-/
def tong_question : Prop := ∀ q, q.Prime → q % 2 = 1 → {p | p.Prime ∧ ¬ ∃ n, P n = p ∧ P (n + 1) = q}.Infinite

/-
$P(m)=2$ if and only if $m$ is a power of 2 (greater than 1).
-/
lemma P_eq_two_iff_pow_two {m : ℕ} (hm : m ≠ 0) : P m = 2 ↔ ∃ k > 0, m = 2 ^ k := by
  constructor <;> intro h;
  · -- If $P(m)=2$, then the greatest prime factor of $m$ is 2. This means all prime factors of $m$ are $\le 2$. Since 2 is the smallest prime, all prime factors must be 2. Thus $m$ is a power of 2. Let $m = 2^k$ for some $k \geq 0$.
    obtain ⟨k, rfl⟩ : ∃ k, m = 2 ^ k := by
      -- By definition of $P$, we know that every prime factor of $m$ is less than or equal to $2$.
      have h_prime_factors : ∀ p ∈ m.primeFactors, p ≤ 2 := by
        unfold P at h;
        have h_prime_factors : ∀ p ∈ m.primeFactors, p ≤ Finset.max m.primeFactors := by
          exact fun p hp => Finset.le_max hp;
        cases h' : Finset.max m.primeFactors <;> aesop;
      rw [ ← Nat.prod_primeFactorsList hm ] ; rw [ List.prod_eq_pow_single 2 ] ; aesop;
      intro p hp hprime; have := h_prime_factors p ( by aesop ) ; interval_cases p <;> simp_all +decide ;
    exact ⟨ k, Nat.pos_of_ne_zero ( by rintro rfl; exact absurd h ( by native_decide ) ), rfl ⟩;
  · unfold P;
    rcases h with ⟨ k, hk, rfl ⟩ ; rcases k with ( _ | _ | k ) <;> simp_all +decide [ Nat.primeFactors_pow ] ;

/-
If $18 \mid k$, then $73 \mid 2^k - 1$.
-/
lemma seventy_three_dvd_two_pow_sub_one_of_eighteen_dvd {k : ℕ} (hk : 18 ∣ k) : 73 ∣ 2^k - 1 := by
  -- Since $18 \mid k$, we can write $k = 18m$ for some integer $m$.
  obtain ⟨m, rfl⟩ : ∃ m, k = 18 * m := hk;
  rw [ pow_mul ] ; erw [ ← Nat.mod_add_div ( 2 ^ 18 ) 73 ] ; norm_num [ Nat.pow_mod, Nat.add_mod, Nat.mul_mod ] ; induction' m with m IH <;> norm_num [ pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod ] at * ; omega;

/-
If $2^k \equiv 1 \pmod{19}$, then $18 \mid k$.
-/
lemma eighteen_dvd_k_of_pow_two_mod_nineteen_eq_one {k : ℕ} (h : 2^k ≡ 1 [MOD 19]) : 18 ∣ k := by
  exact Nat.dvd_of_mod_eq_zero ( by rw [ ← Nat.mod_add_div k 18 ] at h; norm_num [ Nat.ModEq, Nat.pow_add, Nat.pow_mul, Nat.mul_mod, Nat.pow_mod ] at h; have := Nat.mod_lt k ( by decide : 0 < 18 ) ; interval_cases k % 18 <;> trivial )

/-
There is no integer $n$ such that $P(n)=19$ and $P(n+1)=2$.
-/
theorem sampaio_counterexample : ¬ ∃ n, P n = 19 ∧ P (n + 1) = 2 := by
  -- Assume there exists $n$ such that $P(n)=19$ and $P(n+1)=2$.
  by_contra h
  obtain ⟨n, hn1, hn2⟩ := h;
  -- Since $P(n+1)=2$, by `P_eq_two_iff_pow_two`, $n+1 = 2^k$ for some $k>0$. Thus $n = 2^k - 1$.
  have hn_form : ∃ k > 0, n = 2 ^ k - 1 := by
    -- By `P_eq_two_iff_pow_two`, $n+1 = 2^k$ for some $k>0$. Thus $n = 2^k - 1$.
    have hn1_form : ∃ k > 0, n + 1 = 2 ^ k := by
      exact P_eq_two_iff_pow_two ( Nat.succ_ne_zero _ ) |>.1 hn2;
    exact ⟨ hn1_form.choose, hn1_form.choose_spec.1, eq_tsub_of_add_eq hn1_form.choose_spec.2 ⟩;
  obtain ⟨ k, hk_pos, rfl ⟩ := hn_form; simp_all +decide
  -- Since $P(n)=19$, $19 \mid n$, so $2^k - 1 \equiv 0 \pmod{19}$, which means $2^k \equiv 1 \pmod{19}$.
  have h_mod : 2 ^ k ≡ 1 [MOD 19] := by
    -- Since $P(n)=19$, we know that $19$ divides $n$.
    have h_div : 19 ∣ (2 ^ k - 1) := by
      unfold P at hn1;
      have := Finset.mem_of_max ( show ( 2 ^ k - 1 |> Nat.primeFactors |> Finset.max ) = some 19 from by { rw [ Option.getD_eq_iff ] at hn1; aesop } ) ; aesop;
    simpa [ Nat.modEq_iff_dvd ] using h_div.modEq_zero_nat;
  -- By `eighteen_dvd_k_of_pow_two_mod_nineteen_eq_one`, we have $18 \mid k$.
  have h_div : 18 ∣ k := by
    exact eighteen_dvd_k_of_pow_two_mod_nineteen_eq_one h_mod;
  -- By `seventy_three_dvd_two_pow_sub_one_of_eighteen_dvd`, since $18 \mid k$, we have $73 \mid 2^k - 1$.
  have h_div_73 : 73 ∣ 2 ^ k - 1 := by
    exact seventy_three_dvd_two_pow_sub_one_of_eighteen_dvd h_div;
  -- Since $73$ is a prime factor of $n$ (as $73 \mid n$), we must have $73 \le 19$, which is a contradiction.
  have h_contra : 73 ∈ (2 ^ k - 1).primeFactors := by
    norm_num +zetaDelta at *;
    exact ⟨ h_div_73, Nat.sub_ne_zero_of_lt ( one_lt_pow₀ ( by decide ) hk_pos.ne' ) ⟩;
  have h_contra : (2 ^ k - 1).primeFactors.max.getD 0 ≥ 73 := by
    have h_contra : ∀ {s : Finset ℕ}, 73 ∈ s → s.max.getD 0 ≥ 73 := by
      intros s hs; exact (by
      have h_contra : ∀ {s : Finset ℕ}, 73 ∈ s → s.max.getD 0 ≥ 73 := by
        intros s hs
        have h_max : s.max ≤ s.max.getD 0 := by
          cases h : s.max <;> aesop
        exact Nat.cast_le.mp ( le_trans ( Finset.le_max hs ) h_max );
      exact h_contra hs);
    exact h_contra ‹_›;
  unfold P at * ; aesop

/-
A strange pair is a pair of distinct primes p and q such that there is no integer n >= 2 for which P(n) P(n + 1) = pq.
-/
def StrangePair (p q : ℕ) : Prop :=
  p.Prime ∧ q.Prime ∧ p ≠ q ∧ ∀ n ≥ 2, P n * P (n + 1) ≠ p * q

lemma P_mul_P_eq_mul_prime_factors {p q n : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
  (h : P n * P (n + 1) = p * q) :
  (P n = p ∧ P (n + 1) = q) ∨ (P n = q ∧ P (n + 1) = p) := by
    -- Since $p$ and $q$ are distinct primes, their product $pq$ can only be factored into primes as $p$ and $q$.
    have h_factors : ∀ {x y : ℕ}, Nat.Prime x → Nat.Prime y → x * y = p * q → (x = p ∧ y = q) ∨ (x = q ∧ y = p) := by
      intro x y hx hy hxy; have := Nat.Prime.dvd_mul hx |>.1 ( hxy ▸ dvd_mul_right _ _ ) ; have := Nat.Prime.dvd_mul hy |>.1 ( hxy ▸ dvd_mul_left _ _ ) ; simp_all +decide [ Nat.prime_dvd_prime_iff_eq ] ;
      aesop;
    -- Apply the fact that $P(n)$ and $P(n+1)$ are primes.
    have h_prime_factors : Nat.Prime (P n) ∧ Nat.Prime (P (n + 1)) := by
      unfold P at *;
      rcases x : n.primeFactors.max with ( _ | x ) <;> rcases y : ( n + 1 ).primeFactors.max with ( _ | y ) <;> simp_all +decide
      · aesop;
      · aesop;
      · aesop;
      · exact ⟨ Nat.prime_of_mem_primeFactors <| Finset.mem_of_max x, Nat.prime_of_mem_primeFactors <| Finset.mem_of_max y ⟩;
    exact h_factors h_prime_factors.1 h_prime_factors.2 h

/-
If $a^k = -1$ in $\mathbb{Z}/n\mathbb{Z}$ with $n > 2$, then the order of $a$ divides $2k$ but not $k$.
-/
lemma order_properties_of_neg_one {n : ℕ} (hn : n > 2) {a : ZMod n} {k : ℕ} (h : a^k = -1) : orderOf a ∣ 2 * k ∧ ¬ orderOf a ∣ k := by
  norm_num [ orderOf_dvd_iff_pow_eq_one ];
  simp_all +decide [ pow_mul' ];
  intro h'; rcases n with ( _ | _ | _ | n ) <;> simp_all +decide [ ZMod, Fin.ext_iff ] ;

/-
If $\ord_{q_1}(a)=\ord_{q_2}(a)$ and $a^k \equiv -1 \pmod{q_1}$, then $a^k \equiv -1 \pmod{q_2}$.
-/
lemma same_order_neg_one_power {q1 q2 : ℕ} (hq2 : q2.Prime) (h_odd1 : q1 > 2)
  (a : ℕ) (k : ℕ)
  (h_ord : orderOf (a : ZMod q1) = orderOf (a : ZMod q2))
  (h_pow : (a : ZMod q1)^k = -1) :
  (a : ZMod q2)^k = -1 := by
    -- By `order_properties_of_neg_one`, we know that `orderOf (a : ZMod q1) 2 * k` and `orderOf (a : ZMod q1) ∤ k`.
    have h_div : orderOf (a : ZMod q1) ∣ 2 * k ∧ ¬orderOf (a : ZMod q1) ∣ k := by
      exact order_properties_of_neg_one h_odd1 h_pow;
    simp_all +decide [ orderOf_dvd_iff_pow_eq_one ];
    haveI := Fact.mk hq2; exact Or.resolve_left ( eq_or_eq_neg_of_sq_eq_sq _ _ <| by linear_combination' h_div.1 ) h_div.2;

/-
If the greatest prime factor of $n$ is 2, then $n$ is a power of 2.
-/
lemma P_eq_2_implies_power_two {n : ℕ} (h : P n = 2) : ∃ k : ℕ, n = 2^k := by
  by_cases hn : n = 0;
  · simp_all +decide [ P ];
  · unfold P at h;
    -- Since $P(n) = 2$, we have that the maximum prime factor of $n$ is 2. This implies that all prime factors of $n$ are 2.
    have h_prime_factors : n.primeFactors ⊆ {2} := by
      have h_prime_factors : ∀ p ∈ n.primeFactors, p ≤ 2 := by
        have h_prime_factors : ∀ p ∈ n.primeFactors, p ≤ Finset.max n.primeFactors := by
          exact fun p hp => Finset.le_max hp;
        cases h' : n.primeFactors.max <;> aesop;
      intro p hp; specialize h_prime_factors p hp; interval_cases p <;> simp_all +decide ;
    rw [ ← Nat.factorization_prod_pow_eq_self hn ] ; exact ⟨ n.factorization 2, by rw [ Finsupp.prod ] ; aesop ⟩ ;

/-
Under the assumptions, it is impossible that $P(n)=2$ and $P(n+1)=q_1$.
-/
lemma case1_impossible {q1 q2 n : ℕ} (hq1 : q1.Prime) (hq2 : q2.Prime)
  (h_odd1 : q1 > 2)
  (h_q1_lt_q2 : q1 < q2)
  (h_ord : orderOf (2 : ZMod q1) = orderOf (2 : ZMod q2))
  (hPn : P n = 2) (hPn1 : P (n + 1) = q1) : False := by
    -- Since $P(n)=2$, $n=2^k$ for some $k$. Since $P(n+1)=q_1 �$,� $q_1 \mid n+1 = 2^k+1$.
    obtain ⟨k, hk⟩ : ∃ k : ℕ, n = 2^k := by
      exact P_eq_2_implies_power_two hPn
    have hq1_div : q1 ∣ 2^k + 1 := by
      unfold P at hPn1;
      replace hPn1 := Finset.mem_of_max ( show ( n + 1 |> Nat.primeFactors |> Finset.max ) = some q1 from by { unfold Option.getD at hPn1; aesop } ) ; aesop;
    -- Thus $2^k \equiv -1 \pmod{q_2}$. Thus $q_2 \mid 2^k+1 = n+1$.
    have hq2_div : q2 ∣ 2^k + 1 := by
      have hq2_div : (2 : ZMod q2)^k = -1 := by
        have hq1_cong : (2 ^ k : ZMod q1) = -1 := by
          exact eq_neg_of_add_eq_zero_left ( by simpa [ ← ZMod.natCast_eq_zero_iff ] using hq1_div );
        have := same_order_neg_one_power hq2 h_odd1 2 k h_ord hq1_cong; aesop;
      simp_all +decide [ ← ZMod.natCast_eq_zero_iff ];
    -- So $P(n+1) \ge q_2$.
    have hPn1_ge_q2 : q2 ≤ P (2^k + 1) := by
      -- Since $q2$ is a prime factor of $2^k + 1$, it must be less than or equal to the maximum prime factor of $2^k + 1$.
      have hq2_le_max_prime_factor : q2 ≤ (2^k + 1).primeFactors.max.getD 0 := by
        have hq2_prime_factor : q2 ∈ (2^k + 1).primeFactors := by
          aesop
        have hq2_le_max_prime_factor : ∀ {S : Finset ℕ}, q2 ∈ S → q2 ≤ S.max.getD 0 := by
          intros S hq2_in_S; exact (by
          have := Finset.le_max hq2_in_S; cases h : Finset.max S <;> aesop;);
        exact hq2_le_max_prime_factor hq2_prime_factor;
      exact hq2_le_max_prime_factor;
    grind

/-
Under the assumptions, it is impossible that $P(n)=q_1$ and $P(n+1)=2$.
-/
lemma case2_impossible {q1 q2 n : ℕ} (hq1 : q1.Prime) (hq2 : q2.Prime)
  (h_odd1 : q1 > 2)
  (h_q1_lt_q2 : q1 < q2)
  (h_ord : orderOf (2 : ZMod q1) = orderOf (2 : ZMod q2))
  (hPn : P n = q1) (hPn1 : P (n + 1) = 2) : False := by
    -- Since $P(n+1)=2 �$,� $n+1=2^k$ for some $k$.
    obtain ⟨k, hk⟩ : ∃ k, n + 1 = 2 ^ k := by
      exact P_eq_2_implies_power_two hPn1;
    -- Since $q1 \mid n = 2^k - 1$, we have $2^k \equiv 1 \p �mod�{q1}$.
    have h_mod_q1 : 2 ^ k ≡ 1 [MOD q1] := by
      refine Nat.ModEq.symm <| Nat.modEq_of_dvd ?_;
      simp +decide [ ← hk ];
      -- Since $q1$ is the greatest prime factor of $n$, it must divide $n$.
      have h_div : q1 ∈ n.primeFactors := by
        unfold P at hPn;
        have hq1_div_n : n.primeFactors.max = some q1 := by
          unfold Option.getD at hPn; aesop;
        exact Finset.mem_of_max hq1_div_n;
      exact_mod_cast Nat.dvd_of_mem_primeFactors h_div;
    -- Since $\ord_{q_2}(2)=s$, $s$ is the order of 2 mod $q_2$. Thus $2^k \equiv 1 � \�pmod{q_2}$.
    have h_mod_q2 : 2 ^ k ≡ 1 [MOD q2] := by
      simp_all +decide [ ← ZMod.natCast_eq_natCast_iff ];
      rw [ ← orderOf_dvd_iff_pow_eq_one ] at * ; aesop;
    -- Since $q2 \mid 2^k - 1 = n$, we have $P(n) \ge q2 �$�.
    have h_div_q2 : q2 ∣ n := by
      rw [ ← Int.natCast_dvd_natCast ] ; simpa [ ← hk ] using h_mod_q2.symm.dvd;
    -- Since $q2 \mid n$, we have $P(n) \ge q2$.
    have h_Pn_ge_q2 : P n ≥ q2 := by
      have h_Pn_ge_q2 : q2 ∈ n.primeFactors := by
        rcases n with ( _ | _ | n ) <;> simp_all +decide
        cases hPn.symm.trans ( by native_decide : P 0 = 0 );
        contradiction;
      have h_Pn_ge_q2 : ∀ {S : Finset ℕ}, q2 ∈ S → S.max.getD 0 ≥ q2 := by
        intros S hS; exact (by
        have := Finset.le_max hS; cases h : S.max <;> aesop;);
      (expose_names; exact h_Pn_ge_q2 h_Pn_ge_q2_1);
    linarith

/-
Let $2<q_1<q_2$ be primes. If $\ord_{q_1}(2)=\ord_{q_2}(2)$, then the pair $\{2,q_1\}$ is strange.
-/
lemma equal_order_strange {q1 q2 : ℕ} (hq1 : q1.Prime) (hq2 : q2.Prime) (h_order : 2 < q1) (h_q1_lt_q2 : q1 < q2) (h_eq_ord : orderOf (2 : ZMod q1) = orderOf (2 : ZMod q2)) : StrangePair 2 q1 := by
  refine' ⟨ Nat.prime_two, hq1, _, _ ⟩;
  · linarith;
  · -- Assume, for contradiction, that $\{2,q_1\}$ is not strange. Then there exists $n\ge 2 �$� such that
    -- \[
    -- F(n)\,F(n+1)=2q_1.
    -- \]
    intro n hn
    by_contra h_contra
    have h_cases : P n = 2 ∧ P (n + 1) = q1 ∨ P n = q1 ∧ P (n + 1) = 2 := by
      have := P_mul_P_eq_mul_prime_factors Nat.prime_two hq1 ( by linarith ) h_contra; aesop;
    cases h_cases <;> simp_all +decide;
    · exact case1_impossible hq1 hq2 h_order ( by linarith ) h_eq_ord ( by tauto ) ( by tauto );
    · apply case2_impossible hq1 hq2 h_order ( by linarith ) h_eq_ord ( by tauto ) ( by tauto )

/-
For a prime $p > 5$, $N = 2^{2p} + 1$ satisfies $N \equiv 2 \pmod 3$, $N \equiv 0 \pmod 5$, and $N \not\equiv 0 \pmod{25}$.
-/
lemma N_mod_3_and_5 {p : ℕ} (hp : p.Prime) (hp5 : p > 5) :
  (2^(2*p) + 1) % 3 = 2 ∧ (2^(2*p) + 1) % 5 = 0 ∧ (2^(2*p) + 1) % 25 ≠ 0 := by
    norm_num [ Nat.pow_mul, Nat.add_mod, Nat.pow_mod ];
    rw [ ← Nat.mod_add_div p 20 ] at *; have := Nat.mod_lt p ( by decide : 0 < 20 ) ; interval_cases p % 20 <;> norm_num [ Nat.pow_add, Nat.pow_mul, Nat.mul_mod, Nat.pow_mod ] at *;
    all_goals have := Nat.Prime.eq_two_or_odd hp; norm_num [ Nat.add_mod, Nat.mul_mod, Nat.dvd_iff_mod_eq_zero ] at this;
    any_goals omega;
    · norm_num [ show 5 + 20 * ( p / 20 ) = 5 * ( 1 + 4 * ( p / 20 ) ) by ring, Nat.prime_mul_iff ] at hp;
      interval_cases p;
    · norm_num [ show 15 + 20 * ( p / 20 ) = 5 * ( 3 + 4 * ( p / 20 ) ) by ring, Nat.prime_mul_iff ] at hp;
      omega

/-
$2^{2p} + 1$ factors as $(2^p - 2^r + 1)(2^p + 2^r + 1)$ where $r = (p+1)/2$.
-/
lemma N_factorization {p : ℕ} (hp : Odd p) :
  let r := (p + 1) / 2
  let A := 2^p - 2^r + 1
  let B := 2^p + 2^r + 1
  2^(2*p) + 1 = A * B := by
    obtain ⟨ k, rfl ⟩ : ∃ k, p = 2 * k + 1 := hp; ring_nf;
    norm_num [ Nat.add_div ] ; ring_nf;
    zify ; ring_nf;
    rw [ Nat.cast_sub ( by gcongr <;> linarith ) ] ; push_cast ; ring

/-
The factors $A = 2^p - 2^r + 1$ and $B = 2^p + 2^r + 1$ are coprime.
-/
lemma N_factors_coprime {p : ℕ} (hp : Odd p) :
  let r := (p + 1) / 2
  let A := 2^p - 2^r + 1
  let B := 2^p + 2^r + 1
  Nat.gcd A B = 1 := by
    -- Since $B - A = 2 �^{�r+1}$ and $A$ is odd, any common divisor of $A$ and $B$ must also divide $2^{r+1}$. However, since $A$ is odd, the only possible common divisor is $1$.
    have h_div : ∀ d, d ∣ (2 ^ p - 2 ^ ((p + 1) / 2) + 1) → d ∣ (2 ^ p + 2 ^ ((p + 1) / 2) + 1) → d ∣ 2 ^ ((p + 1) / 2 + 1) := by
      intro d hd₁ hd₂; convert Nat.dvd_sub hd₂ hd₁ using 1; rw [ Nat.sub_eq_of_eq_add ] ; ring_nf;
      linarith [ Nat.sub_add_cancel ( show 2 ^ p ≥ 2 ^ ( ( 1 + p ) / 2 ) from pow_le_pow_right₀ ( by decide ) ( Nat.div_le_of_le_mul <| by linarith [ hp.pos ] ) ) ];
    have h_odd : Odd (2 ^ p - 2 ^ ((p + 1) / 2) + 1) := by
      norm_num [ Nat.one_le_iff_ne_zero, parity_simps ];
      exact even_iff_two_dvd.mpr ( Nat.dvd_sub ( dvd_pow_self _ hp.pos.ne' ) ( dvd_pow_self _ ( Nat.ne_of_gt ( Nat.div_pos ( by linarith [ hp.pos ] ) zero_lt_two ) ) ) );
    have := h_div _ ( Nat.gcd_dvd_left _ _ ) ( Nat.gcd_dvd_right _ _ ) ; ( have := Nat.dvd_gcd ( Nat.gcd_dvd_left _ _ ) this; simp_all +decide [ Nat.Coprime, Nat.Coprime.gcd_eq_one ] ; )

/-
Neither $A$ nor $B$ is divisible by 3, and exactly one of them is divisible by 5 (but not 25).
-/
lemma N_factors_divisibility {p : ℕ} (hp : p.Prime) (hp5 : p > 5) :
  let r := (p + 1) / 2
  let A := 2^p - 2^r + 1
  let B := 2^p + 2^r + 1
  ¬(3 ∣ A) ∧ ¬(3 ∣ B) ∧ ((5 ∣ A ∧ ¬(25 ∣ A) ∧ ¬(5 ∣ B)) ∨ (5 ∣ B ∧ ¬(25 ∣ B) ∧ ¬(5 ∣ A))) := by
    -- Since $N = A \cdot B$ and $N \equiv 0 \pmod 5$, $5 \mid N$ but $25 \nmid N$.
    have h_mod_5 : let A := 2^p - 2^((p + 1) / 2) + 1; let B := 2^p + 2^((p + 1) / 2) + 1; (5 ∣ A ∧ ¬25 ∣ A ∧ ¬5 ∣ B) ∨ (5 ∣ B ∧ ¬25 ∣ B ∧ ¬5 ∣ A) := by
      have h_mod_5 : (2^(2*p) + 1) % 5 = 0 ∧ (2^(2*p) + 1) % 25 ≠ 0 := by
        exact N_mod_3_and_5 hp hp5 |>.2;
      have h_mod_5 : let A := 2^p - 2^((p + 1) / 2) + 1; let B := 2^p + 2^((p + 1) / 2) + 1; (A * B) % 5 = 0 ∧ (A * B) % 25 ≠ 0 := by
        convert h_mod_5 using 2;
        · rw [ ← N_factorization ( show Odd p from hp.odd_of_ne_two <| by linarith ) ];
        · rw [ show ( 2 ^ ( 2 * p ) + 1 : ℕ ) = ( 2 ^ p - 2 ^ ( ( p + 1 ) / 2 ) + 1 ) * ( 2 ^ p + 2 ^ ( ( p + 1 ) / 2 ) + 1 ) from ?_ ];
          convert N_factorization ( show Odd p from hp.odd_of_ne_two <| by linarith ) using 1;
      by_cases h5A : 5 ∣ (2^p - 2^((p + 1) / 2) + 1) <;> by_cases h5B : 5 ∣ (2^p + 2^((p + 1) / 2) + 1) <;> simp_all +decide
      · exact h_mod_5.2 ( Nat.mod_eq_zero_of_dvd ( dvd_trans ( by decide ) ( mul_dvd_mul h5A h5B ) ) );
      · exact fun h => h_mod_5.2 <| Nat.mod_eq_zero_of_dvd <| dvd_trans h <| dvd_mul_right _ _;
      · exact fun h => h_mod_5.2 <| Nat.mod_eq_zero_of_dvd <| dvd_trans h <| dvd_mul_left _ _;
      · exact absurd ( Nat.Prime.dvd_mul ( by norm_num : Nat.Prime 5 ) |>.1 ( Nat.dvd_of_mod_eq_zero h_mod_5.1 ) ) ( by tauto );
    -- Since $N = A \cdot B$ and $N \equiv 2 \pmod 3$, $3 \nmid N$, so $3 \nmid A$ and $3 \nmid B$.
    have h_mod_3 : let A := 2^p - 2^((p + 1) / 2) + 1; let B := 2^p + 2^((p + 1) / 2) + 1; ¬(3 ∣ A) ∧ ¬(3 ∣ B) := by
      have h_mod_3 : let A := 2^p - 2^((p + 1) / 2) + 1; let B := 2^p + 2^((p + 1) / 2) + 1; (A * B) % 3 = 2 := by
        convert N_mod_3_and_5 hp hp5 |>.1 using 1;
        rw [ N_factorization ( show Odd p from hp.odd_of_ne_two <| by linarith ) ];
      exact ⟨ fun h => by have := Nat.mod_eq_zero_of_dvd h; simp_all +decide [ Nat.mul_mod ], fun h => by have := Nat.mod_eq_zero_of_dvd h; simp_all +decide [ Nat.mul_mod ] ⟩;
    exact ⟨ h_mod_3.1, h_mod_3.2, h_mod_5 ⟩

/-
For $p \ge 7$, the factors $A$ and $B$ are strictly greater than 5.
-/
lemma N_factors_large {p : ℕ} (hp : p ≥ 7) :
  let r := (p + 1) / 2
  let A := 2^p - 2^r + 1
  let B := 2^p + 2^r + 1
  A > 5 ∧ B > 5 := by
    refine ⟨ ?_, ?_ ⟩ <;> norm_num [ Nat.pow_succ' ] at *;
    · refine lt_add_of_le_of_pos ( Nat.le_sub_of_add_le ?_ ) zero_lt_one;
      rcases Nat.even_or_odd' p with ⟨ c, rfl | rfl ⟩ <;> norm_num [ Nat.add_div ];
      · rw [ pow_mul' ] ; nlinarith [ Nat.pow_le_pow_right ( by decide : 1 ≤ 2 ) ( by linarith : c ≥ 3 ) ];
      · ring_nf;
        rw [ pow_mul ] ; nlinarith [ Nat.pow_le_pow_right ( by decide : 1 ≤ 2 ) ( by linarith : c ≥ 3 ) ];
    · linarith [ pow_le_pow_right₀ ( by decide : 1 ≤ 2 ) hp, pow_pos ( by decide : 0 < 2 ) ( ( p + 1 ) / 2 ) ]

/-
If $n > 1$ is odd and not divisible by 3 or 5, then it has a prime factor greater than 5.
-/
lemma exists_prime_gt_five {n : ℕ} (h_odd : Odd n) (h_not_3 : ¬ 3 ∣ n) (h_not_5 : ¬ 5 ∣ n) (h_gt_1 : n > 1) :
  ∃ q, q.Prime ∧ q ∣ n ∧ q > 5 := by
    -- Since $n$ is odd and greater than 1, it must � have� at least one prime factor. Let $q$ be � the� smallest prime factor of $n$.
    obtain ⟨q, hq_prime, hq_div⟩ : ∃ q, Nat.Prime q ∧ q ∣ n := by
      exact Nat.exists_prime_and_dvd h_gt_1.ne';
    rcases q with ( _ | _ | _ | _ | _ | _ | q ) <;> simp_all +arith +decide
    · exact absurd ( even_iff_two_dvd.mpr hq_div ) ( by simpa using h_odd );
    · exact ⟨ _, hq_prime, hq_div, by linarith ⟩

set_option maxHeartbeats 0 in
/-
Let $p>5$ be a prime and set $N=2^{2p}+1$. Then $N$ has at least two distinct prime divisors greater than $5$.
-/
lemma two_large_primes {p : ℕ} (hp : p.Prime) (hp5 : p > 5) :
  ∃ q1 q2 : ℕ, q1.Prime ∧ q2.Prime ∧ q1 ≠ q2 ∧ q1 > 5 ∧ q2 > 5 ∧ q1 ∣ (2^(2*p) + 1) ∧ q2 ∣ (2^(2*p) + 1) := by
    -- Let $r = (p+1)/2$, $A = 2^p - 2^r + 1$, and $B = 2^p + 2^r + 1$.
    set r := (p + 1) / 2
    set A := 2^p - 2^r + 1
    set B := 2^p + 2^r + 1
    have hN : 2^(2*p) + 1 = A * B := by
      convert N_factorization ( show Odd p from hp.odd_of_ne_two <| by linarith ) using 1
    have h_coprime : Nat.gcd A B = 1 := by
      apply N_factors_coprime; exact hp.odd_of_ne_two (by linarith)
    have h_divisibility : ¬(3 ∣ A) ∧ ¬(3 ∣ B) ∧ ((5 ∣ A ∧ ¬(25 ∣ A) ∧ ¬(5 ∣ B)) ∨ (5 ∣ B ∧ ¬(25 ∣ B) ∧ ¬(5 ∣ A))) := by
      exact N_factors_divisibility hp hp5
    have h_large : A > 5 ∧ B > 5 := by
      exact N_factors_large ( show p ≥ 7 by contrapose! hp5; interval_cases p <;> trivial ) |> fun h => ⟨ h.1, h.2 ⟩;
    -- Case 1: $5 \mid A$. Then $5 \nmid B$.
    by_cases h5A : 5 ∣ A;
    · -- Since $A$ is divisible by 5, $ �A�/5$ is odd and greater than 1. Also �,� $A$ is not divisible by 3 or 25.
      have hA_div_5 : ∃ q1 : ℕ, Nat.Prime q1 ∧ q1 ∣ A / 5 ∧ q1 > 5 := by
        -- Since $A/5$ is odd and greater � than� 1, it must have a prime factor greater � than� 5.
        have hA_div_5_odd : Odd (A / 5) := by
          have hA_odd : Odd A := by
            simp +zetaDelta at *;
            cases le_total ( 2 ^ p ) ( 2 ^ ( ( p + 1 ) / 2 ) ) <;> simp_all +decide [ Nat.one_le_iff_ne_zero, parity_simps ];
          exact hA_odd.of_dvd_nat ( Nat.div_dvd_of_dvd h5A )
        have hA_div_5_gt_1 : 1 < A / 5 := by
          omega
        have hA_div_5_not_div_3 : ¬(3 ∣ A / 5) := by
          exact fun h => h_divisibility.1 ( dvd_trans h ( Nat.div_dvd_of_dvd h5A ) )
        have hA_div_5_not_div_5 : ¬(5 ∣ A / 5) := by
          omega
        have hA_div_5_prime_factor : ∃ q1 : ℕ, Nat.Prime q1 ∧ q1 ∣ A / 5 ∧ q1 > 5 := by
          apply exists_prime_gt_five; assumption; assumption; assumption; assumption;
        exact hA_div_5_prime_factor;
      obtain ⟨q1, hq1⟩ := hA_div_5
      use q1, Nat.minFac B;
      -- Since $B$ is not divisible by 3 or 5, its minimal prime factor must be greater than 5.
      have hB_min_fac_gt_5 : Nat.minFac B > 5 := by
        by_contra h_contra
        have hB_div_3_or_5 : 3 ∣ B ∨ 5 ∣ B := by
          have := Nat.minFac_prime ( by linarith : B ≠ 1 ) ; ( have := Nat.minFac_dvd B; ( interval_cases _ : Nat.minFac B <;> simp_all +decide ) );
          simp +zetaDelta at *;
          norm_num [ Nat.dvd_iff_mod_eq_zero, Nat.add_mod, Nat.pow_mod, hp.ne_zero ] at this;
          norm_num [ Nat.zero_pow ( Nat.div_pos ( by linarith : p + 1 ≥ 2 ) zero_lt_two ) ] at this
        aesop;
      exact ⟨ hq1.1, Nat.minFac_prime ( by linarith ), fun h => by have := Nat.dvd_gcd ( show q1 ∣ A from dvd_trans hq1.2.1 ( Nat.div_dvd_of_dvd h5A ) ) ( show q1 ∣ B from h.symm ▸ Nat.minFac_dvd _ ) ; aesop, hq1.2.2, hB_min_fac_gt_5, dvd_trans hq1.2.1 ( Nat.div_dvd_of_dvd h5A ) |> fun x => dvd_trans x ( hN.symm ▸ dvd_mul_right _ _ ), Nat.minFac_dvd _ |> fun x => dvd_trans x ( hN.symm ▸ dvd_mul_left _ _ ) ⟩;
    · -- Since $5 \mid B$, we can apply `exists_prime_gt_five` to $B/5$ to find a prime factor $ �q�_1 > 5$.
      obtain ⟨q1, hq1⟩ : ∃ q1 : ℕ, Nat.Prime q1 ∧ q1 ∣ B / 5 ∧ q1 > 5 := by
        apply exists_prime_gt_five;
        · rcases h_divisibility.2.2 with h | h <;> simp_all +decide
          simp +zetaDelta at *;
          rcases h.1 with ⟨ k, hk ⟩ ; simp_all +decide [ parity_simps ];
          replace hk := congr_arg Even hk; simp_all +decide [ parity_simps ] ;
          cases p <;> aesop;
        · omega;
        · omega;
        · grind;
      -- Since $A$ is not divisible by 3 or 5, and $A > 5$, it must have a prime factor greater � than� 5.
      obtain ⟨q2, hq2⟩ : ∃ q2 : ℕ, Nat.Prime q2 ∧ q2 ∣ A ∧ q2 > 5 := by
        apply exists_prime_gt_five;
        · rw [ Nat.odd_add, Nat.odd_sub ] <;> norm_num [ Nat.even_pow ];
          · grind;
          · exact pow_le_pow_right₀ ( by decide ) ( Nat.div_le_of_le_mul <| by linarith );
        · tauto;
        · assumption;
        · linarith;
      use q1, q2;
      exact ⟨ hq1.left, hq2.left, fun h => by have := Nat.dvd_gcd ( hq2.right.left ) ( h.symm ▸ hq1.right.left.trans ( Nat.div_dvd_of_dvd ( show 5 ∣ B from h_divisibility.right.right.elim ( fun h => by tauto ) fun h => by tauto ) ) ) ; aesop, hq1.right.right, hq2.right.right, hN.symm ▸ dvd_mul_of_dvd_right ( hq1.right.left.trans ( Nat.div_dvd_of_dvd ( show 5 ∣ B from h_divisibility.right.right.elim ( fun h => by tauto ) fun h => by tauto ) ) ) _, hN.symm ▸ dvd_mul_of_dvd_left hq2.right.left _ ⟩

/-
Let $p>5$ be a prime, let $N=2^{2p}+1$, and let $q>5$ be a prime divisor of $N$. Then $\ord_q(2)=4p$.
-/
lemma order_4p {p q : ℕ} (hp : p.Prime) (hp5 : p > 5) (hq : q.Prime) (hq5 : q > 5) (h_div : q ∣ 2^(2*p) + 1) :
  orderOf (2 : ZMod q) = 4 * p := by
    refine' orderOf_eq_of_pow_and_pow_div_prime _ _ _;
    · linarith;
    · haveI := Fact.mk hq; simp_all +decide [ ← ZMod.natCast_eq_zero_iff, pow_mul' ] ;
      linear_combination' h_div * ( ( 2 ^ p ) ^ 2 - 1 );
    · intro r hr hr' hr''; haveI := Fact.mk hq; simp_all +decide [ ← ZMod.natCast_eq_zero_iff ] ;
      -- Since $r$ is a prime divisor of $4p$, and $p$ is prime and greater than 5, $r$ must be 2 � or� $p$.
      have hr_cases : r = 2 ∨ r = p := by
        have hr_cases : r ∣ 4 * p := by
          simp_all +decide [ ← ZMod.natCast_eq_zero_iff ];
        rw [ Nat.Prime.dvd_mul hr ] at hr_cases;
        exact Or.imp ( fun h => by have := Nat.le_of_dvd ( by linarith ) h; interval_cases r <;> trivial ) ( fun h => by rw [ Nat.prime_dvd_prime_iff_eq ] at h <;> tauto ) hr_cases;
      rcases hr_cases with ( rfl | rfl ) <;> simp_all +decide [ pow_mul' ];
      · norm_num [ show 4 * p / 2 = 2 * p by rw [ Nat.div_eq_of_eq_mul_left zero_lt_two ] ; ring ] at hr'' ; simp_all +decide [ pow_mul', pow_two ];
        rcases q with ( _ | _ | _ | q ) <;> cases h_div <;> contradiction;
      · norm_num [ hp.ne_zero ] at hr'';
        rcases q with ( _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | q ) <;> cases hr'' <;> contradiction

/-
For every prime $p > 5$, there exists a prime $q$ such that $\{2, q\}$ is a strange pair and $\ord_q(2) = 4p$.
-/
lemma exists_strange_q_for_p {p : ℕ} (hp : p.Prime) (hp5 : p > 5) :
  ∃ q, StrangePair 2 q ∧ orderOf (2 : ZMod q) = 4 * p := by
    obtain ⟨ q1, q2, hq1, hq2, hne, hgt1, hgt2, hdvd1, hdvd2 ⟩ := two_large_primes hp hp5; simp_all +decide
    -- By `order_4p`, $\ord_{q_1}(2) = 4p$ and $\ord_{q_2}(2) = 4p$.
    have h_order_q1 : orderOf (2 : ZMod q1) = 4 * p := by
      apply order_4p hp hp5 hq1 hgt1 hdvd1
    have h_order_q2 : orderOf (2 : ZMod q2) = 4 * p := by
      convert order_4p hp hp5 hq2 hgt2 hdvd2 using 1;
    cases lt_or_gt_of_ne hne <;> [ exact ⟨ q1, equal_order_strange hq1 hq2 ( by linarith ) ( by linarith ) ( by aesop ), h_order_q1 ⟩ ; exact ⟨ q2, equal_order_strange hq2 hq1 ( by linarith ) ( by linarith ) ( by aesop ), h_order_q2 ⟩ ]

/-
There are infinitely many primes $q$ such that $\{2, q\}$ is a strange pair.
-/
theorem infinite_strange_pairs : { q | StrangePair 2 q }.Infinite := by
  -- The set of primes is infinite, and the set of primes greater than 5 is also infinite. Therefore, the image of this set under an injective function is also infinite.
  have h_infinite_primes_gt_5 : Set.Infinite {n : ℕ | n.Prime ∧ n > 5} := by
    exact Set.Infinite.mono ( by aesop_cat ) ( Nat.infinite_setOf_prime.diff ( Set.finite_le_nat 5 ) );
  rw [ Set.infinite_iff_exists_gt ] at *;
  -- For any prime $p > 5$, we can find a prime $ �q�$ such that $\{2, q\}$ is a strange pair and $\ord_q(2) = 4p$.
  have h_exists_q : ∀ p : ℕ, Nat.Prime p → 5 < p → ∃ q : ℕ, StrangePair 2 q ∧ orderOf (2 : ZMod q) = 4 * p ∧ q > p := by
    intro p hp hp5
    obtain ⟨q, hq⟩ := exists_strange_q_for_p hp hp5
    use q;
    -- Since $q$ divides $2^{4p} - 1$, the order of $2$ modulo $q$ must divide $q - 1$.
    have h_div : orderOf (2 : ZMod q) ∣ q - 1 := by
      rw [ orderOf_dvd_iff_pow_eq_one ];
      haveI := Fact.mk hq.1.2.1; simpa [ ← ZMod.natCast_eq_zero_iff ] using ZMod.pow_card_sub_one_eq_one ( by intro h; simp_all +decide ) ;
    rcases q with ( _ | _ | q ) <;> simp_all +decide;
    · exact absurd hq.1.2.1 ( by norm_num );
    · cases hq.1.2.1 ; contradiction;
    · linarith [ Nat.le_of_dvd ( Nat.succ_pos _ ) h_div ];
  exact fun a => by obtain ⟨ p, hp₁, hp₂ ⟩ := h_infinite_primes_gt_5 a; obtain ⟨ q, hq₁, hq₂, hq₃ ⟩ := h_exists_q p hp₁.left hp₁.right; exact ⟨ q, hq₁, by linarith ⟩ ;
