/-

This is a Lean formalization of a solution to Erdős Problem 415.
https://www.erdosproblems.com/forum/thread/415

The original proof was found by: Erdős, Graham, Ivić, and Pomerance.

[EGIP96] Erdős, Paul and Graham, S. W. and Ivi\'c, Aleksandar and
Pomerance, Carl, On the number of divisors of {$n!$}. (1996),
337--355.


Aristotle auto-formalized a proof of the same result by Mehtaab
Sawhney (see the forum link above).


The proof is verified by Lean.  The following version numbers were
used:

Lean Toolchain version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7 (v4.24.0)

-/


/-
We define `u n` as the ratio $\tau((n+1)!)/\tau(n!)$. We define the set $S = \{1\} \cup \{1 + 1/k \mid k \in \mathbb{N}, k \ge 1\}$.
We prove that the set of cluster points of the sequence $u$ is exactly $S$.
This is formalized in `erdos_419`.
The proof relies on the fact that $u(n)$ is asymptotically $1 + 1/k$ when $n = kp - 1$ for a large prime $p$, and tends to 1 otherwise (or for other subsequences).
We use the helper lemma `cluster_point_of_k` to show that every $1+1/k$ is a cluster point.
We use `one_is_cluster_point` (provided in the context) to show 1 is a cluster point.
We use `limit_points_subset_S` (provided in the context) to show there are no other cluster points.
-/

import Mathlib

open scoped Classical

set_option maxHeartbeats 0
set_option maxRecDepth 4000

noncomputable def tau (n : ℕ) : ℕ := (Nat.divisors n).card

noncomputable def u (n : ℕ) : ℝ := (tau (n + 1).factorial : ℝ) / (tau n.factorial : ℝ)

def S : Set ℝ := {1} ∪ {x | ∃ k : ℕ, k ≥ 1 ∧ x = 1 + 1 / (k : ℝ)}

/-
The ratio $u(n) = \frac{\tau((n+1)!)}{\tau(n!)}$ can be written as a product over the prime factors of $n+1$.
-/
lemma u_eq_prod (n : ℕ) : u n = ∏ p ∈ (n + 1).primeFactors, (1 + (Nat.factorization (n + 1) p : ℝ) / ((Nat.factorization n.factorial p) + 1)) := by
  -- By definition of $u$, we know that
  unfold u;
  -- We can use the fact that $\tau(n!) = \prod_{p \leq n} (v_p(n!) + 1)$.
  have h_tau_fact : ∀ n : ℕ, tau n.factorial = ∏ p ∈ Nat.primeFactors n.factorial, (Nat.factorization (n.factorial) p + 1) := by
    intro n
    unfold tau;
    -- Apply the formula for the number of divisors of a number given its prime factorization.
    have h_divisors_formula : ∀ {m : ℕ}, m ≠ 0 → (Nat.divisors m).card = ∏ p ∈ Nat.primeFactors m, (Nat.factorization m p + 1) := by
      exact fun {m} a => Nat.card_divisors a;
    exact h_divisors_formula <| Nat.factorial_ne_zero _;
  -- We can simplify the expression by canceling out common terms in the numerator and denominator.
  have h_cancel : (∏ p ∈ Nat.primeFactors (Nat.factorial (n + 1)), (Nat.factorization (Nat.factorial (n + 1)) p + 1)) / (∏ p ∈ Nat.primeFactors (Nat.factorial n), (Nat.factorization (Nat.factorial n) p + 1) : ℝ) = (∏ p ∈ Nat.primeFactors (Nat.factorial (n + 1)), (1 + (Nat.factorization (n + 1)) p / (Nat.factorization (Nat.factorial n) p + 1) : ℝ)) := by
    have h_cancel : (∏ p ∈ Nat.primeFactors (Nat.factorial (n + 1)), (Nat.factorization (Nat.factorial (n + 1)) p + 1)) = (∏ p ∈ Nat.primeFactors (Nat.factorial (n + 1)), (Nat.factorization (Nat.factorial n) p + 1)) * (∏ p ∈ Nat.primeFactors (Nat.factorial (n + 1)), (1 + (Nat.factorization (n + 1)) p / (Nat.factorization (Nat.factorial n) p + 1) : ℝ)) := by
      have h_cancel : ∀ p ∈ Nat.primeFactors (Nat.factorial (n + 1)), (Nat.factorization (Nat.factorial (n + 1)) p + 1) = (Nat.factorization (Nat.factorial n) p + 1) * (1 + (Nat.factorization (n + 1)) p / (Nat.factorization (Nat.factorial n) p + 1) : ℝ) := by
        intro p hp; rw [ mul_add, mul_div_cancel₀ ] <;> norm_cast ; simp_all +decide [ Nat.factorial_succ, Nat.factorization_mul ] ;
        ring;
      push_cast [ ← Finset.prod_mul_distrib ];
      exact Finset.prod_congr rfl h_cancel;
    rw [ h_cancel, div_eq_iff ];
    · norm_num [ mul_comm ];
      rw [ ← Finset.prod_subset ( show n.factorial.primeFactors ⊆ ( n + 1 ).factorial.primeFactors from ?_ ) ] <;> norm_num [ Nat.factorial_ne_zero ];
      · exact fun p pp dp hp => Nat.factorization_eq_zero_of_not_dvd fun h => hp pp h;
      · exact Nat.primeFactors_mono ( Nat.factorial_dvd_factorial ( Nat.le_succ _ ) ) ( by positivity );
    · exact Finset.prod_ne_zero_iff.mpr fun p hp => Nat.cast_add_one_ne_zero _;
  simp_all +decide
  rw [ ← Finset.prod_subset ( show ( n + 1 |> Nat.primeFactors ) ⊆ ( n + 1 |> Nat.factorial |> Nat.primeFactors ) from ?_ ) ];
  · intro p hp hpn; rw [ Nat.factorization_eq_zero_of_not_dvd ] <;> aesop;
  · exact Nat.primeFactors_mono ( Nat.dvd_factorial ( Nat.succ_pos _ ) ( by linarith ) ) ( by positivity )

/-
There is at most one prime factor of $n+1$ greater than $n^{2/3}$.
-/
lemma at_most_one_large_prime (n : ℕ) : ((n + 1).primeFactors.filter (fun p => (p : ℝ) > (n : ℝ) ^ (2 / 3 : ℝ))).card ≤ 1 := by
  -- If there were two such primes $p, q$, then $p \cdot q > n^{4/3} > n+1$ for large $n$, which is a contradiction since $p \cdot q \mid n+1$.
  have h_two_primes : ∀ p q : ℕ, Nat.Prime p → Nat.Prime q → p > (n : ℝ) ^ (2 / 3 : ℝ) → q > (n : ℝ) ^ (2 / 3 : ℝ) → p ∣ n + 1 → q ∣ n + 1 → p = q := by
    intros p q hp hq hp_gt hq_gt hp_div hq_div
    by_contra h_neq
    have h_prod_gt : p * q > n + 1 := by
      -- Since $p$ and $q$ are primes greater than $n^{2/3}$, we have $p^3 > n^2$ and $q^3 > n^2$.
      have hp3_gt_n2 : p^3 > n^2 := by
        exact_mod_cast ( by exact lt_of_le_of_lt ( by rw [ ← Real.rpow_natCast _ 3, ← Real.rpow_mul ( Nat.cast_nonneg _ ) ] ; norm_num ) ( pow_lt_pow_left₀ hp_gt ( by positivity ) ( by norm_num ) ) : ( n :ℝ ) ^ 2 < p ^ 3 )
      have hq3_gt_n2 : q^3 > n^2 := by
        exact_mod_cast ( by exact lt_of_le_of_lt ( by rw [ ← Real.rpow_natCast _ 3, ← Real.rpow_mul ( Nat.cast_nonneg _ ) ] ; norm_num ) ( pow_lt_pow_left₀ hq_gt ( by positivity ) ( by norm_num ) ) : ( n :ℝ ) ^ 2 < q ^ 3 );
      have h_prod_gt : (p * q)^3 > (n + 1)^3 := by
        by_cases hn : n ≥ 3;
        · nlinarith [ Nat.mul_le_mul_left n hn, Nat.mul_le_mul_left n ( Nat.pow_le_pow_left hn 2 ) ];
        · interval_cases n <;> norm_num at *;
          · aesop;
          · have := Nat.le_of_dvd ( by decide ) hp_div; ( have := Nat.le_of_dvd ( by decide ) hq_div; interval_cases p ; interval_cases q ; trivial; );
          · have := Nat.le_of_dvd ( by decide ) hp_div; ( have := Nat.le_of_dvd ( by decide ) hq_div; interval_cases p <;> interval_cases q <;> trivial; );
      exact lt_of_pow_lt_pow_left₀ _ ( by positivity ) h_prod_gt;
    exact h_prod_gt.not_ge ( Nat.le_of_dvd ( Nat.succ_pos _ ) ( Nat.Coprime.mul_dvd_of_dvd_of_dvd ( by simpa [ * ] using Nat.coprime_primes hp hq ) hp_div hq_div ) );
  refine Finset.card_le_one.mpr ?_ ; aesop

/-
The product over prime factors $p \le n^{2/3}$ converges to 1.
-/
noncomputable def small_primes (n : ℕ) : Finset ℕ := (n + 1).primeFactors.filter (fun p => (p : ℝ) ≤ (n : ℝ) ^ (2 / 3 : ℝ))

lemma small_prime_contribution_tendsto_one : Filter.Tendsto (fun n => ∏ p ∈ small_primes n, (1 + (Nat.factorization (n + 1) p : ℝ) / ((Nat.factorization n.factorial p) + 1))) Filter.atTop (nhds 1) := by
  -- The term is bounded by $1 + \frac{\log_2(n+1)}{n/p}$.
  have h_term_bound : ∀ n ≥ 2, ∀ p ∈ small_primes n, (1 + (Nat.factorization (n + 1) p : ℝ) / ((Nat.factorization n.factorial p) + 1)) ≤ (1 + (Real.log (n + 1) / (n / p)) / (Real.log 2)) := by
    field_simp;
    -- Since $v_p(n!) \ge n/p - 1$, we have $v_p(n!) + 1 \ge n/p$.
    have h_vp_bound : ∀ n ≥ 2, ∀ p ∈ small_primes n, (Nat.factorization n.factorial p : ℝ) + 1 ≥ (n : ℝ) / p := by
      -- By definition of $v_p$, we know that $v_p(n!) = \sum_{k=1}^{\infty} \left\lfloor \frac{n}{p^k} \right\rfloor$.
      have h_vp_def : ∀ n ≥ 2, ∀ p ∈ small_primes n, (Nat.factorization n.factorial p : ℝ) = ∑ k ∈ Finset.Ico 1 (Nat.log p n + 1), (n / p ^ k : ℕ) := by
        intros n hn p hp
        rw [Nat.factorization_def];
        · haveI := Fact.mk ( show Nat.Prime p from by exact ( show Nat.Prime p from by exact ( by { unfold small_primes at hp; aesop } ) ) ) ; rw [ padicValNat_factorial ] ; aesop;
        · exact Nat.prime_of_mem_primeFactors ( Finset.mem_filter.mp hp |>.1 );
      intro n hn p hp; rw [ h_vp_def n hn p hp ] ; norm_num [ Finset.sum_Ico_eq_sum_range ];
      rcases p with ( _ | _ | p ) <;> norm_num [ Nat.div_eq_of_lt ] at *;
      · exact absurd hp ( by unfold small_primes; aesop );
      · rcases k : Nat.log ( p + 1 + 1 ) n with ( _ | k ) <;> simp_all +decide [ pow_add ];
        · rw [ div_le_iff₀ ] <;> norm_cast <;> linarith;
        · rw [ div_le_iff₀ ] <;> norm_cast <;> norm_num [ Finset.sum_range_succ' ];
          nlinarith [ Nat.div_add_mod n ( p + 1 + 1 ), Nat.mod_lt n ( Nat.succ_pos ( Nat.succ p ) ), show ∑ x ∈ Finset.range ‹_›, n / ( ( p + 1 + 1 ) * ( p + 1 + 1 ) ^ ( x + 1 ) ) ≥ 0 by exact Nat.zero_le _ ];
    -- Since $v_p(n+1) \le \log_2(n+1)$, we have $v_p(n+1) \le \log_2(n+1)$.
    have h_vp_n1_bound : ∀ n ≥ 2, ∀ p ∈ small_primes n, (Nat.factorization (n + 1) p : ℝ) ≤ Real.log (n + 1) / Real.log 2 := by
      intros n hn p hp
      have h_vp_n1_bound : (Nat.factorization (n + 1) p : ℝ) ≤ Real.log (n + 1) / Real.log p := by
        rw [ le_div_iff₀ ( Real.log_pos <| mod_cast Nat.Prime.one_lt <| by unfold small_primes at hp; aesop ) ] ; nth_rw 1 [ ← Real.log_pow ] ; exact Real.log_le_log ( mod_cast pow_pos ( Nat.Prime.pos <| by unfold small_primes at hp; aesop ) _ ) <| mod_cast Nat.le_of_dvd ( Nat.succ_pos _ ) <| Nat.ordProj_dvd _ _;
      field_simp;
      rw [ le_div_iff₀ ( Real.log_pos <| mod_cast Nat.Prime.one_lt <| by exact Nat.prime_of_mem_primeFactors <| Finset.mem_filter.mp hp |>.1 ) ] at h_vp_n1_bound;
      exact le_trans ( mul_le_mul_of_nonneg_left ( Real.log_le_log ( by norm_num ) ( Nat.cast_le.mpr ( Nat.Prime.two_le ( Nat.prime_of_mem_primeFactors ( Finset.mem_filter.mp hp |>.1 ) ) ) ) ) ( Nat.cast_nonneg _ ) ) h_vp_n1_bound;
    intro n hn p hp; specialize h_vp_bound n hn p hp; specialize h_vp_n1_bound n hn p hp; rw [ add_div', le_div_iff₀ ] at * <;> try positivity;
    rw [ mul_div, le_div_iff₀ ] <;> try positivity;
    rw [ ge_iff_le, div_le_iff₀ ] at h_vp_bound <;> nlinarith [ show ( p : ℝ ) > 0 from Nat.cast_pos.mpr ( Nat.pos_of_mem_primeFactors ( Finset.mem_filter.mp hp |>.1 ) ), Real.log_pos one_lt_two, mul_le_mul_of_nonneg_right h_vp_bound ( Real.log_nonneg one_le_two ) ];
  -- Since $p \le n^{2/3}$, the term is $1 + O(n^{-1/3} \log n)$.
  have h_term_bound_simplified : ∀ n ≥ 2, ∀ p ∈ small_primes n, (1 + (Nat.factorization (n + 1) p : ℝ) / ((Nat.factorization n.factorial p) + 1)) ≤ (1 + (Real.log (n + 1) * p / n) / (Real.log 2)) := by
    convert h_term_bound using 3 ; norm_num [ div_div_eq_mul_div ];
  -- The number of such primes is bounded by $\log_2(n+1)$.
  have h_prime_count_bound : ∀ n ≥ 2, (small_primes n).card ≤ Real.log (n + 1) / Real.log 2 := by
    -- Each prime factor $p$ of $n+1$ satisfies $p \leq n+1$, and there are at most $\log_2(n+1)$ such primes.
    intros n hn
    have h_prime_factors_count : (Nat.primeFactors (n + 1)).card ≤ Real.log (n + 1) / Real.log 2 := by
      rw [ le_div_iff₀ ( Real.log_pos ( by norm_num ) ), ← Real.log_pow ] ; norm_cast ; exact Real.log_le_log ( by positivity ) <| mod_cast Nat.le_trans ( by simpa using Finset.prod_le_prod' fun p hp => Nat.Prime.two_le <| Nat.prime_of_mem_primeFactors hp ) <| Nat.le_of_dvd ( Nat.succ_pos _ ) <| Nat.prod_primeFactors_dvd _;
    exact le_trans ( Nat.cast_le.mpr <| Finset.card_le_card <| Finset.filter_subset _ _ ) h_prime_factors_count;
  -- So the product is $(1 + O(n^{-1/3} \log n))^{\log n} \to 1$.
  have h_product_bound : ∀ n ≥ 2, (∏ p ∈ small_primes n, (1 + (Nat.factorization (n + 1) p : ℝ) / ((Nat.factorization n.factorial p) + 1))) ≤ (1 + (Real.log (n + 1) * (n : ℝ) ^ (2 / 3 : ℝ) / n) / (Real.log 2)) ^ (Real.log (n + 1) / Real.log 2) := by
    intros n hn
    have h_prod_le : (∏ p ∈ small_primes n, (1 + (Nat.factorization (n + 1) p : ℝ) / ((Nat.factorization n.factorial p) + 1))) ≤ (1 + (Real.log (n + 1) * (n : ℝ) ^ (2 / 3 : ℝ) / n) / (Real.log 2)) ^ (small_primes n).card := by
      refine' le_trans ( Finset.prod_le_prod _ fun p hp => h_term_bound_simplified n hn p hp ) _;
      · exact fun _ _ => by positivity;
      · refine' le_trans ( Finset.prod_le_prod _ fun p hp => show ( 1 + Real.log ( n + 1 ) * p / n / Real.log 2 ) ≤ 1 + Real.log ( n + 1 ) * ( n : ℝ ) ^ ( 2 / 3 : ℝ ) / n / Real.log 2 from _ ) _ <;> norm_num;
        · exact fun p hp => add_nonneg zero_le_one <| div_nonneg ( div_nonneg ( mul_nonneg ( Real.log_nonneg <| by linarith ) <| Nat.cast_nonneg _ ) <| Nat.cast_nonneg _ ) <| Real.log_nonneg <| by norm_num;
        · gcongr;
          · exact Real.log_nonneg ( by linarith );
          · exact_mod_cast Finset.mem_filter.mp hp |>.2;
    refine le_trans h_prod_le ?_;
    exact_mod_cast Real.rpow_le_rpow_of_exponent_le ( le_add_of_nonneg_right <| by positivity ) ( h_prime_count_bound n hn );
  -- We'll use the fact that $(1 + x)^y \leq \exp(xy)$ for $x \geq 0$ and $y \geq 0$.
  have h_exp_bound : ∀ n ≥ 2, (1 + (Real.log (n + 1) * (n : ℝ) ^ (2 / 3 : ℝ) / n) / (Real.log 2)) ^ (Real.log (n + 1) / Real.log 2) ≤ Real.exp ((Real.log (n + 1) * (n : ℝ) ^ (2 / 3 : ℝ) / n) / (Real.log 2) * (Real.log (n + 1) / Real.log 2)) := by
    intro n hn; rw [ Real.rpow_def_of_pos ( by exact add_pos_of_pos_of_nonneg zero_lt_one <| div_nonneg ( div_nonneg ( mul_nonneg ( Real.log_nonneg <| by linarith ) <| Real.rpow_nonneg ( by linarith ) _ ) <| by linarith ) <| Real.log_nonneg <| by linarith ) ] ; ring_nf; norm_num;
    have h_exp_bound : ∀ x : ℝ, 0 ≤ x → Real.log (1 + x) ≤ x := by
      exact fun x hx => le_trans ( Real.log_le_sub_one_of_pos ( by linarith ) ) ( by linarith );
    convert mul_le_mul_of_nonneg_left ( h_exp_bound ( Real.log ( 1 + n ) * n ^ ( 2 / 3 : ℝ ) * n⁻¹ * ( Real.log 2 ) ⁻¹ ) ( by exact mul_nonneg ( mul_nonneg ( mul_nonneg ( Real.log_nonneg ( by linarith ) ) ( Real.rpow_nonneg ( by linarith ) _ ) ) ( inv_nonneg.mpr ( by linarith ) ) ) ( inv_nonneg.mpr ( Real.log_nonneg ( by linarith ) ) ) ) ) ( show 0 ≤ Real.log ( 1 + n ) * ( Real.log 2 ) ⁻¹ by exact mul_nonneg ( Real.log_nonneg ( by linarith ) ) ( inv_nonneg.mpr ( Real.log_nonneg ( by linarith ) ) ) ) using 1 ; ring;
  -- We'll use the fact that $\exp(xy) \to 1$ as $x \to 0$ and $y \to \infty$.
  have h_exp_zero : Filter.Tendsto (fun n : ℕ => (Real.log (n + 1) * (n : ℝ) ^ (2 / 3 : ℝ) / n) / (Real.log 2) * (Real.log (n + 1) / Real.log 2)) Filter.atTop (nhds 0) := by
    -- We can simplify the expression inside the limit.
    suffices h_simplify : Filter.Tendsto (fun n : ℕ => (Real.log (n + 1)) ^ 2 / (n : ℝ) ^ (1 / 3 : ℝ) / (Real.log 2) ^ 2) Filter.atTop (nhds 0) by
      refine h_simplify.congr' ?_ ; filter_upwards [ Filter.eventually_gt_atTop 0 ] with n hn ; ring_nf ; norm_num [ hn.ne', Real.rpow_neg, Real.rpow_one, Real.rpow_add, Real.rpow_sub ] ; ring_nf;
      rw [ show ( 2 / 3 : ℝ ) = 1 - 1 / 3 by norm_num, Real.rpow_sub ( by positivity ), Real.rpow_one ] ; ring_nf ; norm_num [ hn.ne' ] ; ring_nf;
      simp +decide [ mul_assoc, mul_comm, mul_left_comm, hn.ne' ];
    -- We can use the fact that $\frac{(\log n)^2}{n^{1/3}} \to 0$ as $n \to \infty$.
    have h_log_div_n : Filter.Tendsto (fun n : ℕ => (Real.log (n : ℝ)) ^ 2 / (n : ℝ) ^ (1 / 3 : ℝ)) Filter.atTop (nhds 0) := by
      -- Let $y = \log x$, therefore the expression becomes $\frac{y^2}{e^{y/3}}$.
      suffices h_log : Filter.Tendsto (fun y : ℝ => y^2 / Real.exp (y / 3)) Filter.atTop (nhds 0) by
        have := h_log.comp Real.tendsto_log_atTop;
        exact this.comp tendsto_natCast_atTop_atTop |> Filter.Tendsto.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with x hx using by norm_num [ Real.rpow_def_of_pos, mul_div, hx ] );
      -- Let $z = \frac{y}{3}$, therefore the expression becomes $\frac{(3z)^2}{e^z} = \frac{9z^2}{e^z}$.
      suffices h_z : Filter.Tendsto (fun z : ℝ => 9 * z^2 / Real.exp z) Filter.atTop (nhds 0) by
        convert h_z.comp ( Filter.tendsto_id.atTop_mul_const ( by norm_num : 0 < ( 3⁻¹ : ℝ ) ) ) using 2 ; norm_num ; ring_nf;
      simpa [ Real.exp_neg, mul_div_assoc ] using Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 2 |> Filter.Tendsto.const_mul 9;
    -- We can use the fact that $\frac{(\log (n+1))^2}{n^{1/3}} \to 0$ as $n \to \infty$.
    have h_log_div_n_shifted : Filter.Tendsto (fun n : ℕ => (Real.log (n + 1 : ℝ)) ^ 2 / (n : ℝ) ^ (1 / 3 : ℝ)) Filter.atTop (nhds 0) := by
      have h_log_div_n_shifted : Filter.Tendsto (fun n : ℕ => (Real.log (n + 1 : ℝ)) ^ 2 / (n + 1 : ℝ) ^ (1 / 3 : ℝ)) Filter.atTop (nhds 0) := by
        exact_mod_cast h_log_div_n.comp ( Filter.tendsto_add_atTop_nat 1 );
      have h_log_div_n_shifted : Filter.Tendsto (fun n : ℕ => ((n + 1 : ℝ) ^ (1 / 3 : ℝ)) / (n : ℝ) ^ (1 / 3 : ℝ)) Filter.atTop (nhds 1) := by
        have h_log_div_n_shifted : Filter.Tendsto (fun n : ℕ => ((1 + 1 / (n : ℝ)) ^ (1 / 3 : ℝ))) Filter.atTop (nhds 1) := by
          convert Filter.Tendsto.rpow ( tendsto_const_nhds.add ( tendsto_one_div_atTop_nhds_zero_nat ) ) tendsto_const_nhds _ using 2 <;> norm_num;
        refine h_log_div_n_shifted.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with n hn using by rw [ ← Real.div_rpow ( by positivity ) ( by positivity ), add_div, div_self ( by positivity ) ] );
      convert ‹Filter.Tendsto ( fun n : ℕ => Real.log ( n + 1 ) ^ 2 / ( n + 1 : ℝ ) ^ ( 1 / 3 : ℝ ) ) Filter.atTop ( nhds 0 ) ›.mul h_log_div_n_shifted using 2 <;> ring_nf;
      rw [ mul_assoc, mul_inv_cancel₀ ( by positivity ), mul_one ];
    simpa using h_log_div_n_shifted.div_const _;
  refine' tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds ( by simpa using Filter.Tendsto.comp ( Real.continuous_exp.tendsto _ ) h_exp_zero ) _ _;
  · filter_upwards [ Filter.eventually_ge_atTop 2 ] with n hn using le_trans ( by norm_num ) ( Finset.prod_le_prod ( fun _ _ => by positivity ) fun _ _ => le_add_of_nonneg_right <| by positivity );
  · filter_upwards [ Filter.eventually_ge_atTop 2 ] with n hn using le_trans ( h_product_bound n hn ) ( by simpa using h_exp_bound n ( mod_cast hn ) )

/-
For sufficiently large $n$, if $p \mid n+1$ and $p > n^{2/3}$, then $v_p(n+1) = 1$ and $v_p(n!) = (n+1)/p - 1$.
-/
lemma large_prime_properties : ∀ᶠ (n : ℕ) in Filter.atTop, ∀ p ∈ (n + 1).primeFactors, (p : ℝ) > (n : ℝ) ^ (2 / 3 : ℝ) → Nat.factorization (n + 1) p = 1 ∧ Nat.factorization n.factorial p = (n + 1) / p - 1 := by
  norm_num +zetaDelta at *;
  use 2^128; (
  -- Let's unfold the definition of $v_p(n+1)$ and $v_p(n!)$
  intro b hb p hp hp_div hp_gt
  have h_vp : (Nat.factorization (b + 1) p) = 1 := by
    -- If $p > n^{2/3}$, then $p^2 > n$ for large $n$, so $v_p(n+1) = 1$.
    have h_vp_n1 : p ^ 2 > b + 1 := by
      -- Raising both sides of $p > b^{2/3}$ to the power of $3/2$ gives $p^{3/2} > b$.
      have hp_cubed : (p : ℝ) ^ 3 > b ^ 2 := by
        exact lt_of_le_of_lt ( by rw [ ← Real.rpow_natCast _ 3, ← Real.rpow_mul ( by positivity ) ] ; norm_num ) ( pow_lt_pow_left₀ hp_gt ( by positivity ) ( by positivity ) );
      norm_cast at hp_cubed; nlinarith [ hp.two_le ] ;
    exact le_antisymm ( Nat.le_of_not_lt fun h => by have := Nat.ordProj_dvd ( b + 1 ) p; exact absurd ( Nat.dvd_trans ( pow_dvd_pow p h ) this ) ( Nat.not_dvd_of_pos_of_lt ( by positivity ) h_vp_n1 ) ) ( Nat.pos_of_ne_zero ( Finsupp.mem_support_iff.mp ( by aesop ) ) );
  have h_vp_fact : (Nat.factorization (b.factorial) p) = ∑ k ∈ Finset.Ico 1 (Nat.log p b + 1), (b / p ^ k) := by
    rw [ Nat.factorization_def ];
    · haveI := Fact.mk hp; rw [ padicValNat_factorial ] ; aesop;
    · assumption;
  -- Since $p > b^{2/3}$, we have $p^2 > b$, thus $\log_p(b) < 2$.
  have h_log : Nat.log p b < 2 := by
    refine' Nat.log_lt_of_lt_pow _ _ <;> norm_num at * <;> try nlinarith [ hp.two_le ] ;
    -- Raising both sides to the power of 3, we get $b^2 < p^3$.
    have h_b2_lt_p3 : (b : ℝ) ^ 2 < p ^ 3 := by
      exact lt_of_le_of_lt ( by rw [ ← Real.rpow_natCast _ 3, ← Real.rpow_mul ( by positivity ) ] ; norm_num ) ( pow_lt_pow_left₀ hp_gt ( by positivity ) ( by positivity ) ) |> lt_of_lt_of_le <| by norm_num;
    norm_cast at h_b2_lt_p3; nlinarith [ hp.two_le ] ;
  interval_cases _ : Nat.log p b <;> simp_all +decide [ Nat.succ_div ];
  exact Eq.symm ( Nat.div_eq_of_lt <| Or.resolve_right ‹_› hp.one_lt.not_ge ));

/-
$u(n)$ is the product of $u_{small}(n)$ and $u_{large}(n)$.
-/
noncomputable def u_small (n : ℕ) : ℝ := ∏ p ∈ small_primes n, (1 + (Nat.factorization (n + 1) p : ℝ) / ((Nat.factorization n.factorial p) + 1))

noncomputable def u_large (n : ℕ) : ℝ := ∏ p ∈ (n + 1).primeFactors \ small_primes n, (1 + (Nat.factorization (n + 1) p : ℝ) / ((Nat.factorization n.factorial p) + 1))

noncomputable def large_prime (n : ℕ) : ℕ := ((n + 1).primeFactors \ small_primes n).max.getD 0

noncomputable def approx_u (n : ℕ) : ℝ :=
  if large_prime n > 0 then 1 + 1 / ((n + 1 : ℝ) / (large_prime n : ℝ)) else 1

lemma u_eq_u_small_mul_u_large (n : ℕ) : u n = u_small n * u_large n := by
  convert Finset.prod_union ?_ using 2;
  rw [ Finset.union_sdiff_of_subset ];
  · exact u_eq_prod n;
  · exact Finset.filter_subset _ _;
  · exact Finset.disjoint_sdiff

/-
`u_small` tends to 1. `large_prime n` is the largest prime factor of $n+1$ greater than $n^{2/3}$, or 0 if none exist.
-/
lemma u_small_tendsto_one : Filter.Tendsto u_small Filter.atTop (nhds 1) := small_prime_contribution_tendsto_one

lemma large_prime_eq_iff (n : ℕ) (p : ℕ) : large_prime n = p ↔ (p = 0 ∧ ((n + 1).primeFactors \ small_primes n) = ∅) ∨ (p ∈ (n + 1).primeFactors \ small_primes n ∧ ∀ q ∈ (n + 1).primeFactors \ small_primes n, q ≤ p) := by
  unfold large_prime;
  constructor <;> intro h;
  · by_cases h' : ( n + 1 |> Nat.primeFactors ) \ small_primes n = ∅ <;> simp_all +decide [ Finset.max ];
    · exact Or.inl h.symm;
    · -- Since the set is non-empty, its supremum is the maximum element.
      have h_max : ∃ q ∈ (n + 1).primeFactors \ small_primes n, ∀ r ∈ (n + 1).primeFactors \ small_primes n, r ≤ q := by
        exact ⟨ Finset.max' _ <| Finset.nonempty_of_ne_empty <| by aesop_cat, Finset.max'_mem _ _, fun r hr => Finset.le_max' _ _ hr ⟩;
      obtain ⟨ q, hq₁, hq₂ ⟩ := h_max; have := h; rw [ show ( ( n + 1 |> Nat.primeFactors ) \ small_primes n |> Finset.sup ) WithBot.some = WithBot.some q from ?_ ] at this; aesop;
      exact le_antisymm ( Finset.sup_le fun x hx => WithBot.coe_le_coe.mpr ( hq₂ x hx ) ) ( Finset.le_sup ( f := WithBot.some ) hq₁ );
  · cases h <;> simp_all +decide [ Finset.max ];
    · rw [ Finset.sdiff_eq_empty_iff_subset.mpr ] <;> aesop;
    · rw [ show ( ( n + 1 |> Nat.primeFactors ) \ small_primes n ).sup WithBot.some = WithBot.some p from ?_ ] ; aesop;
      refine' le_antisymm _ _ <;> aesop

/-
If there are no large primes, `u_large` is 1.
-/
lemma u_large_eq_one_of_large_prime_zero (n : ℕ) (h : large_prime n = 0) : u_large n = 1 := by
  -- By definition of `large_prime`, if `large_prime n = 0`, then the set of large primes is empty.
  have h_large_prime_empty : (n + 1).primeFactors \ small_primes n = ∅ := by
    rw [ large_prime_eq_iff ] at h ; aesop;
  -- Since the set of large primes is empty, the product over this set is 1.
  simp [u_large, h_large_prime_empty]

/-
If there is a large prime, `u_large` is the term corresponding to that prime.
-/
lemma u_large_eq_term_of_large_prime_pos : ∀ᶠ n in Filter.atTop, large_prime n > 0 → u_large n = 1 + (Nat.factorization (n + 1) (large_prime n) : ℝ) / ((Nat.factorization n.factorial (large_prime n)) + 1) := by
  -- By definition of `u_large`, if `large_prime n > 0`, then `u_large n` is the product of terms corresponding to the prime factors of `n + 1` greater than `n^(2/3)`.
  simp [u_large, large_prime];
  -- Let's choose `a` such that for all `b ≥ a`, if `large_prime b > 0`, then `large_prime b` is the unique prime factor of `b + 1` greater than `b^(2/3)`.
  obtain ⟨a, ha⟩ : ∃ a, ∀ b ≥ a, ((b + 1).primeFactors \ small_primes b).card ≤ 1 := by
    use 2^6;
    intros b hb
    have h_card : ((b + 1).primeFactors.filter (fun p => (p : ℝ) > (b : ℝ) ^ (2 / 3 : ℝ))).card ≤ 1 := by
      convert at_most_one_large_prime b using 1;
    convert h_card using 2;
    refine' Finset.card_bij _ _ _ _;
    use fun p hp => p;
    · unfold small_primes; aesop;
    · aesop;
    · unfold small_primes; aesop;
  use a; intros b hb hb'; specialize ha b hb; rcases x : ( b + 1 |> Nat.primeFactors ) \ small_primes b with ⟨ ⟨ p, hp ⟩ ⟩ <;> aesop;

/-
`u_large` is eventually equal to `approx_u`.
-/
lemma u_large_eventually_eq_approx_u : ∀ᶠ n in Filter.atTop, u_large n = approx_u n := by
  -- By definition of $u_{large}$, we know that for sufficiently large $n$, $u_{large}(n)$ is equal to the term corresponding to the largest prime factor of $n+1$ greater than $n^{2/3}$.
  have h_u_large_term : ∀ᶠ n in Filter.atTop, large_prime n > 0 → u_large n = 1 + (Nat.factorization (n + 1) (large_prime n) : ℝ) / ((Nat.factorization n.factorial (large_prime n)) + 1) := by
    exact u_large_eq_term_of_large_prime_pos;
  filter_upwards [ h_u_large_term, large_prime_properties ] with n hn hn';
  by_cases h : large_prime n > 0 <;> simp_all +decide [ approx_u ];
  · -- By definition of `large_prime`, we know that `large_prime n` is a prime factor of `n + 1` greater than `n^(2/3)`.
    obtain ⟨hp_prime, hp_div, hp_gt⟩ : Nat.Prime (large_prime n) ∧ large_prime n ∣ n + 1 ∧ (large_prime n : ℝ) > (n : ℝ) ^ (2 / 3 : ℝ) := by
      have h_large_prime : large_prime n ∈ (n + 1).primeFactors \ small_primes n := by
        have h_large_prime_factor : large_prime n ∈ (n + 1).primeFactors \ small_primes n := by
          have h_large_prime_factor : large_prime n ∈ (n + 1).primeFactors \ small_primes n ∨ large_prime n = 0 := by
            exact Classical.or_iff_not_imp_right.2 fun h => by have := large_prime_eq_iff n ( large_prime n ) ; aesop;
          aesop;
        exact h_large_prime_factor;
      unfold small_primes at h_large_prime; aesop;
    rw [ hn' _ hp_prime hp_div hp_gt |>.1, hn' _ hp_prime hp_div hp_gt |>.2 ] ; norm_num;
    rw [ Nat.cast_sub <| Nat.div_pos ( Nat.le_of_dvd ( Nat.succ_pos _ ) hp_div ) hp_prime.pos ] ; norm_num [ Nat.cast_div, hp_div ];
  · exact u_large_eq_one_of_large_prime_zero n h

/-
`approx_u` is bounded.
-/
lemma approx_u_bounded : ∃ C, ∀ n, |approx_u n| ≤ C := by
  unfold approx_u;
  field_simp;
  refine' ⟨ 3, fun n => _ ⟩ ; split_ifs <;> norm_num [ abs_le ];
  -- Since $large\_prime n$ is a prime factor of $n+1$, we have $large\_prime n \leq n+1$.
  have h_large_prime_le : (large_prime n : ℝ) ≤ n + 1 := by
    have h_large_prime_le : large_prime n ∈ (n + 1).primeFactors := by
      have := large_prime_eq_iff n ( large_prime n ) ; aesop;
    exact_mod_cast Nat.le_of_dvd ( Nat.succ_pos _ ) ( Nat.dvd_of_mem_primeFactors h_large_prime_le );
  exact ⟨ by rw [ le_div_iff₀ ] <;> linarith, by rw [ div_le_iff₀ ] <;> linarith ⟩

/-
The sequence $u(n)$ is asymptotically equivalent to `approx_u n`.
-/
lemma u_approx_main : Filter.Tendsto (fun n => |u n - approx_u n|) Filter.atTop (nhds 0) := by
  -- We'll use that $u(n) - \text{approx\_u}(n)$ is eventually equal to $(u_{\text{small}}(n) - 1) \cdot \text{approx\_u}(n)$.
  have h_diff : ∀ᶠ n in Filter.atTop, u n - approx_u n = (u_small n - 1) * approx_u n := by
    filter_upwards [ u_large_eventually_eq_approx_u ] with n hn using by rw [ u_eq_u_small_mul_u_large, hn ] ; ring;
  -- Since $u_{\text{small}}(n) \to 1$, we have $(u_{\text{small}}(n) - 1) \to 0$.
  have h_small : Filter.Tendsto (fun n => u_small n - 1) Filter.atTop (nhds 0) := by
    convert Filter.Tendsto.sub_const ( u_small_tendsto_one ) 1 using 2 ; ring;
  -- Since $\text{approx\_u}(n)$ is bounded, the product $(u_{\text{small}}(n) - 1) \cdot \text{approx\_u}(n)$ tends to $0$.
  obtain ⟨C, hC⟩ : ∃ C, ∀ n, |approx_u n| ≤ C := approx_u_bounded;
  have h_product : Filter.Tendsto (fun n => (u_small n - 1) * approx_u n) Filter.atTop (nhds 0) := by
    exact squeeze_zero_norm ( fun n => by simpa [ abs_mul ] using mul_le_mul_of_nonneg_left ( hC n ) ( abs_nonneg _ ) ) ( by simpa using h_small.norm.mul_const C );
  exact tendsto_zero_iff_norm_tendsto_zero.mpr ( by simpa using h_product.norm.congr' ( by filter_upwards [ h_diff ] with n hn; aesop ) )

/-
Every value of `approx_u` is in `S`.
-/
lemma approx_u_mem_S (n : ℕ) : approx_u n ∈ S := by
  -- Consider two cases: when `large_prime n` is zero and when it is not.
  by_cases h_large_prime : large_prime n = 0;
  · unfold approx_u S; aesop;
  · -- If `large_prime n` is not zero, then `approx_u n` is defined as $1 + 1/((n+1)/p)$.
    have h_approx_form : ∃ k : ℕ, k ≥ 1 ∧ approx_u n = 1 + (1 : ℝ) / k := by
      -- By definition of `approx_u`, if `large_prime n` is not zero, then `approx_u n` is defined as $1 + 1/((n+1)/p)$.
      use (n + 1) / large_prime n;
      -- Since `large_prime n` is a prime factor of `n + 1`, we have `large_prime n ∣ n + 1`.
      have h_div : large_prime n ∣ n + 1 := by
        have := large_prime_eq_iff n ( large_prime n ) ; aesop;
      exact ⟨ Nat.div_pos ( Nat.le_of_dvd ( Nat.succ_pos _ ) h_div ) ( Nat.pos_of_dvd_of_pos h_div ( Nat.succ_pos _ ) ), by rw [ approx_u ] ; aesop ⟩;
    exact Set.mem_union_right _ ⟨ _, h_approx_form.choose_spec.1, h_approx_form.choose_spec.2 ⟩

/-
$S$ is a closed set.
-/
lemma S_is_closed : IsClosed S := by
  refine' IsCompact.isClosed _;
  -- The set $\{1 + 1/k \mid k \ge 1\}$ has 1 as its only accumulation point.
  have h_acc : Filter.Tendsto (fun k : ℕ => 1 + 1 / (k : ℝ)) Filter.atTop (nhds 1) := by
    simpa using tendsto_const_nhds.add ( tendsto_inverse_atTop_nhds_zero_nat );
  have h_seq_compact : IsCompact ({1} ∪ Set.range (fun k : ℕ => 1 + 1 / (k + 1 : ℝ))) := by
    convert ( h_acc.comp ( Filter.tendsto_add_atTop_nat 1 ) ) |> fun h => h.isCompact_insert_range using 1 ; aesop;
  convert h_seq_compact using 1;
  norm_num [ Set.ext_iff ];
  exact fun x => or_congr Iff.rfl ⟨ fun ⟨ k, hk₁, hk₂ ⟩ => ⟨ k - 1, by cases k <;> aesop ⟩, fun ⟨ k, hk ⟩ => ⟨ k + 1, by linarith, by cases k <;> aesop ⟩ ⟩

/-
The limit points of $u$ are contained in $S$.
-/
lemma limit_points_subset_S : {x : ℝ | MapClusterPt x Filter.atTop u} ⊆ S := by
  intro x hx;
  -- Since $x$ is a cluster point of $u$, there exists a subsequence $u(n_k) \to x$.
  obtain ⟨nk, hnk⟩ : ∃ nk : ℕ → ℕ, StrictMono nk ∧ Filter.Tendsto (u ∘ nk) Filter.atTop (nhds x) := by
    exact Filter.subseq_tendsto_of_neBot hx;
  -- Since $|u(n_k) - approx\_u(n_k)| \to 0$, we have $approx\_u(n_k) \to x$.
  have h_approx_u_lim : Filter.Tendsto (approx_u ∘ nk) Filter.atTop (nhds x) := by
    have h_approx_u_lim : Filter.Tendsto (fun k => |(u ∘ nk) k - (approx_u ∘ nk) k|) Filter.atTop (nhds 0) := by
      have h_approx_u_lim : Filter.Tendsto (fun n => |u n - approx_u n|) Filter.atTop (nhds 0) := by
        exact u_approx_main;
      exact h_approx_u_lim.comp hnk.1.tendsto_atTop;
    simpa using hnk.2.sub ( tendsto_zero_iff_norm_tendsto_zero.mpr h_approx_u_lim );
  exact S_is_closed.mem_of_tendsto h_approx_u_lim ( Filter.Eventually.of_forall fun n => approx_u_mem_S _ )

/-
1 is a cluster point of the sequence $u$.
-/
lemma one_is_cluster_point : MapClusterPt 1 Filter.atTop u := by
  -- By definition of $u$, we know that for any $k$, $u(2^k - 1) \to 1$ as $k \to \infty$.
  have h_subseq : Filter.Tendsto (fun k => u (2^k - 1)) Filter.atTop (nhds 1) := by
    -- For the subsequence $u(2^k - 1)$, we have $u(2^k - 1) = \frac{\tau((2^k)!)}{\tau((2^k - 1)!)}$.
    -- Since $\tau((2^k)!) = \tau((2^k - 1)!) \cdot \tau(2^k)$ and $\tau(2^k) = k + 1$, we get $u(2^k - 1) = k + 1$.
    have h_subseq : ∀ k : ℕ, u (2^k - 1) = ∏ p ∈ (2^k).primeFactors, (1 + (Nat.factorization (2^k) p : ℝ) / ((Nat.factorization (2^k - 1).factorial p) + 1)) := by
      intro k; convert u_eq_prod ( 2 ^ k - 1 ) using 1;
      rw [ Nat.sub_add_cancel ( Nat.one_le_pow _ _ ( by decide ) ) ];
    -- Since $\tau((2^k)!) = \tau((2^k - 1)!) \cdot \tau(2^k)$ and $\tau(2^k) = k + 1$, we get $u(2^k - 1) = k + 1$.
    have h_subseq_simplified : ∀ k : ℕ, u (2^k - 1) = 1 + (k : ℝ) / ((Nat.factorization (2^k - 1).factorial 2) + 1) := by
      intro k; rw [ h_subseq k ] ; rcases k with ( _ | k ) <;> norm_num [ Nat.primeFactors_pow ] ;
    -- Since $\tau((2^k - 1)!) = (2^{k-1} + 2^{k-2} + \cdots + 2^0) = 2^k - 1$, we have $v_2((2^k - 1)!) = 2^k - 1 - k$.
    have h_factorial_2 : ∀ k : ℕ, k ≥ 1 → Nat.factorization (2^k - 1).factorial 2 = 2^k - 1 - k := by
      intro k hk
      have h_factorial_2 : Nat.factorization (2^k - 1).factorial 2 = ∑ i ∈ Finset.Ico 1 (k + 1), (2^k - 1) / 2^i := by
        rw [ Nat.factorization_def ];
        · rw [ padicValNat_factorial ];
          refine' Nat.lt_succ_of_le ( Nat.le_trans ( Nat.log_mono_right <| Nat.sub_le _ _ ) _ ) ; norm_num [ Nat.log_pow ];
        · norm_num;
      -- We'll use that $\sum_{i=1}^{k} \frac{2^k - 1}{2^i} = 2^k - 1 - k$.
      have h_sum : ∑ i ∈ Finset.Ico 1 (k + 1), (2^k - 1) / 2^i = ∑ i ∈ Finset.Ico 1 (k + 1), (2^(k-i) - 1) := by
        refine' Finset.sum_congr rfl fun i hi => _;
        rw [ show 2 ^ k - 1 = 2 ^ i * ( 2 ^ ( k - i ) - 1 ) + ( 2 ^ i - 1 ) by zify ; cases le_iff_exists_add.mp ( show i ≤ k from by linarith [ Finset.mem_Ico.mp hi ] ) ; simp +decide [ *, pow_add ] ; ring, Nat.add_div ] <;> norm_num [ Nat.pow_succ' ];
        rw [ Nat.div_eq_of_lt, if_neg ] <;> norm_num [ Nat.one_le_iff_ne_zero ];
      -- We'll use that $\sum_{i=1}^{k} (2^{k-i} - 1) = (2^k - 1) - k$.
      have h_sum_simplified : ∑ i ∈ Finset.Ico 1 (k + 1), (2^(k-i) - 1) = ∑ i ∈ Finset.range k, (2^i - 1) := by
        rw [ Finset.sum_Ico_eq_sum_range ] ; norm_num [ add_comm, add_left_comm ];
        conv_rhs => rw [ ← Finset.sum_range_reflect ] ;
        simp +decide only [Nat.sub_sub, add_comm];
      rw [ h_factorial_2, h_sum, h_sum_simplified ];
      rw [ Nat.sub_sub ];
      exact eq_tsub_of_add_eq ( by { exact Nat.recOn k ( by norm_num ) fun n ih => by rw [ Finset.sum_range_succ, pow_succ' ] ; linarith [ Nat.sub_add_cancel ( Nat.one_le_pow n 2 zero_lt_two ), Nat.sub_add_cancel ( Nat.one_le_pow ( n + 1 ) 2 zero_lt_two ) ] } );
    -- Substitute $v_2((2^k - 1)!) = 2^k - 1 - k$ into the expression for $u(2^k - 1)$.
    have h_subseq_final : ∀ k : ℕ, k ≥ 1 → u (2^k - 1) = 1 + (k : ℝ) / (2^k - k) := by
      intro k hk; rw [ h_subseq_simplified, h_factorial_2 k hk ] ; norm_num [ Nat.cast_sub ( show k ≤ 2 ^ k - 1 from Nat.le_sub_one_of_lt ( Nat.recOn k ( by norm_num ) fun n ihn => by rw [ pow_succ' ] ; linarith [ Nat.sub_add_cancel ( Nat.one_le_pow n 2 zero_lt_two ) ] ) ) ] ;
      ring;
    -- We need to show that $\frac{k}{2^k - k} \to 0$ as $k \to \infty$.
    have h_frac_zero : Filter.Tendsto (fun k : ℕ => (k : ℝ) / (2^k - k)) Filter.atTop (nhds 0) := by
      -- We can convert this limit into a form that is easier to handle by substituting $m = k$.
      suffices h_convert : Filter.Tendsto (fun m : ℕ => (m : ℝ) / (2 ^ m)) Filter.atTop (nhds 0) by
        convert h_convert.div ( show Filter.Tendsto ( fun m : ℕ => ( 1 - ( m : ℝ ) / 2 ^ m ) ) Filter.atTop ( nhds ( 1 - 0 ) ) from tendsto_const_nhds.sub h_convert ) _ using 2 <;> norm_num;
        rw [ div_div, mul_sub, mul_one, mul_div_cancel₀ _ ( by positivity ) ];
      refine' squeeze_zero_norm' _ tendsto_inverse_atTop_nhds_zero_nat;
      norm_num;
      exact ⟨ 8, fun n hn => by rw [ inv_eq_one_div, div_le_div_iff₀ ] <;> norm_cast <;> induction hn <;> norm_num [ Nat.pow_succ ] at * ; nlinarith ⟩;
    simpa using Filter.Tendsto.congr' ( by filter_upwards [ Filter.eventually_ge_atTop 1 ] with k hk; aesop ) ( h_frac_zero.const_add 1 );
  rw [ MapClusterPt ];
  rw [ clusterPt_iff_frequently ];
  intro s hs;
  rw [ Filter.frequently_iff_seq_frequently ];
  use fun k => u ( 2 ^ k - 1 );
  exact ⟨ Filter.Tendsto.comp ( Filter.tendsto_map ) ( Filter.tendsto_sub_atTop_nat 1 |> Filter.Tendsto.comp <| Nat.tendsto_pow_atTop_atTop_of_one_lt one_lt_two ), h_subseq.eventually ( hs ) |> fun h => h.frequently ⟩

/-
For sufficiently large primes $p$, the "large prime" of $k \cdot p - 1$ is $p$.
-/
lemma large_prime_of_kp_minus_1 (k : ℕ) (hk : k ≥ 1) : ∀ᶠ p in Filter.atTop, Nat.Prime p → large_prime (k * p - 1) = p := by
  -- Let $n = k \cdot p - 1$. Then $n + 1 = k \cdot p$.
  have h_n_plus_one : ∀ p : ℕ, Nat.Prime p → k * p - 1 + 1 = k * p := by
    exact fun p hp => Nat.succ_pred_eq_of_pos ( Nat.mul_pos hk hp.pos );
  -- For sufficiently large primes $p$, we have $p > n^{2/3}$ and for any prime $q \mid k$, $q \le n^{2/3}$.
  have h_large_prime_conditions : ∀ᶠ p in Filter.atTop, Nat.Prime p → (p : ℝ) > (k * p - 1 : ℝ) ^ (2 / 3 : ℝ) ∧ ∀ q ∈ k.primeFactors, (q : ℝ) ≤ (k * p - 1 : ℝ) ^ (2 / 3 : ℝ) := by
    have h_large_prime_conditions : ∀ᶠ p in Filter.atTop, Nat.Prime p → (p : ℝ) > (k * p - 1 : ℝ) ^ (2 / 3 : ℝ) := by
      -- For large $p$, we have $(kp)^{2/3} < p$, which simplifies to $k^{2/3} < p^{1/3}$, or $k^2 < p$.
      have h_p_gt_kp_simplified : ∀ᶠ p in Filter.atTop, Nat.Prime p → (k : ℝ) ^ 2 < p := by
        exact Filter.eventually_atTop.mpr ⟨ k ^ 2 + 1, fun p hp hp' => mod_cast by nlinarith ⟩;
      filter_upwards [ h_p_gt_kp_simplified, Filter.eventually_gt_atTop 1 ] with p hp₁ hp₂ aesop;
      -- Raising both sides to the power of 3, we get $(kp - 1)^2 < p^3$.
      have h_cube : ((k * p - 1 : ℝ) ^ 2) < p ^ 3 := by
        nlinarith [ show ( k : ℝ ) ≥ 1 by norm_cast, show ( p : ℝ ) ≥ 2 by norm_cast, hp₁ aesop, pow_two ( p - 1 : ℝ ) ];
      contrapose! h_cube;
      convert pow_le_pow_left₀ ( by positivity ) h_cube 3 using 1 ; rw [ ← Real.rpow_natCast _ 3, ← Real.rpow_mul ( by nlinarith [ show ( k : ℝ ) ≥ 1 by norm_cast, show ( p : ℝ ) ≥ 2 by norm_cast ] ) ] ; norm_num;
    -- For any prime $q \mid k$, we have $q \le k$. We need $q \le n^{2/3}$. Since $q \le k$ and $n^{2/3} \to \infty$, this holds for large $p$.
    have h_prime_factors_bound : ∀ q ∈ k.primeFactors, Filter.Tendsto (fun p : ℕ => (k * p - 1 : ℝ) ^ (2 / 3 : ℝ)) Filter.atTop Filter.atTop := by
      exact fun q hq => tendsto_rpow_atTop ( by positivity ) |> Filter.Tendsto.comp <| Filter.tendsto_atTop_add_const_right _ _ <| tendsto_natCast_atTop_atTop.const_mul_atTop ( by positivity );
    have h_prime_factors_bound : ∀ q ∈ k.primeFactors, ∃ N : ℕ, ∀ p ≥ N, (q : ℝ) ≤ (k * p - 1 : ℝ) ^ (2 / 3 : ℝ) := by
      exact fun q hq => Filter.eventually_atTop.mp ( h_prime_factors_bound q hq |> Filter.Tendsto.eventually_ge_atTop <| q );
    choose! N hN using h_prime_factors_bound;
    filter_upwards [ h_large_prime_conditions, Filter.eventually_ge_atTop ( Finset.sup ( Nat.primeFactors k ) N ) ] with p hp₁ hp₂ hp₃ using ⟨ hp₁ hp₃, fun q hq => hN q hq p ( le_trans ( Finset.le_sup ( f := N ) hq ) hp₂ ) ⟩;
  -- By definition of `large_prime`, if $p > n^{2/3}$ and for any prime $q \mid k$, $q \le n^{2/3}$, then `large_prime n = p`.
  have h_large_prime_eq_p : ∀ p : ℕ, Nat.Prime p → (p : ℝ) > (k * p - 1 : ℝ) ^ (2 / 3 : ℝ) ∧ (∀ q ∈ k.primeFactors, (q : ℝ) ≤ (k * p - 1 : ℝ) ^ (2 / 3 : ℝ)) → large_prime (k * p - 1) = p := by
    intros p hp h_conditions
    have h_prime_factors : (k * p - 1 + 1).primeFactors = k.primeFactors ∪ {p} := by
      rw [ h_n_plus_one p hp, Nat.primeFactors_mul ] <;> aesop;
    apply (large_prime_eq_iff (k * p - 1) p).mpr;
    simp_all +decide [ Finset.ext_iff ];
    refine Or.inr ⟨ ⟨ ⟨ by linarith, by linarith [ hp.pos ] ⟩, ?_ ⟩, fun a ha ha' ha'' ha''' => ?_ ⟩ <;> simp_all +decide [ small_primes ];
    · cases k <;> cases p <;> aesop;
    · exact_mod_cast h_conditions.2 a ha ha' |> le_trans <| le_of_lt h_conditions.1;
  filter_upwards [ h_large_prime_conditions ] with p hp using fun hp' => h_large_prime_eq_p p hp' ( hp hp' )

/-
For any $k \ge 1$, $1 + 1/k$ is a cluster point of the sequence $u(n)$.
-/
lemma cluster_point_of_k (k : ℕ) (hk : k ≥ 1) : MapClusterPt (1 + 1 / (k : ℝ)) Filter.atTop u := by
  -- Since $p$ is a prime such that $p > \max(1000, k^2)$ and $large_prime (k * p - 1) = p$, we have $approx_u (k * p - 1) = 1 + 1 / k$.
  have h_approx_u : ∀ᶠ p in Filter.atTop, Nat.Prime p → large_prime (k * p - 1) = p → approx_u (k * p - 1) = 1 + 1 / (k : ℝ) := by
    filter_upwards [ Filter.eventually_gt_atTop ( max 1000 ( k ^ 2 ) ) ] with p hp_prime hp_gt hp_large_prime
    have h_approx_u : approx_u (k * p - 1) = 1 + 1 / ((k * p - 1 + 1 : ℝ) / (p : ℝ)) := by
      simp [approx_u, hp_large_prime];
      rw [ Nat.cast_sub ( by nlinarith [ le_max_left 1000 ( k ^ 2 ), le_max_right 1000 ( k ^ 2 ) ] ) ] ; aesop;
    simp_all +decide [ ne_of_gt hp_gt.pos ];
  -- Since $p$ is a prime such that $p > \max(1000, k^2)$ and $large_prime (k * p - 1) = p$, we have $u (k * p - 1) \to 1 + 1 / k$.
  have h_u_approx : Filter.Tendsto (fun p : ℕ => u (k * p - 1)) (Filter.atTop ⊓ Filter.principal {p | Nat.Prime p ∧ large_prime (k * p - 1) = p}) (nhds (1 + 1 / (k : ℝ))) := by
    have h_u_approx : Filter.Tendsto (fun p : ℕ => approx_u (k * p - 1)) (Filter.atTop ⊓ Filter.principal {p | Nat.Prime p ∧ large_prime (k * p - 1) = p}) (nhds (1 + 1 / (k : ℝ))) := by
      rw [ Filter.tendsto_congr' ];
      exact tendsto_const_nhds;
      rw [ Filter.EventuallyEq, Filter.eventually_inf_principal ] ; aesop;
    have h_u_approx : Filter.Tendsto (fun p : ℕ => |u (k * p - 1) - approx_u (k * p - 1)|) (Filter.atTop ⊓ Filter.principal {p | Nat.Prime p ∧ large_prime (k * p - 1) = p}) (nhds 0) := by
      have h_u_approx : Filter.Tendsto (fun n => |u n - approx_u n|) Filter.atTop (nhds 0) := by
        convert u_approx_main using 1;
      refine' h_u_approx.comp _;
      rw [ Filter.tendsto_atTop ];
      exact fun n => Filter.eventually_inf_principal.mpr <| Filter.eventually_atTop.mpr ⟨ n + 1, fun p hp hp' => Nat.le_sub_one_of_lt <| by nlinarith [ hp'.1.two_le ] ⟩;
    simpa using ‹Filter.Tendsto ( fun p : ℕ => approx_u ( k * p - 1 ) ) ( Filter.atTop ⊓ Filter.principal { p : ℕ | Nat.Prime p ∧ large_prime ( k * p - 1 ) = p } ) ( nhds ( 1 + 1 / ( k : ℝ ) ) ) ›.add ( tendsto_zero_iff_norm_tendsto_zero.mpr h_u_approx ) |> Filter.Tendsto.congr ( by intros; simp +decide );
  rw [ mapClusterPt_iff_frequently ];
  intro s hs; have := h_u_approx.eventually hs; simp_all +decide [ Filter.eventually_inf_principal ] ;
  obtain ⟨ a, ha ⟩ := this;
  -- Since there are infinitely many primes, we can find infinitely many $b \geq a$ such that $large_prime (k * b - 1) = b$.
  have h_inf_primes : Set.Infinite {b : ℕ | Nat.Prime b ∧ large_prime (k * b - 1) = b} := by
    have := large_prime_of_kp_minus_1 k hk;
    rw [ Filter.eventually_atTop ] at this; rcases this with ⟨ N, hN ⟩ ; exact Set.infinite_of_forall_exists_gt fun n => by rcases Nat.exists_infinite_primes ( n + N + 1 ) with ⟨ p, hp₁, hp₂ ⟩ ; exact ⟨ p, ⟨ hp₂, hN p ( by linarith ) hp₂ ⟩, by linarith ⟩ ;
  rw [ Filter.frequently_atTop ];
  exact fun n => by rcases h_inf_primes.exists_gt ( n + a ) with ⟨ b, hb₁, hb₂ ⟩ ; exact ⟨ k * b - 1, Nat.le_sub_one_of_lt ( by nlinarith [ Nat.Prime.two_le hb₁.1 ] ), ha b ( by linarith ) hb₁.1 hb₁.2 ⟩ ;

/-
The set of limit points of $u(n)$ is exactly the set $S$.
-/
theorem erdos_419 : {x : ℝ | MapClusterPt x Filter.atTop u} = S := by
  -- To prove equality of sets, we show each set is a subset of the other.
  apply Set.eq_of_subset_of_subset;
  · exact limit_points_subset_S;
  · rintro x ( rfl | ⟨ k, hk, rfl ⟩ );
    · exact one_is_cluster_point;
    · convert cluster_point_of_k k hk using 1
