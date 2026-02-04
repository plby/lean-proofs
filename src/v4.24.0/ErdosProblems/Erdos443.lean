/-

This is a Lean formalization of a solution to Erdős Problem 443.
https://www.erdosproblems.com/forum/thread/443

The original proof was found by: Hegyvári and Cambie

[He25] N. Hegyvári, An elementary question of Erdős and
Graham. arXiv:2503.24201 (2025).


The paper by Hegyvári was auto-formalized by Aristotle (from
Harmonic).


The proof is verified by Lean.  The following version numbers were
used:

Lean Toolchain version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7 (v4.24.0)

-/


/-
We have formalized and proved the results from the paper "An elementary question of Erdős and Graham" by Norbert Hegyvári.

Specifically, we have proved:
1. Theorem 1.1: For $m > n$, $|A_n \cap A_m| \le \tau_{m,n}$, with equality if $m$ is even and $n$ is odd. (`theorem_1_1`)
2. Corollary 1.2: An upper bound on $|A_n \cap A_m|$ for large $m, n$. (`corollary_1_2`)
3. Theorem 1.3: For every $s$, there exist $n < m$ such that $|A_n \cap A_m| = s$. (`theorem_1_3`)
4. A conditional sum-product result: If $A \subset [1, n^{(\log \log n)^c}]$, then $\max(|A+A|, |AA|) \gg n^{4/3 - 3/(\log \log n)^{1-c}}$. (`sum_product_result`)

The proofs follow the arguments in the paper, using elementary number theory and hypergraph estimates.
-/

import Mathlib


open scoped Classical

open scoped Pointwise

--set_option linter.mathlibStandardSet false

set_option maxHeartbeats 0

/-
For any integer $k \ge 1$, $\log(k+1) \le k \log 2$.
-/
lemma log_divisor_bound_term (k : ℕ) (hk : 1 ≤ k) :
  Real.log (k + 1) ≤ k * Real.log 2 := by
    rw [ ← Real.log_rpow, Real.log_le_log_iff ] <;> norm_cast <;> induction hk <;> norm_num [ pow_succ' ] at * ; nlinarith

/-
The sum of logarithms of the divisor counts for prime factors greater than $y$ is bounded by $\frac{\log 2}{\log y} \log n$.
-/
lemma log_rough_part_le (n : ℕ) (y : ℝ) (hy : 1 < y) :
  ∑ p ∈ n.primeFactors.filter (fun (p : ℕ) => y < (p : ℝ)), Real.log ((n.factorization p : ℝ) + 1) ≤ Real.log 2 / Real.log y * Real.log n := by
  by_cases hn : n = 0;
  · aesop;
  · -- We can bound the sum of logarithms of the divisor counts for prime factors greater than $y$ using the inequality $\log(v_p(n)+1) \le v_p(n) \log 2$.
    have h_bound : (∑ p ∈ n.primeFactors.filter (fun p => y < p : ℕ → Prop), Real.log ((Nat.factorization n) p + 1)) ≤ (Real.log 2) * (∑ p ∈ n.primeFactors.filter (fun p => y < p : ℕ → Prop), (Nat.factorization n) p) := by
      push_cast [ Finset.mul_sum _ _ _ ];
      exact Finset.sum_le_sum fun p hp => by rw [ mul_comm ] ; exact log_divisor_bound_term ( n.factorization p ) ( Nat.pos_of_ne_zero ( Finsupp.mem_support_iff.mp ( Finset.mem_filter.mp hp |>.1 ) ) ) ;
    -- We can bound the sum of the powers of the prime factors greater than $y$ using the inequality $\sum_{p \in S} v_p(n) \log p \le \log n$.
    have h_sum_bound : (∑ p ∈ n.primeFactors.filter (fun p => y < p : ℕ → Prop), (Nat.factorization n) p * Real.log p) ≤ Real.log n := by
      have h_sum_bound : (∑ p ∈ n.primeFactors, (Nat.factorization n) p * Real.log p) ≤ Real.log n := by
        conv_rhs => rw [ ← Nat.factorization_prod_pow_eq_self hn ];
        norm_num [ Finsupp.prod ];
        rw [ Real.log_prod _ _ fun p hp => by aesop ] ; exact Finset.sum_le_sum fun p hp => by rw [ Real.log_pow ] ;
      exact le_trans ( Finset.sum_le_sum_of_subset_of_nonneg ( Finset.filter_subset _ _ ) fun _ _ _ => mul_nonneg ( Nat.cast_nonneg _ ) ( Real.log_nonneg ( Nat.one_le_cast.mpr ( Nat.pos_of_mem_primeFactors ‹_› ) ) ) ) h_sum_bound;
    -- We can bound the sum of the powers of the prime factors greater than $y$ using the inequality $\sum_{p \in S} v_p(n) \log p \ge \log y \sum_{p \in S} v_p(n)$.
    have h_sum_bound_lower : (∑ p ∈ n.primeFactors.filter (fun p => y < p : ℕ → Prop), (Nat.factorization n) p * Real.log p) ≥ (Real.log y) * (∑ p ∈ n.primeFactors.filter (fun p => y < p : ℕ → Prop), (Nat.factorization n) p) := by
      push_cast [ Finset.mul_sum _ _ _ ];
      exact Finset.sum_le_sum fun p hp => by nlinarith only [ Real.log_le_log ( by positivity ) ( show ( p : ℝ ) ≥ y by exact le_of_lt ( Finset.mem_filter.mp hp |>.2 ) ), show ( 0 : ℝ ) ≤ Nat.factorization n p by positivity ] ;
    rw [ div_mul_eq_mul_div, le_div_iff₀ ] <;> nlinarith [ Real.log_pos hy, Real.log_pos one_lt_two ]

/-
The sum of logarithms of the divisor counts for prime factors at most $y$ is bounded by $y \log(\frac{\log n}{\log 2} + 1)$.
-/
lemma log_smooth_part_le (n : ℕ) (y : ℝ) (hy : 0 < y) :
  ∑ p ∈ n.primeFactors.filter (fun (p : ℕ) => (p : ℝ) ≤ y), Real.log ((n.factorization p : ℝ) + 1) ≤ y * Real.log (Real.log n / Real.log 2 + 1) := by
  by_cases hn : n = 0;
  · aesop;
  · field_simp;
    -- The number of terms in the sum is at most $y$.
    have h_num_terms : (Finset.filter (fun p : ℕ => (p : ℝ) ≤ y) n.primeFactors).card ≤ y := by
      refine' le_trans _ ( Nat.floor_le hy.le );
      exact_mod_cast le_trans ( Finset.card_le_card <| show Finset.filter ( fun p : ℕ => ( p : ℝ ) ≤ y ) n.primeFactors ⊆ Finset.Icc 1 ( Nat.floor y ) from fun p hp => Finset.mem_Icc.mpr ⟨ Nat.pos_of_mem_primeFactors <| Finset.mem_filter.mp hp |>.1, Nat.le_floor <| Finset.mem_filter.mp hp |>.2 ⟩ ) <| by simp;
    -- Each term in the sum is bounded by $\log(\frac{\log n}{\log 2} + 1)$.
    have h_term_bound : ∀ p ∈ Finset.filter (fun p : ℕ => (p : ℝ) ≤ y) n.primeFactors, Real.log ((n.factorization p) + 1) ≤ Real.log ((Real.log n + Real.log 2) / Real.log 2) := by
      intro p hp
      have h_vp_bound : (n.factorization p : ℝ) ≤ Real.log n / Real.log 2 := by
        field_simp;
        rw [ ← Real.log_pow ] ; gcongr ; norm_cast ; exact Nat.le_of_dvd ( Nat.pos_of_ne_zero hn ) ( Nat.ordProj_dvd _ _ ) |> le_trans ( Nat.pow_le_pow_left ( Nat.Prime.two_le <| Nat.prime_of_mem_primeFactors <| Finset.filter_subset _ _ hp ) _ );
      exact Real.log_le_log ( by positivity ) ( by rw [ le_div_iff₀ ( by positivity ) ] at *; linarith );
    exact le_trans ( Finset.sum_le_sum h_term_bound ) ( by simpa using mul_le_mul_of_nonneg_right h_num_terms <| Real.log_nonneg <| by rw [ le_div_iff₀ <| Real.log_pos <| by norm_num ] ; linarith [ Real.log_nonneg <| show ( n : ℝ ) ≥ 1 by exact Nat.one_le_cast.mpr <| Nat.pos_of_ne_zero hn, Real.log_pos <| show ( 2 : ℝ ) > 1 by norm_num ] )

/-
The limit of $\frac{(\log n)^\alpha \log \log n}{\log n / \log \log n}$ as $n \to \infty$ is 0 for $\alpha < 1$.
-/
lemma smooth_part_limit (α : ℝ) (hα : α < 1) :
  Filter.Tendsto (fun n => (Real.log n) ^ α * Real.log (Real.log n) / (Real.log n / Real.log (Real.log n))) Filter.atTop (nhds 0) := by
  -- We want to show $\frac{(\log n)^\alpha \log \log n}{\log n / \log \log n} \to 0$.
  -- This simplifies to $(\log n)^{\alpha-1} (\log \log n)^2$.
  suffices h_simplified : Filter.Tendsto (fun n : ℝ => (Real.log n) ^ (α - 1) * (Real.log (Real.log n)) ^ 2) Filter.atTop (nhds 0) by
    refine h_simplified.congr' ?_;
    filter_upwards [ Filter.eventually_gt_atTop 1, Filter.eventually_gt_atTop ( Real.exp 1 ) ] with n hn hn' ; rw [ Real.rpow_sub_one ( ne_of_gt <| Real.log_pos hn ) ] ; ring_nf;
    grind;
  -- Let $y = \log \log n$. Then we need to show that $y^2 / e^{(1-\alpha)y} \to 0$ as $y \to \infty$.
  suffices h_y : Filter.Tendsto (fun y : ℝ => y^2 / Real.exp ((1 - α) * y)) Filter.atTop (nhds 0) by
    have h_subst : Filter.Tendsto (fun n : ℝ => (Real.log (Real.log n)) ^ 2 / Real.exp ((1 - α) * Real.log (Real.log n))) Filter.atTop (nhds 0) := by
      exact h_y.comp ( Real.tendsto_log_atTop.comp ( Real.tendsto_log_atTop ) );
    refine h_subst.congr' ?_;
    filter_upwards [ Filter.eventually_gt_atTop 1, Filter.eventually_gt_atTop ( Real.exp 1 ) ] with n hn hn' ; rw [ Real.rpow_def_of_pos ( Real.log_pos hn ) ] ; ring_nf ;
    rw [ ← Real.exp_neg ] ; ring_nf;
  -- Let $z = (1 - \alpha)y$. Then we need to show that $z^2 / e^z \to 0$ as $z \to \infty$.
  suffices h_z : Filter.Tendsto (fun z : ℝ => z^2 / Real.exp z) Filter.atTop (nhds 0) by
    -- Apply the substitution $z = (1 - \alpha)y$ to rewrite the limit expression.
    have h_subst : Filter.Tendsto (fun y : ℝ => ((1 - α) * y)^2 / Real.exp ((1 - α) * y)) Filter.atTop (nhds 0) := by
      exact h_z.comp <| Filter.tendsto_id.const_mul_atTop <| by linarith;
    convert h_subst.div_const ( ( 1 - α ) ^ 2 ) using 2 <;> ring_nf;
    nlinarith [ inv_mul_cancel_left₀ ( by nlinarith : ( 1 - α * 2 + α ^ 2 ) ≠ 0 ) ( ( ‹_› : ℝ ) ^ 2 * ( Real.exp ( ‹_› - ‹_› * α ) ) ⁻¹ ) ];
  simpa [ Real.exp_neg ] using Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 2

/-
For sufficiently large $n$, the smooth part bound is smaller than a fraction of the total bound.
-/
lemma smooth_part_bound_asymptotic (ε : ℝ) (hε : 0 < ε) :
  ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
  let y := (Real.log n) ^ (1 / (1 + ε / 2))
  y * Real.log (Real.log n / Real.log 2 + 1) < (ε / 2) * Real.log 2 * Real.log n / Real.log (Real.log n) := by
  -- Using the lemma smooth_part_limit, we know that the limit of the left-hand side as $n \to \infty$ is 0.
  have h_lim : Filter.Tendsto (fun n : ℕ => (Real.log n) ^ (1 / (1 + ε / 2)) * Real.log (Real.log n / Real.log 2 + 1) / (Real.log n / Real.log (Real.log n))) Filter.atTop (nhds 0) := by
    have := smooth_part_limit ( 1 / ( 1 + ε / 2 ) ) ( by rw [ div_lt_iff₀ ] <;> linarith );
    -- Applying the fact that multiplication by a bounded function preserves limits.
    have h_mul : Filter.Tendsto (fun n : ℕ => (Real.log n) ^ (1 / (1 + ε / 2)) * Real.log (Real.log n) / (Real.log n / Real.log (Real.log n)) * (Real.log (Real.log n / Real.log 2 + 1) / Real.log (Real.log n))) Filter.atTop (nhds 0) := by
      convert this.comp tendsto_natCast_atTop_atTop |> Filter.Tendsto.mul <| show Filter.Tendsto ( fun n : ℕ => Real.log ( Real.log n / Real.log 2 + 1 ) / Real.log ( Real.log n ) ) Filter.atTop ( nhds 1 ) from ?_ using 2 <;> norm_num;
      -- We can use the fact that $\log(a + b) \sim \log a$ as $a \to \infty$ and $b$ is bounded.
      have h_log_approx : Filter.Tendsto (fun n : ℕ => Real.log (Real.log n / Real.log 2 + 1) / Real.log (Real.log n / Real.log 2)) Filter.atTop (nhds 1) := by
        -- We can use the fact that $\log(a + 1) \sim \log(a)$ as $a \to \infty$.
        have h_log_approx : Filter.Tendsto (fun a : ℝ => Real.log (a + 1) / Real.log a) Filter.atTop (nhds 1) := by
          -- We can use the fact that $\log(a + 1) = \log a + \log(1 + 1/a)$ and apply the properties of logarithms.
          have h_log_approx : Filter.Tendsto (fun a : ℝ => (Real.log a + Real.log (1 + 1 / a)) / Real.log a) Filter.atTop (nhds 1) := by
            ring_nf;
            exact le_trans ( Filter.Tendsto.add ( tendsto_const_nhds.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 1 ] with x hx using by rw [ mul_inv_cancel₀ ( ne_of_gt ( Real.log_pos hx ) ) ] ) ) ( Filter.Tendsto.mul ( Filter.Tendsto.log ( tendsto_const_nhds.add ( tendsto_inv_atTop_zero ) ) ( by norm_num ) ) ( tendsto_inv_atTop_zero.comp Real.tendsto_log_atTop ) ) ) ( by norm_num );
          refine h_log_approx.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with x hx using by rw [ one_add_div hx.ne', Real.log_div ] <;> norm_num <;> linarith );
        exact h_log_approx.comp <| Filter.Tendsto.atTop_div_const ( by positivity ) <| Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop;
      -- We can use the fact that $\log(a / b) = \log a - \log b$ to rewrite the denominator.
      have h_log_div : Filter.Tendsto (fun n : ℕ => Real.log (Real.log n / Real.log 2) / Real.log (Real.log n)) Filter.atTop (nhds 1) := by
        have h_log_div : Filter.Tendsto (fun n : ℕ => (Real.log (Real.log n) - Real.log (Real.log 2)) / Real.log (Real.log n)) Filter.atTop (nhds 1) := by
          norm_num [ sub_div ];
          exact le_trans ( Filter.Tendsto.sub ( tendsto_const_nhds.congr' <| by filter_upwards [ Filter.eventually_gt_atTop 2 ] with x hx; rw [ div_self <| ne_of_gt <| Real.log_pos <| show 1 < Real.log x from by rw [ Real.lt_log_iff_exp_lt <| by positivity ] ; exact Real.exp_one_lt_d9.trans_le <| by norm_num; linarith [ show ( x : ℝ ) ≥ 3 by exact_mod_cast hx ] ] ) <| tendsto_const_nhds.div_atTop <| Real.tendsto_log_atTop.comp <| Real.tendsto_log_atTop.comp <| tendsto_natCast_atTop_atTop ) <| by norm_num;
        refine h_log_div.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 2 ] with n hn; rw [ Real.log_div ( ne_of_gt <| Real.log_pos <| Nat.one_lt_cast.mpr <| by linarith ) ( ne_of_gt <| Real.log_pos <| by norm_num ) ] );
      have := h_log_approx.mul h_log_div;
      simpa using this.congr' ( by filter_upwards [ h_log_approx.eventually_ne one_ne_zero ] with n hn using by rw [ div_mul_div_cancel₀ ( by aesop ) ] );
    refine h_mul.congr' ?_;
    filter_upwards [ Filter.eventually_gt_atTop 2 ] with n hn ; by_cases h : Real.log ( Real.log n ) = 0 <;> simp_all +decide [ div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm ];
  -- By the definition of limit, for any ε' > 0, there exists an N such that for all n ≥ N, the ratio is less than ε'.
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ n ≥ N, (Real.log n) ^ (1 / (1 + ε / 2)) * Real.log (Real.log n / Real.log 2 + 1) / (Real.log n / Real.log (Real.log n)) < (ε / 2) * Real.log 2 := by
    simpa using h_lim.eventually ( gt_mem_nhds <| by positivity );
  refine' ⟨ N + 3, fun n hn => _ ⟩ ; specialize hN n ( by linarith ) ; rw [ div_lt_iff₀ ] at hN;
  · grind;
  · exact div_pos ( Real.log_pos ( by norm_cast; linarith ) ) ( Real.log_pos ( show 1 < Real.log n from by rw [ Real.lt_log_iff_exp_lt ( by norm_cast; linarith ) ] ; exact Real.exp_one_lt_d9.trans_le ( by norm_num; linarith [ show ( n : ℝ ) ≥ 3 by norm_cast; linarith ] ) ) )

/-
For sufficiently large $n$, the sum of logarithms of the divisor counts is bounded by $(1+\varepsilon) \log 2 \frac{\log n}{\log \log n}$.
-/
lemma log_divisor_bound_aux (ε : ℝ) (hε : 0 < ε) :
  ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
  ∑ p ∈ n.primeFactors, Real.log ((n.factorization p : ℝ) + 1) <
  (1 + ε) * Real.log 2 * Real.log n / Real.log (Real.log n) := by
  -- Choose $y$ as in \ref{ref:8098816}. Note $y > 1$ for large $n$.
  set y := fun n : ℕ => (Real.log n) ^ (1 / (1 + ε / 2)) with hy_def
  have hy_ge_1 (n : ℕ) (hn_ge_3 : 3 ≤ n) : 1 < y n := by
    exact Real.one_lt_rpow ( by rw [ Real.lt_log_iff_exp_lt ( by positivity ) ] ; exact Real.exp_one_lt_d9.trans_le ( by norm_num; linarith [ show ( n : ℝ ) ≥ 3 by norm_cast ] ) ) ( by positivity );
  -- By `smooth_part_bound_asymptotic`, this is bounded by $\frac{\varepsilon}{2} \log 2 \frac{\log n}{\log \log n}$.
  obtain ⟨N_smooth, hN_smooth⟩ : ∃ N_smooth : ℕ, ∀ n : ℕ, N_smooth ≤ n →
    y n * Real.log ((Real.log n) / Real.log 2 + 1) < (ε / 2) * Real.log 2 * Real.log n / Real.log (Real.log n) := by
      convert smooth_part_bound_asymptotic ε hε using 1;
  -- By `log_rough_part_le`, this bound becomes $(1+\varepsilon/2) \log 2 \frac{\log n}{\log \log n}$.
  have h_rough_part_bound (n : ℕ) (hn_ge_3 : 3 ≤ n) (hn_ge_N_smooth : N_smooth ≤ n) : (∑ p ∈ n.primeFactors.filter (fun (p : ℕ) => y n < (p : ℝ)), Real.log ((n.factorization p : ℝ) + 1)) ≤ (1 + ε / 2) * Real.log 2 * Real.log n / Real.log (Real.log n) := by
    -- Applying the lemma `log_rough_part_le` with $y = (\log n)^{\frac{1}{1+\varepsilon/2}}$.
    have h_rough_part_bound : (∑ p ∈ n.primeFactors.filter (fun (p : ℕ) => y n < (p : ℝ)), Real.log ((n.factorization p : ℝ) + 1)) ≤ (Real.log 2) / (Real.log (y n)) * Real.log n := by
      convert log_rough_part_le n ( y n ) ( hy_ge_1 n hn_ge_3 ) using 1;
    convert h_rough_part_bound using 1 ; rw [ Real.log_rpow ( Real.log_pos <| by norm_cast; linarith ) ] ; ring_nf;
    norm_num ; ring;
  -- By `log_smooth_part_le`, this is bounded by $y \log(\frac{\log n}{\log 2} + 1)$.
  have h_smooth_part_bound (n : ℕ) (hn_ge_3 : 3 ≤ n) (hn_ge_N_smooth : N_smooth ≤ n) : (∑ p ∈ n.primeFactors.filter (fun (p : ℕ) => (p : ℝ) ≤ y n), Real.log ((n.factorization p : ℝ) + 1)) ≤ y n * Real.log ((Real.log n) / Real.log 2 + 1) := by
    convert log_smooth_part_le n ( y n ) ( by linarith [ hy_ge_1 n hn_ge_3 ] ) using 1;
  refine' ⟨ N_smooth + 3, fun n hn => _ ⟩ ; specialize hN_smooth n ( by linarith ) ; specialize h_rough_part_bound n ( by linarith ) ( by linarith ) ; specialize h_smooth_part_bound n ( by linarith ) ( by linarith ) ; simp_all +decide [ Finset.sum_filter ];
  convert lt_of_le_of_lt ( add_le_add h_rough_part_bound h_smooth_part_bound ) ( add_lt_add_left hN_smooth _ ) using 1;
  · simpa only [ ← Finset.sum_add_distrib ] using Finset.sum_congr rfl fun x hx => by split_ifs <;> linarith;
  · ring

/-
For any $\varepsilon > 0$, there exists an $N$ such that for all $n \ge N$, the number of divisors of $n$ is less than $n^{\frac{(1+\varepsilon) \log 2}{\log \log n}}$.
-/
theorem divisor_bound (ε : ℝ) (hε : 0 < ε) :
  ∃ N : ℕ, ∀ n : ℕ, N ≤ n → (Nat.divisors n).card < (n : ℝ) ^ ((1 + ε) * Real.log 2 / Real.log (Real.log n)) := by
    -- Apply `log_divisor_bound_aux` to get an $N$ such that for $n \ge N$, $\sum \log(v_p+1) < (1+\varepsilon) \log 2 \frac{\log n}{\log \log n}$.
    obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∑ p ∈ n.factorization.support, (Real.log ((n.factorization p) + 1)) <
      (1 + ε) * Real.log 2 * Real.log n / Real.log (Real.log n) := by
        exact log_divisor_bound_aux ε hε;
    -- We know $d(n) = \prod (v_p+1)$, so $\log d(n) = \sum \log(v_p+1)$.
    have log_divisors_card : ∀ n : ℕ, n > 0 → Real.log (Nat.divisors n).card ≤ ∑ p ∈ n.factorization.support, (Real.log ((n.factorization p) + 1)) := by
      intro n hn
      have h_divisors_card : (Nat.divisors n).card = (∏ p ∈ n.factorization.support, (n.factorization p + 1)) := by
        -- Applying the formula for the number of divisors of a number from its prime factorization.
        have h_divisors_formula : ∀ {m : ℕ}, m ≠ 0 → (Nat.divisors m).card = ∏ p ∈ m.primeFactors, (Nat.factorization m p + 1) := by
          exact fun {m} a => Nat.card_divisors a;
        exact h_divisors_formula hn.ne';
      rw [ h_divisors_card, ← Real.log_prod ] <;> norm_cast ; aesop;
    refine' ⟨ N + 2, fun n hn => _ ⟩ ; specialize hN n ( by linarith ) ; specialize log_divisors_card n ( by linarith ) ; rw [ Real.lt_rpow_iff_log_lt ] <;> norm_num <;> try linarith [ Nat.pos_of_ne_zero ( show n ≠ 0 by linarith ) ] ;
    convert lt_of_le_of_lt log_divisors_card hN using 1 ; ring

/-
We proved that for any $\varepsilon > 0$, for sufficiently large $n$, the number of divisors $d(n)$ satisfies $d(n) < n^{\frac{(1+\varepsilon)\log 2}{\log \log n}}$.
The proof uses the bound $\log d(n) = \sum_{p|n} \log(v_p(n)+1)$.
We split the sum into primes $p \le y$ and $p > y$ where $y = (\log n)^{\frac{1}{1+\varepsilon/2}}$.
The contribution from large primes is bounded by $(1+\varepsilon/2) \log 2 \frac{\log n}{\log \log n}$.
The contribution from small primes is negligible.
Exponentiating gives the result.
-/


/-
Let $A_k=\{r(k-r): 1\leq r \leq k-1\}$.
-/
def A (k : ℕ) : Finset ℕ :=
  (Finset.Ioo 0 k).image (fun r => r * (k - r))

/-
Let $T_{m,n}=\{(M,N): NM=m^2-n^2; \ M+N<2m; \ 0<M\leq N<M+2n\}$, and write $\tau_{m,n}:=|T_{m,n}|$.
-/
def T (m n : ℕ) : Finset (ℕ × ℕ) :=
  (Nat.divisorsAntidiagonal (m^2 - n^2)).filter (fun ⟨M, N⟩ => M + N < 2 * m ∧ 0 < M ∧ M ≤ N ∧ N < M + 2 * n)

def τ (m n : ℕ) : ℕ := (T m n).card

/-
For every $x \in A_n$, there is a unique $k$ such that $2k \le n$ and $x = k(n-k)$.
-/
lemma unique_k_for_val (n : ℕ) (x : ℕ) (hx : x ∈ A n) :
  ∃! k, 2 * k ≤ n ∧ k * (n - k) = x := by
    -- Since $x \in A_n$, there exists at least one $k$ such that $2k \leq n$ and $k(n-k) = x$.
    have h_exists : ∃ k, 2 * k ≤ n ∧ k * (n - k) = x := by
      obtain ⟨ k, hk ⟩ := Finset.mem_image.mp hx;
      by_cases hk_le : k ≤ n / 2;
      · exact ⟨ k, by linarith [ Nat.div_mul_le_self n 2 ], hk.2 ⟩;
      · exact ⟨ n - k, by omega, by rw [ Nat.sub_sub_self ( by linarith [ Finset.mem_Ioo.mp hk.1 ] ) ] ; linarith ⟩;
    obtain ⟨ k, hk₁, hk₂ ⟩ := h_exists;
    use k;
    field_simp;
    exact ⟨ ⟨ hk₁, hk₂ ⟩, fun y hy => by nlinarith [ Nat.sub_add_cancel ( by linarith : k ≤ n ), Nat.sub_add_cancel ( by linarith : y ≤ n ) ] ⟩

/-
If $k(n-k) = r(m-r)$ with $n < m$, $2k \le n$, and $2r \le m$, then $r < k$.
-/
lemma r_lt_k_of_eq (m n k r : ℕ) (hmn : n < m) (hk : 2 * k ≤ n) (hr : 2 * r ≤ m) (h_eq : k * (n - k) = r * (m - r)) (hk_pos : 0 < k) :
  r < k := by
    -- Since $k \le n/2 < m/2$ and $r \le m/2$, and $f(x) = x(m-x)$ is strictly increasing on $[0, m/2]$, if $r \ge k$, then $f(r) \ge f(k)$.
    have h_inc : r ≥ k → r * (m - r) ≥ k * (m - k) := by
      exact fun h => by nlinarith only [ h, hr, hk, hmn, Nat.sub_add_cancel ( by linarith : k ≤ m ), Nat.sub_add_cancel ( by linarith : r ≤ m ) ] ;
    exact not_le.mp fun h => by nlinarith [ h_inc h, Nat.sub_add_cancel ( by linarith : k ≤ n ), Nat.sub_add_cancel ( by linarith : k ≤ m ) ] ;

/-
The map $(k, r) \mapsto (m - 2r - n + 2k, m - 2r + n - 2k)$.
-/
def to_T_pair (m n k r : ℕ) : ℕ × ℕ :=
  (m - 2 * r - n + 2 * k, m - 2 * r + n - 2 * k)

/-
The map $(k, r) \mapsto ((m - 2r) - (n - 2k), (m - 2r) + (n - 2k))$.
-/
def to_T_pair' (m n k r : ℕ) : ℕ × ℕ :=
  ((m - 2 * r) - (n - 2 * k), (m - 2 * r) + (n - 2 * k))

/-
The map $(k, r) \mapsto ((m - 2r) - (n - 2k), (m - 2r) + (n - 2k))$ maps solutions to $T_{m,n}$.
-/
lemma to_T_pair_mem_T' (m n k r : ℕ) (hmn : n < m) (hk : 2 * k ≤ n) (hr : 2 * r ≤ m) (h_eq : k * (n - k) = r * (m - r)) (hk_pos : 0 < k) :
  to_T_pair' m n k r ∈ T m n := by
    refine' Finset.mem_filter.mpr ⟨ _, _ ⟩;
    · rw [ Nat.mem_divisorsAntidiagonal ];
      zify [ to_T_pair' ];
      repeat rw [ Nat.cast_sub ] <;> push_cast <;> repeat nlinarith only [ hk, hr, hmn ] ;
      · zify at *;
        exact ⟨ by rw [ Nat.cast_sub ( by linarith ), Nat.cast_sub ( by linarith ) ] at h_eq; nlinarith, by nlinarith ⟩;
      · exact Nat.sub_le_of_le_add <| by linarith [ Nat.sub_add_cancel <| show 2 * r ≤ m from hr, Nat.sub_add_cancel <| show 2 * k ≤ n from hk, r_lt_k_of_eq m n k r hmn hk hr h_eq hk_pos ] ;
    · refine' ⟨ _, _, _, _ ⟩;
      · zify;
        repeat rw [ Nat.cast_sub ] <;> push_cast <;> try linarith;
        · linarith [ show r > 0 from Nat.pos_of_ne_zero fun h => by subst h; nlinarith [ Nat.sub_pos_of_lt ( show k < n from by linarith ) ] ];
        · exact le_of_not_gt fun h => by nlinarith [ Nat.sub_add_cancel ( by linarith : 2 * k ≤ n ), Nat.sub_add_cancel ( by linarith : 2 * r ≤ m ), Nat.sub_add_cancel ( by linarith : k ≤ n ), Nat.sub_add_cancel ( by linarith : r ≤ m ) ] ;
      · -- Since $r < k$ (by `r_lt_k_of_eq`), $2r < 2k$.
        have hr_lt_hk : 2 * r < 2 * k := by
          exact Nat.mul_lt_mul_of_pos_left ( r_lt_k_of_eq m n k r hmn hk hr h_eq hk_pos ) zero_lt_two;
        omega;
      · exact le_add_of_le_of_nonneg ( Nat.sub_le _ _ ) ( Nat.zero_le _ );
      · omega

/-
The map `to_T_pair'` is injective on the set of solutions.
-/
lemma to_T_pair_inj_on_solutions (m n k1 r1 k2 r2 : ℕ) (hmn : n < m)
  (hk1 : 2 * k1 ≤ n) (hr1 : 2 * r1 ≤ m) (h_eq1 : k1 * (n - k1) = r1 * (m - r1)) (hk1_pos : 0 < k1)
  (hk2 : 2 * k2 ≤ n) (hr2 : 2 * r2 ≤ m) (h_eq2 : k2 * (n - k2) = r2 * (m - r2)) (hk2_pos : 0 < k2)
  (h_pair : to_T_pair' m n k1 r1 = to_T_pair' m n k2 r2) :
  k1 = k2 ∧ r1 = r2 := by
    unfold to_T_pair' at h_pair;
    have h_eq1' : r1 < k1 := by
      exact r_lt_k_of_eq m n k1 r1 hmn hk1 hr1 h_eq1 hk1_pos
    have h_eq2' : r2 < k2 := by
      exact r_lt_k_of_eq m n k2 r2 hmn hk2 hr2 h_eq2 hk2_pos;
    grind

/-
The map $(M, N) \mapsto (k, r)$ defined by $2r = m - (M+N)/2$ and $2k = n - (N-M)/2$.
-/
def from_T_pair (m n M N : ℕ) : ℕ × ℕ :=
  let X := (M + N) / 2
  let Y := (N - M) / 2
  let r := (m - X) / 2
  let k := (n - Y) / 2
  (k, r)

/-
Functions to extract the unique $k$ and $r$ for a given $x$.
-/
noncomputable def get_k (n : ℕ) (x : ℕ) (hx : x ∈ A n) : ℕ :=
  Classical.choose (unique_k_for_val n x hx)

noncomputable def get_r (m : ℕ) (x : ℕ) (hx : x ∈ A m) : ℕ :=
  Classical.choose (unique_k_for_val m x hx)

/-
$|A_n \cap A_m| \le \tau_{m,n}$ for $m > n$.
-/
theorem card_intersection_le (m n : ℕ) (hmn : n < m) :
  (A n ∩ A m).card ≤ τ m n := by
    -- By definition of $A$, for each $x \in A_n \cap A_m$, there exist unique $k$ and $r$ such that $x = k(n-k) = r(m-r)$.
    have h_map : ∀ x ∈ A n ∩ A m, ∃ k r : ℕ, 2 * k ≤ n ∧ 2 * r ≤ m ∧ k * (n - k) = r * (m - r) ∧ x = k * (n - k) := by
      simp +zetaDelta at *;
      intro x hx_n hx_m;
      obtain ⟨ k, hk ⟩ := Finset.mem_image.mp hx_n;
      obtain ⟨ r, hr ⟩ := Finset.mem_image.mp hx_m;
      use if 2 * k ≤ n then k else n - k, by
        split_ifs <;> omega, if 2 * r ≤ m then r else m - r, by
        split_ifs <;> omega;
      grind;
    choose! k r hk hr h_eq h_card using h_map;
    -- By definition of $T$, the map $x \mapsto \text{to\_T\_pair'}(m, n, k_x, r_x)$ is injective on $A_n \cap A_m$.
    have h_inj : ∀ x y : ℕ, x ∈ A n ∩ A m → y ∈ A n ∩ A m → x ≠ y → to_T_pair' m n (k x) (r x) ≠ to_T_pair' m n (k y) (r y) := by
      intros x y hx hy hxy h_eq_pair;
      have := to_T_pair_inj_on_solutions m n ( k x ) ( r x ) ( k y ) ( r y ) hmn ( hk x hx ) ( hr x hx ) ( h_eq x hx ) ( Nat.pos_of_ne_zero fun h => ?_ ) ( hk y hy ) ( hr y hy ) ( h_eq y hy ) ( Nat.pos_of_ne_zero fun h => ?_ ) h_eq_pair;
      · grind;
      · specialize h_card x hx; simp +decide [ h ] at h_card;
        exact absurd h_card ( by rw [ Finset.mem_inter ] at hx; exact ne_of_gt ( Finset.mem_image.mp ( hx.1 ) |> fun ⟨ r, hr₁, hr₂ ⟩ => hr₂.symm ▸ Nat.mul_pos ( Finset.mem_Ioo.mp hr₁ |>.1 ) ( Nat.sub_pos_of_lt ( Finset.mem_Ioo.mp hr₁ |>.2 ) ) ) );
      · specialize h_card y hy; simp +decide [ h ] at h_card;
        simp_all +decide [ A ];
        exact absurd hy.1 ( by rintro ⟨ a, ⟨ ha₁, ha₂ ⟩, ha₃ | ha₃ ⟩ <;> omega );
    -- By definition of $T$, the image of $A_n \cap A_m$ under the map $x \mapsto \text{to\_T\_pair'}(m, n, k_x, r_x)$ is a subset of $T_{m,n}$.
    have h_image : Finset.image (fun x => to_T_pair' m n (k x) (r x)) (A n ∩ A m) ⊆ T m n := by
      intro x hx
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx;
      convert to_T_pair_mem_T' m n ( k y ) ( r y ) hmn ( hk y hy ) ( hr y hy ) ( h_eq y hy ) ( Nat.pos_of_ne_zero fun h => ?_ ) using 1;
      specialize h_card y hy; simp +decide [ h ] at h_card;
      simp_all +decide [ A ];
      exact absurd hy.1 ( by rintro ⟨ a, ⟨ ha₁, ha₂ ⟩, ha₃ | ha₃ ⟩ <;> omega );
    have := Finset.card_le_card h_image; rw [ Finset.card_image_of_injOn fun x hx y hy hxy => by contrapose! hxy; exact h_inj x y hx hy hxy ] at this; exact this;

/-
If $m$ is even and $n$ is odd, and $MN = m^2 - n^2$ with $M \le N$, then $M+N$ is divisible by 4 and $N-M \equiv 2 \pmod 4$.
-/
lemma mod_4_properties (m n M N : ℕ) (hmn : n < m) (hm : Even m) (hn : Odd n) (hMN : M * N = m^2 - n^2) (h_le : M ≤ N) :
  (M + N) % 4 = 0 ∧ (N - M) % 4 = 2 := by
    -- Since $m^2 \equiv 0 \pmod{4}$ and $n^2 \equiv 1 \pmod{4}$, we have $(m^2 - n^2) \equiv 3 \pmod{4}$.
    have h_mod4 : (M * N) % 4 = 3 := by
      rw [ hMN, ← Nat.mod_add_div ( m ^ 2 ) 4, ← Nat.mod_add_div ( n ^ 2 ) 4 ] ; obtain ⟨ k, rfl ⟩ := hn; obtain ⟨ l, rfl ⟩ := hm; ring_nf; norm_num [ Nat.add_mod, Nat.mul_mod ] ;
      zify;
      rw [ Int.ofNat_sub ] <;> norm_num [ Int.add_emod, Int.sub_emod, Int.mul_emod ];
      nlinarith [ Nat.div_mul_le_self ( 1 + k * 4 + k ^ 2 * 4 ) 4 ];
    rw [ ← Nat.mod_add_div N 4, ← Nat.mod_add_div M 4 ] at *; norm_num [ Nat.add_mod, Nat.mul_mod ] at *; have := Nat.mod_lt M zero_lt_four; have := Nat.mod_lt N zero_lt_four; interval_cases M % 4 <;> interval_cases N % 4 <;> simp_all ( config := { decide := Bool.true } ) only;
    · exact ⟨ trivial, by omega ⟩;
    · exact ⟨ trivial, by omega ⟩

/-
If $m$ is even and $n$ is odd, then for any $(M, N) \in T_{m,n}$, the values $k$ and $r$ derived from `from_T_pair` are valid integers.
-/
lemma from_T_pair_valid_integers (m n M N : ℕ) (hmn : n < m) (hm : Even m) (hn : Odd n) (hT : (M, N) ∈ T m n) :
  let (k, r) := from_T_pair m n M N
  2 * k = n - (N - M) / 2 ∧ 2 * r = m - (M + N) / 2 := by
    -- Let's simplify the expression for $k$ and $r$.
    simp [from_T_pair];
    -- By `mod_4_properties`, $M+N$ is divisible by 4 and $N-M \equiv 2 \pmod 4$.
    have h_mod : (M + N) % 4 = 0 ∧ (N - M) % 4 = 2 := by
      apply mod_4_properties m n M N hmn hm hn;
      · unfold T at hT; aesop;
      · exact Finset.mem_filter.mp hT |>.2.2.2.1;
    grind

/-
If $m$ is even and $n$ is odd, then for any $(M, N) \in T_{m,n}$, the values $k$ and $r$ derived from `from_T_pair` correspond to a valid solution.
-/
lemma from_T_pair_is_solution (m n M N : ℕ) (hmn : n < m) (hm : Even m) (hn : Odd n) (hT : (M, N) ∈ T m n) :
  let (k, r) := from_T_pair m n M N
  2 * k ≤ n ∧ 2 * r ≤ m ∧ k * (n - k) = r * (m - r) ∧ 0 < k ∧ 0 < r := by
    -- By definition of $from_T_pair$, we know that $2k = n - (N-M)/2$ and $2r = m - (M+N)/2$.
    obtain ⟨hk, hr⟩ := from_T_pair_valid_integers m n M N hmn hm hn hT;
    -- By definition of $from_T_pair$, we know that $k(n-k) = r(m-r)$.
    have h_eq : (n - (N - M) / 2) * (n + (N - M) / 2) = (m - (M + N) / 2) * (m + (M + N) / 2) := by
      have h_eq : (n - (N - M) / 2) * (n + (N - M) / 2) = n^2 - ((N - M) / 2)^2 ∧ (m - (M + N) / 2) * (m + (M + N) / 2) = m^2 - ((M + N) / 2)^2 := by
        constructor <;> rw [ Nat.mul_comm ] <;> rw [ ← Nat.sq_sub_sq ];
      have h_eq : m^2 - n^2 = ((M + N) / 2)^2 - ((N - M) / 2)^2 := by
        have h_eq : m^2 - n^2 = M * N := by
          unfold T at hT; aesop;
        cases le_total N M <;> simp_all +decide [ Nat.even_iff ];
        · exact absurd ( congr_arg Even hk ) ( by simp +decide [ hn, parity_simps ] );
        · -- By expanding the right-hand side, we can verify the equality.
          have h_expand : ((M + N) / 2) ^ 2 - ((N - M) / 2) ^ 2 = (M * N) := by
            have h_even : Even (M + N) ∧ Even (N - M) := by
              replace h_eq := congr_arg Even h_eq; simp_all +decide [ Nat.even_sub, parity_simps ] ;
              by_cases heven : Even M <;> by_cases heven' : Even N <;> simp_all +decide [ Nat.even_sub ( show n ^ 2 ≤ m ^ 2 from Nat.pow_le_pow_left hmn.le 2 ), parity_simps ];
              · grind;
              · grind;
              · exact ⟨ iff_of_false ( by simpa using heven ) ( by simpa using heven' ), iff_of_false ( by simpa using heven' ) ( by simpa using heven ) ⟩
            exact Nat.sub_eq_of_eq_add <| by nlinarith only [ Nat.div_mul_cancel ( even_iff_two_dvd.mp h_even.1 ), Nat.div_mul_cancel ( even_iff_two_dvd.mp h_even.2 ), Nat.sub_add_cancel ‹_› ] ;
          exact h_expand.symm;
      rw [ Nat.sub_eq_iff_eq_add ] at h_eq;
      · rw [ ‹ ( n - ( N - M ) / 2 ) * ( n + ( N - M ) / 2 ) = n ^ 2 - ( ( N - M ) / 2 ) ^ 2 ∧ ( m - ( M + N ) / 2 ) * ( m + ( M + N ) / 2 ) = m ^ 2 - ( ( M + N ) / 2 ) ^ 2 ›.1, ‹ ( n - ( N - M ) / 2 ) * ( n + ( N - M ) / 2 ) = n ^ 2 - ( ( N - M ) / 2 ) ^ 2 ∧ ( m - ( M + N ) / 2 ) * ( m + ( M + N ) / 2 ) = m ^ 2 - ( ( M + N ) / 2 ) ^ 2 ›.2, h_eq ];
        rw [ tsub_add_eq_add_tsub ];
        · rw [ Nat.sub_right_comm, Nat.add_sub_cancel_left ];
        · exact Nat.pow_le_pow_left ( Nat.div_le_div_right ( by omega ) ) _;
      · gcongr;
    -- By definition of $from_T_pair$, we know that $k > 0$ and $r > 0$.
    have hk_pos : 0 < (n - (N - M) / 2) / 2 := by
      by_contra hk_neg;
      simp_all +decide [ Nat.even_iff ];
      interval_cases _ : n - ( N - M ) / 2 <;> simp_all +decide;
      cases h_eq <;> simp_all +decide [ Nat.sub_eq_zero_iff_le ];
      linarith [ Finset.mem_filter.mp hT |>.2.1, Nat.div_mul_le_self ( M + N ) 2 ]
    have hr_pos : 0 < (m - (M + N) / 2) / 2 := by
      have hM_pos : M + N < 2 * m := by
        exact Finset.mem_filter.mp hT |>.2.1;
      exact Nat.div_pos ( Nat.le_of_dvd ( Nat.sub_pos_of_lt ( by omega ) ) ( Nat.dvd_of_mod_eq_zero ( by rw [ Nat.mod_eq_zero_of_dvd ] ; exact Nat.dvd_of_mod_eq_zero ( by omega ) ) ) ) zero_lt_two;
    field_simp;
    refine' ⟨ _, _, _, hk_pos, hr_pos ⟩;
    · unfold from_T_pair; aesop;
    · exact hr.le.trans ( Nat.sub_le _ _ );
    · unfold from_T_pair;
      rw [ show n - ( n - ( N - M ) / 2 ) / 2 = ( n + ( N - M ) / 2 ) / 2 by omega, show m - ( m - ( M + N ) / 2 ) / 2 = ( m + ( M + N ) / 2 ) / 2 by omega ];
      convert congr_arg ( · / 4 ) h_eq using 1 <;> ring_nf;
      · rw [ ← Nat.mul_div_mul_comm ];
        · ring_nf;
        · exact hk ▸ dvd_mul_right _ _;
        · cases hn ; cases hm ; omega;
      · rw [ ← Nat.mul_div_assoc ];
        · rw [ ← hr ] ; ring_nf;
          norm_num [ ← add_mul ];
          grind;
        · grind

/-
If $m$ is even and $n$ is odd, then $|A_n \cap A_m| = \tau_{m,n}$.
-/
theorem card_intersection_eq (m n : ℕ) (hmn : n < m) (hm : Even m) (hn : Odd n) :
  (A n ∩ A m).card = τ m n := by
    -- We'll use that $|A_n \cap A_m| \le |T_{m,n}|$ from `card_intersection_le`.
    have h_le : (A n ∩ A m).card ≤ τ m n := by
      apply card_intersection_le m n hmn;
    -- To show that $|A_n \cap A_m| \ge \tau_{m,n}$, we need to prove that for every $(M, N) \in T_{m,n}$, there exists $x \in A_n \cap A_m$ such that $(M, N) \in T_{m,n}$.
    have h_ge : ∀ (M N : ℕ), (M, N) ∈ T m n → ∃ x ∈ A n ∩ A m, let (k, r) := from_T_pair m n M N; x = k * (n - k) := by
      intro M N hMN
      obtain ⟨k, r, hk, hr, h_eq⟩ : ∃ k r : ℕ, 2 * k ≤ n ∧ 2 * r ≤ m ∧ k * (n - k) = r * (m - r) ∧ 0 < k ∧ 0 < r ∧ let (k', r') := from_T_pair m n M N; k = k' ∧ r = r' := by
        exact ⟨ _, _, from_T_pair_is_solution m n M N hmn hm hn hMN |>.1, from_T_pair_is_solution m n M N hmn hm hn hMN |>.2.1, from_T_pair_is_solution m n M N hmn hm hn hMN |>.2.2.1, from_T_pair_is_solution m n M N hmn hm hn hMN |>.2.2.2.1, from_T_pair_is_solution m n M N hmn hm hn hMN |>.2.2.2.2, rfl, rfl ⟩;
      norm_num +zetaDelta at *;
      exact ⟨ Finset.mem_image.mpr ⟨ ( from_T_pair m n M N ).1, Finset.mem_Ioo.mpr ⟨ by linarith, by linarith ⟩, by simp +decide [ ← h_eq.2.2.2.1 ] ⟩, Finset.mem_image.mpr ⟨ r, Finset.mem_Ioo.mpr ⟨ by linarith, by linarith ⟩, by simp +decide [ ← h_eq.2.2.2.1, h_eq.1 ] ⟩ ⟩;
    refine' le_antisymm h_le _;
    choose! f hf₁ hf₂ using h_ge;
    -- We'll use that $f$ is injective on $T_{m,n}$ to show that $|T_{m,n}| \le |A_n \cap A_m|$.
    have h_inj : ∀ (M N M' N' : ℕ), (M, N) ∈ T m n → (M', N') ∈ T m n → f M N = f M' N' → (M, N) = (M', N') := by
      intros M N M' N' hT hT' h_eq
      have h_k_r : let (k, r) := from_T_pair m n M N; let (k', r') := from_T_pair m n M' N'; k = k' ∧ r = r' := by
        have h_k_r : let (k, r) := from_T_pair m n M N; let (k', r') := from_T_pair m n M' N'; k * (n - k) = k' * (n - k') ∧ r * (m - r) = r' * (m - r') := by
          have h_k_r : let (k, r) := from_T_pair m n M N; let (k', r') := from_T_pair m n M' N'; k * (n - k) = r * (m - r) ∧ k' * (n - k') = r' * (m - r') := by
            exact ⟨ from_T_pair_is_solution m n M N hmn hm hn hT |>.2.2.1, from_T_pair_is_solution m n M' N' hmn hm hn hT' |>.2.2.1 ⟩;
          grind;
        have h_k_r_unique : ∀ (k r k' r' : ℕ), 2 * k ≤ n → 2 * r ≤ m → 2 * k' ≤ n → 2 * r' ≤ m → k * (n - k) = k' * (n - k') → r * (m - r) = r' * (m - r') → k = k' ∧ r = r' := by
          intros k r k' r' hk hr hk' hr' h_eq_k h_eq_r
          have h_k_eq_k' : k = k' := by
            by_contra h_contra;
            exact h_contra <| by nlinarith only [ hk, hk', h_eq_k, Nat.sub_add_cancel ( by linarith : k ≤ n ), Nat.sub_add_cancel ( by linarith : k' ≤ n ) ] ;
          have h_r_eq_r' : r = r' := by
            rw [ Nat.mul_sub_left_distrib, Nat.mul_sub_left_distrib ] at h_eq_r;
            rw [ tsub_eq_iff_eq_add_of_le ( by nlinarith only [ hr, hr' ] ) ] at h_eq_r;
            rw [ tsub_add_eq_add_tsub ( by nlinarith only [ hr', hmn ] ) ] at h_eq_r;
            rw [ eq_tsub_iff_add_eq_of_le ] at h_eq_r;
            · nlinarith only [ h_eq_r, hmn, hr, hr' ];
            · exact le_add_of_le_of_nonneg ( Nat.mul_le_mul_left _ ( by linarith ) ) ( Nat.zero_le _ )
          exact ⟨h_k_eq_k', h_r_eq_r'⟩;
        apply h_k_r_unique;
        any_goals omega;
        · convert h_k_r.1 using 1;
        · convert h_k_r.2 using 1;
      have h_eq_pair : to_T_pair' m n (from_T_pair m n M N).1 (from_T_pair m n M N).2 = (M, N) ∧ to_T_pair' m n (from_T_pair m n M' N').1 (from_T_pair m n M' N').2 = (M', N') := by
        have h_eq_pair : ∀ (M N : ℕ), (M, N) ∈ T m n → to_T_pair' m n (from_T_pair m n M N).1 (from_T_pair m n M N).2 = (M, N) := by
          intros M N hT
          obtain ⟨hk, hr, h_eq, hk_pos, hr_pos⟩ := from_T_pair_is_solution m n M N hmn hm hn hT;
          have := from_T_pair_valid_integers m n M N hmn hm hn hT; simp_all +decide
          unfold to_T_pair'; simp +decide [ this ] ;
          have h_mod4 : (M + N) % 4 = 0 ∧ (N - M) % 4 = 2 := by
            apply mod_4_properties m n M N hmn hm hn (by
            unfold T at hT; aesop;) (by
            exact Finset.mem_filter.mp hT |>.2.2.2.1);
          omega;
        exact ⟨ h_eq_pair M N hT, h_eq_pair M' N' hT' ⟩;
      grind;
    have h_card_le : (Finset.image (fun p => f p.1 p.2) (T m n)).card ≤ (A n ∩ A m).card := by
      exact Finset.card_le_card fun x hx => by obtain ⟨ p, hp, rfl ⟩ := Finset.mem_image.mp hx; exact hf₁ _ _ hp;
    rwa [ Finset.card_image_of_injOn fun p hp q hq h => h_inj _ _ _ _ hp hq h ] at h_card_le

/-
Let $m>n$. Then $|A_n\cap A_m|\leq \tau_{m,n}$. Furthermore if $m$ is even and $n$ is odd then equality holds.
-/
theorem theorem_1_1 (m n : ℕ) (hmn : n < m) :
  (A n ∩ A m).card ≤ τ m n ∧ (Even m → Odd n → (A n ∩ A m).card = τ m n) := by
    exact ⟨ card_intersection_le m n hmn, fun hm hn => card_intersection_eq m n hmn hm hn ⟩

/-
For every $\varepsilon>0$ there exists a threshold $n_0$ such that $m>n>n_0$ we have 
$$
|A_n\cap A_m|<(m)^{\frac{(2+\varepsilon)\log 2}{\log\log m}}
$$
-/
theorem corollary_1_2 (ε : ℝ) (hε : 0 < ε) :
  ∃ n₀ : ℕ, ∀ m n : ℕ, n₀ < n → n < m →
  ((A n ∩ A m).card : ℝ) < (m : ℝ) ^ ((2 + ε) * Real.log 2 / Real.log (Real.log m)) := by
    -- Set $\delta = \frac{\varepsilon}{4}$.
    obtain ⟨N₀, hN₀⟩ : ∃ N₀ : ℕ, ∀ x : ℕ, x ≥ N₀ → (Nat.divisors x).card < (x : ℝ) ^ ((1 + ε / 4) * Real.log 2 / Real.log (Real.log x)) := by
      have := divisor_bound ( ε / 4 ) ( by positivity ) ; aesop;
    -- Let $n₀ = N₀ + 1$.
    use N₀ + 1;
    intros m n hn hm
    have h_div : (Nat.divisors (m^2 - n^2)).card < (m^2 - n^2 : ℝ) ^ ((1 + ε / 4) * Real.log 2 / Real.log (Real.log (m^2 - n^2))) := by
      convert hN₀ ( m ^ 2 - n ^ 2 ) _ using 1;
      · rw [ Nat.cast_sub ( by nlinarith ) ] ; push_cast ; ring;
      · exact le_tsub_of_add_le_left ( by nlinarith only [ hn, hm ] );
    -- Since $m^2 - n^2 < m^2$, we have $(m^2 - n^2)^{\frac{(1+\delta)\log 2}{\log\log(m^2-n^2)}} < (m^2)^{\frac{(1+\delta)\log 2}{\log\log m}}$.
    have h_exp : (m^2 - n^2 : ℝ) ^ ((1 + ε / 4) * Real.log 2 / Real.log (Real.log (m^2 - n^2))) < (m^2 : ℝ) ^ ((1 + ε / 4) * Real.log 2 / Real.log (Real.log m)) := by
      refine' lt_of_le_of_lt ( Real.rpow_le_rpow ( _ ) ( sub_le_self _ <| by positivity ) <| _ ) _;
      · exact sub_nonneg_of_le ( by gcongr );
      · exact le_trans ( by norm_num ) ( div_nonneg ( by positivity ) ( Real.log_nonneg ( show 1 ≤ Real.log ( m ^ 2 - n ^ 2 ) from by rw [ Real.le_log_iff_exp_le ( sub_pos.mpr <| by norm_cast; nlinarith ) ] ; exact Real.exp_one_lt_d9.le.trans <| by norm_num; nlinarith [ show ( m : ℝ ) ≥ n + 1 by norm_cast, show ( n : ℝ ) ≥ N₀ + 2 by norm_cast ] ) ) );
      · refine' Real.rpow_lt_rpow_of_exponent_lt _ _;
        · exact one_lt_pow₀ ( by norm_cast; linarith ) ( by norm_num );
        · gcongr;
          · exact Real.log_pos <| by rw [ Real.lt_log_iff_exp_lt <| by norm_cast; linarith ] ; exact Real.exp_one_lt_d9.trans_le <| by norm_num; linarith [ show ( m : ℝ ) ≥ 3 by norm_cast; linarith ] ;
          · exact Real.log_pos ( by norm_cast; linarith );
          · norm_cast ; linarith;
          · rcases n with ( _ | _ | n ) <;> rcases m with ( _ | _ | m ) <;> norm_num at *;
            exact lt_tsub_iff_left.mpr ( by norm_cast; nlinarith only [ hm ] );
    refine' lt_of_le_of_lt _ ( h_div.trans h_exp ) |> lt_of_lt_of_le <| _;
    · -- By definition of $A$, we know that $|A_n \cap A_m| \le \tau_{m,n}$.
      have h_card_le_tau : (A n ∩ A m).card ≤ τ m n := by
        exact card_intersection_le m n hm;
      refine' mod_cast h_card_le_tau.trans _;
      refine' Finset.card_filter_le _ _ |> le_trans <| _;
      rw [ Nat.divisorsAntidiagonal ];
      refine' le_trans ( Finset.card_le_card _ ) _;
      exact Finset.image ( fun x => ( x, ( m ^ 2 - n ^ 2 ) / x ) ) ( Nat.divisors ( m ^ 2 - n ^ 2 ) );
      · simp +decide [ Finset.subset_iff ];
        exact fun a b x hx₁ hx₂ hx₃ hx₄ hx₅ => ⟨ ⟨ hx₄.symm ▸ Nat.dvd_of_mod_eq_zero ( by rw [ Nat.mod_eq_zero_of_dvd ] ; exact ⟨ ( m ^ 2 - n ^ 2 ) / x, by linarith ⟩ ), Nat.sub_ne_zero_of_lt ( by nlinarith ) ⟩, hx₄.symm ▸ hx₅ ⟩;
      · exact Finset.card_image_le;
    · rw [ ← Real.rpow_natCast, ← Real.rpow_mul ( Nat.cast_nonneg _ ) ] ; ring_nf ; norm_num;
      exact Real.rpow_le_rpow_of_exponent_le ( mod_cast by linarith ) ( by nlinarith [ show 0 ≤ ε * Real.log 2 * ( Real.log ( Real.log m ) ) ⁻¹ by exact mul_nonneg ( mul_nonneg hε.le ( Real.log_nonneg one_le_two ) ) ( inv_nonneg.mpr ( Real.log_nonneg ( show 1 ≤ Real.log m by rw [ Real.le_log_iff_exp_le ( by norm_cast; linarith ) ] ; exact Real.exp_one_lt_d9.le.trans ( by norm_num; linarith [ show ( m : ℝ ) ≥ 3 by norm_cast; linarith ] ) ) ) ) ] )

/-
Construction of $m, n$ for Theorem 1.3.
-/
def construction_1_3 (s p α : ℕ) : ℕ × ℕ :=
  let m := 2^α * p^s + 1
  let n := m - 2
  (m, n)

/-
The set of pairs $(M_i, N_i)$ for $i \in \{0, \dots, s-1\}$.
Note: The paper uses $N_i = 2^{\alpha+1} p^i$ and $M_i = 2 p^{s-i}$ for $0 \le i \le s$.
And excludes $i=s$.
So $i$ ranges from $0$ to $s-1$.
$M_i = 2 p^{s-i}$.
$N_i = 2^{\alpha+1} p^i$.
Wait, if $i=0$, $M_0 = 2 p^s, N_0 = 2^{\alpha+1}$.
If $i=s-1$, $M_{s-1} = 2 p^1, N_{s-1} = 2^{\alpha+1} p^{s-1}$.
My definition above uses `s - 1 - i` and `i + 1`.
Let's match the paper exactly.
Paper: $N_i = 2^{\alpha+1} p^i, M_i = 2 p^{s-i}$.
Range $0 \le i \le s$.
Excluded $i=s$.
So valid $i \in \{0, \dots, s-1\}$.
Let's use this indexing.
$M_i = 2 p^{s-i}$.
$N_i = 2^{\alpha+1} p^i$.
For $i \in \{0, \dots, s-1\}$.
-/
def construction_pairs (s p α : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range s).image (fun i => (2 * p^(s - 1 - i), 2^(α + 1) * p^(i + 1)))

/-
The set of pairs $(M_i, N_i)$ for $i \in \{0, \dots, s-1\}$.
$M_i = 2 p^{s-i}$.
$N_i = 2^{\alpha+1} p^i$.
This matches the paper's definition for the valid range.
-/
def construction_pairs' (s p α : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range s).image (fun i => (2 * p^(s - i), 2^(α + 1) * p^i))

/-
Each pair in `construction_pairs'` belongs to $T_{m,n}$.
-/
lemma construction_pairs_in_T (s p α : ℕ) (hp : Odd p) (hp_ge_3 : 3 ≤ p) (h_pow : p^s < 2^α) :
  let (m, n) := construction_1_3 s p α
  construction_pairs' s p α ⊆ T m n := by
    unfold construction_pairs';
    intro hx;
    simp +zetaDelta at *;
    rintro x hx rfl;
    refine' Finset.mem_filter.mpr ⟨ _, _ ⟩;
    · rw [ Nat.mem_divisorsAntidiagonal ];
      zify;
      rw [ Nat.cast_sub ] <;> norm_num <;> ring_nf;
      · rw [ Nat.cast_sub <| Nat.one_le_iff_ne_zero.mpr <| by positivity ] ; push_cast ; ring_nf;
        exact ⟨ by rw [ ← pow_add, Nat.sub_add_cancel hx.le ], by positivity ⟩;
      · nlinarith [ Nat.sub_add_cancel ( show 1 ≤ p ^ s * 2 ^ α from Nat.mul_pos ( pow_pos ( by linarith ) _ ) ( pow_pos ( by linarith ) _ ) ), pow_mul p s 2, pow_mul 2 α 2 ];
    · refine' ⟨ _, _, _, _ ⟩;
      · rw [ show p ^ s = p ^ ( s - x ) * p ^ x by rw [ ← pow_add, Nat.sub_add_cancel hx.le ] ] at *;
        ring_nf at *;
        nlinarith [ Nat.zero_le ( p ^ ( s - x ) * p ^ x ), Nat.zero_le ( p ^ x * 2 ^ α ), Nat.zero_le ( p ^ ( s - x ) * 2 ^ α ), Nat.zero_le ( p ^ x * 2 ), Nat.zero_le ( p ^ ( s - x ) * 2 ), Nat.zero_le ( p ^ x * 2 ^ α * 2 ), Nat.zero_le ( p ^ ( s - x ) * 2 ^ α * 2 ), Nat.pow_le_pow_right ( by linarith : 1 ≤ p ) ( show s - x ≥ 1 from Nat.sub_pos_of_lt hx ), Nat.pow_le_pow_right ( by linarith : 1 ≤ p ) ( show x ≥ 0 from Nat.zero_le x ) ];
      · positivity;
      · rw [ pow_add ];
        nlinarith [ pow_pos hp.pos x, pow_le_pow_right₀ hp.pos.nat_succ_le ( show s - x ≤ s by exact Nat.sub_le _ _ ), pow_pos hp.pos ( s - x ), pow_le_pow_right₀ hp.pos.nat_succ_le ( show x ≤ s by linarith ), pow_pos ( zero_lt_two' ℕ ) α ];
      · ring_nf at *;
        nlinarith [ pow_pos hp.pos x, pow_pos hp.pos ( s - x ), pow_pos ( zero_lt_two' ℕ ) α, pow_le_pow_right₀ ( show 1 ≤ p by linarith ) ( show x ≤ s by linarith ), pow_le_pow_right₀ ( show 1 ≤ p by linarith ) ( show s - x ≥ 1 by exact Nat.sub_pos_of_lt hx ), Nat.sub_add_cancel ( show 1 ≤ p ^ s * 2 ^ α from Nat.mul_pos ( pow_pos hp.pos _ ) ( pow_pos ( zero_lt_two' ℕ ) _ ) ) ]

/-
The number of constructed pairs is $s$.
-/
lemma card_construction_pairs (s p α : ℕ) (hp : 1 < p) :
  (construction_pairs' s p α).card = s := by
    -- Since the function is injective, the cardinality of the image is equal to the cardinality of the domain.
    have h_inj : Function.Injective (fun i => (2 * p^(s - i), 2^(α + 1) * p^i)) := by
      norm_num [ Function.Injective ];
      exact fun a b h₁ h₂ => Nat.pow_right_injective hp h₂;
    convert Finset.card_image_of_injective ( Finset.range s ) h_inj;
    norm_num

/-
The condition that $M+N \equiv 2m \pmod 4$ and $N-M \equiv 2n \pmod 4$.
-/
def satisfies_parity (m n M N : ℕ) : Prop :=
  (M + N) % 4 = (2 * m) % 4 ∧ (N - M) % 4 = (2 * n) % 4

/-
The subset of $T_{m,n}$ satisfying the parity conditions.
-/
noncomputable def T_parity (m n : ℕ) : Finset (ℕ × ℕ) :=
  (T m n).filter (fun ⟨M, N⟩ => satisfies_parity m n M N)

/-
Pairs in `construction_pairs'` satisfy the parity condition.
-/
lemma construction_pairs_satisfies_parity (s p α : ℕ) (hs : 0 < s) (hp : Odd p) (hα : 1 ≤ α) (h_pow : p^s < 2^α) :
  let (m, n) := construction_1_3 s p α
  ∀ M N, (M, N) ∈ construction_pairs' s p α → satisfies_parity m n M N := by
    intros M N hMN
    obtain ⟨i, hi⟩ : ∃ i ∈ Finset.range s, (M, N) = (2 * p^(s - i), 2^(α + 1) * p^i) := by
      unfold construction_pairs' at hMN; aesop;
    norm_num [ satisfies_parity, construction_1_3 ] at *;
    rcases α with ( _ | α ) <;> rcases hp with ⟨ m, rfl ⟩ <;> norm_num [ Nat.pow_succ', ← mul_assoc, Nat.add_mod, Nat.mul_mod ] at *;
    zify ; norm_num [ Int.add_emod, Int.sub_emod, Int.mul_emod, hi.2.1, hi.2.2 ];
    rw [ Nat.cast_sub, Nat.cast_sub ] <;> norm_num [ Int.add_emod, Int.sub_emod, Int.mul_emod ] <;> ring_nf <;> norm_cast <;> norm_num [ Nat.add_mod, Nat.mul_mod, Nat.pow_mod ] ;
    · have := Nat.mod_lt m zero_lt_four; interval_cases m % 4 <;> rcases α with ( _ | _ | α ) <;> norm_num [ pow_succ, mul_assoc, Nat.mul_mod ] at *;
      all_goals rcases Nat.even_or_odd' ( s - i ) with ⟨ k, hk | hk ⟩ <;> norm_num [ pow_add, pow_mul, Nat.mul_mod, Nat.pow_mod, hk ] ;
      all_goals have := Int.emod_nonneg m four_pos.ne'; have := Int.emod_lt_of_pos m four_pos; interval_cases ( m % 4 : ℤ ) <;> norm_num [ Int.negSucc_eq ] ;
      all_goals rcases Nat.even_or_odd' s with ⟨ c, rfl | rfl ⟩ <;> norm_num [ Nat.pow_add, Nat.pow_mul, Nat.mul_mod, Nat.pow_mod ] ;
      all_goals norm_cast; norm_num [ Nat.pow_add, Nat.pow_mul, Nat.mul_mod, Nat.pow_mod ] ;
      all_goals norm_num [ Int.negSucc_eq ] ;
    · nlinarith [ pow_pos ( by linarith : 0 < 1 + m * 2 ) s, pow_pos ( by linarith : 0 < 2 ) α ];
    · rw [ show ( 1 + m * 2 ) = ( 2 * m + 1 ) by ring ];
      nlinarith [ pow_pos ( by linarith : 0 < 2 * m + 1 ) ( s - i ), pow_pos ( by linarith : 0 < 2 * m + 1 ) i, pow_pos ( by linarith : 0 < 2 ) α, pow_le_pow_right₀ ( by linarith : 1 ≤ 2 * m + 1 ) ( show s - i ≤ s by exact Nat.sub_le _ _ ), pow_le_pow_right₀ ( by linarith : 1 ≤ 2 ) ( show α ≥ 0 by linarith ) ]

/-
Pairs in `construction_pairs'` satisfy $M \equiv 2 \pmod 4$ and $N \equiv 0 \pmod 4$.
-/
lemma construction_pairs_mod_4 (s p α : ℕ) (hp : Odd p) (hα : 1 ≤ α) :
  ∀ M N, (M, N) ∈ construction_pairs' s p α → M % 4 = 2 ∧ N % 4 = 0 := by
    -- Let's unfold the definition of `construction_pairs'`.
    unfold construction_pairs';
    simp +zetaDelta at *;
    rintro M N x hx rfl rfl; rcases α with ( _ | α ) <;> rcases p with ( _ | _ | p ) <;> norm_num [ Nat.pow_succ', ← mul_assoc, Nat.mul_mod ] at *;
    rcases Nat.even_or_odd' p with ⟨ k, rfl | rfl ⟩ <;> ring_nf <;> norm_num [ Nat.add_mod, Nat.mul_mod, Nat.pow_mod ] at *;
    · exact absurd hp ( by simp +decide [ parity_simps ] );
    · have := Nat.mod_lt k zero_lt_four; interval_cases k % 4 <;> norm_num [ Nat.pow_mod ] ;
      · exact Nat.recOn ( s - x ) ( by norm_num ) fun n ihn => by norm_num [ Nat.pow_succ', Nat.mul_mod ] at ihn ⊢; have := Nat.mod_lt ( 3 ^ n ) zero_lt_four; interval_cases ( 3 ^ n % 4 ) <;> trivial;
      · rcases Nat.even_or_odd' ( s - x ) with ⟨ c, d | d ⟩ <;> norm_num [ Nat.pow_add, Nat.pow_mul, Nat.mul_mod, Nat.pow_mod, d ]

/-
Conditions on parameters s, p, α for the construction.
-/
def valid_params (s p α : ℕ) : Prop := 0 < s ∧ Odd p ∧ 3 ≤ p ∧ 1 ≤ α ∧ p^s < 2^α

/-
If k(n-k) = r(m-r) with n < m, then n - 2k <= m - 2r.
-/
lemma m_sub_2r_ge_n_sub_2k (m n k r : ℕ) (hmn : n < m) (hk : 2 * k ≤ n) (hr : 2 * r ≤ m) (h_eq : k * (n - k) = r * (m - r)) (hk_pos : 0 < k) :
  n - 2 * k ≤ m - 2 * r := by
    -- By contradiction, assume $n - 2k > m - 2r$.
    by_contra h_contra;
    -- Since $r$ is a positive integer, we can divide both sides of $r*(n - (m - 2r)) < 2k(k - r)$ by $r$ to get $n - (m - 2r) < 2k(k - r)/r$.
    have h_div : n - (m - 2 * r) < 2 * k * (k - r) / r := by
      zify at *;
      repeat rw [ Nat.cast_sub ] at * <;> push_cast at * <;> repeat linarith;
      · nlinarith [ h_eq, hk_pos, h_contra ];
      · nlinarith only [ hk_pos, hmn, hk, hr, h_eq, h_contra ];
      · omega;
    rcases k with ( _ | _ | k ) <;> rcases r with ( _ | _ | r ) <;> norm_num at *;
    · grind;
    · rw [ Nat.lt_iff_add_one_le, Nat.le_div_iff_mul_le ] at h_div <;> norm_num at *;
      grind

/-
The constructed pair satisfies the parity conditions.
-/
lemma to_T_pair_satisfies_parity (m n k r : ℕ) (hmn : n < m) (hk : 2 * k ≤ n) (hr : 2 * r ≤ m) (h_eq : k * (n - k) = r * (m - r)) (hk_pos : 0 < k) :
  let (M, N) := to_T_pair' m n k r
  satisfies_parity m n M N := by
    unfold satisfies_parity to_T_pair'
    generalize_proofs at *; (
    have := m_sub_2r_ge_n_sub_2k m n k r hmn hk hr h_eq hk_pos;
    omega)

/-
For the constructed m, n, 2m = 2 mod 4 and 2n = 2 mod 4.
-/
lemma m_n_mod_4 (s p α : ℕ) (hs : 0 < s) (hp : Odd p) (hα : 1 ≤ α) :
  let (m, n) := construction_1_3 s p α
  (2 * m) % 4 = 2 ∧ (2 * n) % 4 = 2 := by
    unfold construction_1_3; norm_num; ring_nf;
    rcases α with ( _ | _ | α ) <;> norm_num [ Nat.pow_succ', ← mul_assoc, Nat.add_mod, Nat.mul_mod ] at *;
    · rw [ ← Nat.mod_add_div ( p ^ s ) 4 ] ; have := Nat.mod_lt ( p ^ s ) zero_lt_four; interval_cases _ : p ^ s % 4 <;> norm_num [ Nat.add_mod, Nat.mul_mod ] ;
      · exact absurd ( congr_arg ( · % 2 ) ‹p ^ s % 4 = 0› ) ( by norm_num [ Nat.pow_mod, Nat.odd_iff.mp hp ] );
      · grind;
      · grind;
      · grind;
    · zify;
      rw [ Int.ofNat_sub ( by nlinarith [ pow_pos ( show 0 < p by contrapose! hp; aesop ) s, pow_pos ( show 0 < 2 by decide ) α ] ) ] ; norm_num [ Int.add_emod, Int.sub_emod, Int.mul_emod ]

/-
If a pair satisfies the parity conditions and is in T, it yields a valid solution.
-/
lemma solution_from_parity (m n M N : ℕ) (hmn : n < m) (hT : (M, N) ∈ T m n) (h_parity : satisfies_parity m n M N) :
  let (k, r) := from_T_pair m n M N
  k * (n - k) = r * (m - r) ∧ 2 * k ≤ n ∧ 2 * r ≤ m ∧ 0 < k ∧ 0 < r := by
    field_simp;
    -- By definition of `from_T_pair`, we have `2 * k = n - (N - M) / 2` and `2 * r = m - (M + N) / 2`.
    obtain ⟨hk, hr⟩ : 2 * (from_T_pair m n M N).1 = n - (N - M) / 2 ∧ 2 * (from_T_pair m n M N).2 = m - (M + N) / 2 := by
      unfold satisfies_parity at h_parity;
      unfold from_T_pair;
      grind;
    have h_eq : 4 * (from_T_pair m n M N).1 * (n - (from_T_pair m n M N).1) = 4 * (from_T_pair m n M N).2 * (m - (from_T_pair m n M N).2) := by
      have h_eq : 4 * (from_T_pair m n M N).1 * (n - (from_T_pair m n M N).1) = (n - (N - M) / 2) * (n + (N - M) / 2) ∧ 4 * (from_T_pair m n M N).2 * (m - (from_T_pair m n M N).2) = (m - (M + N) / 2) * (m + (M + N) / 2) := by
        constructor <;> rw [ Nat.mul_sub_left_distrib ] <;> ring_nf;
        · exact Nat.sub_eq_of_eq_add <| by nlinarith only [ Nat.sub_add_cancel <| show ( N - M ) / 2 ≤ n from by { exact Nat.div_le_of_le_mul <| by { have := Finset.mem_filter.mp hT; norm_num at *; omega } }, hk ] ;
        · exact Nat.sub_eq_of_eq_add <| by nlinarith only [ hr, Nat.sub_add_cancel <| show ( M + N ) / 2 ≤ m from Nat.div_le_of_le_mul <| by linarith [ Finset.mem_filter.mp hT |>.2.1 ] ] ;
      have h_eq : (n - (N - M) / 2) * (n + (N - M) / 2) = n^2 - (N - M)^2 / 4 ∧ (m - (M + N) / 2) * (m + (M + N) / 2) = m^2 - (M + N)^2 / 4 := by
        constructor <;> rw [ Nat.mul_comm ];
        · rw [ ← Nat.sq_sub_sq ];
          rw [ Nat.div_pow ];
          unfold satisfies_parity at h_parity; omega;
        · rw [ ← Nat.sq_sub_sq ] ; ring_nf;
          rw [ show M * N * 2 + M ^ 2 + N ^ 2 = ( M + N ) ^ 2 by ring ] ; rw [ Nat.div_pow ] ; norm_num;
          exact Nat.dvd_of_mod_eq_zero ( by rw [ Nat.mod_eq_zero_of_dvd ] ; exact Nat.dvd_of_mod_eq_zero ( by have := h_parity.1; omega ) );
      have h_eq : 4 * n^2 - (N - M)^2 = 4 * m^2 - (M + N)^2 := by
        have h_eq : M * N = m^2 - n^2 := by
          unfold T at hT; aesop;
        rw [ eq_tsub_iff_add_eq_of_le ] at h_eq;
        · rw [ Nat.sub_eq_of_eq_add ] ; ring_nf;
          rw [ tsub_add_eq_add_tsub ];
          · exact eq_tsub_of_add_eq ( by nlinarith only [ Nat.sub_add_cancel ( show M ≤ N from by { have := hT; exact Finset.mem_filter.mp this |>.2.2.2.1 } ), h_eq ] );
          · nlinarith only [ hmn, h_eq, show M + N < 2 * m from by { have := Finset.mem_filter.mp hT; aesop } ];
        · gcongr;
      grind;
    refine' ⟨ by linarith, _, _, _, _ ⟩;
    · exact hk.le.trans ( Nat.sub_le _ _ );
    · exact hr.le.trans ( Nat.sub_le _ _ );
    · unfold T at hT ; norm_num at hT ; omega;
    · have h_pos : M + N < 2 * m := by
        exact Finset.mem_filter.mp hT |>.2.1;
      omega

/-
The constructed pairs yield valid solutions.
-/
lemma construction_pairs_yield_solutions (s p α : ℕ) (hs : 0 < s) (hp : Odd p) (hp_ge_3 : 3 ≤ p) (hα : 1 ≤ α) (h_pow : p^s < 2^α) :
  let (m, n) := construction_1_3 s p α
  ∀ M N, (M, N) ∈ construction_pairs' s p α →
  let (k, r) := from_T_pair m n M N
  k * (n - k) = r * (m - r) ∧ 2 * k ≤ n ∧ 2 * r ≤ m ∧ 0 < k ∧ 0 < r := by
    intro M N hMN
    apply solution_from_parity;
    · exact Nat.sub_lt ( Nat.succ_pos _ ) ( by norm_num );
    · exact construction_pairs_in_T s p α hp hp_ge_3 h_pow hMN;
    · apply construction_pairs_satisfies_parity s p α hs hp hα h_pow M N hMN

/-
The function to_T_pair' is the inverse of from_T_pair for valid inputs.
-/
lemma from_T_pair_inverse (m n M N : ℕ) (hmn : n < m) (hT : (M, N) ∈ T m n) (h_parity : satisfies_parity m n M N) :
  let (k, r) := from_T_pair m n M N
  to_T_pair' m n k r = (M, N) := by
    have := solution_from_parity m n M N hmn hT h_parity;
    unfold to_T_pair';
    have h_sub : let (k, r) := from_T_pair m n M N; M + N = 2 * m - 4 * r ∧ N - M = 2 * n - 4 * k := by
      unfold from_T_pair at *;
      unfold satisfies_parity at h_parity; omega;
    have h_sub : let (k, r) := from_T_pair m n M N; m - 2 * r = (M + N) / 2 ∧ n - 2 * k = (N - M) / 2 := by
      grind;
    have h_sub : let (k, r) := from_T_pair m n M N; (M + N) / 2 - (N - M) / 2 = M ∧ (M + N) / 2 + (N - M) / 2 = N := by
      constructor <;> rw [ Nat.sub_eq_of_eq_add ];
      any_goals rw [ Nat.sub_add_cancel ( show M ≤ N from by { exact Finset.mem_filter.mp hT |>.2.2.2.1 } ) ];
      · rw [ show M + N = M + ( N - M ) + M by linarith [ Nat.sub_add_cancel ( show M ≤ N from by
                                                                                exact Finset.mem_filter.mp hT |>.2.2.2.1 ) ] ] ; omega;
      · linarith [ Nat.sub_add_cancel ( show M ≤ N from by { exact Finset.mem_filter.mp hT |>.2.2.2.1 } ), Nat.div_mul_cancel ( show 2 ∣ M + N from Nat.dvd_of_mod_eq_zero ( by { unfold satisfies_parity at h_parity; omega } ) ), Nat.div_mul_cancel ( show 2 ∣ N - M from Nat.dvd_of_mod_eq_zero ( by { unfold satisfies_parity at h_parity; omega } ) ) ];
    aesop

/-
For the constructed parameters, if a pair satisfies parity, then M is 2 mod 4.
-/
lemma parity_implies_M_mod_4 (s p α : ℕ) (hs : 0 < s) (hp : Odd p) (hp_ge_3 : 3 ≤ p) (hα : 1 ≤ α) (h_pow : p^s < 2^α) :
  let (m, n) := construction_1_3 s p α
  ∀ M N, (M, N) ∈ T_parity m n → M % 4 = 2 := by
    intro M N hMN
    obtain ⟨hMN_T, h_parity⟩ := Finset.mem_filter.mp hMN
    have hMN_eq : M * N = 2^(α + 2) * p^s := by
      have hMN_eq : M * N = (construction_1_3 s p α).1 ^ 2 - (construction_1_3 s p α).2 ^ 2 := by
        unfold T at hMN_T; aesop;
      convert hMN_eq using 1 ; ring_nf!;
      exact eq_tsub_of_add_eq ( by rw [ show construction_1_3 s p α = ( 2 ^ α * p ^ s + 1, 2 ^ α * p ^ s - 1 ) by rfl ] ; nlinarith only [ Nat.sub_add_cancel ( show 1 ≤ 2 ^ α * p ^ s from Nat.mul_pos ( pow_pos ( by decide ) _ ) ( pow_pos ( by linarith ) _ ) ) ] )
    have hMN_mod : (M + N) % 4 = 2 ∧ (N - M) % 4 = 2 := by
      have hMN_mod : (2 * (construction_1_3 s p α).1) % 4 = 2 ∧ (2 * (construction_1_3 s p α).2) % 4 = 2 := by
        exact m_n_mod_4 s p α hs hp hα;
      exact ⟨ h_parity.1.trans hMN_mod.1, h_parity.2.trans hMN_mod.2 ⟩
    have hN_mod : N % 4 = 0 := by
      cases le_total M N <;> simp_all +decide [ Nat.add_mod ];
      -- If $N \equiv 2 \pmod{4}$, then $N = 4k + 2$ for some integer $k$.
      by_contra hN_mod_contra
      obtain ⟨k, hk⟩ : ∃ k, N = 4 * k + 2 := by
        exact ⟨ N / 4, by omega ⟩;
      -- Since $M$ is even, we can write $M = 2m$ for some integer $m$.
      obtain ⟨m, hm⟩ : ∃ m, M = 2 * m := by
        rcases Nat.even_or_odd' M with ⟨ m, rfl | rfl ⟩ <;> simp_all +arith +decide [ Nat.add_mod, Nat.mul_mod ];
        omega;
      -- Since $M$ is even, we can write $M = 2m$ for some integer $m$. Then $MN = 2m(4k + 2) = 8mk + 4m$.
      have hMN_factor : m * (2 * k + 1) = 2^α * p^s := by
        subst_vars; ring_nf at *; linarith;
      -- Since $2k + 1$ is odd and divides $2^\alpha p^s$, it must divide $p^s$.
      have h_div_ps : 2 * k + 1 ∣ p^s := by
        exact ( Nat.Coprime.dvd_of_dvd_mul_left ( show Nat.Coprime ( 2 * k + 1 ) ( 2 ^ α ) from Nat.Coprime.pow_right _ <| by norm_num ) <| hMN_factor ▸ dvd_mul_left _ _ );
      nlinarith only [ hMN_factor, h_div_ps, h_pow, hMN_mod, hMN_T, h_parity, hm, hk, ‹M ≤ N›, Nat.le_of_dvd ( pow_pos ( by linarith ) _ ) h_div_ps ]
    have hM_mod : M % 4 = 2 := by
      omega
    exact hM_mod

/-
If a pair is in T_parity, then M is of the form 2 * p^y.
-/
lemma M_form_in_T_parity (s p α : ℕ) (hs : 0 < s) (hp : p.Prime) (hp_odd : p ≠ 2) (hα : 1 ≤ α) (h_pow : p^s < 2^α) :
  let (m, n) := construction_1_3 s p α
  ∀ M N, (M, N) ∈ T_parity m n → ∃ y, y ≤ s ∧ M = 2 * p^y := by
    have h_parity_implies_M_mod_4 : ∀ M N, (M, N) ∈ T_parity (2^α * p^s + 1) (2^α * p^s - 1) → M % 4 = 2 := by
      apply parity_implies_M_mod_4;
      · exact hs;
      · exact hp.odd_of_ne_two hp_odd;
      · exact lt_of_le_of_ne hp.two_le ( Ne.symm hp_odd );
      · grind;
      · linarith;
    intro M N hMN
    have hM_div : M ∣ 2^(α + 2) * p^s := by
      have hMN_eq : M * N = (2^α * p^s + 1)^2 - (2^α * p^s - 1)^2 := by
        unfold T_parity at hMN;
        unfold T at hMN; aesop;
      convert hMN_eq ▸ dvd_mul_right _ _ using 1 ; rw [ Nat.sq_sub_sq ] ; ring_nf; zify ; ring_nf;
      repeat rw [ Nat.cast_sub ] <;> push_cast <;> repeat nlinarith [ pow_pos hp.pos s, pow_pos ( zero_lt_two' ℕ ) α ] ; ;
      grind;
    -- Since $M$ is 2 mod 4, we can write $M = 2 * k$ where $k$ is odd.
    obtain ⟨k, hk⟩ : ∃ k, M = 2 * k ∧ Odd k := by
      have := h_parity_implies_M_mod_4 M N hMN; use M / 2; exact ⟨by linarith [Nat.mod_add_div M 2, show M % 2 = 0 from by omega], by exact Nat.odd_iff.mpr (by omega)⟩;
    -- Since $k$ is odd and divides $2^{\alpha+1} p^s$, it must divide $p^s$.
    have hk_div_ps : k ∣ p^s := by
      have hk_div_ps : k ∣ 2^(α + 1) * p^s := by
        exact Exists.elim hM_div fun x hx => ⟨ x, by rw [ hk.1 ] at hx; ring_nf at hx ⊢; linarith ⟩;
      exact ( Nat.Coprime.dvd_of_dvd_mul_left ( show Nat.Coprime k ( 2 ^ ( α + 1 ) ) from Nat.Coprime.pow_right _ <| by obtain ⟨ m, rfl ⟩ := hk.2; norm_num ) hk_div_ps );
    rw [ Nat.dvd_prime_pow hp ] at hk_div_ps ; aesop

/-
If M is of the form 2 * p^y, then N is determined.
-/
lemma N_form_in_T_parity (s p α : ℕ) (hp : p.Prime) (hp_odd : p ≠ 2) (h_pow : p^s < 2^α) :
  let (m, n) := construction_1_3 s p α
  ∀ M N, (M, N) ∈ T_parity m n → ∀ y, M = 2 * p^y → N = 2^(α + 1) * p^(s - y) := by
    intro M N hT y hy;
    have hMN : M * N = 2^(α + 2) * p^s := by
      have hMN : M * N = (2 ^ α * p ^ s + 1) ^ 2 - (2 ^ α * p ^ s - 1) ^ 2 := by
        unfold T_parity at hT;
        unfold T at hT; aesop;
      rw [ hMN, Nat.sub_eq_of_eq_add ] ; zify ; cases h : 2 ^ α * p ^ s <;> norm_num [ h ] ; ring_nf;
      · aesop;
      · push_cast [ pow_add, pow_mul' ] ; nlinarith only [ h ]
    have hy_le_s : y ≤ s := by
      have hy_le_s : p^y ∣ p^s := by
        have h_div : p^y ∣ 2^(α + 1) * p^s := by
          exact ⟨ N, by rw [ hy ] at hMN; ring_nf at *; linarith ⟩;
        exact ( Nat.Coprime.dvd_of_dvd_mul_left ( show Nat.Coprime ( p ^ y ) ( 2 ^ ( α + 1 ) ) from Nat.Coprime.pow _ _ <| hp.coprime_iff_not_dvd.mpr fun h => hp_odd <| by have := Nat.le_of_dvd ( by positivity ) h; interval_cases p <;> trivial ) h_div );
      rw [ pow_dvd_pow_iff ] at hy_le_s <;> aesop
    have hN : N = 2^(α + 1) * p^(s - y) := by
      simp_all +decide [ pow_add, mul_comm ];
      exact mul_left_cancel₀ ( show p ^ y * 2 ≠ 0 by exact mul_ne_zero ( pow_ne_zero _ hp.ne_zero ) two_ne_zero ) <| by rw [ show p ^ s = p ^ ( s - y ) * p ^ y by rw [ ← pow_add, Nat.sub_add_cancel hy_le_s ] ] at hMN; linarith;
    exact hN

/-
The constructed pairs are a subset of T_parity.
-/
lemma construction_pairs_subset_T_parity (s p α : ℕ) (hs : 0 < s) (hp : Odd p) (hp_ge_3 : 3 ≤ p) (hα : 1 ≤ α) (h_pow : p^s < 2^α) :
  let (m, n) := construction_1_3 s p α
  construction_pairs' s p α ⊆ T_parity m n := by
    have h_P_subset_C : (construction_pairs' s p α : Finset (ℕ × ℕ)) ⊆ T_parity (2^α * p^s + 1) (2^α * p^s - 1) := by
      intro x hx
      have h_conditions : x ∈ T (2^α * p^s + 1) (2^α * p^s - 1) ∧ satisfies_parity (2^α * p^s + 1) (2^α * p^s - 1) x.1 x.2 := by
        apply And.intro;
        · apply construction_pairs_in_T s p α hp hp_ge_3 h_pow;
          assumption;
        · apply construction_pairs_satisfies_parity s p α hs hp hα h_pow x.1 x.2 hx
      exact Finset.mem_filter.mpr ⟨ h_conditions.1, h_conditions.2 ⟩;
    exact h_P_subset_C

/-
T_parity is a subset of construction_pairs'.
-/
lemma T_parity_subset_construction_pairs (s p α : ℕ) (hs : 0 < s) (hp : p.Prime) (hp_odd : p ≠ 2) (hα : 1 ≤ α) (h_pow : p^s < 2^α) :
  let (m, n) := construction_1_3 s p α
  T_parity m n ⊆ construction_pairs' s p α := by
    field_simp;
    intro x hx;
    -- By `M_form_in_T_parity`, $M = 2 p^y$ for some $y \le s$.
    obtain ⟨y, hy₁, hy₂⟩ : ∃ y, y ≤ s ∧ x.1 = 2 * p^y := by
      apply M_form_in_T_parity s p α hs hp hp_odd hα h_pow x.1 x.2 hx;
    -- By `N_form_in_T_parity`, $N = 2^{\alpha+1} p^{s-y}$.
    have hy₃ : x.2 = 2^(α + 1) * p^(s - y) := by
      apply N_form_in_T_parity s p α hp hp_odd h_pow;
      exact hx;
      exact hy₂;
    -- Let $i = s - y$. Then $0 \le i \le s$.
    set i := s - y
    have hi : i ≤ s := by
      exact Nat.sub_le _ _
    have hi_pos : i < s := by
      refine' lt_of_le_of_ne hi _;
      intro H; simp_all +decide [ T_parity ] ;
      unfold T at hx; simp_all +decide [ Finset.mem_filter ] ;
      unfold construction_1_3 at *; simp_all +decide [ Nat.pow_succ', Nat.mul_assoc ] ;
      linarith [ pow_pos hp.pos y ];
    simp_all +decide [ construction_pairs' ];
    exact ⟨ i, hi_pos, Prod.ext ( by rw [ Nat.sub_sub_self hy₁ ] ; aesop ) ( by aesop ) ⟩

/-
The set of construction pairs is exactly the set of T pairs satisfying parity (assuming p is prime).
-/
lemma construction_pairs_eq_T_parity (s p α : ℕ) (hs : 0 < s) (hp : p.Prime) (hp_ge_3 : 3 ≤ p) (hα : 1 ≤ α) (h_pow : p^s < 2^α) :
  let (m, n) := construction_1_3 s p α
  construction_pairs' s p α = T_parity m n := by
    apply Finset.Subset.antisymm;
    · convert construction_pairs_subset_T_parity s p α hs _ _ _ _ using 1
      all_goals generalize_proofs at *;
      · exact hp.odd_of_ne_two <| by linarith;
      · exact hp_ge_3;
      · linarith;
      · exact h_pow;
    · convert T_parity_subset_construction_pairs s p α hs hp ( by linarith ) hα h_pow using 1

/-
The map from T_parity lands in the intersection of A_n and A_m.
-/
def T_parity_map (m n : ℕ) (p : ℕ × ℕ) : ℕ :=
  let (k, _) := from_T_pair m n p.1 p.2
  k * (n - k)

lemma T_parity_map_mem_intersection (m n : ℕ) (hmn : n < m) (p : ℕ × ℕ) (hp : p ∈ T_parity m n) :
  T_parity_map m n p ∈ A n ∩ A m := by
    -- By definition of $T_parity$, we know that $p \in T_parity m n$ implies $p \in T m n$ and $p$ satisfies the parity conditions.
    obtain ⟨hp_T, hp_parity⟩ : p ∈ T m n ∧ satisfies_parity m n p.1 p.2 := by
      exact Finset.mem_filter.mp hp;
    -- By definition of $T_parity$, we know that $p \in T_parity m n$ implies $k$ and $r$ are valid integers and satisfy the conditions to be in $A_n$ and $A_m$.
    obtain ⟨hk, hr, h_eq, hk_pos, hr_pos⟩ := (solution_from_parity m n p.1 p.2 hmn hp_T hp_parity);
    simp +zetaDelta at *;
    -- By definition of $T_parity_map$, we know that $T_parity_map m n p = k * (n - k)$ and $T_parity_map m n p = r * (m - r)$.
    have hT_parity_map : T_parity_map m n p = ((n - (p.2 - p.1) / 2) / 2) * (n - ((n - (p.2 - p.1) / 2) / 2)) ∧ T_parity_map m n p = ((m - (p.1 + p.2) / 2) / 2) * (m - ((m - (p.1 + p.2) / 2) / 2)) := by
      exact ⟨ rfl, hk ▸ rfl ⟩;
    exact ⟨ hT_parity_map.1.symm ▸ Finset.mem_image.mpr ⟨ ( n - ( p.2 - p.1 ) / 2 ) / 2, Finset.mem_Ioo.mpr ⟨ by omega, by omega ⟩, rfl ⟩, hT_parity_map.2.symm ▸ Finset.mem_image.mpr ⟨ ( m - ( p.1 + p.2 ) / 2 ) / 2, Finset.mem_Ioo.mpr ⟨ by omega, by omega ⟩, rfl ⟩ ⟩

/-
The function k(n-k) is injective for 2k <= n.
-/
lemma k_inj_on_le_half (n k1 k2 : ℕ) (h1 : 2 * k1 ≤ n) (h2 : 2 * k2 ≤ n) (h_eq : k1 * (n - k1) = k2 * (n - k2)) :
  k1 = k2 := by
    cases le_total k1 k2 <;> nlinarith [ tsub_add_cancel_of_le ( by linarith : k1 ≤ n ), tsub_add_cancel_of_le ( by linarith : k2 ≤ n ) ]

/-
The function from_T_pair is the left inverse of to_T_pair'.
-/
lemma to_T_pair_inverse_left (m n k r : ℕ) (hmn : n < m) (hk : 2 * k ≤ n) (hr : 2 * r ≤ m) (h_eq : k * (n - k) = r * (m - r)) (hk_pos : 0 < k) :
  from_T_pair m n (to_T_pair' m n k r).1 (to_T_pair' m n k r).2 = (k, r) := by
    unfold from_T_pair to_T_pair';
    simp +zetaDelta at *;
    constructor <;> rw [ Nat.sub_eq_of_eq_add ];
    rw [ Nat.mul_div_cancel_left _ ( by decide ) ];
    rw [ tsub_tsub_assoc ];
    grind;
    any_goals exact 2 * r;
    · exact Nat.le_add_right _ _;
    · exact m_sub_2r_ge_n_sub_2k m n k r hmn hk hr h_eq hk_pos;
    · norm_num;
    · rw [ Nat.div_eq_of_eq_mul_left zero_lt_two ];
      rw [ Nat.add_sub_cancel' hr ];
      rw [ tsub_add_eq_add_tsub ];
      · exact Nat.sub_eq_of_eq_add <| by ring;
      · exact m_sub_2r_ge_n_sub_2k m n k r hmn hk hr h_eq hk_pos

/-
The set of valid solution pairs (k, r).
-/
def Solutions (m n : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.product (Finset.range (n + 1)) (Finset.range (m + 1))).filter
    (fun ⟨k, r⟩ => 2 * k ≤ n ∧ 2 * r ≤ m ∧ k * (n - k) = r * (m - r) ∧ 0 < k ∧ 0 < r)

/-
The map from the intersection to T_parity (as a function on elements).
-/
noncomputable def intersection_to_T_parity_map (m n : ℕ) (x : ℕ) (hx : x ∈ A n ∩ A m) : ℕ × ℕ :=
  let k := get_k n x (Finset.mem_of_mem_inter_left hx)
  let r := get_r m x (Finset.mem_of_mem_inter_right hx)
  to_T_pair' m n k r

/-
The map from intersection lands in T_parity.
-/
lemma intersection_to_T_parity_map_mem (m n : ℕ) (hmn : n < m) (x : ℕ) (hx : x ∈ A n ∩ A m) :
  intersection_to_T_parity_map m n x hx ∈ T_parity m n := by
    apply Classical.byContradiction
    intro h_contra;
    -- By definition of `intersection_to_T_parity_map`, we have `x = k * (n - k)` and `x = r * (m - r)` for some `k` and `r`.
    obtain ⟨k, hk⟩ : ∃ k, 2 * k ≤ n ∧ k * (n - k) = x ∧ x ∈ A n := by
      exact ⟨ _, unique_k_for_val n x ( Finset.mem_of_mem_inter_left hx ) |> ExistsUnique.exists |> Classical.choose_spec |> And.left, unique_k_for_val n x ( Finset.mem_of_mem_inter_left hx ) |> ExistsUnique.exists |> Classical.choose_spec |> And.right, Finset.mem_of_mem_inter_left hx ⟩
    obtain ⟨r, hr⟩ : ∃ r, 2 * r ≤ m ∧ r * (m - r) = x ∧ x ∈ A m := by
      exact Classical.not_not.1 fun h => h ( unique_k_for_val m x ( Finset.mem_of_mem_inter_right hx ) |> fun h' => ⟨ h'.exists.choose, h'.exists.choose_spec.1, h'.exists.choose_spec.2, Finset.mem_of_mem_inter_right hx ⟩ );
    -- By definition of `intersection_to_T_parity_map`, we have `intersection_to_T_parity_map m n hmn x hx = to_T_pair' m n k r`.
    have h_map_eq : intersection_to_T_parity_map m n x hx = to_T_pair' m n k r := by
      have h_map_eq : get_k n x (Finset.mem_of_mem_inter_left hx) = k ∧ get_r m x (Finset.mem_of_mem_inter_right hx) = r := by
        have h_unique : ∀ k', 2 * k' ≤ n ∧ k' * (n - k') = x → k' = get_k n x (Finset.mem_of_mem_inter_left hx) := by
          exact fun k' hk' => Classical.choose_spec ( unique_k_for_val n x hk.2.2 ) |>.2 k' hk' |> fun h => h.symm ▸ rfl;
        have h_unique_r : ∀ r', 2 * r' ≤ m ∧ r' * (m - r') = x → r' = get_r m x (Finset.mem_of_mem_inter_right hx) := by
          exact Classical.choose_spec ( unique_k_for_val m x hr.2.2 ) |>.2;
        exact ⟨ h_unique k ⟨ hk.1, hk.2.1 ⟩ ▸ rfl, h_unique_r r ⟨ hr.1, hr.2.1 ⟩ ▸ rfl ⟩;
      unfold intersection_to_T_parity_map; aesop;
    have h_map_mem : to_T_pair' m n k r ∈ T m n ∧ satisfies_parity m n (to_T_pair' m n k r).1 (to_T_pair' m n k r).2 := by
      apply And.intro;
      · apply to_T_pair_mem_T' m n k r hmn hk.1 hr.1 (by linarith) (by
        rcases k with ( _ | k ) <;> rcases r with ( _ | r ) <;> norm_num at *;
        · norm_num [ hk.1.symm, hr.1.symm, A ] at hx;
          omega;
        · grind);
      · apply to_T_pair_satisfies_parity m n k r hmn hk.left hr.left (by linarith) (by
        rcases k with ( _ | k ) <;> rcases r with ( _ | r ) <;> norm_num at *;
        · norm_num [ hk.1.symm, hr.1.symm, A ] at hx;
          omega;
        · grind);
    exact h_contra <| h_map_eq ▸ Finset.mem_filter.mpr ⟨ h_map_mem.1, h_map_mem.2 ⟩

/-
The function from the intersection to T_parity (as a map between subtypes).
-/
noncomputable def intersection_to_T_parity (m n : ℕ) (hmn : n < m) (x : ↥(A n ∩ A m)) : ↥(T_parity m n) :=
  ⟨intersection_to_T_parity_map m n x.1 x.2, intersection_to_T_parity_map_mem m n hmn x.1 x.2⟩

/-
The function from T_parity to the intersection (as a map between subtypes).
-/
noncomputable def T_parity_to_intersection (m n : ℕ) (hmn : n < m) (p : ↥(T_parity m n)) : ↥(A n ∩ A m) :=
  ⟨T_parity_map m n p.1, T_parity_map_mem_intersection m n hmn p.1 p.2⟩

/-
The function $f(x) = x^2/(x+K)$ is increasing for $x>0, K \ge 0$.
Hence if $S \ge mR$, then $S^2/(S+K) \ge (mR)^2/(mR+K) = mR^2/(R+K/m)$.
-/
lemma algebraic_helper (S K : ℝ) (hS : 0 < S) (hK : 0 ≤ K) (m R : ℝ) (hm : 0 < m) (hR : 0 < R) (h_sum : m * R ≤ S) :
  m * R^2 / (R + K / m) ≤ S^2 / (S + K) := by
    field_simp;
    nlinarith [ mul_le_mul_of_nonneg_left h_sum ( show 0 ≤ S * m by positivity ), mul_le_mul_of_nonneg_left h_sum ( show 0 ≤ S by positivity ), mul_le_mul_of_nonneg_left h_sum ( show 0 ≤ K by positivity ), mul_le_mul_of_nonneg_left h_sum ( show 0 ≤ m * R by positivity ), mul_le_mul_of_nonneg_left h_sum ( show 0 ≤ m by positivity ), mul_le_mul_of_nonneg_left h_sum ( show 0 ≤ R by positivity ) ]

/-
The sum of degrees of vertices in a hypergraph is equal to the sum of the cardinalities of the edges.
-/
def degree {α : Type*} [DecidableEq α] (E : Finset (Finset α)) (v : α) : ℕ :=
  (E.filter (v ∈ ·)).card

lemma sum_degrees_eq_sum_card {α : Type*} [DecidableEq α] (E : Finset (Finset α)) :
  ∑ v ∈ E.biUnion id, degree E v = ∑ e ∈ E, e.card := by
    simp +decide only [degree, Finset.card_eq_sum_ones];
    rw [ Finset.sum_sigma' ];
    rw [ Finset.sum_sigma' ];
    refine' Finset.sum_bij ( fun x _ => ⟨ x.2, x.1 ⟩ ) _ _ _ _ <;> aesop

/-
The sum of squared degrees is the sum of intersection sizes of all pairs of edges.
-/
lemma sum_sq_degrees_eq {α : Type*} [DecidableEq α] (E : Finset (Finset α)) :
  ∑ v ∈ E.biUnion id, (degree E v)^2 = ∑ e1 ∈ E, ∑ e2 ∈ E, (e1 ∩ e2).card := by
    -- By Fubini's theorem, we can interchange the order of summation.
    have h_fubini : ∑ e1 ∈ E, ∑ e2 ∈ E, (e1 ∩ e2).card = ∑ v ∈ E.biUnion id, ∑ e1 ∈ E, ∑ e2 ∈ E, (if v ∈ e1 ∧ v ∈ e2 then 1 else 0) := by
      rw [ Finset.sum_comm, Finset.sum_congr rfl ];
      rw [ Finset.sum_comm ];
      intro e he
      have h_card : ∀ x_1 ∈ E, (x_1 ∩ e).card = ∑ y ∈ E.biUnion id, if y ∈ x_1 ∧ y ∈ e then 1 else 0 := by
        simp +contextual
        intro x hx; congr 1 with y ; aesop;
      rw [ Finset.sum_congr rfl h_card, Finset.sum_comm ];
      simp +decide only [and_comm];
    simp_all +decide
    refine' Finset.sum_congr rfl fun v hv => _;
    simp +decide only [degree];
    simp +decide only [Finset.card_filter, pow_two];
    rw [ Finset.sum_mul _ _ _ ] ; exact Finset.sum_congr rfl fun _ _ => by split_ifs <;> simp +decide [ * ] ;

/-
The sum of intersection sizes of all pairs of edges is bounded by the sum of edge sizes plus $m(m-1)k$.
-/
lemma intersection_sum_bound {α : Type*} [DecidableEq α] (E : Finset (Finset α)) (m k : ℕ)
  (hm : E.card = m)
  (hk : ∀ e1 ∈ E, ∀ e2 ∈ E, e1 ≠ e2 → (e1 ∩ e2).card ≤ k) :
  ∑ e1 ∈ E, ∑ e2 ∈ E, (e1 ∩ e2).card ≤ (∑ e ∈ E, e.card) + m * (m - 1) * k := by
    -- Apply the bound on the inner sum to each term in the outer sum.
    have h_inner_bound : ∀ e1 ∈ E, ∑ e2 ∈ E, (e1 ∩ e2).card ≤ e1.card + (m - 1) * k := by
      intro e1 he1
      have h_inner_bound : ∑ e2 ∈ E \ {e1}, (e1 ∩ e2).card ≤ (m - 1) * k := by
        exact le_trans ( Finset.sum_le_sum fun x hx => hk e1 he1 x ( Finset.mem_sdiff.mp hx |>.1 ) ( by aesop ) ) ( by simp [ Finset.card_sdiff, * ] );
      rw [ Finset.sum_eq_add_sum_diff_singleton he1 ];
      grind
    generalize_proofs at *;
    convert Finset.sum_le_sum h_inner_bound using 1 ; simp +decide [ mul_comm, mul_left_comm, Finset.sum_add_distrib, hm ]

/-
Let $\mathcal{H}=(V,E)$ be a hypergraph with $m$ many edges and assume that the cardinality of each edge is at least $R$. Assume that for every distinct edges $e,e'\in E$ $|e\cap e'|\leq k$. Then,  $|V|\geq \frac{mR^2}{R+(m-1)k}$.
-/
lemma hypergraph_bound {α : Type*} [DecidableEq α] (E : Finset (Finset α)) (m R k : ℕ) :
  E.card = m →
  (∀ e ∈ E, R ≤ e.card) →
  (∀ e1 ∈ E, ∀ e2 ∈ E, e1 ≠ e2 → (e1 ∩ e2).card ≤ k) →
  (E.biUnion id).card * (R + (m - 1) * k) ≥ m * R^2 := by
    -- By Cauchy-Schwarz, $(\sum d(v))^2 \le |V| \sum d(v)^2$.
    have h_cauchy_schwarz : (∑ v ∈ E.biUnion id, degree E v)^2 ≤ (E.biUnion id).card * ∑ v ∈ E.biUnion id, (degree E v)^2 := by
      have h_cauchy_schwarz : ∀ (u v : α → ℝ), (∑ x ∈ E.biUnion id, u x * v x) ^ 2 ≤ (∑ x ∈ E.biUnion id, u x ^ 2) * (∑ x ∈ E.biUnion id, v x ^ 2) := by
        exact fun u v => Finset.sum_mul_sq_le_sq_mul_sq (E.biUnion id) u v;
      convert h_cauchy_schwarz ( fun _ => 1 ) ( fun x => ( degree E x : ℝ ) ) using 1 ; simp +decide;
      norm_cast;
    -- Using `algebraic_helper`, $\frac{S^2}{S+K} \ge \frac{m R^2}{R + K/m} = \frac{m R^2}{R + (m-1)k}$.
    intros hm hR hk
    have h_algebraic_helper : (m * R)^2 / (m * R + m * (m - 1) * k : ℝ) ≥ m * R^2 / (R + (m - 1) * k : ℝ) := by
      by_cases hm : m = 0 <;> by_cases hR : R = 0 <;> simp_all +decide [ sq, mul_assoc ];
      rw [ div_le_div_iff₀ ] <;> nlinarith only [ show ( 0 : ℝ ) < m by positivity, show ( 0 : ℝ ) < R by positivity, show ( 0 : ℝ ) ≤ ( m - 1 ) * k by exact mul_nonneg ( sub_nonneg.mpr ( Nat.one_le_cast.mpr ( Nat.pos_of_ne_zero hm ) ) ) ( Nat.cast_nonneg k ) ] ;
    by_cases h : m = 0 <;> by_cases h' : R = 0 <;> simp_all +decide [ mul_pow ];
    have h_subst : (m * R : ℝ)^2 / (m * R + m * (m - 1) * k) ≤ (E.biUnion id).card := by
      have h_subst : (m * R : ℝ)^2 / (m * R + m * (m - 1) * k) ≤ (∑ v ∈ E.biUnion id, degree E v)^2 / ((∑ v ∈ E.biUnion id, degree E v) + m * (m - 1) * k) := by
        have h_sum_ge : (∑ v ∈ E.biUnion id, degree E v : ℝ) ≥ m * R := by
          have h_sum_ge : (∑ v ∈ E.biUnion id, degree E v : ℝ) = ∑ e ∈ E, e.card := by
            exact mod_cast sum_degrees_eq_sum_card E;
          exact h_sum_ge.symm ▸ mod_cast hm.symm ▸ le_trans ( by simp +decide [ mul_comm ] ) ( Finset.sum_le_sum hR );
        by_cases hk : k = 0 <;> simp_all +decide
        · rw [ sq, mul_div_cancel_left₀ _ ( by positivity ), sq, mul_div_cancel_left₀ _ ( by nlinarith [ show 0 < ( m : ℝ ) * R by positivity ] ) ] ; gcongr;
        · convert algebraic_helper ( ∑ v ∈ E.biUnion id, ( degree E v : ℝ ) ) ( m * ( m - 1 ) * k ) _ _ m R _ _ _ using 1 <;> try positivity;
          · -- By simplifying, we can see that both sides are equal.
            field_simp [mul_comm, mul_assoc, mul_left_comm];
          · exact lt_of_lt_of_le ( by positivity ) h_sum_ge;
          · exact mul_nonneg ( mul_nonneg ( Nat.cast_nonneg _ ) ( sub_nonneg.mpr ( Nat.one_le_cast.mpr ( Nat.pos_of_ne_zero h ) ) ) ) ( Nat.cast_nonneg _ );
          · convert h_sum_ge using 1;
      refine le_trans h_subst ?_;
      refine' div_le_of_le_mul₀ _ _ _ <;> norm_cast;
      · exact add_nonneg ( Nat.cast_nonneg _ ) ( mul_nonneg ( mul_nonneg ( Nat.cast_nonneg _ ) ( by rw [ Int.subNatNat_eq_coe ] ; norm_num; linarith [ Nat.pos_of_ne_zero h ] ) ) ( Nat.cast_nonneg _ ) );
      · exact Nat.zero_le _;
      · have h_sum_sq_degrees : ∑ v ∈ E.biUnion id, (degree E v)^2 ≤ (∑ e ∈ E, e.card) + m * (m - 1) * k := by
          convert intersection_sum_bound E m k hm hk using 1;
          convert sum_sq_degrees_eq E using 1;
        have h_sum_card : ∑ e ∈ E, e.card ≤ ∑ v ∈ E.biUnion id, degree E v := by
          rw [ sum_degrees_eq_sum_card ];
        rw [ Int.subNatNat_of_le ( Nat.one_le_iff_ne_zero.mpr h ) ] ; norm_cast ; nlinarith;
    rcases m with ( _ | m ) <;> simp_all +decide
    rw [ div_le_iff₀ ] at h_subst <;> norm_cast at * <;> first | positivity | nlinarith;

/-
$B_k = \{(a, a') \in A \times A : a+a'=k, a \le a'\}$.
-/
def B_set (A : Finset ℕ) (k : ℕ) : Finset (ℕ × ℕ) :=
  (A.product A).filter (fun x => x.1 + x.2 = k ∧ x.1 ≤ x.2)

/-
$C_k = \{a a' : (a, a') \in B_k\}$.
$|C_k| = |B_k|$.
-/
def C_set (A : Finset ℕ) (k : ℕ) : Finset ℕ :=
  (B_set A k).image (fun x => x.1 * x.2)

lemma C_set_card_eq_B_set_card (A : Finset ℕ) (k : ℕ) :
  (C_set A k).card = (B_set A k).card := by
    rw [ show C_set A k = Finset.image ( fun x : ℕ × ℕ => x.1 * x.2 ) ( B_set A k ) from ?_ ];
    · -- To prove injectivity, assume two pairs (x, y) and (a, b) in B_set A k map to the same product. Then x*y = a*b and x + y = a + b. Since x ≤ y and a ≤ b, we can derive that x = a and y = b.
      have h_inj : ∀ x y a b : ℕ, x ∈ A → y ∈ A → a ∈ A → b ∈ A → x ≤ y → a ≤ b → x + y = k → a + b = k → x * y = a * b → x = a ∧ y = b := by
        intros x y a b hx hy ha hb hxy hab hxk hyk hxy_eq
        have h_eq : x = a ∨ x = b := by
          exact Classical.or_iff_not_imp_left.2 fun h => mul_left_cancel₀ ( Nat.ne_of_gt ( Nat.pos_of_ne_zero ( by aesop_cat : x ≠ 0 ) ) ) <| by cases lt_or_gt_of_ne h <;> nlinarith;
        grind;
      rw [ Finset.card_image_of_injOn ];
      intro x hx y hy; specialize h_inj x.1 x.2 y.1 y.2; ( unfold B_set at *; aesop; );
    · unfold C_set B_set; ext; aesop;

/-
If $S$ consists of positive integers, then $C_k \subseteq A_k$.
-/
lemma C_set_subset_A_k (S : Finset ℕ) (k : ℕ) (hS : ∀ x ∈ S, 1 ≤ x) :
  C_set S k ⊆ A k := by
    -- Take any element x in C_set S k. Then x = a * a' where a and a' are in S and a + a' = k.
    intro x hx
    obtain ⟨a, a', haS, ha'S, hsum, hx_eq⟩ : ∃ a a', a ∈ S ∧ a' ∈ S ∧ a + a' = k ∧ x = a * a' := by
      unfold C_set at hx; unfold B_set at hx; aesop;
    unfold A; aesop;

/-
$C_k \cap C_j \subseteq A_k \cap A_j$.
-/
lemma C_set_inter_subset_A_inter (S : Finset ℕ) (k j : ℕ) (hS : ∀ x ∈ S, 1 ≤ x) :
  C_set S k ∩ C_set S j ⊆ A k ∩ A j := by
    exact Finset.inter_subset_inter ( C_set_subset_A_k S k hS ) ( C_set_subset_A_k S j hS )

/-
The sum of sizes of $B_{full}$ sets is $n^2$.
-/
def B_full (A : Finset ℕ) (k : ℕ) : Finset (ℕ × ℕ) :=
  (A.product A).filter (fun x => x.1 + x.2 = k)

lemma sum_B_full_eq_sq (A : Finset ℕ) :
  ∑ k ∈ A + A, (B_full A k).card = (A.card)^2 := by
    -- The sets $B_{full}(A, k)$ for $k \in A+A$ form a partition of $A \times A$.
    have h_partition : Finset.biUnion (A + A) (fun k => B_full A k) = A ×ˢ A := by
      ext ⟨x, y⟩; simp [B_full];
      exact fun hx hy => Finset.add_mem_add hx hy;
    conv_rhs => rw [ sq, ← Finset.card_product ];
    rw [ ← h_partition, Finset.card_biUnion ];
    intro k hk l hl hkl; simp_all +decide [ Finset.disjoint_left, B_full ] ;

/-
The number of heavy indices is at least $(n^2 - |A+A|\delta)/n$.
-/
noncomputable def heavy_indices (A : Finset ℕ) (δ : ℝ) : Finset ℕ :=
  (A + A).filter (fun k => (B_full A k).card > δ)

lemma heavy_indices_card_bound (A : Finset ℕ) (n : ℕ) (δ : ℝ) (hA : A.card = n) (hδ : 0 ≤ δ) :
  (heavy_indices A δ).card * n ≥ n^2 - (A + A).card * δ := by
    -- By definition of heavy indices, we have $\sum_{k \in heavy\_indices(A, \delta)} |B_{full}(k)| \ge n^2 - |A+A| \delta$.
    have h_sum_heavy : (∑ k ∈ heavy_indices A δ, (B_full A k).card : ℝ) ≥ (n^2 : ℝ) - ((A + A).card : ℝ) * δ := by
      have h_sum_heavy : (∑ k ∈ (A + A), (B_full A k).card : ℝ) ≥ (n^2 : ℝ) := by
        rw_mod_cast [ ← hA ];
        convert sum_B_full_eq_sq A |> ge_of_eq;
      -- The sum of the sizes of the $B_{full}$ sets for the heavy indices is at least $n^2$ minus the sum of the sizes of the $B_{full}$ sets for the non-heavy indices.
      have h_sum_nonheavy : (∑ k ∈ (A + A) \ heavy_indices A δ, (B_full A k).card : ℝ) ≤ ((A + A).card : ℝ) * δ := by
        refine' le_trans ( Finset.sum_le_sum fun x hx => show ( B_full A x |> Finset.card : ℝ ) ≤ δ from _ ) _;
        · unfold heavy_indices at hx; aesop;
        · simp +zetaDelta at *;
          exact mul_le_mul_of_nonneg_right ( mod_cast Finset.card_le_card fun x hx => by aesop ) hδ;
      rw [ ← Finset.sum_sdiff ( show heavy_indices A δ ⊆ A + A from ?_ ) ] at * ; linarith!;
      unfold heavy_indices; aesop;
    refine le_trans h_sum_heavy ?_;
    have h_sum_le : ∀ k ∈ heavy_indices A δ, (B_full A k).card ≤ n := by
      intro k hk;
      have h_card_le_n : ∀ a ∈ A, (A.filter (fun b => a + b = k)).card ≤ 1 := by
        exact fun a ha => Finset.card_le_one.mpr fun b hb c hc => by linarith [ Finset.mem_filter.mp hb, Finset.mem_filter.mp hc ] ;
      have h_card_le_n : (B_full A k).card ≤ ∑ a ∈ A, (A.filter (fun b => a + b = k)).card := by
        rw [ show B_full A k = Finset.biUnion A ( fun a => Finset.image ( fun b => ( a, b ) ) ( Finset.filter ( fun b => a + b = k ) A ) ) from ?_, Finset.card_biUnion ];
        · exact Finset.sum_le_sum fun x hx => Finset.card_image_le;
        · exact fun a ha b hb hab => Finset.disjoint_left.mpr fun x hx₁ hx₂ => hab <| by aesop;
        · ext ⟨a, b⟩; simp [B_full];
          tauto;
      exact h_card_le_n.trans ( by simpa [ hA ] using Finset.sum_le_sum ‹∀ a ∈ A, Finset.card ( Finset.filter ( fun b => a + b = k ) A ) ≤ 1› );
    exact_mod_cast Finset.sum_le_card_nsmul _ _ _ h_sum_le

/-
$2 |C_k| \ge |B_{full}(k)|$.
-/
lemma C_set_card_lower_bound (A : Finset ℕ) (k : ℕ) :
  2 * (C_set A k).card ≥ (B_full A k).card := by
    -- Let's split the sum $\sum_{x \in B_{full} k} 1$ into two parts: one where $x.1 \leq x.2$ and one where $x.1 > x.2$.
    have h_split_sum : ∑ x ∈ B_full A k, 1 ≤ ∑ x ∈ B_set A k, 1 + ∑ x ∈ B_set A k, 1 := by
      -- Since $B_{full} k$ is the union of $B_{set} k$ and its symmetric counterpart, we can split the sum accordingly.
      have h_union : B_full A k = B_set A k ∪ Finset.image (fun x => (x.2, x.1)) (B_set A k) := by
        ext ⟨a, b⟩; simp [B_full, B_set];
        grind +ring;
      rw [ h_union, ← Finset.sum_union_inter ];
      simp +zetaDelta at *;
      exact le_trans ( Finset.card_union_le _ _ ) ( add_le_add_left ( Finset.card_image_le ) _ );
    -- Since $C_set A k$ is the image of $B_set A k$ under the function $x \mapsto x.1 * x.2$, and this function is injective on $B_set A k$, we have $|C_set A k| = |B_set A k|$.
    have h_C_set_card : (C_set A k).card = (B_set A k).card := by
      exact C_set_card_eq_B_set_card A k;
    simp_all +decide [ two_mul ]

/-
For large $n$, $4/L + 2 \log 2 L^{c-1} \le 3 L^{c-1}$ where $L = \log \log n$.
-/
lemma exponent_inequality (c : ℝ) (hc : 0 < c) (hc1 : c < 1) :
  ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
  let L := Real.log (Real.log n)
  4 / L + 2 * Real.log 2 * L^(c - 1) ≤ 3 * L^(c - 1) := by
    -- We want $4 L^{-1} + 2 \log 2 L^{c-1} \le 3 L^{c-1}$.
    -- Divide by $L^{c-1}$: $4 L^{-1 - (c-1)} + 2 \log 2 \le 3$.
    -- $4 L^{-c} + 2 \log 2 \le 3$.
    suffices h_div : ∃ N : ℕ, ∀ n : ℕ, N ≤ n → (let L := Real.log (Real.log n); 4 / L^c + 2 * Real.log 2 ≤ 3) by
      obtain ⟨ N, hN ⟩ := h_div; use Max.max N 3; intros n hn; specialize hN n <| le_trans ( le_max_left _ _ ) hn; rcases eq_or_ne ( Real.log ( Real.log n ) ) 0 with h|h <;> simp_all +decide [ Real.rpow_sub_one ] ;
      · rcases h with ( ( rfl | rfl | h ) | h | h ) <;> norm_cast at * ; aesop;
        · grind;
        · exact absurd h <| ne_of_gt <| Real.lt_log_iff_exp_lt ( by norm_cast; linarith ) |>.2 <| by exact Real.exp_one_lt_d9.trans_le <| by norm_num; linarith [ show ( n : ℝ ) ≥ 3 by norm_cast; linarith ] ;
        · exact absurd h ( by norm_num; linarith [ Real.log_nonneg ( show ( n : ℝ ) ≥ 1 by norm_cast; linarith ) ] );
      · convert mul_le_mul_of_nonneg_right hN ( show 0 ≤ Real.log ( Real.log n ) ^ c / Real.log ( Real.log n ) from div_nonneg ( Real.rpow_nonneg ( Real.log_nonneg <| show 1 ≤ Real.log n from by rw [ Real.le_log_iff_exp_le <| by norm_cast; linarith ] ; exact Real.exp_one_lt_d9.le.trans <| by norm_num; linarith [ show ( n :ℝ ) ≥ 3 by norm_cast; linarith ] ) _ ) ( Real.log_nonneg <| show 1 ≤ Real.log n from by rw [ Real.le_log_iff_exp_le <| by norm_cast; linarith ] ; exact Real.exp_one_lt_d9.le.trans <| by norm_num; linarith [ show ( n :ℝ ) ≥ 3 by norm_cast; linarith ] ) ) using 1 ; ring_nf;
        by_cases h' : Real.log ( Real.log n ) ^ c = 0 <;> simp_all +decide [ add_comm, mul_assoc ];
        exact ne_of_gt ( Real.rpow_pos_of_pos ( Real.log_pos <| show 1 < Real.log n from by rw [ Real.lt_log_iff_exp_lt <| by norm_cast; linarith ] ; exact Real.exp_one_lt_d9.trans_le <| by norm_num; linarith [ show ( n :ℝ ) ≥ 3 by norm_cast; linarith ] ) _ ) h';
    -- Since $c > 0$, $L^{-c} \to 0$ as $n \to \infty$.
    have h_lim : Filter.Tendsto (fun n : ℕ => 4 / (Real.log (Real.log n)) ^ c) Filter.atTop (nhds 0) := by
      exact tendsto_const_nhds.div_atTop ( tendsto_rpow_atTop ( by positivity ) |> Filter.Tendsto.comp <| Real.tendsto_log_atTop.comp <| Real.tendsto_log_atTop.comp <| tendsto_natCast_atTop_atTop );
    exact Filter.eventually_atTop.mp ( h_lim.eventually ( gt_mem_nhds <| show 0 < 3 - 2 * Real.log 2 by have := Real.log_two_lt_d9; norm_num1 at *; linarith ) ) |> fun ⟨ N, hN ⟩ ↦ ⟨ N, fun n hn ↦ by linarith [ hN n hn ] ⟩

/-
If the sumset is small, there are many heavy indices. Specifically, if $|S+S| \le n^{4/3 - 3/(\log \log n)^{1-c}}$, then there are at least $0.5n$ indices $k$ such that $|B_k| > 0.5 n^{2/3 - 2/\log \log n}$.
-/
theorem heavy_indices_lower_bound (c : ℝ) (hc0 : 0 < c) (hc1 : c < 1) :
  ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
  ∀ S : Finset ℕ, S.card = n →
  let T := (S + S).card
  let δ := 0.5 * (n : ℝ) ^ (2/3 - 2 / Real.log (Real.log n))
  (T : ℝ) ≤ (n : ℝ) ^ (4/3 - 3 / (Real.log (Real.log n)) ^ (1 - c)) →
  ((heavy_indices S δ).card : ℝ) ≥ 0.5 * n := by
    -- Let's choose any $N$ such that for all $n \geq N$, the inequality $4/L + 2 \log 2 L^{c-1} \le 3 L^{c-1}$ holds.
    obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      let L := Real.log (Real.log n)
      4 / L + 2 * Real.log 2 * L^(c - 1) ≤ 3 * L^(c - 1) := by
        exact exponent_inequality c hc0 hc1;
    refine' ⟨ N + 4, fun n hn S hS hT => _ ⟩ ; specialize hN n ( by linarith ) ; norm_num at *;
    -- Applying the lemma heavy_indices_card_bound with δ = 0.5 * n^(2/3 - 2 / Real.log (Real.log n)), we get:
    have h_card_bound : (heavy_indices S (1 / 2 * (n : ℝ) ^ (2 / 3 - 2 / Real.log (Real.log n)))).card * n ≥ n^2 - (S + S).card * (1 / 2 * (n : ℝ) ^ (2 / 3 - 2 / Real.log (Real.log n))) := by
      convert heavy_indices_card_bound S n ( 1 / 2 * ( n : ℝ ) ^ ( 2 / 3 - 2 / Real.log ( Real.log n ) ) ) hS _ using 1 ; norm_num;
      positivity;
    -- We'll use that $T \leq n^{4/3 - 3 / (\log \log n)^{1-c}}$ and $\delta = 0.5 n^{2/3 - 2 / \log \log n}$ to bound the term $T \cdot \delta$.
    have h_T_delta_bound : (S + S).card * (1 / 2 * (n : ℝ) ^ (2 / 3 - 2 / Real.log (Real.log n))) ≤ (n : ℝ) ^ (4 / 3 - 3 / (Real.log (Real.log n)) ^ (1 - c)) * (1 / 2 * (n : ℝ) ^ (2 / 3 - 2 / Real.log (Real.log n))) := by
      gcongr;
    -- Simplify the expression $n^{4/3 - 3 / (\log \log n)^{1-c}} \cdot 0.5 n^{2/3 - 2 / \log \log n}$ to $0.5 n^{2 - 3 / (\log \log n)^{1-c} - 2 / \log \log n}$.
    have h_simplified : (n : ℝ) ^ (4 / 3 - 3 / (Real.log (Real.log n)) ^ (1 - c)) * (1 / 2 * (n : ℝ) ^ (2 / 3 - 2 / Real.log (Real.log n))) = (1 / 2 : ℝ) * (n : ℝ) ^ (2 - 3 / (Real.log (Real.log n)) ^ (1 - c) - 2 / Real.log (Real.log n)) := by
      rw [ mul_left_comm, ← Real.rpow_add ( by norm_cast; linarith ) ] ; ring_nf;
    -- For large $n$, $3 / (\log \log n)^{1-c} + 2 / \log \log n > 0$, so $0.5 n^{2 - 3 / (\log \log n)^{1-c} - 2 / \log \log n} < 0.5 n^2$.
    have h_large_n : (n : ℝ) ^ (2 - 3 / (Real.log (Real.log n)) ^ (1 - c) - 2 / Real.log (Real.log n)) < (n : ℝ) ^ 2 := by
      have h_large_n : 3 / (Real.log (Real.log n)) ^ (1 - c) + 2 / Real.log (Real.log n) > 0 := by
        exact add_pos_of_nonneg_of_pos ( div_nonneg zero_le_three ( Real.rpow_nonneg ( Real.log_nonneg ( show 1 ≤ Real.log n by rw [ Real.le_log_iff_exp_le ( by norm_cast; linarith ) ] ; exact Real.exp_one_lt_d9.le.trans ( by norm_num; linarith [ show ( n : ℝ ) ≥ 4 by norm_cast; linarith ] ) ) ) _ ) ) ( div_pos zero_lt_two ( Real.log_pos ( show 1 < Real.log n by rw [ Real.lt_log_iff_exp_lt ( by norm_cast; linarith ) ] ; exact Real.exp_one_lt_d9.trans_le ( by norm_num; linarith [ show ( n : ℝ ) ≥ 4 by norm_cast; linarith ] ) ) ) );
      exact lt_of_lt_of_le ( Real.rpow_lt_rpow_of_exponent_lt ( by norm_cast; linarith ) ( show ( 2 - 3 / Real.log ( Real.log n ) ^ ( 1 - c ) - 2 / Real.log ( Real.log n ) ) < 2 by linarith ) ) ( by norm_num );
    nlinarith [ show ( n : ℝ ) ≥ 4 by norm_cast; linarith ]

/-
The function $x \mapsto \frac{\log x}{\log \log x}$ is eventually increasing.
-/
lemma log_div_log_log_increasing :
  ∃ X : ℝ, 0 < X ∧ ∀ x y : ℝ, X ≤ x → x ≤ y →
  Real.log x / Real.log (Real.log x) ≤ Real.log y / Real.log (Real.log y) := by
    -- The derivative of $f(x) = \frac{\log x}{\log \log x}$ is $f'(x) = \frac{\frac{1}{x} \log \log x - \log x \frac{1}{\log x} \frac{1}{x}}{(\log \log x)^2} = \frac{\log \log x - 1}{x (\log \log x)^2}$.
    -- This is positive when $\log \log x > 1$, i.e., $x > e^e$.
    use Real.exp (Real.exp 1) + 1;
    -- By the properties of the derivative, if the derivative is positive on an interval, then the function is increasing on that interval. Hence, we need to show that the derivative is positive for $x > e^e$.
    have h_deriv_pos : ∀ x, Real.exp (Real.exp 1) < x → deriv (fun x => Real.log x / Real.log (Real.log x)) x > 0 := by
      intro x hx
      have h_deriv : deriv (fun x => Real.log x / Real.log (Real.log x)) x = (Real.log (Real.log x) - 1) / (x * (Real.log (Real.log x))^2) := by
        convert HasDerivAt.deriv ( HasDerivAt.div ( Real.hasDerivAt_log ( show x ≠ 0 by linarith [ Real.exp_pos ( Real.exp 1 ) ] ) ) ( HasDerivAt.log ( Real.hasDerivAt_log ( show x ≠ 0 by linarith [ Real.exp_pos ( Real.exp 1 ) ] ) ) ( show Real.log x ≠ 0 by exact ne_of_gt <| Real.log_pos <| lt_trans ( by norm_num [ Real.exp_pos ] ) hx ) ) ( show Real.log ( Real.log x ) ≠ 0 by exact ne_of_gt <| Real.log_pos <| by rw [ Real.lt_log_iff_exp_lt ] <;> linarith [ Real.add_one_le_exp 1, Real.add_one_le_exp ( Real.exp 1 ) ] ) ) using 1 ; ring_nf;
        norm_num [ ne_of_gt ( Real.log_pos ( show 1 < x by linarith [ Real.add_one_le_exp 1, Real.add_one_le_exp ( Real.exp 1 ) ] ) ) ];
      exact h_deriv.symm ▸ div_pos ( sub_pos_of_lt ( Real.lt_log_iff_exp_lt ( Real.log_pos <| lt_trans ( by norm_num [ Real.exp_pos ] ) hx ) |>.2 <| by rw [ Real.lt_log_iff_exp_lt ] <;> linarith [ Real.add_one_le_exp 1, Real.add_one_le_exp ( Real.exp 1 ) ] ) ) ( mul_pos ( lt_trans ( by positivity ) hx ) <| sq_pos_of_pos <| Real.log_pos <| show 1 < Real.log x from by rw [ Real.lt_log_iff_exp_lt ] <;> linarith [ Real.add_one_le_exp 1, Real.add_one_le_exp ( Real.exp 1 ) ] );
    -- By the Mean Value Theorem, if the derivative of a function is positive on an interval, then the function is strictly increasing on that interval.
    have h_mvt : ∀ x y, x < y → Real.exp (Real.exp 1) < x → x ≤ y → ∃ c ∈ Set.Ioo x y, deriv (fun x => Real.log x / Real.log (Real.log x)) c = (Real.log y / Real.log (Real.log y) - Real.log x / Real.log (Real.log x)) / (y - x) := by
      intros x y hxy hx hy; apply_rules [ exists_deriv_eq_slope ];
      · exact continuousOn_of_forall_continuousAt fun x hx => DifferentiableAt.continuousAt ( by exact differentiableAt_of_deriv_ne_zero ( ne_of_gt ( h_deriv_pos x ( by linarith [ hx.1, Real.add_one_le_exp 1, Real.add_one_le_exp ( Real.exp 1 ) ] ) ) ) );
      · exact fun u hu => DifferentiableAt.differentiableWithinAt ( by exact differentiableAt_of_deriv_ne_zero ( ne_of_gt ( h_deriv_pos u ( by linarith [ hu.1 ] ) ) ) );
    exact ⟨ by positivity, fun x y hx hy => by rcases eq_or_lt_of_le hy with rfl | hy' <;> [ norm_num; exact by obtain ⟨ c, ⟨ hxc, hcy ⟩, hcd ⟩ := h_mvt x y hy' ( by linarith ) ( by linarith ) ; have := h_deriv_pos c ( by linarith ) ; rw [ hcd, div_eq_mul_inv ] at this ; nlinarith [ inv_mul_cancel₀ ( by linarith : ( y - x ) ≠ 0 ) ] ] ⟩

/-
As $n \to \infty$, $\log M \sim (\log \log n)^c \log n$.
-/
lemma log_M_asymp (c : ℝ) (hc0 : 0 < c) (hc1 : c < 1) :
  Filter.Tendsto (fun n => Real.log (2 * (n : ℝ) ^ ((Real.log (Real.log n)) ^ c)) / ((Real.log (Real.log n)) ^ c * Real.log n)) Filter.atTop (nhds 1) := by
    -- We can split the logarithm of the product into the sum of logarithms.
    suffices h_split : Filter.Tendsto (fun n => (Real.log 2 + (Real.log (Real.log n))^c * Real.log n) / ((Real.log (Real.log n))^c * Real.log n)) Filter.atTop (nhds 1) by
      refine h_split.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 1 ] with n hn using by rw [ Real.log_mul ( by positivity ) ( by positivity ), Real.log_rpow ( by positivity ) ] );
    -- We can split the fraction into two parts: $\frac{\log 2}{(\log \log n)^c \log n}$ and $\frac{(\log \log n)^c \log n}{(\log \log n)^c \log n}$.
    suffices h_split : Filter.Tendsto (fun n => Real.log 2 / ((Real.log (Real.log n))^c * Real.log n) + 1) Filter.atTop (nhds 1) by
      refine h_split.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 1, Filter.eventually_gt_atTop ( Real.exp 1 ) ] with n hn hn' using by rw [ add_div, div_self <| mul_ne_zero ( ne_of_gt <| Real.rpow_pos_of_pos ( Real.log_pos <| show 1 < Real.log n by rw [ Real.lt_log_iff_exp_lt <| by linarith ] ; linarith ) _ ) <| ne_of_gt <| Real.log_pos <| show 1 < n by linarith ] );
    exact le_trans ( Filter.Tendsto.add ( tendsto_const_nhds.div_atTop <| Filter.Tendsto.atTop_mul_atTop₀ ( tendsto_rpow_atTop ( by linarith ) |> Filter.Tendsto.comp <| Real.tendsto_log_atTop.comp <| Real.tendsto_log_atTop ) <| Real.tendsto_log_atTop ) tendsto_const_nhds ) ( by norm_num )

/-
As $n \to \infty$, $\log \log M \sim \log \log n$.
-/
lemma log_log_M_asymp (c : ℝ) (hc0 : 0 < c) (hc1 : c < 1) :
  Filter.Tendsto (fun n => Real.log (Real.log (2 * (n : ℝ) ^ ((Real.log (Real.log n)) ^ c))) / Real.log (Real.log n)) Filter.atTop (nhds 1) := by
    have h_log_log_M : Filter.Tendsto (fun n => Real.log ((Real.log (2 * (n : ℝ) ^ ((Real.log (Real.log n)) ^ c)) - ((Real.log (Real.log n)) ^ c * Real.log n)) / ((Real.log (Real.log n)) ^ c * Real.log n) + 1) / Real.log (Real.log n)) Filter.atTop (nhds 0) := by
      have h_log_log_M : Filter.Tendsto (fun n => ((Real.log (2 * (n : ℝ) ^ ((Real.log (Real.log n)) ^ c)) - ((Real.log (Real.log n)) ^ c * Real.log n)) / ((Real.log (Real.log n)) ^ c * Real.log n))) Filter.atTop (nhds 0) := by
        have h_log_log_M : Filter.Tendsto (fun n => (Real.log (2 * (n : ℝ) ^ ((Real.log (Real.log n)) ^ c)) / ((Real.log (Real.log n)) ^ c * Real.log n)) - 1) Filter.atTop (nhds 0) := by
          convert Filter.Tendsto.sub_const ( log_M_asymp c hc0 hc1 ) 1 using 2 ; ring;
        refine h_log_log_M.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 1, Filter.eventually_gt_atTop ( Real.exp 1 ) ] with n hn hn'; rw [ sub_div, div_self <| ne_of_gt <| mul_pos ( Real.rpow_pos_of_pos ( Real.log_pos <| show 1 < Real.log n from by rw [ Real.lt_log_iff_exp_lt <| by linarith ] ; linarith ) _ ) <| Real.log_pos <| show 1 < n from by linarith ] );
      convert Filter.Tendsto.div_atTop ( Filter.Tendsto.log ( h_log_log_M.add_const 1 ) _ ) ( Real.tendsto_log_atTop.comp ( Real.tendsto_log_atTop ) ) using 2 ; norm_num;
    have h_log_log_M : Filter.Tendsto (fun n => (Real.log ((Real.log (2 * (n : ℝ) ^ ((Real.log (Real.log n)) ^ c)) - ((Real.log (Real.log n)) ^ c * Real.log n)) / ((Real.log (Real.log n)) ^ c * Real.log n) + 1) + Real.log ((Real.log (Real.log n)) ^ c * Real.log n)) / Real.log (Real.log n)) Filter.atTop (nhds 1) := by
      have h_log_log_M : Filter.Tendsto (fun n => Real.log ((Real.log (Real.log n)) ^ c * Real.log n) / Real.log (Real.log n)) Filter.atTop (nhds 1) := by
        have h_log_log_M : Filter.Tendsto (fun n => (c * Real.log (Real.log (Real.log n)) + Real.log (Real.log n)) / Real.log (Real.log n)) Filter.atTop (nhds 1) := by
          have h_log_log_M : Filter.Tendsto (fun n => c * Real.log (Real.log (Real.log n)) / Real.log (Real.log n) + 1) Filter.atTop (nhds 1) := by
            have h_log_log_M : Filter.Tendsto (fun n => Real.log (Real.log (Real.log n)) / Real.log (Real.log n)) Filter.atTop (nhds 0) := by
              have h_log_log_M : Filter.Tendsto (fun x => Real.log x / x) Filter.atTop (nhds 0) := by
                -- Let $y = \frac{1}{x}$, so we can rewrite the limit as $\lim_{y \to 0^+} y \log(1/y)$.
                suffices h_log_recip : Filter.Tendsto (fun y => y * Real.log (1 / y)) (Filter.map (fun x => 1 / x) Filter.atTop) (nhds 0) by
                  exact h_log_recip.congr ( by simp +contextual [ div_eq_inv_mul ] );
                norm_num +zetaDelta at *;
                exact tendsto_nhdsWithin_of_tendsto_nhds ( by simpa using Real.continuous_mul_log.neg.tendsto 0 );
              exact h_log_log_M.comp ( Real.tendsto_log_atTop.comp ( Real.tendsto_log_atTop ) );
            simpa [ mul_div_assoc ] using Filter.Tendsto.add ( h_log_log_M.const_mul c ) tendsto_const_nhds;
          refine h_log_log_M.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 1, Filter.eventually_gt_atTop ( Real.exp 1 ) ] with n hn hn'; rw [ add_div, div_self <| ne_of_gt <| Real.log_pos <| show 1 < Real.log n from by rw [ Real.lt_log_iff_exp_lt <| by linarith ] ; linarith ] );
        refine h_log_log_M.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 1, Filter.eventually_gt_atTop ( Real.exp 1 ) ] with n hn hn'; rw [ Real.log_mul ( by exact ne_of_gt ( Real.rpow_pos_of_pos ( Real.log_pos <| show 1 < Real.log n from by rw [ Real.lt_log_iff_exp_lt <| by positivity ] ; linarith ) _ ) ) ( by exact ne_of_gt ( Real.log_pos <| show 1 < n from by linarith ) ) ] ; rw [ Real.log_rpow ( Real.log_pos <| show 1 < Real.log n from by rw [ Real.lt_log_iff_exp_lt <| by positivity ] ; linarith ) ] ) ;
      convert ‹Filter.Tendsto ( fun n => Real.log ( ( Real.log ( 2 * n ^ Real.log ( Real.log n ) ^ c ) - Real.log ( Real.log n ) ^ c * Real.log n ) / ( Real.log ( Real.log n ) ^ c * Real.log n ) + 1 ) / Real.log ( Real.log n ) ) Filter.atTop ( nhds 0 ) ›.add h_log_log_M using 2 <;> ring;
    refine h_log_log_M.congr' ?_;
    filter_upwards [ Filter.eventually_gt_atTop 1, Filter.eventually_gt_atTop ( Real.exp 1 ), Filter.eventually_gt_atTop ( Real.exp ( Real.exp 1 ) ) ] with n hn hn' hn'';
    rw [ div_add_one, Real.log_div ] <;> norm_num;
    · exact ⟨ by positivity, by linarith [ Real.one_le_rpow hn.le ( show 0 ≤ Real.log ( Real.log n ) ^ c by exact Real.rpow_nonneg ( Real.log_nonneg ( show 1 ≤ Real.log n by rw [ Real.le_log_iff_exp_le ( by positivity ) ] ; linarith [ Real.add_one_le_exp 1 ] ) ) _ ) ], by linarith [ Real.one_le_rpow hn.le ( show 0 ≤ Real.log ( Real.log n ) ^ c by exact Real.rpow_nonneg ( Real.log_nonneg ( show 1 ≤ Real.log n by rw [ Real.le_log_iff_exp_le ( by positivity ) ] ; linarith [ Real.add_one_le_exp 1 ] ) ) _ ) ] ⟩;
    · exact ⟨ ne_of_gt ( Real.rpow_pos_of_pos ( Real.log_pos ( show 1 < Real.log n from by rw [ Real.lt_log_iff_exp_lt ] <;> linarith [ Real.add_one_le_exp 1 ] ) ) _ ), by linarith, by linarith, by linarith ⟩;
    · exact ⟨ ne_of_gt ( Real.rpow_pos_of_pos ( Real.log_pos ( show 1 < Real.log n from by rw [ Real.lt_log_iff_exp_lt ] <;> linarith [ Real.add_one_le_exp 1 ] ) ) _ ), by linarith, by linarith, by linarith ⟩

/-
The ratio of $\frac{\log M}{\log \log M}$ to $\frac{\log n}{(\log \log n)^{1-c}}$ tends to 1.
-/
lemma ratio_asymp (c : ℝ) (hc0 : 0 < c) (hc1 : c < 1) :
  Filter.Tendsto (fun n => (Real.log (2 * (n : ℝ) ^ ((Real.log (Real.log n)) ^ c)) / Real.log (Real.log (2 * (n : ℝ) ^ ((Real.log (Real.log n)) ^ c)))) / (Real.log n / (Real.log (Real.log n)) ^ (1 - c))) Filter.atTop (nhds 1) := by
    -- Rewrite the limit expression using the fact that $\frac{\log M_n}{\log \log M_n} \frac{(\log \log n)^{1-c}}{\log n}$ tends to 1.
    have h_rewrite : Filter.Tendsto (fun n => (Real.log (2 * n ^ ((Real.log (Real.log n)) ^ c))) / ((Real.log (Real.log n)) ^ c * Real.log n) * (Real.log (Real.log n)) / (Real.log (Real.log (2 * n ^ ((Real.log (Real.log n)) ^ c))))) Filter.atTop (nhds 1) := by
      -- We can use the fact that $\log(M_n) \sim (\log \log n)^c \log n$ and $\log(\log M_n) \sim \log \log n$ as $n \to \infty$.
      have h_log_M_log_log_M : Filter.Tendsto (fun n => Real.log (2 * n ^ ((Real.log (Real.log n)) ^ c)) / ((Real.log (Real.log n)) ^ c * Real.log n)) Filter.atTop (nhds 1) ∧ Filter.Tendsto (fun n => Real.log (Real.log (2 * n ^ ((Real.log (Real.log n)) ^ c))) / Real.log (Real.log n)) Filter.atTop (nhds 1) := by
        exact ⟨ log_M_asymp c hc0 hc1, log_log_M_asymp c hc0 hc1 ⟩;
      simpa [ mul_div_assoc ] using h_log_M_log_log_M.1.mul ( h_log_M_log_log_M.2.inv₀ <| by norm_num );
    simp_all +decide [ division_def ];
    refine h_rewrite.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 1, Filter.eventually_gt_atTop ( Real.exp 1 ) ] with n hn hn' ; rw [ Real.rpow_sub ( Real.log_pos <| show 1 < Real.log n from by rw [ Real.lt_log_iff_exp_lt <| by positivity ] ; linarith [ Real.add_one_le_exp 1 ] ) ] ; norm_num ; ring )

/-
For large $n$, $\frac{\log M}{\log \log M} \le \frac{2}{2.1 \log 2} \frac{\log n}{(\log \log n)^{1-c}}$.
-/
lemma algebraic_bound_step1 (c : ℝ) (hc0 : 0 < c) (hc1 : c < 1) :
  ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
  let L := Real.log (Real.log n)
  let M := 2 * (n : ℝ) ^ (L ^ c)
  Real.log M / Real.log (Real.log M) ≤ (2 / (2.1 * Real.log 2)) * Real.log n / L ^ (1 - c) := by
    -- By the properties of logarithms and limits, we can simplify the ratio.
    have h_ratio_simplified : Filter.Tendsto (fun n => (Real.log (2 * (n : ℝ) ^ ((Real.log (Real.log n)) ^ c)) / Real.log (Real.log (2 * (n : ℝ) ^ ((Real.log (Real.log n)) ^ c)))) / (Real.log n / (Real.log (Real.log n)) ^ (1 - c))) Filter.atTop (nhds 1) := by
      convert ratio_asymp c hc0 hc1 using 1;
    -- By the properties of logarithms and limits, we can simplify the ratio and find such an $N$.
    have h_ratio_simplified : ∃ N : ℕ, ∀ n ≥ N, (Real.log (2 * (n : ℝ) ^ ((Real.log (Real.log n)) ^ c)) / Real.log (Real.log (2 * (n : ℝ) ^ ((Real.log (Real.log n)) ^ c)))) / (Real.log n / (Real.log (Real.log n)) ^ (1 - c)) ≤ 2 / (2.1 * Real.log 2) := by
      have := h_ratio_simplified.eventually ( ge_mem_nhds <| show ( 1 : ℝ ) < 2 / ( 2.1 * Real.log 2 ) from ?_ );
      · rw [ Filter.eventually_atTop ] at this; rcases this with ⟨ N, hN ⟩ ; exact ⟨ ⌈N⌉₊, fun n hn => hN n <| Nat.le_of_ceil_le hn ⟩ ;
      · rw [ lt_div_iff₀ ] <;> have := Real.log_two_lt_d9 <;> norm_num at * <;> linarith [ Real.log_pos one_lt_two ];
    obtain ⟨ N, hN ⟩ := h_ratio_simplified; use N + 3; intros n hn; specialize hN n ( by linarith ) ; by_cases hn' : Real.log n = 0 <;> by_cases hn'' : Real.log ( Real.log n ) = 0 <;> simp_all +decide [ mul_div_assoc ] ;
    · rcases hn' with ( rfl | rfl | hn' ) <;> norm_cast at *;
    · cases hn'' <;> simp_all +decide [ ne_of_gt ];
      · exact div_nonpos_of_nonneg_of_nonpos ( Real.log_nonneg ( by norm_num ) ) ( Real.log_nonpos ( by positivity ) ( by linarith [ Real.log_le_sub_one_of_pos zero_lt_two ] ) );
      · linarith [ Real.log_pos ( show ( n : ℝ ) > 1 by norm_cast; linarith ) ];
    · rwa [ div_le_iff₀ ( div_pos ( Real.log_pos ( by norm_cast; linarith ) ) ( Real.rpow_pos_of_pos ( Real.log_pos ( show 1 < Real.log n from by rw [ Real.lt_log_iff_exp_lt ( by norm_cast; linarith ) ] ; exact Real.exp_one_lt_d9.trans_le ( by norm_num; linarith [ show ( n : ℝ ) ≥ 3 by norm_cast; linarith ] ) ) ) _ ) ) ] at hN

/-
For large $n$, if $K \le m \le 2 n^{(\log \log n)^c}$, then $m^{\frac{2.1 \log 2}{\log \log m}} \le n^{\frac{2}{(\log \log n)^{1-c}}}$.
-/
lemma exponent_bound_lemma (c : ℝ) (hc0 : 0 < c) (hc1 : c < 1) :
  ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
  ∃ K : ℝ, ∀ m : ℝ, K ≤ m →
  m ≤ 2 * (n : ℝ) ^ ((Real.log (Real.log n)) ^ c) →
  m ^ (2.1 * Real.log 2 / Real.log (Real.log m)) ≤ (n : ℝ) ^ (2 / (Real.log (Real.log n)) ^ (1 - c)) := by
    -- By `algebraic_bound_step1`, there exists an $N_1$ such that for $n \geq N_1$, the inequality holds.
    obtain ⟨N1, hN1⟩ : ∃ N1 : ℕ, ∀ n : ℕ, N1 ≤ n →
      let L := Real.log (Real.log n)
      let M := 2 * (n : ℝ) ^ (L ^ c)
      Real.log M / Real.log (Real.log M) ≤ (2 / (2.1 * Real.log 2)) * Real.log n / L ^ (1 - c) := by
        exact algebraic_bound_step1 c hc0 hc1;
    -- By `log_div_log_log_increasing`, there exists an $X$ such that for $m \geq X$ and $n \geq X$, the inequality holds.
    obtain ⟨X, hX_pos, hX⟩ : ∃ X : ℝ, 0 < X ∧ ∀ x y : ℝ, X ≤ x → x ≤ y →
        Real.log x / Real.log (Real.log x) ≤ Real.log y / Real.log (Real.log y) := by
          exact log_div_log_log_increasing;
    refine' ⟨ ⌈X⌉₊ + N1 + 1, fun n hn => ⟨ ⌈X⌉₊ + 1, fun m hm₁ hm₂ => _ ⟩ ⟩;
    -- By `hN1`, we have $\frac{\log m}{\log \log m} \le \frac{2}{2.1 \log 2} \frac{\log n}{(\log \log n)^{1-c}}$.
    have h_log_ratio : Real.log m / Real.log (Real.log m) ≤ (2 / (2.1 * Real.log 2)) * Real.log n / (Real.log (Real.log n)) ^ (1 - c) := by
      refine le_trans ( hX _ _ ?_ hm₂ ) ( hN1 n ( by linarith ) );
      linarith [ Nat.le_ceil X ];
    rw [ Real.rpow_def_of_pos ( by linarith ), Real.rpow_def_of_pos ( by norm_cast; linarith ) ];
    convert Real.exp_le_exp.mpr ( mul_le_mul_of_nonneg_right h_log_ratio <| show 0 ≤ 2.1 * Real.log 2 by positivity ) using 1 ; ring_nf;
    ring_nf;
    norm_num

/-
The sequence $n^{\frac{2}{(\log \log n)^{1-c}}}$ tends to infinity as $n \to \infty$.
-/
lemma limit_bound_lemma (c : ℝ) :
  Filter.Tendsto (fun n : ℕ => (n : ℝ) ^ (2 / (Real.log (Real.log n)) ^ (1 - c))) Filter.atTop Filter.atTop := by
    -- We want to show $n^{\frac{2}{(\log \log n)^{1-c}}} \to \infty$.
    -- Let $L = \log \log n$. The exponent is $\frac{2}{L^{1-c}}$.
    -- The expression is $\exp(\log n \cdot \frac{2}{L^{1-c}}) = \exp(\frac{2 \log n}{(\log \log n)^{1-c}})$.
    -- Let $x = \log n$. Then $L = \log x$.
    -- We look at $\frac{2x}{(\log x)^{1-c}}$.
    -- Since $1-c > 0$, $(\log x)^{1-c}$ grows much slower than $x$.
    -- So $\frac{2x}{(\log x)^{1-c}} \to \infty$.
    have h_exp : Filter.Tendsto (fun x : ℝ => (2 * x) / (Real.log x) ^ (1 - c)) Filter.atTop Filter.atTop := by
      -- We can use the fact that $\frac{x}{(\log x)^{1-c}}$ tends to infinity as $x$ goes to infinity.
      have h_log : Filter.Tendsto (fun x : ℝ => x / (Real.log x) ^ (1 - c)) Filter.atTop Filter.atTop := by
        -- Let $y = \log x$, therefore the limit becomes $\lim_{y \to \infty} \frac{e^y}{y^{1-c}}$.
        suffices h_log : Filter.Tendsto (fun y : ℝ => Real.exp y / y ^ (1 - c)) Filter.atTop Filter.atTop by
          have := h_log.comp Real.tendsto_log_atTop;
          exact this.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with x hx using by rw [ Function.comp_apply, Real.exp_log hx ] );
        exact tendsto_exp_div_rpow_atTop (1 - c);
      simpa only [ mul_div_assoc ] using h_log.const_mul_atTop zero_lt_two;
    -- By substituting $x = \log n$, we can rewrite the limit expression.
    have h_subst : Filter.Tendsto (fun n : ℕ => Real.exp ((2 * Real.log n) / (Real.log (Real.log n)) ^ (1 - c))) Filter.atTop Filter.atTop := by
      exact Real.tendsto_exp_atTop.comp <| h_exp.comp <| Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop;
    refine h_subst.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with n hn; rw [ Real.rpow_def_of_pos ( Nat.cast_pos.mpr hn ) ] ; ring_nf )

/-
For any constant $K$, for sufficiently large $n$, $n^{\frac{2}{(\log \log n)^{1-c}}} \ge K$.
-/
lemma eventually_bound_gt_K (c : ℝ) (K : ℝ) :
  ∃ N : ℕ, ∀ n : ℕ, N ≤ n → K ≤ (n : ℝ) ^ (2 / (Real.log (Real.log n)) ^ (1 - c)) := by
    have h_tendsto : Filter.Tendsto (fun n : ℕ => (n : ℝ) ^ (2 / (Real.log (Real.log n)) ^ (1 - c))) Filter.atTop Filter.atTop := by
      convert limit_bound_lemma c using 1;
    simpa using h_tendsto.eventually_ge_atTop K

/-
For large $n$, if $K \le m \le 2 n^{(\log \log n)^c}$, then $m^{\frac{2.1 \log 2}{\log \log m}} \le n^{\frac{2}{(\log \log n)^{1-c}}}$. (Constant K version)
-/
lemma exponent_bound_lemma_const (c : ℝ) (hc0 : 0 < c) (hc1 : c < 1) :
  ∃ N : ℕ, ∃ K : ℝ, ∀ n : ℕ, N ≤ n →
  ∀ m : ℝ, K ≤ m →
  m ≤ 2 * (n : ℝ) ^ ((Real.log (Real.log n)) ^ c) →
  m ^ (2.1 * Real.log 2 / Real.log (Real.log m)) ≤ (n : ℝ) ^ (2 / (Real.log (Real.log n)) ^ (1 - c)) := by
    obtain ⟨ N₁, hN₁ ⟩ := algebraic_bound_step1 c hc0 hc1;
    -- By `log_div_log_log_increasing`, let $X$ be such that for $x, y \ge X$ with $x \le y$, we have $\frac{\log x}{\log \log x} \le \frac{\log y}{\log \log y}$.
    obtain ⟨ X, hX₀, hX₁ ⟩ := log_div_log_log_increasing;
    refine' ⟨ N₁ + ⌈X⌉₊ + 1, X, fun n hn m hm₁ hm₂ => _ ⟩ ; norm_num at *;
    -- By `hN₁`, we have $\frac{\log m}{\log \log m} \le \frac{2}{2.1 \log 2} \frac{\log n}{(\log \log n)^{1-c}}$.
    have h_log_ratio : Real.log m / Real.log (Real.log m) ≤ (2 / (2.1 * Real.log 2)) * Real.log n / (Real.log (Real.log n)) ^ (1 - c) := by
      convert le_trans ( hX₁ m ( 2 * ( n : ℝ ) ^ ( Real.log ( Real.log n ) ) ^ c ) hm₁ hm₂ ) ( hN₁ n ( by linarith ) ) using 1 ; ring;
    rw [ Real.rpow_def_of_pos ( by linarith ), Real.rpow_def_of_pos ( by norm_cast; linarith ) ];
    convert Real.exp_le_exp.mpr ( mul_le_mul_of_nonneg_left h_log_ratio <| show 0 ≤ 21 / 10 * Real.log 2 by positivity ) using 1 ; ring_nf;
    ring_nf ; norm_num

/-
For sufficiently large $n$, if $j$ is large enough (greater than some constant $K$) and $j < k \le 2 n^{(\log \log n)^c}$, then $|A_k \cap A_j| \le n^{\frac{2}{(\log \log n)^{1-c}}}$.
-/
theorem intersection_bound_large (c : ℝ) (hc0 : 0 < c) (hc1 : c < 1) :
  ∃ N : ℕ, ∃ K : ℕ, ∀ n : ℕ, N ≤ n →
  let limit := 2 * (n : ℝ) ^ ((Real.log (Real.log n)) ^ c)
  let bound := (n : ℝ) ^ (2 / (Real.log (Real.log n)) ^ (1 - c))
  ∀ k j : ℕ, K ≤ j → j < k → (k : ℝ) ≤ limit →
  ((A k ∩ A j).card : ℝ) ≤ bound := by
    -- By `corollary_1_2`, there exists $n_0$ such that for $k > j > n_0$, $|A_k \cap A_j| < k^{\frac{2.1 \log 2}{\log \log k}}$.
    obtain ⟨n₀, hn₀⟩ : ∃ n₀ : ℕ, ∀ m n : ℕ, n₀ < n → n < m → ((A n ∩ A m).card : ℝ) < (m : ℝ) ^ (2.1 * Real.log 2 / Real.log (Real.log m)) := by
      have := @corollary_1_2 ( 0.1 : ℝ ) ; norm_num at * ; aesop;
    -- By `exponent_bound_lemma_const`, there exists $N_1, K_1$ such that for $n \ge N_1$ and $k \ge K_1$, if $k \le \text{limit}$, then $k^{\frac{2.1 \log 2}{\log \log k}} \le \text{bound}$.
    obtain ⟨N₁, K₁, hK₁⟩ : ∃ N₁ K₁ : ℕ, ∀ n ≥ N₁, ∀ k : ℕ, K₁ ≤ k → k ≤ 2 * (n : ℝ) ^ ((Real.log (Real.log n)) ^ c) → (k : ℝ) ^ (2.1 * Real.log 2 / Real.log (Real.log k)) ≤ (n : ℝ) ^ (2 / (Real.log (Real.log n)) ^ (1 - c)) := by
      have := exponent_bound_lemma_const c hc0 hc1;
      obtain ⟨ N, K, h ⟩ := this; exact ⟨ N, ⌈K⌉₊, fun n hn k hk₁ hk₂ => h n hn k ( Nat.le_of_ceil_le hk₁ ) hk₂ ⟩ ;
    refine' ⟨ N₁ + n₀ + K₁ + 1, n₀ + K₁ + 1, fun n hn k j hj₁ hj₂ hj₃ => _ ⟩;
    have := hn₀ k j ( by linarith ) ( by linarith );
    simpa only [ Finset.inter_comm ] using this.le.trans ( hK₁ n ( by linarith ) k ( by linarith ) hj₃ ) ;

/-
For sufficiently large $n$, if $j$ is small (less than $K$), then $|A_k \cap A_j| \le n^{\frac{2}{(\log \log n)^{1-c}}}$.
-/
lemma intersection_bound_small (c : ℝ) (K : ℝ) :
  ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
  let bound := (n : ℝ) ^ (2 / (Real.log (Real.log n)) ^ (1 - c))
  ∀ k j : ℕ, (j : ℝ) < K →
  ((A k ∩ A j).card : ℝ) ≤ bound := by
    -- From `bound_exists`, for large enough $n$, $j \le \text{bound}$.
    obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ j : ℕ, j < K → (j : ℝ) ≤ (n : ℝ) ^ (2 / (Real.log (Real.log n)) ^ (1 - c)) := by
      have := eventually_bound_gt_K c ( K + 1 );
      exact ⟨ this.choose, fun n hn j hj => by linarith [ this.choose_spec n hn ] ⟩;
    refine' ⟨ N, fun n hn k j hj => le_trans _ ( hN n hn j hj ) ⟩;
    refine' mod_cast le_trans ( Finset.card_le_card <| Finset.inter_subset_right ) _;
    exact le_trans ( Finset.card_image_le ) ( by simp +arith +decide )

/-
For sufficiently large $n$, if $k, j$ are distinct and bounded by $2 n^{(\log \log n)^c}$, then $|A_k \cap A_j| \le n^{\frac{2}{(\log \log n)^{1-c}}}$.
-/
theorem intersection_bound_asymptotic (c : ℝ) (hc0 : 0 < c) (hc1 : c < 1) :
  ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
  let limit := 2 * (n : ℝ) ^ ((Real.log (Real.log n)) ^ c)
  let bound := (n : ℝ) ^ (2 / (Real.log (Real.log n)) ^ (1 - c))
  ∀ k j : ℕ, k ≠ j → (k : ℝ) ≤ limit → (j : ℝ) ≤ limit →
  ((A k ∩ A j).card : ℝ) ≤ bound := by
    -- Obtain $N_1$ and $N_2$ from `intersection_bound_large` and `intersection_bound_small` respectively.
    obtain ⟨N₁, K₁, hN₁⟩ := intersection_bound_large c hc0 hc1
    obtain ⟨N₂, hN₂⟩ := intersection_bound_small c K₁;
    use Nat.max N₁ N₂ + K₁ + 1;
    intro n hn k j hk hk' hj';
    -- Without loss of generality, assume $j < k$.
    suffices h_wlog : ∀ k j : ℕ, k ≠ j → k ≤ 2 * (n : ℝ) ^ ((Real.log (Real.log n)) ^ c) → j ≤ 2 * (n : ℝ) ^ ((Real.log (Real.log n)) ^ c) → k > j → ((A k ∩ A j).card : ℝ) ≤ (n : ℝ) ^ (2 / (Real.log (Real.log n)) ^ (1 - c)) by
      cases lt_or_gt_of_ne hj' <;> [ exact fun hk hk' => by simpa only [ Finset.inter_comm ] using h_wlog _ _ ( Ne.symm hj' ) hk' hk ( by linarith ) ; ; exact fun hk hk' => h_wlog _ _ hj' hk hk' ( by linarith ) ] ;
    generalize_proofs at *; (
    exact fun k j hj hk hk' hjk => if hjk' : j < K₁ then hN₂ n ( by linarith [ Nat.le_max_left N₁ N₂, Nat.le_max_right N₁ N₂ ] ) k j ( mod_cast hjk' ) else hN₁ n ( by linarith [ Nat.le_max_left N₁ N₂, Nat.le_max_right N₁ N₂ ] ) k j ( by linarith ) hjk hk)

/-
If a family of sets has large size (at least R) and small pairwise intersections (at most K < R), then the sets are distinct.
-/
lemma distinct_sets_of_large_gap {α : Type*} [DecidableEq α] (U : Finset ℕ) (F : ℕ → Finset α) (R K : ℕ)
  (hR : R > K)
  (h_size : ∀ k ∈ U, (F k).card ≥ R)
  (h_inter : ∀ k j, k ∈ U → j ∈ U → k ≠ j → (F k ∩ F j).card ≤ K) :
  ∀ k j, k ∈ U → j ∈ U → k ≠ j → F k ≠ F j := by
    grind

/-
For large $n$, $R \le mk$.
-/
lemma R_le_mk (c : ℝ) (hc0 : 0 < c) (hc1 : c < 1) :
  ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
  let L := Real.log (Real.log n)
  let R := 0.5 * (n : ℝ) ^ (2/3 - 2 / L)
  let k := (n : ℝ) ^ (2 / L ^ (1 - c))
  let m := 0.5 * (n : ℝ)
  R ≤ m * k := by
    -- By simplifying the exponents, we can see that for sufficiently large $n$, the inequality holds.
    have h_exp : ∃ N : ℕ, ∀ n ≥ N, (2 / 3 - 2 / Real.log (Real.log n)) ≤ 1 + 2 / Real.log (Real.log n) ^ (1 - c) := by
      refine' ⟨ 3, fun n hn => _ ⟩ ; ring_nf;
      exact le_add_of_le_of_nonneg ( by linarith [ inv_nonneg.2 ( Real.log_nonneg ( show 1 ≤ Real.log n by rw [ Real.le_log_iff_exp_le ( by positivity ) ] ; exact Real.exp_one_lt_d9.le.trans ( by norm_num; linarith [ show ( n:ℝ ) ≥ 3 by norm_cast ] ) ) ) ] ) ( by exact mul_nonneg ( inv_nonneg.2 ( Real.rpow_nonneg ( Real.log_nonneg ( show 1 ≤ Real.log n by rw [ Real.le_log_iff_exp_le ( by positivity ) ] ; exact Real.exp_one_lt_d9.le.trans ( by norm_num; linarith [ show ( n:ℝ ) ≥ 3 by norm_cast ] ) ) ) _ ) ) zero_le_two );
    field_simp;
    obtain ⟨ N, hN ⟩ := h_exp; use N + 3; intro n hn; specialize hN n ( by linarith ) ; rw [ ← Real.rpow_one_add' ] <;> norm_num at *;
    · exact Real.rpow_le_rpow_of_exponent_le ( by norm_cast; linarith ) ( by ring_nf at *; linarith );
    · exact ne_of_gt ( add_pos_of_pos_of_nonneg zero_lt_one ( div_nonneg zero_le_two ( Real.rpow_nonneg ( Real.log_nonneg ( show 1 ≤ Real.log n by rw [ Real.le_log_iff_exp_le ( by norm_cast; linarith ) ] ; exact Real.exp_one_lt_d9.le.trans ( by norm_num; linarith [ show ( n : ℝ ) ≥ 3 by norm_cast; linarith ] ) ) ) _ ) ) )

/-
For large $n$, $R^2 / (2k) \ge \text{bound}$.
-/
lemma algebraic_bound_simplified (c : ℝ) (hc0 : 0 < c) (hc1 : c < 1) :
  ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
  let L := Real.log (Real.log n)
  let R := 0.5 * (n : ℝ) ^ (2/3 - 2 / L)
  let k := (n : ℝ) ^ (2 / L ^ (1 - c))
  let bound := (n : ℝ) ^ (4/3 - 3 / L ^ (1 - c))
  R^2 / (2 * k) ≥ bound := by
    -- We want to show $0.125 n^{4/3 - 4/L - 2/L^{1-c}} \ge n^{4/3 - 3/L^{1-c}}$.
    suffices h_suff : ∃ N : ℕ, ∀ n : ℕ, N ≤ n → (0.125 : ℝ) * (n : ℝ) ^ (4 / 3 - 4 / Real.log (Real.log n) - 2 / (Real.log (Real.log n)) ^ (1 - c)) ≥ (n : ℝ) ^ (4 / 3 - 3 / (Real.log (Real.log n)) ^ (1 - c)) by
      obtain ⟨ N, hN ⟩ := h_suff; use N; intros n hn; convert hN n hn using 1; ring_nf;
      by_cases hn' : n = 0 <;> norm_num [ hn', Real.rpow_def_of_pos ] ; ring_nf;
      · norm_num [ show 1 - c ≠ 0 by linarith ];
      · rw [ ← Real.rpow_natCast, ← Real.rpow_mul ( by positivity ) ] ; rw [ ← Real.rpow_neg ( by positivity ) ] ; rw [ ← Real.rpow_add ( by positivity ) ] ; ring_nf;
    -- Dividing by $n^{4/3 - 3/L^{1-c}}$, we need $0.125 n^{1/L^{1-c} - 4/L} \ge 1$.
    suffices h_suff' : ∃ N : ℕ, ∀ n : ℕ, N ≤ n → (0.125 : ℝ) * (n : ℝ) ^ (1 / (Real.log (Real.log n)) ^ (1 - c) - 4 / Real.log (Real.log n)) ≥ 1 by
      field_simp;
      obtain ⟨ N, hN ⟩ := h_suff'; use N + 3; intros n hn; convert mul_le_mul_of_nonneg_left ( hN n ( by linarith ) ) ( Real.rpow_nonneg ( Nat.cast_nonneg n ) ( ( 4 - 3 ^ 2 / Real.log ( Real.log n ) ^ ( 1 - c ) ) / 3 ) ) using 1 ; ring;
      rw [ mul_left_comm, ← Real.rpow_add ( by norm_cast; linarith ) ] ; ring_nf;
    -- Taking logs: $\log 0.125 + (1/L^{1-c} - 4/L) \log n \ge 0$.
    suffices h_log : Filter.Tendsto (fun n : ℕ => Real.log 0.125 + (1 / (Real.log (Real.log n)) ^ (1 - c) - 4 / Real.log (Real.log n)) * Real.log n) Filter.atTop Filter.atTop by
      have := h_log.eventually_gt_atTop 0;
      rw [ Filter.eventually_atTop ] at this; rcases this with ⟨ N, hN ⟩ ; use N + 2; intros n hn; specialize hN n ( by linarith ) ; rw [ Real.rpow_def_of_pos ( by norm_cast; linarith ) ] ; ring_nf at *; norm_num at *;
      rw [ ← Real.log_le_log_iff ( by positivity ) ( by positivity ), Real.log_mul ( by positivity ) ( by positivity ), Real.log_exp ] ; norm_num at * ; linarith;
    -- We'll use that $\frac{\log n}{L^{1-c}} \to \infty$ and $\frac{4 \log n}{L} \to 0$ as $n \to \infty$.
    have h_lim : Filter.Tendsto (fun n : ℕ => (Real.log n) / (Real.log (Real.log n)) ^ (1 - c)) Filter.atTop Filter.atTop ∧ Filter.Tendsto (fun n : ℕ => (4 * Real.log n) / Real.log (Real.log n)) Filter.atTop Filter.atTop := by
      constructor;
      · -- Let $y = \log \log n$, so we can rewrite the limit as $\lim_{y \to \infty} \frac{e^y}{y^{1-c}}$.
        suffices h_log_log : Filter.Tendsto (fun y : ℝ => Real.exp y / y ^ (1 - c)) Filter.atTop Filter.atTop by
          have h_log_log : Filter.Tendsto (fun n : ℕ => Real.exp (Real.log (Real.log n)) / (Real.log (Real.log n)) ^ (1 - c)) Filter.atTop Filter.atTop := by
            exact h_log_log.comp ( Real.tendsto_log_atTop.comp ( Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop ) );
          refine h_log_log.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 1 ] with n hn; rw [ Real.exp_log ( Real.log_pos ( Nat.one_lt_cast.mpr hn ) ) ] );
        exact tendsto_exp_div_rpow_atTop (1 - c);
      · -- We can use the change of variables $u = \log n$ to transform the limit expression.
        suffices h_log : Filter.Tendsto (fun u : ℝ => 4 * u / Real.log u) Filter.atTop Filter.atTop by
          exact h_log.comp ( Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop );
        -- We can use the change of variables $v = \log u$ to transform the limit expression.
        suffices h_log : Filter.Tendsto (fun v : ℝ => 4 * Real.exp v / v) Filter.atTop Filter.atTop by
          have := h_log.comp Real.tendsto_log_atTop;
          exact this.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with x hx using by rw [ Function.comp_apply, Real.exp_log hx ] );
        simpa [ mul_div_assoc ] using Filter.Tendsto.const_mul_atTop ( by norm_num ) ( Real.tendsto_exp_div_pow_atTop 1 );
    norm_num [ sub_mul, div_eq_mul_inv ] at *;
    have h_lim : Filter.Tendsto (fun n : ℕ => (Real.log (Real.log n) ^ (1 - c))⁻¹ * Real.log n - 4 * (Real.log (Real.log n))⁻¹ * Real.log n) Filter.atTop Filter.atTop := by
      have h_lim : Filter.Tendsto (fun n : ℕ => (Real.log (Real.log n) ^ (1 - c))⁻¹ * Real.log n * (1 - 4 * (Real.log (Real.log n))⁻¹ * Real.log n / ((Real.log (Real.log n) ^ (1 - c))⁻¹ * Real.log n))) Filter.atTop Filter.atTop := by
        have h_lim : Filter.Tendsto (fun n : ℕ => (Real.log (Real.log n) ^ (1 - c))⁻¹ * Real.log n) Filter.atTop Filter.atTop ∧ Filter.Tendsto (fun n : ℕ => 4 * (Real.log (Real.log n))⁻¹ * Real.log n / ((Real.log (Real.log n) ^ (1 - c))⁻¹ * Real.log n)) Filter.atTop (nhds 0) := by
          have h_lim : Filter.Tendsto (fun n : ℕ => 4 * (Real.log (Real.log n))⁻¹ / (Real.log (Real.log n) ^ (1 - c))⁻¹) Filter.atTop (nhds 0) := by
            have h_lim : Filter.Tendsto (fun n : ℕ => (Real.log (Real.log n))⁻¹ * (Real.log (Real.log n) ^ (1 - c))) Filter.atTop (nhds 0) := by
              have h_lim : Filter.Tendsto (fun n : ℕ => (Real.log (Real.log n)) ^ (1 - c - 1)) Filter.atTop (nhds 0) := by
                simpa using tendsto_rpow_neg_atTop ( by linarith : 0 < - ( 1 - c - 1 ) ) |> Filter.Tendsto.comp <| Real.tendsto_log_atTop.comp <| Real.tendsto_log_atTop.comp <| tendsto_natCast_atTop_atTop;
              refine h_lim.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 2 ] with n hn; rw [ ← Real.rpow_neg_one, ← Real.rpow_add ( Real.log_pos <| show 1 < Real.log n from by rw [ Real.lt_log_iff_exp_lt <| by positivity ] ; exact Real.exp_one_lt_d9.trans_le <| by norm_num; linarith [ show ( n : ℝ ) ≥ 3 by norm_cast ] ) ] ; ring_nf );
            convert h_lim.const_mul 4 using 2 <;> ring_nf;
            norm_num;
          exact ⟨ by simpa only [ mul_comm ] using ‹Filter.Tendsto ( fun n : ℕ => Real.log n * ( Real.log ( Real.log n ) ^ ( 1 - c ) ) ⁻¹ ) Filter.atTop Filter.atTop ∧ Filter.Tendsto ( fun n : ℕ => 4 * Real.log n * ( Real.log ( Real.log n ) ) ⁻¹ ) Filter.atTop Filter.atTop›.1, h_lim.congr' <| by filter_upwards [ Filter.eventually_gt_atTop 1 ] with n hn; rw [ mul_div_mul_right _ _ <| ne_of_gt <| Real.log_pos <| Nat.one_lt_cast.mpr hn ] ⟩;
        apply Filter.Tendsto.atTop_mul_pos;
        exacts [ zero_lt_one, h_lim.1, by simpa using h_lim.2.const_sub 1 ];
      refine h_lim.congr' ?_;
      filter_upwards [ Filter.eventually_gt_atTop 1, ‹Filter.Tendsto ( fun n : ℕ => Real.log ↑n * ( Real.log ( Real.log ↑n ) ^ ( 1 - c ) ) ⁻¹ ) Filter.atTop Filter.atTop ∧ Filter.Tendsto ( fun n : ℕ => 4 * Real.log ↑n * ( Real.log ( Real.log ↑n ) ) ⁻¹ ) Filter.atTop Filter.atTop›.1.eventually_gt_atTop 0 ] with n hn hn' using by rw [ mul_sub, mul_one, mul_div_cancel₀ _ ( by linarith ) ] ;
    exact Filter.Tendsto.add_atTop tendsto_const_nhds h_lim

/-
For large $n$, $K < R$.
-/
lemma R_gt_K (c : ℝ) (hc1 : c < 1) :
  ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
  let L := Real.log (Real.log n)
  let R := 0.5 * (n : ℝ) ^ (2/3 - 2 / L)
  let K := (n : ℝ) ^ (2 / L ^ (1 - c))
  K < R := by
    -- We want $n^{2/L^{1-c}} < 0.5 n^{2/3 - 2/L}$.
    -- Taking logs: $\frac{2 \log n}{L^{1-c}} < \log 0.5 + (2/3 - 2/L) \log n$.
    -- Dividing by $\log n$: $\frac{2}{L^{1-c}} < \frac{\log 0.5}{\log n} + 2/3 - 2/L$.
    have h_bound : ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        let L := Real.log (Real.log n)
        (2 / L ^ (1 - c)) < (Real.log 0.5) / Real.log n + 2 / 3 - 2 / L := by
          -- As $n \to \infty$, $L \to \infty$ and $L^{1-c} \to \infty$, so the left-hand side tends to $0$.
          have h_lhs_zero : Filter.Tendsto (fun n : ℕ => 2 / (Real.log (Real.log n)) ^ (1 - c)) Filter.atTop (nhds 0) := by
            exact tendsto_const_nhds.div_atTop ( tendsto_rpow_atTop ( by linarith ) |> Filter.Tendsto.comp <| Real.tendsto_log_atTop.comp <| Real.tendsto_log_atTop.comp <| tendsto_natCast_atTop_atTop );
          -- As $n \to \infty$, $\frac{\log 0.5}{\log n} \to 0$ and $\frac{2}{L} \to 0$, so the right-hand side tends to $2/3$.
          have h_rhs_three_quarters : Filter.Tendsto (fun n : ℕ => (Real.log 0.5) / Real.log n + 2 / 3 - 2 / Real.log (Real.log n)) Filter.atTop (nhds (2 / 3)) := by
            exact le_trans ( Filter.Tendsto.sub ( Filter.Tendsto.add ( tendsto_const_nhds.div_atTop <| Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop ) tendsto_const_nhds ) <| tendsto_const_nhds.div_atTop <| Real.tendsto_log_atTop.comp <| Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop ) <| by norm_num;
          exact Filter.eventually_atTop.mp ( h_lhs_zero.eventually ( gt_mem_nhds <| show 0 < 2 / 3 - 2 / 3 / 2 by norm_num ) ) |> fun ⟨ N, hN ⟩ ↦ Filter.eventually_atTop.mp ( h_rhs_three_quarters.eventually ( lt_mem_nhds <| show 2 / 3 - 2 / 3 / 2 < 2 / 3 by norm_num ) ) |> fun ⟨ M, hM ⟩ ↦ ⟨ Max.max N M, fun n hn ↦ by linarith [ hN n ( le_trans ( le_max_left _ _ ) hn ), hM n ( le_trans ( le_max_right _ _ ) hn ) ] ⟩;
    obtain ⟨ N, hN ⟩ := h_bound; use N + 2; intro n hn; specialize hN n ( by linarith ) ; norm_num [ Real.rpow_def_of_pos ] at *;
    rw [ ← Real.log_lt_log_iff ( by exact Real.rpow_pos_of_pos ( Nat.cast_pos.mpr <| by linarith ) _ ) ( by exact mul_pos ( by norm_num ) <| Real.rpow_pos_of_pos ( Nat.cast_pos.mpr <| by linarith ) _ ), Real.log_mul ( by norm_num ) ( by exact ne_of_gt <| Real.rpow_pos_of_pos ( Nat.cast_pos.mpr <| by linarith ) _ ), Real.log_rpow ] <;> norm_num at *;
    · rw [ Real.log_rpow ( by norm_cast; linarith ) ];
      convert mul_lt_mul_of_pos_right hN ( Real.log_pos <| show ( n : ℝ ) > 1 by norm_cast; linarith ) using 1 ; ring_nf;
      norm_num [ show Real.log n ≠ 0 by exact ne_of_gt <| Real.log_pos <| by norm_cast; linarith ];
    · linarith

/-
If we have a large family of large sets with small intersections, their union is large.
-/
lemma final_combination (n : ℕ) (U : Finset ℕ) (C : ℕ → Finset ℕ) (R K : ℕ) (bound : ℝ)
  (hU : (U.card : ℝ) ≥ 0.5 * n)
  (hR : ∀ k ∈ U, (C k).card ≥ R)
  (hK : ∀ k j, k ∈ U → j ∈ U → k ≠ j → (C k ∩ C j).card ≤ K)
  (hRK : K < R)
  (h_alg : (0.5 * n) * (R : ℝ)^2 / (R + (0.5 * n) * K) ≥ bound) :
  ((U.biUnion C).card : ℝ) ≥ bound := by
    -- By `distinct_sets_of_large_gap`, the map $C$ is injective on $U$, so $|E| = |U|$. Let $m = |E|$.
    have h_distinct : ∀ k j, k ∈ U → j ∈ U → k ≠ j → C k ≠ C j := by
      exact fun k j a a_1 a_2 => distinct_sets_of_large_gap U C R K hRK hR hK k j a a_1 a_2
    have h_card_E : (Finset.biUnion U C).card * (R + (Finset.card U - 1) * K) ≥ Finset.card U * R^2 := by
      -- Apply the hypergraph bound lemma with the set E = U.image C, m = U.card, R, and K.
      have h_hypergraph : ∀ (E : Finset (Finset ℕ)), (∀ e ∈ E, R ≤ e.card) → (∀ e1 ∈ E, ∀ e2 ∈ E, e1 ≠ e2 → (e1 ∩ e2).card ≤ K) → (E.biUnion id).card * (R + (E.card - 1) * K) ≥ E.card * R^2 := by
        exact fun E a a_1 => hypergraph_bound E E.card R K rfl a a_1;
      specialize h_hypergraph (U.image C) (by
      aesop_cat;) (by
      rintro _ he1 _ he2 hne; obtain ⟨ k, hk, rfl ⟩ := Finset.mem_image.mp he1; obtain ⟨ j, hj, rfl ⟩ := Finset.mem_image.mp he2; aesop;);
      convert h_hypergraph using 1 <;> norm_num [ Finset.card_image_of_injOn fun x hx y hy hxy => not_imp_not.mp ( h_distinct x y hx hy ) hxy ];
      exact Or.inl ( congr_arg Finset.card ( by ext; aesop ) )
    have h_card_E_ge : (Finset.biUnion U C).card ≥ (Finset.card U : ℝ) * R^2 / (R + (Finset.card U - 1) * K) := by
      rcases U with ⟨ ⟨ k, hk ⟩ ⟩ <;> norm_num at *;
      rw [ div_le_iff₀ ] <;> norm_cast at * ; nlinarith
    have h_card_E_ge_final : (Finset.biUnion U C).card ≥ (Finset.card U : ℝ) * R^2 / (R + Finset.card U * K) := by
      exact le_trans ( div_le_div_of_nonneg_left ( by positivity ) ( by nlinarith [ show ( R : ℝ ) > K by norm_cast ] ) ( by nlinarith [ show ( R : ℝ ) > K by norm_cast ] ) ) h_card_E_ge
    have h_card_E_ge_final_bound : (Finset.biUnion U C).card ≥ (0.5 * n : ℝ) * R^2 / (R + (0.5 * n : ℝ) * K) := by
      refine le_trans ?_ h_card_E_ge_final;
      rw [ div_le_div_iff₀ ] <;> try norm_num ; nlinarith [ ( by norm_cast : ( K :ℝ ) < R ) ] ;
      nlinarith [ ( by positivity : 0 ≤ ( R : ℝ ) ^ 2 * K ), ( by positivity : 0 ≤ ( R : ℝ ) ^ 2 * n ), ( by positivity : 0 ≤ ( R : ℝ ) ^ 2 * U.card ), ( by positivity : 0 ≤ ( K : ℝ ) * n ), ( by positivity : 0 ≤ ( K : ℝ ) * U.card ), ( by positivity : 0 ≤ ( n : ℝ ) * U.card ), mul_le_mul_of_nonneg_left hU <| show 0 ≤ ( R : ℝ ) ^ 2 by positivity ]
    have h_final : (Finset.biUnion U C).card ≥ bound := by
      exact h_alg.trans h_card_E_ge_final_bound
    exact h_final

/-
The map from T_parity to the intersection followed by the map back to T_parity is the identity.
-/
lemma T_parity_map_inverse (m n : ℕ) (hmn : n < m) (p : ℕ × ℕ) (hp : p ∈ T_parity m n) :
  intersection_to_T_parity_map m n (T_parity_map m n p) (T_parity_map_mem_intersection m n hmn p hp) = p := by
    -- Let's unfold the definitions of `intersection_to_T_parity_map` and `T_parity_map`.
    unfold intersection_to_T_parity_map T_parity_map
    generalize_proofs at *;
    -- By definition of `from_T_pair`, we know that `get_k n (k * (n - k)) = k` and `get_r m (k * (n - k)) = r`.
    have h_get_k : get_k n ((from_T_pair m n p.1 p.2).1 * (n - (from_T_pair m n p.1 p.2).1)) ‹_› = (from_T_pair m n p.1 p.2).1 := by
      unfold get_k
      generalize_proofs at *;
      have := solution_from_parity m n p.1 p.2 hmn (Finset.mem_filter.mp hp |>.1) (Finset.mem_filter.mp hp |>.2);
      exact Classical.choose_spec ‹∃ x, ( fun k => 2 * k ≤ n ∧ k * ( n - k ) = ( from_T_pair m n p.1 p.2 ).1 * ( n - ( from_T_pair m n p.1 p.2 ).1 ) ) x ∧ ∀ y, 2 * y ≤ n ∧ y * ( n - y ) = ( from_T_pair m n p.1 p.2 ).1 * ( n - ( from_T_pair m n p.1 p.2 ).1 ) → y = x› |>.2 _ ⟨ this.2.1, rfl ⟩ ▸ rfl
    have h_get_r : get_r m ((from_T_pair m n p.1 p.2).1 * (n - (from_T_pair m n p.1 p.2).1)) ‹_› = (from_T_pair m n p.1 p.2).2 := by
      unfold get_r
      generalize_proofs at *; (
      have := solution_from_parity m n p.1 p.2 hmn (Finset.mem_filter.mp hp).1 (Finset.mem_filter.mp hp).2
      generalize_proofs at *; (
      exact Classical.choose_spec ‹∃ x, ( fun k => 2 * k ≤ m ∧ k * ( m - k ) = ( from_T_pair m n p.1 p.2 ).1 * ( n - ( from_T_pair m n p.1 p.2 ).1 ) ) x ∧ ∀ y, 2 * y ≤ m ∧ y * ( m - y ) = ( from_T_pair m n p.1 p.2 ).1 * ( n - ( from_T_pair m n p.1 p.2 ).1 ) → y = x› |>.2 _ ⟨ this.2.2.1, this.1.symm ⟩ ▸ rfl))
    generalize_proofs at *;
    convert from_T_pair_inverse m n p.1 p.2 _ _ _ using 1
    all_goals generalize_proofs at *;
    · congr! 1
    · linarith;
    · exact Finset.mem_of_mem_filter (p.1, p.2) hp;
    · exact Finset.mem_filter.mp hp |>.2

/-
get_k returns a valid k such that 2k <= n and k(n-k) = x.
-/
lemma get_k_prop (n x : ℕ) (hx : x ∈ A n) :
  2 * (get_k n x hx) ≤ n ∧ (get_k n x hx) * (n - (get_k n x hx)) = x := by
    exact Classical.choose_spec ( unique_k_for_val n x hx ) |>.1 |> fun h => ⟨ h.1, h.2 ⟩

/-
get_k returns a positive integer.
-/
lemma get_k_pos (n x : ℕ) (hx : x ∈ A n) :
  0 < get_k n x hx := by
    -- From `get_k_prop`, we have `k * (n - k) = x`.
    -- Since `x ∈ A n`, `x` is in the image of `(0, n)` under `r ↦ r(n-r)`.
    -- For `r ∈ (0, n)`, `r(n-r) > 0`. So `x > 0`.
    -- Since `k * (n - k) = x > 0`, we must have `k > 0`.
    have h_pos : 0 < x := by
      unfold A at hx; aesop;
    have := get_k_prop n x hx; nlinarith [ Nat.sub_add_cancel ( show ( get_k n x hx ) ≤ n from by linarith ) ] ;

/-
get_r returns a valid r such that 2r <= m and r(m-r) = x.
-/
lemma get_r_prop (m x : ℕ) (hx : x ∈ A m) :
  2 * (get_r m x hx) ≤ m ∧ (get_r m x hx) * (m - (get_r m x hx)) = x := by
    exact Classical.choose_spec ( unique_k_for_val m x hx ) |>.1 |> fun h => ⟨ h.1, h.2 ⟩

/-
get_r returns a positive integer.
-/
lemma get_r_pos (m x : ℕ) (hx : x ∈ A m) :
  0 < get_r m x hx := by
    by_contra h_negop;
    -- Since `x ∈ A m`, `x` is in the image of `(0, m)` under `r ↦ r(m-r)`.
    -- For `r ∈ (0, m)`, `r(m-r) > 0`. So `x > 0`.
    have hx_pos : 0 < x := by
      obtain ⟨ y, hy, rfl ⟩ := Finset.mem_image.mp hx; aesop;
    have := get_r_prop m x hx; aesop;

/-
The values k and r obtained from x satisfy the solution conditions.
-/
lemma get_k_r_properties (m n : ℕ) (x : ℕ) (hx : x ∈ A n ∩ A m) :
  let k := get_k n x (Finset.mem_of_mem_inter_left hx)
  let r := get_r m x (Finset.mem_of_mem_inter_right hx)
  2 * k ≤ n ∧ 2 * r ≤ m ∧ k * (n - k) = r * (m - r) ∧ 0 < k ∧ 0 < r := by
    exact ⟨ get_k_prop n x ( Finset.mem_of_mem_inter_left hx ) |>.1, get_r_prop m x ( Finset.mem_of_mem_inter_right hx ) |>.1, by linarith [ get_k_prop n x ( Finset.mem_of_mem_inter_left hx ) |>.2, get_r_prop m x ( Finset.mem_of_mem_inter_right hx ) |>.2 ], get_k_pos n x ( Finset.mem_of_mem_inter_left hx ), get_r_pos m x ( Finset.mem_of_mem_inter_right hx ) ⟩

/-
The map from intersection to T_parity followed by the map back to intersection is the identity.
-/
lemma intersection_to_T_parity_map_inverse (m n : ℕ) (hmn : n < m) (x : ℕ) (hx : x ∈ A n ∩ A m) :
  T_parity_map m n (intersection_to_T_parity_map m n x hx) = x := by
    -- By definition of `from_T_pair` and `to_T_pair'`, we know that `from_T_pair m n (to_T_pair' m n k r) = (k, r)`.
    have h_from_to : from_T_pair m n (to_T_pair' m n (get_k n x (Finset.mem_of_mem_inter_left hx)) (get_r m x (Finset.mem_of_mem_inter_right hx))).1 (to_T_pair' m n (get_k n x (Finset.mem_of_mem_inter_left hx)) (get_r m x (Finset.mem_of_mem_inter_right hx))).2 = (get_k n x (Finset.mem_of_mem_inter_left hx), get_r m x (Finset.mem_of_mem_inter_right hx)) := by
      apply to_T_pair_inverse_left;
      · exact hmn;
      · exact get_k_prop n x ( Finset.mem_of_mem_inter_left hx ) |>.1;
      · exact get_r_prop m x ( Finset.mem_of_mem_inter_right hx ) |>.1;
      · rw [ get_k_prop _ _ ( Finset.mem_of_mem_inter_left hx ) |>.2, get_r_prop _ _ ( Finset.mem_of_mem_inter_right hx ) |>.2 ];
      · exact get_k_pos n x (Finset.mem_of_mem_inter_left hx);
    convert congr_arg ( fun p : ℕ × ℕ => p.1 * ( n - p.1 ) ) h_from_to using 1;
    exact Eq.symm ( get_k_prop n x ( Finset.mem_of_mem_inter_left hx ) |>.2 )

/-
The cardinality of the intersection of A_n and A_m is equal to the cardinality of T_parity, provided m and n are odd.
-/
theorem card_intersection_eq_card_T_parity (m n : ℕ) (hmn : n < m) :
  (A n ∩ A m).card = (T_parity m n).card := by
    have h_bij : Finset.card (Finset.image (fun p => T_parity_map m n p) (T_parity m n)) = Finset.card (T_parity m n) := by
      rw [ Finset.card_image_of_injOn ];
      intro p hp q hq h_eq; have := T_parity_map_inverse m n hmn p hp; have := T_parity_map_inverse m n hmn q hq; aesop;
    rw [ ← h_bij, show ( Finset.image ( fun p => T_parity_map m n p ) ( T_parity m n ) ) = A n ∩ A m from ?_ ];
    ext x;
    simp +zetaDelta at *;
    constructor;
    · rintro ⟨ a, b, h, rfl ⟩;
      have := T_parity_map_mem_intersection m n hmn ( a, b ) h; aesop;
    · intro hx;
      use (intersection_to_T_parity_map m n x (by
      exact Finset.mem_inter.mpr hx)).1, (intersection_to_T_parity_map m n x (by
      exact Finset.mem_inter.mpr hx)).2
      generalize_proofs at *;
      exact ⟨ intersection_to_T_parity_map_mem m n hmn x ‹_›, intersection_to_T_parity_map_inverse m n hmn x ‹_› ⟩

/-
For the constructed m and n, the size of the intersection of A_n and A_m is exactly s.
-/
theorem theorem_1_3_lemma (s : ℕ) (hs : 0 < s) (p : ℕ) (hp : p.Prime) (hp_ge_3 : 3 ≤ p) (α : ℕ) (hα : 1 ≤ α) (h_pow : p^s < 2^α) :
  let (m, n) := construction_1_3 s p α
  (A n ∩ A m).card = s := by
    -- By definition of $A_n$ and $A_m$, we have $(A_n \cap A_m).card = (T_parity m n).card$.
    have h_card_eq : (A (construction_1_3 s p α).2 ∩ A (construction_1_3 s p α).1).card = (T_parity (construction_1_3 s p α).1 (construction_1_3 s p α).2).card := by
      apply card_intersection_eq_card_T_parity;
      · exact Nat.sub_lt ( by positivity ) ( by positivity );
    convert h_card_eq using 1;
    convert card_construction_pairs s p α ( by linarith ) |> Eq.symm using 1;
    convert congr_arg Finset.card ( construction_pairs_eq_T_parity s p α hs hp hp_ge_3 hα h_pow |> Eq.symm ) using 1

/-
Definitions for the sequences n_k and m_k for Theorem 1.3.
-/
noncomputable def seq_p (k : ℕ) : ℕ := Nat.nth Nat.Prime (k + 1)

noncomputable def seq_alpha (s k : ℕ) : ℕ := s * (seq_p k) + 1

noncomputable def seq_m (s k : ℕ) : ℕ := 2^(seq_alpha s k) * (seq_p k)^s + 1

noncomputable def seq_n (s k : ℕ) : ℕ := seq_m s k - 2

/-
Theorem 1.3: For every s, there exists an infinite sequence of pairs (n_k, m_k) such that |A_{n_k} \cap A_{m_k}| = s.
-/
theorem theorem_1_3 (s : ℕ) (hs : 0 < s) :
  ∃ n_seq m_seq : ℕ → ℕ,
    (∀ k, n_seq k < m_seq k) ∧
    (∀ k, m_seq k < n_seq (k + 1)) ∧
    (∀ k, (A (n_seq k) ∩ A (m_seq k)).card = s) := by
      refine' ⟨ fun k => seq_n s k, fun k => seq_m s k, _, _, _ ⟩ <;> intro k <;> simp +decide
      · exact Nat.sub_lt ( Nat.succ_pos _ ) ( by positivity );
      · -- Since $p_{k+1} > p_k$, we have $p_{k+1}^s > p_k^s$ and $2^{s p_{k+1} + 1} > 2^{s p_k + 1}$.
        have h_exp : 2^(s * Nat.nth Nat.Prime (k + 2) + 1) > 2^(s * Nat.nth Nat.Prime (k + 1) + 1) ∧ Nat.nth Nat.Prime (k + 2)^s > Nat.nth Nat.Prime (k + 1)^s := by
          exact ⟨ pow_lt_pow_right₀ ( by decide ) ( by nlinarith [ Nat.Prime.one_lt ( Nat.prime_nth_prime ( k + 1 ) ), Nat.Prime.one_lt ( Nat.prime_nth_prime ( k + 2 ) ), Nat.nth_strictMono ( Nat.infinite_setOf_prime ) ( by linarith : k + 1 < k + 2 ) ] ), pow_lt_pow_left₀ ( Nat.nth_strictMono ( Nat.infinite_setOf_prime ) ( by linarith ) ) ( Nat.zero_le _ ) ( by linarith ) ⟩;
        unfold seq_m seq_n; simp +decide [ *, Nat.pow_succ' ] at *;
        unfold seq_alpha seq_p seq_m; simp +decide [ *, Nat.pow_succ' ] at * ;
        unfold seq_alpha seq_p; simp +decide [ *, Nat.pow_succ' ] at * ;
        exact lt_tsub_iff_left.mpr ( by nlinarith [ Nat.Prime.two_le ( Nat.prime_nth_prime ( k + 1 ) ), Nat.Prime.two_le ( Nat.prime_nth_prime ( k + 2 ) ), pow_pos ( Nat.Prime.pos ( Nat.prime_nth_prime ( k + 1 ) ) ) s, pow_pos ( Nat.Prime.pos ( Nat.prime_nth_prime ( k + 2 ) ) ) s, pow_pos ( zero_lt_two' ℕ ) ( s * Nat.nth Nat.Prime ( k + 1 ) ), pow_pos ( zero_lt_two' ℕ ) ( s * Nat.nth Nat.Prime ( k + 2 ) ) ] );
      · convert theorem_1_3_lemma s hs ( seq_p k ) ( Nat.prime_nth_prime ( k + 1 ) ) ?_ ( seq_alpha s k ) ?_ ?_ using 1;
        · exact Nat.succ_le_of_lt ( Nat.lt_of_le_of_lt ( Nat.Prime.two_le ( Nat.prime_nth_prime 0 ) ) ( Nat.nth_strictMono ( Nat.infinite_setOf_prime ) ( Nat.succ_pos _ ) ) );
        · exact Nat.succ_pos _;
        · -- By definition of $seq_p$ and $seq_alpha$, we have $seq_p k \geq 3$ and $seq_alpha s k = s * seq_p k + 1$.
          have h_seq_p_ge_3 : 3 ≤ seq_p k := by
            exact Nat.succ_le_of_lt ( Nat.lt_of_le_of_lt ( Nat.Prime.two_le ( Nat.prime_nth_prime 0 ) ) ( Nat.nth_strictMono ( Nat.infinite_setOf_prime ) ( Nat.succ_pos _ ) ) )
          have h_seq_alpha_ge_4 : seq_alpha s k ≥ 4 := by
            exact Nat.succ_le_succ ( Nat.mul_le_mul hs h_seq_p_ge_3 );
          rw [ show seq_alpha s k = s * seq_p k + 1 by rfl, pow_add, pow_mul' ];
          -- By induction on $p$, we can show that $p < 2^p$ for all $p \geq 3$.
          have h_ind : ∀ p ≥ 3, p < 2^p := by
            exact fun p hp => by induction hp <;> norm_num [ Nat.pow_succ ] at * ; linarith;
          exact lt_of_le_of_lt ( Nat.pow_le_pow_left ( le_of_lt ( h_ind _ h_seq_p_ge_3 ) ) _ ) ( lt_mul_of_one_lt_right ( by positivity ) ( by norm_num ) )

/-
For large n, 1/L^(1-c) - 4/L is positive.
-/
lemma exponent_gap_pos (c : ℝ) (hc0 : 0 < c) (hc1 : c < 1) :
  ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
  let L := Real.log (Real.log n)
  1 / L^(1 - c) - 4 / L > 0 := by
    -- We want $1/L^{1-c} > 4/L$.
    -- Multiply by $L$: $L^c > 4$.
    suffices hL_gt_4 : ∃ N : ℕ, ∀ n : ℕ, N ≤ n → (Real.log (Real.log n)) ^ c > 4 by
      obtain ⟨ N, hN ⟩ := hL_gt_4; use N + 3; intros n hn; rw [ gt_iff_lt ] ; rw [ div_sub_div, lt_div_iff₀ ] <;> norm_num;
      · have := hN n ( by linarith );
        rw [ show ( 1 - c ) = 1 - c by ring, Real.rpow_sub' ] <;> norm_num;
        · rw [ div_mul_eq_mul_div, div_lt_iff₀ ] <;> nlinarith [ show 0 < Real.log ( Real.log n ) from Real.log_pos <| show 1 < Real.log n from by rw [ Real.lt_log_iff_exp_lt <| by norm_cast ; linarith ] ; exact Real.exp_one_lt_d9.trans_le <| by norm_num ; linarith [ show ( n : ℝ ) ≥ 3 by norm_cast ; linarith ] ];
        · exact Real.log_nonneg ( show 1 ≤ Real.log n from by rw [ Real.le_log_iff_exp_le ( by norm_cast; linarith ) ] ; exact Real.exp_one_lt_d9.le.trans ( by norm_num; linarith [ show ( n : ℝ ) ≥ 3 by norm_cast; linarith ] ) );
        · linarith;
      · exact mul_pos ( Real.rpow_pos_of_pos ( Real.log_pos ( show 1 < Real.log n from by rw [ Real.lt_log_iff_exp_lt ( by norm_cast; linarith ) ] ; exact Real.exp_one_lt_d9.trans_le ( by norm_num; linarith [ show ( n : ℝ ) ≥ 3 by norm_cast; linarith ] ) ) ) _ ) ( Real.log_pos ( show 1 < Real.log n from by rw [ Real.lt_log_iff_exp_lt ( by norm_cast; linarith ) ] ; exact Real.exp_one_lt_d9.trans_le ( by norm_num; linarith [ show ( n : ℝ ) ≥ 3 by norm_cast; linarith ] ) ) );
      · exact ne_of_gt ( Real.rpow_pos_of_pos ( Real.log_pos <| show 1 < Real.log n from by rw [ Real.lt_log_iff_exp_lt <| by norm_cast; linarith ] ; exact Real.exp_one_lt_d9.trans_le <| by norm_num; linarith [ show ( n : ℝ ) ≥ 3 by norm_cast; linarith ] ) _ );
      · exact ⟨ ⟨ by linarith, by linarith, by linarith ⟩, by linarith [ show 1 < Real.log n from by rw [ Real.lt_log_iff_exp_lt ( by norm_cast; linarith ) ] ; exact Real.exp_one_lt_d9.trans_le ( by norm_num; linarith [ show ( n : ℝ ) ≥ 3 by norm_cast; linarith ] ) ], by linarith [ show 0 < Real.log n from Real.log_pos ( by norm_cast; linarith ) ] ⟩;
    have hL_gt_4 : Filter.Tendsto (fun n : ℕ => (Real.log (Real.log n)) ^ c) Filter.atTop Filter.atTop := by
      exact tendsto_rpow_atTop ( by positivity ) |> Filter.Tendsto.comp <| Real.tendsto_log_atTop.comp <| Real.tendsto_log_atTop.comp <| tendsto_natCast_atTop_atTop;
    simpa using hL_gt_4.eventually_gt_atTop 4

/-
Adjusted algebraic bound for the sum-product result proof, using R = 0.25 * ...
-/
lemma final_algebraic_bound_adjusted (c : ℝ) (hc0 : 0 < c) (hc1 : c < 1) :
  ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
  let L := Real.log (Real.log n)
  let R := 0.25 * (n : ℝ) ^ (2/3 - 2 / L)
  let k := (n : ℝ) ^ (2 / L ^ (1 - c))
  let m := 0.5 * (n : ℝ)
  let bound := (n : ℝ) ^ (4/3 - 3 / L ^ (1 - c))
  m * R^2 / (R + m * k) ≥ bound := by
    -- By dividing both sides of the inequality by $bound$, we can simplify it to $0.0625 * n^{1/L^{1-c} - 4/L} / (1 + R/(m*k)) \geq 1$.
    suffices h_simplified : ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        let L := Real.log (Real.log n);
        let R := 0.25 * (n : ℝ) ^ (2 / 3 - 2 / L);
        let k := (n : ℝ) ^ (2 / L ^ (1 - c));
        let m := 0.5 * (n : ℝ);
        let bound := (n : ℝ) ^ (4 / 3 - 3 / L ^ (1 - c));
        0.0625 * (n : ℝ) ^ (1 / L ^ (1 - c) - 4 / L) / (1 + R / (m * k)) ≥ 1 by
          cases' h_simplified with N hN h_simplified; use N + 2; intros n hn; specialize hN n ( by linarith ) ; norm_num at *;
          rw [ le_div_iff₀ ] at hN ⊢;
          · rw [ one_mul, add_div', div_le_iff₀ ] at hN <;> ring_nf at * <;> norm_num at *;
            · convert mul_le_mul_of_nonneg_left hN ( show ( 0 : ℝ ) ≤ n ^ ( 4 / 3 - ( Real.log ( Real.log n ) ^ ( 1 - c ) ) ⁻¹ * 3 ) by positivity ) using 1 <;> ring_nf;
              norm_num [ sq, mul_assoc, ← Real.rpow_add ( Nat.cast_pos.mpr <| by linarith : 0 < ( n : ℝ ) ) ] ; ring_nf;
            · exact mul_pos ( Nat.cast_pos.mpr ( by linarith ) ) ( Real.rpow_pos_of_pos ( Nat.cast_pos.mpr ( by linarith ) ) _ );
            · exact ⟨ by linarith, by exact ne_of_gt ( Real.rpow_pos_of_pos ( Nat.cast_pos.mpr ( by linarith ) ) _ ) ⟩;
          · exact add_pos_of_nonneg_of_pos ( mul_nonneg ( by norm_num ) ( Real.rpow_nonneg ( Nat.cast_nonneg _ ) _ ) ) ( mul_pos ( by norm_num; linarith ) ( Real.rpow_pos_of_pos ( Nat.cast_pos.mpr ( by linarith ) ) _ ) );
          · positivity;
    have h_exp : Filter.Tendsto (fun n : ℕ => (0.0625 * (n : ℝ) ^ (1 / (Real.log (Real.log n)) ^ (1 - c) - 4 / (Real.log (Real.log n)))) / (1 + (0.25 * (n : ℝ) ^ (2 / 3 - 2 / (Real.log (Real.log n)))) / ((0.5 * (n : ℝ)) * (n : ℝ) ^ (2 / (Real.log (Real.log n)) ^ (1 - c))))) Filter.atTop Filter.atTop := by
      have h_exp : Filter.Tendsto (fun n : ℕ => (n : ℝ) ^ (1 / (Real.log (Real.log n)) ^ (1 - c) - 4 / (Real.log (Real.log n)))) Filter.atTop Filter.atTop := by
        have h_exp : Filter.Tendsto (fun n : ℕ => (1 / (Real.log (Real.log n)) ^ (1 - c) - 4 / (Real.log (Real.log n))) * Real.log n) Filter.atTop Filter.atTop := by
          -- We can factor out $\frac{\log n}{L^{1-c}}$ and use the fact that $1 - \frac{4}{L^c}$ tends to $1$ as $n \to \infty$.
          have h_factor : Filter.Tendsto (fun n : ℕ => (Real.log n / (Real.log (Real.log n))^(1 - c)) * (1 - 4 / (Real.log (Real.log n))^c)) Filter.atTop Filter.atTop := by
            have h_factor : Filter.Tendsto (fun n : ℕ => (Real.log n / (Real.log (Real.log n))^(1 - c))) Filter.atTop Filter.atTop := by
              -- Let $y = \log \log n$, therefore the expression becomes $\frac{e^y}{y^{1-c}}$.
              suffices h_y : Filter.Tendsto (fun y : ℝ => Real.exp y / y^(1 - c)) Filter.atTop Filter.atTop by
                have h_subst : Filter.Tendsto (fun n : ℕ => Real.exp (Real.log (Real.log n)) / (Real.log (Real.log n))^(1 - c)) Filter.atTop Filter.atTop := by
                  exact h_y.comp ( Real.tendsto_log_atTop.comp ( Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop ) );
                refine h_subst.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 1 ] with n hn; rw [ Real.exp_log ( Real.log_pos <| Nat.one_lt_cast.mpr hn ) ] );
              exact tendsto_exp_div_rpow_atTop (1 - c);
            apply Filter.Tendsto.atTop_mul_pos;
            exacts [ show 0 < 1 by norm_num, h_factor, le_trans ( tendsto_const_nhds.sub <| tendsto_const_nhds.div_atTop <| tendsto_rpow_atTop ( by linarith ) |> Filter.Tendsto.comp <| Real.tendsto_log_atTop.comp <| Real.tendsto_log_atTop.comp <| tendsto_natCast_atTop_atTop ) <| by norm_num ];
          refine h_factor.congr' ?_ ; filter_upwards [ Filter.eventually_gt_atTop 2 ] with n hn ; rw [ Real.rpow_sub ] <;> norm_num ; ring_nf ; norm_num [ ne_of_gt, Real.log_pos, hn ] ; ring_nf;
          · rw [ mul_inv_cancel_right₀ ( ne_of_gt ( Real.rpow_pos_of_pos ( Real.log_pos ( show 1 < Real.log n from by rw [ Real.lt_log_iff_exp_lt ( by positivity ) ] ; exact Real.exp_one_lt_d9.trans_le ( by norm_num; linarith [ show ( n : ℝ ) ≥ 3 by norm_cast ] ) ) ) _ ) ) ] ; ring;
          · exact Real.log_pos <| by rw [ Real.lt_log_iff_exp_lt <| by positivity ] ; exact Real.exp_one_lt_d9.trans_le <| by norm_num; linarith [ show ( n : ℝ ) ≥ 3 by norm_cast ] ;
        have h_exp : Filter.Tendsto (fun n : ℕ => Real.exp ((1 / (Real.log (Real.log n)) ^ (1 - c) - 4 / (Real.log (Real.log n))) * Real.log n)) Filter.atTop Filter.atTop := by
          aesop;
        refine h_exp.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with n hn; rw [ Real.rpow_def_of_pos ( Nat.cast_pos.mpr hn ), mul_comm ] );
      have h_frac : Filter.Tendsto (fun n : ℕ => (0.25 * (n : ℝ) ^ (2 / 3 - 2 / (Real.log (Real.log n)))) / ((0.5 * (n : ℝ)) * (n : ℝ) ^ (2 / (Real.log (Real.log n)) ^ (1 - c)))) Filter.atTop (nhds 0) := by
        -- Simplify the expression inside the limit.
        suffices h_frac_simplified : Filter.Tendsto (fun n : ℕ => (0.5 : ℝ) * (n : ℝ) ^ (2 / 3 - 2 / (Real.log (Real.log n)) - 1 - 2 / (Real.log (Real.log n)) ^ (1 - c))) Filter.atTop (nhds 0) by
          refine h_frac_simplified.congr' ?_;
          filter_upwards [ Filter.eventually_gt_atTop 1 ] with n hn;
          rw [ Real.rpow_sub ( by positivity ), Real.rpow_sub ( by positivity ) ] ; ring_nf;
          norm_num ; ring;
        -- The exponent $-1/3 - 2/L - 2/L^{1-c}$ tends to $-1/3$ as $n \to \infty$.
        have h_exp_neg : Filter.Tendsto (fun n : ℕ => (2 / 3 - 2 / (Real.log (Real.log n)) - 1 - 2 / (Real.log (Real.log n)) ^ (1 - c))) Filter.atTop (nhds (-1 / 3)) := by
          exact le_trans ( Filter.Tendsto.sub ( Filter.Tendsto.sub ( tendsto_const_nhds.sub <| tendsto_const_nhds.div_atTop <| Real.tendsto_log_atTop.comp <| Real.tendsto_log_atTop.comp <| tendsto_natCast_atTop_atTop ) tendsto_const_nhds ) <| tendsto_const_nhds.div_atTop <| tendsto_rpow_atTop ( by linarith ) |> Filter.Tendsto.comp <| Real.tendsto_log_atTop.comp <| Real.tendsto_log_atTop.comp <| tendsto_natCast_atTop_atTop ) <| by norm_num;
        have h_exp_neg : Filter.Tendsto (fun n : ℕ => (n : ℝ) ^ (2 / 3 - 2 / (Real.log (Real.log n)) - 1 - 2 / (Real.log (Real.log n)) ^ (1 - c))) Filter.atTop (nhds 0) := by
          have h_exp_neg : Filter.Tendsto (fun n : ℕ => Real.exp ((2 / 3 - 2 / (Real.log (Real.log n)) - 1 - 2 / (Real.log (Real.log n)) ^ (1 - c)) * Real.log n)) Filter.atTop (nhds 0) := by
            norm_num +zetaDelta at *;
            apply_rules [ Filter.Tendsto.neg_mul_atTop, h_exp_neg ];
            · norm_num +zetaDelta at *
            · exact Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop;
          refine h_exp_neg.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with n hn; rw [ Real.rpow_def_of_pos ( Nat.cast_pos.mpr hn ) ] ; ring_nf );
        simpa using h_exp_neg.const_mul 0.5;
      apply Filter.Tendsto.atTop_mul_pos;
      exacts [ show 0 < ( 1 + 0 ) ⁻¹ by norm_num, Filter.Tendsto.const_mul_atTop ( by norm_num ) h_exp, by simpa using Filter.Tendsto.inv₀ ( h_frac.const_add 1 ) ( by norm_num ) ];
    exact Filter.eventually_atTop.mp ( h_exp.eventually_ge_atTop 1 ) |> fun ⟨ N, hN ⟩ => ⟨ N, fun n hn => hN n hn ⟩

/-
For large n, R <= m * k with the adjusted constants.
-/
lemma denominator_bound_adjusted (c : ℝ) (hc0 : 0 < c) (hc1 : c < 1) :
  ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
  let L := Real.log (Real.log n)
  let R := 0.25 * (n : ℝ) ^ (2/3 - 2 / L)
  let k := (n : ℝ) ^ (2 / L ^ (1 - c))
  let m := 0.5 * (n : ℝ)
  R ≤ m * k := by
    -- We want $0.25 n^{2/3 - 2/L} \le 0.5 n^{1 + 2/L^{1-c}}$.
    suffices h_simp : ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        let L := Real.log (Real.log n);
        let exp := 2 / 3 - 2 / L - 1 - 2 / L ^ (1 - c);
        (0.5 : ℝ) * (n : ℝ) ^ exp ≤ 1 by
          obtain ⟨ N, hN ⟩ := h_simp;
          use N + 2; intros n hn; specialize hN n ( by linarith ) ; norm_num [ Real.rpow_sub ( by norm_cast; linarith : 0 < ( n :ℝ ) ) ] at *;
          convert mul_le_mul_of_nonneg_left hN ( show ( 0 :ℝ ) ≤ 1 / 2 * n * n ^ ( 2 / Real.log ( Real.log n ) ^ ( 1 - c ) ) by positivity ) using 1 ; ring_nf;
          · simp +decide [ mul_assoc, mul_comm, mul_left_comm, ne_of_gt ( show 0 < n by linarith ) ];
            rw [ mul_left_comm, mul_inv_cancel₀ ( ne_of_gt ( Real.rpow_pos_of_pos ( Nat.cast_pos.mpr ( by linarith ) ) _ ) ), mul_one ];
          · ring;
    -- The exponent is negative for large $n$ (since $L \to \infty$, the terms with $L$ go to 0, so the limit is $-1/3$).
    have h_exp_neg : Filter.Tendsto (fun n : ℕ => let L := Real.log (Real.log n); let exp := 2 / 3 - 2 / L - 1 - 2 / L ^ (1 - c); exp) Filter.atTop (nhds (-1 / 3)) := by
      exact le_trans ( Filter.Tendsto.sub ( Filter.Tendsto.sub ( tendsto_const_nhds.sub ( tendsto_const_nhds.div_atTop <| Real.tendsto_log_atTop.comp <| Real.tendsto_log_atTop.comp <| tendsto_natCast_atTop_atTop ) ) tendsto_const_nhds ) <| tendsto_const_nhds.div_atTop <| tendsto_rpow_atTop ( by linarith ) |> Filter.Tendsto.comp <| Real.tendsto_log_atTop.comp <| Real.tendsto_log_atTop.comp <| tendsto_natCast_atTop_atTop ) <| by norm_num;
    -- Since the exponent is negative for large $n$, we have $n^{\text{exp}} \to 0$ as $n \to \infty$.
    have h_exp_zero : Filter.Tendsto (fun n : ℕ => (n : ℝ) ^ (let L := Real.log (Real.log n); let exp := 2 / 3 - 2 / L - 1 - 2 / L ^ (1 - c); exp)) Filter.atTop (nhds 0) := by
      have h_exp_zero : Filter.Tendsto (fun n : ℕ => Real.exp ((let L := Real.log (Real.log n); let exp := 2 / 3 - 2 / L - 1 - 2 / L ^ (1 - c); exp) * Real.log n)) Filter.atTop (nhds 0) := by
        norm_num [ Real.exp_neg ] at *;
        apply_rules [ Filter.Tendsto.neg_mul_atTop, h_exp_neg ];
        · grind;
        · exact Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop;
      refine h_exp_zero.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with n hn; rw [ Real.rpow_def_of_pos ( Nat.cast_pos.mpr hn ) ] ; ring_nf );
    exact Filter.eventually_atTop.mp ( h_exp_zero.eventually ( ge_mem_nhds <| show 0 < 1 / ( 2 : ℝ ) by norm_num ) ) |> fun ⟨ N, hN ⟩ ↦ ⟨ N, fun n hn ↦ by linarith [ hN n hn ] ⟩

/-
Hypergraph bound for real R and K.
-/
lemma hypergraph_bound_real {α : Type*} [DecidableEq α] (E : Finset (Finset α)) (m : ℕ) (R K : ℝ) :
  E.card = m →
  (∀ e ∈ E, (e.card : ℝ) ≥ R) →
  (∀ e1 ∈ E, ∀ e2 ∈ E, e1 ≠ e2 → (e1 ∩ e2).card ≤ K) →
  0 < R →
  0 ≤ K →
  0 < m →
  (E.biUnion id).card * (R + (m - 1) * K) ≥ m * R^2 := by
    intros hm hE₁ hE₂ hR hK hm_pos
    have h_cauchy_schwarz : (∑ e ∈ E, e.card : ℝ) ^ 2 ≤ (E.biUnion id).card * (∑ e1 ∈ E, ∑ e2 ∈ E, (e1 ∩ e2).card) := by
      have h_cauchy_schwarz : ∀ (V : Finset α) (E : Finset (Finset α)), (∀ e ∈ E, e ⊆ V) → (∑ e ∈ E, e.card : ℝ) ^ 2 ≤ V.card * (∑ e1 ∈ E, ∑ e2 ∈ E, (e1 ∩ e2).card) := by
        intros V E hE_subset
        have h_cauchy_schwarz : (∑ e ∈ E, e.card : ℝ) ^ 2 ≤ V.card * (∑ v ∈ V, (∑ e ∈ E, if v ∈ e then 1 else 0) ^ 2) := by
          have h_cauchy_schwarz : ∀ (u v : α → ℝ), (∑ x ∈ V, u x * v x) ^ 2 ≤ (∑ x ∈ V, u x ^ 2) * (∑ x ∈ V, v x ^ 2) := by
            exact fun u v => Finset.sum_mul_sq_le_sq_mul_sq V u v;
          convert h_cauchy_schwarz ( fun _ => 1 ) ( fun v => ∑ e ∈ E, if v ∈ e then 1 else 0 ) using 1 <;> simp +decide
          rw [ Finset.sum_congr rfl fun e he => Nat.cast_inj.mpr <| Finset.card_eq_sum_ones _ ];
          rw [ Finset.sum_congr rfl fun e he => Nat.cast_sum _ _ ];
          rw [ Finset.sum_congr rfl fun e he => Finset.sum_congr rfl fun x hx => by rw [ show ( 1 : ℕ ) = if x ∈ e then 1 else 0 by aesop ] ] ; simp +decide
          rw [ show ( ∑ x ∈ V, ( Finset.card ( Finset.filter ( fun e => x ∈ e ) E ) : ℝ ) ) = ∑ e ∈ E, ( Finset.card e : ℝ ) from ?_ ];
          simp +decide only [Finset.card_filter];
          rw [ Finset.sum_congr rfl fun x hx => Nat.cast_sum _ _ ] ; rw [ Finset.sum_comm ] ; simp +decide
          exact Finset.sum_congr rfl fun e he => by rw [ Finset.inter_eq_right.mpr ( hE_subset e he ) ] ;
        -- The sum of the squares of the degrees of the vertices is equal to the sum of the intersection sizes of all pairs of edges.
        have h_sum_sq_degrees_eq : ∑ v ∈ V, (∑ e ∈ E, if v ∈ e then 1 else 0) ^ 2 = ∑ e1 ∈ E, ∑ e2 ∈ E, (e1 ∩ e2).card := by
          have h_sum_sq_degrees_eq : ∑ v ∈ V, (∑ e ∈ E, if v ∈ e then 1 else 0) ^ 2 = ∑ e1 ∈ E, ∑ e2 ∈ E, ∑ v ∈ V, (if v ∈ e1 then 1 else 0) * (if v ∈ e2 then 1 else 0) := by
            simp +decide only [sq, Finset.sum_mul _ _ _];
            rw [ Finset.sum_comm, Finset.sum_congr rfl ] ; intros ; rw [ Finset.sum_comm ] ; simp +decide [ Finset.sum_ite ] ;
          simp_all +decide
          exact Finset.sum_congr rfl fun e1 he1 => Finset.sum_congr rfl fun e2 he2 => by rw [ Finset.inter_eq_right.mpr ( Finset.inter_subset_left.trans ( hE_subset _ he2 ) ) ] ; simp +decide [ Finset.inter_comm ] ;
        exact h_cauchy_schwarz.trans ( by rw [ ← h_sum_sq_degrees_eq ] ; norm_cast );
      exact h_cauchy_schwarz _ _ fun e he => Finset.subset_biUnion_of_mem id he;
    -- Applying the bounds on the sum of intersections, we get:
    have h_sum_inter_bound : (∑ e1 ∈ E, ∑ e2 ∈ E, (e1 ∩ e2).card : ℝ) ≤ (∑ e ∈ E, e.card : ℝ) + (E.card * (E.card - 1) * K) := by
      have h_sum_inter_bound : ∀ e1 ∈ E, ∑ e2 ∈ E, (e1 ∩ e2).card ≤ e1.card + (E.card - 1) * K := by
        intro e1 he1
        have h_sum_inter_bound : ∑ e2 ∈ E \ {e1}, (e1 ∩ e2).card ≤ (E.card - 1) * K := by
          have h_sum_inter_bound : ∀ e2 ∈ E \ {e1}, (e1 ∩ e2).card ≤ K := by
            exact fun e2 he2 => hE₂ e1 he1 e2 ( Finset.mem_sdiff.mp he2 |>.1 ) ( by aesop );
          simpa [ Finset.card_sdiff, * ] using Finset.sum_le_sum h_sum_inter_bound;
        convert add_le_add_left h_sum_inter_bound ( e1.card : ℝ ) using 1 ; simp +decide [ Finset.sum_eq_add_sum_diff_singleton he1 ];
      convert Finset.sum_le_sum h_sum_inter_bound using 1 ; norm_num [ Finset.sum_add_distrib, Finset.mul_sum _ _ _ ] ; ring_nf;
      simpa [ Finset.sum_add_distrib, Finset.mul_sum _ _ _, Finset.sum_mul ] using by ring;
    -- Applying the bounds on the sum of edge sizes, we get:
    have h_sum_edge_size_bound : (∑ e ∈ E, e.card : ℝ) ≥ m * R := by
      exact le_trans ( by aesop ) ( Finset.sum_le_sum fun e he => hE₁ e he );
    -- Applying the algebraic helper lemma to combine the inequalities.
    have h_algebraic_helper : (∑ e ∈ E, e.card : ℝ) ^ 2 / ((∑ e ∈ E, e.card : ℝ) + (E.card * (E.card - 1) * K)) ≥ (m * R) ^ 2 / ((m * R) + (m * (m - 1) * K)) := by
      have h_algebraic_helper : ∀ (S K : ℝ) (hS : 0 < S) (hK : 0 ≤ K) (m R : ℝ) (hm : 0 < m) (hR : 0 < R) (h_sum : m * R ≤ S), m * R^2 / (R + K / m) ≤ S^2 / (S + K) := by
        exact fun S K hS hK m R hm hR h_sum => algebraic_helper S K hS hK m R hm hR h_sum;
      specialize h_algebraic_helper (∑ e ∈ E, e.card : ℝ) (↑E.card * (↑E.card - 1) * K) (by
      exact lt_of_lt_of_le ( by positivity ) h_sum_edge_size_bound) (by
      exact mul_nonneg ( mul_nonneg ( Nat.cast_nonneg _ ) ( sub_nonneg.mpr ( Nat.one_le_cast.mpr ( Finset.card_pos.mpr ( Finset.nonempty_of_ne_empty ( by aesop_cat ) ) ) ) ) ) hK) (↑m : ℝ) R (by
      positivity) (by
      exact hR) (by
      exact h_sum_edge_size_bound);
      simp_all +decide [ mul_pow, mul_comm ];
      convert h_algebraic_helper using 1 ; rw [ show R + K * ( m * ( m - 1 ) ) / m = ( R * m + K * ( m * ( m - 1 ) ) ) / m by rw [ add_div' ] ; ring_nf ; positivity ] ; rw [ div_div_eq_mul_div ] ; ring;
    -- Combining the inequalities from h_cauchy_schwarz, h_sum_inter_bound, and h_algebraic_helper, we get:
    have h_combined : (m * R) ^ 2 / ((m * R) + (m * (m - 1) * K)) ≤ (E.biUnion id).card := by
      refine' le_trans h_algebraic_helper ( div_le_of_le_mul₀ _ _ _ );
      · exact add_nonneg ( Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _ ) ( mul_nonneg ( mul_nonneg ( Nat.cast_nonneg _ ) ( sub_nonneg.mpr ( Nat.one_le_cast.mpr ( Finset.card_pos.mpr ⟨ _, Classical.choose_spec ( Finset.card_pos.mp ( by linarith ) ) ⟩ ) ) ) ) hK );
      · positivity;
      · exact h_cauchy_schwarz.trans ( mul_le_mul_of_nonneg_left ( by simpa [ ← @Nat.cast_le ℝ ] using h_sum_inter_bound ) ( Nat.cast_nonneg _ ) );
    rw [ div_le_iff₀ ] at h_combined <;> nlinarith [ show 0 < ( m : ℝ ) * R by positivity, show 0 ≤ ( m : ℝ ) * ( m - 1 ) * K by exact mul_nonneg ( mul_nonneg ( Nat.cast_nonneg _ ) ( sub_nonneg.mpr ( Nat.one_le_cast.mpr hm_pos ) ) ) hK ] ;

/-
If a family of sets satisfies the hypergraph conditions and the algebraic bound holds for the minimum number of sets, then the union is large enough.
-/
lemma hypergraph_consequence (n : ℕ) (U : Finset ℕ) (C : ℕ → Finset ℕ) (R K bound : ℝ)
  (h_U : (U.card : ℝ) ≥ 0.5 * n)
  (h_R : ∀ k ∈ U, (C k).card ≥ R)
  (h_K : ∀ k j, k ∈ U → j ∈ U → k ≠ j → (C k ∩ C j).card ≤ K)
  (h_alg : (0.5 * n) * R^2 / (R + (0.5 * n) * K) ≥ bound)
  (h_RK : K < R)
  (h_pos : 0 < R)
  (h_K_nonneg : 0 ≤ K)
  (h_n : 0 < n) :
  ((U.biUnion C).card : ℝ) ≥ bound := by
    -- Apply the hypergraph bound to the set $E = \{C(k) : k \in U\}$.
    have h_hypergraph : (U.biUnion C).card * (R + (U.card - 1) * K) ≥ U.card * R^2 := by
      have h_hypergraph : ∀ E : Finset (Finset ℕ), E.card = U.card → (∀ e ∈ E, (e.card : ℝ) ≥ R) → (∀ e1 ∈ E, ∀ e2 ∈ E, e1 ≠ e2 → (e1 ∩ e2).card ≤ K) → (E.biUnion id).card * (R + (U.card - 1) * K) ≥ U.card * R^2 := by
        intros E hE_card hE_R hE_K
        have := hypergraph_bound_real E U.card R K hE_card (fun e he => hE_R e he) (fun e1 he1 e2 he2 he_ne => hE_K e1 he1 e2 he2 he_ne) h_pos h_K_nonneg (by
        exact Nat.cast_pos.mp ( lt_of_lt_of_le ( by positivity ) h_U ));
        convert this using 1;
      convert h_hypergraph ( Finset.image C U ) _ _ _ using 1;
      · rw [ Finset.image_biUnion ];
        rfl;
      · rw [ Finset.card_image_of_injOn ];
        intros k hk j hj hij;
        grind;
      · aesop;
      · grind;
    -- Since $f(x) = x R^2 / (R + xK)$ is increasing for $x > 0$, we have $f(U.card) \ge f(0.5 n)$.
    have h_f_inc : (U.card : ℝ) * R^2 / (R + U.card * K) ≥ (0.5 * n : ℝ) * R^2 / (R + 0.5 * n * K) := by
      have h_f_inc : ∀ x y : ℝ, 0 < x → x ≤ y → x * R^2 / (R + x * K) ≤ y * R^2 / (R + y * K) := by
        intro x y hx hy; rw [ div_le_div_iff₀ ] <;> nlinarith [ mul_le_mul_of_nonneg_left hy h_pos.le, mul_le_mul_of_nonneg_left hy h_K_nonneg ] ;
      exact h_f_inc _ _ ( by positivity ) h_U;
    exact h_alg.trans ( h_f_inc.trans ( by rw [ div_le_iff₀ ] <;> nlinarith ) )

/-
For large n, K < R with the adjusted constant R = 0.25 * ...
-/
lemma R_gt_K_adjusted (c : ℝ) (hc1 : c < 1) :
  ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
  let L := Real.log (Real.log n)
  let R := 0.25 * (n : ℝ) ^ (2/3 - 2 / L)
  let K := (n : ℝ) ^ (2 / L ^ (1 - c))
  K < R := by
    have h_log : Filter.Tendsto (fun n : ℕ => (2 / (Real.log (Real.log n)) ^ (1 - c) - 2 / 3 + 2 / Real.log (Real.log n)) * Real.log n) Filter.atTop Filter.atBot := by
      have h_log : Filter.Tendsto (fun n : ℕ => (2 / (Real.log (Real.log n)) ^ (1 - c) - 2 / 3 + 2 / Real.log (Real.log n))) Filter.atTop (nhds (0 - 2 / 3 + 0)) := by
        exact Filter.Tendsto.add ( Filter.Tendsto.sub ( tendsto_const_nhds.div_atTop <| tendsto_rpow_atTop ( by linarith ) |> Filter.Tendsto.comp <| Real.tendsto_log_atTop.comp <| Real.tendsto_log_atTop.comp <| tendsto_natCast_atTop_atTop ) tendsto_const_nhds ) <| tendsto_const_nhds.div_atTop <| Real.tendsto_log_atTop.comp <| Real.tendsto_log_atTop.comp <| tendsto_natCast_atTop_atTop;
      apply_rules [ Filter.Tendsto.neg_mul_atTop ];
      · norm_num;
      · exact Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop;
    -- By definition of exponentiation, if the logarithm of a number is less than the logarithm of another number, then the first number is less than the second.
    have h_exp : ∀ᶠ n : ℕ in Filter.atTop, Real.log ((n : ℝ) ^ (2 / (Real.log (Real.log n)) ^ (1 - c))) < Real.log (0.25 * (n : ℝ) ^ (2 / 3 - 2 / Real.log (Real.log n))) := by
      have h_exp : ∀ᶠ n : ℕ in Filter.atTop, (2 / (Real.log (Real.log n)) ^ (1 - c)) * Real.log n < Real.log 0.25 + (2 / 3 - 2 / Real.log (Real.log n)) * Real.log n := by
        filter_upwards [ h_log.eventually ( Filter.eventually_lt_atBot ( Real.log 0.25 ) ) ] with n hn using by linarith;
      filter_upwards [ h_exp, Filter.eventually_gt_atTop 1 ] with n hn hn' ; rw [ Real.log_mul ( by positivity ) ( by positivity ), Real.log_rpow ( by positivity ), Real.log_rpow ( by positivity ) ] ; aesop;
    obtain ⟨ N, hN ⟩ := Filter.eventually_atTop.mp h_exp;
    exact ⟨ N + 1, fun n hn => by have := hN n ( by linarith ) ; rw [ Real.log_lt_log_iff ( by exact Real.rpow_pos_of_pos ( Nat.cast_pos.mpr <| by linarith ) _ ) ( by exact mul_pos ( by norm_num ) <| Real.rpow_pos_of_pos ( Nat.cast_pos.mpr <| by linarith ) _ ) ] at this; norm_num at * ; linarith ⟩

/-
If |A+A| is small, then |AA| is large (at least the bound).
-/
theorem sum_product_result_implication (c : ℝ) (hc0 : 0 < c) (hc1 : c < 1) :
  ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
  ∀ A : Finset ℕ, A.card = n →
  (∀ x ∈ A, 1 ≤ x) →
  (∀ x ∈ A, (x : ℝ) ≤ (n : ℝ) ^ ((Real.log (Real.log n)) ^ c)) →
  let bound := (n : ℝ) ^ (4/3 - 3 / (Real.log (Real.log n)) ^ (1 - c))
  ((A + A).card : ℝ) < bound →
  (((A.product A).image (fun (x : ℕ × ℕ) => x.1 * x.2)).card : ℝ) ≥ bound := by
    -- By `heavy_indices_lower_bound`, there are at least $0.5n$ heavy indices.
    obtain ⟨N1, hN1⟩ : ∃ N1 : ℕ, ∀ n : ℕ, N1 ≤ n →
      let L := Real.log (Real.log n)
      let bound := (n : ℝ) ^ (4 / 3 - 3 / L ^ (1 - c))
      let δ := 0.5 * (n : ℝ) ^ (2 / 3 - 2 / L)
      ∀ A : Finset ℕ, A.card = n →
      (∀ x ∈ A, 1 ≤ x) →
      (∀ x ∈ A, (x : ℝ) ≤ n ^ (Real.log (Real.log n)) ^ c) →
      (A + A).card < bound →
      ((heavy_indices A δ).card : ℝ) ≥ 0.5 * n := by
        have := @heavy_indices_lower_bound c hc0 hc1;
        exact ⟨ this.choose, fun n hn A hA hA' hA'' hA''' => this.choose_spec n hn A hA <| le_of_lt hA''' ⟩;
    -- By `intersection_bound_asymptotic`, for distinct k, j in heavy_indices, |C_k ∩ C_j| ≤ K.
    obtain ⟨N2, hN2⟩ : ∃ N2 : ℕ, ∀ n : ℕ, N2 ≤ n →
      let L := Real.log (Real.log n)
      let bound := (n : ℝ) ^ (4 / 3 - 3 / L ^ (1 - c))
      let K := (n : ℝ) ^ (2 / L ^ (1 - c))
      ∀ A : Finset ℕ, A.card = n →
      (∀ x ∈ A, 1 ≤ x) →
      (∀ x ∈ A, (x : ℝ) ≤ n ^ (Real.log (Real.log n)) ^ c) →
      (A + A).card < bound →
      ∀ k j : ℕ, k ∈ heavy_indices A (0.5 * (n : ℝ) ^ (2 / 3 - 2 / L)) → j ∈ heavy_indices A (0.5 * (n : ℝ) ^ (2 / 3 - 2 / L)) → k ≠ j →
      ((C_set A k ∩ C_set A j).card : ℝ) ≤ K := by
        obtain ⟨ N2, hN2 ⟩ := intersection_bound_asymptotic c hc0 hc1;
        refine' ⟨ N2, fun n hn A hnA hA₁ hA₂ hA₃ k j hk hj hkj => _ ⟩;
        refine le_trans ?_ ( hN2 n hn k j hkj ?_ ?_ ) <;> norm_num [ heavy_indices ] at *;
        · exact Finset.card_le_card fun x hx => C_set_inter_subset_A_inter A k j hA₁ |> fun h => h hx;
        · rcases Finset.mem_add.mp hk.1 with ⟨ x, hx, y, hy, rfl ⟩ ; exact_mod_cast ( by linarith [ hA₂ x hx, hA₂ y hy ] : ( x : ℝ ) + y ≤ 2 * n ^ Real.log ( Real.log n ) ^ c ) ;
        · obtain ⟨ x, hx, y, hy, rfl ⟩ := Finset.mem_add.mp hj.1;
          exact_mod_cast ( by linarith [ hA₂ x hx, hA₂ y hy ] : ( x + y : ℝ ) ≤ 2 * n ^ Real.log ( Real.log n ) ^ c );
    -- By `final_algebraic_bound_adjusted`, the algebraic condition for `hypergraph_consequence` holds.
    obtain ⟨N3, hN3⟩ : ∃ N3 : ℕ, ∀ n : ℕ, N3 ≤ n →
      let L := Real.log (Real.log n)
      let bound := (n : ℝ) ^ (4 / 3 - 3 / L ^ (1 - c))
      let R := 0.25 * (n : ℝ) ^ (2 / 3 - 2 / L)
      let K := (n : ℝ) ^ (2 / L ^ (1 - c))
      let m := 0.5 * (n : ℝ)
      m * R^2 / (R + m * K) ≥ bound := by
        exact final_algebraic_bound_adjusted c hc0 hc1;
    -- By `R_gt_K_adjusted`, K < R.
    obtain ⟨N4, hN4⟩ : ∃ N4 : ℕ, ∀ n : ℕ, N4 ≤ n →
      let L := Real.log (Real.log n)
      let R := 0.25 * (n : ℝ) ^ (2 / 3 - 2 / L)
      let K := (n : ℝ) ^ (2 / L ^ (1 - c))
      K < R := by
        exact R_gt_K_adjusted c hc1;
    refine' ⟨ N1 + N2 + N3 + N4 + 10, fun n hn A hA hA1 hA2 hA3 => _ ⟩;
    -- Apply `hypergraph_consequence` to get $|\bigcup_{k \in U} C_k| \ge bound$.
    have h_union : ((heavy_indices A (0.5 * (n : ℝ) ^ (2 / 3 - 2 / Real.log (Real.log n)))).biUnion (fun k => C_set A k)).card ≥ (n : ℝ) ^ (4 / 3 - 3 / Real.log (Real.log n) ^ (1 - c)) := by
      apply hypergraph_consequence;
      exact hN1 n ( by linarith ) A hA hA1 hA2 hA3;
      case R => exact 0.25 * ( n : ℝ ) ^ ( 2 / 3 - 2 / Real.log ( Real.log n ) );
      case K => exact ( n : ℝ ) ^ ( 2 / Real.log ( Real.log n ) ^ ( 1 - c ) );
      any_goals linarith;
      any_goals positivity;
      · intro k hk;
        have := Finset.mem_filter.mp hk |>.2;
        have := C_set_card_lower_bound A k;
        norm_num at * ; linarith [ ( by norm_cast : ( 2 : ℝ ) * ( C_set A k |> Finset.card ) ≥ ( B_full A k |> Finset.card ) ) ];
      · exact hN2 n ( by linarith ) A hA hA1 hA2 hA3;
      · grind;
      · exact hN4 n ( by linarith );
      · exact mul_pos ( by norm_num ) ( Real.rpow_pos_of_pos ( Nat.cast_pos.mpr ( by linarith ) ) _ );
    refine le_trans h_union ?_;
    refine' mod_cast Finset.card_le_card _;
    simp +decide [ Finset.subset_iff ];
    intro x k hk hx; unfold C_set at hx; obtain ⟨ a, ha, rfl ⟩ := Finset.mem_image.mp hx; exact ⟨ _, _, Finset.mem_product.mp ( Finset.mem_filter.mp ha |>.1 ) |>.1 |> fun h => ⟨ h, Finset.mem_product.mp ( Finset.mem_filter.mp ha |>.1 ) |>.2 ⟩, rfl ⟩ ;

/-
Conditional sum-product result: If A is a subset of integers up to n^{(log log n)^c}, then max(|A+A|, |AA|) is at least n^{4/3 - 3/(log log n)^{1-c}}.
-/
theorem sum_product_result (c : ℝ) (hc0 : 0 < c) (hc1 : c < 1) :
  ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
  ∀ A : Finset ℕ, A.card = n →
  (∀ x ∈ A, 1 ≤ x) →
  (∀ x ∈ A, (x : ℝ) ≤ (n : ℝ) ^ ((Real.log (Real.log n)) ^ c)) →
  let bound := (n : ℝ) ^ (4/3 - 3 / (Real.log (Real.log n)) ^ (1 - c))
  max ((A + A).card : ℝ) (((A.product A).image (fun (x : ℕ × ℕ) => x.1 * x.2)).card : ℝ) ≥ bound := by
    -- By `sum_product_result_implication`, there exists an $N$ such that for all $n \geq N$ and any set $A$ satisfying the conditions, if $|A+A| < bound$, then $|AA| \geq bound$.
    obtain ⟨N, hN⟩ := sum_product_result_implication c hc0 hc1;
    exact ⟨ N, fun n hn A hA h1 h2 => by specialize hN n hn A hA h1 h2; contrapose! hN; aesop ⟩

theorem erdos_443_part_one (s : ℕ) :
  ∃ m n : ℕ, n < m ∧ s ≤ ((A n ∩ A m).card : ℝ) := by
  -- By Theorem 1.3, there exist infinitely many pairs (n_k, m_k) such that |A_{n_k} \cap A_{m_k}| = s.
  have h_inf : ∀ s : ℕ, 0 < s → ∃ n m : ℕ, n < m ∧ (A n ∩ A m).card = s := by
    intro s hs;
    -- By Theorem 1.3, there exist infinitely many pairs (n_k, m_k) such that |A_{n_k} \cap A_{m_k}| = s. Use this theorem.
    have h_theorem : ∃ n_seq m_seq : ℕ → ℕ,
      (∀ k, n_seq k < m_seq k) ∧
      (∀ k, m_seq k < n_seq (k + 1)) ∧
      (∀ k, (A (n_seq k) ∩ A (m_seq k)).card = s) := by
        exact theorem_1_3 s hs;
    exact ⟨ _, _, h_theorem.choose_spec.choose_spec.1 0, h_theorem.choose_spec.choose_spec.2.2 0 ⟩;
  -- We'll use the fact that if s is zero, we can choose n = 0 and m = 1, and if s is positive, we can use the result from h_inf.
  by_cases hs : s = 0;
  · exact ⟨ 1, 0, by norm_num, by norm_num [ hs ] ⟩;
  · exact Exists.elim ( h_inf s ( Nat.pos_of_ne_zero hs ) ) fun n hn => Exists.elim hn fun m hm => ⟨ m, n, hm.1, mod_cast hm.2.ge ⟩

theorem erdos_443_part_two (ε : ℝ) (hε : 0 < ε) :
  ∃ n₀ : ℕ, ∀ m n : ℕ, n₀ < n → n < m →
  ((A n ∩ A m).card : ℝ) < ((m : ℝ) * n) ^ (ε) := by
  -- By Corollary 1.2, there exists an $N_1$ such that for all $m > n > N_1$, $|A_n \cap A_m| < m^{\frac{3 \log 2}{\log \log m}}$.
  obtain ⟨N1, hN1⟩ : ∃ N1 : ℕ, ∀ m n : ℕ, N1 < n → n < m → ((A n ∩ A m).card : ℝ) < (m : ℝ) ^ ((3 * Real.log 2) / Real.log (Real.log m)) := by
    obtain ⟨ N1, hN1 ⟩ := corollary_1_2 1 ( by norm_num );
    exact ⟨ N1, fun m n hn hm => mod_cast hN1 m n hn hm ⟩;
  -- Choose $N_2$ such that for all $m > N_2$, $m^{\frac{3 \log 2}{\log \log m}} < m^\epsilon$.
  obtain ⟨N2, hN2⟩ : ∃ N2 : ℕ, ∀ m : ℕ, N2 < m → (m : ℝ) ^ ((3 * Real.log 2) / Real.log (Real.log m)) < (m : ℝ) ^ ε := by
    -- Choose $N_2$ such that for all $m > N_2$, $\frac{3 \log 2}{\log \log m} < \epsilon$.
    obtain ⟨N2, hN2⟩ : ∃ N2 : ℕ, ∀ m : ℕ, N2 < m → (3 * Real.log 2) / Real.log (Real.log m) < ε := by
      have h_log_log : Filter.Tendsto (fun m : ℕ => Real.log (Real.log m)) Filter.atTop Filter.atTop := by
        exact Real.tendsto_log_atTop.comp <| Real.tendsto_log_atTop.comp <| tendsto_natCast_atTop_atTop;
      exact Filter.eventually_atTop.mp ( h_log_log.eventually_gt_atTop ( 3 * Real.log 2 / ε ) ) |> fun ⟨ N2, hN2 ⟩ ↦ ⟨ N2, fun m hm ↦ by rw [ div_lt_iff₀ ] <;> nlinarith [ hN2 m hm.le, Real.log_pos one_lt_two, mul_div_cancel₀ ( 3 * Real.log 2 ) hε.ne' ] ⟩;
    exact ⟨ N2 + 1, fun m hm => Real.rpow_lt_rpow_of_exponent_lt ( by norm_cast; linarith ) ( hN2 m ( by linarith ) ) ⟩;
  use Max.max N1 N2 + 1; intros m n hn hm; specialize hN1 m n ( by linarith [ Nat.le_max_left N1 N2 ] ) hm; specialize hN2 m ( by linarith [ Nat.le_max_right N1 N2 ] ) ; rw [ Real.mul_rpow ( by positivity ) ( by positivity ) ] ; exact lt_of_lt_of_le hN1 ( le_trans hN2.le <| le_mul_of_one_le_right ( by positivity ) <| Real.one_le_rpow ( by norm_cast; linarith [ Nat.le_max_left N1 N2, Nat.le_max_right N1 N2 ] ) <| by positivity ) ;

#print axioms erdos_443_part_one
-- 'erdos_443_part_one' depends on axioms: [propext, Classical.choice, Quot.sound]

#print axioms erdos_443_part_two
-- 'erdos_443_part_two' depends on axioms: [propext, Classical.choice, Quot.sound]
