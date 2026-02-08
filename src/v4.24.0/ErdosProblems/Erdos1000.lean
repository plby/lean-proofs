/-

This is a Lean formalization of a solution to Erdős Problem 1000.
https://www.erdosproblems.com/forum/thread/1000

The original proof was found by: J. A. Haight

[Ha] Haight, J. A., Metric Diophantine approximation and related
topics. PhD thesis


A proof of ChatGPT's choice was auto-formalized by Aristotle (from
Harmonic).  The final theorem statement was written by ChatGPT.


The proof is verified by Lean.  The following version numbers were
used:

Lean Toolchain version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7 (v4.24.0)

-/


/-
We prove the main theorem `thm_main` which states that there exists a strictly increasing sequence A such that the Cesaro average of phi_A(k)/n_k tends to 0.
The proof constructs the sequence `n_seq` by concatenating blocks of multiples of a large prime `r_t` with divisors of `Q_t` (product of first t primes).
We prove that the average over each block is bounded by `2 * A_val t`, where `A_val t` tends to 0.
We use `lem_block` to conclude that the Cesaro average tends to 0.
Helper lemmas `n_seq_phi_bound_correct`, `block_sum_bound`, `inv_r_seq_le_A_val`, `sum_bound_eval` were proved to support the main theorem.
-/

import Mathlib

namespace Erdos1000


set_option linter.mathlibStandardSet false

open scoped Classical

set_option maxHeartbeats 0

/-
For a sequence A = {n_k}, phi_A(k) is the number of integers m with 1 <= m <= n_k such that n_k / gcd(m, n_k) is not equal to any n_j for j < k.
-/
def phi_A (n : ℕ → ℕ) (k : ℕ) : ℕ :=
  (Finset.filter (fun m => 1 ≤ m ∧ ∀ j < k, n k / Nat.gcd m (n k) ≠ n j) (Finset.range (n k + 1))).card

/-
Lemma 1: Let p be a prime and q a positive integer coprime to p. Assume that for every proper divisor d of q, pd appears in the sequence A before pq. If n_k = pq, then phi_A(k)/n_k <= phi(q)/q + 1/p.
-/
lemma lem_primeblock (n : ℕ → ℕ) (k : ℕ) (p q : ℕ)
    (h_mono : StrictMono n)
    (hp : p.Prime)
    (hq : 0 < q)
    (hpq : Nat.Coprime p q)
    (hnk : n k = p * q)
    (h_div : ∀ d, d ∣ q → d < q → ∃ j < k, n j = p * d) :
    (phi_A n k : ℚ) / n k ≤ (Nat.totient q : ℚ) / q + 1 / p := by
  -- Let's split the count into two parts: those $m$ where $p \nmid m$ and those where $p \mid m$.
  have h_split : phi_A n k ≤ Nat.totient (p * q) + q := by
    -- If $p \mid m$, then $m = p * m'$ for some $m'$ with $1 \leq m' \leq q$. There are exactly $q$ such $m'$.
    have h_div : Finset.filter (fun m => p ∣ m) (Finset.filter (fun m => 1 ≤ m ∧ ∀ j < k, n k / Nat.gcd m (n k) ≠ n j) (Finset.range (n k + 1))) ⊆ Finset.image (fun m' => p * m') (Finset.Icc 1 q) := by
      intro m hm;
      norm_num +zetaDelta at *;
      exact ⟨ m / p, ⟨ Nat.div_pos ( Nat.le_of_dvd ( by linarith ) hm.2 ) hp.pos, Nat.div_le_of_le_mul <| by nlinarith ⟩, Nat.mul_div_cancel' hm.2 ⟩;
    -- If $p \nmid m$, then $(m, pq) = (m, q)$ and $\frac{pq}{(m, pq)} = p \cdot \frac{q}{(m, q)}$.
    have h_not_div : Finset.filter (fun m => ¬p ∣ m) (Finset.filter (fun m => 1 ≤ m ∧ ∀ j < k, n k / Nat.gcd m (n k) ≠ n j) (Finset.range (n k + 1))) ⊆ Finset.filter (fun m => Nat.gcd m (p * q) = 1) (Finset.range (p * q + 1)) := by
      intro m hm; simp_all +decide [ Finset.subset_iff ] ;
      by_contra h_contra;
      -- Since $p \nmid m$, we have $\gcd(m, pq) = \gcd(m, q)$.
      have h_gcd : Nat.gcd m (p * q) = Nat.gcd m q := by
        exact Nat.Coprime.gcd_mul_left_cancel_right _ <| hp.coprime_iff_not_dvd.mpr hm.2;
      -- Since $p \nmid m$, we have $\gcd(m, q) \neq 1$, which implies that $q / \gcd(m, q)$ is a proper divisor of $q$.
      have h_proper_divisor : ∃ d, d ∣ q ∧ d < q ∧ q / Nat.gcd m q = d := by
        exact ⟨ q / Nat.gcd m q, Nat.div_dvd_of_dvd <| Nat.gcd_dvd_right _ _, Nat.div_lt_self hq <| lt_of_le_of_ne ( Nat.gcd_pos_of_pos_right _ hq ) <| Ne.symm <| by aesop, rfl ⟩;
      obtain ⟨ d, hd₁, hd₂, hd₃ ⟩ := h_proper_divisor; specialize ‹∀ d : ℕ, d ∣ q → d < q → ∃ j < k, n j = p * d› d hd₁ hd₂; simp_all +decide
      obtain ⟨ j, hj₁, hj₂ ⟩ := h_div; specialize hm; have := hm.1.2.2 j hj₁; simp_all +decide [ Nat.mul_div_assoc, Nat.gcd_dvd_right ] ;
    have h_card : (Finset.filter (fun m => p ∣ m) (Finset.filter (fun m => 1 ≤ m ∧ ∀ j < k, n k / Nat.gcd m (n k) ≠ n j) (Finset.range (n k + 1)))).card + (Finset.filter (fun m => ¬p ∣ m) (Finset.filter (fun m => 1 ≤ m ∧ ∀ j < k, n k / Nat.gcd m (n k) ≠ n j) (Finset.range (n k + 1)))).card ≤ q + Nat.totient (p * q) := by
      refine' add_le_add _ _;
      · exact le_trans ( Finset.card_le_card h_div ) ( Finset.card_image_le.trans ( by simp ) );
      · refine' le_trans ( Finset.card_le_card h_not_div ) _;
        rw [ Nat.totient_eq_card_coprime ];
        simp +decide [ Nat.coprime_comm, Finset.filter ];
        rw [ Multiset.filter_cons ] ; aesop;
    convert h_card using 1;
    · rw [ Finset.filter_card_add_filter_neg_card_eq_card ];
      exact rfl;
    · ring;
  simp_all +decide [ Nat.totient_mul, Nat.Coprime ];
  field_simp;
  rw [ add_div', div_le_div_iff_of_pos_right ] <;> norm_cast <;> nlinarith [ hp.two_le, Nat.totient_le p, Nat.totient_le q ]

/-
Lemma 2: Let Q_t be the product of the first t primes. Then (1/2^t) * sum_{d|Q_t} (phi(d)/d) = product_{i=1}^t (1 - 1/(2p_i)).
-/
noncomputable def Q (t : ℕ) : ℕ := (Finset.range t).prod (fun i => Nat.nth Nat.Prime i)

lemma lem_divisoravg (t : ℕ) :
    (1 / 2 ^ t : ℚ) * (Nat.divisors (Q t)).sum (fun d => (Nat.totient d : ℚ) / d) =
    (Finset.range t).prod (fun i => 1 - 1 / (2 * (Nat.nth Nat.Prime i : ℚ))) := by
  -- Since $Q_t$ is squarefree, each divisor $d\mid Q_t$ corresponds to a subset $S\subseteq\{1,\dots,t\}$ via $d=\prod_{i\in S}p_i$.
  have h_divisors : ∀ d ∈ Nat.divisors (Q t), (Nat.totient d : ℚ) / d = ∏ i ∈ Finset.range t, if (Nat.nth Nat.Prime i) ∣ d then (1 - 1 / (Nat.nth Nat.Prime i : ℚ)) else 1 := by
    intro d hd
    have h_divisors : (Nat.totient d : ℚ) / d = ∏ p ∈ Nat.primeFactors d, (1 - 1 / (p : ℚ)) := by
      have := Nat.totient_eq_mul_prod_factors d;
      by_cases hd : d = 0 <;> aesop;
    -- Since $d$ divides $Q_t$, its prime factors are a subset of the first $t$ primes.
    have h_prime_factors : Nat.primeFactors d ⊆ Finset.image (Nat.nth Nat.Prime) (Finset.range t) := by
      intro p hp;
      have h_prime_factors_subset : p ∣ ∏ i ∈ Finset.range t, Nat.nth Nat.Prime i := by
        exact dvd_trans ( Nat.dvd_of_mem_primeFactors hp ) ( Nat.dvd_of_mem_divisors hd );
      simp_all +decide [ Nat.Prime.dvd_iff_not_coprime, Nat.coprime_prod_right_iff ];
      obtain ⟨ x, hx₁, hx₂ ⟩ := h_prime_factors_subset; have := Nat.coprime_primes hp.1 ( Nat.prime_nth_prime x ) ; aesop;
    -- Since these two products are over the same set, they are equal.
    have h_prod_eq : ∏ p ∈ Nat.primeFactors d, (1 - 1 / (p : ℚ)) = ∏ p ∈ Finset.image (Nat.nth Nat.Prime) (Finset.range t), (if p ∣ d then (1 - 1 / (p : ℚ)) else 1) := by
      rw [ ← Finset.prod_subset h_prime_factors ];
      · exact Finset.prod_congr rfl fun x hx => by rw [ if_pos ( Nat.dvd_of_mem_primeFactors hx ) ] ;
      · aesop;
    rw [ h_divisors, h_prod_eq, Finset.prod_image <| by intros a ha b hb hab; simpa using Nat.nth_injective ( Nat.infinite_setOf_prime ) hab ];
  -- Therefore, $\sum_{d\mid Q_t}\frac{\varphi(d)}{d}=\sum_{S\subseteq\{1,\dots,t\}}\ \prod_{i\in S}\left(1-\frac1{p_i}\right)$.
  have h_sum_divisors : ∑ d ∈ Nat.divisors (Q t), (Nat.totient d : ℚ) / d = ∑ S ∈ Finset.powerset (Finset.range t), (∏ i ∈ S, (1 - 1 / (Nat.nth Nat.Prime i : ℚ))) := by
    -- By definition of divisors, we can rewrite the sum over the divisors of $Q_t$ as a sum over the subsets of $\{1, \dots, t\}$.
    have h_divisors_subsets : Nat.divisors (Q t) = Finset.image (fun S => ∏ i ∈ S, Nat.nth Nat.Prime i) (Finset.powerset (Finset.range t)) := by
      unfold Q;
      induction ( Finset.range t ) using Finset.induction <;> simp_all +decide [ Nat.divisors_mul ];
      rw [ Nat.Prime.divisors ( Nat.prime_nth_prime _ ) ];
      rw [ Finset.powerset_insert ];
      ext; simp [Finset.mem_mul, Finset.mem_image];
      grind;
    rw [ h_divisors_subsets, Finset.sum_image ];
    · refine' Finset.sum_congr rfl fun S hS => _;
      rw [ h_divisors _ ( h_divisors_subsets.symm ▸ Finset.mem_image_of_mem _ hS ) ];
      simp +decide [ Finset.prod_ite, Nat.Prime.dvd_iff_not_coprime ];
      refine' Finset.prod_bij ( fun x hx => x ) _ _ _ _ <;> simp_all +decide [ Nat.coprime_prod_right_iff ];
      · intro a ha x hx; rw [ Nat.gcd_comm ] ; simp_all +decide [ Nat.coprime_primes ] ;
        intro h; have := Nat.nth_injective ( Nat.infinite_setOf_prime ) h; aesop;
      · exact fun x hx => ⟨ Finset.mem_range.mp ( hS hx ), x, hx, by simp +decide [ Nat.Prime.ne_one ] ⟩;
    · intros S hS T hT h_eq; apply_fun fun x => x.primeFactors at h_eq; simp_all +decide [ Finset.subset_iff ] ;
      simp_all +decide [ Finset.ext_iff, Set.subset_def ];
      intro x; specialize h_eq ( Nat.nth Nat.Prime x ) ( Nat.prime_nth_prime x ) ; simp_all +decide [ Nat.Prime.dvd_iff_not_coprime, Nat.coprime_prod_right_iff ] ;
      simp_all +decide [ Nat.coprime_primes, Finset.prod_eq_zero_iff, Nat.Prime.ne_zero ];
      exact ⟨ fun hx => h_eq.mp ⟨ x, hx, rfl ⟩ |> fun ⟨ y, hy, hy' ⟩ => by have := Nat.nth_injective ( Nat.infinite_setOf_prime ) hy'; aesop, fun hx => h_eq.mpr ⟨ x, hx, rfl ⟩ |> fun ⟨ y, hy, hy' ⟩ => by have := Nat.nth_injective ( Nat.infinite_setOf_prime ) hy'; aesop ⟩;
  -- Therefore, $\sum_{S\subseteq\{1,\dots,t\}}\ \prod_{i\in S}\left(1-\frac1{p_i}\right)=\prod_{i=1}^t\left(1+\left(1-\frac1{p_i}\right)\right)$.
  have h_sum_powerset : ∑ S ∈ Finset.powerset (Finset.range t), (∏ i ∈ S, (1 - 1 / (Nat.nth Nat.Prime i : ℚ))) = ∏ i ∈ Finset.range t, (1 + (1 - 1 / (Nat.nth Nat.Prime i : ℚ))) := by
    simp +decide [ add_comm ( 1 : ℚ ), Finset.prod_add ];
  rw [ h_sum_divisors, h_sum_powerset ];
  field_simp;
  rw [ Finset.prod_congr rfl fun _ _ => show ( 1 + ( 1 - 1 / ( Nat.nth Nat.Prime _ : ℚ ) ) ) = 2 * ( ( 2 - 1 / ( Nat.nth Nat.Prime _ : ℚ ) ) / 2 ) by ring, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range ]

/-
Lemma 3: The sum of the reciprocals of the primes diverges to infinity.
-/
lemma lem_sumrecipprimes : Filter.Tendsto (fun N => ∑ p ∈ Finset.filter Nat.Prime (Finset.range N), 1 / (p : ℝ)) Filter.atTop Filter.atTop := by
  -- By contradiction, assume the sum of the reciprocals of the primes converges.
  by_contra h_contra
  have h_sum_finite : Summable (fun p : ℕ => if Nat.Prime p then (1 : ℝ) / p else 0) := by
    rw [ summable_iff_not_tendsto_nat_atTop_of_nonneg ];
    · simpa [ Finset.sum_filter ] using h_contra;
    · intro n; split_ifs <;> positivity;
  -- Consider the product $\prod_{p \leq N} (1 + \frac{1}{p} + \frac{1}{p^2} + \cdots)$.
  have h_prod : Filter.Tendsto (fun N : ℕ => ∏ p ∈ Finset.filter Nat.Prime (Finset.range (N + 1)), (1 - (1 : ℝ) / p)⁻¹) Filter.atTop Filter.atTop := by
    -- We know that $\prod_{p \leq N} (1 + \frac{1}{p} + \frac{1}{p^2} + \cdots)$ is greater than or equal to $\sum_{n \leq N} \frac{1}{n}$.
    have h_prod_ge_harmonic : ∀ N : ℕ, ∏ p ∈ Finset.filter Nat.Prime (Finset.range (N + 1)), (1 - (1 : ℝ) / p)⁻¹ ≥ ∑ n ∈ Finset.Icc 1 N, (1 : ℝ) / n := by
      -- By definition of product, we know that $\prod_{p \leq N} (1 + \frac{1}{p} + \frac{1}{p^2} + \cdots)$ is greater than or equal to $\sum_{n \leq N} \frac{1}{n}$.
      intros N
      have h_prod_ge_harmonic_step : ∏ p ∈ Finset.filter Nat.Prime (Finset.range (N + 1)), (∑ k ∈ Finset.range (Nat.log p N + 1), (1 : ℝ) / p ^ k) ≥ ∑ n ∈ Finset.Icc 1 N, (1 : ℝ) / n := by
        -- Every integer $n \leq N$ can be written as a product of prime powers $p^k \leq N$.
        have h_decomp : ∀ n ∈ Finset.Icc 1 N, (∃ f : ℕ → ℕ, (∀ p, Nat.Prime p → f p ≤ Nat.log p N) ∧ n = ∏ p ∈ Finset.filter Nat.Prime (Finset.range (N + 1)), p ^ f p) := by
          intro n hn
          use fun p => Nat.factorization n p;
          norm_num +zetaDelta at *;
          refine' ⟨ fun p pp => Nat.le_log_of_pow_le pp.one_lt <| Nat.le_trans ( Nat.le_of_dvd hn.1 <| Nat.ordProj_dvd _ _ ) hn.2, _ ⟩;
          conv_lhs => rw [ ← Nat.factorization_prod_pow_eq_self ( by linarith : n ≠ 0 ) ] ;
          rw [ Finsupp.prod_of_support_subset ] <;> norm_num;
          exact fun p hp => Finset.mem_filter.mpr ⟨ Finset.mem_range.mpr ( by linarith [ Nat.le_of_mem_primeFactors hp ] ), Nat.prime_of_mem_primeFactors hp ⟩;
        choose! f hf1 hf2 using h_decomp;
        -- By definition of $f$, we can rewrite the sum $\sum_{n \leq N} \frac{1}{n}$ as $\sum_{n \leq N} \prod_{p \leq N} \frac{1}{p^{f(n, p)}}$.
        have h_sum_rewrite : ∑ n ∈ Finset.Icc 1 N, (1 : ℝ) / n = ∑ n ∈ Finset.Icc 1 N, ∏ p ∈ Finset.filter Nat.Prime (Finset.range (N + 1)), (1 : ℝ) / p ^ f n p := by
          refine Finset.sum_congr rfl fun n hn => ?_;
          rw [ hf2 n hn, Nat.cast_prod ];
          simp +decide [ ← hf2 n hn ];
        rw [ h_sum_rewrite, Finset.prod_sum ];
        refine' le_trans _ ( Finset.sum_le_sum_of_subset_of_nonneg _ fun _ _ _ => Finset.prod_nonneg fun _ _ => by positivity );
        rotate_left;
        exact Finset.image ( fun n => fun p hp => f n p ) ( Finset.Icc 1 N );
        · norm_num [ Finset.image_subset_iff ];
          exact fun n hn hn' p hp hp' => Nat.lt_succ_of_le ( hf1 n ( Finset.mem_Icc.mpr ⟨ hn, hn' ⟩ ) p hp' );
        · rw [ Finset.sum_image ];
          · exact Finset.sum_le_sum fun _ _ => by rw [ ← Finset.prod_attach ] ;
          · intros n hn m hm hnm;
            rw [ hf2 n hn, hf2 m hm ];
            exact Finset.prod_congr rfl fun p hp => congr_arg _ ( congr_fun ( congr_fun hnm p ) hp );
      refine le_trans h_prod_ge_harmonic_step ?_;
      gcongr;
      rw [ ← tsum_geometric_of_lt_one ( by positivity ) ( by simpa using inv_lt_one_of_one_lt₀ <| Nat.one_lt_cast.mpr <| Nat.Prime.one_lt <| Finset.mem_filter.mp ‹_› |>.2 ) ];
      simp +zetaDelta at *;
      exact Summable.sum_le_tsum ( Finset.range ( Nat.log _ _ + 1 ) ) ( fun _ _ => by positivity ) ( by simpa using summable_geometric_of_lt_one ( by positivity ) ( inv_lt_one_of_one_lt₀ <| Nat.one_lt_cast.mpr <| Nat.Prime.one_lt <| by tauto ) );
    refine' Filter.tendsto_atTop_mono h_prod_ge_harmonic _;
    have h_harmonic_diverges : Filter.Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, (1 : ℝ) / (n + 1)) Filter.atTop Filter.atTop := by
      exact not_summable_iff_tendsto_nat_atTop_of_nonneg ( fun _ => by positivity ) |>.1 ( by exact_mod_cast mt ( summable_nat_add_iff 1 |>.1 ) Real.not_summable_one_div_natCast );
    exact h_harmonic_diverges.congr fun N => by erw [ Finset.sum_Ico_eq_sub _ _ ] <;> norm_num [ Finset.sum_range_succ' ] ;
  -- Since $\prod_{p \leq N} (1 + \frac{1}{p} + \frac{1}{p^2} + \cdots)$ is bounded above by $\exp(\sum_{p \leq N} \frac{2}{p})$, and $\sum_{p \leq N} \frac{2}{p}$ converges, we have a contradiction.
  have h_exp_bound : ∀ N : ℕ, ∏ p ∈ Finset.filter Nat.Prime (Finset.range (N + 1)), (1 - (1 : ℝ) / p)⁻¹ ≤ Real.exp (∑ p ∈ Finset.filter Nat.Prime (Finset.range (N + 1)), (2 : ℝ) / p) := by
    -- For each prime $p$, we have $(1 - \frac{1}{p})^{-1} \leq \exp(\frac{2}{p})$.
    have h_prime_bound : ∀ p : ℕ, Nat.Prime p → (1 - (1 : ℝ) / p)⁻¹ ≤ Real.exp (2 / p) := by
      intro p hp; rw [ inv_eq_one_div, div_le_iff₀ ] <;> ring_nf;
      · nlinarith [ Real.add_one_le_exp ( ( p : ℝ ) ⁻¹ * 2 ), inv_pos.mpr ( show 0 < ( p : ℝ ) by exact Nat.cast_pos.mpr hp.pos ), mul_inv_cancel₀ ( show ( p : ℝ ) ≠ 0 by exact Nat.cast_ne_zero.mpr hp.ne_zero ), show ( p : ℝ ) ≥ 2 by exact Nat.cast_le.mpr hp.two_le ];
      · exact sub_pos_of_lt ( inv_lt_one_of_one_lt₀ ( mod_cast hp.one_lt ) );
    exact fun N => by rw [ Real.exp_sum ] ; exact Finset.prod_le_prod ( fun _ _ => inv_nonneg.2 <| sub_nonneg.2 <| div_le_self zero_le_one <| mod_cast Nat.Prime.pos <| by aesop ) fun _ _ => h_prime_bound _ <| by aesop;
  have h_exp_bound : Filter.Tendsto (fun N : ℕ => Real.exp (∑ p ∈ Finset.filter Nat.Prime (Finset.range (N + 1)), (2 : ℝ) / p)) Filter.atTop Filter.atTop → False := by
    norm_num [ div_eq_mul_inv, Finset.mul_sum _ _ _ ] at *;
    exact fun h => not_tendsto_atTop_of_tendsto_nhds ( by simpa [ Finset.sum_filter ] using h_sum_finite.mul_left 2 |> Summable.hasSum |> HasSum.tendsto_sum_nat |> Filter.Tendsto.comp <| Filter.tendsto_add_atTop_nat 1 ) h;
  exact h_exp_bound <| Filter.tendsto_atTop_mono ( by aesop ) h_prod

/-
Lemma 4: The product of (1 - 1/(2p_i)) for i from 1 to t tends to 0 as t tends to infinity.
-/
lemma lem_product0 : Filter.Tendsto (fun t => (Finset.range t).prod (fun i => 1 - 1 / (2 * (Nat.nth Nat.Prime i : ℚ)))) Filter.atTop (nhds 0) := by
  -- By Lemma 3, the series $\sum_{i=1}^\infty \frac{1}{2p_i}$ diverges.
  have h_sum_diverges : Filter.Tendsto (fun t => ∑ i ∈ Finset.range t, (1 / (2 * Nat.nth Nat.Prime i : ℝ))) Filter.atTop Filter.atTop := by
    -- By Lemma 3, the series $\sum_{i=1}^\infty \frac{1}{p_i}$ diverges.
    have h_sum_diverges : Filter.Tendsto (fun t => ∑ i ∈ Finset.range t, (1 / (Nat.nth Nat.Prime i : ℝ))) Filter.atTop Filter.atTop := by
      have h_reciprocals : Filter.Tendsto (fun N => ∑ p ∈ Finset.filter Nat.Prime (Finset.range N), (1 / (p : ℝ))) Filter.atTop Filter.atTop := by
        exact lem_sumrecipprimes
      have h_reciprocals : ∀ t : ℕ, ∑ i ∈ Finset.range t, (1 / (Nat.nth Nat.Prime i : ℝ)) ≥ ∑ p ∈ Finset.filter Nat.Prime (Finset.range (Nat.nth Nat.Prime t)), (1 / (p : ℝ)) := by
        intros t
        have h_subset : Finset.filter Nat.Prime (Finset.range (Nat.nth Nat.Prime t)) ⊆ Finset.image (Nat.nth Nat.Prime) (Finset.range t) := by
          intros p hp;
          norm_num +zetaDelta at *;
          refine' ⟨ Nat.count ( Nat.Prime ) p, _, _ ⟩;
          · contrapose! hp;
            intro h; exact fun h' => hp.not_lt <| Nat.lt_of_not_ge fun h'' => h.not_le <| Nat.le_of_lt_succ <| by linarith [ Nat.nth_count h', Nat.nth_monotone ( Nat.infinite_setOf_prime ) h'' ] ;
          · rw [ Nat.nth_count ] ; aesop;
        exact le_trans ( Finset.sum_le_sum_of_subset_of_nonneg h_subset fun _ _ _ => by positivity ) ( by rw [ Finset.sum_image <| by intros a ha b hb hab; simpa using Nat.nth_injective ( Nat.infinite_setOf_prime ) hab ] );
      exact Filter.tendsto_atTop_mono h_reciprocals <| by rename_i h; exact h.comp <| Nat.nth_strictMono ( Nat.infinite_setOf_prime ) |> StrictMono.tendsto_atTop;
    simpa [ Finset.mul_sum _ _ _, mul_comm ] using h_sum_diverges.const_mul_atTop ( by norm_num : ( 0 : ℝ ) < 1 / 2 );
  -- Therefore, $\prod_{i=1}^\infty (1 - \frac{1}{2p_i})$ converges to 0.
  have h_prod_zero : Filter.Tendsto (fun t => ∏ i ∈ Finset.range t, (1 - 1 / (2 * Nat.nth Nat.Prime i : ℝ))) Filter.atTop (nhds 0) := by
    -- We'll use the fact that if the sum of the reciprocals of the primes diverges, then the product of (1 - 1/(2p_i)) tends to 0.
    have h_prod_zero : ∀ t : ℕ, (∏ i ∈ Finset.range t, (1 - 1 / (2 * (Nat.nth Nat.Prime i) : ℝ))) ≤ Real.exp (-∑ i ∈ Finset.range t, (1 / (2 * (Nat.nth Nat.Prime i) : ℝ))) := by
      -- We'll use the fact that $1 - x \leq e^{-x}$ for all $x$.
      have h_exp : ∀ x : ℝ, 0 < x ∧ x < 1 → (1 - x) ≤ Real.exp (-x) := by
        exact fun x hx => by linarith [ Real.add_one_le_exp ( -x ) ] ;
      exact fun t => le_trans ( Finset.prod_le_prod ( fun _ _ => sub_nonneg.2 <| div_le_one_of_le₀ ( by norm_cast; linarith [ Nat.Prime.two_le <| Nat.prime_nth_prime ‹_› ] ) <| by positivity ) fun _ _ => h_exp _ ⟨ by exact one_div_pos.2 <| mul_pos zero_lt_two <| Nat.cast_pos.2 <| Nat.Prime.pos <| Nat.prime_nth_prime _, by exact div_lt_one ( by norm_cast; linarith [ Nat.Prime.two_le <| Nat.prime_nth_prime ‹_› ] ) |>.2 <| by norm_cast; linarith [ Nat.Prime.two_le <| Nat.prime_nth_prime ‹_› ] ⟩ ) <| by rw [ ← Real.exp_sum ] ; norm_num;
    exact squeeze_zero ( fun t => Finset.prod_nonneg fun _ _ => sub_nonneg.2 <| div_le_self zero_le_one <| by norm_cast; linarith [ Nat.Prime.two_le <| Nat.prime_nth_prime ‹_› ] ) h_prod_zero <| Real.tendsto_exp_atBot.comp <| Filter.tendsto_neg_atTop_atBot.comp h_sum_diverges;
  convert h_prod_zero using 1;
  norm_num [ tendsto_iff_norm_sub_tendsto_zero ];
  norm_num [ Norm.norm ]

/-
Lemma 5: If a sequence a_k in [0,1] has block sums bounded by c_t * 2^t where c_t -> 0, then the Cesaro average of a_k tends to 0.
-/
lemma lem_block (a : ℕ → ℝ) (c : ℕ → ℝ)
    (h_bound : ∀ k, 0 ≤ a k ∧ a k ≤ 1)
    (h_c_nonneg : ∀ t, 0 ≤ c t)
    (h_c_to_zero : Filter.Tendsto c Filter.atTop (nhds 0))
    (h_sum : ∀ t ≥ 1, ∑ k ∈ Finset.Icc (2^t - 1) (2^(t+1) - 2), a k ≤ c t * (2^t : ℝ)) :
    Filter.Tendsto (fun N : ℕ => (1 / N : ℝ) * ∑ k ∈ Finset.Icc 1 N, a k) Filter.atTop (nhds 0) := by
  -- By Lemma 5, it suffices to show that the limit of the average of the $a_k$'s is bounded by the limit of the average of the $c_t$'s.
  suffices h_suff : Filter.Tendsto (fun t : ℕ => (∑ k ∈ Finset.Icc 1 (2 ^ (t + 1) - 2), a k) / (2 ^ (t + 1) - 2 : ℝ)) Filter.atTop (nhds 0) by
    -- By the properties of the average, if the average of the $a_k$'s over the intervals $[2^t - 1, 2^{t+1} - 2]$ tends to 0, then the average of the $a_k$'s over the entire range also tends to 0.
    have h_avg : ∀ N : ℕ, (∑ k ∈ Finset.Icc 1 N, a k) ≤ (∑ k ∈ Finset.Icc 1 (2 ^ (Nat.log 2 N + 1 + 1) - 2), a k) := by
      intro N; gcongr ; aesop;
      exact Nat.le_sub_of_add_le ( by rw [ Nat.pow_succ ] ; linarith [ Nat.lt_pow_of_log_lt one_lt_two ( by linarith : Nat.log 2 N < Nat.log 2 N + 1 ) ] );
    -- Using the bound from h_avg, we can show that the average of the $a_k$'s over the entire range is bounded by the average of the $a_k$'s over the intervals $[2^t - 1, 2^{t+1} - 2]$.
    have h_avg_bound : ∀ N : ℕ, N ≥ 1 → (∑ k ∈ Finset.Icc 1 N, a k) / (N : ℝ) ≤ (∑ k ∈ Finset.Icc 1 (2 ^ (Nat.log 2 N + 1 + 1) - 2), a k) / (2 ^ (Nat.log 2 N + 1 + 1) - 2 : ℝ) * 4 := by
      intros N hN
      have h_avg_bound_step : (2 ^ (Nat.log 2 N + 1 + 1) - 2 : ℝ) ≥ N / 4 := by
        have := Nat.lt_pow_succ_log_self ( by decide : 1 < 2 ) N;
        norm_num [ pow_succ' ] at * ; linarith [ ( by norm_cast : ( N : ℝ ) + 1 ≤ 2 * 2 ^ Nat.log 2 N ) ];
      rw [ div_mul_eq_mul_div, div_le_div_iff₀ ] <;> try positivity;
      · have := h_avg N;
        rw [ mul_assoc ];
        gcongr;
        · exact sub_nonneg_of_le ( by exact le_trans ( by norm_num ) ( pow_le_pow_right₀ ( by norm_num ) ( Nat.succ_le_succ ( Nat.succ_le_succ ( Nat.zero_le _ ) ) ) ) );
        · exact Finset.sum_nonneg fun _ _ => h_bound _ |>.1;
        · norm_num [ pow_succ' ];
          exact_mod_cast ( by linarith [ Nat.pow_log_le_self 2 ( by linarith : N ≠ 0 ) ] : ( 2 : ℕ ) * ( 2 * 2 ^ Nat.log 2 N ) ≤ 4 * N + 2 );
      · exact lt_of_lt_of_le ( by positivity ) h_avg_bound_step;
    -- Since the average of the $a_k$'s over the intervals $[2^t - 1, 2^{t+1} - 2]$ tends to 0, multiplying by 4 preserves the limit.
    have h_avg_mul : Filter.Tendsto (fun N : ℕ => (∑ k ∈ Finset.Icc 1 (2 ^ (Nat.log 2 N + 1 + 1) - 2), a k) / (2 ^ (Nat.log 2 N + 1 + 1) - 2 : ℝ) * 4) Filter.atTop (nhds 0) := by
      simpa using Filter.Tendsto.mul ( h_suff.comp ( Filter.tendsto_add_atTop_nat 1 |> Filter.Tendsto.comp <| Filter.tendsto_atTop_atTop.mpr fun x => ⟨ 2 ^ x, fun n hn => Nat.le_log_of_pow_le ( by norm_num ) hn ⟩ ) ) tendsto_const_nhds;
    refine' squeeze_zero_norm' _ h_avg_mul;
    filter_upwards [ Filter.eventually_ge_atTop 1 ] with N hN using by rw [ Real.norm_of_nonneg ( mul_nonneg ( by positivity ) ( Finset.sum_nonneg fun _ _ => h_bound _ |>.1 ) ) ] ; simpa [ div_eq_inv_mul ] using h_avg_bound N hN;
  -- By Lemma 5, it suffices to show that the limit of the average of the $a_k$'s is bounded by the limit of the average of the $c_t$'s. Hence, we need to show that:
  suffices h_suff : Filter.Tendsto (fun t : ℕ => (∑ j ∈ Finset.range t, c (j + 1) * 2 ^ (j + 1)) / (2 ^ (t + 1) - 2 : ℝ)) Filter.atTop (nhds 0) by
    -- By Lemma 5, it suffices to show that the average of the $a_k$'s is bounded above by the average of the $c_t$'s.
    have h_bound : ∀ t ≥ 1, (∑ k ∈ Finset.Icc 1 (2 ^ (t + 1) - 2), a k) ≤ (∑ j ∈ Finset.range t, c (j + 1) * 2 ^ (j + 1)) := by
      intros t ht
      induction' ht with t ht ih;
      · simpa using h_sum 1 le_rfl;
      · have := h_sum ( t + 1 ) ( Nat.le_succ_of_le ht );
        erw [ Finset.sum_Ico_eq_sub _ _ ] at * <;> norm_num [ Finset.sum_range_succ ] at *;
        · rw [ show ( 2 ^ ( t + 1 ) - 1 : ℕ ) = ( 2 ^ ( t + 1 ) - 2 ) + 1 by exact Nat.sub_eq_of_eq_add <| by linarith [ Nat.sub_add_cancel <| show 2 ≤ 2 ^ ( t + 1 ) from le_trans ( by norm_num ) <| pow_le_pow_right₀ ( by norm_num ) <| Nat.succ_le_succ ht ] ] at this ; norm_num [ Finset.sum_range_succ ] at * ; linarith;
        · ring_nf;
          linarith [ pow_pos ( zero_lt_two' ℝ ) t, Nat.sub_add_cancel ( show 2 ≤ 2 ^ t * 4 from by linarith [ pow_pos ( zero_lt_two' ℕ ) t ] ) ];
    refine' squeeze_zero_norm' _ h_suff;
    filter_upwards [ Filter.eventually_ge_atTop 1 ] with t ht using by rw [ Real.norm_of_nonneg ( div_nonneg ( Finset.sum_nonneg fun _ _ => by linarith [ ‹∀ k, 0 ≤ a k ∧ a k ≤ 1› ‹_› ] ) ( sub_nonneg.mpr ( by linarith [ pow_le_pow_right₀ ( by norm_num : ( 1 : ℝ ) ≤ 2 ) ( by linarith : t + 1 ≥ 1 ) ] ) ) ) ] ; exact div_le_div_of_nonneg_right ( h_bound t ht ) ( sub_nonneg.mpr ( by linarith [ pow_le_pow_right₀ ( by norm_num : ( 1 : ℝ ) ≤ 2 ) ( by linarith : t + 1 ≥ 1 ) ] ) ) ;
  -- We'll use the fact that if the denominator grows much faster than the numerator, the quotient tends to zero.
  have h_dominate : ∀ ε > 0, ∃ N : ℕ, ∀ t ≥ N, (∑ j ∈ Finset.range t, c (j + 1) * 2 ^ (j + 1)) ≤ (ε / 2) * (2 ^ (t + 1) - 2) := by
    intro ε hε_pos
    obtain ⟨N₀, hN₀⟩ : ∃ N₀ : ℕ, ∀ t ≥ N₀, c (t + 1) ≤ ε / 4 := by
      exact Filter.eventually_atTop.mp ( h_c_to_zero.eventually ( ge_mem_nhds <| by linarith ) ) |> fun ⟨ N₀, hN₀ ⟩ => ⟨ N₀, fun t ht => hN₀ _ <| Nat.le_succ_of_le ht ⟩;
    -- We can bound the sum $\sum_{j=0}^{t-1} c_{j+1} 2^{j+1}$ by splitting it into two parts: the sum up to $N₀$ and the sum from $N₀$ to $t-1$.
    have h_split_sum : ∀ t ≥ N₀, (∑ j ∈ Finset.range t, c (j + 1) * 2 ^ (j + 1)) ≤ (∑ j ∈ Finset.range N₀, c (j + 1) * 2 ^ (j + 1)) + (∑ j ∈ Finset.Ico N₀ t, (ε / 4) * 2 ^ (j + 1)) := by
      intro t ht; rw [ ← Finset.sum_range_add_sum_Ico _ ht ] ; exact add_le_add_left ( Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_right ( hN₀ i <| Finset.mem_Ico.mp hi |>.1 ) <| by positivity ) _;
    -- We can bound the sum $\sum_{j=N₀}^{t-1} \frac{\epsilon}{4} 2^{j+1}$ by a geometric series.
    have h_geo_series : ∀ t ≥ N₀, (∑ j ∈ Finset.Ico N₀ t, (ε / 4) * 2 ^ (j + 1)) ≤ (ε / 4) * (2 ^ (t + 1) - 2 ^ (N₀ + 1)) := by
      intro t ht; rw [ Finset.sum_Ico_eq_sum_range ] ; norm_num [ pow_succ', ← Finset.mul_sum _ _ _ ] ; ring_nf; norm_num;
      rw [ ← Finset.mul_sum _ _ _, geom_sum_eq ] <;> ring_nf <;> norm_num;
      rw [ mul_assoc, ← pow_add, Nat.add_sub_of_le ht ];
    -- Choose $N$ such that for all $t \geq N$, the sum $\sum_{j=0}^{N₀-1} c_{j+1} 2^{j+1}$ is less than $\frac{\epsilon}{4} (2^{t+1} - 2)$.
    obtain ⟨N₁, hN₁⟩ : ∃ N₁ : ℕ, ∀ t ≥ N₁, (∑ j ∈ Finset.range N₀, c (j + 1) * 2 ^ (j + 1)) ≤ (ε / 4) * (2 ^ (t + 1) - 2) := by
      have h_geo_series : Filter.Tendsto (fun t : ℕ => (ε / 4) * (2 ^ (t + 1) - 2)) Filter.atTop Filter.atTop := by
        exact Filter.Tendsto.const_mul_atTop ( by positivity ) ( Filter.tendsto_atTop_add_const_right _ _ ( tendsto_pow_atTop_atTop_of_one_lt one_lt_two |> Filter.Tendsto.comp <| Filter.tendsto_add_atTop_nat _ ) );
      exact Filter.eventually_atTop.mp ( h_geo_series.eventually_ge_atTop ( ∑ j ∈ Finset.range N₀, c ( j + 1 ) * 2 ^ ( j + 1 ) ) );
    exact ⟨ Max.max N₀ N₁, fun t ht => by nlinarith [ h_split_sum t ( le_trans ( le_max_left _ _ ) ht ), h_geo_series t ( le_trans ( le_max_left _ _ ) ht ), hN₁ t ( le_trans ( le_max_right _ _ ) ht ), pow_pos ( zero_lt_two' ℝ ) ( t + 1 ), pow_le_pow_right₀ ( by norm_num : ( 1 : ℝ ) ≤ 2 ) ( show N₀ + 1 ≥ 1 by norm_num ) ] ⟩;
  rw [ Metric.tendsto_nhds ];
  simp +zetaDelta at *;
  intro ε hε; obtain ⟨ N, hN ⟩ := h_dominate ε hε; exact ⟨ N + 1, fun n hn => by rw [ abs_of_nonneg ( Finset.sum_nonneg fun _ _ => mul_nonneg ( h_c_nonneg _ ) ( pow_nonneg zero_le_two _ ) ), abs_of_nonneg ( sub_nonneg.mpr ( by linarith [ pow_le_pow_right₀ ( by norm_num : ( 1 : ℝ ) ≤ 2 ) ( show n + 1 ≥ 2 by linarith ) ] ) ) ] ; rw [ div_lt_iff₀ ] <;> nlinarith [ hN n ( by linarith ), pow_le_pow_right₀ ( by norm_num : ( 1 : ℝ ) ≤ 2 ) ( show n + 1 ≥ 2 by linarith ) ] ⟩ ;

/-
A_val(t) tends to 0 as t tends to infinity.
-/
noncomputable def A_val (t : ℕ) : ℝ := (Finset.range t).prod (fun i => 1 - 1 / (2 * (Nat.nth Nat.Prime i : ℝ)))

lemma A_val_tendsto_zero : Filter.Tendsto A_val Filter.atTop (nhds 0) := by
  convert lem_product0 using 1;
  norm_num [ Metric.tendsto_nhds, A_val ];
  norm_num [ Norm.norm ]

/-
r_seq(t+1) is a prime strictly greater than max(r_seq(t)*Q(t), Q(t+1), ceil(1/A_val(t+1))).
-/
noncomputable def r_seq : ℕ → ℕ
| 0 => 2
| t + 1 => Nat.find (Nat.exists_infinite_primes (max (r_seq t * Q t) (max (Q (t + 1)) (Nat.ceil (1 / A_val (t + 1)))) + 1))

lemma r_seq_spec (t : ℕ) :
    let R := max (r_seq t * Q t) (max (Q (t + 1)) (Nat.ceil (1 / A_val (t + 1))))
    r_seq (t + 1) > R ∧ (r_seq (t + 1)).Prime := by
  have h_r_seq_gt : r_seq (t + 1) > max (r_seq t * Q t) (max (Q (t + 1)) ⌈1 / A_val (t + 1)⌉₊) := by
    exact Nat.find_spec ( Nat.exists_infinite_primes ( Max.max ( r_seq t * Q t ) ( Max.max ( Q ( t + 1 ) ) ⌈1 / A_val ( t + 1 ) ⌉₊ ) + 1 ) ) |>.1.trans_lt' ( Nat.lt_succ_self _ );
  exact ⟨ h_r_seq_gt, Nat.find_spec ( Nat.exists_infinite_primes _ ) |>.2 ⟩

/-
Definition of the sequence n_seq.
-/
noncomputable def n_seq (k : ℕ) : ℕ :=
  if k = 0 then 1 else
  let t := Nat.log 2 (k + 1)
  let j := k - (2^t - 2)
  let divisors := (Nat.divisors (Q t)).sort (· ≤ ·)
  r_seq t * divisors.get! (j - 1)

/-
n_seq is strictly increasing within each block.
-/
lemma n_seq_block_mono (t : ℕ) (k : ℕ)
    (hk1 : 2^t - 1 ≤ k) (hk2 : k + 1 ≤ 2^(t+1) - 2) :
    n_seq k < n_seq (k + 1) := by
  -- Since $k$ and $k+1$ are in the same block $I_t$, they have the same $t = \lfloor \log_2(k+1) \rfloor = \lfloor \log_2(k+2) \rfloor$.
  set t' := Nat.log 2 (k + 1)
  have ht'_eq : t' = t := by
    refine' Nat.log_eq_iff ( by norm_num ) |>.2 ⟨ _, _ ⟩;
    · omega;
    · omega;
  unfold n_seq;
  by_cases hk : k = 0 <;> simp_all +decide [ Nat.pow_succ' ];
  · omega;
  · rw [ show Nat.log 2 ( k + 1 + 1 ) = t from _ ];
    · -- Since the divisors are sorted strictly increasingly, we have $d_{t, j} < d_{t, j+1}$.
      have h_divisors_strict_mono : ∀ j < (Nat.divisors (Q t)).card - 1, (Finset.sort (· ≤ ·) (Nat.divisors (Q t)))[j]?.getD 0 < (Finset.sort (· ≤ ·) (Nat.divisors (Q t)))[j + 1]?.getD 0 := by
        intros j hj_lt
        have h_sorted : List.Pairwise (· < ·) (Finset.sort (· ≤ ·) (Nat.divisors (Q t))) := by
          convert Finset.sort_sorted_lt _;
        have := List.pairwise_iff_get.mp h_sorted;
        by_cases hj : j < List.length (Finset.sort (· ≤ ·) (Nat.divisors (Q t))) <;> by_cases hj' : j + 1 < List.length (Finset.sort (· ≤ ·) (Nat.divisors (Q t))) <;> simp_all +decide
        · exact this ⟨ j, by linarith ⟩ ⟨ j + 1, by linarith ⟩ ( Nat.lt_succ_self _ );
        · omega;
        · omega;
        · omega;
      convert mul_lt_mul_of_pos_left ( h_divisors_strict_mono ( k - ( 2 ^ t - 2 ) - 1 ) _ ) ( Nat.Prime.pos ( show Nat.Prime ( r_seq t ) from ?_ ) ) using 1;
      · grind;
      · rw [ show k + 1 - ( 2 ^ t - 2 ) - 1 = k - ( 2 ^ t - 2 ) - 1 + 1 from by omega ];
      · -- Since $Q(t)$ is the product of the first $t$ primes, the number of divisors of $Q(t)$ is $2^t$.
        have h_divisors_card : (Nat.divisors (Q t)).card = 2 ^ t := by
          -- Since $Q(t)$ is the product of the first $t$ primes, the number of divisors of $Q(t)$ is $2^t$ by definition.
          have h_divisors_card : (Nat.divisors (Finset.prod (Finset.range t) (fun i => Nat.nth Nat.Prime i))).card = Finset.prod (Finset.range t) (fun i => (Nat.divisors (Nat.nth Nat.Prime i)).card) := by
            have h_divisors_card : ∀ {a b : ℕ}, Nat.gcd a b = 1 → (Nat.divisors (a * b)).card = (Nat.divisors a).card * (Nat.divisors b).card := by
              exact fun {a b} a_1 => Nat.Coprime.card_divisors_mul a_1;
            induction' t with t ih;
            · norm_num;
            · induction' t + 1 with t ih <;> simp_all +decide [ Finset.prod_range_succ ];
              rw [ h_divisors_card, ih ];
              exact Nat.Coprime.prod_left fun i hi => Nat.coprime_comm.mp <| Nat.Prime.coprime_iff_not_dvd ( Nat.prime_nth_prime _ ) |>.2 <| Nat.not_dvd_of_pos_of_lt ( Nat.Prime.pos <| Nat.prime_nth_prime _ ) <| Nat.nth_strictMono ( Nat.infinite_setOf_prime ) <| Finset.mem_range.mp hi;
          simp_all +decide [ Nat.Prime.divisors ];
          exact h_divisors_card.trans ( by rw [ Finset.prod_congr rfl fun _ _ => Finset.card_pair <| ne_of_lt <| Nat.Prime.one_lt <| Nat.prime_nth_prime _ ] ; norm_num );
        omega;
      · induction t <;> simp_all +decide
        exact Nat.find_spec ( Nat.exists_infinite_primes _ ) |>.2;
    · rw [ Nat.log_eq_iff ] at * <;> norm_num at * ; omega

/-
The last element of block t is strictly less than the first element of block t+1.
-/
lemma n_seq_block_transition (t : ℕ) :
    n_seq (2^(t+1) - 2) < n_seq (2^(t+1) - 1) := by
  unfold n_seq;
  -- Let's simplify the expressions for the indices.
  have h_indices : Nat.log 2 (2 ^ (t + 1) - 2 + 1) = t ∧ Nat.log 2 (2 ^ (t + 1) - 1 + 1) = t + 1 := by
    constructor;
    · rw [ Nat.log_eq_iff ] <;> norm_num [ Nat.pow_succ' ];
      exact ⟨ by linarith [ Nat.sub_add_cancel ( show 2 ≤ 2 * 2 ^ t from by linarith [ Nat.one_le_pow t 2 zero_lt_two ] ), Nat.one_le_pow t 2 zero_lt_two ], by linarith [ Nat.sub_add_cancel ( show 2 ≤ 2 * 2 ^ t from by linarith [ Nat.one_le_pow t 2 zero_lt_two ] ) ] ⟩;
    · rw [ Nat.sub_add_cancel ( Nat.one_le_pow _ _ ( by decide ) ), Nat.log_pow ( by decide ) ];
  rcases n : 2 ^ t with ( _ | _ | k ) <;> simp_all +decide [ Nat.pow_succ' ];
  · norm_num [ ← h_indices.1 ] at *;
    unfold Q; simp +arith +decide
    exact le_trans ( by decide ) ( Nat.mul_le_mul ( Nat.Prime.two_le ( r_seq_spec 0 |>.2 ) ) ( Nat.one_le_iff_ne_zero.mpr <| by native_decide ) );
  · simp +arith +decide [ Nat.mul_succ ];
    refine' lt_of_le_of_lt _ ( mul_lt_mul_of_pos_right ( r_seq_spec t |>.1 ) _ );
    · refine' le_trans _ ( Nat.mul_le_mul_right _ <| le_max_left _ _ );
      refine' le_trans _ ( Nat.mul_le_mul_left _ <| Nat.one_le_iff_ne_zero.mpr _ );
      · simp +arith +decide [ Nat.sub_sub ];
        refine' Nat.mul_le_mul_left _ _;
        by_cases h : 2 * k + 1 - k < Finset.card ( Nat.divisors ( Q t ) ) <;> simp_all +decide [ two_mul, add_assoc ];
        exact Finset.mem_sort ( α := ℕ ) ( · ≤ · ) |>.1 ( List.getElem_mem _ ) |> fun x => Nat.divisor_le x;
      · erw [ List.getElem?_eq_getElem ] <;> norm_num;
        any_goals exact Finset.prod_ne_zero_iff.mpr fun i hi => Nat.Prime.ne_zero <| Nat.prime_nth_prime i;
        exact Nat.ne_of_gt <| Nat.pos_of_mem_divisors <| Finset.mem_sort ( α := ℕ ) ( · ≤ · ) |>.1 <| List.getElem_mem _;
    · rw [ List.getElem?_eq_getElem ] <;> norm_num;
      refine' Nat.pos_of_mem_divisors ( Finset.mem_sort ( α := ℕ ) ( · ≤ · ) |>.1 ( List.getElem_mem _ ) );
      exact Finset.prod_ne_zero_iff.mpr fun i hi => Nat.Prime.ne_zero <| by aesop;

/-
The sequence n_seq is strictly increasing.
-/
lemma n_seq_strictMono : StrictMono n_seq := by
  -- By combining the results from n_seq_block_mono and n_seq_block_transition, we can conclude that the entire sequence is strictly increasing.
  have h_strict_mono : ∀ k, n_seq k < n_seq (k + 1) := by
    -- By definition of $n_seq$, we know that $n_seq k$ is strictly increasing within each block and between blocks.
    intros k
    by_cases hk : ∃ t, 2^t - 1 ≤ k ∧ k + 1 ≤ 2^(t+1) - 2;
    · exact n_seq_block_mono _ _ hk.choose_spec.1 hk.choose_spec.2;
    · -- Since $k$ is not in the same block as $k+1$, it must be the last element of block $t$.
      obtain ⟨t, ht⟩ : ∃ t, k = 2^(t+1) - 2 := by
        -- Since $k$ is not in the same block as $k+1$, it must be the last element of some block $t$.
        obtain ⟨t, ht⟩ : ∃ t, 2^t - 1 ≤ k ∧ k < 2^(t+1) - 1 := by
          use Nat.log 2 (k + 1);
          exact ⟨ Nat.sub_le_of_le_add <| by linarith [ Nat.pow_log_le_self 2 <| show k + 1 ≠ 0 by linarith ], Nat.lt_sub_of_add_lt <| by linarith [ Nat.lt_pow_of_log_lt one_lt_two <| show Nat.log 2 ( k + 1 ) < Nat.log 2 ( k + 1 ) + 1 by linarith ] ⟩;
        grind;
      rw [ ht ];
      convert n_seq_block_transition t using 1;
      rcases n : 2 ^ ( t + 1 ) with ( _ | _ | n ) <;> aesop;
  exact strictMono_nat_of_lt_succ h_strict_mono

/-
Bound for phi_A(k)/n_k for k in block t.
-/
lemma n_seq_phi_bound (t : ℕ) (k : ℕ)
    (ht : t ≥ 1)
    (hk1 : 2^t - 1 ≤ k) (hk2 : k + 1 ≤ 2^(t+1) - 2) :
    (phi_A n_seq k : ℚ) / n_seq k ≤ (Nat.totient (n_seq k / r_seq t) : ℚ) / (n_seq k / r_seq t) + 1 / r_seq t := by
  -- We apply `lem_primeblock` with $p = r_t$ and $q = n_k / r_t$.
  have h_apply_lemma : ((phi_A n_seq k : ℚ) / (n_seq k : ℚ)) ≤ ((Nat.totient (n_seq k / r_seq t) : ℚ) / (n_seq k / r_seq t : ℚ)) + 1 / (r_seq t : ℚ) := by
    have h_mono : StrictMono n_seq := n_seq_strictMono
    have h_p_prime : Nat.Prime (r_seq t) := by
      induction ht <;> simp_all +decide
      · exact Nat.find_spec ( Nat.exists_infinite_primes _ ) |>.2;
      · exact Nat.find_spec ( Nat.exists_infinite_primes _ ) |>.2
    have h_q_pos : 0 < (n_seq k / r_seq t) := by
      -- By definition of $n_seq$, we know that $n_seq k = r_seq t * q$ for some $q$.
      obtain ⟨q, hq⟩ : ∃ q, n_seq k = r_seq t * q := by
        by_cases hk : k = 0;
        · grind;
        · -- By definition of $n_seq$, we know that $n_seq k = r_seq t * (n_seq k / r_seq t)$.
          simp [n_seq];
          rw [ show Nat.log 2 ( k + 1 ) = t from _ ];
          · aesop;
          · rw [ Nat.log_eq_iff ] <;> norm_num;
            exact ⟨ by omega, by omega ⟩;
      rcases q with ( _ | _ | q ) <;> simp_all +decide [ Nat.mul_div_cancel_left _ h_p_prime.pos ];
      · have := h_mono ( show 0 < k from Nat.pos_of_ne_zero ( by rintro rfl; norm_num at * ; linarith [ Nat.pow_le_pow_right two_pos ht ] ) ) ; aesop;
      · exact h_p_prime.pos
    have h_coprime : Nat.Coprime (r_seq t) (n_seq k / r_seq t) := by
      -- Since $r_t > Q_t$ and $r_t$ is prime, $r_t$ is coprime to $Q_t$, hence to $q$.
      have h_coprime_Q : Nat.Coprime (r_seq t) (Q t) := by
        -- Since $r_t > Q_t$ and $r_t$ is prime, $r_t$ cannot divide any of the primes in the product defining $Q_t$.
        have h_r_gt_Q : r_seq t > Q t := by
          induction' t with t ih <;> simp_all +decide [ Nat.pow_succ' ];
          have := r_seq_spec t; aesop;
        refine' h_p_prime.coprime_iff_not_dvd.mpr _;
        exact Nat.not_dvd_of_pos_of_lt ( Nat.pos_of_ne_zero ( by exact Finset.prod_ne_zero_iff.mpr fun i hi => Nat.Prime.ne_zero ( by aesop ) ) ) h_r_gt_Q;
      refine' h_coprime_Q.coprime_dvd_right _;
      -- By definition of $n_seq$, we know that $n_seq k = r_seq t * divisors.get! (j - 1)$ for some $j$.
      obtain ⟨j, hj⟩ : ∃ j, n_seq k = r_seq t * ((Nat.divisors (Q t)).sort (· ≤ ·)).get! j := by
        unfold n_seq;
        split_ifs <;> norm_num;
        · rw [ Nat.sub_le_iff_le_add ] at hk1 ; linarith [ Nat.pow_le_pow_right two_pos ht ];
        · rw [ show Nat.log 2 ( k + 1 ) = t from _ ];
          · exact ⟨ _, rfl ⟩;
          · rw [ Nat.log_eq_iff ] <;> norm_num;
            omega;
      by_cases hj' : j < List.length ( Finset.sort ( fun x1 x2 => x1 ≤ x2 ) ( Q t |> Nat.divisors ) ) <;> simp_all +decide [ Nat.mul_div_cancel_left _ h_p_prime.pos ];
      exact Nat.dvd_of_mem_divisors <| Finset.mem_sort ( α := ℕ ) ( · ≤ · ) |>.1 <| by aesop;
    have h_nk_eq : n_seq k = r_seq t * (n_seq k / r_seq t) := by
      rw [ Nat.mul_div_cancel' ];
      unfold n_seq;
      split_ifs <;> norm_num;
      · omega;
      · rw [ show Nat.log 2 ( k + 1 ) = t from _ ];
        · exact dvd_mul_right _ _;
        · rw [ Nat.log_eq_iff ] <;> norm_num;
          omega
    have h_div : ∀ e, e ∣ (n_seq k / r_seq t) → e < (n_seq k / r_seq t) → ∃ j < k, n_seq j = r_seq t * e := by
      intro e he_div he_lt
      obtain ⟨j, hj⟩ : ∃ j, j < k ∧ n_seq j = r_seq t * e := by
        have h_divisors : Finset.image (fun j => n_seq j) (Finset.Ico (2^t - 1) (2^(t+1) - 1)) = Finset.image (fun d => r_seq t * d) (Nat.divisors (Q t)) := by
          refine' Finset.eq_of_subset_of_card_le ( Finset.image_subset_iff.mpr _ ) _;
          · intro x hx;
            rcases x with ( _ | x ) <;> norm_num [ n_seq ] at hx ⊢;
            · exact absurd hx ( Nat.sub_ne_zero_of_lt ( one_lt_pow₀ one_lt_two ( by linarith ) ) );
            · -- Since $2^t \leq x + 2 < 2^{t+1}$, we have $\log_2(x + 2) = t$.
              have h_log : Nat.log 2 (x + 2) = t := by
                rw [ Nat.log_eq_iff ] <;> norm_num;
                omega;
              use (Finset.sort (· ≤ ·) (Nat.divisors (Q t)))[x + 1 - (2 ^ t - 2) - 1]?.getD 0;
              norm_num [ h_log ];
              refine' ⟨ _, _ ⟩;
              · by_cases h : x + 1 - ( 2 ^ t - 2 ) - 1 < Finset.card ( Nat.divisors ( Q t ) ) <;> simp +decide [ h ];
                · exact Nat.dvd_of_mem_divisors <| Finset.mem_sort ( α := ℕ ) ( · ≤ · ) |>.1 <| by simp;
                · contrapose! h;
                  refine' lt_of_lt_of_le _ ( Finset.card_mono <| show Nat.divisors ( Q t ) ≥ Finset.image ( fun d => d ) ( Finset.image ( fun d => ∏ i ∈ d, Nat.nth Nat.Prime i ) ( Finset.powerset ( Finset.range t ) ) ) from _ );
                  · rw [ Finset.card_image_of_injective, Finset.card_image_of_injOn ] <;> norm_num [ Function.Injective ];
                    · omega;
                    · intro a ha b hb; simp +decide at *;
                      intro h_eq;
                      apply_fun fun s => Nat.primeFactors s at h_eq;
                      -- Since the prime factors of the product of primes in a subset of the first t primes are exactly the primes in that subset, we can conclude that a = b.
                      have h_prime_factors : ∀ s : Finset ℕ, s ⊆ Finset.range t → (∏ i ∈ s, Nat.nth Nat.Prime i).primeFactors = s.image (fun i => Nat.nth Nat.Prime i) := by
                        intro s hs; induction s using Finset.induction <;> simp +decide [ * ] ;
                        rw [ Nat.primeFactors_mul, ‹ ( _ : Finset ℕ ) ⊆ Finset.range t → ( ∏ i ∈ _, Nat.nth Nat.Prime i |> Nat.primeFactors ) = _› <| Finset.Subset.trans ( Finset.subset_insert _ _ ) hs ] <;> norm_num [ Nat.Prime.ne_zero, Finset.prod_eq_zero_iff ];
                      rw [ h_prime_factors a ( fun x hx => Finset.mem_range.mpr ( ha hx ) ), h_prime_factors b ( fun x hx => Finset.mem_range.mpr ( hb hx ) ) ] at h_eq;
                      exact Finset.image_injective ( Nat.nth_injective ( Nat.infinite_setOf_prime ) ) h_eq;
                  · intro d hd; simp +decide [ Q ] at hd ⊢;
                    obtain ⟨ a, ha₁, rfl ⟩ := hd; exact ⟨ by rw [ ← Finset.prod_sdiff ha₁ ] ; norm_num, Finset.prod_ne_zero_iff.mpr fun i hi => Nat.Prime.ne_zero <| by norm_num ⟩ ;
              · exact Finset.prod_ne_zero_iff.mpr fun i hi => Nat.Prime.ne_zero <| Nat.prime_nth_prime i;
          · rw [ Finset.card_image_of_injective _ fun x y hxy => mul_left_cancel₀ h_p_prime.ne_zero hxy, Finset.card_image_of_injective _ h_mono.injective ] ; norm_num;
            -- The number of divisors of $Q_t$ is $2^t$.
            have h_divisors_card : (Nat.divisors (Q t)).card = 2^t := by
              have h_divisors_card : (Nat.divisors (Finset.prod (Finset.range t) (fun i => Nat.nth Nat.Prime i))).card = Finset.prod (Finset.range t) (fun i => (Nat.divisors (Nat.nth Nat.Prime i)).card) := by
                have h_divisors_card : ∀ {m n : ℕ}, Nat.Coprime m n → (Nat.divisors (m * n)).card = (Nat.divisors m).card * (Nat.divisors n).card := by
                  exact fun {m n} a => Nat.Coprime.card_divisors_mul a;
                induction' t with t ih;
                · contradiction;
                · induction' t + 1 with t ih <;> simp +decide [ Finset.prod_range_succ, * ];
                  rw [ h_divisors_card, ih ];
                  refine' Nat.Coprime.prod_left _;
                  intro i hi; rw [ Nat.coprime_primes ] <;> norm_num [ Nat.Prime.ne_zero, Nat.Prime.ne_one ] ;
                  exact fun h => by have := Nat.nth_injective ( Nat.infinite_setOf_prime ) h; linarith [ Finset.mem_range.mp hi ] ;
              simp_all +singlePass [ Nat.Prime.divisors ];
              exact h_divisors_card.trans ( by rw [ Finset.prod_congr rfl fun _ _ => Finset.card_pair <| ne_of_lt <| Nat.Prime.one_lt <| Nat.prime_nth_prime _ ] ; norm_num );
            omega
        -- Since $e$ is a divisor of $n_k / r_t$, and $n_k / r_t$ is a divisor of $Q_t$, $e$ must also be a divisor of $Q_t$.
        have h_e_div_Q : e ∣ Q t := by
          have h_e_div_Q : n_seq k / r_seq t ∣ Q t := by
            replace h_divisors := Finset.ext_iff.mp h_divisors ( n_seq k ) ; norm_num at h_divisors;
            contrapose! h_divisors;
            refine Or.inl ⟨ ⟨ k, ⟨ ?_, ?_ ⟩, rfl ⟩, ?_ ⟩;
            · omega;
            · exact lt_of_lt_of_le hk2 ( Nat.sub_le_sub_right ( Nat.le_succ _ ) _ );
            · intro x hx H; rw [ eq_comm ] at H; simp_all +singlePass ;
          exact dvd_trans he_div h_e_div_Q;
        replace h_divisors := Finset.ext_iff.mp h_divisors ( r_seq t * e ) ; norm_num at *;
        obtain ⟨ j, hj₁, hj₂ ⟩ := h_divisors.mpr ⟨ e, ⟨ h_e_div_Q, by
          exact Finset.prod_ne_zero_iff.mpr fun i hi => Nat.Prime.ne_zero <| Nat.prime_nth_prime i ⟩, Or.inl rfl ⟩;
        refine' ⟨ j, _, hj₂ ⟩;
        exact lt_of_not_ge fun h => he_lt.not_le <| Nat.le_of_not_lt fun h' => by nlinarith [ h_mono.monotone h ] ;
      use j
    convert lem_primeblock n_seq k ( r_seq t ) ( n_seq k / r_seq t ) h_mono h_p_prime h_q_pos h_coprime h_nk_eq h_div using 1;
    rw [ Nat.cast_div ( h_nk_eq.symm ▸ dvd_mul_right _ _ ) ( Nat.cast_ne_zero.mpr h_p_prime.ne_zero ) ];
  convert h_apply_lemma using 1

/-
The function k -> k - (2^t - 2) - 1 maps the block indices to the range [0, 2^t - 1].
-/
lemma block_index_map (t : ℕ) (ht : t ≥ 1) :
    (Finset.Icc (2^t - 1) (2^(t+1) - 2)).image (fun k => k - (2^t - 2) - 1) = Finset.range (2^t) := by
  ext;
  norm_num +zetaDelta at *;
  constructor;
  · rintro ⟨ a, ⟨ ha₁, ha₂ ⟩, rfl ⟩;
    rw [ tsub_tsub, tsub_lt_iff_left ] <;> linarith [ Nat.sub_add_cancel ( show 2 ≤ 2 ^ t from le_trans ( by decide ) ( pow_le_pow_right₀ ( by decide ) ht ) ), pow_succ' 2 t, Nat.sub_add_cancel ( show 2 ≤ 2 ^ ( t + 1 ) from le_trans ( by decide ) ( pow_le_pow_right₀ ( by decide ) ( Nat.succ_le_succ ht ) ) ) ];
  · intro h;
    refine' ⟨ 2 ^ t + ‹ℕ› - 1, _, _ ⟩ <;> omega

/-
The number of divisors of Q(t) is 2^t.
-/
lemma card_divisors_Q (t : ℕ) : (Nat.divisors (Q t)).card = 2^t := by
  -- By definition of $Q$, we know that $Q_t = \prod_{i=0}^{t-1} p_i$, where $p_i$ is the $i$-th prime number.
  have hQ_def : Q t = ∏ i ∈ Finset.range t, Nat.nth Nat.Prime i := by
    rfl;
  -- Since the primes are distinct, the divisors of $Q_t$ are precisely the products of subsets of $\{p_0, p_1, \ldots, p_{t-1}\}$.
  have h_divisors : (Q t).divisors = Finset.image (fun s => ∏ i ∈ s, Nat.nth Nat.Prime i) (Finset.powerset (Finset.range t)) := by
    rw [ hQ_def ];
    induction ( Finset.range t ) using Finset.induction <;> simp_all +decide [ Nat.divisors_mul ];
    rw [ Nat.Prime.divisors ( Nat.prime_nth_prime _ ) ];
    ext; simp [Finset.mem_mul, Finset.mem_image];
    constructor;
    · rintro ( ⟨ s, hs, rfl ⟩ | ⟨ s, hs, rfl ⟩ ) <;> [ exact ⟨ s, Finset.Subset.trans hs ( Finset.subset_insert _ _ ), rfl ⟩ ; exact ⟨ Insert.insert _ s, Finset.insert_subset_insert _ hs, by rw [ Finset.prod_insert ( Finset.notMem_mono hs ‹_› ) ] ⟩ ];
    · rintro ⟨ s, hs, rfl ⟩ ; by_cases h : ‹_› ∈ s <;> simp_all +decide [ Finset.subset_iff ] ;
      · exact Or.inr ⟨ s.erase ‹_›, fun x hx => by cases hs ( Finset.mem_of_mem_erase hx ) <;> aesop, by rw [ mul_comm, Finset.prod_erase_mul _ _ h ] ⟩;
      · exact Or.inl ⟨ s, fun x hx => Or.resolve_left ( hs hx ) ( by aesop ), rfl ⟩;
  rw [ h_divisors, Finset.card_image_of_injOn, Finset.card_powerset ] ; aesop;
  intros s hs t ht h_eq; apply_fun fun x => x.primeFactors at h_eq; simp_all +decide
  simp_all +decide [ Finset.ext_iff, Set.subset_def ];
  intro x; specialize h_eq ( Nat.nth Nat.Prime x ) ( Nat.prime_nth_prime x ) ; simp_all +decide [ Nat.Prime.dvd_iff_not_coprime, Nat.coprime_prod_right_iff ] ;
  simp_all +decide [ Nat.coprime_primes, Finset.prod_eq_zero_iff, Nat.Prime.ne_zero ];
  exact ⟨ fun hx => h_eq.mp ⟨ x, hx, rfl ⟩ |> fun ⟨ y, hy, hy' ⟩ => by have := Nat.nth_injective ( Nat.infinite_setOf_prime ) hy'; aesop, fun hx => h_eq.mpr ⟨ x, hx, rfl ⟩ |> fun ⟨ y, hy, hy' ⟩ => by have := Nat.nth_injective ( Nat.infinite_setOf_prime ) hy'; aesop ⟩

/-
For t >= 1, the sum of f(n_k/r_t) over the block t is equal to the sum of f(d) over the divisors of Q_t.
-/
lemma sum_over_block_eq_sum_over_divisors (t : ℕ) (ht : t ≥ 1) (f : ℕ → ℝ) :
    ∑ k ∈ Finset.Icc (2^t - 1) (2^(t+1) - 2), f (n_seq k / r_seq t) = ∑ d ∈ Nat.divisors (Q t), f d := by
  -- By definition of $n_seq$, we know that for $k \in [2^t - 1, 2^{t+1} - 2]$, $n_k / r_t$ is a divisor of $Q_t$.
  have h_divisors : ∀ k ∈ Finset.Icc (2^t - 1) (2^(t+1) - 2), n_seq k / r_seq t ∈ Nat.divisors (Q t) := by
    unfold n_seq;
    -- By definition of $n_seq$, for $k \in [2^t - 1, 2^{t+1} - 2]$, $n_k / r_t$ is a divisor of $Q_t$.
    intros k hk
    have ht : Nat.log 2 (k + 1) = t := by
      rw [ Nat.log_eq_iff ] <;> norm_num;
      exact ⟨ by linarith [ Finset.mem_Icc.mp hk, Nat.sub_add_cancel ( Nat.one_le_pow t 2 zero_lt_two ) ], by linarith [ Finset.mem_Icc.mp hk, Nat.sub_add_cancel ( show 2 ≤ 2 ^ ( t + 1 ) from le_self_pow₀ ( by norm_num ) ( by linarith ) ) ] ⟩;
    have h_divisors : (Finset.sort (· ≤ ·) (Nat.divisors (Q t))).get! (k - (2^t - 2) - 1) ∈ Nat.divisors (Q t) := by
      have h_divisors : k - (2^t - 2) - 1 < (Nat.divisors (Q t)).card := by
        rw [ card_divisors_Q ];
        rw [ Nat.sub_sub, tsub_lt_iff_left ] <;> norm_num at * <;> linarith [ Nat.sub_add_cancel ( show 2 ≤ 2 ^ t from le_trans ( by decide ) ( pow_le_pow_right₀ ( by decide ) ‹1 ≤ t› ) ), Nat.sub_add_cancel ( show 2 ≤ 2 ^ ( t + 1 ) from le_trans ( by decide ) ( pow_le_pow_right₀ ( by decide ) ( Nat.succ_le_succ ‹1 ≤ t› ) ) ), pow_succ' 2 t ];
      simp +zetaDelta at *;
      exact ⟨ Nat.dvd_of_mem_divisors <| Finset.mem_sort ( α := ℕ ) ( · ≤ · ) |>.1 <| by aesop, Nat.ne_of_gt <| Finset.prod_pos fun p hp => Nat.Prime.pos <| by aesop ⟩;
    split_ifs <;> simp_all +decide
    · grind;
    · rw [ Nat.mul_div_cancel_left _ ( Nat.pos_of_ne_zero ( by
        exact Nat.ne_of_gt ( Nat.recOn t ( by norm_num [ r_seq ] ) fun n ihn => Nat.Prime.pos ( by exact Nat.find_spec ( Nat.exists_infinite_primes _ ) |>.2 ) ) ) ) ] ; aesop;
  have h_divisors_eq : Finset.image (fun k => n_seq k / r_seq t) (Finset.Icc (2^t - 1) (2^(t+1) - 2)) = Nat.divisors (Q t) := by
    refine' Finset.eq_of_subset_of_card_le ( fun x hx => _ ) _;
    · grind;
    · rw [ Finset.card_image_of_injOn ];
      · rw [ card_divisors_Q ] ; norm_num [ Nat.pow_succ' ] ; omega;
      · intro k hk l hl hkl;
        -- Since $n_seq$ is strictly increasing, if $n_seq k / r_seq t = n_seq l / r_seq t$, then $n_seq k = n_seq l$.
        have h_eq : n_seq k = n_seq l := by
          have h_eq : n_seq k = r_seq t * (n_seq k / r_seq t) ∧ n_seq l = r_seq t * (n_seq l / r_seq t) := by
            have h_eq : ∀ k ∈ Finset.Icc (2^t - 1) (2^(t+1) - 2), r_seq t ∣ n_seq k := by
              intros k hk
              simp [n_seq];
              split_ifs <;> simp_all +decide
              · exact absurd hk ( Nat.sub_ne_zero_of_lt ( one_lt_pow₀ one_lt_two ( by linarith ) ) );
              · rw [ show Nat.log 2 ( k + 1 ) = t from _ ];
                · exact dvd_mul_right _ _;
                · rw [ Nat.log_eq_iff ] <;> norm_num;
                  exact ⟨ hk.1, by rw [ pow_succ' ] at *; omega ⟩;
            exact ⟨ Eq.symm ( Nat.mul_div_cancel' ( h_eq k hk ) ), Eq.symm ( Nat.mul_div_cancel' ( h_eq l hl ) ) ⟩;
          grind;
        exact StrictMono.injective ( show StrictMono n_seq from by exact n_seq_strictMono ) h_eq;
  rw [ ← h_divisors_eq, Finset.sum_image ];
  have := Finset.card_image_iff.mp ( show Finset.card ( Finset.image ( fun k => n_seq k / r_seq t ) ( Finset.Icc ( 2 ^ t - 1 ) ( 2 ^ ( t + 1 ) - 2 ) ) ) = Finset.card ( Finset.Icc ( 2 ^ t - 1 ) ( 2 ^ ( t + 1 ) - 2 ) ) from ?_ ) ; aesop;
  rw [ h_divisors_eq, card_divisors_Q ] ; norm_num [ Nat.pow_succ' ];
  exact eq_tsub_of_add_eq ( by linarith [ Nat.sub_add_cancel ( show 1 ≤ 2 ^ t from Nat.one_le_pow _ _ ( by decide ) ), Nat.sub_add_cancel ( show 2 ≤ 2 * 2 ^ t from by linarith [ Nat.pow_le_pow_right ( by decide : 1 ≤ 2 ) ht ] ) ] )

/-
For t >= 1, the sum of f(n_k/r_t) over the block t is equal to the sum of f(d) over the divisors of Q_t.
-/
lemma sum_over_block_eq_sum_over_divisors_correct (t : ℕ) (ht : t ≥ 1) (f : ℕ → ℝ) :
    ∑ k ∈ Finset.Icc (2^t - 1) (2^(t+1) - 2), f (n_seq k / r_seq t) = ∑ d ∈ Nat.divisors (Q t), f d := by
  let I := Finset.Icc (2^t - 1) (2^(t+1) - 2)
  let D := Nat.divisors (Q t)
  let g (k : ℕ) := n_seq k / r_seq t
  have h_bij : ∀ k ∈ I, g k ∈ D := by
    intro k hk
    -- We need to show n_seq k / r_seq t is a divisor of Q t
    norm_num +zetaDelta at *;
    -- By definition of $n_seq$, we have that $n_seq k = r_seq t * d$ for some divisor $d$ of $Q t$.
    obtain ⟨d, hd⟩ : ∃ d, n_seq k = r_seq t * d ∧ d ∈ Nat.divisors (Q t) := by
      unfold n_seq;
      split_ifs <;> simp_all +decide
      · linarith [ Nat.pow_le_pow_right two_pos ht ];
      · rw [ show Nat.log 2 ( k + 1 ) = t by exact Nat.log_eq_iff ( by norm_num ) |>.2 ⟨ by linarith, by rw [ pow_succ' ] ; omega ⟩ ];
        refine' ⟨ _, rfl, _, _ ⟩;
        · by_cases h : k - ( 2 ^ t - 2 ) - 1 < List.length ( Finset.sort ( fun x1 x2 => x1 ≤ x2 ) ( Q t |> Nat.divisors ) ) <;> simp_all +decide
          · exact Nat.dvd_of_mem_divisors <| Finset.mem_sort ( α := ℕ ) ( fun x1 x2 => x1 ≤ x2 ) |>.1 <| by aesop;
          · have h_card : (Nat.divisors (Q t)).card = 2^t := by
              exact card_divisors_Q t;
            omega;
        · exact Finset.prod_ne_zero_iff.mpr fun i hi => Nat.Prime.ne_zero <| by aesop;
    rw [ hd.1, Nat.mul_div_cancel_left _ ( Nat.Prime.pos ( show Nat.Prime ( r_seq t ) from ?_ ) ) ] ; aesop;
    induction' t with t ih;
    · contradiction;
    · exact Nat.find_spec ( Nat.exists_infinite_primes _ ) |>.2
  have h_inj : ∀ k₁ ∈ I, ∀ k₂ ∈ I, g k₁ = g k₂ → k₁ = k₂ := by
    intro k₁ hk₁ k₂ hk₂ h_eq
    -- Since $n_k$ is strictly increasing, if $n_k1 = n_k2$, then $k1 = k2$.
    have h_strict_mono : ∀ k₁ k₂, k₁ < k₂ → n_seq k₁ < n_seq k₂ := by
      exact fun k₁ k₂ hk => n_seq_strictMono hk;
    -- Since $r_seq t$ is a prime number, it is non-zero, so we can multiply both sides of the equation $n_seq k₁ / r_seq t = n_seq k₂ / r_seq t$ by $r_seq t$ to get $n_seq k₁ = n_seq k₂$.
    have h_eq_n : n_seq k₁ = n_seq k₂ := by
      have h_eq_n : n_seq k₁ = r_seq t * g k₁ ∧ n_seq k₂ = r_seq t * g k₂ := by
        -- By definition of $n_seq$, we know that $n_seq k = r_seq t * (divisors.get! (j - 1))$ where $j = k - (2^t - 2)$.
        have h_n_seq_def : ∀ k ∈ I, n_seq k = r_seq t * ((Nat.divisors (Q t)).sort (· ≤ ·)).get! (k - (2^t - 2) - 1) := by
          intros k hk
          simp [n_seq];
          -- Since $k \in I$, we have $2^t \leq k + 1 < 2^{t+1}$, thus $\log_2(k + 1) = t$.
          have h_log : Nat.log 2 (k + 1) = t := by
            rw [ Nat.log_eq_iff ] <;> norm_num;
            exact ⟨ by linarith [ Finset.mem_Icc.mp hk, Nat.sub_add_cancel ( Nat.one_le_pow t 2 zero_lt_two ) ], by linarith [ Finset.mem_Icc.mp hk, Nat.sub_add_cancel ( show 2 ≤ 2 ^ ( t + 1 ) from le_self_pow₀ ( by decide ) ( by linarith ) ) ] ⟩;
          aesop;
        -- By definition of $g$, we know that $g k = n_seq k / r_seq t$.
        simp [g, h_n_seq_def k₁ hk₁, h_n_seq_def k₂ hk₂];
        exact ⟨ Or.inl <| Eq.symm <| Nat.mul_div_cancel_left _ <| Nat.Prime.pos <| show Nat.Prime ( r_seq t ) from Nat.recOn t ( by norm_num [ r_seq ] ) fun t ih => Nat.find_spec ( Nat.exists_infinite_primes _ ) |>.2, Or.inl <| Eq.symm <| Nat.mul_div_cancel_left _ <| Nat.Prime.pos <| show Nat.Prime ( r_seq t ) from Nat.recOn t ( by norm_num [ r_seq ] ) fun t ih => Nat.find_spec ( Nat.exists_infinite_primes _ ) |>.2 ⟩;
      rw [ h_eq_n.1, h_eq_n.2, h_eq ];
    exact le_antisymm ( le_of_not_gt fun h => by linarith [ h_strict_mono _ _ h ] ) ( le_of_not_gt fun h => by linarith [ h_strict_mono _ _ h ] )
  have h_surj : ∀ d ∈ D, ∃ k, ∃ (hk : k ∈ I), g k = d := by
    intro d hd
    -- Since D has 2^t elements and I has 2^t elements, and g is injective on I, the image of g over I must be exactly D.
    have h_card : Finset.card (Finset.image g I) = 2 ^ t := by
      rw [ Finset.card_image_of_injOn fun k₁ hk₁ k₂ hk₂ h => h_inj k₁ hk₁ k₂ hk₂ h ];
      simp +zetaDelta at *;
      exact Nat.sub_eq_of_eq_add <| by linarith [ Nat.sub_add_cancel <| show 1 ≤ 2 ^ t from Nat.one_le_pow _ _ zero_lt_two, Nat.sub_add_cancel <| show 2 ≤ 2 ^ ( t + 1 ) from le_trans ( by decide ) <| pow_le_pow_right₀ ( by decide ) <| Nat.succ_le_succ ht, pow_succ' 2 t ] ;
    have h_image : Finset.image g I = D := by
      exact Finset.eq_of_subset_of_card_le ( Finset.image_subset_iff.mpr fun x hx => h_bij x hx ) ( by rw [ h_card, card_divisors_Q t ] );
    exact Exists.elim ( Finset.mem_image.mp ( h_image.symm ▸ hd ) ) fun k hk => ⟨ k, hk.1, hk.2 ⟩
  exact Finset.sum_bij (fun k _ => g k) h_bij h_inj h_surj (fun _ _ => rfl)

/-
For t >= 1, 1/r_seq(t) <= A_val(t).
-/
lemma inv_r_seq_le_A_val (t : ℕ) (ht : t ≥ 1) :
    1 / (r_seq t : ℝ) ≤ A_val t := by
      induction ht <;> norm_num [ *, Finset.prod_range_succ ] at *;
      · norm_num [ A_val ];
        rw [ inv_eq_one_div, div_le_div_iff₀ ] <;> norm_cast;
        · exact le_trans ( by norm_num ) ( Nat.mul_le_mul_left 3 ( show r_seq 1 ≥ 2 by exact Nat.Prime.two_le ( r_seq_spec 0 |>.2 ) ) );
        · exact Nat.Prime.pos ( r_seq_spec 0 |>.2 );
      · -- By definition of $r_seq$, we know that $r_seq (m + 1) > \max(r_seq m * Q m, Q (m + 1), \lceil 1 / A_val (m + 1) \rceil)$.
        have h_r_seq_gt : r_seq (Nat.succ ‹_›) > Nat.ceil (1 / A_val (Nat.succ ‹_›)) := by
          exact Nat.lt_of_ceil_lt ( r_seq_spec _ |>.1.trans_le' <| by aesop );
        field_simp;
        rw [ div_le_iff₀ ] <;> norm_num at *;
        · rw [ ← div_le_iff₀' ] <;> norm_num;
          · exact le_trans ( Nat.le_ceil _ ) ( mod_cast h_r_seq_gt.le );
          · exact Finset.prod_pos fun i hi => sub_pos.mpr <| by rw [ div_lt_iff₀ ] <;> norm_cast <;> linarith [ Nat.Prime.two_le <| Nat.prime_nth_prime i ] ;
        · linarith

/-
The sum of the bound terms over block t equals 2^t * A_val t + 2^t / r_seq t.
-/
lemma sum_bound_eval (t : ℕ) (ht : t ≥ 1) :
    ∑ k ∈ Finset.Icc (2^t - 1) (2^(t+1) - 2), ((Nat.totient (n_seq k / r_seq t) : ℝ) / (n_seq k / r_seq t) + 1 / r_seq t) =
    (2^t : ℝ) * A_val t + (2^t : ℝ) / r_seq t := by
      -- Split the sum into two parts: the sum of the totient function divided by the divisor, and the sum of 1/r_seq t.
      have h_split : ∑ k ∈ Finset.Icc (2^t - 1) (2^(t+1) - 2), ((Nat.totient (n_seq k / r_seq t) : ℝ) / (n_seq k / r_seq t)) = 2^t * A_val t := by
        convert sum_over_block_eq_sum_over_divisors t ht ( fun x => ( Nat.totient x : ℝ ) / x ) using 1;
        · refine' Finset.sum_congr rfl fun x hx => _;
          unfold n_seq;
          -- Since $x$ is in the interval $[2^t - 1, 2^{t+1} - 2]$, we have $\log_2(x + 1) = t$.
          have h_log : Nat.log 2 (x + 1) = t := by
            rw [ Nat.log_eq_iff ] <;> norm_num;
            exact ⟨ by linarith [ Finset.mem_Icc.mp hx, Nat.sub_add_cancel ( Nat.one_le_pow t 2 zero_lt_two ) ], by linarith [ Finset.mem_Icc.mp hx, Nat.sub_add_cancel ( show 2 ≤ 2 ^ ( t + 1 ) from le_trans ( by decide ) ( Nat.pow_le_pow_right ( by decide ) ( Nat.succ_le_succ ht ) ) ) ] ⟩;
          aesop;
        · -- Apply the lemma lem_divisoravg to Q t.
          have h_divisoravg : (1 / (2 ^ t : ℚ)) * (∑ d ∈ Nat.divisors (Q t), (Nat.totient d : ℚ) / d) = (Finset.range t).prod (fun i => 1 - 1 / (2 * (Nat.nth Nat.Prime i : ℚ))) := by
            convert lem_divisoravg t using 1;
          unfold A_val; norm_num [ ← @Rat.cast_inj ℝ ] at *; rw [ inv_mul_eq_div, div_eq_iff ] at * <;> first | positivity | linarith;
      norm_num [ ← h_split, Finset.sum_add_distrib, div_eq_mul_inv ];
      rw [ Nat.cast_sub ] <;> norm_num [ pow_succ' ] ; ring_nf;
      · exact Or.inl ( by rw [ Nat.cast_sub ( by linarith [ Nat.pow_le_pow_right two_pos ht ] ) ] ; push_cast; ring );
      · omega

/-
If e is a proper divisor of the d-part of n_seq k, then r_seq t * e appears earlier in the same block.
-/
lemma n_seq_divisors_property (t : ℕ) (k : ℕ)
    (ht : t ≥ 1)
    (hk : k ∈ Finset.Icc (2^t - 1) (2^(t+1) - 2))
    (e : ℕ) (he_dvd : e ∣ (n_seq k / r_seq t)) (he_lt : e < (n_seq k / r_seq t)) :
    ∃ j ∈ Finset.Icc (2^t - 1) (2^(t+1) - 2), j < k ∧ n_seq j = r_seq t * e := by
      -- Let $d = n_seq k / r_seq t$. From the definition of $n_seq$, $d$ is an element of $divisors_Q t$.
      set d := n_seq k / r_seq t
      have hd_divisors : d ∈ Nat.divisors (Q t) := by
        -- Since $k \in \text{Finset.Icc} (2^t - 1) (2^{t+1} - 2)$, we have $t = \text{Nat.log} 2 (k + 1)$.
        have ht_eq : t = Nat.log 2 (k + 1) := by
          rw [ eq_comm, Nat.log_eq_iff ] <;> norm_num;
          exact ⟨ by linarith [ Finset.mem_Icc.mp hk, Nat.sub_add_cancel ( Nat.one_le_pow t 2 zero_lt_two ) ], by linarith [ Finset.mem_Icc.mp hk, Nat.sub_add_cancel ( show 2 ≤ 2 ^ ( t + 1 ) from le_trans ( by decide ) ( Nat.pow_le_pow_right ( by decide ) ( Nat.succ_le_succ ht ) ) ) ] ⟩;
        -- By definition of $n_seq$, we know that $n_seq k = r_seq t * divisors_Q t.get! (j - 1)$ for some $j$.
        have h_nseq_def : n_seq k = r_seq t * ((Nat.divisors (Q t)).sort (· ≤ ·)).get! (k - (2^t - 2) - 1) := by
          unfold n_seq; aesop;
        simp +zetaDelta at *;
        rw [ h_nseq_def, Nat.mul_div_cancel_left _ ( Nat.Prime.pos ( show Nat.Prime ( r_seq t ) from ?_ ) ) ];
        · refine' ⟨ _, _ ⟩;
          · by_cases h : k - ( 2 ^ t - 2 ) - 1 < List.length ( Finset.sort ( fun x1 x2 => x1 ≤ x2 ) ( Q t |> Nat.divisors ) ) <;> simp_all +decide
            exact Nat.dvd_of_mem_divisors <| Finset.mem_sort ( α := ℕ ) ( · ≤ · ) |>.1 <| by simp;
          · exact Finset.prod_ne_zero_iff.mpr fun i hi => Nat.Prime.ne_zero <| by aesop;
        · exact Nat.recOn t ( by norm_num [ show r_seq 0 = 2 from rfl ] ) fun t ih => r_seq_spec t |>.2;
      -- Since $e | d$ and $d | Q t$, $e$ is also in $divisors_Q t$.
      have he_divisors : e ∈ Nat.divisors (Q t) := by
        exact Nat.mem_divisors.mpr ⟨ dvd_trans he_dvd ( Nat.dvd_of_mem_divisors hd_divisors ), by aesop ⟩;
      -- Since $e$ is in $divisors_Q t$ and $e < d$, there exists an index $j$ in the block such that $n_seq j = r_seq t * e$.
      obtain ⟨j, hj⟩ : ∃ j ∈ Finset.Icc (2^t - 1) (2^(t+1) - 2), n_seq j = r_seq t * e := by
        have h_map : Finset.image (fun j => n_seq j) (Finset.Icc (2^t - 1) (2^(t+1) - 2)) = Finset.image (fun d => r_seq t * d) (Nat.divisors (Q t)) := by
          -- By definition of $n_seq$, the elements of the block are exactly the multiples of $r_seq t$ by the divisors of $Q t$.
          have h_block_elements : ∀ j ∈ Finset.Icc (2^t - 1) (2^(t+1) - 2), n_seq j ∈ Finset.image (fun d => r_seq t * d) (Nat.divisors (Q t)) := by
            intro j hj
            simp [n_seq];
            -- Since $j$ is in the block, we have $Nat.log 2 (j + 1) = t$.
            have h_log : Nat.log 2 (j + 1) = t := by
              rw [ Nat.log_eq_iff ] <;> norm_num;
              exact ⟨ by linarith [ Finset.mem_Icc.mp hj, Nat.sub_add_cancel ( Nat.one_le_pow t 2 zero_lt_two ) ], by linarith [ Finset.mem_Icc.mp hj, Nat.sub_add_cancel ( show 2 ≤ 2 ^ ( t + 1 ) from le_trans ( by decide ) ( Nat.pow_le_pow_right ( by decide ) ( Nat.succ_le_succ ht ) ) ) ] ⟩;
            by_cases hj_zero : j = 0 <;> simp_all +decide
            · grind;
            · by_cases h : j - ( 2 ^ t - 2 ) - 1 < List.length ( Finset.sort ( fun x1 x2 => x1 ≤ x2 ) ( Q t |> Nat.divisors ) ) <;> simp_all +decide
              · exact ⟨ _, Nat.dvd_of_mem_divisors <| Finset.mem_sort ( α := ℕ ) ( · ≤ · ) |>.1 <| by aesop, Or.inl rfl ⟩;
              · contrapose! h;
                rw [ card_divisors_Q ];
                rw [ tsub_tsub, tsub_lt_iff_left ] <;> linarith [ Nat.sub_add_cancel ( show 2 ≤ 2 ^ t from le_trans ( by decide ) ( pow_le_pow_right₀ ( by decide ) ht ) ), Nat.sub_add_cancel ( show 2 ≤ 2 ^ ( t + 1 ) from le_trans ( by decide ) ( pow_le_pow_right₀ ( by decide ) ( Nat.succ_le_succ ht ) ) ), pow_succ' 2 t ];
          refine' Finset.eq_of_subset_of_card_le ( Finset.image_subset_iff.mpr h_block_elements ) _;
          rw [ Finset.card_image_of_injective, Finset.card_image_of_injOn ];
          · rw [ card_divisors_Q ] ; norm_num [ Nat.pow_succ' ] ; omega;
          · exact fun x hx y hy hxy => by simpa using StrictMono.injective n_seq_strictMono hxy;
          · intro a b; aesop;
        replace h_map := Finset.ext_iff.mp h_map ( r_seq t * e ) ; aesop;
      refine' ⟨ j, hj.1, _, hj.2 ⟩;
      -- Since $e < d$, we have $n_seq j < n_seq k$.
      have h_nseq_lt : n_seq j < n_seq k := by
        rw [ Nat.lt_iff_add_one_le, Nat.le_div_iff_mul_le ] at * <;> norm_num at *;
        · linarith [ show r_seq t > 0 from Nat.Prime.pos ( show Nat.Prime ( r_seq t ) from Nat.recOn t ( by norm_num [ r_seq ] ) fun n ihn => Nat.find_spec ( Nat.exists_infinite_primes _ ) |>.2 ) ];
        · exact Nat.Prime.pos ( by exact Nat.recOn t ( by norm_num [ r_seq ] ) fun n ihn => by exact Nat.find_spec ( Nat.exists_infinite_primes _ ) |>.2 );
      exact lt_of_not_ge fun h => h_nseq_lt.not_le <| by simpa using n_seq_strictMono.monotone h;

/-
r_seq t is coprime to the d-part of n_seq k.
-/
lemma r_seq_coprime_aux (t : ℕ) (k : ℕ)
    (ht : t ≥ 1)
    (hk : k ∈ Finset.Icc (2^t - 1) (2^(t+1) - 2)) :
    Nat.Coprime (r_seq t) (n_seq k / r_seq t) := by
      -- From the definition of n_seq, we know that n_seq k / r_seq t is a divisor of Q t.
      have h_div : n_seq k / r_seq t ∣ Q t := by
        unfold n_seq;
        split_ifs;
        · norm_num [ ‹_› ] at *;
          exact absurd hk ( Nat.sub_ne_zero_of_lt ( one_lt_pow₀ one_lt_two ( by linarith ) ) );
        · rw [ show Nat.log 2 ( k + 1 ) = t from _ ];
          · rw [ Nat.mul_div_cancel_left _ ( Nat.Prime.pos ( by exact Nat.recOn t ( by exact Nat.prime_two ) fun t ih => by exact Nat.find_spec ( Nat.exists_infinite_primes _ ) |>.2 ) ) ];
            by_cases h : k - ( 2 ^ t - 2 ) - 1 < List.length ( Finset.sort ( fun x1 x2 => x1 ≤ x2 ) ( Q t |> Nat.divisors ) ) <;> simp_all +decide [ Nat.sub_sub ];
            · exact Nat.dvd_of_mem_divisors <| Finset.mem_sort ( α := ℕ ) ( · ≤ · ) |>.1 <| by aesop;
            · -- Since $Q_t$ is the product of the first $t$ primes, its number of divisors is $2^t$.
              have h_divisors_card : (Nat.divisors (Q t)).card = 2^t := by
                exact card_divisors_Q t;
              omega;
          · rw [ Nat.log_eq_iff ] <;> norm_num;
            exact ⟨ by linarith [ Finset.mem_Icc.mp hk, Nat.sub_add_cancel ( Nat.one_le_pow t 2 zero_lt_two ) ], by linarith [ Finset.mem_Icc.mp hk, Nat.sub_add_cancel ( show 2 ≤ 2 ^ ( t + 1 ) from le_trans ( by decide ) ( Nat.pow_le_pow_right ( by decide ) ( Nat.succ_le_succ ht ) ) ) ] ⟩;
      -- From r_seq_spec, we know that r_seq t > Q t.
      have h_r_gt_Q : r_seq t > Q t := by
        induction' t with t ih;
        · contradiction;
        · exact lt_of_le_of_lt ( le_max_of_le_right ( le_max_left _ _ ) ) ( r_seq_spec _ |>.1 );
      -- Since $r_seq t$ is prime and greater than $Q t$, it cannot divide any divisor of $Q t$.
      have h_r_not_div_Q : ¬(r_seq t ∣ Q t) := by
        exact Nat.not_dvd_of_pos_of_lt ( Nat.pos_of_ne_zero ( by exact ne_of_gt ( Finset.prod_pos fun i hi => Nat.Prime.pos ( by aesop ) ) ) ) h_r_gt_Q;
      exact Nat.Prime.coprime_iff_not_dvd ( show Nat.Prime ( r_seq t ) from by rcases t with ( _ | _ | t ) <;> [ norm_num [ r_seq ] ; exact Nat.find_spec ( Nat.exists_infinite_primes _ ) |>.2; exact Nat.find_spec ( Nat.exists_infinite_primes _ ) |>.2 ] ) |>.2 fun h => h_r_not_div_Q <| dvd_trans h h_div

/-
For any k in the t-th block, phi_A(n_seq k)/n_seq k <= phi(n_seq k/r_seq t)/(n_seq k/r_seq t) + 1/r_seq t.
-/
lemma n_seq_phi_bound_correct (t : ℕ) (k : ℕ)
    (ht : t ≥ 1)
    (hk : k ∈ Finset.Icc (2^t - 1) (2^(t+1) - 2)) :
    (phi_A n_seq k : ℚ) / n_seq k ≤ (Nat.totient (n_seq k / r_seq t) : ℚ) / (n_seq k / r_seq t) + 1 / r_seq t := by
      -- Apply `lem_primeblock` with $p = r_seq t$ and $q = n_seq k / r_seq t$.
      have h_apply_lemma : (phi_A n_seq k : ℚ) / (n_seq k : ℚ) ≤ ((Nat.totient (n_seq k / r_seq t) : ℚ) / (n_seq k / r_seq t)) + (1 / (r_seq t : ℚ)) := by
        have h_coprime : Nat.Coprime (r_seq t) (n_seq k / r_seq t) := by
          exact r_seq_coprime_aux t k ht hk
        have h_apply_lemma : n_seq k = r_seq t * (n_seq k / r_seq t) ∧ (∀ d, d ∣ (n_seq k / r_seq t) → d < (n_seq k / r_seq t) → ∃ j < k, n_seq j = r_seq t * d) := by
          refine' ⟨ Eq.symm ( Nat.mul_div_cancel' _ ), _ ⟩;
          · unfold n_seq;
            field_simp;
            rw [ show Nat.log 2 ( k + 1 ) = t from _ ];
            · split_ifs <;> simp_all +decide [ Nat.dvd_iff_mod_eq_zero ];
              exact absurd hk ( Nat.sub_ne_zero_of_lt ( one_lt_pow₀ one_lt_two ( by linarith ) ) );
            · rw [ Nat.log_eq_iff ] <;> norm_num;
              exact ⟨ by linarith [ Finset.mem_Icc.mp hk, Nat.sub_add_cancel ( Nat.one_le_pow t 2 zero_lt_two ) ], by linarith [ Finset.mem_Icc.mp hk, Nat.sub_add_cancel ( show 2 ≤ 2 ^ ( t + 1 ) from le_trans ( by decide ) ( pow_le_pow_right₀ ( by decide ) ( Nat.succ_le_succ ht ) ) ) ] ⟩;
          · exact fun d hd hd' => by obtain ⟨ j, hj₁, hj₂, hj₃ ⟩ := n_seq_divisors_property t k ht hk d hd hd'; exact ⟨ j, hj₂, hj₃ ⟩ ;
        convert lem_primeblock n_seq k ( r_seq t ) ( n_seq k / r_seq t ) n_seq_strictMono _ _ _ _ _ using 1;
        any_goals tauto;
        · rw [ Nat.cast_div ( h_apply_lemma.1.symm ▸ dvd_mul_right _ _ ) ( Nat.cast_ne_zero.mpr <| by intro h; simp_all +singlePass ) ];
        · rcases t with ( _ | t ) <;> norm_num [ r_seq_spec ] at *;
        · rcases x : n_seq k / r_seq t with ( _ | _ | k ) <;> simp +arith +decide [ x ] at *;
          exact Nat.Prime.ne_one ( show Nat.Prime ( r_seq t ) from Nat.recOn t ( by norm_num [ show r_seq 0 = 2 from rfl ] ) fun n ihn => Nat.find_spec ( Nat.exists_infinite_primes _ ) |>.2 ) h_coprime;
      convert h_apply_lemma using 1

/-
The sum of phi_A(n_seq k)/n_seq k over block t is bounded by 2 * A_val t * 2^t.
-/
lemma block_sum_bound (t : ℕ) (ht : t ≥ 1) :
    ∑ k ∈ Finset.Icc (2^t - 1) (2^(t+1) - 2), (phi_A n_seq k : ℝ) / n_seq k ≤ (2 * A_val t) * (2^t : ℝ) := by
      -- By Lemma `n_seq_phi_bound_correct`, each term in the sum is bounded above by $\phi(n_k/r_t)/n_k/r_t + 1/r_t$.
      have h_sum_bound : ∑ k ∈ Finset.Icc (2 ^ t - 1) (2 ^ (t + 1) - 2), (phi_A n_seq k : ℚ) / (n_seq k) ≤ ∑ k ∈ Finset.Icc (2 ^ t - 1) (2 ^ (t + 1) - 2), ((Nat.totient (n_seq k / r_seq t) : ℚ) / (n_seq k / r_seq t) + 1 / r_seq t) := by
        apply Finset.sum_le_sum
        intro k hk
        apply n_seq_phi_bound_correct t k ht hk;
      -- Since $1/r_seq t \leq A_val t$, we can replace $2^t / r_seq t$ with $2^t * A_val t$ in the sum.
      have h_sum_bound_replace : ∑ k ∈ Finset.Icc (2 ^ t - 1) (2 ^ (t + 1) - 2), ((Nat.totient (n_seq k / r_seq t) : ℚ) / (n_seq k / r_seq t) + 1 / r_seq t) ≤ (2 ^ t : ℚ) * A_val t + (2 ^ t : ℚ) * A_val t := by
        have h_sum_bound_replace : ∑ k ∈ Finset.Icc (2 ^ t - 1) (2 ^ (t + 1) - 2), ((Nat.totient (n_seq k / r_seq t) : ℚ) / (n_seq k / r_seq t) + 1 / r_seq t) = (2 ^ t : ℚ) * A_val t + (2 ^ t : ℚ) / r_seq t := by
          convert sum_bound_eval t ht using 1;
          · norm_num [ ← @Rat.cast_inj ℝ ];
          · norm_num;
        have h_inv_r_seq_le_A_val : (1 : ℚ) / r_seq t ≤ A_val t := by
          convert inv_r_seq_le_A_val t ht using 1;
          norm_num;
        simp_all +decide [ div_eq_mul_inv ];
      -- By combining the inequalities from h_sum_bound and h_sum_bound_replace, we conclude the proof.
      have h_final : ∑ k ∈ Finset.Icc (2 ^ t - 1) (2 ^ (t + 1) - 2), (phi_A n_seq k : ℚ) / (n_seq k) ≤ (2 ^ t : ℚ) * A_val t + (2 ^ t : ℚ) * A_val t := by
        exact le_trans ( mod_cast h_sum_bound ) h_sum_bound_replace;
      convert h_final using 1 ; push_cast ; ring;
      push_cast; ring;

/-
There exists a strictly increasing sequence A={n_1<n_2<...} of positive integers such that lim_{N->infinity} (1/N) * sum_{k=1}^N phi_A(k)/n_k = 0.
-/
theorem thm_main : ∃ n : ℕ → ℕ, StrictMono n ∧ Filter.Tendsto (fun (N : ℕ) => (1 / (N : ℝ)) * ∑ k ∈ Finset.Icc 1 N, (phi_A n k : ℝ) / (n k : ℝ)) Filter.atTop (nhds 0) := by
  refine' ⟨ n_seq, ?_, _ ⟩;
  · exact n_seq_strictMono;
  · -- Apply the lemma `lem_block` with the sequence `a_k = phi_A(n_seq, k)/n_seq k` and `c_t = 2 * A_val t`.
    have h_apply_lemma : Filter.Tendsto (fun N : ℕ => (1 / N : ℝ) * ∑ k ∈ Finset.Icc 1 N, (phi_A n_seq k : ℝ) / n_seq k) Filter.atTop (nhds 0) := by
      have h_bound : ∀ k, 0 ≤ (phi_A n_seq k : ℝ) / n_seq k ∧ (phi_A n_seq k : ℝ) / n_seq k ≤ 1 := by
        intro k;
        refine' ⟨ by positivity, div_le_one_of_le₀ _ _ ⟩ <;> norm_cast <;> norm_num [ phi_A ];
        exact le_trans ( Finset.card_le_card ( show Finset.filter ( fun m => 1 ≤ m ∧ ∀ j < k, ¬n_seq k / m.gcd ( n_seq k ) = n_seq j ) ( Finset.range ( n_seq k + 1 ) ) ⊆ Finset.Ico 1 ( n_seq k + 1 ) from fun x hx => Finset.mem_Ico.mpr ⟨ by linarith [ Finset.mem_filter.mp hx ], by linarith [ Finset.mem_range.mp ( Finset.mem_filter.mp hx |>.1 ) ] ⟩ ) ) ( by simp +arith +decide )
      have h_c_nonneg : ∀ t, 0 ≤ 2 * A_val t := by
        exact fun t => mul_nonneg zero_le_two <| Finset.prod_nonneg fun _ _ => sub_nonneg.2 <| div_le_self zero_le_one <| by norm_cast; linarith [ Nat.Prime.two_le <| Nat.prime_nth_prime ‹_› ] ;
      have h_c_to_zero : Filter.Tendsto (fun t => 2 * A_val t) Filter.atTop (nhds 0) := by
        convert A_val_tendsto_zero.const_mul 2 using 2 ; ring
      have h_sum : ∀ t ≥ 1, ∑ k ∈ Finset.Icc (2^t - 1) (2^(t+1) - 2), (phi_A n_seq k : ℝ) / n_seq k ≤ (2 * A_val t) * (2^t : ℝ) := by
        convert block_sum_bound using 1
      apply_rules [ @lem_block ];
    simpa only [ one_div, inv_mul_eq_div ] using h_apply_lemma

open scoped BigOperators

open Filter

open Topology

/-- `phiA n k` counts the integers `m` with `1 ≤ m ≤ n k` such that the reduced denominator
of `m / n k` is not equal to any earlier term `n j` (for `j < k`).

Here the reduced denominator of `m / n` is `n / Nat.gcd m n`. -/
def phiA (n : ℕ → ℕ) (k : ℕ) : ℕ :=
  ((Finset.Icc 1 (n k)).filter (fun m =>
      ∀ j ∈ Finset.range k, n k / Nat.gcd m (n k) ≠ n j)).card

/-- The Cesàro mean `(1/N) * ∑_{k < N} φ_A(k)/n_k` as an `ℝ`-valued sequence. -/
noncomputable def cesaroPhi (n : ℕ → ℕ) (N : ℕ) : ℝ :=
  ((N : ℝ)⁻¹) *
    ∑ k ∈ Finset.range N, (phiA n k : ℝ) / (n k : ℝ)

/-
"Is there an infinite strictly increasing sequence `A = {n₁ < n₂ < ...}` such that
`lim_{N→∞} (1/N) * ∑_{k≤N} φ_A(k)/n_k = 0`?"

Notes:
* We index from `0` in Lean: `n 0` corresponds to `n₁`, `n 1` to `n₂`, etc.
* Then `∑ k in range N` sums the first `N` terms, matching `∑_{1≤k≤N}` up to this index shift.

The Erdős-Graham conjecture is true: there exists a strictly increasing sequence A such that the Cesaro mean of phi_A(k)/n_k tends to 0. We use the constructed sequence n_seq.
-/
theorem erdos_1000_true :
  ∃ n : ℕ → ℕ,
    StrictMono n ∧
    (∀ k, 0 < n k) ∧
    Tendsto (cesaroPhi n) atTop (𝓝 (0 : ℝ)) := by
  -- We apply `lem_block` to the sequence `a k = (phi_A n_seq k : ℝ) / n_seq k`.
  have h_apply_lem_block : Tendsto (fun N : ℕ => (1 / (N : ℝ)) * ∑ k ∈ Finset.Icc 1 N, (phiA n_seq k : ℝ) / (n_seq k : ℝ)) Filter.atTop (nhds 0) := by
    -- Applying the lemma `lem_block` to the sequence `a k = (phi_A n_seq k : ℝ) / n_seq k`.
    have h_apply_lem_block : ∀ (a : ℕ → ℝ), (∀ k, 0 ≤ a k ∧ a k ≤ 1) → Filter.Tendsto (fun t : ℕ => (Finset.range t).prod (fun i => 1 - 1 / (2 * (Nat.nth Nat.Prime i : ℝ)))) Filter.atTop (nhds 0) → (∀ t ≥ 1, ∑ k ∈ Finset.Icc (2^t - 1) (2^(t+1) - 2), a k ≤ (2 * (Finset.range t).prod (fun i => 1 - 1 / (2 * (Nat.nth Nat.Prime i : ℝ)))) * (2^t : ℝ)) → Filter.Tendsto (fun N : ℕ => (1 / (N : ℝ)) * ∑ k ∈ Finset.Icc 1 N, a k) Filter.atTop (nhds 0) := by
      intros a ha h_prod h_sum_bound
      apply lem_block a (fun t => 2 * (Finset.range t).prod (fun i => 1 - 1 / (2 * (Nat.nth Nat.Prime i : ℝ)))) ha (fun t => by
        exact mul_nonneg zero_le_two <| Finset.prod_nonneg fun _ _ => sub_nonneg.2 <| div_le_self zero_le_one <| by norm_cast; linarith [ Nat.Prime.two_le <| Nat.prime_nth_prime ‹_› ] ;) (by
      simpa using h_prod.const_mul 2) h_sum_bound;
    apply h_apply_lem_block;
    · intro k
      simp [phiA];
      exact ⟨ by positivity, div_le_one_of_le₀ ( mod_cast le_trans ( Finset.card_filter_le _ _ ) ( by norm_num ) ) ( by positivity ) ⟩;
    · convert A_val_tendsto_zero using 1;
    · intro t ht; convert block_sum_bound t ht using 1 ;
      unfold phiA phi_A; norm_num [ Finset.sum_filter, Finset.sum_Ico_eq_sum_range ] ;
      congr! 3;
      congr 1 with m ; simp +arith +decide [ Nat.lt_succ_iff ];
      tauto;
  refine' ⟨ n_seq, n_seq_strictMono, _, _ ⟩;
  · intro k;
    induction' k with k ih;
    · unfold n_seq; norm_num;
    · exact lt_of_lt_of_le ih ( n_seq_strictMono.monotone ( Nat.le_succ _ ) );
  · -- Since `cesaroPhi` sums from `k=0` to `N-1`, we need to adjust the index to match `h_apply_lem_block`.
    have h_shift : Filter.Tendsto (fun N : ℕ => (1 / (N : ℝ)) * ∑ k ∈ Finset.range N, (phiA n_seq k : ℝ) / (n_seq k : ℝ)) Filter.atTop (nhds 0) := by
      -- The term `a 0 = 1`, so the term `a 0 / N` tends to 0.
      have h_a0 : Filter.Tendsto (fun N : ℕ => (phiA n_seq 0 : ℝ) / (n_seq 0 : ℝ) / (N : ℝ)) Filter.atTop (nhds 0) := by
        exact tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop;
      -- The term `(1/N) * ∑_{k=1}^{N-1} a k` is `((N-1)/N) * (1/(N-1) * ∑_{k=1}^{N-1} a k)`.
      have h_shift : Filter.Tendsto (fun N : ℕ => ((N - 1 : ℝ) / N) * (1 / (N - 1 : ℝ)) * ∑ k ∈ Finset.Icc 1 (N - 1), (phiA n_seq k : ℝ) / (n_seq k : ℝ)) Filter.atTop (nhds 0) := by
        have h_shift : Filter.Tendsto (fun N : ℕ => ((N - 1 : ℝ) / N) * (1 / (N - 1 : ℝ)) * ∑ k ∈ Finset.Icc 1 (N - 1), (phiA n_seq k : ℝ) / (n_seq k : ℝ)) Filter.atTop (nhds 0) := by
          have h_avg : Filter.Tendsto (fun N : ℕ => (1 / (N - 1 : ℝ)) * ∑ k ∈ Finset.Icc 1 (N - 1), (phiA n_seq k : ℝ) / (n_seq k : ℝ)) Filter.atTop (nhds 0) := by
            rw [ ← Filter.tendsto_add_atTop_iff_nat 1 ] ; aesop;
          convert h_avg.mul ( show Filter.Tendsto ( fun N : ℕ => ( N - 1 : ℝ ) / N ) Filter.atTop ( nhds 1 ) from ?_ ) using 2 <;> ring_nf;
          simpa using Filter.Tendsto.sub ( tendsto_const_nhds.congr' ( by filter_upwards [ Filter.eventually_ne_atTop 0 ] with N hN; aesop ) ) ( tendsto_inverse_atTop_nhds_zero_nat );
        convert h_shift using 1;
      have h_split : ∀ N : ℕ, N ≥ 1 → (1 / (N : ℝ)) * ∑ k ∈ Finset.range N, (phiA n_seq k : ℝ) / (n_seq k : ℝ) = (phiA n_seq 0 : ℝ) / (n_seq 0 : ℝ) / (N : ℝ) + ((N - 1 : ℝ) / N) * (1 / (N - 1 : ℝ)) * ∑ k ∈ Finset.Icc 1 (N - 1), (phiA n_seq k : ℝ) / (n_seq k : ℝ) := by
        intro N hN; erw [ Finset.sum_Ico_eq_sub _ ] <;> norm_num [ Finset.sum_range_succ' ] ; ring_nf;
        cases N <;> norm_num [ add_comm, Finset.sum_range_succ' ] at * ; ring_nf;
        by_cases h : ‹_› = 0 <;> simp +decide [ h, mul_assoc, mul_comm ] ; ring;
      simpa using Filter.Tendsto.congr' ( by filter_upwards [ Filter.eventually_ge_atTop 1 ] with N hN; aesop ) ( h_a0.add h_shift );
    exact h_shift.congr fun N => by simp +decide [ cesaroPhi ] ;
