/-
We prove Theorem 1 from the paper "Factorial divisibility with bounded primes beyond the logarithmic barrier: an infinitely-many n result of Erdős type".
The main result is `theorem_1`, which states that for any $r \ge 1$, there are infinitely many $n$ such that there exist $a_1, a_2 > 0$ with $a_1 + a_2 > n + \omega(r) \log n$ and $a_1! a_2! \mid n! P_r^n$.
The proof follows the strategy outlined in the paper, using a primewise reduction, Kummer's theorem, and probabilistic arguments to control the valuations of primes in a short interval.
-/

import Mathlib

namespace Erdos401b

set_option linter.mathlibStandardSet false

open scoped Classical

/-
p_j is the j-th prime number (1-indexed).
-/
noncomputable def p (j : ℕ) : ℕ := Nat.nth Nat.Prime (j - 1)

/-
P_r is the product of the first r primes.
-/
noncomputable def P (r : ℕ) : ℕ := ∏ j ∈ Finset.range r, p (j + 1)

/-
eta = 1/10, gamma = 9/70, omega(r) = (gamma/16) * (q-1)/log q where q = p_{r+1}.
-/
noncomputable def η : ℝ := 1 / 10

noncomputable def γ : ℝ := 9 / 70

noncomputable def ω (r : ℕ) : ℝ :=
  let q := (p (r + 1) : ℝ)
  (γ / 16) * (q - 1) / Real.log q

/-
q = p_{r+1} is the first prime not dividing P_r.
-/
noncomputable def q (r : ℕ) : ℕ := p (r + 1)

/-
c = 2 * omega(r) = (gamma/8) * (q-1)/log q.
-/
noncomputable def c (r : ℕ) : ℝ := (γ / 8) * ((q r : ℝ) - 1) / Real.log (q r)

/-
k = floor(c log M).
-/
noncomputable def k_param (r M : ℕ) : ℕ := Nat.floor (c r * Real.log M)

/-
kappa_p(m) = v_p(choose(2m, m)).
-/
def κ (p m : ℕ) : ℕ := padicValNat p (Nat.choose (2 * m) m)

/-
W_p(m) = v_p(product_{i=1}^k (m+i)).
-/
def W (p m k : ℕ) : ℕ := padicValNat p (∏ i ∈ Finset.range k, (m + 1 + i))

/-
W_p(m) is the difference of valuations of (m+k)! and m!.
-/
lemma W_eq_val_factorial (p m k : ℕ) (hp : p.Prime) :
    W p m k = padicValNat p (Nat.factorial (m + k)) - padicValNat p (Nat.factorial m) := by
  -- We can express the product $\prod_{i=0}^{k-1} (m + 1 + i)$ as $\frac{(m + k)!}{m!}$.
  have h_prod : ∏ i ∈ Finset.range k, (m + 1 + i) = Nat.factorial (m + k) / Nat.factorial m := by
    exact Eq.symm ( Nat.div_eq_of_eq_mul_left ( Nat.factorial_pos _ ) <| Nat.recOn k ( by norm_num ) fun n ih => by simp +decide [ Nat.factorial, Finset.prod_range_succ ] at * ; nlinarith );
  unfold W;
  rw [ h_prod, ← Nat.factorization_def, ← Nat.factorization_def, Nat.factorization_div ];
  · simp +decide [ hp, Nat.factorization ];
  · exact Nat.factorial_dvd_factorial ( Nat.le_add_right _ _ );
  · assumption;
  · assumption

/-
A prime divides P_r iff it is less than or equal to p_r.
-/
lemma prime_dvd_P_iff (r : ℕ) (hr : r ≥ 1) (pp : ℕ) (hpp : pp.Prime) :
    pp ∣ P r ↔ pp ≤ p r := by
  constructor;
  · intro h;
    -- Since $pp$ divides $P_r$, it must divide at least one of the primes in the product $\prod_{j=1}^r p_j$.
    obtain ⟨j, hj⟩ : ∃ j ∈ Finset.range r, pp ∣ p (j + 1) := by
      unfold P at h;
      haveI := Fact.mk hpp; simp_all +decide [ ← ZMod.natCast_eq_zero_iff, Finset.prod_eq_zero_iff ] ;
    have h_le : pp ≤ p (j + 1) := by
      exact Nat.le_of_dvd ( Nat.Prime.pos ( by exact Nat.prime_nth_prime _ ) ) hj.2;
    refine le_trans h_le ?_;
    refine' Nat.nth_monotone _ _;
    · exact Nat.infinite_setOf_prime;
    · exact Nat.le_pred_of_lt ( Finset.mem_range.mp hj.1 );
  · intro hpp_le_pr
    have h_prime_divisors : ∀ {q : ℕ}, Nat.Prime q → q ≤ p r → q ∈ Finset.image (fun j => p (j + 1)) (Finset.range r) := by
      -- Since $q$ is prime and $q \leq p_r$, it must be one of the first $r$ primes.
      intros q hq hq_le_pr
      have hq_prime_index : ∃ j ∈ Finset.range r, q = p (j + 1) := by
        -- Since $q$ is prime and $q \leq p_r$, it must be one of the first $r$ primes by definition of $p$.
        have hq_prime_index : ∃ j < r, q = Nat.nth Nat.Prime j := by
          refine' ⟨ Nat.count ( Nat.Prime ) q, _, _ ⟩;
          · contrapose! hq_le_pr;
            refine' Nat.nth_lt_of_lt_count _;
            exact lt_of_lt_of_le ( Nat.pred_lt ( ne_bot_of_gt hr ) ) hq_le_pr;
          · rw [ Nat.nth_count ] ; aesop;
        aesop;
      aesop;
    obtain ⟨ j, hj, rfl ⟩ := Finset.mem_image.mp ( h_prime_divisors hpp hpp_le_pr ) ; exact Finset.dvd_prod_of_mem _ ( Finset.mem_range.mpr <| by linarith [ Finset.mem_range.mp hj ] ) ;

/-
P_r is squarefree.
-/
lemma P_squarefree (r : ℕ) : Squarefree (P r) := by
  -- By definition of $P$, $P_r$ is the product of distinct primes $p_1, p_2, \ldots, p_r$.
  have hP_r_prime_factors : P r = ∏ j ∈ Finset.range r, Nat.nth Nat.Prime j := by
    exact rfl;
  rw [ hP_r_prime_factors ];
  induction' r with r ih;
  · norm_num;
  · induction' r + 1 with r ih <;> simp_all +decide [ Finset.prod_range_succ, Nat.squarefree_mul_iff ];
    exact ⟨ Nat.Coprime.prod_left fun i hi => Nat.coprime_comm.mp <| Nat.Prime.coprime_iff_not_dvd ( Nat.prime_nth_prime _ ) |>.2 <| Nat.not_dvd_of_pos_of_lt ( Nat.Prime.pos <| Nat.prime_nth_prime _ ) <| Nat.nth_strictMono ( Nat.infinite_setOf_prime ) <| Finset.mem_range.mp hi, Nat.prime_nth_prime _ |> fun h => h.squarefree ⟩

/-
The p-adic valuation of P_r is 1 if p <= p_r, and 0 otherwise.
-/
lemma padicValNat_P (r : ℕ) (hr : r ≥ 1) (pp : ℕ) (hp : pp.Prime) :
    padicValNat pp (P r) = if pp ≤ p r then 1 else 0 := by
  have h_padic_val : padicValNat pp (P r) ≤ 1 := by
    have := P_squarefree r;
    have := this.natFactorization_le_one pp;
    rw [ Nat.factorization_def ] at this ; aesop;
    assumption;
  split_ifs <;> simp_all [ Nat.Prime.dvd_iff_not_coprime ];
  · have h_div : pp ∣ P r := by
      (expose_names; exact (prime_dvd_P_iff r hr pp hp).mpr h);
    have h_not_div : ¬(pp ^ 2 ∣ P r) := by
      have h_not_div : Squarefree (P r) := by
        exact P_squarefree r;
      exact fun h => absurd ( h_not_div.squarefree_of_dvd h ) ( by rw [ sq, Nat.squarefree_mul_iff ] ; aesop );
    have h_padic_val_eq : padicValNat pp (P r) ≥ 1 := by
      contrapose! h_not_div; aesop;
    grind;
  · exact Or.inr <| Or.inr <| hp.coprime_iff_not_dvd.mpr fun h => by have := prime_dvd_P_iff r hr pp hp |>.1 h; linarith;

/-
The divisibility condition is equivalent to W_p(m) <= kappa_p(m) + 2m for p <= p_r, and W_p(m) <= kappa_p(m) for p > p_r.
-/
lemma primewise_target (r m k : ℕ) (hr : r ≥ 1) :
    (Nat.factorial (m + k) * Nat.factorial m) ∣ (Nat.factorial (2 * m) * (P r)^(2 * m)) ↔
    ∀ pp : ℕ, pp.Prime → W pp m k ≤ κ pp m + if pp ≤ p r then 2 * m else 0 := by
  -- By the lemma on p-adic valuations, we can rewrite the divisibility condition in terms of p-adic valuations.
  have h_val : (Nat.factorial (m + k) * Nat.factorial m) ∣ (Nat.factorial (2 * m)) * (P r) ^ (2 * m) ↔
    ∀ pp : ℕ, pp.Prime → padicValNat pp (Nat.factorial (m + k) * Nat.factorial m) ≤ padicValNat pp (Nat.factorial (2 * m)) + 2 * m * padicValNat pp (P r) := by
      rw [ ← Nat.factorization_le_iff_dvd ] <;> try positivity;
      · rw [ Nat.factorization_mul, Nat.factorization_mul ] <;> norm_num;
        · constructor <;> intro h pp <;> have := h pp <;> simp_all +decide [ ← Nat.factorization_def ];
          · rw [ Nat.factorization_mul ] <;> first | positivity | aesop;
          · by_cases hpp : Nat.Prime pp <;> simp_all +decide [ Nat.factorization_mul, Nat.factorial_ne_zero ];
        · positivity;
        · exact fun h => absurd h <| Finset.prod_ne_zero_iff.mpr fun i hi => Nat.Prime.ne_zero <| Nat.prime_nth_prime _;
        · positivity;
        · positivity;
      · norm_num [ Nat.factorial_ne_zero, P ];
        exact fun h => absurd h <| ne_of_gt <| Finset.prod_pos fun i hi => Nat.Prime.pos <| by unfold p; aesop;
  simp_all +decide [ W, κ ];
  -- Apply the lemma on p-adic valuations to rewrite the divisibility condition in terms of p-adic valuations.
  have h_val_rewrite : ∀ pp : ℕ, Nat.Prime pp → padicValNat pp ((m + k).factorial * m.factorial) = padicValNat pp (∏ i ∈ Finset.range k, (m + 1 + i)) + 2 * padicValNat pp (Nat.factorial m) := by
    intros pp hpp
    have h_val_rewrite : padicValNat pp ((m + k).factorial) = padicValNat pp (∏ i ∈ Finset.range k, (m + 1 + i)) + padicValNat pp (Nat.factorial m) := by
      have h_val_rewrite : (m + k).factorial = (∏ i ∈ Finset.range k, (m + 1 + i)) * m.factorial := by
        exact Nat.recOn k ( by norm_num ) fun n ih => by rw [ Nat.add_succ, Nat.factorial_succ, Finset.prod_range_succ ] ; nlinarith;
      haveI := Fact.mk hpp; rw [ h_val_rewrite, padicValNat.mul ( Finset.prod_ne_zero_iff.mpr fun _ _ => by positivity ) ( Nat.factorial_ne_zero _ ) ] ;
    haveI := Fact.mk hpp; rw [ padicValNat.mul ( by positivity ) ( by positivity ) ] ; linarith;
  have h_val_rewrite : ∀ pp : ℕ, Nat.Prime pp → padicValNat pp ((2 * m).factorial) = padicValNat pp ((2 * m).choose m) + 2 * padicValNat pp (Nat.factorial m) := by
    intro pp pp_prime; rw [ Nat.choose_eq_factorial_div_factorial ( by linarith ) ] ;
    haveI := Fact.mk pp_prime; rw [ ← padicValNat.pow, ← padicValNat.mul ] <;> norm_num [ two_mul, Nat.factorial_ne_zero ] ;
    · rw [ sq, Nat.div_mul_cancel ( Nat.factorial_mul_factorial_dvd_factorial_add _ _ ) ];
    · exact Nat.le_of_dvd ( Nat.factorial_pos _ ) ( Nat.factorial_mul_factorial_dvd_factorial_add _ _ );
  have h_val_rewrite : ∀ pp : ℕ, Nat.Prime pp → padicValNat pp (P r) = if pp ≤ p r then 1 else 0 := by
    intros pp hpp
    apply padicValNat_P r hr pp hpp;
  grind +ring
  
/-
The p-adic valuation of n! is at most n.
-/
lemma padicValNat_factorial_le (n p : ℕ) (hp : p.Prime) :
    padicValNat p (Nat.factorial n) ≤ n := by
  haveI := Fact.mk hp;
  -- The $p$-adic valuation of $n!$ is given by the sum of the floor of $n/p^k$ for $k$ from $1$ to infinity.
  have h_padic_val : padicValNat p (Nat.factorial n) = ∑ k ∈ Finset.Ico 1 (Nat.log p n + 1), (n / p ^ k) := by
    rw [ padicValNat_factorial ];
    grind;
  -- Each term in the sum $\sum_{k=1}^{\infty} \left\lfloor \frac{n}{p^k} \right\rfloor$ is less than or equal to $\frac{n}{p^k}$, and the sum is finite.
  have h_sum_le : ∑ k ∈ Finset.Ico 1 (Nat.log p n + 1), (n / p ^ k) ≤ n * (∑ k ∈ Finset.Ico 1 (Nat.log p n + 1), (1 / p ^ k : ℝ)) := by
    norm_num [ Finset.mul_sum _ _ _ ];
    exact Finset.sum_le_sum fun _ _ => by rw [ ← div_eq_mul_inv ] ; rw [ le_div_iff₀ ( pow_pos ( Nat.cast_pos.mpr hp.pos ) _ ) ] ; norm_cast; linarith [ Nat.div_mul_le_self n ( p ^ ‹_› ) ] ;
  -- The series $\sum_{k=1}^{\infty} \frac{1}{p^k}$ is a geometric series with sum $\frac{1}{p-1}$.
  have h_geo_series : ∑ k ∈ Finset.Ico 1 (Nat.log p n + 1), (1 / p ^ k : ℝ) < 1 := by
    ring_nf;
    erw [ geom_sum_Ico ] <;> norm_num [ hp.ne_zero ];
    · rw [ div_lt_iff_of_neg ] <;> nlinarith only [ show ( p : ℝ ) ≥ 2 by exact_mod_cast hp.two_le, inv_pos.mpr ( show ( p : ℝ ) > 0 by exact_mod_cast hp.pos ), inv_pos.mpr ( show ( p ^ ( 1 + Nat.log p n ) : ℝ ) > 0 by exact_mod_cast pow_pos hp.pos _ ), mul_inv_cancel₀ ( show ( p : ℝ ) ≠ 0 by exact_mod_cast hp.ne_zero ), mul_inv_cancel₀ ( show ( p ^ ( 1 + Nat.log p n ) : ℝ ) ≠ 0 by exact_mod_cast pow_ne_zero _ hp.ne_zero ), pow_le_pow_right₀ ( show ( p : ℝ ) ≥ 1 by exact_mod_cast hp.one_lt.le ) ( show 1 + Nat.log p n ≥ 1 by norm_num ) ];
    · exact hp.ne_one;
  exact h_padic_val ▸ Nat.cast_le.mp ( h_sum_le.trans ( mul_le_of_le_one_right ( Nat.cast_nonneg _ ) h_geo_series.le ) )
  
/-
For any prime p and k <= m, W_p(m) <= 2m.
-/
lemma paid_primes (m k p : ℕ) (hp : p.Prime) (hk : k ≤ m) : W p m k ≤ 2 * m := by
  exact le_trans ( W_eq_val_factorial p m k hp ▸ tsub_le_self ) ( by linarith [ padicValNat_factorial_le ( m + k ) p hp ] )

/-
t_p = ceil(gamma/4 * log_p M).
-/
noncomputable def t (p M : ℕ) : ℕ := Nat.ceil (γ / 4 * (Real.log M / Real.log p))

/-
If p^j divides m+i and i is small, then kappa_p(m) >= j.
-/
lemma kappa_ge_j (p m i j : ℕ) (hp : p.Prime) (hi_pos : 0 < i) (h_div : p^j ∣ m + i) (h_small : 2 * i < p) :
    j ≤ κ p m := by
  -- By definition of κ, we know that κ_p(m) is the number of t such that p^t ≤ m % p^t + m % p^t = 2 * (m % p^t).
  have h_kappa_def : κ p m = ((Finset.Ico 1 (Nat.log p (2 * m) + 1)).filter (fun t => p ^ t ≤ 2 * (m % p ^ t))).card := by
    unfold κ;
    haveI := Fact.mk hp;
    rw [ padicValNat_choose ];
    any_goals exact Nat.lt_succ_self _;
    · simp +arith +decide [ two_mul ];
    · linarith;
  -- For t in 1..j, this condition holds.
  have h_cond : ∀ t ∈ Finset.Ico 1 (j + 1), p ^ t ≤ 2 * (m % p ^ t) := by
    intro t ht
    have h_mod : m % p ^ t = p ^ t - i % p ^ t := by
      -- Since $p^j \mid m + i$, we have $m \equiv -i \pmod{p^t}$ for any $t \leq j$.
      have h_mod_eq : m ≡ -i [ZMOD p ^ t] := by
        exact Int.ModEq.symm <| Int.modEq_of_dvd <| by simpa [ ← Int.natCast_dvd_natCast ] using dvd_trans ( pow_dvd_pow _ <| Finset.mem_Ico.mp ht |>.2 |> Nat.lt_succ_iff.mp ) h_div;
      -- Since $p^t \mid m + i$, we have $m \equiv -i \pmod{p^t}$, which implies $m \% p^t = p^t - i \% p^t$.
      have h_mod_eq : m % p ^ t = (p ^ t - i % p ^ t) % p ^ t := by
        rw [ ← Int.natCast_inj ] ; simp_all +decide [ Int.ModEq ];
        rw [ Nat.cast_sub ( Nat.le_of_lt <| Nat.mod_lt _ <| pow_pos hp.pos _ ) ] ; simp +decide [ Int.emod_eq_emod_iff_emod_sub_eq_zero ];
      rw [ h_mod_eq, Nat.mod_eq_of_lt ( Nat.sub_lt ( pow_pos hp.pos _ ) ( Nat.pos_of_ne_zero ( by exact Nat.modEq_zero_iff_dvd.not.mpr <| Nat.not_dvd_of_pos_of_lt hi_pos <| by nlinarith [ Nat.pow_le_pow_right hp.one_lt.le <| show t ≥ 1 from Finset.mem_Ico.mp ht |>.1 ] ) ) ) ];
    rw [ h_mod, Nat.mul_sub_left_distrib ];
    exact le_tsub_of_add_le_left ( by linarith [ Nat.mod_le i ( p ^ t ), pow_le_pow_right₀ hp.one_lt.le ( show t ≥ 1 by linarith [ Finset.mem_Ico.mp ht ] ) ] );
  rw [ h_kappa_def ];
  refine' le_trans _ ( Finset.card_mono <| show Finset.Ico 1 ( j + 1 ) ⊆ Finset.filter ( fun t => p ^ t ≤ 2 * ( m % p ^ t ) ) ( Finset.Ico 1 ( Nat.log p ( 2 * m ) + 1 ) ) from fun x hx => Finset.mem_filter.mpr ⟨ Finset.mem_Ico.mpr ⟨ by linarith [ Finset.mem_Ico.mp hx ], _ ⟩, h_cond x hx ⟩ );
  · norm_num;
  · refine' Nat.lt_succ_of_le ( Nat.le_log_of_pow_le hp.one_lt _ );
    have := h_cond x hx;
    exact le_trans this ( Nat.mul_le_mul_left _ ( Nat.mod_le _ _ ) )

/-
Definitions of L, Q_val, and X.
L_p = floor((1-eta) log_p M).
Q_p = p^L_p.
X_p(m) counts digits d_u of m (for u < L_p) such that 2*d_u >= p+1.
-/
noncomputable def L (p M : ℕ) : ℕ := Nat.floor ((1 - η) * (Real.log M / Real.log p))

noncomputable def Q_val (p M : ℕ) : ℕ := p ^ (L p M)

noncomputable def X (p m M : ℕ) : ℕ := ((Nat.digits p m).take (L p M)).countP (fun d => 2 * d ≥ p + 1)

/-
V_p(m) is the maximum valuation in the block. W_p(m) is bounded by k/(p-1) + V_p(m).
-/
def V (p m k : ℕ) : ℕ := Finset.sup (Finset.range k) (fun i => padicValNat p (m + 1 + i))

/-
The number of multiples of q in (m, m+k] is at most k/q + 1.
-/
lemma count_le (m k q : ℕ) (hq : q > 0) : (m + k) / q - m / q ≤ k / q + 1 := by
  exact Nat.sub_le_of_le_add <| by nlinarith [ Nat.div_mul_le_self ( m + k ) q, Nat.div_add_mod ( m + k ) q, Nat.mod_lt ( m + k ) hq, Nat.div_mul_le_self m q, Nat.div_add_mod m q, Nat.mod_lt m hq, Nat.div_mul_le_self k q, Nat.div_add_mod k q, Nat.mod_lt k hq ] ;

/-
The sum of k/p^i for i from 1 to v is at most k/(p-1).
-/
lemma sum_div_pow_le (k v p : ℕ) (hp : p ≥ 2) : ∑ i ∈ Finset.range v, k / p ^ (i + 1) ≤ k / (p - 1) := by
  have h_sum_le : ∀ v : ℕ, ∑ i ∈ Finset.range v, k / p ^ (i + 1) ≤ k * (1 - (1 / p : ℝ) ^ v) / (p - 1) := by
    intro v
    have h_sum_le : ∑ i ∈ Finset.range v, (k / p ^ (i + 1) : ℝ) ≤ k * (1 - (1 / p : ℝ) ^ v) / (p - 1) := by
      induction v <;> simp_all +decide [ Finset.sum_range_succ, pow_succ, mul_assoc, div_eq_mul_inv ];
      refine le_trans ( add_le_add_right ‹_› _ ) ?_;
      rcases p with ( _ | _ | p ) <;> norm_num at *;
      -- Combine and simplify the terms on the left-hand side.
      field_simp
      ring_nf;
      norm_num;
    refine le_trans ?_ h_sum_le;
    rw [ Nat.cast_sum ] ; exact Finset.sum_le_sum fun _ _ => by rw [ le_div_iff₀ ( by positivity ) ] ; norm_cast ; nlinarith [ Nat.div_mul_le_self k ( p ^ ( ‹_› + 1 ) ), pow_pos ( zero_lt_two.trans_le hp ) ( ‹_› + 1 ) ] ;
  specialize h_sum_le v ; rw [ le_div_iff₀ ] at * <;> norm_num at * <;> try linarith;
  rw [ Nat.le_div_iff_mul_le ( Nat.sub_pos_of_lt hp ) ] ; rw [ ← @Nat.cast_le ℝ ] ; cases p <;> norm_num at * ; nlinarith [ inv_pos.mpr ( pow_pos ( by positivity : 0 < ( ( Nat.cast:ℕ →ℝ ) ‹_› + 1 ) ) v ) ] ;

/-
If j > V(p, m, k), then there are no multiples of p^j in (m, m+k].
-/
lemma N_eq_zero_of_gt_V (p m k j : ℕ) (hp : p.Prime) (hj : j > V p m k) : (m + k) / p ^ j - m / p ^ j = 0 := by
  refine Nat.sub_eq_zero_of_le ?_;
  contrapose! hj;
  -- Since $m / p^j < (m + k) / p^j$, there exists an integer $x \in (m, m+k]$ such that $p^j \mid x$.
  obtain ⟨x, hx⟩ : ∃ x ∈ Finset.Icc (m + 1) (m + k), p ^ j ∣ x := by
    use p ^ j * ((m + k) / p ^ j);
    exact ⟨ Finset.mem_Icc.mpr ⟨ by nlinarith [ Nat.div_add_mod ( m + k ) ( p ^ j ), Nat.mod_lt ( m + k ) ( pow_pos hp.pos j ), Nat.div_mul_le_self m ( p ^ j ), Nat.div_add_mod m ( p ^ j ), Nat.mod_lt m ( pow_pos hp.pos j ) ], by nlinarith [ Nat.div_mul_le_self ( m + k ) ( p ^ j ) ] ⟩, dvd_mul_right _ _ ⟩;
  refine' le_trans _ ( Finset.le_sup <| Finset.mem_range.mpr <| show x - ( m + 1 ) < k from _ );
  · haveI := Fact.mk hp; rw [ padicValNat_dvd_iff ] at hx; aesop;
  · rw [ tsub_lt_iff_left ] <;> linarith [ Finset.mem_Icc.mp hx.1 ]

lemma W_le_V (p m k : ℕ) (hp : p.Prime) : W p m k ≤ k / (p - 1) + V p m k := by
  -- By definition of $W$, we can write it as the difference of the p-adic valuations of $(m+k)!$ and $m!$. Using `padicValNat_factorial`, we express these valuations as sums.
  set b := Nat.log p (m + k) + 1 + 1 with hb
  have hW_sum : W p m k = ∑ i ∈ Finset.Ico 1 b, ((m + k) / p ^ i - m / p ^ i) := by
    have hW_sum : W p m k = padicValNat p (Nat.factorial (m + k)) - padicValNat p (Nat.factorial m) := by
      apply W_eq_val_factorial;
      assumption;
    have hW_sum : padicValNat p (Nat.factorial (m + k)) = ∑ i ∈ Finset.Ico 1 b, (m + k) / p ^ i ∧ padicValNat p (Nat.factorial m) = ∑ i ∈ Finset.Ico 1 b, m / p ^ i := by
      haveI := Fact.mk hp; rw [ padicValNat_factorial, padicValNat_factorial ] ; aesop;
      · exact Nat.lt_succ_of_le ( Nat.le_succ_of_le ( Nat.log_mono_right ( Nat.le_add_right _ _ ) ) );
      · linarith;
    rw [ ‹W p m k = _›, hW_sum.1, hW_sum.2, Nat.sub_eq_of_eq_add ];
    rw [ ← Finset.sum_add_distrib, Finset.sum_congr rfl fun _ _ => tsub_add_cancel_of_le <| Nat.div_le_div_right <| by linarith ];
  have hsum_bound : ∑ i ∈ Finset.Ico 1 b, ((m + k) / p ^ i - m / p ^ i) ≤ ∑ i ∈ Finset.Ico 1 (V p m k + 1), (k / p ^ i + 1) := by
    have hsum_bound : ∑ i ∈ Finset.Ico 1 b, ((m + k) / p ^ i - m / p ^ i) ≤ ∑ i ∈ Finset.Ico 1 (V p m k + 1), ((m + k) / p ^ i - m / p ^ i) := by
      have hW_truncated : ∀ i ∈ Finset.Ico (V p m k + 1) b, ((m + k) / p ^ i - m / p ^ i) = 0 := by
        intros i hi;
        exact N_eq_zero_of_gt_V p m k i hp ( by linarith [ Finset.mem_Ico.mp hi ] );
      rw [ ← Finset.sum_sdiff <| Finset.Ico_subset_Ico_right <| show V p m k + 1 ≤ b from _ ];
      · rw [ Finset.sum_eq_zero ] <;> aesop;
      · refine' Nat.succ_le_succ _;
        refine' Finset.sup_le fun i hi => _;
        have := Nat.ordProj_dvd ( m + 1 + i ) p;
        rw [ ← Nat.factorization_def ];
        · exact Nat.le_succ_of_le ( Nat.le_log_of_pow_le hp.one_lt <| by linarith [ Finset.mem_range.mp hi, Nat.le_of_dvd ( by linarith ) this ] );
        · assumption;
    refine le_trans hsum_bound <| Finset.sum_le_sum fun i hi => ?_;
    have := count_le m k ( p ^ i ) ( pow_pos hp.pos _ ) ; aesop;
  have hsum_div_pow_le : ∑ i ∈ Finset.Ico 1 (V p m k + 1), (k / p ^ i) ≤ k / (p - 1) := by
    convert sum_div_pow_le k ( V p m k ) p hp.two_le using 1;
    simp +arith +decide [ add_comm, Finset.sum_Ico_eq_sum_range ];
  simp_all +decide [ Finset.sum_add_distrib ];
  grind
  
/-
Probability of predicate P for m uniform in [M, 2M].
-/
noncomputable def prob_event (M : ℕ) (P : ℕ → Prop) [DecidablePred P] : ℝ :=
  ((Finset.Icc M (2 * M)).filter P).card / (M + 1)

/-
Definitions of prob_ZMod, theta, and mu.
prob_ZMod is the probability of P in ZMod Q.
theta(p) = (p-1)/(2p).
mu(p, M) = theta(p) * L(p, M).
-/
noncomputable def prob_ZMod (Q : ℕ) [NeZero Q] (P : ZMod Q → Prop) [DecidablePred P] : ℝ :=
  ((Finset.univ : Finset (ZMod Q)).filter P).card / (Q : ℝ)

noncomputable def theta (p : ℕ) : ℝ := ((p : ℝ) - 1) / (2 * (p : ℝ))

noncomputable def mu (p M : ℕ) : ℝ := theta p * (L p M : ℝ)

/-
Probability of a modular event in [M, 2M] is close to its probability in ZMod Q.
-/
lemma prob_event_le_prob_ZMod (M Q : ℕ) (P : ZMod Q → Prop) [DecidablePred P]
    [NeZero Q] (hM : M ≠ 0) (h_bound : (Q : ℝ) ≤ (M : ℝ) ^ (1 - η)) :
    prob_event M (fun m => P (m : ZMod Q)) ≤ prob_ZMod Q P + 2 / (M : ℝ) ^ η := by
  -- Since $Q \leq M^{1-\eta}$, we have $Q/(M+1) \leq M^{1-\eta}/M = 1/M^{\eta}$.
  have h_Q_div_M1 : (Q : ℝ) / (M + 1) ≤ 1 / (M : ℝ) ^ η := by
    field_simp;
    refine le_trans ( mul_le_mul_of_nonneg_right h_bound <| by positivity ) ?_;
    rw [ ← Real.rpow_add ] <;> norm_num [ hM ];
    positivity;
  -- The probability of P in [M, 2M] is at most the probability of P in ZMod Q plus the probability of P in the remainder block.
  have h_prob_remainder : (Finset.filter (fun m : ℕ => P (m : ZMod Q)) (Finset.Icc M (2 * M))).card ≤ (Finset.filter P (Finset.univ : Finset (ZMod Q))).card * ((M + 1) / Q) + Q := by
    -- The interval [M, 2M] can be divided into full blocks of length Q and a remainder block.
    have h_divide : Finset.Icc M (2 * M) ⊆ Finset.biUnion (Finset.range ((M + 1) / Q)) (fun i => Finset.Ico (M + i * Q) (M + (i + 1) * Q)) ∪ Finset.Ico (M + (M + 1) / Q * Q) (2 * M + 1) := by
      intro x hx;
      by_cases h_case : x < M + (M + 1) / Q * Q;
      · exact Finset.mem_union_left _ <| Finset.mem_biUnion.mpr ⟨ ( x - M ) / Q, Finset.mem_range.mpr <| Nat.div_lt_of_lt_mul <| by rw [ tsub_lt_iff_left ] <;> linarith [ Finset.mem_Icc.mp hx ], Finset.mem_Ico.mpr ⟨ by linarith [ Nat.div_mul_le_self ( x - M ) Q, Nat.sub_add_cancel <| show M ≤ x from Finset.mem_Icc.mp hx |>.1 ], by linarith [ Nat.div_add_mod ( x - M ) Q, Nat.mod_lt ( x - M ) <| NeZero.pos Q, Nat.sub_add_cancel <| show M ≤ x from Finset.mem_Icc.mp hx |>.1 ] ⟩ ⟩;
      · exact Finset.mem_union_right _ ( Finset.mem_Ico.mpr ⟨ by linarith [ Finset.mem_Icc.mp hx ], by linarith [ Finset.mem_Icc.mp hx ] ⟩ );
    -- Each full block of length Q contributes at most |A| to the count of m such that m mod Q in A.
    have h_full_blocks : (Finset.filter (fun m : ℕ => P (m : ZMod Q)) (Finset.biUnion (Finset.range ((M + 1) / Q)) (fun i => Finset.Ico (M + i * Q) (M + (i + 1) * Q)))).card ≤ (Finset.filter P (Finset.univ : Finset (ZMod Q))).card * ((M + 1) / Q) := by
      have h_full_blocks : ∀ i ∈ Finset.range ((M + 1) / Q), (Finset.filter (fun m : ℕ => P (m : ZMod Q)) (Finset.Ico (M + i * Q) (M + (i + 1) * Q))).card ≤ (Finset.filter P (Finset.univ : Finset (ZMod Q))).card := by
        intro i hi
        have h_full_block : Finset.image (fun m : ℕ => m : ℕ → ZMod Q) (Finset.filter (fun m : ℕ => P (m : ZMod Q)) (Finset.Ico (M + i * Q) (M + (i + 1) * Q))) ⊆ Finset.filter P (Finset.univ : Finset (ZMod Q)) := by
          intro x hx
          aesop;
        have := Finset.card_le_card h_full_block; rw [ Finset.card_image_of_injOn ] at this; aesop;
        intros m hm m' hm' h; simp_all +decide [ ZMod.natCast_eq_natCast_iff' ] ;
        exact le_antisymm ( Nat.le_of_not_lt fun hnm => by have := Nat.modEq_iff_dvd.mp h.symm; norm_num at this; nlinarith [ Int.le_of_dvd ( by linarith ) this ] ) ( Nat.le_of_not_lt fun hnm => by have := Nat.modEq_iff_dvd.mp h; norm_num at this; nlinarith [ Int.le_of_dvd ( by linarith ) this ] );
      rw [ Finset.filter_biUnion ] ; exact le_trans ( Finset.card_biUnion_le ) ( by simpa [ mul_comm ] using Finset.sum_le_sum h_full_blocks ) ;
    -- The remainder block contributes at most Q to the count of m such that m mod Q in A.
    have h_remainder_block : (Finset.filter (fun m : ℕ => P (m : ZMod Q)) (Finset.Ico (M + (M + 1) / Q * Q) (2 * M + 1))).card ≤ Q := by
      refine' le_trans ( Finset.card_le_card _ ) _;
      exact Finset.Ico ( M + ( M + 1 ) / Q * Q ) ( M + ( M + 1 ) / Q * Q + Q );
      · exact fun x hx => Finset.mem_Ico.mpr ⟨ Finset.mem_Ico.mp ( Finset.mem_filter.mp hx |>.1 ) |>.1, by linarith [ Finset.mem_Ico.mp ( Finset.mem_filter.mp hx |>.1 ) |>.2, Nat.div_add_mod ( M + 1 ) Q, Nat.mod_lt ( M + 1 ) ( NeZero.pos Q ) ] ⟩;
      · norm_num;
    refine le_trans ?_ ( add_le_add h_full_blocks h_remainder_block );
    rw [ ← Finset.card_union_add_card_inter ];
    exact le_add_right ( Finset.card_mono <| by intro x hx; specialize h_divide ( Finset.mem_filter.mp hx |>.1 ) ; aesop );
  -- The probability of P in [M, 2M] is at most the probability of P in ZMod Q plus the probability of P in the remainder block, divided by (M+1).
  have h_prob_remainder_div : (Finset.filter (fun m : ℕ => P (m : ZMod Q)) (Finset.Icc M (2 * M))).card / (M + 1 : ℝ) ≤ (Finset.filter P (Finset.univ : Finset (ZMod Q))).card / Q + Q / (M + 1 : ℝ) := by
    rw [ div_add_div, div_le_div_iff₀ ] <;> try positivity;
    · norm_cast;
      nlinarith [ Nat.div_mul_le_self ( M + 1 ) Q, Nat.zero_le ( ( Finset.filter P Finset.univ ).card * ( M + 1 ) ), Nat.zero_le ( Q * Q ), Nat.zero_le ( Q * ( M + 1 ) ) ];
    · exact mul_pos ( Nat.cast_pos.mpr <| NeZero.pos Q ) <| Nat.cast_add_one_pos _;
    · aesop;
  convert h_prob_remainder_div.trans ( add_le_add_left ( h_Q_div_M1.trans _ ) _ ) using 1 ; ring_nf!;
  exact le_mul_of_one_le_right ( by positivity ) ( by norm_num )

/-
Probability of a modular event in [M, 2M] is close to its probability in ZMod Q.
-/
lemma prob_event_le_prob_ZMod' (M Q : ℕ) (P : ZMod Q → Prop) [DecidablePred P]
    [NeZero Q] (hM : M ≠ 0) (h_bound : (Q : ℝ) ≤ (M : ℝ) ^ (1 - η)) :
    prob_event M (fun m => P (m : ZMod Q)) ≤ prob_ZMod Q P + 2 / (M : ℝ) ^ η := by
  exact prob_event_le_prob_ZMod M Q P hM h_bound
  
/-
X_fixed depends only on m mod p^L.
-/
def X_fixed (p L m : ℕ) : ℕ := ((Nat.digits p m).take L).countP (fun d => 2 * d ≥ p + 1)

lemma X_fixed_mod (p L m : ℕ) (hp : p.Prime) : X_fixed p L m = X_fixed p L (m % p ^ L) := by
  -- Let's rewrite m as m = q * p^L + r, where r < p^L.
  obtain ⟨q, r, hr⟩ : ∃ q r, m = q * p ^ L + r ∧ r < p ^ L := by
    exact ⟨ m / p ^ L, m % p ^ L, by rw [ Nat.div_add_mod' ], Nat.mod_lt _ ( pow_pos hp.pos _ ) ⟩;
  simp +decide [ hr.1, Nat.add_mod, Nat.mod_eq_of_lt hr.2 ];
  unfold X_fixed;
  have h_digits_eq : Nat.digits p (q * p ^ L + r) = Nat.digits p r ++ Nat.digits p (q * p ^ (L - (Nat.digits p r).length)) := by
    rw [ Nat.add_comm, Nat.digits_append_digits ];
    · rw [ mul_left_comm, ← pow_add, Nat.add_sub_of_le ];
      have := @Nat.digits_len p r;
      exact if hr : r = 0 then by simp +decide [ hr ] else by rw [ this hp.one_lt hr ] ; exact Nat.log_lt_of_lt_pow ( by positivity ) ( by linarith ) ;
    · exact hp.pos;
  rw [ h_digits_eq, List.take_append ];
  induction L - List.length ( Nat.digits p r ) <;> simp_all +decide [ pow_succ, ← mul_assoc ];
  rcases p with ( _ | _ | p ) <;> simp_all +decide [ mul_assoc ];
  cases q <;> simp_all +decide
  simp_all +decide [ Nat.mul_mod, Nat.mul_div_assoc ]

/-
Q_p <= M^(1-eta).
-/
lemma Q_le_bound (p M : ℕ) (hp : p.Prime) (hM : M ≠ 0) :
    (Q_val p M : ℝ) ≤ (M : ℝ) ^ (1 - η) := by
  unfold Q_val;
  -- By definition of $L$, we know that $L p M \leq (1 - η) * (Real.log M / Real.log p)$.
  have hL : L p M ≤ (1 - η) * (Real.log M / Real.log p) := by
    exact Nat.floor_le ( mul_nonneg ( sub_nonneg.2 <| by norm_num [ η ] ) <| div_nonneg ( Real.log_nonneg <| Nat.one_le_cast.2 <| Nat.pos_of_ne_zero hM ) <| Real.log_nonneg <| Nat.one_le_cast.2 hp.pos );
  rw [ Real.le_rpow_iff_log_le ] <;> norm_num <;> try positivity;
  · rwa [ mul_div, le_div_iff₀ ( Real.log_pos <| Nat.one_lt_cast.mpr hp.one_lt ) ] at hL;
  · exact_mod_cast pow_pos hp.pos _
    
/-
X p m M corresponds to X_ZMod on the residue class.
-/
noncomputable def X_ZMod (p M : ℕ) (x : ZMod (Q_val p M)) : ℕ := X_fixed p (L p M) x.val

lemma X_eq_X_ZMod (p M m : ℕ) (hp : p.Prime) :
    X p m M = X_ZMod p M (m : ZMod (Q_val p M)) := by
  unfold X_ZMod;
  convert X_fixed_mod p ( L p M ) m using 1;
  aesop

/-
The number of large digits in Fin p is (p-1)/2.
-/
lemma card_large_digits (p : ℕ) (hp : p.Prime) (hp_ge_3 : p ≥ 3) :
    ((Finset.univ : Finset (Fin p)).filter (fun d => 2 * (d : ℕ) ≥ p + 1)).card = (p - 1) / 2 := by
  rcases Nat.even_or_odd' p with ⟨ c, rfl | rfl ⟩ <;> norm_num at *;
  · simp_all +decide [ Nat.prime_mul_iff ];
  · rw [ Finset.card_eq_of_bijective ];
    use fun i hi => c + 1 + i;
    · simp +zetaDelta at *;
      exact fun a ha => ⟨ a - ( c + 1 ), by omega, by omega ⟩;
    · simp +zetaDelta at *;
      exact fun i hi => ⟨ ⟨ ⟨ c + 1 + i, by linarith ⟩, rfl ⟩, by linarith ⟩;
    · aesop

/-
digits_vec maps x in ZMod(p^L) to its digit vector.
-/
def digits_vec (p L : ℕ) [Fact p.Prime] (x : ZMod (p ^ L)) : Fin L → Fin p :=
  fun i => ⟨(x.val / p ^ (i : ℕ)) % p, Nat.mod_lt _ (Nat.Prime.pos Fact.out)⟩

/-
digits_vec is a bijection.
-/
def digits_vec_equiv (p L : ℕ) [Fact p.Prime] : ZMod (p ^ L) ≃ (Fin L → Fin p) :=
  { toFun := digits_vec p L
    invFun := fun f => (∑ i : Fin L, (f i : ℕ) * p ^ (i : ℕ))
    left_inv := by
      -- By definition of `digits_vec`, we know that `digits_vec p L x` is the list of digits of `x` in base `p`.
      intro x
      simp [digits_vec];
      have h_digits : ∀ (x : ℕ), x < p ^ L → ∑ i ∈ Finset.range L, (x / p ^ i % p : ℕ) * p ^ i = x := by
        induction' L with L ih;
        · aesop;
        · intro x hx; specialize ih ( x / p ) ; simp_all +decide [ Finset.sum_range_succ', pow_succ ] ;
          convert congr_arg ( · * p + x % p ) ( ih ( x / p ) ( Nat.div_lt_of_lt_mul <| by linarith ) ) using 1;
          · simp +decide [ Nat.div_div_eq_div_mul, mul_assoc, mul_comm, Finset.mul_sum _ _ _ ];
          · rw [ Nat.div_add_mod' ];
      have := h_digits x.val ( show x.val < p ^ L from x.val_lt ) ; simp_all +decide [ Finset.sum_range ] ;
      simpa [ ← ZMod.natCast_eq_zero_iff ] using congr_arg ( fun x : ℕ => x : ℕ → ZMod ( p ^ L ) ) this
    right_inv := by
      intro f; ext i; simp +decide
      -- By definition of $digits_vec$, we know that $(digits_vec p L x) i = (x.val / p^i) % p$.
      have h_digits_vec : ∀ x : ZMod (p ^ L), ∀ i : Fin L, (digits_vec p L x) i = (x.val / p ^ (i : ℕ)) % p := by
        exact fun x i => rfl;
      -- By definition of $digits_vec$, we know that $(digits_vec p L x) i = (x.val / p^i) % p$. Therefore, we can simplify the expression.
      have h_simplify : (∑ i : Fin L, (f i : ℕ) * p ^ (i : ℕ)) / p ^ (i : ℕ) % p = (f i : ℕ) := by
        have h_simplify : (∑ i : Fin L, (f i : ℕ) * p ^ (i : ℕ)) / p ^ (i : ℕ) = (∑ j ∈ Finset.univ.filter (fun j => j.val ≥ i.val), (f j : ℕ) * p ^ (j.val - i.val)) := by
          have h_simplify : (∑ i : Fin L, (f i : ℕ) * p ^ (i : ℕ)) = (∑ j ∈ Finset.univ.filter (fun j => j.val < i.val), (f j : ℕ) * p ^ (j : ℕ)) + p ^ (i : ℕ) * (∑ j ∈ Finset.univ.filter (fun j => j.val ≥ i.val), (f j : ℕ) * p ^ (j.val - i.val)) := by
            have h_simplify : (∑ i : Fin L, (f i : ℕ) * p ^ (i : ℕ)) = (∑ j ∈ Finset.univ.filter (fun j => j.val < i.val), (f j : ℕ) * p ^ (j : ℕ)) + (∑ j ∈ Finset.univ.filter (fun j => j.val ≥ i.val), (f j : ℕ) * p ^ (j : ℕ)) := by
              rw [ Finset.sum_filter, Finset.sum_filter ] ; rw [ ← Finset.sum_add_distrib ] ; congr ; ext j ; split_ifs <;> linarith;
            rw [ h_simplify, Finset.mul_sum _ _ _ ];
            exact congrArg₂ ( · + · ) rfl ( Finset.sum_congr rfl fun x hx => by rw [ mul_left_comm, ← pow_add, add_tsub_cancel_of_le ( Finset.mem_filter.mp hx |>.2 ) ] );
          rw [ h_simplify, Nat.add_div ] <;> norm_num [ Nat.Prime.pos Fact.out ];
          rw [ Nat.div_eq_of_lt, if_neg ] <;> norm_num;
          · exact Nat.mod_lt _ ( pow_pos ( Nat.Prime.pos Fact.out ) _ );
          · refine' lt_of_le_of_lt ( Finset.sum_le_sum fun _ _ => Nat.mul_le_mul_right _ <| Nat.le_sub_one_of_lt <| Fin.is_lt _ ) _;
            have h_sum_lt : ∀ (n : ℕ), ∑ i ∈ Finset.range n, (p - 1) * p ^ i < p ^ n := by
              intro n; induction n <;> simp_all +decide [ Finset.sum_range_succ, pow_succ' ] ; nlinarith [ Nat.sub_add_cancel ( show 1 ≤ p from Nat.Prime.pos Fact.out ), pow_pos ( show 0 < p from Nat.Prime.pos Fact.out ) ‹_› ] ;
            convert h_sum_lt i using 1;
            refine' Finset.sum_bij ( fun j hj => j ) _ _ _ _ <;> simp +decide [ Fin.ext_iff ];
            exact fun b hb => ⟨ ⟨ b, by linarith [ Fin.is_lt i ] ⟩, hb, rfl ⟩;
        rw [ h_simplify, Finset.sum_nat_mod ];
        rw [ Finset.sum_eq_single i ] <;> simp +contextual [ Nat.mod_eq_of_lt, Fin.is_lt ];
        exact fun j hij hj => Nat.mod_eq_zero_of_dvd <| dvd_mul_of_dvd_right ( dvd_pow_self _ <| Nat.sub_ne_zero_of_lt <| hij.lt_of_ne' hj ) _;
      convert h_simplify using 1;
      convert h_digits_vec _ _;
      have h_sum_mod : (∑ i : Fin L, (f i : ℕ) * p ^ (i : ℕ)) < p ^ L := by
        have h_sum_lt_pL : ∀ (L : ℕ) (f : Fin L → Fin p), (∑ i : Fin L, (f i : ℕ) * p ^ (i : ℕ)) < p ^ L := by
          intro L f; induction' L with L ih <;> simp_all +decide [ Fin.sum_univ_succ, pow_succ' ] ;
          have := ih ( fun i => f i.succ );
          rw [ show ( ∑ i : Fin L, ( f i.succ : ℕ ) * ( p * p ^ ( i : ℕ ) ) ) = p * ( ∑ i : Fin L, ( f i.succ : ℕ ) * p ^ ( i : ℕ ) ) by rw [ Finset.mul_sum _ _ _ ] ; exact Finset.sum_congr rfl fun _ _ => by ring ] ; nlinarith [ Fin.is_lt ( f 0 ), pow_pos ( Nat.Prime.pos Fact.out : 0 < p ) L ];
        exact h_sum_lt_pL L f;
      norm_cast;
      erw [ ZMod.val_cast_of_lt h_sum_mod ] }

/-
X_ZMod corresponds to X_vec on the digit vector.
-/
def X_vec (p L : ℕ) (f : Fin L → Fin p) : ℕ :=
  (Finset.univ.filter (fun i => 2 * (f i : ℕ) ≥ p + 1)).card

lemma X_ZMod_eq_X_vec (p M : ℕ) [Fact p.Prime] (x : ZMod (Q_val p M)) :
    X_ZMod p M x = X_vec p (L p M) (digits_vec p (L p M) x) := by
  -- By definition of $X_ZMod$ and $X_vec$, we can show that they are equal by considering the digits of $x$ in base $p$.
  have h_digits : X_fixed p (L p M) x.val = X_vec p (L p M) (digits_vec p (L p M) x) := by
    unfold X_fixed X_vec digits_vec; simp +decide
    -- By definition of `Nat.digits`, the digits of `x.val` in base `p` are exactly the remainders when `x.val` is divided by `p`, `p^2`, `p^3`, etc.
    have h_digits : ∀ i : Fin (L p M), (Nat.digits p x.val)[i]! = (x.val / p ^ (i : ℕ)) % p := by
      -- By definition of `Nat.digits`, the i-th digit of `x.val` in base `p` is `(x.val / p^i) % p`.
      have h_digit_def : ∀ n i, (Nat.digits p n)[i]! = (n / p ^ i) % p := by
        intro n i; induction' i with i ih generalizing n <;> simp_all +decide [ Nat.pow_succ', ← Nat.div_div_eq_div_mul ] ;
        · rcases p with ( _ | _ | p ) <;> rcases n with ( _ | _ | n ) <;> simp_all +decide [ Nat.mod_eq_of_lt ];
        · rcases p with ( _ | _ | p ) <;> rcases n with ( _ | _ | n ) <;> simp_all +decide [ Nat.div_div_eq_div_mul ];
      exact fun i => h_digit_def _ _;
    -- By definition of `List.countP`, we can rewrite the left-hand side of the equation.
    have h_countP : List.countP (fun d => p + 1 ≤ 2 * d) (List.take (L p M) (Nat.digits p x.val)) = Finset.sum (Finset.range (L p M)) (fun i => if p + 1 ≤ 2 * ((Nat.digits p x.val)[i]!) then 1 else 0) := by
      have h_countP : ∀ (L : List ℕ) (n : ℕ), List.countP (fun d => p + 1 ≤ 2 * d) (List.take n L) = Finset.sum (Finset.range n) (fun i => if p + 1 ≤ 2 * (L[i]!) then 1 else 0) := by
        intros L n; induction' n with n ih generalizing L <;> simp_all +decide
        rcases L with ( _ | ⟨ a, L ⟩ ) <;> simp_all +decide [ List.take ];
        rw [ Finset.card_filter ];
        rw [ Finset.sum_range_succ' ] ; aesop;
      apply h_countP;
    rw [ h_countP, Finset.card_filter ];
    rw [ Finset.sum_range ] ; aesop;
  exact h_digits
  
set_option maxHeartbeats 0 in
/-
The number of functions with exactly k large digits is given by the binomial formula.
-/
lemma card_X_vec_eq (p L k : ℕ) (hp : p.Prime) (hp_ge_3 : p ≥ 3) :
    ((Finset.univ : Finset (Fin L → Fin p)).filter (fun f => X_vec p L f = k)).card =
    (L.choose k) * ((p - 1) / 2) ^ k * ((p + 1) / 2) ^ (L - k) := by
  by_contra h_contra;
  -- Let S be the set of large digits in Fin p. |S| = (p-1)/2.
  set S := Finset.filter (fun d : Fin p => 2 * (d : ℕ) ≥ p + 1) (Finset.univ : Finset (Fin p))
  have hS_card : S.card = (p - 1) / 2 := by
    convert card_large_digits p hp hp_ge_3 using 1;
    refine' Finset.card_bij ( fun x hx => x ) _ _ _ <;> aesop;
  -- For a fixed subset $A$ of size $k$, the number of functions $f$ such that $f$ maps exactly $k$ indices to $S$ is $|S|^k \cdot |T|^{L-k}$.
  have h_subset : ∀ A : Finset (Fin L), A.card = k → (Finset.filter (fun f : Fin L → Fin p => ∀ i, f i ∈ S ↔ i ∈ A) (Finset.univ : Finset (Fin L → Fin p))).card = ((p - 1) / 2) ^ k * ((p + 1) / 2) ^ (L - k) := by
    intros A hA_card
    have h_subset : (Finset.filter (fun f : Fin L → Fin p => ∀ i, f i ∈ S ↔ i ∈ A) (Finset.univ : Finset (Fin L → Fin p))).card = (∏ i : Fin L, if i ∈ A then S.card else (p - S.card)) := by
      have h_subset : (Finset.filter (fun f : Fin L → Fin p => ∀ i, f i ∈ S ↔ i ∈ A) (Finset.univ : Finset (Fin L → Fin p))).card = (∏ i : Fin L, (Finset.filter (fun d : Fin p => d ∈ S ↔ i ∈ A) (Finset.univ : Finset (Fin p))).card) := by
        have h_subset : (Finset.filter (fun f : Fin L → Fin p => ∀ i, f i ∈ S ↔ i ∈ A) (Finset.univ : Finset (Fin L → Fin p))).card = (Finset.pi Finset.univ fun i : Fin L => Finset.filter (fun d : Fin p => d ∈ S ↔ i ∈ A) (Finset.univ : Finset (Fin p))).card := by
          refine' Finset.card_bij _ _ _ _;
          use fun a ha i _ => a i;
          · aesop;
          · simp +contextual [ funext_iff ];
          · simp +zetaDelta at *;
            exact fun b hb => ⟨ fun i => b i ( Finset.mem_univ i ), hb, rfl ⟩;
        rw [ h_subset, Finset.card_pi ];
      convert h_subset using 2;
      split_ifs <;> simp_all +decide [ Finset.filter_not, Finset.card_sdiff ];
    rw [ h_subset, Finset.prod_ite ];
    simp_all +decide [ Finset.filter_not, Finset.card_sdiff ];
    exact Or.inl ( by rw [ show p - ( p - 1 ) / 2 = ( p + 1 ) / 2 from Nat.sub_eq_of_eq_add <| by linarith [ Nat.div_mul_cancel ( show 2 ∣ p - 1 from even_iff_two_dvd.mp <| hp.even_sub_one <| by linarith ), Nat.div_mul_cancel ( show 2 ∣ p + 1 from even_iff_two_dvd.mp <| by simpa [ parity_simps ] using hp.eq_two_or_odd'.resolve_left <| by linarith ), Nat.sub_add_cancel hp.pos ] ] );
  -- The set of functions $f$ such that $X_vec p L f = k$ is the union over all subsets $A$ of size $k$ of the sets of functions that map exactly $k$ indices to $S$.
  have h_union : Finset.filter (fun f : Fin L → Fin p => X_vec p L f = k) (Finset.univ : Finset (Fin L → Fin p)) = Finset.biUnion (Finset.powersetCard k (Finset.univ : Finset (Fin L))) (fun A => Finset.filter (fun f : Fin L → Fin p => ∀ i, f i ∈ S ↔ i ∈ A) (Finset.univ : Finset (Fin L → Fin p))) := by
    ext f; simp [X_vec];
    constructor <;> intro h;
    · use Finset.filter (fun i => f i ∈ S) Finset.univ; aesop;
    · aesop;
  rw [ h_union, Finset.card_biUnion ] at h_contra;
  · exact h_contra <| by rw [ Finset.sum_congr rfl fun x hx => h_subset x <| Finset.mem_powersetCard.mp hx |>.2 ] ; simp +decide [ mul_comm, mul_left_comm, Finset.card_univ ] ;
  · intros A hA B hB hAB; simp_all +decide [ Finset.disjoint_left ] ;
    exact fun f hf => by obtain ⟨ x, hx ⟩ := Finset.not_subset.mp ( show ¬A ⊆ B from fun h => hAB <| Finset.eq_of_subset_of_card_le h <| by linarith ) ; exact ⟨ x, by aesop ⟩ ;

/-
Q_val is positive.
-/
lemma Q_val_pos (p M : ℕ) (hp : p.Prime) : 0 < Q_val p M := by
  exact pow_pos hp.pos _

/-
Q_val is non-zero.
-/
instance Q_val_neZero (p M : ℕ) [hp : Fact p.Prime] : NeZero (Q_val p M) :=
  ⟨ne_of_gt (Q_val_pos p M hp.out)⟩

set_option maxHeartbeats 0 in
/-
Lemma 6 (Binomial law and Chernoff).
For a prime p >= 3, let U be uniform on {0, ..., Q_p - 1}. Then X_p(U) follows a Binomial distribution with parameters L_p and theta_p = (p-1)/(2p).
We have P(X_p(U) <= 1/2 mu_p) <= exp(-1/8 mu_p).
-/
lemma chernoff_bound_X_fixed (p M : ℕ) [Fact p.Prime] (hp_ge_3 : p ≥ 3) :
    prob_ZMod (Q_val p M) (fun x => (X_ZMod p M x : ℝ) ≤ 1 / 2 * mu p M) ≤ Real.exp (-1 / 8 * mu p M) := by
  unfold prob_ZMod mu; norm_num;
  -- Using the binomial distribution, we can bound the probability.
  have h_binom : (∑ k ∈ Finset.range (Nat.floor ((1 / 2) * (theta p * L p M)) + 1), (Nat.choose (L p M) k) * ((p - 1) / 2) ^ k * ((p + 1) / 2) ^ (L p M - k)) ≤ Real.exp (-1 / 8 * (theta p * L p M)) * (p ^ (L p M)) := by
    -- Applying the Chernoff bound to the binomial distribution.
    have h_chernoff : ∀ (n : ℕ) (p : ℝ), 0 < p ∧ p < 1 → (∑ k ∈ Finset.range (Nat.floor ((1 / 2) * (n * p)) + 1), Nat.choose n k * p ^ k * (1 - p) ^ (n - k)) ≤ Real.exp (-1 / 8 * (n * p)) := by
      intros n p hp
      have h_chernoff : ∀ t : ℝ, 0 < t → (∑ k ∈ Finset.range (Nat.floor ((1 / 2) * (n * p)) + 1), Nat.choose n k * p ^ k * (1 - p) ^ (n - k)) ≤ Real.exp (t * (1 / 2) * (n * p)) * (p * Real.exp (-t) + (1 - p)) ^ n := by
        -- Applying the Chernoff bound to the binomial distribution, we get:
        intros t ht
        have h_chernoff_step : (∑ k ∈ Finset.range (Nat.floor ((1 / 2) * (n * p)) + 1), Nat.choose n k * p ^ k * (1 - p) ^ (n - k)) ≤ Real.exp (t * (1 / 2) * (n * p)) * (∑ k ∈ Finset.range (n + 1), Nat.choose n k * p ^ k * (1 - p) ^ (n - k) * Real.exp (-t * k)) := by
          have h_chernoff_step : (∑ k ∈ Finset.range (Nat.floor ((1 / 2) * (n * p)) + 1), Nat.choose n k * p ^ k * (1 - p) ^ (n - k)) ≤ ∑ k ∈ Finset.range (n + 1), Nat.choose n k * p ^ k * (1 - p) ^ (n - k) * Real.exp (t * ((1 / 2) * (n * p) - k)) := by
            have h_chernoff_step : ∀ k ∈ Finset.range (Nat.floor ((1 / 2) * (n * p)) + 1), Nat.choose n k * p ^ k * (1 - p) ^ (n - k) ≤ Nat.choose n k * p ^ k * (1 - p) ^ (n - k) * Real.exp (t * ((1 / 2) * (n * p) - k)) := by
              exact fun k hk => le_mul_of_one_le_right ( mul_nonneg ( mul_nonneg ( Nat.cast_nonneg _ ) ( pow_nonneg hp.1.le _ ) ) ( pow_nonneg ( sub_nonneg.2 hp.2.le ) _ ) ) ( Real.one_le_exp ( mul_nonneg ht.le ( sub_nonneg.2 ( by nlinarith [ Nat.floor_le ( show 0 ≤ 1 / 2 * ( ( n : ℝ ) * p ) by nlinarith ), show ( k : ℝ ) ≤ ⌊1 / 2 * ( ( n : ℝ ) * p ) ⌋₊ by exact_mod_cast Finset.mem_range_succ_iff.mp hk ] ) ) ) );
            refine' le_trans ( Finset.sum_le_sum h_chernoff_step ) _;
            exact Finset.sum_le_sum_of_subset_of_nonneg ( Finset.range_mono ( Nat.succ_le_succ ( Nat.floor_le_of_le ( by nlinarith ) ) ) ) fun _ _ _ => mul_nonneg ( mul_nonneg ( mul_nonneg ( Nat.cast_nonneg _ ) ( pow_nonneg hp.1.le _ ) ) ( pow_nonneg ( sub_nonneg.2 hp.2.le ) _ ) ) ( Real.exp_nonneg _ );
          convert h_chernoff_step using 1;
          rw [ Finset.mul_sum _ _ _ ] ; exact Finset.sum_congr rfl fun _ _ => by rw [ mul_left_comm ] ; rw [ ← Real.exp_add ] ; ring_nf;
        convert h_chernoff_step using 2;
        rw [ add_pow ];
        exact Finset.sum_congr rfl fun _ _ => by rw [ mul_pow, ← Real.exp_nat_mul ] ; ring_nf;
      refine le_trans ( h_chernoff ( Real.log 2 ) ( Real.log_pos one_lt_two ) ) ?_;
      norm_num [ Real.exp_neg, Real.exp_log ];
      rw [ ← Real.log_le_log_iff ( by exact mul_pos ( Real.exp_pos _ ) ( pow_pos ( by linarith ) _ ) ) ( by positivity ), Real.log_mul ( by positivity ) ( by exact ne_of_gt ( pow_pos ( by linarith ) _ ) ), Real.log_pow, Real.log_exp ] ; ring_nf ; norm_num;
      have := Real.log_le_sub_one_of_pos ( show 0 < 1 + - ( p * ( 1 / 2 ) ) by linarith );
      have := Real.log_two_lt_d9 ; norm_num at * ; nlinarith [ show ( n : ℝ ) * p ≥ 0 by exact mul_nonneg ( Nat.cast_nonneg _ ) hp.1.le ];
    -- Applying the Chernoff bound with $n = L p M$ and $p = \frac{p-1}{2p}$.
    have h_apply_chernoff : (∑ k ∈ Finset.range (Nat.floor ((1 / 2) * (L p M * ((p - 1) / (2 * p) : ℝ))) + 1), Nat.choose (L p M) k * ((p - 1) / (2 * p) : ℝ) ^ k * (1 - (p - 1) / (2 * p) : ℝ) ^ (L p M - k)) ≤ Real.exp (-1 / 8 * (L p M * ((p - 1) / (2 * p) : ℝ))) := by
      exact h_chernoff _ _ ⟨ div_pos ( by norm_num; linarith ) ( by positivity ), by rw [ div_lt_iff₀ ] <;> linarith [ show ( p : ℝ ) ≥ 3 by norm_cast ] ⟩;
    convert mul_le_mul_of_nonneg_right h_apply_chernoff ( pow_nonneg ( Nat.cast_nonneg p : ( 0 : ℝ ) ≤ p ) ( L p M ) ) using 1 <;> norm_num [ theta ] ; ring_nf;
    · rw [ Finset.mul_sum _ _ _ ] ; refine' Finset.sum_congr rfl fun x hx => _ ; rw [ Nat.cast_div ( show 2 ∣ p - 1 from even_iff_two_dvd.mp ( Nat.Prime.even_sub_one Fact.out ( by linarith ) ) ) ( by norm_num ) ] ; rw [ Nat.cast_div ( show 2 ∣ 1 + p from even_iff_two_dvd.mp ( by simpa [ parity_simps ] using Nat.Prime.odd_of_ne_two Fact.out ( by linarith ) ) ) ( by norm_num ) ] ; norm_num ; ring_nf;
      rw [ Nat.cast_sub ( by linarith ) ] ; ring_nf;
      field_simp;
      rw [ show ( -1 + p : ℝ ) = ( p + -1 ) by ring, show ( 1 + p : ℝ ) = ( p + 1 ) by ring ] ; norm_num [ mul_pow, mul_assoc, mul_comm, mul_left_comm, div_eq_mul_inv ] ;
      -- Combine and simplify the exponents of $p$.
      field_simp
      ring_nf;
      simp +zetaDelta at *;
      exact Or.inl ( by rw [ mul_assoc, ← pow_add, Nat.add_sub_of_le ( by linarith [ show x ≤ L p M from by linarith [ Nat.floor_le_of_le ( show ( L p M : ℝ ) * 4⁻¹ + ( p : ℝ ) ⁻¹ * ( L p M : ℝ ) * ( -1 / 4 ) ≤ L p M by nlinarith [ show ( p : ℝ ) ≥ 3 by norm_cast, inv_mul_cancel₀ ( by positivity : ( p : ℝ ) ≠ 0 ) ] ) ] ] ) ] );
    · exact Or.inl <| mul_comm _ _;
  -- Using the bijection between `digits_vec` and `Fin L → Fin p`, we can rewrite the cardinality in terms of the binomial distribution.
  have h_card_eq : (Finset.filter (fun x : ZMod (p ^ L p M) => (X_ZMod p M x : ℝ) ≤ 1 / 2 * (theta p * L p M)) Finset.univ).card = ∑ k ∈ Finset.range (Nat.floor ((1 / 2) * (theta p * L p M)) + 1), (Nat.choose (L p M) k) * ((p - 1) / 2) ^ k * ((p + 1) / 2) ^ (L p M - k) := by
    have h_card_eq : (Finset.filter (fun x : ZMod (p ^ L p M) => (X_ZMod p M x : ℝ) ≤ 1 / 2 * (theta p * L p M)) Finset.univ).card = (Finset.filter (fun f : Fin (L p M) → Fin p => (X_vec p (L p M) f : ℝ) ≤ 1 / 2 * (theta p * L p M)) Finset.univ).card := by
      rw [ Finset.card_filter, Finset.card_filter ];
      conv_rhs => rw [ ← Equiv.sum_comp ( digits_vec_equiv p ( L p M ) ) ] ;
      exact Finset.sum_congr rfl fun x hx => by rw [ X_ZMod_eq_X_vec ] ; rfl;
    rw [ h_card_eq ];
    have h_card_eq : (Finset.filter (fun f : Fin (L p M) → Fin p => (X_vec p (L p M) f : ℝ) ≤ 1 / 2 * (theta p * L p M)) Finset.univ).card = ∑ k ∈ Finset.range (Nat.floor ((1 / 2) * (theta p * L p M)) + 1), (Finset.filter (fun f : Fin (L p M) → Fin p => X_vec p (L p M) f = k) Finset.univ).card := by
      have h_card_eq : (Finset.filter (fun f : Fin (L p M) → Fin p => (X_vec p (L p M) f : ℝ) ≤ 1 / 2 * (theta p * L p M)) Finset.univ).card = ∑ k ∈ Finset.range (Nat.floor ((1 / 2) * (theta p * L p M)) + 1), (Finset.filter (fun f : Fin (L p M) → Fin p => X_vec p (L p M) f = k) Finset.univ).card := by
        have h_card_eq : Finset.filter (fun f : Fin (L p M) → Fin p => (X_vec p (L p M) f : ℝ) ≤ 1 / 2 * (theta p * L p M)) Finset.univ = Finset.biUnion (Finset.range (Nat.floor ((1 / 2) * (theta p * L p M)) + 1)) (fun k => Finset.filter (fun f : Fin (L p M) → Fin p => X_vec p (L p M) f = k) Finset.univ) := by
          field_simp;
          ext f; simp [X_vec];
          rw [ Nat.lt_succ_iff, Nat.le_floor_iff ( by exact div_nonneg ( mul_nonneg ( div_nonneg ( sub_nonneg.mpr <| Nat.one_le_cast.mpr <| Nat.Prime.pos Fact.out ) <| by positivity ) <| Nat.cast_nonneg _ ) zero_le_two ), le_div_iff₀ ] ; norm_cast
        rw [ h_card_eq, Finset.card_biUnion ];
        exact fun i hi j hj hij => Finset.disjoint_left.mpr fun x => by aesop;
      convert h_card_eq using 1;
    rw [ h_card_eq ];
    refine' Finset.sum_congr rfl fun k hk => _;
    convert card_X_vec_eq p ( L p M ) k ( Fact.out : Nat.Prime p ) hp_ge_3 using 1;
  rw [ div_le_iff₀ ] <;> norm_num at *;
  · convert h_binom using 1;
    · exact_mod_cast h_card_eq;
    · unfold Q_val; norm_num;
  · exact pow_pos ( Nat.Prime.pos Fact.out ) _

/-
Lemma 6 (Binomial law and Chernoff) - Part 2.
For m uniform on [M, 2M], P(X_p(m) <= 1/2 mu_p) <= exp(-1/8 mu_p) + 2/M^eta.
-/
lemma chernoff_bound_X (p M : ℕ) (hp : p.Prime) (hp_ge_3 : p ≥ 3) (hM : M ≠ 0)
    (h_bound : (Q_val p M : ℝ) ≤ (M : ℝ) ^ (1 - η)) :
    prob_event M (fun m => (X p m M : ℝ) ≤ 1 / 2 * mu p M) ≤ Real.exp (-1 / 8 * mu p M) + 2 / (M : ℝ) ^ η := by
      convert le_trans ( prob_event_le_prob_ZMod' M ( Q_val p M ) _ _ _ ) ( add_le_add_right ( chernoff_bound_X_fixed p M hp_ge_3 ) _ ) using 1;
      · congr! 2;
        rw [ X_eq_X_ZMod p M _ hp ];
      · assumption;
      · convert h_bound using 1;
      · exact ⟨ hp ⟩

/-
c1 = (1 - eta) / 48.
-/
noncomputable def c1 : ℝ := (1 - η) / 48

/-
Lemma 5 (Forced carries from large digits).
If d_u >= (p+1)/2, then there is a carry from digit u to u+1.
Consequently, kappa_p(m) >= X_p(m).
-/
lemma forced_carries_smallp (p m M : ℕ) [Fact p.Prime] (hp_ge_3 : p ≥ 3) :
    κ p m ≥ X p m M := by
      -- By Kummer's theorem, κ_p(m) is equal to the number of carries when adding m and m in base p.
      have h_kummer : κ p m = Finset.card (Finset.filter (fun i => 2 * (m % p ^ i) ≥ p ^ i) (Finset.Ico 1 (Nat.log p (2 * m) + 1))) := by
        unfold κ;
        rw [ padicValNat_choose ];
        any_goals exact Nat.lt_succ_self _;
        · norm_num [ two_mul, Nat.add_mod ];
        · linarith;
      -- We'll use that $X_p(m)$ counts the number of indices $u$ such that $2 * d_u \geq p + 1$, which corresponds to $2 * (m % p^u) \geq p^u$.
      have h_X_count : X p m M ≤ Finset.card (Finset.filter (fun u => 2 * (m % p ^ (u + 1)) ≥ p ^ (u + 1)) (Finset.Ico 0 (L p M))) := by
        have h_X_count : ∀ u < L p M, 2 * ((Nat.digits p m)[u]!) ≥ p + 1 → 2 * (m % p ^ (u + 1)) ≥ p ^ (u + 1) := by
          intro u hu h
          have h_mod : m % p ^ (u + 1) = ∑ i ∈ Finset.range (u + 1), ((Nat.digits p m)[i]!) * p ^ i := by
            have h_mod : m % p ^ (u + 1) = Nat.ofDigits p ((Nat.digits p m).take (u + 1)) := by
              conv_lhs => rw [ ← Nat.ofDigits_digits p m ];
              rw [ ← List.take_append_drop ( u + 1 ) ( Nat.digits p m ), Nat.ofDigits_append ];
              cases min_cases ( u + 1 ) ( List.length ( Nat.digits p m ) ) <;> simp_all +decide
              · rw [ Nat.mod_eq_of_lt ];
                refine' Nat.ofDigits_lt_base_pow_length _ _ |> lt_of_lt_of_le <| Nat.pow_le_pow_right ( by linarith ) <| by simp +decide [ * ] ;
                · grind;
                · exact fun x hx => Nat.digits_lt_base ( by linarith ) ( List.mem_of_mem_take hx );
              · grind;
            rw [ h_mod ];
            induction' u + 1 with u ih <;> simp_all +decide [ Finset.sum_range_succ ];
            rw [ List.take_succ ];
            cases h : ( Nat.digits p m)[u]? <;> simp_all +decide [ Nat.ofDigits_append, Nat.ofDigits_singleton ];
            grind +ring;
          -- Since $2 * ((Nat.digits p m).get! u) ≥ p + 1$, we have $2 * (m % p ^ (u + 1)) ≥ 2 * ((Nat.digits p m).get! u) * p ^ u$.
          have h_mod_ge : 2 * (m % p ^ (u + 1)) ≥ 2 * ((Nat.digits p m)[u]!) * p ^ u := by
            simp_all +decide [ mul_assoc, Finset.sum_range_succ ];
          exact le_trans ( by ring_nf; nlinarith [ pow_pos ( zero_lt_three.trans_le hp_ge_3 ) u ] ) h_mod_ge;
        have h_X_count : X p m M ≤ Finset.card (Finset.filter (fun u => 2 * ((Nat.digits p m)[u]!) ≥ p + 1) (Finset.Ico 0 (L p M))) := by
          have h_X_count : ∀ {l : List ℕ}, X p m M = List.countP (fun d => 2 * d ≥ p + 1) (List.take (L p M) (Nat.digits p m)) := by
            aesop;
          rw [ h_X_count ];
          · induction' L p M with L ih <;> simp_all +decide [ List.take_succ ];
            by_cases h : p + 1 ≤ 2 * (Nat.digits p m)[L]?.getD 0 <;> simp_all +decide [ Finset.filter ];
            · grind;
            · cases h' : ( Nat.digits p m)[L]? <;> aesop;
          · exact [ ];
        exact h_X_count.trans ( Finset.card_mono <| fun x hx => by aesop );
      -- Since the set of indices $u$ such that $2 * (m % p^u) \geq p^u$ includes all $u$ such that $2 * (m % p^{u+1}) \geq p^{u+1}$, we have:
      have h_superset : Finset.filter (fun i => 2 * (m % p ^ i) ≥ p ^ i) (Finset.Ico 1 (Nat.log p (2 * m) + 1)) ⊇ Finset.image (fun u => u + 1) (Finset.filter (fun u => 2 * (m % p ^ (u + 1)) ≥ p ^ (u + 1)) (Finset.Ico 0 (L p M))) := by
        simp +decide [ Finset.subset_iff ];
        rintro _ i hi₁ hi₂ rfl; refine' ⟨ ⟨ Nat.succ_pos _, _ ⟩, hi₂ ⟩ ;
        refine' Nat.succ_lt_succ ( Nat.le_log_of_pow_le ( by linarith ) _ );
        exact le_trans hi₂ ( Nat.mul_le_mul_left _ ( Nat.mod_le _ _ ) );
      exact h_kummer.symm ▸ le_trans h_X_count ( Finset.card_le_card h_superset |> le_trans ( by rw [ Finset.card_image_of_injective ] ; aesop_cat ) )

/-
Lemma 7 (Uniform carry threshold).
For every prime p <= 2k with p >= 3, and all sufficiently large M,
P(kappa_p(m) <= gamma log_p M) <= exp(-c1 log M / log p) + 2/M^eta.
-/
theorem uniform_carry_threshold (r : ℕ) :
    ∃ M0, ∀ M ≥ M0, ∀ p, p.Prime → 3 ≤ p → p ≤ 2 * k_param r M →
    prob_event M (fun m => (κ p m : ℝ) ≤ γ * (Real.log M / Real.log p)) ≤
    Real.exp (-c1 * (Real.log M / Real.log p)) + 2 / (M : ℝ) ^ η := by
      -- Choose M0 such that for all M ≥ M0, we have log_p M ≥ 48 / (1 - η).
      obtain ⟨M0, hM0⟩ : ∃ M0 : ℕ, ∀ M ≥ M0, ∀ p : ℕ, Nat.Prime p → 3 ≤ p → p ≤ 2 * k_param r M → (Real.log M / Real.log p) ≥ 48 / (1 - η) := by
        -- Since $p \leq 2k \leq 2c \log M$, we have $\log p \leq \log(2c) + \log \log M$.
        have h_log_p_bound : ∀ M : ℕ, M ≥ 2 → ∀ p : ℕ, Nat.Prime p → 3 ≤ p → p ≤ 2 * k_param r M → Real.log p ≤ Real.log (2 * (c r)) + Real.log (Real.log M) := by
          intros M hM p hp hp_ge_3 hp_le_2k
          have h_log_p_bound : p ≤ 2 * c r * Real.log M := by
            have h_log_p_bound : p ≤ 2 * Nat.floor (c r * Real.log M) := by
              exact hp_le_2k;
            rw [ mul_assoc ] ; exact le_trans ( Nat.cast_le.mpr h_log_p_bound ) ( by simpa using mul_le_mul_of_nonneg_left ( Nat.floor_le ( show 0 ≤ c r * Real.log M by exact mul_nonneg ( show 0 ≤ c r by exact div_nonneg ( mul_nonneg ( by norm_num [ γ ] ) ( sub_nonneg.mpr <| Nat.one_le_cast.mpr <| Nat.Prime.pos <| by { exact Nat.prime_nth_prime _ } ) ) <| Real.log_nonneg <| Nat.one_le_cast.mpr <| Nat.Prime.pos <| by { exact Nat.prime_nth_prime _ } ) <| Real.log_nonneg <| Nat.one_le_cast.mpr <| by linarith ) ) zero_le_two ) ;
          rw [ ← Real.log_mul ];
          · exact Real.log_le_log ( Nat.cast_pos.mpr hp.pos ) h_log_p_bound;
          · aesop;
          · exact ne_of_gt <| Real.log_pos <| Nat.one_lt_cast.mpr hM;
        -- Choose $M_0$ such that for all $M \geq M_0$, $\frac{\log M}{\log(2c) + \log \log M} \geq \frac{48}{1 - \eta}$.
        obtain ⟨M0, hM0⟩ : ∃ M0 : ℕ, ∀ M ≥ M0, Real.log M / (Real.log (2 * (c r)) + Real.log (Real.log M)) ≥ 48 / (1 - η) := by
          have h_log_ratio_bound : Filter.Tendsto (fun M : ℕ => Real.log M / (Real.log (2 * (c r)) + Real.log (Real.log M))) Filter.atTop Filter.atTop := by
            -- We can use the fact that $\frac{\log M}{\log \log M}$ tends to infinity as $M$ tends to infinity.
            have h_log_log : Filter.Tendsto (fun M : ℕ => Real.log M / Real.log (Real.log M)) Filter.atTop Filter.atTop := by
              -- We can use the change of variables $u = \log M$ to transform the limit expression.
              suffices h_log_log_u : Filter.Tendsto (fun u : ℝ => u / Real.log u) Filter.atTop Filter.atTop by
                exact h_log_log_u.comp ( Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop );
              -- We can use the change of variables $v = \log u$ to transform the limit expression.
              suffices h_log_ratio_transformed : Filter.Tendsto (fun v : ℝ => Real.exp v / v) Filter.atTop Filter.atTop by
                have := h_log_ratio_transformed.comp Real.tendsto_log_atTop;
                exact this.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with x hx using by rw [ Function.comp_apply, Real.exp_log hx ] );
              simpa using Real.tendsto_exp_div_pow_atTop 1;
            have h_log_log : Filter.Tendsto (fun M : ℕ => (Real.log M / Real.log (Real.log M)) / (1 + Real.log (2 * (c r)) / Real.log (Real.log M))) Filter.atTop Filter.atTop := by
              have h_log_log : Filter.Tendsto (fun M : ℕ => 1 + Real.log (2 * (c r)) / Real.log (Real.log M)) Filter.atTop (nhds 1) := by
                exact le_trans ( tendsto_const_nhds.add <| tendsto_const_nhds.div_atTop <| Real.tendsto_log_atTop.comp <| Real.tendsto_log_atTop.comp <| tendsto_natCast_atTop_atTop ) <| by norm_num;
              apply_rules [ Filter.Tendsto.atTop_mul_pos, h_log_log.inv₀ ] ; norm_num;
              norm_num;
            refine h_log_log.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 2 ] with M hM using by rw [ div_div, mul_add, mul_div_cancel₀ _ ( ne_of_gt <| Real.log_pos <| show 1 < Real.log M from by rw [ Real.lt_log_iff_exp_lt <| by positivity ] ; exact Real.exp_one_lt_d9.trans_le <| by norm_num; linarith [ show ( M : ℝ ) ≥ 3 by norm_cast ] ) ] ; ring );
          exact Filter.eventually_atTop.mp ( h_log_ratio_bound.eventually_ge_atTop _ );
        refine' ⟨ Max.max M0 2, fun M hM p hp hp' hp'' => le_trans ( hM0 M ( le_trans ( le_max_left _ _ ) hM ) ) _ ⟩;
        gcongr;
        · exact Real.log_pos ( by norm_cast; linarith );
        · exact h_log_p_bound M ( le_trans ( le_max_right _ _ ) hM ) p hp hp' hp'';
      use M0 + 1;
      intro M hM p hp hp3 hp2k
      have h_gamma_log_p : γ * (Real.log M / Real.log p) ≤ (1 / 2) * mu p M := by
        unfold mu;
        -- Since $L_p = \lfloor (1 - \eta) \log_p M \rfloor$, we have $L_p \geq (1 - \eta) \log_p M - 1$.
        have hL_p : (L p M : ℝ) ≥ (1 - η) * (Real.log M / Real.log p) - 1 := by
          exact le_of_lt ( Nat.sub_one_lt_floor _ );
        unfold theta;
        unfold γ η at *;
        nlinarith [ show ( p : ℝ ) ≥ 3 by norm_cast, show ( p : ℝ ) ≥ 3 by norm_cast, mul_div_cancel₀ ( ( p : ℝ ) - 1 ) ( by positivity : ( 2 * p : ℝ ) ≠ 0 ), hM0 M ( by linarith ) p hp hp3 hp2k, mul_div_cancel₀ ( 48 : ℝ ) ( by linarith : ( 1 - 1 / 10 : ℝ ) ≠ 0 ) ];
      have h_exp_bound : Real.exp (-1 / 8 * mu p M) ≤ Real.exp (-c1 * (Real.log M / Real.log p)) := by
        have h_mu_bound : mu p M ≥ (1 - η) / 3 * (Real.log M / Real.log p) - 1 / 3 := by
          have h_mu_bound : mu p M ≥ (1 - η) / 3 * (Real.log M / Real.log p) - 1 / 3 := by
            have h_theta_bound : theta p ≥ 1 / 3 := by
              exact le_div_iff₀ ( by positivity ) |>.2 ( by linarith [ show ( p : ℝ ) ≥ 3 by norm_cast ] )
            have h_L_bound : (L p M : ℝ) ≥ (1 - η) * (Real.log M / Real.log p) - 1 := by
              exact le_of_lt ( Nat.sub_one_lt_floor _ )
            unfold mu; nlinarith;
          exact h_mu_bound;
        norm_num [ c1, η ] at *;
        linarith [ hM0 M ( by linarith ) p hp hp3 hp2k ];
      have h_prob_bound : prob_event M (fun m => (κ p m : ℝ) ≤ γ * (Real.log M / Real.log p)) ≤ prob_event M (fun m => (X p m M : ℝ) ≤ 1 / 2 * mu p M) := by
        have h_prob_bound : ∀ m : ℕ, (κ p m : ℝ) ≤ γ * (Real.log M / Real.log p) → (X p m M : ℝ) ≤ 1 / 2 * mu p M := by
          intros m hm
          have h_kappa_ge_X : (κ p m : ℝ) ≥ (X p m M : ℝ) := by
            have h_kappa_ge_X : ∀ m : ℕ, (κ p m : ℝ) ≥ (X p m M : ℝ) := by
              intro m
              have h_kappa_ge_X : κ p m ≥ X p m M := by
                convert forced_carries_smallp p m M ( by exact hp3 ) using 1;
                exact ⟨ hp ⟩
              exact_mod_cast h_kappa_ge_X;
            exact h_kappa_ge_X m;
          grind;
        apply_rules [ div_le_div_of_nonneg_right ];
        · exact_mod_cast Finset.card_mono fun x hx => by aesop;
        · positivity;
      refine le_trans h_prob_bound <| le_trans ( chernoff_bound_X p M hp hp3 ( by linarith ) ?_ ) ?_;
      · convert Q_le_bound p M hp ( by linarith ) using 1;
      · exact add_le_add_right h_exp_bound _

/-
Lemma 8 (Max-valuation tail bound).
Let p be prime and t >= 1 with p^t <= M^(1-eta).
Then P(V_p(m) >= t) <= k/p^t + 2/M^eta.
-/
lemma V_p_tail (p t M k : ℕ) (hp : p.Prime) (ht : t ≥ 1) (hM : M ≠ 0)
    (h_bound : (p ^ t : ℝ) ≤ (M : ℝ) ^ (1 - η)) :
    prob_event M (fun m => V p m k ≥ t) ≤ (k : ℝ) / (p ^ t : ℝ) + 2 / (M : ℝ) ^ η := by
      -- The event V_p(m) >= t means there exists i in {1, ..., k} such that p^t divides m+i.
      have h_event : ∀ m, V p m k ≥ t ↔ ∃ i ∈ Finset.range k, (m + 1 + i) % p^t = 0 := by
        intro m; rw [ ge_iff_le ] ; simp +decide
        constructor;
        · intro h;
          -- By definition of $V$, if $t \leq V p m k$, then there exists some $i \in \{0, 1, ..., k-1\}$ such that $p^t \mid (m + 1 + i)$.
          obtain ⟨i, hi⟩ : ∃ i ∈ Finset.range k, p^t ∣ (m + 1 + i) := by
            contrapose! h;
            refine' lt_of_le_of_lt ( Finset.sup_le _ ) _;
            exact t - 1;
            · intro i hi; specialize h i hi; rw [ padicValNat ] ; aesop;
            · exact Nat.pred_lt ( ne_bot_of_gt ht );
          exact ⟨ i, Finset.mem_range.mp hi.1, Nat.mod_eq_zero_of_dvd hi.2 ⟩;
        · simp +zetaDelta at *;
          intro x hx hx'; have := Nat.dvd_of_mod_eq_zero hx'; obtain ⟨ c, hc ⟩ := this; simp_all +decide
          refine' le_trans _ ( Finset.le_sup <| Finset.mem_range.mpr hx );
          haveI := Fact.mk hp; rw [ hc, padicValNat.mul ] <;> aesop;
      -- Let Q = p^t. The set of bad residues is A = {-1, ..., -k} mod Q.
      set Q := p^t
      set A : Finset (ZMod Q) := Finset.image (fun i : ℕ => -(i + 1 : ZMod Q)) (Finset.range k);
      -- The probability that $m \mod Q \in A$ is at most $|A| / Q$.
      have h_prob_A : (prob_event M (fun m => (m : ZMod Q) ∈ A)) ≤ (A.card : ℝ) / Q + 2 / (M : ℝ) ^ η := by
        have h_prob_A : (prob_event M (fun m => (m : ZMod Q) ∈ A)) ≤ (A.card : ℝ) / Q + 2 / (M : ℝ) ^ η := by
          have hQ_pos : 0 < Q := by
            exact pow_pos hp.pos _
          have hQ_ne_zero : NeZero Q := by
            exact ⟨ hQ_pos.ne' ⟩
          convert prob_event_le_prob_ZMod M Q ( fun m => m ∈ A ) ( by aesop ) ( by aesop ) using 1;
          unfold prob_ZMod; ring_nf;
          simp +decide [ mul_comm ];
        convert h_prob_A using 1;
      refine le_trans ?_ ( h_prob_A.trans ?_ );
      · simp_all +decide [ ← ZMod.val_natCast ];
        refine' div_le_div_of_nonneg_right _ ( by positivity );
        simp +zetaDelta at *;
        exact Finset.card_mono fun x hx => by obtain ⟨ i, hi, hi' ⟩ := Finset.mem_filter.mp hx |>.2; exact Finset.mem_filter.mpr ⟨ Finset.mem_Icc.mpr ⟨ by linarith [ Finset.mem_Icc.mp ( Finset.mem_filter.mp hx |>.1 ) ], by linarith [ Finset.mem_Icc.mp ( Finset.mem_filter.mp hx |>.1 ) ] ⟩, i, hi, by linear_combination' -hi' ⟩ ;
      · gcongr;
        · exact_mod_cast pow_pos hp.pos _;
        · exact Finset.card_image_le.trans ( by simp );
        · norm_cast

/-
Lemma 9 (Monotonicity).
The function f(x) = (x-1)/log x is increasing for x >= 3.
Consequently, if 3 <= q <= p, then (q-1)/log q <= (p-1)/log p.
-/
lemma monotone_f (x y : ℝ) (hx : 3 ≤ x) (hxy : x ≤ y) :
    (x - 1) / Real.log x ≤ (y - 1) / Real.log y := by
  -- We'll use the fact that $f(x)$ is increasing to show this inequality.
  have h_deriv_pos : ∀ x ≥ 3, 0 < deriv (fun x => (x - 1) / Real.log x) x := by
    intro x hx;
    norm_num [ show x ≠ 0 by linarith, show Real.log x ≠ 0 by exact ne_of_gt <| Real.log_pos <| by linarith ];
    exact div_pos ( sub_pos_of_lt ( by nlinarith [ inv_mul_cancel₀ ( by linarith : x ≠ 0 ), Real.log_inv x ▸ Real.log_lt_sub_one_of_pos ( inv_pos.mpr ( by linarith : 0 < x ) ) ( by nlinarith [ inv_mul_cancel₀ ( by linarith : x ≠ 0 ) ] ) ] ) ) ( sq_pos_of_pos ( Real.log_pos ( by linarith ) ) );
  by_contra h_contra;
  -- Apply the Mean Value Theorem to the interval [x, y].
  obtain ⟨c, hc⟩ : ∃ c ∈ Set.Ioo x y, deriv (fun x => (x - 1) / Real.log x) c = ((y - 1) / Real.log y - (x - 1) / Real.log x) / (y - x) := by
    apply_rules [ exists_deriv_eq_slope ];
    · exact hxy.lt_of_ne ( by rintro rfl; linarith );
    · exact continuousOn_of_forall_continuousAt fun x hx => ContinuousAt.div ( continuousAt_id.sub continuousAt_const ) ( Real.continuousAt_log ( by linarith [ hx.1 ] ) ) ( ne_of_gt ( Real.log_pos ( by linarith [ hx.1 ] ) ) );
    · exact fun u hu => DifferentiableAt.differentiableWithinAt ( by exact differentiableAt_of_deriv_ne_zero ( ne_of_gt ( h_deriv_pos u ( by linarith [ hu.1 ] ) ) ) );
  rw [ eq_div_iff ] at hc <;> nlinarith [ hc.1.1, hc.1.2, h_deriv_pos c ( by linarith [ hc.1.1, hc.1.2 ] ) ]
  
/-
Lemma 10.
For p >= q, k/(p-1) <= (gamma/8) * log_p M.
-/
lemma k_div_p_minus_one_le (r M p : ℕ) (hr : r ≥ 1) (hp : p.Prime) (hp_ge_q : p ≥ q r) (hM : M > 1) :
    (k_param r M : ℝ) / (p - 1) ≤ (γ / 8) * (Real.log M / Real.log p) := by
      -- Substitute the definition of $c$ into the inequality.
      have h_subst_c : (k_param r M : ℝ) ≤ (γ / 8) * ((q r : ℝ) - 1) / Real.log (q r) * Real.log M := by
        exact Nat.floor_le ( mul_nonneg ( div_nonneg ( mul_nonneg ( by norm_num [ γ ] ) ( sub_nonneg.mpr ( Nat.one_le_cast.mpr ( Nat.Prime.pos ( Nat.prime_nth_prime _ ) ) ) ) ) ( Real.log_nonneg ( Nat.one_le_cast.mpr ( Nat.Prime.pos ( Nat.prime_nth_prime _ ) ) ) ) ) ( Real.log_nonneg ( Nat.one_le_cast.mpr hM.le ) ) );
      -- Substitute the definition of $q$ into the inequality.
      have h_subst_q : ((q r : ℝ) - 1) / Real.log (q r) ≤ ((p : ℝ) - 1) / Real.log p := by
        apply_rules [ monotone_f ];
        · norm_cast;
          exact Nat.succ_le_of_lt ( Nat.lt_of_le_of_lt ( Nat.Prime.two_le ( Nat.prime_nth_prime 0 ) ) ( Nat.nth_strictMono ( Nat.infinite_setOf_prime ) ( Nat.sub_pos_of_lt ( by linarith ) ) ) );
        · exact_mod_cast hp_ge_q;
      rw [ div_le_iff₀ ];
      · convert h_subst_c.trans _ using 1;
        convert mul_le_mul_of_nonneg_right ( mul_le_mul_of_nonneg_left h_subst_q <| show 0 ≤ γ / 8 by exact div_nonneg ( by norm_num [ γ ] ) <| by norm_num ) <| Real.log_nonneg <| Nat.one_le_cast.mpr <| pos_of_gt hM using 1 ; ring;
        ring;
      · exact sub_pos_of_lt ( Nat.one_lt_cast.mpr hp.one_lt )

/-
Pi is the set of primes p such that p_r < p <= 2k.
G_event is the event that kappa_p(m) >= gamma * log_p M.
H_event is the event that V_p(m) < t_p.
-/
noncomputable def Pi (r M : ℕ) : Finset ℕ := (Finset.range (2 * k_param r M + 1)).filter (fun pp => pp.Prime ∧ pp > p r)

def G_event (p M m : ℕ) : Prop := (κ p m : ℝ) ≥ γ * (Real.log M / Real.log p)

def H_event (r p M m : ℕ) : Prop := V p m (k_param r M) < t p M

/-
Lemma 12.
For sufficiently large M, and all p in Pi, p^t <= M^(1-eta).
-/
lemma V_p_condition_holds (r : ℕ) :
    ∃ M0, ∀ M ≥ M0, ∀ pp ∈ Pi r M, (pp ^ t pp M : ℝ) ≤ (M : ℝ) ^ (1 - η) := by
  -- Since $p \leq 2k$ and $k \approx \frac{\gamma}{8} \frac{q-1}{\log q} \log M$, we have $p \leq M^{1/2}$.
  have h_p_le_sqrt_M : ∃ M0, ∀ M ≥ M0, ∀ pp ∈ Pi r M, (pp : ℝ) ≤ (M : ℝ) ^ (1 / 2 : ℝ) := by
    -- Since $p \leq 2k$ and $k \approx \frac{\gamma}{8} \frac{q-1}{\log q} \log M$, we have $p \leq M^{1/2}$ for sufficiently large $M$.
    have h_p_le_sqrt_M : ∃ M0, ∀ M ≥ M0, 2 * k_param r M ≤ (M : ℝ) ^ (1 / 2 : ℝ) := by
      -- Since $k \approx \frac{\gamma}{8} \frac{q-1}{\log q} \log M$, we have $2k \approx \frac{\gamma}{4} \frac{q-1}{\log q} \log M$.
      have h_2k_approx : ∃ C : ℝ, ∀ M ≥ 2, 2 * k_param r M ≤ C * Real.log M := by
        use 2 * (γ / 8) * ((q r : ℝ) - 1) / Real.log (q r) + 2;
        intro M hM
        have h_k_le : (k_param r M : ℝ) ≤ (γ / 8) * ((q r : ℝ) - 1) / Real.log (q r) * Real.log M := by
          refine' le_trans ( Nat.floor_le _ ) _;
          · exact mul_nonneg ( div_nonneg ( mul_nonneg ( by norm_num [ γ ] ) ( sub_nonneg.mpr ( Nat.one_le_cast.mpr ( Nat.Prime.pos ( show Nat.Prime ( q r ) from by exact Nat.prime_nth_prime _ ) ) ) ) ) ( Real.log_nonneg ( Nat.one_le_cast.mpr ( Nat.Prime.pos ( show Nat.Prime ( q r ) from by exact Nat.prime_nth_prime _ ) ) ) ) ) ( Real.log_nonneg ( Nat.one_le_cast.mpr ( by linarith ) ) );
          · unfold c q; aesop;
        ring_nf at *; nlinarith [ Real.log_nonneg ( show ( M : ℝ ) ≥ 1 by norm_cast; linarith ) ] ;
      -- Since $\log M$ grows slower than any polynomial function, we can find $M0$ such that for all $M \geq M0$, $C \log M \leq M^{1/2}$.
      obtain ⟨C, hC⟩ := h_2k_approx;
      have h_log_growth : ∃ M0 : ℕ, ∀ M ≥ M0, C * Real.log M ≤ (M : ℝ) ^ (1 / 2 : ℝ) := by
        -- We can divide both sides by $\sqrt{M}$ to get $C \frac{\log M}{\sqrt{M}} \leq 1$.
        suffices h_div : ∃ M0 : ℕ, ∀ M ≥ M0, C * (Real.log M / Real.sqrt M) ≤ 1 by
          norm_num [ ← Real.sqrt_eq_rpow ] at *;
          exact ⟨ h_div.choose + 2, fun M hM => by have := h_div.choose_spec M ( by linarith ) ; rw [ mul_div, div_le_iff₀ ( Real.sqrt_pos.mpr ( Nat.cast_pos.mpr ( by linarith ) ) ) ] at this; linarith ⟩;
        -- We know that $\frac{\log M}{\sqrt{M}}$ tends to $0$ as $M$ tends to infinity.
        have h_log_sqrt_zero : Filter.Tendsto (fun M : ℕ => Real.log M / Real.sqrt M) Filter.atTop (nhds 0) := by
          -- Let $y = \sqrt{M}$, so we can rewrite the limit as $\lim_{y \to \infty} \frac{\log y^2}{y} = \lim_{y \to \infty} \frac{2 \log y}{y}$.
          suffices h_log_sqrt_y : Filter.Tendsto (fun y : ℝ => 2 * Real.log y / y) Filter.atTop (nhds 0) by
            have := h_log_sqrt_y.comp ( show Filter.Tendsto ( fun M : ℕ => Real.sqrt M ) Filter.atTop Filter.atTop from Filter.tendsto_atTop_atTop.mpr fun x => ⟨ Nat.ceil ( x ^ 2 ), fun M hM => Real.le_sqrt_of_sq_le <| by simpa using hM ⟩ );
            exact this.congr fun M => by rw [ Function.comp_apply ] ; rw [ Real.log_sqrt ( Nat.cast_nonneg _ ) ] ; ring;
          -- Let $z = \frac{1}{y}$, so we can rewrite the limit as $\lim_{z \to 0^+} 2z \log(1/z)$.
          suffices h_log_recip : Filter.Tendsto (fun z : ℝ => 2 * z * Real.log (1 / z)) (Filter.map (fun y => 1 / y) Filter.atTop) (nhds 0) by
            exact h_log_recip.congr ( by simp +contextual [ div_eq_mul_inv, mul_assoc, mul_comm ] );
          norm_num +zetaDelta at *;
          exact tendsto_nhdsWithin_of_tendsto_nhds ( by have := Real.continuous_mul_log.tendsto 0; simpa [ mul_assoc ] using this.neg.const_mul 2 );
        simpa using h_log_sqrt_zero.const_mul C |> fun h => h.eventually ( ge_mem_nhds <| by norm_num );
      exact ⟨ Max.max 2 h_log_growth.choose, fun M hM => le_trans ( hC M ( le_trans ( le_max_left _ _ ) hM ) ) ( h_log_growth.choose_spec M ( le_trans ( le_max_right _ _ ) hM ) ) ⟩;
    exact ⟨ h_p_le_sqrt_M.choose, fun M hM pp hpp => le_trans ( mod_cast Finset.mem_filter.mp hpp |>.1 |> fun x => Finset.mem_range_succ_iff.mp x ) ( h_p_le_sqrt_M.choose_spec M hM ) ⟩;
  -- Since $t = \lceil \gamma/4 \log_p M \rceil$, we have $t \leq \gamma/4 \log_p M + 1$.
  have h_t_le : ∀ M ≥ 2, ∀ pp : ℕ, pp.Prime → (pp : ℝ) > 1 → t pp M ≤ (γ / 4) * (Real.log M / Real.log pp) + 1 := by
    exact fun M hM pp hp hp' => le_of_lt <| Nat.ceil_lt_add_one <| mul_nonneg ( by norm_num [ γ ] ) <| div_nonneg ( Real.log_nonneg <| mod_cast by linarith ) <| Real.log_nonneg <| mod_cast hp.one_lt.le;
  -- Combining the above results, we get $p^t \leq p^{(\gamma/4) \log_p M + 1} = p \cdot M^{\gamma/4}$.
  have h_combined : ∃ M0, ∀ M ≥ M0, ∀ pp ∈ Pi r M, (pp : ℝ) ^ (t pp M) ≤ (pp : ℝ) * (M : ℝ) ^ (γ / 4 : ℝ) := by
    have h_combined : ∀ M ≥ 2, ∀ pp : ℕ, pp.Prime → (pp : ℝ) > 1 → (pp : ℝ) ^ (t pp M) ≤ (pp : ℝ) * (M : ℝ) ^ (γ / 4 : ℝ) := by
      intros M hM pp hp hp_gt1
      have h_exp : (pp : ℝ) ^ (t pp M) ≤ (pp : ℝ) ^ ((γ / 4) * (Real.log M / Real.log pp) + 1) := by
        exact_mod_cast Real.rpow_le_rpow_of_exponent_le hp_gt1.le ( h_t_le M hM pp hp hp_gt1 );
      convert h_exp using 1 ; rw [ Real.rpow_add <| by positivity, Real.rpow_one ] ; rw [ Real.rpow_def_of_pos <| by positivity, Real.rpow_def_of_pos <| by positivity ] ; ring_nf;
      norm_num [ ne_of_gt, Real.log_pos hp_gt1 ];
    exact ⟨ 2, fun M hM pp hpp => h_combined M hM pp ( Finset.mem_filter.mp hpp |>.2.1 ) ( mod_cast Nat.Prime.one_lt ( Finset.mem_filter.mp hpp |>.2.1 ) ) ⟩;
  -- Since $p \leq M^{1/2}$, we have $p \cdot M^{\gamma/4} \leq M^{1/2} \cdot M^{\gamma/4} = M^{1/2 + \gamma/4}$.
  obtain ⟨M0, hM0⟩ := h_combined;
  obtain ⟨M1, hM1⟩ := h_p_le_sqrt_M;
  use max M0 M1;
  intro M hM pp hpp;
  have h_exp : (pp : ℝ) * (M : ℝ) ^ (γ / 4 : ℝ) ≤ (M : ℝ) ^ (1 / 2 + γ / 4 : ℝ) := by
    rw [ Real.rpow_add' ] <;> norm_num;
    · exact mul_le_mul_of_nonneg_right ( hM1 M ( le_trans ( le_max_right _ _ ) hM ) pp hpp ) ( by positivity );
    · unfold γ; norm_num;
  refine le_trans ( hM0 M ( le_trans ( le_max_left _ _ ) hM ) pp hpp ) ( h_exp.trans ?_ );
  unfold γ η; norm_num;
  rcases M with ( _ | _ | M ) <;> norm_num at *;
  exact Real.rpow_le_rpow_of_exponent_le ( by linarith ) ( by norm_num )

/-
The number of primes in Pi is at most 2k+1.
-/
lemma Pi_card_le (r M : ℕ) : (Pi r M).card ≤ 2 * k_param r M + 1 := by
  exact le_trans ( Finset.card_filter_le _ _ ) ( by simp +arith +decide )

/-
p^t >= M^(gamma/4).
-/
lemma p_pow_t_ge (p M : ℕ) (hp : p ≥ 2) (hM : M ≥ 1) :
    (p : ℝ) ^ (t p M) ≥ (M : ℝ) ^ (γ / 4) := by
  have h_exp : (p : ℝ) ^ t p M ≥ (p : ℝ) ^ (γ / 4 * (Real.log M / Real.log p)) := by
    exact_mod_cast Real.rpow_le_rpow_of_exponent_le ( Nat.one_le_cast.mpr ( by linarith ) ) ( Nat.le_ceil _ );
  convert h_exp using 1 ; rw [ Real.rpow_def_of_pos ( by positivity ), Real.rpow_def_of_pos ( by positivity ) ] ; ring_nf;
  norm_num [ ne_of_gt, Real.log_pos, show p > 1 by linarith ]

/-
Lemma 3 (Forced carries from a large p-power divisor).
If p^j divides m+i and i <= (p-1)/2, then kappa_p(m) >= j.
-/
lemma forced_carries_largep (p m i j : ℕ) [Fact p.Prime] (hi_pos : 1 ≤ i) (hi_le : i ≤ (p - 1) / 2) (h_div : p ^ j ∣ m + i) :
    j ≤ κ p m := by
  convert kappa_ge_j p m i j Fact.out hi_pos h_div _;
  omega

/-
Union bound for prob_event.
-/
lemma prob_union_bound (M : ℕ) (S : Finset ℕ) (P : ℕ → ℕ → Prop) [∀ p, DecidablePred (P p)] :
    prob_event M (fun m => ∀ p ∈ S, P p m) ≥ 1 - ∑ p ∈ S, prob_event M (fun m => ¬ P p m) := by
      -- Let's rewrite the goal using the definition of probability.
      suffices h_suff : ((Finset.Icc M (2 * M)).filter (fun m => ∀ p ∈ S, P p m)).card ≥ (M + 1) - ∑ p ∈ S, ((Finset.Icc M (2 * M)).filter (fun m => ¬P p m)).card by
        unfold prob_event;
        rw [ ← Finset.sum_div _ _ _, ge_iff_le, sub_le_iff_le_add ];
        rw [ ← add_div, le_div_iff₀ ] <;> norm_cast <;> aesop;
      have h_prob_event : Finset.card (Finset.filter (fun m => ∀ p ∈ S, P p m) (Finset.Icc M (2 * M))) ≥ Finset.card (Finset.Icc M (2 * M)) - Finset.card (Finset.biUnion S (fun p => Finset.filter (fun m => ¬P p m) (Finset.Icc M (2 * M)))) := by
        rw [ show ( Finset.filter ( fun m => ∀ p ∈ S, P p m ) ( Finset.Icc M ( 2 * M ) ) ) = Finset.Icc M ( 2 * M ) \ ( Finset.biUnion S fun p => Finset.filter ( fun m => ¬P p m ) ( Finset.Icc M ( 2 * M ) ) ) from ?_ ];
        · grind;
        · ext; aesop;
      simp_all +decide [ two_mul ];
      linarith [ show Finset.card ( Finset.biUnion S fun p => Finset.filter ( fun m => ¬P p m ) ( Finset.Icc M ( M + M ) ) ) ≤ ∑ x ∈ S, Finset.card ( Finset.filter ( fun m => ¬P x m ) ( Finset.Icc M ( M + M ) ) ) from Finset.card_biUnion_le ]

/-
The sum of 4/M^eta over Pi tends to 0 as M -> infinity.
-/
lemma sum_const_bound_tendsto_zero (r : ℕ) :
    Filter.Tendsto (fun M => ∑ _ ∈ Pi r M, 4 / (M : ℝ) ^ η) Filter.atTop (nhds 0) := by
      -- The sum over Pi is bounded by (2k + 1) * 4/M^eta.
      have h_bound : ∀ M : ℕ, (∑ _ ∈ Pi r M, (4 : ℝ) / (M : ℝ) ^ η) ≤ (2 * Nat.floor (c r * Real.log M) + 1) * 4 / (M : ℝ) ^ η := by
        intro M;
        refine' le_trans ( Finset.sum_le_sum_of_subset_of_nonneg ( Finset.filter_subset _ _ ) fun _ _ _ => by positivity ) _;
        norm_num [ mul_div_assoc ];
        bound;
      -- Since $c r$ is a constant, $2 * Nat.floor (c r * Real.log M)$ grows slower than $M^η$.
      have h_floor : Filter.Tendsto (fun M : ℕ => (Nat.floor (c r * Real.log M) : ℝ) / (M : ℝ) ^ η) Filter.atTop (nhds 0) := by
        -- We'll use the fact that $Nat.floor (c r * Real.log M)$ grows slower than $M^η$.
        have h_floor_growth : Filter.Tendsto (fun M : ℕ => (c r * Real.log M) / (M : ℝ) ^ η) Filter.atTop (nhds 0) := by
          -- Let $y = \log M$, therefore the expression becomes $\frac{c r y}{e^{η y}}$.
          suffices h_log : Filter.Tendsto (fun y : ℝ => (c r * y) / Real.exp (η * y)) Filter.atTop (nhds 0) by
            have := h_log.comp ( Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop );
            refine this.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with M hM using by simp +decide [ Real.rpow_def_of_pos ( Nat.cast_pos.mpr hM ), mul_comm ] );
          -- Let $z = \eta y$, therefore the expression becomes $\frac{c r}{\eta} \cdot \frac{z}{e^z}$.
          suffices h_z : Filter.Tendsto (fun z : ℝ => (c r / η) * z / Real.exp z) Filter.atTop (nhds 0) by
            convert h_z.comp ( Filter.tendsto_id.const_mul_atTop ( show 0 < η by norm_num [ η ] ) ) using 2 ; norm_num ; ring_nf;
            norm_num [ mul_assoc, mul_comm η, show η ≠ 0 by norm_num [ η ] ];
          simpa [ mul_div_assoc, Real.exp_neg ] using tendsto_const_nhds.mul ( Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1 );
        refine' squeeze_zero_norm' _ h_floor_growth;
        filter_upwards [ Filter.eventually_gt_atTop 1 ] with M hM using by rw [ Real.norm_of_nonneg ( by positivity ) ] ; exact div_le_div_of_nonneg_right ( Nat.floor_le <| mul_nonneg ( show ( 0 : ℝ ) ≤ c r by exact div_nonneg ( mul_nonneg ( by norm_num [ γ ] ) <| sub_nonneg.mpr <| Nat.one_le_cast.mpr <| Nat.Prime.pos <| by exact Nat.prime_nth_prime _ ) <| Real.log_nonneg <| Nat.one_le_cast.mpr <| Nat.Prime.pos <| by exact Nat.prime_nth_prime _ ) <| Real.log_nonneg <| Nat.one_le_cast.mpr <| by linarith ) <| by positivity;
      refine' squeeze_zero ( fun M => Finset.sum_nonneg fun _ _ => by positivity ) h_bound _;
      ring_nf;
      simpa using Filter.Tendsto.add ( h_floor.mul_const 8 ) ( tendsto_inv_atTop_zero.comp ( tendsto_rpow_atTop ( by norm_num [ η ] ) |> Filter.Tendsto.comp <| tendsto_natCast_atTop_atTop ) |> Filter.Tendsto.mul_const 4 )

/-
The sum of exp(-c1 log M / log p) over Pi tends to 0.
-/
lemma sum_exp_bound_tendsto_zero (r : ℕ) :
    Filter.Tendsto (fun M => ∑ pp ∈ Pi r M, Real.exp (-c1 * (Real.log M / Real.log pp))) Filter.atTop (nhds 0) := by
      have := @Pi_card_le r;
      -- We'll use the fact that $k \sim c \log M$ to bound the sum.
      have h_bound : ∃ C > 0, ∀ M ≥ 2, k_param r M ≤ C * Real.log M := by
        use c r + 1, by
          exact add_pos_of_nonneg_of_pos ( div_nonneg ( mul_nonneg ( by norm_num [ γ ] ) ( sub_nonneg.mpr ( Nat.one_le_cast.mpr ( Nat.Prime.pos ( show Nat.Prime ( q r ) from Nat.prime_nth_prime _ ) ) ) ) ) ( Real.log_nonneg ( Nat.one_le_cast.mpr ( Nat.Prime.pos ( show Nat.Prime ( q r ) from Nat.prime_nth_prime _ ) ) ) ) ) zero_lt_one
        generalize_proofs at *; (
        intro M hM; rw [ k_param ] ; exact le_trans ( Nat.floor_le ( mul_nonneg ( show 0 ≤ c r by exact div_nonneg ( mul_nonneg ( by norm_num [ γ ] ) ( sub_nonneg.mpr <| Nat.one_le_cast.mpr <| Nat.Prime.pos <| by exact Nat.prime_nth_prime _ ) ) <| Real.log_nonneg <| Nat.one_le_cast.mpr <| Nat.Prime.pos <| by exact Nat.prime_nth_prime _ ) <| Real.log_nonneg <| Nat.one_le_cast.mpr <| by linarith ) ) <| by nlinarith [ Real.log_nonneg <| show ( M :ℝ ) ≥ 1 by norm_cast; linarith ] ;);
      -- Using the bound on $k$, we can show that the sum of the probabilities tends to 0.
      obtain ⟨C, hC_pos, hC_bound⟩ := h_bound;
      have h_sum_zero : Filter.Tendsto (fun M : ℕ => (2 * C * Real.log M + 1) * Real.exp (-c1 * (Real.log M / Real.log (2 * C * Real.log M + 1)))) Filter.atTop (nhds 0) := by
        -- Let $u = \log M$. Then we need to show that $(2C u + 1) \exp(-c1 u / \log(2C u + 1))$ tends to 0 as $u$ tends to infinity.
        suffices h_log : Filter.Tendsto (fun u : ℝ => (2 * C * u + 1) * Real.exp (-c1 * u / Real.log (2 * C * u + 1))) Filter.atTop (nhds 0) by
          convert h_log.comp ( Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop ) using 2 ; norm_num ; ring_nf;
          norm_num;
        -- Let $v = \log(2Cu + 1)$. Then we need to show that $(2Cu + 1) \exp(-c1 u / v)$ tends to 0 as $v$ tends to infinity.
        suffices h_log' : Filter.Tendsto (fun v : ℝ => (Real.exp v) * Real.exp (-c1 * (Real.exp v - 1) / (2 * C * v))) Filter.atTop (nhds 0) by
          have h_log' : Filter.Tendsto (fun u : ℝ => (Real.exp (Real.log (2 * C * u + 1))) * Real.exp (-c1 * (Real.exp (Real.log (2 * C * u + 1)) - 1) / (2 * C * Real.log (2 * C * u + 1)))) Filter.atTop (nhds 0) := by
            exact h_log'.comp ( Real.tendsto_log_atTop.comp <| Filter.tendsto_atTop_add_const_right _ _ <| Filter.tendsto_id.const_mul_atTop <| by positivity );
          refine h_log'.congr' ?_;
          filter_upwards [ Filter.eventually_gt_atTop 0 ] with u hu;
          rw [ Real.exp_log ( by positivity ) ] ; ring_nf;
          norm_num [ mul_assoc, mul_comm C, hC_pos.ne' ];
        -- We can simplify the expression inside the exponential.
        suffices h_simplify : Filter.Tendsto (fun v : ℝ => v - c1 * (Real.exp v - 1) / (2 * C * v)) Filter.atTop Filter.atBot by
          simpa [ ← Real.exp_add, neg_div ] using h_simplify;
        -- We can factor out $v$ from the expression inside the limit.
        suffices h_factor : Filter.Tendsto (fun v : ℝ => v * (1 - c1 * (Real.exp v - 1) / (2 * C * v^2))) Filter.atTop Filter.atBot by
          grind;
        -- We can factor out $v$ from the expression inside the limit and use the fact that $c1 * (Real.exp v - 1) / (2 * C * v^2)$ tends to infinity as $v$ tends to infinity.
        have h_factor : Filter.Tendsto (fun v : ℝ => c1 * (Real.exp v - 1) / (2 * C * v^2)) Filter.atTop Filter.atTop := by
          -- We can factor out $v$ from the expression inside the limit and use the fact that $c1 * (Real.exp v - 1) / v^2$ tends to infinity as $v$ tends to infinity.
          have h_factor : Filter.Tendsto (fun v : ℝ => (Real.exp v - 1) / v^2) Filter.atTop Filter.atTop := by
            have h_exp : Filter.Tendsto (fun v : ℝ => Real.exp v / v ^ 2) Filter.atTop Filter.atTop := by
              exact Real.tendsto_exp_div_pow_atTop 2;
            simp_all +decide [ sub_div ];
            exact Filter.Tendsto.atTop_add h_exp ( Filter.Tendsto.neg ( tendsto_inv_atTop_zero.comp ( by norm_num ) ) );
          convert h_factor.const_mul_atTop ( show 0 < c1 / ( 2 * C ) by exact div_pos ( show 0 < c1 by exact div_pos ( sub_pos.mpr <| by norm_num [ η ] ) <| by norm_num ) <| by positivity ) using 2 ; ring;
        rw [ Filter.tendsto_atTop_atBot ];
        exact fun b => Filter.eventually_atTop.mp ( h_factor.eventually_gt_atTop ( |b| + 1 ) ) |> fun ⟨ i, hi ⟩ => ⟨ Max.max i 1, fun x hx => by cases abs_cases b <;> nlinarith [ hi x ( le_trans ( le_max_left _ _ ) hx ), le_max_right i 1 ] ⟩;
      refine' squeeze_zero_norm' _ h_sum_zero;
      filter_upwards [ Filter.eventually_ge_atTop 2 ] with M hM;
      rw [ Real.norm_of_nonneg ( Finset.sum_nonneg fun _ _ => Real.exp_nonneg _ ) ];
      refine' le_trans ( Finset.sum_le_sum fun p hp => Real.exp_le_exp.mpr <| mul_le_mul_of_nonpos_left ( div_le_div_of_nonneg_left _ _ _ ) <| neg_nonpos.mpr <| show 0 ≤ c1 by exact div_nonneg ( sub_nonneg.mpr <| by norm_num [ η ] ) <| by norm_num [ c1 ] ) _;
      any_goals exact fun p => Real.log ( 2 * C * Real.log M + 1 );
      · positivity;
      · exact Real.log_pos <| Nat.one_lt_cast.mpr <| Nat.Prime.one_lt <| Finset.mem_filter.mp hp |>.2.1;
      · gcongr;
        · exact Nat.cast_pos.mpr ( Nat.Prime.pos ( Finset.mem_filter.mp hp |>.2.1 ) );
        · have := Finset.mem_filter.mp hp |>.2.2; ( have := Finset.mem_filter.mp hp |>.2.1; ( have := Finset.mem_range.mp ( Finset.mem_filter.mp hp |>.1 ) ; ( norm_num at * ; nlinarith [ hC_bound M hM, show ( p : ℝ ) ≤ 2 * k_param r M + 1 from mod_cast by linarith ] ; ) ) );
      · norm_num;
        exact mul_le_mul_of_nonneg_right ( le_trans ( Nat.cast_le.mpr ( this M ) ) ( by push_cast; nlinarith [ hC_bound M hM, Real.log_nonneg ( show ( M : ℝ ) ≥ 1 by norm_cast; linarith ) ] ) ) ( Real.exp_nonneg _ )

/-
The sum of k/p^t over Pi tends to 0.
-/
lemma sum_k_div_pow_tendsto_zero (r : ℕ) :
    Filter.Tendsto (fun M => ∑ pp ∈ Pi r M, (k_param r M : ℝ) / (pp ^ t pp M : ℝ)) Filter.atTop (nhds 0) := by
      -- Sum <= |Pi| * max (k / p^t).
      have h_sum_le : ∀ M : ℕ, M ≥ 2 → ∑ pp ∈ Pi r M, (k_param r M : ℝ) / pp ^ t pp M ≤ (2 * k_param r M + 1) * (k_param r M : ℝ) / (M : ℝ) ^ (γ / 4) := by
        intro M hM
        have h_card_pi : (Pi r M).card ≤ 2 * k_param r M + 1 := by
          exact Pi_card_le r M;
        have h_max : ∀ pp ∈ Pi r M, (k_param r M : ℝ) / pp ^ t pp M ≤ (k_param r M : ℝ) / (M : ℝ) ^ (γ / 4) := by
          intros pp hpp
          have h_exp : (pp : ℝ) ^ (t pp M) ≥ (M : ℝ) ^ (γ / 4) := by
            exact p_pow_t_ge pp M ( Nat.Prime.two_le <| by unfold Pi at hpp; aesop ) ( by linarith );
          gcongr;
        refine le_trans ( Finset.sum_le_sum h_max ) ?_ ; norm_num [ mul_div_assoc ] ; gcongr ; norm_cast;
      -- Since $k \leq c \log M$, we have $(2k + 1)k \leq (2c \log M + 1)c \log M$.
      have h_bound : ∀ M : ℕ, M ≥ 2 → (2 * k_param r M + 1) * (k_param r M : ℝ) ≤ (2 * (c r) * Real.log M + 1) * (c r) * Real.log M := by
        intros M hM
        have h_k_le : (k_param r M : ℝ) ≤ (c r) * Real.log M := by
          exact Nat.floor_le ( mul_nonneg ( show 0 ≤ c r by exact div_nonneg ( mul_nonneg ( by norm_num [ γ ] ) ( sub_nonneg.mpr ( Nat.one_le_cast.mpr ( Nat.Prime.pos ( show Nat.Prime ( q r ) from Nat.prime_nth_prime _ ) ) ) ) ) ( Real.log_nonneg ( Nat.one_le_cast.mpr ( Nat.Prime.pos ( show Nat.Prime ( q r ) from Nat.prime_nth_prime _ ) ) ) ) ) ( Real.log_nonneg ( Nat.one_le_cast.mpr ( by linarith ) ) ) );
        nlinarith [ show 0 ≤ c r * Real.log M by exact mul_nonneg ( show 0 ≤ c r by exact div_nonneg ( mul_nonneg ( by norm_num [ γ ] ) ( sub_nonneg.mpr ( Nat.one_le_cast.mpr ( Nat.Prime.pos ( show Nat.Prime ( q r ) from Nat.prime_nth_prime _ ) ) ) ) ) ( Real.log_nonneg ( Nat.one_le_cast.mpr ( Nat.Prime.pos ( show Nat.Prime ( q r ) from Nat.prime_nth_prime _ ) ) ) ) ) ( Real.log_nonneg ( Nat.one_le_cast.mpr ( by linarith ) ) ) ];
      -- Therefore, $(2c \log M + 1)c \log M / M^{\gamma/4}$ tends to $0$ as $M \to \infty$.
      have h_tendsto_zero : Filter.Tendsto (fun M : ℕ => (2 * (c r) * Real.log M + 1) * (c r) * Real.log M / (M : ℝ) ^ (γ / 4)) Filter.atTop (nhds 0) := by
        -- Let $y = \log M$, therefore the expression becomes $\frac{(2c y + 1)c y}{e^{y \gamma / 4}}$.
        suffices h_log : Filter.Tendsto (fun y : ℝ => (2 * (c r) * y + 1) * (c r) * y / Real.exp (y * (γ / 4))) Filter.atTop (nhds 0) by
          have h_subst : Filter.Tendsto (fun M : ℕ => (2 * (c r) * Real.log M + 1) * (c r) * Real.log M / Real.exp (Real.log M * (γ / 4))) Filter.atTop (nhds 0) := by
            exact h_log.comp ( Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop );
          refine h_subst.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with M hM using by rw [ Real.rpow_def_of_pos ( Nat.cast_pos.mpr hM ) ] );
        -- Let $z = y \gamma / 4$, therefore the expression becomes $\frac{(2c z / (\gamma / 4) + 1)c z / (\gamma / 4)}{e^z}$.
        suffices h_z : Filter.Tendsto (fun z : ℝ => (2 * (c r) * z / (γ / 4) + 1) * (c r) * z / (γ / 4) / Real.exp z) Filter.atTop (nhds 0) by
          convert h_z.comp ( Filter.tendsto_id.atTop_mul_const ( show 0 < ( γ / 4 : ℝ ) by norm_num [ γ ] ) ) using 2 ; norm_num ; ring_nf;
          norm_num [ mul_assoc, mul_comm, mul_left_comm, γ ];
          ring;
        -- We can factor out $z$ from the numerator and use the fact that $\frac{z}{e^z}$ tends to $0$ as $z$ tends to infinity.
        suffices h_factor : Filter.Tendsto (fun z : ℝ => z ^ 2 / Real.exp z) Filter.atTop (nhds 0) ∧ Filter.Tendsto (fun z : ℝ => z / Real.exp z) Filter.atTop (nhds 0) by
          convert Filter.Tendsto.add ( h_factor.1.const_mul ( 2 * c r * c r / ( γ / 4 ) ^ 2 ) ) ( h_factor.2.const_mul ( c r / ( γ / 4 ) ) ) using 2 <;> ring;
        exact ⟨ by simpa [ Real.exp_neg ] using Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 2, by simpa [ Real.exp_neg ] using Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1 ⟩;
      refine' squeeze_zero_norm' _ h_tendsto_zero;
      filter_upwards [ Filter.eventually_ge_atTop 2 ] with M hM using by rw [ Real.norm_of_nonneg ( Finset.sum_nonneg fun _ _ => by positivity ) ] ; exact le_trans ( h_sum_le M hM ) ( by exact div_le_div_of_nonneg_right ( h_bound M hM ) ( by positivity ) ) ;

/-
The total sum of failure bounds tends to 0.
-/
lemma total_sum_tendsto_zero (r : ℕ) :
    Filter.Tendsto (fun M => ∑ pp ∈ Pi r M, (Real.exp (-c1 * (Real.log M / Real.log pp)) + (k_param r M : ℝ) / (pp ^ t pp M : ℝ) + 4 / (M : ℝ) ^ η)) Filter.atTop (nhds 0) := by
      -- Apply the fact that the sum of limits is the limit of the sums.
      have h_sum : Filter.Tendsto (fun M => (∑ pp ∈ Pi r M, Real.exp (-c1 * (Real.log M / Real.log pp))) + (∑ pp ∈ Pi r M, (k_param r M : ℝ) / (pp ^ t pp M : ℝ)) + (∑ pp ∈ Pi r M, (4 / (M : ℝ) ^ η))) Filter.atTop (nhds (0 + 0 + 0)) := by
        exact Filter.Tendsto.add ( Filter.Tendsto.add ( by simpa using sum_exp_bound_tendsto_zero r ) ( by simpa using sum_k_div_pow_tendsto_zero r ) ) ( by simpa using sum_const_bound_tendsto_zero r );
      simpa [ Finset.sum_add_distrib ] using h_sum

/-
The sum of failure bounds is eventually less than 1.
-/
lemma sum_failure_bound_lt_one (r : ℕ) :
    ∃ M0, ∀ M ≥ M0,
    ∑ pp ∈ Pi r M, (Real.exp (-c1 * (Real.log M / Real.log pp)) + (k_param r M : ℝ) / (pp ^ t pp M : ℝ) + 4 / (M : ℝ) ^ η) < 1 := by
  have := total_sum_tendsto_zero r;
  simpa using this.eventually ( gt_mem_nhds zero_lt_one )

/-
Lemma 14.
For sufficiently large M and p in Pi, the failure probability is bounded by the sum of the individual bounds.
-/
lemma prob_failure_le_bound (r : ℕ) :
    ∃ M0, ∀ M ≥ M0, ∀ pp ∈ Pi r M,
    prob_event M (fun m => ¬(G_event pp M m ∧ H_event r pp M m)) ≤
    Real.exp (-c1 * (Real.log M / Real.log pp)) + (k_param r M : ℝ) / (pp ^ t pp M : ℝ) + 4 / (M : ℝ) ^ η := by
      -- We bound prob(not (G and H)) <= prob(not G) + prob(not H).
      have h_bound : ∀ M pp, pp ∈ Pi r M →
          prob_event M (fun m => ¬(G_event pp M m ∧ H_event r pp M m)) ≤
          prob_event M (fun m => ¬G_event pp M m) + prob_event M (fun m => ¬H_event r pp M m) := by
            intro M pp hpp; rw [ prob_event ] ; rw [ prob_event ] ; rw [ prob_event ] ;
            field_simp;
            exact mod_cast le_trans ( Finset.card_le_card fun x hx => by by_cases h : G_event pp M x <;> by_cases h' : H_event r pp M x <;> aesop ) ( Finset.card_union_le _ _ );
      -- Apply the bounds from uniform_carry_threshold and V_p_tail.
      obtain ⟨M0, hM0⟩ : ∃ M0, ∀ M ≥ M0, ∀ pp ∈ Pi r M, pp.Prime → 3 ≤ pp → pp ≤ 2 * k_param r M →
          prob_event M (fun m => ¬G_event pp M m) ≤ Real.exp (-c1 * (Real.log M / Real.log pp)) + 2 / (M : ℝ) ^ η := by
            obtain ⟨ M0, hM0 ⟩ := uniform_carry_threshold r;
            use M0;
            intros M hM pp hpp hp_prime hp_ge_3 hp_le_2k
            specialize hM0 M hM pp hp_prime hp_ge_3 hp_le_2k;
            refine le_trans ?_ hM0;
            refine' div_le_div_of_nonneg_right _ ( by positivity );
            norm_num [ G_event ];
            exact Finset.card_mono fun x hx => Finset.mem_filter.mpr ⟨ Finset.mem_filter.mp hx |>.1, le_of_lt <| Finset.mem_filter.mp hx |>.2 ⟩;
      -- Apply the bound from V_p_tail.
      obtain ⟨M1, hM1⟩ : ∃ M1, ∀ M ≥ M1, ∀ pp ∈ Pi r M, pp.Prime → 3 ≤ pp → pp ≤ 2 * k_param r M →
          prob_event M (fun m => ¬H_event r pp M m) ≤ (k_param r M : ℝ) / (pp ^ t pp M : ℝ) + 2 / (M : ℝ) ^ η := by
            obtain ⟨ M1, hM1 ⟩ := V_p_condition_holds r;
            use Max.max M1 2;
            intros M hM pp hpp hp_prime hp_ge_3 hp_le_2k
            have hV_p_tail : prob_event M (fun m => V pp m (k_param r M) ≥ t pp M) ≤ (k_param r M : ℝ) / (pp ^ t pp M : ℝ) + 2 / (M : ℝ) ^ η := by
              apply V_p_tail pp (t pp M) M (k_param r M) hp_prime (Nat.ceil_pos.mpr (by
              exact mul_pos ( by norm_num [ γ ] ) ( div_pos ( Real.log_pos ( by norm_cast; linarith [ le_max_right M1 2 ] ) ) ( Real.log_pos ( by norm_cast; linarith ) ) ))) (by
              linarith [ le_max_right M1 2 ]) (hM1 M (le_trans (le_max_left _ _) hM) pp hpp);
            unfold H_event; aesop;
      use Max.max M0 M1;
      intros M hM pp hpp
      have h_prime : pp.Prime := by
        exact Finset.mem_filter.mp hpp |>.2.1
      have h_ge_3 : 3 ≤ pp := by
        contrapose! hpp; interval_cases pp <;> simp_all +decide ;
        simp +decide [ Pi ];
        exact fun _ => Nat.Prime.two_le ( Nat.prime_nth_prime _ )
      have h_le_2k : pp ≤ 2 * k_param r M := by
        exact Finset.mem_filter.mp hpp |>.2.2 |> fun h => by linarith [ Finset.mem_range.mp ( Finset.mem_filter.mp hpp |>.1 ) ] ;
      exact le_trans ( h_bound M pp hpp ) ( by convert add_le_add ( hM0 M ( le_trans ( le_max_left _ _ ) hM ) pp hpp h_prime h_ge_3 h_le_2k ) ( hM1 M ( le_trans ( le_max_right _ _ ) hM ) pp hpp h_prime h_ge_3 h_le_2k ) using 1 ; ring )

/-
Lemma 11 (Positive probability).
For sufficiently large M, the probability that (G_p and H_p) holds for all p in Pi is positive.
-/
lemma positive_probability_main (r : ℕ) :
    ∃ M0, ∀ M ≥ M0, prob_event M (fun m => ∀ pp ∈ Pi r M, G_event pp M m ∧ H_event r pp M m) > 0 := by
      obtain ⟨ M1, hM1 ⟩ := prob_failure_le_bound r;
      obtain ⟨ M2, hM2 ⟩ := sum_failure_bound_lt_one r;
      use Max.max M1 M2;
      intro M hM;
      specialize hM1 M ( le_trans ( le_max_left _ _ ) hM );
      specialize hM2 M ( le_trans ( le_max_right _ _ ) hM );
      have h_union := prob_union_bound M ( Pi r M ) ( fun pp m => G_event pp M m ∧ H_event r pp M m );
      refine lt_of_lt_of_le ?_ h_union;
      rw [ sub_pos ];
      refine lt_of_le_of_lt ( Finset.sum_le_sum fun pp hpp => hM1 pp hpp ) hM2

/-
Lemma 4 (All primes p > 2k are automatically good).
For every integer m and every prime p > 2k, W_p(m) <= kappa_p(m).
-/
lemma p_gt_2k (m k p : ℕ) (hp : p.Prime) (hp_gt : p > 2 * k) :
    W p m k ≤ κ p m := by
  -- Since $p > 2k$, we have $k / (p - 1) < 1$, thus $W_p(m) \leq V_p(m)$.
  have hW_le_V : W p m k ≤ V p m k := by
    have hW_le_V : W p m k ≤ k / (p - 1) + V p m k := by
      exact W_le_V p m k hp;
    rcases p with ( _ | _ | p ) <;> simp_all +decide
    exact hW_le_V.trans ( by rw [ Nat.div_eq_of_lt ] <;> linarith );
  -- Since $p > 2k$, we have $V_p(m) \leq \kappa_p(m)$ by definition of $V$.
  have hV_le_kappa : V p m k ≤ κ p m := by
    have h_def : ∀ i ∈ Finset.range k, padicValNat p (m + 1 + i) ≤ κ p m := by
      intro i hi;
      convert forced_carries_largep p m ( i + 1 ) ( padicValNat p ( m + 1 + i ) ) _ _ _ using 1;
      · exact ⟨ hp ⟩;
      · linarith;
      · rw [ Nat.le_div_iff_mul_le ] <;> linarith [ Finset.mem_range.mp hi, Nat.sub_add_cancel hp.pos ];
      · convert Nat.ordProj_dvd ( m + 1 + i ) p using 1 ; ring_nf;
        · rw [ Nat.factorization_def ] ; aesop;
        · ring
    exact Finset.sup_le h_def;
  linarith

/-
For p in Pi, if G and H hold, then W_p <= kappa_p.
-/
lemma divisibility_for_Pi (r M m : ℕ) (hr : r ≥ 1) (hM : M > 1) (pp : ℕ) (hpp : pp ∈ Pi r M)
    (hG : G_event pp M m) (hH : H_event r pp M m) :
    W pp m (k_param r M) ≤ κ pp m := by
  -- Using Lemma k_div_p_minus_one_le, we have (k_param r M : ℝ) / (pp - 1) ≤ (γ / 8) * (Real.log M / Real.log pp).
  have h_k_div_p_minus_one_le : (k_param r M : ℝ) / (pp - 1) ≤ (γ / 8) * (Real.log M / Real.log pp) := by
    apply k_div_p_minus_one_le r M pp hr (by
    exact Finset.mem_filter.mp hpp |>.2.1) (by
    unfold Pi at hpp;
    norm_num +zetaDelta at *;
    -- Since $pp$ is a prime and greater than $p_r$, it must be at least $p_{r+1}$, which is $q_r$.
    have hpp_ge_q : pp ≥ Nat.nth Nat.Prime r := by
      refine' Nat.le_of_lt_succ _;
      refine' Nat.lt_succ_of_le ( Nat.le_of_not_lt fun h => _ );
      rw [ Nat.nth_eq_sInf ] at h;
      refine' h.not_ge ( Nat.sInf_le ⟨ hpp.2.1, _ ⟩ );
      intro k hk; exact lt_of_le_of_lt ( Nat.nth_monotone ( Nat.infinite_setOf_prime ) ( Nat.le_sub_one_of_lt hk ) ) hpp.2.2;
    exact hpp_ge_q) hM;
  -- Since $V pp m (k_param r M) < t pp M$, we have $V pp m (k_param r M) \le t pp M - 1$.
  have h_V_le_t_minus_1 : (V pp m (k_param r M) : ℝ) ≤ (t pp M : ℝ) - 1 := by
    exact le_tsub_of_add_le_right ( mod_cast hH );
  -- Using Lemma W_le_V, we have $W pp m (k_param r M) \le (k_param r M) / (pp - 1) + V pp m (k_param r M)$.
  have h_W_le : (W pp m (k_param r M) : ℝ) ≤ (k_param r M : ℝ) / (pp - 1) + (V pp m (k_param r M) : ℝ) := by
    have := W_le_V pp m ( k_param r M ) ( show pp.Prime from Finset.mem_filter.mp hpp |>.2.1 );
    rcases pp with ( _ | _ | pp ) <;> norm_num at *;
    · unfold Pi at hpp; aesop;
    · rw [ div_add', le_div_iff₀ ] <;> norm_cast <;> nlinarith [ Nat.div_mul_le_self ( k_param r M ) ( pp + 1 ) ];
  -- Using Lemma t_def, we have $t pp M \le (γ / 4) * (Real.log M / Real.log pp) + 1$.
  have h_t_le : (t pp M : ℝ) ≤ (γ / 4) * (Real.log M / Real.log pp) + 1 := by
    exact le_of_lt ( Nat.ceil_lt_add_one ( mul_nonneg ( by norm_num [ γ ] ) ( div_nonneg ( Real.log_nonneg ( mod_cast hM.le ) ) ( Real.log_nonneg ( mod_cast Nat.Prime.pos ( by unfold Pi at hpp; aesop ) ) ) ) ) );
  exact Nat.cast_le.mp ( by linarith [ show ( κ pp m : ℝ ) ≥ γ * ( Real.log M / Real.log pp ) by exact_mod_cast hG ] : ( W pp m ( k_param r M ) : ℝ ) ≤ κ pp m )
  
/-
For large M, k > omega * log(2m).
-/
lemma k_gt_omega_log_2m (r : ℕ) :
    ∃ M0, ∀ M ≥ M0, ∀ m ∈ Finset.Icc M (2 * M),
    (k_param r M : ℝ) > ω r * Real.log (2 * m) := by
      -- We can choose $M0$ such that for all $M \geq M0$, $c \log M - 1 > \omega \log(4M)$.
      obtain ⟨M0, hM0⟩ : ∃ M0, ∀ M ≥ M0, (c r * Real.log M - 1) > ω r * (Real.log M + Real.log 4) := by
        have h_pos : 0 < (c r - ω r) := by
          unfold c ω; norm_num;
          unfold q p; ring_nf; norm_num [ γ ] ;
          nlinarith [ show ( Nat.nth Nat.Prime r : ℝ ) ≥ 2 by exact_mod_cast Nat.Prime.two_le ( Nat.prime_nth_prime r ), inv_pos.mpr ( Real.log_pos ( show ( Nat.nth Nat.Prime r : ℝ ) > 1 by exact_mod_cast Nat.Prime.one_lt ( Nat.prime_nth_prime r ) ) ) ];
        exact ⟨ Real.exp ( ( 1 + ω r * Real.log 4 ) / ( c r - ω r ) + 1 ), fun M hM => by nlinarith [ Real.log_exp ( ( 1 + ω r * Real.log 4 ) / ( c r - ω r ) + 1 ), Real.log_le_log ( by positivity ) hM, mul_div_cancel₀ ( 1 + ω r * Real.log 4 ) h_pos.ne' ] ⟩;
      -- By combining the results from hM0 and the properties of the floor function, we can conclude the proof.
      use Nat.ceil M0 + 1;
      intros M hM m hm; have := hM0 M ( Nat.le_of_ceil_le ( by linarith ) ) ; rw [ Real.log_mul ( by norm_num ) ( by norm_cast; linarith [ Finset.mem_Icc.mp hm ] ) ];
      -- Since $m \leq 2M$, we have $\log m \leq \log (2M) = \log 2 + \log M$.
      have h_log_m : Real.log m ≤ Real.log 2 + Real.log M := by
        rw [ ← Real.log_mul, Real.log_le_log_iff ] <;> norm_cast <;> nlinarith [ Finset.mem_Icc.mp hm ];
      rw [ show ( 4 : ℝ ) = 2 ^ 2 by norm_num, Real.log_pow ] at this ; norm_num at *;
      exact lt_of_lt_of_le ( by nlinarith [ Real.log_pos one_lt_two, show ω r > 0 from div_pos ( mul_pos ( by norm_num : ( 0 : ℝ ) < 9 / 70 / 16 ) ( sub_pos.mpr <| Nat.one_lt_cast.mpr <| Nat.Prime.one_lt <| Nat.prime_nth_prime _ ) ) <| Real.log_pos <| show ( q r : ℝ ) > 1 from Nat.one_lt_cast.mpr <| Nat.Prime.one_lt <| Nat.prime_nth_prime _ ] ) <| Nat.sub_one_lt_floor _ |> le_of_lt

/-
For large M, k <= M.
-/
lemma k_le_M_for_large_M (r : ℕ) :
    ∃ M0, ∀ M ≥ M0, k_param r M ≤ M := by
  -- We'll use that $k \leq M$ for sufficiently large $M$.
  have h_k_le_M : ∃ M0 : ℕ, ∀ M ≥ M0, (γ / 8) * ((q r) - 1) / (Real.log (q r)) * Real.log M ≤ M := by
    have h_log_growth : Filter.Tendsto (fun M : ℝ => (γ / 8) * ((q r : ℝ) - 1) / Real.log (q r) * Real.log M / M) Filter.atTop (nhds 0) := by
      -- We can factor out the constant $(γ / 8) * ((q r : ℝ) - 1) / Real.log (q r)$ and use the fact that $\frac{\log M}{M}$ tends to $0$ as $M$ tends to infinity.
      have h_log_div_M : Filter.Tendsto (fun M : ℝ => Real.log M / M) Filter.atTop (nhds 0) := by
        -- Let $y = \frac{1}{x}$, so we can rewrite the limit as $\lim_{y \to 0^+} y \log(1/y)$.
        suffices h_log_recip : Filter.Tendsto (fun y : ℝ => y * Real.log (1 / y)) (Filter.map (fun x => 1 / x) Filter.atTop) (nhds 0) by
          exact h_log_recip.congr ( by simp +contextual [ div_eq_inv_mul ] );
        norm_num;
        exact tendsto_nhdsWithin_of_tendsto_nhds ( by simpa using Real.continuous_mul_log.neg.tendsto 0 );
      simpa [ mul_div_assoc ] using h_log_div_M.const_mul _;
    have := h_log_growth.eventually ( gt_mem_nhds zero_lt_one );
    rw [ Filter.eventually_atTop ] at this; rcases this with ⟨ M0, hM0 ⟩ ; exact ⟨ ⌈M0⌉₊ + 1, fun M hM => by have := hM0 M ( Nat.le_of_ceil_le ( by linarith ) ) ; rw [ div_lt_iff₀ ( by norm_cast; linarith ) ] at this; linarith ⟩ ;
  exact ⟨ h_k_le_M.choose, fun M hM => Nat.floor_le_of_le <| h_k_le_M.choose_spec M hM ⟩

/-
If m satisfies the conditions for Pi and k <= m, then the divisibility holds.
-/
lemma divisibility_holds (r M m : ℕ) (hr : r ≥ 1) (hM : M > 1) (hm : k_param r M ≤ m)
    (h_Pi : ∀ pp ∈ Pi r M, G_event pp M m ∧ H_event r pp M m) :
    (Nat.factorial (m + k_param r M) * Nat.factorial m) ∣ (Nat.factorial (2 * m) * (P r)^(2 * m)) := by
      have := @primewise_target r m ( k_param r M ) hr;
      refine this.mpr fun pp hp => ?_;
      split_ifs;
      · exact le_add_of_nonneg_of_le ( Nat.zero_le _ ) ( paid_primes m ( k_param r M ) pp hp hm );
      · by_cases hpp : pp > 2 * k_param r M;
        · exact le_add_of_le_of_nonneg ( p_gt_2k m ( k_param r M ) pp hp hpp ) ( Nat.zero_le _ );
        · exact h_Pi pp ( Finset.mem_filter.mpr ⟨ Finset.mem_range.mpr ( by linarith ), hp, by linarith ⟩ ) |>.1 |> fun h => divisibility_for_Pi r M m hr hM pp ( Finset.mem_filter.mpr ⟨ Finset.mem_range.mpr ( by linarith ), hp, by linarith ⟩ ) h ( h_Pi pp ( Finset.mem_filter.mpr ⟨ Finset.mem_range.mpr ( by linarith ), hp, by linarith ⟩ ) |>.2 )

/-
For sufficiently large M, there exists a good m in [M, 2M].
-/
lemma exists_good_m (r : ℕ) (hr : r ≥ 1) :
    ∃ M0, ∀ M ≥ M0, ∃ m ∈ Finset.Icc M (2 * M),
      (Nat.factorial (m + k_param r M) * Nat.factorial m) ∣ (Nat.factorial (2 * m) * (P r)^(2 * m)) ∧
      (m + k_param r M) + m > 2 * m + ω r * Real.log (2 * m) := by
        -- By combining the results from the lemmas, we can conclude that for sufficiently large M, there exists an m in [M, 2M] satisfying the required conditions.
        obtain ⟨M1, hM1⟩ := positive_probability_main r
        obtain ⟨M2, hM2⟩ := k_le_M_for_large_M r
        obtain ⟨M3, hM3⟩ := k_gt_omega_log_2m r
        obtain ⟨M4, hM4⟩ := exists_nat_gt (2 * M2 + 2 * M3 + 2 * M1 + 2);
        use M4 + 2 * M3 + 2 * M2 + 2 * M1 + 2;
        intro M hM
        obtain ⟨m, hm⟩ : ∃ m ∈ Finset.Icc M (2 * M), ∀ pp ∈ Pi r M, G_event pp M m ∧ H_event r pp M m := by
          contrapose! hM1;
          refine' ⟨ M, _, _ ⟩ <;> norm_num [ prob_event ] at *;
          · linarith;
          · rw [ Finset.card_eq_zero.mpr ] <;> aesop;
        exact ⟨ m, hm.1, divisibility_holds r M m hr ( by linarith ) ( by linarith [ Finset.mem_Icc.mp hm.1, hM2 M ( by linarith ) ] ) hm.2, by linarith [ hM3 M ( by linarith ) m hm.1 ] ⟩

/-
Theorem 1.
For fixed r, there are infinitely many n with the desired property.
-/
theorem theorem_1 (r : ℕ) (hr : r ≥ 1) :
    Set.Infinite {n : ℕ | ∃ a1 a2 : ℕ, a1 > 0 ∧ a2 > 0 ∧
      (a1 : ℝ) + a2 > n + ω r * Real.log n ∧
      (Nat.factorial a1 * Nat.factorial a2) ∣ (Nat.factorial n * (P r)^n)} := by
  -- Apply the lemma to find such an $M0$.
  obtain ⟨M0, hM0⟩ := exists_good_m r hr;
  rw [ Set.infinite_iff_exists_gt ];
  intro a
  obtain ⟨m, hm⟩ := hM0 (a + M0 + 1) (by linarith);
  simp +zetaDelta at *;
  use 2 * m;
  exact ⟨ ⟨ m + k_param r ( a + M0 + 1 ), by linarith, m, by linarith, by push_cast; linarith, hm.2.1 ⟩, by linarith ⟩

#print axioms theorem_1
-- 'theorem_1' depends on axioms: [propext, Classical.choice, Quot.sound]
