/-

This is a Lean formalization of a solution to Erdős Problem 897.
https://www.erdosproblems.com/forum/thread/897

The original proof was found by: Eduard Wirsing

Eduard Wirsing. Additive and completely additive functions with
restricted growth. Recent progress in analytic number theory, Vol. 2
(Durham, 1979), pp. 231–280.  (See pp. 235 - 236.)


THIS proof was found by: Archivara Math Research Agent

An Additive Counterexample: Erdos Problem 897
https://archivara.org/paper/df04f023-6ef0-4c52-bd12-18cdaa8f0741


The proof by Archivara-Agent was auto-formalized into Lean by
Aristotle from Harmonic.

The final theorem statement is from the Formal Conjectures project
organized by Google DeepMind.


The proof is verified by Lean.  The following version numbers were
used:

Lean Toolchain version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7 (v4.24.0)

-/


/-
We have constructed an additive function $f$ and proven the following properties:
1. `lemma1`: $\limsup_{p, k} \frac{f(p^k)}{\log(p^k)} = \infty$.
2. `corollary1`: $\limsup_{n \to \infty} \frac{f(n+1)-f(n)}{\log n} \le 4$.
3. `f_pos_eventually`: $f(n) > 0$ for sufficiently large $n$.
4. `corollary2`: $\limsup_{n \to \infty} \frac{f(n+1)}{f(n)} = 1$.

These results answer negatively the question of Erdős asking whether an additive function that is arbitrarily large on prime powers relative to log must have arbitrarily large normalized consecutive differences or ratios.
-/

import Mathlib

namespace Erdos897


set_option linter.mathlibStandardSet false

open scoped Classical

/-
Define iterated logarithms by $\log ^{(0)} x:=x$ and, for $j \geq 0$ and $x>1$, $\log ^{(j+1)} x:=\log \left(\log ^{(j)} x\right)$. Define the iterated logarithm count (the "log-star" function) by $\log ^{*} x:=\min \left\{j \geq 0: \log ^{(j)} x \leq 1\right\}$.
-/
noncomputable def iteratedLog (j : ℕ) (x : ℝ) : ℝ :=
  match j with
  | 0 => x
  | j + 1 => Real.log (iteratedLog j x)

noncomputable def logStar (x : ℝ) : ℕ :=
  if h : ∃ j, iteratedLog j x ≤ 1 then Nat.find h else 0

/-
For each prime power $q=p^{k}$ with $k \geq 1$, define $f(q):=\log q \cdot \log ^{*} q$. Extend $f$ additively to all $n \geq 1$ via prime factorization: if $n=\prod_{i=1}^{r} p_{i}^{a_{i}}$ then $f(n):=\sum_{i=1}^{r} f\left(p_{i}^{a_{i}}\right)=\sum_{i=1}^{r} \log \left(p_{i}^{a_{i}}\right) \cdot \log ^{*}\left(p_{i}^{a_{i}}\right)$, and set $f(1)=0$.
-/
noncomputable def f_prime_power (p k : ℕ) : ℝ :=
  let q := (p : ℝ) ^ k
  Real.log q * (logStar q)

noncomputable def f (n : ℕ) : ℝ :=
  ∑ p ∈ n.factorization.support, f_prime_power p (n.factorization p)

/-
Lemma 1. For any prime power $q=p^{k}$, $\frac{f(q)}{\log q}=\log ^{*} q$. In particular, $\limsup _{p, k} \frac{f\left(p^{k}\right)}{\log \left(p^{k}\right)}=\infty$.
-/
lemma lemma1 (p k : ℕ) (hp : p.Prime) (hk : k ≥ 1) :
    let q := p ^ k
    f q / Real.log q = logStar q := by
      -- Apply the definition of $f_prime_power$ to rewrite $f$.
      have hf_prime_power : f (p ^ k) = f_prime_power p k := by
        unfold f;
        norm_num [ Nat.factorization_pow, hp, hk ];
        rw [ Finsupp.support_single_ne_zero ] <;> aesop;
      norm_num [ hf_prime_power, f_prime_power ];
      rw [ mul_div_cancel_left₀ _ ( mul_ne_zero ( Nat.cast_ne_zero.mpr ( by linarith ) ) ( ne_of_gt ( Real.log_pos ( Nat.one_lt_cast.mpr hp.one_lt ) ) ) ) ]

/-
Lemma 2. For all $n \geq 2$, $f(n) \leq \log ^{*} n \cdot \log n$.
-/
lemma lemma2 (n : ℕ) (hn : n ≥ 2) : f n ≤ logStar n * Real.log n := by
  -- By definition of $f$, we can write it as a sum over the prime factors of $n$.
  have h_def : f n = ∑ p ∈ n.factorization.support, (Real.log (p ^ (n.factorization p))) * (logStar (p ^ (n.factorization p))) := by
    exact rfl;
  -- Since $\log^* q_i \leq \log^* n$ for each prime factor $p_i$ of $n$, we can bound the sum.
  have h_bound : ∀ p ∈ n.factorization.support, (logStar (p ^ (n.factorization p))) ≤ (logStar n) := by
    unfold logStar;
    intro p hp;
    split_ifs <;> norm_num at *;
    · intro m hm;
      -- By definition of $iteratedLog$, we know that $iteratedLog m (p ^ (n.factorization p)) \leq iteratedLog m n$.
      have h_iteratedLog_le : iteratedLog m (p ^ (n.factorization p)) ≤ iteratedLog m n := by
        induction' m with m ih;
        · -- Since $p^{n.factorization p}$ is a divisor of $n$, we have $p^{n.factorization p} \leq n$.
          have h_div : (p : ℝ) ^ (n.factorization p) ≤ n := by
            exact_mod_cast Nat.le_of_dvd ( by positivity ) ( Nat.ordProj_dvd _ _ );
          exact h_div;
        · exact Real.log_le_log ( by linarith [ hm m ( by linarith ) ] ) ( ih fun k hk => hm k ( by linarith ) );
      exact lt_of_lt_of_le ( hm m le_rfl ) h_iteratedLog_le;
    · rename_i h₁ h₂;
      contrapose! h₂;
      -- Since $n \geq 2$, we can apply the definition of $logStar$ to find such an $x$.
      have h_log_star : ∃ x, iteratedLog x (n : ℝ) ≤ 1 := by
        have h_seq : ∀ x : ℕ, iteratedLog x (n : ℝ) > 1 → iteratedLog (x + 1) (n : ℝ) < iteratedLog x (n : ℝ) := by
          exact fun x hx => by rw [ show iteratedLog ( x + 1 ) ( n : ℝ ) = Real.log ( iteratedLog x ( n : ℝ ) ) by rfl ] ; exact lt_of_lt_of_le ( Real.log_lt_sub_one_of_pos ( by linarith ) ( by linarith ) ) ( by linarith ) ;
        by_cases h_seq : ∀ x : ℕ, iteratedLog x (n : ℝ) > 1;
        · -- Since the sequence is strictly decreasing and bounded below by 1, it must converge to some limit $L$.
          obtain ⟨L, hL⟩ : ∃ L, Filter.Tendsto (fun x => iteratedLog x (n : ℝ)) Filter.atTop (nhds L) := by
            exact ⟨ _, tendsto_atTop_ciInf ( show Antitone fun x => iteratedLog x ( n : ℝ ) from antitone_nat_of_succ_le fun x => by linarith [ h_seq x, ‹∀ x : ℕ, iteratedLog x ( n : ℝ ) > 1 → iteratedLog ( x + 1 ) ( n : ℝ ) < iteratedLog x ( n : ℝ ) › x ( h_seq x ) ] ) ⟨ 1, Set.forall_mem_range.mpr fun x => le_of_lt ( h_seq x ) ⟩ ⟩;
          -- Taking the limit of both sides of the recurrence relation $iteratedLog (x + 1) (n : ℝ) = Real.log (iteratedLog x (n : ℝ))$, we get $L = Real.log L$.
          have h_lim_eq : L = Real.log L := by
            have h_lim_eq : Filter.Tendsto (fun x => iteratedLog (x + 1) (n : ℝ)) Filter.atTop (nhds (Real.log L)) := by
              convert Filter.Tendsto.log hL _ using 1;
              exact ne_of_gt <| lt_of_lt_of_le zero_lt_one <| le_of_tendsto_of_tendsto' tendsto_const_nhds hL fun x => le_of_lt <| h_seq x;
            rw [ tendsto_nhds_unique h_lim_eq ( hL.comp ( Filter.tendsto_add_atTop_nat 1 ) ) ];
          linarith [ Real.log_le_sub_one_of_pos ( show 0 < L by linarith [ show 0 < L by exact lt_of_lt_of_le zero_lt_one ( le_of_tendsto_of_tendsto' tendsto_const_nhds hL fun x => le_of_lt ( h_seq x ) ) ] ) ];
        · aesop;
      exact h_log_star;
  -- Using the bound $\log^* q_i \leq \log^* n$, we can factor out $\log^* n$ from the sum.
  have h_factor : f n ≤ (logStar n) * ∑ p ∈ n.factorization.support, Real.log (p ^ (n.factorization p)) := by
    rw [ h_def, Finset.mul_sum _ _ _ ];
    exact Finset.sum_le_sum fun p hp => by rw [ mul_comm ] ; exact mul_le_mul_of_nonneg_right ( mod_cast h_bound p hp ) ( Real.log_nonneg <| one_le_pow₀ <| mod_cast Nat.pos_of_mem_primeFactors hp ) ;
  convert h_factor using 2;
  conv_lhs => rw [ ← Nat.factorization_prod_pow_eq_self ( by positivity : n ≠ 0 ) ];
  rw [ ← Real.log_prod ] <;> norm_cast ; aesop

/-
Define a rapidly growing sequence by $E_{0}:=1$ and $E_{j+1}:=e^{E_{j}}$ for $j \geq 0$.
-/
noncomputable def E (j : ℕ) : ℝ :=
  match j with
  | 0 => 1
  | j + 1 => Real.exp (E j)

/-
The sequence $E_j$ is strictly increasing.
-/
lemma E_strictMono : StrictMono E := by
  refine' strictMono_nat_of_lt_succ _;
  intro n;
  -- By definition of $E$, we know that $E (n + 1) = e^{E n}$.
  rw [show E (n + 1) = Real.exp (E n) from rfl];
  linarith [ Real.add_one_le_exp ( E n ) ]

/-
$\log^{(j)}(E_k) = E_{k-j}$ for $j \le k$.
-/
lemma iteratedLog_E {j k : ℕ} (h : j ≤ k) : iteratedLog j (E k) = E (k - j) := by
  -- We prove this by induction on $j$.
  induction' j with j ih;
  · rfl;
  · -- For the inductive step, we know that $\log^{(j+1)}(E_k) = \log(\log^{(j)}(E_k))$.
    have h_log_succ : iteratedLog (j + 1) (E k) = Real.log (iteratedLog j (E k)) := by
      rfl;
    rw [ h_log_succ, ih ( Nat.le_of_succ_le h ) ];
    rw [ show k - j = ( k - ( j + 1 ) ) + 1 by omega, show E ( ( k - ( j + 1 ) ) + 1 ) = Real.exp ( E ( k - ( j + 1 ) ) ) by rfl, Real.log_exp ]

/-
$\log^* x = k \iff E_{k-1} < x \le E_k$ for $k \ge 1$.
-/
lemma logStar_eq_iff {x : ℝ} {k : ℕ} (hk : k ≥ 1) :
    logStar x = k ↔ E (k - 1) < x ∧ x ≤ E k := by
      -- By definition of log-star, we know that $\log^{(j)} x > 1$ for all $j < k$ and $\log^{(k)} x \le 1$.
      have h_log_star_def : logStar x = k ↔ (∀ j < k, iteratedLog j x > 1) ∧ iteratedLog k x ≤ 1 := by
        unfold logStar;
        split_ifs <;> simp_all +decide [ Nat.find_eq_iff ];
        · tauto;
        · exact iff_of_false ( by linarith ) ( by linarith [ ‹∀ x_1 : ℕ, 1 < iteratedLog x_1 x› k ] );
      constructor;
      · intro h;
        -- By definition of $E$, we know that $E (k - 1) < x$ and $x \leq E k$.
        have h_E_lt_x : E (k - 1) < x := by
          have := h_log_star_def.mp h;
          -- By definition of $E$, we know that $E (k - 1) = \exp^{(k - 1)}(1)$.
          have h_E_def : E (k - 1) = Real.exp^[k - 1] 1 := by
            refine' Nat.recOn ( k - 1 ) _ _ <;> simp_all +decide [ Function.iterate_succ_apply' ];
            · rfl;
            · exact fun n hn => by rw [ ← hn ] ; rfl;
          rcases k with ( _ | k ) <;> simp_all +decide
          have h_exp_iter : ∀ j ≤ k, Real.exp^[j] 1 < iteratedLog (k - j) x := by
            intro j hj; induction' j with j ih <;> simp_all +decide [ Function.iterate_succ_apply' ] ;
            specialize ih ( Nat.le_of_succ_le hj );
            rw [ show k - j = ( k - ( j + 1 ) ) + 1 by omega, iteratedLog ] at ih;
            rwa [ Real.lt_log_iff_exp_lt ( by linarith [ this.1 ( k - ( j + 1 ) ) ( by omega ) ] ) ] at ih;
          simpa using h_exp_iter k le_rfl
        have h_x_le_Ek : x ≤ E k := by
          have := h_log_star_def.mp h |>.2;
          contrapose! this;
          -- By definition of $E$, we know that $E k < x$ implies $\log^{(k)} x > 1$.
          have h_log_k_gt_1 : ∀ j ≤ k, iteratedLog j x > E (k - j) := by
            intro j hj;
            induction' j with j ih;
            · exact this;
            · have h_log_k_gt_1 : iteratedLog (j + 1) x = Real.log (iteratedLog j x) := by
                exact rfl;
              rw [ h_log_k_gt_1 ];
              refine' lt_of_le_of_lt _ ( Real.log_lt_log ( _ ) ( ih ( Nat.le_of_succ_le hj ) ) );
              · rw [ show k - j = ( k - ( j + 1 ) ) + 1 by omega, show E ( ( k - ( j + 1 ) ) + 1 ) = Real.exp ( E ( k - ( j + 1 ) ) ) by rfl ] ; norm_num;
              · exact Nat.recOn ( k - j ) ( by norm_num [ show E 0 = 1 from rfl ] ) fun n ihn => by rw [ show E ( n + 1 ) = Real.exp ( E n ) from rfl ] ; positivity;
          specialize h_log_k_gt_1 k ; aesop
        exact ⟨h_E_lt_x, h_x_le_Ek⟩;
      · intro hx
        have h_log_star_def : (∀ j < k, iteratedLog j x > 1) ∧ iteratedLog k x ≤ 1 := by
          have h_log_star_def : ∀ j < k, iteratedLog j x > E (k - j - 1) := by
            intro j hj
            induction' j with j ih;
            · aesop;
            · have h_log_star_def : iteratedLog (j + 1) x = Real.log (iteratedLog j x) := by
                rfl;
              have h_log_star_def : Real.log (iteratedLog j x) > Real.log (E (k - j - 1)) := by
                exact Real.log_lt_log ( by exact show 0 < E ( k - j - 1 ) from Nat.recOn ( k - j - 1 ) ( by norm_num [ show E 0 = 1 from rfl ] ) fun n ihn => by rw [ show E ( n + 1 ) = Real.exp ( E n ) from rfl ] ; positivity ) ( ih ( Nat.lt_of_succ_lt hj ) );
              have h_log_star_def : Real.log (E (k - j - 1)) = E (k - j - 2) := by
                rcases n : k - j with ( _ | _ | n ) <;> simp_all +decide
                · omega;
                · omega;
                · exact Real.log_exp _;
              grind;
          have h_log_star_def : iteratedLog k x ≤ 1 := by
            have h_log_star_def : iteratedLog k x ≤ iteratedLog k (E k) := by
              have h_log_star_def : ∀ j ≤ k, iteratedLog j x ≤ iteratedLog j (E k) := by
                intro j hj
                induction' j with j ih;
                · exact hx.2;
                · have h_log_star_def : Real.log (iteratedLog j x) ≤ Real.log (iteratedLog j (E k)) := by
                    apply Real.log_le_log;
                    · exact lt_of_le_of_lt ( by exact le_of_lt ( show 0 < E ( k - j - 1 ) from Nat.recOn ( k - j - 1 ) ( by norm_num [ show E 0 = 1 from rfl ] ) fun n ihn => by rw [ show E ( n + 1 ) = Real.exp ( E n ) from rfl ] ; positivity ) ) ( h_log_star_def j ( Nat.lt_of_succ_le hj ) );
                    · exact ih ( Nat.le_of_succ_le hj );
                  exact h_log_star_def;
              exact h_log_star_def k le_rfl;
            have h_log_star_def : iteratedLog k (E k) = E 0 := by
              convert iteratedLog_E le_rfl;
              norm_num;
            aesop;
          exact ⟨ fun j hj => lt_of_le_of_lt ( show 1 ≤ E ( k - j - 1 ) from Nat.recOn ( k - j - 1 ) ( by norm_num [ show E 0 = 1 from rfl ] ) fun n ihn => by rw [ show E ( n + 1 ) = Real.exp ( E n ) from rfl ] ; exact Real.one_le_exp ( by linarith ) ) ( by solve_by_elim ), h_log_star_def ⟩;
        aesop

/-
Define the sets $\mathcal{S}$ and $\mathcal{B}$ of prime factors based on the size of their prime powers relative to $E_{k-3}$, and the sum $S_{\mathcal{S}}$ of the logarithms of the prime powers in $\mathcal{S}$.
-/
noncomputable def S_set (n : ℕ) (k : ℕ) : Finset ℕ :=
  n.factorization.support.filter (fun p => (p : ℝ) ^ (n.factorization p) ≤ E (k - 3))

noncomputable def B_set (n : ℕ) (k : ℕ) : Finset ℕ :=
  n.factorization.support.filter (fun p => (p : ℝ) ^ (n.factorization p) > E (k - 3))

noncomputable def sum_S (n : ℕ) (k : ℕ) : ℝ :=
  ∑ p ∈ S_set n k, Real.log ((p : ℝ) ^ (n.factorization p))

/-
$S_{\mathcal{S}} \le E_{k-3} \cdot E_{k-4}$ for $k \ge 6$.
-/
lemma sum_S_bound (n : ℕ) (k : ℕ) (hk : k ≥ 6) :
    sum_S n k ≤ E (k - 3) * E (k - 4) := by
      -- The number of indices in $\mathcal{S}$ is at most the number of primes $p \le E_{k-3}$, hence at most $E_{k-3}$.
      have h_card_S : (S_set n k).card ≤ E (k - 3) := by
        -- Each prime $p$ in $S$ satisfies $p \leq E_{k-3}$, so the number of primes in $S$ is at most the number of integers up to $E_{k-3}$.
        have h_prime_bound : ∀ p ∈ S_set n k, p ≤ E (k - 3) := by
          intro p hp
          have h_prime_bound : (p : ℝ) ^ (n.factorization p) ≤ E (k - 3) := by
            exact Finset.mem_filter.mp hp |>.2;
          refine le_trans ?_ h_prime_bound;
          exact_mod_cast Nat.le_self_pow ( Nat.ne_of_gt ( Nat.pos_of_ne_zero ( Finsupp.mem_support_iff.mp ( Finset.mem_filter.mp hp |>.1 ) ) ) ) _;
        have h_card_bound : (S_set n k).card ≤ Finset.card (Finset.Icc 1 (Nat.floor (E (k - 3)))) := by
          refine Finset.card_le_card ?_;
          exact fun p hp => Finset.mem_Icc.mpr ⟨ Nat.pos_of_ne_zero <| by unfold S_set at hp; aesop, Nat.le_floor <| h_prime_bound p hp ⟩;
        exact le_trans ( Nat.cast_le.mpr h_card_bound ) ( by simpa using Nat.floor_le ( show 0 ≤ E ( k - 3 ) by exact Nat.recOn ( k - 3 ) ( by norm_num [ E ] ) fun n ihn => by rw [ E ] ; positivity ) );
      refine' le_trans ( Finset.sum_le_sum fun p hp => show Real.log ( ( p : ℝ ) ^ ( n.factorization p ) ) ≤ E ( k - 4 ) from _ ) _;
      · -- For $i \in \mathcal{S}$ we have $\log(p^a) \le \log(E_{k-3}) = E_{k-4}$.
        have h_log_S : Real.log ((p : ℝ) ^ (n.factorization p)) ≤ Real.log (E (k - 3)) := by
          exact Real.log_le_log ( mod_cast pow_pos ( Nat.pos_of_mem_primeFactors ( Finset.filter_subset _ _ hp ) ) _ ) ( mod_cast Finset.mem_filter.mp hp |>.2 );
        rcases k with ( _ | _ | _ | _ | k ) <;> simp_all +decide [ E ];
      · simpa [ mul_comm ] using mul_le_mul_of_nonneg_right h_card_S ( show 0 ≤ E ( k - 4 ) by exact Nat.recOn ( k - 4 ) ( by norm_num [ show E 0 = 1 from rfl ] ) fun n ihn => by rw [ show E ( n + 1 ) = Real.exp ( E n ) from rfl ] ; positivity )

/-
If $q > E_{k-3}$, then $\log^* q \ge k-2$.
-/
lemma logStar_lower_bound_B {q : ℝ} {k : ℕ} (hq : q > E (k - 3)) :
    logStar q ≥ k - 2 := by
      -- By Definition~\ref{def:logStar}, $\log^* q < k-2 \implies \log^* q \le k-3$.
      by_contra h_contra
      have h_logStar_le : logStar q ≤ k - 3 := by
        omega;
      -- By Lemma~\ref{lem:logStar_eq_iff}, $q \le E_{\log^* q} \le E_{k-3}$.
      have h_q_le_E : q ≤ E (logStar q) := by
        have h_logStar_eq_iff : ∀ {x : ℝ} {k : ℕ}, k ≥ 1 → logStar x = k → x ≤ E k := by
          intro x k hk hk'; rw [ ← hk' ] ; exact logStar_eq_iff ( by linarith ) |>.1 rfl |>.2;
        apply h_logStar_eq_iff;
        · unfold logStar;
          split_ifs <;> norm_num;
          · exact lt_of_le_of_lt ( show 1 ≤ E ( k - 3 ) from Nat.recOn ( k - 3 ) ( by norm_num [ show E 0 = 1 from rfl ] ) fun n ihn => by rw [ show E ( n + 1 ) = Real.exp ( E n ) from rfl ] ; exact Real.one_le_exp ( by linarith ) ) hq;
          · -- If no such $j$ exists, then $\log^{(j)} q > 1$ for all $j$.
            have h_log_gt_one : ∀ j : ℕ, iteratedLog j q > 1 := by
              aesop;
            -- Since $\log^{(j)} q > 1$ for all $j$, we have $\log^{(j+1)} q = \log(\log^{(j)} q) < \log^{(j)} q$.
            have h_log_decreasing : ∀ j : ℕ, iteratedLog (j + 1) q < iteratedLog j q := by
              exact fun j => by rw [ show iteratedLog ( j + 1 ) q = Real.log ( iteratedLog j q ) by rfl ] ; exact Real.log_lt_iff_lt_exp ( by linarith [ h_log_gt_one j ] ) |>.2 ( by linarith [ h_log_gt_one j, Real.add_one_le_exp ( iteratedLog j q ) ] ) ;
            -- Since $\log^{(j)} q$ is strictly decreasing and bounded below by 1, it must converge to some limit $L$.
            obtain ⟨L, hL⟩ : ∃ L, Filter.Tendsto (fun j => iteratedLog j q) Filter.atTop (nhds L) := by
              exact ⟨ _, tendsto_atTop_ciInf ( show Antitone fun j => iteratedLog j q from antitone_nat_of_succ_le fun j => le_of_lt ( h_log_decreasing j ) ) ⟨ 1, Set.forall_mem_range.mpr fun j => le_of_lt ( h_log_gt_one j ) ⟩ ⟩;
            -- Taking the limit of both sides of $\log^{(j+1)} q = \log(\log^{(j)} q)$, we get $L = \log L$.
            have hL_eq : L = Real.log L := by
              have hL_eq : Filter.Tendsto (fun j => iteratedLog (j + 1) q) Filter.atTop (nhds (Real.log L)) := by
                convert Filter.Tendsto.log hL _ using 1;
                exact ne_of_gt ( lt_of_lt_of_le zero_lt_one ( le_of_tendsto_of_tendsto' tendsto_const_nhds hL fun j => le_of_lt ( h_log_gt_one j ) ) );
              rw [ tendsto_nhds_unique hL_eq ( hL.comp ( Filter.tendsto_add_atTop_nat 1 ) ) ];
            linarith [ Real.log_le_sub_one_of_pos ( show 0 < L by linarith [ show 0 < L by exact lt_of_lt_of_le zero_lt_one ( le_of_tendsto_of_tendsto' tendsto_const_nhds hL fun j => le_of_lt ( h_log_gt_one j ) ) ] ) ];
        · rfl;
      -- Since $E$ is strictly increasing, we have $E (logStar q) \leq E (k - 3)$.
      have h_E_logStar_le_E_k_minus_3 : E (logStar q) ≤ E (k - 3) := by
        exact monotone_nat_of_le_succ ( fun n => by exact le_of_lt ( E_strictMono ( Nat.lt_succ_self n ) ) ) h_logStar_le;
      linarith

/-
For $k \ge 6$, $(k-3) E_{k-3} E_{k-4} \le e^{E_{k-3}}$.
-/
lemma E_growth_inequality (k : ℕ) (hk : k ≥ 6) :
    (k - 3) * E (k - 3) * E (k - 4) ≤ Real.exp (E (k - 3)) := by
      -- Let $x = E_{k-3}$. Then $E_{k-4} = \log x$.
      set x := E (k - 3)
      have hx : E (k - 4) = Real.log x := by
        rcases k with ( _ | _ | _ | _ | k ) <;> simp_all +decide;
        have h_log : E (k + 1) = Real.exp (E k) := by
          exact rfl;
        aesop;
      -- We need to show $(k-3) x \log x \le e^x$.
      -- Since $k \ge 6$, $x = E_{k-3} \ge E_3 = e^{e^e}$.
      have hx_ge_E3 : x ≥ Real.exp (Real.exp (Real.exp 1)) := by
        -- By definition of $E$, we know that $E_{k-3} \ge E_3$ for $k \ge 6$.
        have h_E_ge_E3 : ∀ k ≥ 6, E (k - 3) ≥ E 3 := by
          exact fun k hk => E_strictMono.monotone ( Nat.le_sub_of_add_le hk );
        exact le_trans ( by norm_num [ show E 3 = Real.exp ( Real.exp ( Real.exp 1 ) ) by rfl ] ) ( h_E_ge_E3 k hk );
      -- Since $k \ge 6$, we have $k - 3 \le x$.
      have hk_le_x : (k - 3 : ℝ) ≤ x := by
        -- By definition of $E$, we know that $E_j \ge j$ for all $j$.
        have h_E_ge_j : ∀ j : ℕ, E j ≥ j := by
          intro j;
          induction' j with j ih;
          · norm_num [ show E 0 = 1 by rfl ];
          · rw [ show E ( j + 1 ) = Real.exp ( E j ) by rfl ] ; norm_num ; linarith [ Real.add_one_le_exp ( E j ) ];
        exact le_trans ( by norm_num [ Nat.cast_sub ( show 3 ≤ k by linarith ) ] ) ( h_E_ge_j _ );
      -- We'll use that $e^x \geq x^3$ for $x \geq E_3$.
      have h_exp_ge_x3 : Real.exp x ≥ x^3 := by
        -- We'll use that $e^x \geq x^3$ for $x \geq E_3$. This follows from the fact that the exponential function grows faster than any polynomial function.
        have h_exp_growth : ∀ x ≥ 10, Real.exp x ≥ x^3 := by
          intro x hx; rw [ Real.exp_eq_exp_ℝ ] ; norm_num [ NormedSpace.exp_eq_tsum_div ];
          refine' le_trans _ ( Summable.sum_le_tsum ( Finset.range 10 ) ( fun _ _ => by positivity ) ( by simpa using Real.summable_pow_div_factorial x ) ) ; norm_num [ Finset.sum_range_succ, Nat.factorial ] ; ring_nf ; norm_num;
          nlinarith [ pow_nonneg ( by linarith : 0 ≤ x ) 2, pow_nonneg ( by linarith : 0 ≤ x ) 3, pow_nonneg ( by linarith : 0 ≤ x ) 4, pow_nonneg ( by linarith : 0 ≤ x ) 5, pow_nonneg ( by linarith : 0 ≤ x ) 6, pow_nonneg ( by linarith : 0 ≤ x ) 7, pow_nonneg ( by linarith : 0 ≤ x ) 8 ];
        refine h_exp_growth x ?_;
        refine le_trans ?_ hx_ge_E3;
        rw [ ← Real.log_le_log_iff ( by positivity ) ( by positivity ), Real.log_exp ];
        rw [ show ( 10 : ℝ ) = 2 * 5 by norm_num, Real.log_mul ] <;> norm_num;
        rw [ show ( 5 : ℝ ) = 2 ^ 2 * 1.25 by norm_num, Real.log_mul, Real.log_pow ] <;> norm_num;
        exact le_trans ( add_le_add ( Real.log_two_lt_d9.le ) ( add_le_add ( mul_le_mul_of_nonneg_left ( Real.log_two_lt_d9.le ) zero_le_two ) ( Real.log_le_sub_one_of_pos ( by norm_num ) ) ) ) ( by have := Real.exp_one_gt_d9.le; norm_num1 at *; rw [ show Real.exp ( Real.exp 1 ) = Real.exp 1 * Real.exp ( Real.exp 1 - 1 ) by rw [ ← Real.exp_add, add_sub_cancel ] ] ; nlinarith [ Real.add_one_le_exp ( Real.exp 1 - 1 ) ] );
      -- Since $x \geq E_3$, we have $\log x \leq x$.
      have h_log_x_le_x : Real.log x ≤ x := by
        exact le_trans ( Real.log_le_sub_one_of_pos ( by linarith [ Real.exp_pos ( Real.exp ( Real.exp 1 ) ) ] ) ) ( by linarith );
      exact le_trans ( mul_le_mul_of_nonneg_right ( mul_le_mul_of_nonneg_right hk_le_x <| by linarith [ Real.exp_pos ( Real.exp ( Real.exp 1 ) ) ] ) <| by linarith [ Real.log_nonneg <| show 1 ≤ E ( k - 3 ) from hx_ge_E3.trans' <| Real.one_le_exp <| by positivity ] ) <| by nlinarith [ Real.log_nonneg <| show 1 ≤ E ( k - 3 ) from hx_ge_E3.trans' <| Real.one_le_exp <| by positivity ] ;

/-
If $\log^* n = k \ge 6$, then $S_{\mathcal{S}} \le \frac{\log n}{k-3}$.
-/
lemma sum_S_le_log_n_div_k_minus_3 (n : ℕ) (k : ℕ) (hk : k ≥ 6) (h_logStar : logStar n = k) :
    sum_S n k ≤ Real.log n / (k - 3) := by
      -- Since $\log^* n = k$, we have $n > E_{k-1}$, so $\log n > E_{k-2} = e^{E_{k-3}}$.
      have h_log_n : Real.log n > Real.exp (E (k - 3)) := by
        -- Since $\log^* n = k$, we have $E_{k-1} < n \le E_k$.
        have h_bounds : E (k - 1) < n ∧ n ≤ E k := by
          exact h_logStar ▸ logStar_eq_iff ( by linarith ) |>.1 rfl;
        -- Since $\log^* n = k$, we have $n > E_{k-1}$, so $\log n > E_{k-2} = e^{E_{k-3}}$ by definition of $E$.
        have h_log_n : Real.log n > Real.log (E (k - 1)) := by
          exact Real.log_lt_log ( by exact lt_of_lt_of_le ( by norm_num ) ( show ( E ( k - 1 ) : ℝ ) ≥ 1 by exact Nat.recOn ( k - 1 ) ( by norm_num [ E ] ) fun j ih => by rw [ E ] ; exact Real.one_le_exp ( by linarith ) ) ) h_bounds.1;
        rcases k with ( _ | _ | _ | k ) <;> simp_all +decide
        rw [ show E ( k + 1 + 1 ) = Real.exp ( E ( k + 1 ) ) by rfl, Real.log_exp ] at h_log_n ; aesop;
      have := sum_S_bound n k hk;
      rw [ le_div_iff₀ ] <;> nlinarith [ show ( k : ℝ ) ≥ 6 by norm_cast, E_growth_inequality k hk ]

/-
Define the sum $S_{\mathcal{B}}$ of the logarithms of the prime powers in $\mathcal{B}$.
-/
noncomputable def sum_B (n : ℕ) (k : ℕ) : ℝ :=
  ∑ p ∈ B_set n k, Real.log ((p : ℝ) ^ (n.factorization p))

/-
$f(n)$ splits into sums over $\mathcal{B}$ and $\mathcal{S}$.
-/
lemma f_split (n : ℕ) (k : ℕ) :
    f n = ∑ p ∈ B_set n k, Real.log ((p : ℝ) ^ (n.factorization p)) * logStar ((p : ℝ) ^ (n.factorization p)) +
          ∑ p ∈ S_set n k, Real.log ((p : ℝ) ^ (n.factorization p)) * logStar ((p : ℝ) ^ (n.factorization p)) := by
            rw [ ← Finset.sum_union ];
            · unfold f B_set S_set;
              rcongr x ; by_cases hx : ( x : ℝ ) ^ ( n.factorization x ) > E ( k - 3 ) <;> aesop;
            · exact Finset.disjoint_filter.mpr fun _ _ _ _ => by linarith;

/-
The sum over $\mathcal{B}$ is at least $(k-2) S_{\mathcal{B}}$.
-/
lemma sum_B_lower_bound (n : ℕ) (k : ℕ) :
    ∑ p ∈ B_set n k, Real.log ((p : ℝ) ^ (n.factorization p)) * logStar ((p : ℝ) ^ (n.factorization p)) ≥
    (k - 2 : ℝ) * sum_B n k := by
      -- For each $p \in \mathcal{B}$, we have $p^{v_p(n)} > E_{k-3}$. By `logStar_lower_bound_B`, $\log^*(p^{v_p(n)}) \ge k-2$.
      have h_logStar_B : ∀ p ∈ B_set n k, logStar ((p : ℝ) ^ (n.factorization p)) ≥ k - 2 := by
        intros p hp
        have h_p_gt_E : (p : ℝ) ^ (n.factorization p) > E (k - 3) := by
          exact Finset.mem_filter.mp hp |>.2
        exact logStar_lower_bound_B h_p_gt_E;
      have h_sum_B_lower_bound : ∀ p ∈ B_set n k, Real.log ((p : ℝ) ^ (n.factorization p)) * (logStar ((p : ℝ) ^ (n.factorization p))) ≥ (k - 2) * Real.log ((p : ℝ) ^ (n.factorization p)) := by
        norm_num +zetaDelta at *;
        intro p hp; specialize h_logStar_B p hp; nlinarith [ show ( k : ℝ ) ≤ logStar ( ( p : ℝ ) ^ ( n.factorization p ) ) + 2 by exact_mod_cast h_logStar_B, show ( 0 : ℝ ) ≤ ( n.factorization p : ℝ ) * Real.log p by positivity ] ;
      simpa [ Finset.mul_sum _ _ _, mul_assoc, mul_left_comm, sum_B ] using Finset.sum_le_sum h_sum_B_lower_bound

/-
The sum over $\mathcal{S}$ is at least $S_{\mathcal{S}}$.
-/
lemma sum_S_lower_bound (n : ℕ) (k : ℕ) :
    ∑ p ∈ S_set n k, Real.log ((p : ℝ) ^ (n.factorization p)) * logStar ((p : ℝ) ^ (n.factorization p)) ≥
    sum_S n k := by
      have h_logStar_ge_one : ∀ p ∈ S_set n k, 1 ≤ logStar ((p : ℝ) ^ (n.factorization p)) := by
        intro p hp
        have h_logStar_pos : 0 < logStar ((p : ℝ) ^ (n.factorization p)) := by
          unfold logStar;
          split_ifs <;> norm_num;
          · -- Since $p$ is a prime and $n.factorization p \geq 1$, we have $p \geq 2$ and $n.factorization p \geq 1$, thus $p^{n.factorization p} \geq 2^1 = 2$.
            have h_prime_pow_ge_two : 2 ≤ (p : ℝ) ^ (n.factorization p) := by
              norm_cast;
              by_cases hp_prime : Nat.Prime p;
              · exact one_lt_pow₀ hp_prime.one_lt ( Nat.ne_of_gt ( Nat.pos_of_ne_zero ( Finsupp.mem_support_iff.mp ( Finset.mem_filter.mp hp |>.1 ) ) ) );
              · unfold S_set at hp; aesop;
            exact h_prime_pow_ge_two.trans_lt' ( by norm_num );
          · rename_i h;
            -- By definition of $iteratedLog$, we know that $iteratedLog j (p ^ (n.factorization p))$ tends to $-\infty$ as $j$ tends to infinity.
            have h_iteratedLog_neg_inf : Filter.Tendsto (fun j => iteratedLog j (p ^ (n.factorization p) : ℝ)) Filter.atTop Filter.atBot := by
              have h_iteratedLog_neg_inf : ∀ j : ℕ, iteratedLog (j + 1) (p ^ (n.factorization p) : ℝ) ≤ iteratedLog j (p ^ (n.factorization p) : ℝ) - 1 := by
                intro j;
                exact Real.log_le_sub_one_of_pos ( by linarith [ show 1 < iteratedLog j ( ( p : ℝ ) ^ ( n.factorization p ) ) from lt_of_not_ge fun h' => h ⟨ j, h' ⟩ ] );
              -- By induction, we can show that $iteratedLog j (p ^ (n.factorization p)) \leq iteratedLog 0 (p ^ (n.factorization p)) - j$.
              have h_iteratedLog_le : ∀ j : ℕ, iteratedLog j (p ^ (n.factorization p) : ℝ) ≤ iteratedLog 0 (p ^ (n.factorization p) : ℝ) - j := by
                exact fun j => Nat.recOn j ( by norm_num ) fun j ih => by norm_num; linarith [ h_iteratedLog_neg_inf j ] ;
              exact Filter.tendsto_atTop_atBot.mpr fun x => ⟨ Nat.ceil ( iteratedLog 0 ( p ^ ( n.factorization p ) : ℝ ) - x ), fun j hj => by linarith [ Nat.ceil_le.mp hj, h_iteratedLog_le j ] ⟩;
            exact h <| by have := h_iteratedLog_neg_inf.eventually ( Filter.eventually_le_atBot 1 ) ; obtain ⟨ j, hj ⟩ := this.exists; exact ⟨ j, hj ⟩ ;
        exact h_logStar_pos;
      exact Finset.sum_le_sum fun p hp => le_mul_of_one_le_right ( Real.log_nonneg <| mod_cast Nat.one_le_iff_ne_zero.mpr <| by aesop ) <| mod_cast h_logStar_ge_one p hp

/-
$S_{\mathcal{B}} + S_{\mathcal{S}} = \log n$.
-/
lemma sum_B_add_sum_S (n : ℕ) (k : ℕ) (hn : n ≠ 0) :
    sum_B n k + sum_S n k = Real.log n := by
      unfold sum_B sum_S;
      rw [ ← Finset.sum_union ];
      · rw [ show B_set n k ∪ S_set n k = n.factorization.support from ?_ ];
        · conv_rhs => rw [ ← Nat.factorization_prod_pow_eq_self hn ];
          norm_num [ Finsupp.prod ];
          rw [ Real.log_prod _ _ fun x hx => by aesop, Finset.sum_congr rfl fun x hx => Real.log_pow _ _ ];
        · ext; simp [B_set, S_set];
          exact ⟨ fun h => h.elim ( fun h => h.1 ) fun h => h.1, fun h => if h' : E ( k - 3 ) < ( ↑‹ℕ› : ℝ ) ^ ( n.factorization ‹ℕ› ) then Or.inl ⟨ h, h' ⟩ else Or.inr ⟨ h, le_of_not_gt h' ⟩ ⟩;
      · exact Finset.disjoint_filter.mpr fun _ _ _ _ => by linarith;

/-
For sufficiently large $n$, $\log^* n \ge 6$.
-/
lemma logStar_ge_six_of_large_n : ∃ n₀, ∀ n ≥ n₀, logStar n ≥ 6 := by
  -- By definition of $E$, there exists $n_0$ such that $E_5 < n_0$.
  obtain ⟨n₀, hn₀⟩ : ∃ n₀ : ℝ, E 5 < n₀ := by
    exact NoMaxOrder.exists_gt _;
  use n₀ + 1;
  intro n hn
  have h_logStar_n : E 5 < n ∧ n ≤ E (logStar n) := by
    have h_logStar_n : E (logStar n - 1) < n ∧ n ≤ E (logStar n) := by
      -- By definition of $logStar$, we know that $logStar n$ is the smallest integer $k$ such that $E_{k-1} < n \leq E_k$.
      have h_logStar_def : ∃ k, E (k - 1) < n ∧ n ≤ E k := by
        -- Since $E_j$ is strictly increasing and tends to infinity, there exists $k$ such that $E_k \geq n$.
        obtain ⟨k, hk⟩ : ∃ k : ℕ, E k ≥ n := by
          have h_logStar_def : Filter.Tendsto E Filter.atTop Filter.atTop := by
            refine' Filter.tendsto_atTop_mono _ tendsto_natCast_atTop_atTop;
            intro n;
            induction' n with n ih;
            · norm_num [ show E 0 = 1 by rfl ];
            · exact le_trans ( by norm_num ) ( Real.add_one_le_exp _ ) |> le_trans <| Real.exp_le_exp.mpr ih;
          exact ( h_logStar_def.eventually_ge_atTop n ) |> fun h => h.exists;
        contrapose! hk;
        induction' k with k ih;
        · unfold E; linarith [ show 1 < n₀ from by linarith [ show 1 < E 5 from by exact lt_of_le_of_lt ( by norm_num [ E ] ) ( E_strictMono ( show 5 > 0 by norm_num ) ) ] ] ;
        · exact hk _ ih;
      obtain ⟨k, hk⟩ := h_logStar_def
      have h_logStar_eq : logStar n = k := by
        apply (logStar_eq_iff (by
        contrapose! hk; aesop)).mpr hk
      rw [h_logStar_eq] at *; exact hk;
    exact ⟨ by linarith, h_logStar_n.2 ⟩;
  contrapose! h_logStar_n;
  exact fun _ => lt_of_le_of_lt ( E_strictMono.monotone ( Nat.le_of_lt_succ h_logStar_n ) ) ( by linarith )

/-
$f(n) \ge (k-2)\log n - (k-3)S_{\mathcal{S}}$.
-/
lemma f_lower_bound_intermediate (n : ℕ) (k : ℕ) (hn : n ≠ 0) :
    f n ≥ (k - 2 : ℝ) * Real.log n - (k - 3 : ℝ) * sum_S n k := by
      have := f_split n k;
      have := sum_B_lower_bound n k
      have := sum_S_lower_bound n k; ( have := sum_B_add_sum_S n k hn; ( norm_num at *; nlinarith; ) )

/-
Lemma 3. There exists an absolute constant $n_{0}$ such that for all $n \geq n_{0}$, $f(n) \geq\left(\log ^{*} n-3\right) \log n$.
-/
lemma lemma3 : ∃ n₀, ∀ n ≥ n₀, f n ≥ (logStar n - 3) * Real.log n := by
  -- We have established that for sufficiently large $n$, $k = \log^* n \ge 6$.
  obtain ⟨n₀, hn₀⟩ : ∃ n₀, ∀ n ≥ n₀, logStar n ≥ 6 := by
    exact logStar_ge_six_of_large_n;
  use Nat.ceil n₀ + 1;
  intros n hn
  have h_logStar : logStar n ≥ 6 := by
    exact hn₀ n <| le_of_lt <| Nat.lt_of_ceil_lt hn;
  have := f_lower_bound_intermediate n ( logStar n ) ( by linarith )
  have := sum_S_le_log_n_div_k_minus_3 n ( logStar n ) ( by linarith ) rfl;
  rw [ le_div_iff₀ ] at this <;> nlinarith [ show ( logStar n : ℝ ) ≥ 6 by norm_cast ]

/-
$\log^*(n+1) \le \log^* n + 1$.
-/
lemma logStar_succ_le (n : ℕ) : logStar (n + 1) ≤ logStar n + 1 := by
  -- Let $k = \log^* n$. Then $n \le E_k$.
  set k := logStar n
  have hn_le_Ek : (n : ℝ) ≤ E k := by
    by_cases hk : k = 0;
    · contrapose! hk;
      -- Since $E_0 = 1$ and $n$ is a natural number, $n \geq 1$. Therefore, $\log^* n \geq 1$.
      have h_logStar_pos : 1 ≤ logStar n := by
        refine' Nat.one_le_iff_ne_zero.mpr _;
        intro h; simp_all +decide [ logStar ] ;
        contrapose! h;
        -- Since $n \geq 2$, we can choose $x$ such that $\log^{(x)} n \leq 1$.
        obtain ⟨x, hx⟩ : ∃ x, iteratedLog x (n : ℝ) ≤ 1 := by
          -- We'll use that $n > 1$ to find such an $x$.
          have h_exists_x : ∃ x, iteratedLog x (n : ℝ) ≤ 1 := by
            have h_log_iter : ∀ m : ℕ, iteratedLog m (n : ℝ) > 1 → iteratedLog (m + 1) (n : ℝ) < iteratedLog m (n : ℝ) := by
              exact fun m hm => by rw [ show iteratedLog ( m + 1 ) ( n : ℝ ) = Real.log ( iteratedLog m ( n : ℝ ) ) by rfl ] ; exact lt_of_lt_of_le ( Real.log_lt_sub_one_of_pos ( by linarith ) ( by linarith ) ) ( by linarith ) ;
            by_cases h_exists_x : ∀ m : ℕ, iteratedLog m (n : ℝ) > 1;
            · -- Since the sequence is strictly decreasing and bounded below by 1, it must converge to some limit $L$.
              obtain ⟨L, hL⟩ : ∃ L, Filter.Tendsto (fun m => iteratedLog m (n : ℝ)) Filter.atTop (nhds L) := by
                have h_decreasing : StrictAnti (fun m => iteratedLog m (n : ℝ)) := by
                  exact strictAnti_nat_of_succ_lt fun m => h_log_iter m ( h_exists_x m );
                exact ⟨ _, tendsto_atTop_ciInf h_decreasing.antitone ⟨ 1, Set.forall_mem_range.mpr fun m => le_of_lt ( h_exists_x m ) ⟩ ⟩;
              -- Taking the limit of both sides of the inequality $\log^{(m+1)}(n) < \log^{(m)}(n)$, we get $L \leq \log(L)$.
              have hL_le_logL : L ≤ Real.log L := by
                have hL_le_logL : Filter.Tendsto (fun m => iteratedLog (m + 1) (n : ℝ)) Filter.atTop (nhds (Real.log L)) := by
                  convert Filter.Tendsto.log hL _ using 1;
                  exact ne_of_gt <| lt_of_lt_of_le zero_lt_one <| le_of_tendsto_of_tendsto' tendsto_const_nhds hL fun m => le_of_lt <| h_exists_x m;
                linarith [ tendsto_nhds_unique hL_le_logL ( hL.comp ( Filter.tendsto_add_atTop_nat 1 ) ) ];
              linarith [ Real.log_le_sub_one_of_pos ( show 0 < L by exact lt_of_lt_of_le zero_lt_one ( le_of_tendsto_of_tendsto' tendsto_const_nhds hL fun m => le_of_lt ( h_exists_x m ) ) ) ];
            · aesop;
          exact h_exists_x;
        refine' ⟨ x, hx, _ ⟩ ; rcases n with ( _ | _ | n ) <;> norm_num at *;
        · exact False.elim <| hk.not_le <| by exact Nat.recOn k ( by norm_num [ show E 0 = 1 from rfl ] ) fun n ihn => by rw [ show E ( n + 1 ) = Real.exp ( E n ) from rfl ] ; positivity;
        · exact absurd hk ( not_lt_of_ge <| by exact Nat.recOn k ( by norm_num [ show E 0 = 1 from rfl ] ) fun n ihn => by rw [ show E ( n + 1 ) = Real.exp ( E n ) from rfl ] ; exact Real.one_le_exp <| by positivity );
        · exact lt_add_of_pos_of_le ( by positivity ) ( by norm_num );
      linarith;
    · have := logStar_eq_iff ( show 1 ≤ k from Nat.pos_of_ne_zero hk ) |>.1 rfl; aesop;
  -- Since $n + 1 \le E_k + 1$, we have $\log^*(n + 1) \le k + 1$.
  have h_logStar_n_plus_1 : logStar (n + 1) ≤ k + 1 := by
    have h_logStar_n_plus_1_le : (n + 1 : ℝ) ≤ E (k + 1) := by
      exact le_trans ( add_le_add_right hn_le_Ek 1 ) ( by rw [ show E ( k + 1 ) = Real.exp ( E k ) by rfl ] ; linarith [ Real.add_one_le_exp ( E k ) ] )
    contrapose! h_logStar_n_plus_1_le;
    -- Since $\log^*(n+1) > k + 1$, we have $E_{k+1} < n+1$.
    have h_E_k_plus_1_lt_n_plus_1 : E (logStar (n + 1) - 1) < n + 1 := by
      apply (logStar_eq_iff (by linarith)).mp (by
      rfl) |>.1;
    exact lt_of_le_of_lt ( E_strictMono.monotone ( Nat.le_pred_of_lt h_logStar_n_plus_1_le ) ) h_E_k_plus_1_lt_n_plus_1;
  exact h_logStar_n_plus_1

/-
$\lim_{k \to \infty} \frac{k}{E_{k-2}} = 0$.
-/
lemma limit_k_div_E_k_minus_2 : Filter.Tendsto (fun k : ℕ => (k : ℝ) / E (k - 2)) Filter.atTop (nhds 0) := by
  -- For $k \ge 4$, $E_{k-2} \ge 2^{k-2}$.
  have h_E_ge_pow : ∀ k ≥ 4, (E (k - 2)) ≥ 2 ^ (k - 2) := by
    intro k hk;
    induction' k - 2 with k hk ih <;> norm_num [ pow_succ', E ] at *;
    rw [ ← Real.rpow_one 2, Real.rpow_def_of_pos ] <;> norm_num;
    rw [ ← Real.exp_nat_mul, ← Real.exp_add ];
    exact Real.exp_le_exp.mpr ( by have := Real.log_two_lt_d9; norm_num1 at *; nlinarith [ Real.log_nonneg one_le_two, show ( 2:ℝ ) ^ k ≥ ↑k + 1 by exact mod_cast Nat.recOn k ( by norm_num ) fun n ihn => by rw [ pow_succ' ] ; nlinarith [ Real.log_nonneg one_le_two ] ] );
  refine' squeeze_zero_norm' _ _;
  use fun n => ( n : ℝ ) / 2 ^ ( n - 2 );
  · filter_upwards [ Filter.eventually_ge_atTop 4 ] with n hn using by rw [ Real.norm_of_nonneg ( by exact div_nonneg ( Nat.cast_nonneg _ ) ( by exact le_trans ( by positivity ) ( h_E_ge_pow n hn ) ) ) ] ; exact div_le_div_of_nonneg_left ( by positivity ) ( by positivity ) ( h_E_ge_pow n hn ) ;
  · rw [ ← Filter.tendsto_add_atTop_iff_nat 2 ] ; norm_num;
    refine' squeeze_zero_norm' _ tendsto_inverse_atTop_nhds_zero_nat ; norm_num;
    exact ⟨ 8, fun n hn => by rw [ inv_eq_one_div, div_le_div_iff₀ ] <;> norm_cast <;> induction hn <;> norm_num [ Nat.pow_succ ] at * ; nlinarith ⟩

/-
For sufficiently large $n$, $\frac{f(n+1)-f(n)}{\log n} \leq 4 + \frac{\log^* n + 1}{\log n}$.
-/
lemma helper_inequality : ∃ N, ∀ n ≥ N, (f (n + 1) - f n) / Real.log n ≤ 4 + (logStar n + 1) / Real.log n := by
  -- For large $n$, we have $f(n+1) \le (\log^* n + 1)(\log n + 1)$ by Lemma 2.
  have h_f_succ_le : ∃ N, ∀ n ≥ N, f (n + 1) ≤ (logStar n + 1) * (Real.log n + 1) := by
    -- For large $n$, we have $f(n+1) \le (\log^* (n+1)) \log(n+1)$ by Lemma 2.
    have h_f_succ_le : ∃ N, ∀ n ≥ N, f (n + 1) ≤ (logStar (n + 1)) * Real.log (n + 1) := by
      exact ⟨ 1, fun n hn => by simpa using lemma2 ( n + 1 ) ( by linarith ) ⟩;
    -- Using the fact that $\log^*(n+1) \le \log^* n + 1$ and $\log(n+1) \le \log n + 1$, we can bound $f(n+1)$.
    obtain ⟨N, hN⟩ := h_f_succ_le
    use N
    intro n hn
    have h_log_star : logStar (n + 1) ≤ logStar n + 1 := by
      convert logStar_succ_le n using 1
    have h_log : Real.log (n + 1) ≤ Real.log n + 1 := by
      rcases eq_or_ne n 0 with rfl | hn' <;> simp_all +decide
      rw [ Real.log_le_iff_le_exp, Real.exp_add, Real.exp_log ] <;> first | positivity | nlinarith [ Real.add_one_le_exp 1, show ( n : ℝ ) ≥ 1 by exact Nat.one_le_cast.mpr ( Nat.pos_of_ne_zero hn' ) ] ;
    have h_bound : f (n + 1) ≤ (logStar n + 1) * (Real.log n + 1) := by
      exact le_trans ( hN n hn ) ( mul_le_mul ( mod_cast h_log_star ) h_log ( Real.log_nonneg ( by linarith ) ) ( by positivity ) )
    exact h_bound;
  -- Also, $f(n) \ge (\log^* n - 3) \log n$ by Lemma 3.
  have h_f_ge : ∃ N, ∀ n ≥ N, f n ≥ (logStar n - 3) * Real.log n := by
    have := lemma3; aesop;
  obtain ⟨ N₁, hN₁ ⟩ := h_f_succ_le; obtain ⟨ N₂, hN₂ ⟩ := h_f_ge; use Max.max N₁ N₂ + 2; intro n hn; rw [ div_le_iff₀ ] <;> nlinarith [ hN₁ n ( by linarith [ le_max_left N₁ N₂ ] ), hN₂ n ( by linarith [ le_max_right N₁ N₂ ] ), Real.log_pos <| show ( n :ℝ ) > 1 by norm_cast; linarith [ le_max_left N₁ N₂, le_max_right N₁ N₂ ], mul_div_cancel₀ ( ( logStar n :ℝ ) + 1 ) <| ne_of_gt <| Real.log_pos <| show ( n :ℝ ) > 1 by norm_cast; linarith [ le_max_left N₁ N₂, le_max_right N₁ N₂ ] ] ;

/-
If $\log^* n \ge 2$, then $\log n > E_{\log^* n - 2}$.
-/
lemma log_n_lower_bound (n : ℕ) (h : logStar n ≥ 2) : Real.log n > E (logStar n - 2) := by
  -- By Lemma~\ref{lem:logStar_eq_iff}, $E_{k-1} < n$.
  have h_E_lt_n : E (logStar n - 1) < n := by
    have := logStar_eq_iff ( by linarith : 1 ≤ logStar n ) |>.1 rfl; aesop;
  -- Since $k-1 \ge 1$, $E_{k-1} = \exp(E_{k-2})$.
  have h_E_exp : E (logStar n - 1) = Real.exp (E (logStar n - 2)) := by
    rcases k : logStar n with ( _ | _ | k ) <;> aesop;
  simpa [ h_E_exp ] using Real.log_lt_log ( by exact h_E_exp.symm ▸ Real.exp_pos _ ) h_E_lt_n

/-
If $n > E_k$, then $\log^* n > k$.
-/
lemma logStar_gt_of_gt_E (k : ℕ) (n : ℕ) (h : (n : ℝ) > E k) : logStar n > k := by
  -- Suppose for contradiction that $\log^* n \le k$.
  by_contra h_contra
  have h_le : logStar n ≤ k := by
    exact le_of_not_gt h_contra;
  -- Then $n \le E_{\log^* n} \le E_k$ because $E$ is increasing.
  have h_le_E : (n : ℝ) ≤ E (logStar n) := by
    have h_le_E : ∀ x : ℝ, x > 1 → x ≤ E (logStar x) := by
      intros x hx
      obtain ⟨k, hk⟩ : ∃ k, logStar x = k ∧ E (k - 1) < x ∧ x ≤ E k := by
        have h_logStar_def : ∃ k, E (k - 1) < x ∧ x ≤ E k := by
          have h_logStar_def : ∃ k, x ≤ E k := by
            have h_unbounded : ∀ M : ℝ, ∃ k, E k > M := by
              intro M;
              induction' exists_nat_gt M with k hk;
              use k + 1;
              refine' lt_of_lt_of_le hk _;
              field_simp;
              induction' k with k ih;
              · norm_num [ show E 1 = Real.exp 1 by rfl ];
                positivity;
              · induction' k + 1 with k ih <;> norm_num [ *, Nat.cast_succ ] at *;
                · exact Real.exp_nonneg _;
                · exact le_trans ( add_le_add_right ih 1 ) ( by linarith! [ Real.add_one_le_exp ( E ( k + 1 ) ) ] );
            exact Exists.elim ( h_unbounded x ) fun k hk => ⟨ k, le_of_lt hk ⟩;
          contrapose! h_logStar_def;
          intro k; induction k <;> aesop;
        obtain ⟨ k, hk₁, hk₂ ⟩ := h_logStar_def;
        exact ⟨ k, logStar_eq_iff ( show k ≥ 1 from Nat.pos_of_ne_zero ( by rintro rfl; norm_num at hk₁; linarith ) ) |>.2 ⟨ hk₁, hk₂ ⟩, hk₁, hk₂ ⟩;
      aesop;
    rcases n with ( _ | _ | n ) <;> norm_num at *;
    · exact False.elim <| h.not_le <| by exact Nat.recOn k ( by norm_num [ show E 0 = 1 by rfl ] ) fun n ihn => by rw [ show E ( n + 1 ) = Real.exp ( E n ) by rfl ] ; positivity;
    · exact absurd h ( not_lt_of_ge ( show 1 ≤ E k from Nat.recOn k ( by norm_num [ show E 0 = 1 from rfl ] ) fun n ihn => by rw [ show E ( n + 1 ) = Real.exp ( E n ) from rfl ] ; exact Real.one_le_exp ( by linarith ) ) );
    · exact h_le_E _ ( by linarith );
  exact h.not_le ( h_le_E.trans <| by exact monotone_nat_of_le_succ ( fun k => by simpa using Real.exp_le_exp.mpr <| show E k ≤ E ( k + 1 ) from by simpa using Real.add_one_le_exp ( E k ) |> le_trans ( by norm_num ) ) h_le )

/-
$\log^* n \to \infty$ as $n \to \infty$.
-/
lemma logStar_tendsto_atTop : Filter.Tendsto (fun n : ℕ => logStar n) Filter.atTop Filter.atTop := by
  refine' Filter.tendsto_atTop_atTop.mpr _;
  intro k; use ⌊E k⌋₊ + 1; intro n hn; exact (by
  have := logStar_gt_of_gt_E k n ( Nat.lt_of_floor_lt hn );
  linarith);

/-
The limit of $\frac{k+1}{E_{k-2}}$ as $k \to \infty$ is 0.
-/
lemma limit_k_plus_one_div_E_k_minus_2 : Filter.Tendsto (fun k : ℕ => (k + 1 : ℝ) / E (k - 2)) Filter.atTop (nhds 0) := by
  have := @limit_k_div_E_k_minus_2;
  convert this.add ( show Filter.Tendsto ( fun k : ℕ => ( 1 : ℝ ) / E ( k - 2 ) ) Filter.atTop ( nhds 0 ) from tendsto_const_nhds.div_atTop <| ?_ ) using 2 <;> ring_nf;
  refine' Filter.tendsto_atTop_atTop.mpr _;
  -- We'll use that $E_k$ grows faster than any exponential function.
  have h_exp_growth : ∀ k, E k ≥ k := by
    intro k; induction' k with k ih <;> norm_num [ * ];
    · exact zero_le_one;
    · exact le_trans ( by linarith ) ( Real.add_one_le_exp _ ) |> le_trans <| Real.exp_le_exp.mpr ih;
  exact fun x => ⟨ ⌈x⌉₊ + 2, fun n hn => le_trans ( Nat.le_ceil _ ) ( by exact le_trans ( mod_cast by omega ) ( h_exp_growth _ ) ) ⟩

/-
The limit of $\frac{\log^* n + 1}{\log n}$ as $n \to \infty$ is 0.
-/
lemma limit_logStar_div_log : Filter.Tendsto (fun n : ℕ => (logStar n + 1 : ℝ) / Real.log n) Filter.atTop (nhds 0) := by
  have h_upper_bound : ∀ᶠ n : ℕ in Filter.atTop, (logStar n + 1) / Real.log n ≤ (logStar n + 1) / E (logStar n - 2) := by
    -- For large $n$, $\log^* n \ge 2$, so $\log n > E_{\log^* n - 2}$.
    have h_log_n_lower_bound : ∀ᶠ n : ℕ in Filter.atTop, 2 ≤ logStar n := by
      have := logStar_tendsto_atTop; have := this.eventually_ge_atTop 2; aesop;
    filter_upwards [ h_log_n_lower_bound ] with n hn using div_le_div_of_nonneg_left ( by positivity ) ( by exact show 0 < E ( logStar n - 2 ) from Nat.recOn ( logStar n - 2 ) ( by norm_num [ E ] ) fun n ihn => by rw [ show E ( n + 1 ) = Real.exp ( E n ) from rfl ] ; positivity ) ( by linarith [ log_n_lower_bound n hn ] );
  -- Since $\frac{k+1}{E_{k-2}} \to 0$ as $k \to \infty$, the composition tends to 0.
  have h_comp : Filter.Tendsto (fun k : ℕ => (k + 1 : ℝ) / E (k - 2)) Filter.atTop (nhds 0) := by
    exact limit_k_plus_one_div_E_k_minus_2;
  refine' squeeze_zero_norm' _ ( h_comp.comp _ );
  norm_num +zetaDelta at *;
  exact ⟨ h_upper_bound.choose, fun n hn => by rw [ abs_of_nonneg ( by positivity ), abs_of_nonneg ( Real.log_natCast_nonneg _ ) ] ; exact h_upper_bound.choose_spec n hn ⟩;
  exact logStar_tendsto_atTop

/-
The sequence 4 + (logStar n + 1)/log n tends to 4 in EReal.
-/
lemma limit_helper_RHS : Filter.Tendsto (fun n : ℕ => ((4 : ℝ) + (logStar n + 1) / Real.log n : EReal)) Filter.atTop (nhds 4) := by
  have h_cont : Filter.Tendsto (fun n : ℕ => (logStar n + 1) / Real.log n : ℕ → ℝ) Filter.atTop (nhds 0) := by
    exact limit_logStar_div_log;
  convert tendsto_const_nhds.add h_cont using 2 ; norm_num;
  erw [ ← EReal.tendsto_coe ] ; norm_num;
  convert Iff.rfl

/-
The limit superior of (f(n+1)-f(n))/log(n) is at most 4 (in EReal).
-/
lemma corollary1 : Filter.limsup (fun n : ℕ => ((f (n + 1) - f n) / Real.log n : EReal)) Filter.atTop ≤ 4 := by
  -- Let `u n = (f (n + 1) - f n) / Real.log n` and `v n = 4 + (logStar n + 1) / Real.log n`.
  set u : ℕ → ℝ := fun n => ((f (n + 1) - f n) / Real.log n : ℝ)
  set v : ℕ → ℝ := fun n => (4 : ℝ) + (logStar n + 1) / Real.log n;
  -- By `helper_inequality`, `u n ≤ v n` eventually.
  have h_u_le_v : ∀ᶠ n in Filter.atTop, u n ≤ v n := by
    have := helper_inequality; aesop;
  -- By `limit_helper_RHS`, `v n` tends to 4 in `EReal`.
  have h_v_tendsto : Filter.Tendsto (fun n => (v n : EReal)) Filter.atTop (nhds 4) := by
    convert limit_helper_RHS using 1;
  -- By `lemma helper_inequality`, `u n ≤ v n` eventually.
  have h_u_le_v_eventually : ∀ᶠ n in Filter.atTop, (u n : EReal) ≤ (v n : EReal) := by
    convert h_u_le_v using 1;
    norm_num [ ← EReal.coe_le_coe_iff ];
  have h_limsup_le : Filter.limsup (fun n => (u n : EReal)) Filter.atTop ≤ Filter.limsup (fun n => (v n : EReal)) Filter.atTop := by
    apply_rules [ Filter.limsup_le_limsup ];
    · refine' ⟨ ⊥, _ ⟩ ; aesop;
    · exact Filter.Tendsto.isBoundedUnder_le h_v_tendsto;
  convert h_limsup_le.trans _;
  rw [ h_v_tendsto.limsup_eq ]

/-
For sufficiently large $n$, $f(n) > 0$.
-/
lemma f_pos_eventually : ∀ᶠ n in Filter.atTop, f n > 0 := by
  -- By Lemma 3, there exists an $n₀$ such that for all $n ≥ n₀$, $f(n) ≥ (\log^* n - 3) \log n$.
  obtain ⟨n₀, hn₀⟩ : ∃ n₀, ∀ n ≥ n₀, f n ≥ (logStar n - 3) * Real.log n := by
    exact lemma3;
  have h_logStar_growth : ∀ᶠ n : ℕ in Filter.atTop, logStar n > 3 := by
    have := logStar_tendsto_atTop.eventually_gt_atTop 3; aesop;
  filter_upwards [ h_logStar_growth, Filter.eventually_ge_atTop n₀, Filter.eventually_gt_atTop 1 ] with n hn hn' hn'' using lt_of_lt_of_le ( mul_pos ( sub_pos.mpr <| Nat.cast_lt.mpr hn ) <| Real.log_pos <| Nat.one_lt_cast.mpr hn'' ) <| hn₀ n hn'

/-
The sequence $\frac{f(n+1)}{f(n)}$ is eventually bounded.
-/
lemma ratio_bounded : Filter.IsBoundedUnder (· ≤ ·) Filter.atTop (fun n => f (n + 1) / f n) := by
  have h_eventually_le : ∀ᶠ n in Filter.atTop, f (n + 1) / f n ≤ 1 + (4 + (logStar n + 1) / Real.log n) / (logStar n - 3) := by
    -- Using the inequality from `helper_inequality`, we can show that $f(n+1)/f(n) \leq 1 + (4 + (\log^* n + 1)/\log n)/(\log^* n - 3)$ eventually.
    have h_eventually_le : ∀ᶠ n in Filter.atTop, f (n + 1) - f n ≤ (4 + (logStar n + 1) / Real.log n) * Real.log n ∧ f n ≥ (logStar n - 3) * Real.log n := by
      -- Using the inequality from `helper_inequality`, we can show that $f(n+1) - f(n) \leq (4 + (\log^* n + 1)/\log n) \cdot \log n$ eventually.
      have h_eventually_le : ∀ᶠ n in Filter.atTop, f (n + 1) - f n ≤ (4 + (logStar n + 1) / Real.log n) * Real.log n := by
        have h_eventually_le : ∀ᶠ n in Filter.atTop, (f (n + 1) - f n) / Real.log n ≤ 4 + (logStar n + 1) / Real.log n := by
          have := helper_inequality;
          aesop;
        filter_upwards [ h_eventually_le, Filter.eventually_gt_atTop 1 ] with n hn hn' using by rw [ ← div_le_iff₀ ( Real.log_pos <| Nat.one_lt_cast.mpr hn' ) ] ; exact hn;
      -- Using the inequality from `lemma3`, we can show that $f(n) \geq (\log^* n - 3) \cdot \log n$ eventually.
      have h_eventually_ge : ∀ᶠ n in Filter.atTop, f n ≥ (logStar n - 3) * Real.log n := by
        have := lemma3;
        exact Filter.eventually_atTop.mpr ⟨ this.choose, fun n hn => this.choose_spec n hn ⟩;
      exact h_eventually_le.and h_eventually_ge;
    have h_eventually_le : ∀ᶠ n in Filter.atTop, f n > 0 ∧ (logStar n : ℝ) > 3 := by
      have h_eventually_le : Filter.Tendsto (fun n : ℕ => logStar n) Filter.atTop Filter.atTop := by
        apply_rules [ logStar_tendsto_atTop ];
      filter_upwards [ h_eventually_le.eventually_gt_atTop 3, f_pos_eventually ] with n hn hn' using ⟨ hn', mod_cast hn ⟩;
    filter_upwards [ h_eventually_le, ‹∀ᶠ n in Filter.atTop, f ( n + 1 ) - f n ≤ ( 4 + ( logStar n + 1 ) / Real.log n ) * Real.log n ∧ f n ≥ ( logStar n - 3 ) * Real.log n› ] with n hn hn' ; rw [ div_le_iff₀ ];
    · rw [ add_mul, div_mul_eq_mul_div, add_comm ];
      rw [ add_div', le_div_iff₀ ] <;> try linarith;
      rw [ add_comm 1 n ] ; nlinarith [ show ( 0 :ℝ ) ≤ ( 4 + ( logStar n + 1 ) / Real.log n ) by exact add_nonneg zero_le_four <| div_nonneg ( by linarith ) <| Real.log_natCast_nonneg _ ];
    · linarith;
  -- The term $(4 + (logStar n + 1) / Real.log n) / (logStar n - 3)$ tends to $0$ as $n$ tends to infinity.
  have h_term_zero : Filter.Tendsto (fun n : ℕ => (4 + (logStar n + 1) / Real.log n) / (logStar n - 3)) Filter.atTop (nhds 0) := by
    have h_term_zero : Filter.Tendsto (fun n : ℕ => (logStar n + 1) / Real.log n) Filter.atTop (nhds 0) := by
      convert limit_logStar_div_log using 1;
    convert Filter.Tendsto.div_atTop ( tendsto_const_nhds.add h_term_zero ) _ using 1;
    exact Filter.tendsto_atTop_add_const_right _ _ <| tendsto_natCast_atTop_atTop.comp <| Filter.tendsto_atTop_atTop.mpr fun x => by rcases Filter.eventually_atTop.mp ( logStar_tendsto_atTop.eventually_ge_atTop x ) with ⟨ N, hN ⟩ ; exact ⟨ N, fun n hn => hN n hn ⟩ ;
  have := h_term_zero.const_add 1;
  exact ⟨ _, Filter.eventually_atTop.mpr ⟨ Classical.choose ( Filter.eventually_atTop.mp h_eventually_le ), fun n hn => le_trans ( Classical.choose_spec ( Filter.eventually_atTop.mp h_eventually_le ) n hn ) ( le_ciSup ( this.bddAbove_range ) _ ) ⟩ ⟩

/-!
# Erdős Problem 897

*Reference:* [erdosproblems.com/897](https://www.erdosproblems.com/897)
-/

lemma f_hypothesis : ((Filter.atTop ⊓ Filter.principal {(p, k) : ℕ × ℕ | p.Prime}).limsup (fun (p, k) => (f (p^k) / (p^k : ℝ).log : EReal)) = ⊤) := by
  -- By definition of $f$, we know that $f(p^k) / \log(p^k) = \log^* (p^k)$.
  have h_eq : ∀ p k : ℕ, Nat.Prime p → k ≥ 1 → (f (p ^ k) : ℝ) / Real.log ((p : ℝ) ^ k) = logStar ((p : ℝ) ^ k) := by
    convert lemma1 using 1;
    norm_cast;
  -- Since $\log^*$ tends to infinity, the limit superior of $\log^* (p^k)$ as $p$ and $k$ tend to infinity is also infinity.
  have h_logStar_inf : Filter.Tendsto (fun p : ℕ × ℕ => logStar ((p.1 : ℝ) ^ p.2)) (Filter.atTop ⊓ Filter.principal {(p, k) : ℕ × ℕ | Nat.Prime p}) Filter.atTop := by
    refine' Filter.tendsto_atTop.mpr _;
    intro b;
    -- Since $\log^*$ tends to infinity, for any $b$, there exists $N$ such that for all $n \geq N$, $\log^* n \geq b$.
    obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ n ≥ N, logStar n ≥ b := by
      exact Filter.eventually_atTop.mp ( logStar_tendsto_atTop.eventually_ge_atTop b ) |> fun ⟨ N, hN ⟩ => ⟨ N, fun n hn => hN n hn ⟩;
    rw [ Filter.eventually_inf_principal ];
    rw [ Filter.eventually_atTop ];
    use ( N + 1, 1 );
    intro p hp hp_prime; specialize hN ( p.1 ^ p.2 ) ( by linarith [ show p.1 ^ p.2 ≥ N + 1 from Nat.succ_le_of_lt ( lt_of_lt_of_le ( Nat.lt_of_succ_le hp.1 ) ( Nat.le_self_pow ( by linarith [ hp.2 ] ) _ ) ) ] ) ; aesop;
  have h_limsup_inf : Filter.Tendsto (fun p : ℕ × ℕ => (logStar ((p.1 : ℝ) ^ p.2) : EReal)) (Filter.atTop ⊓ Filter.principal {(p, k) : ℕ × ℕ | Nat.Prime p}) (nhds ⊤) := by
    rw [ Filter.tendsto_atTop ] at *;
    rw [ EReal.tendsto_nhds_top_iff_real ];
    intro x; specialize h_logStar_inf ( ⌈x⌉₊ + 1 ) ; filter_upwards [ h_logStar_inf ] with a ha; exact EReal.coe_lt_coe_iff.mpr ( lt_of_le_of_lt ( Nat.le_ceil _ ) ( mod_cast ha ) ) ;
  convert h_limsup_inf.limsup_eq using 1;
  · refine' Filter.limsup_congr _;
    rw [ Filter.eventually_inf_principal ];
    rw [ Filter.eventually_atTop ];
    use (2, 1);
    intro p hp hp'; specialize h_eq p.1 p.2 hp'.out ( Nat.pos_of_ne_zero ( by aesop ) ) ; norm_cast at *;
    convert congr_arg ( ( ↑ ) : ℝ → EReal ) h_eq using 1;
  · refine' Filter.neBot_iff.mpr _;
    norm_num [ Filter.inf_principal_eq_bot ];
    exact fun n m => by rcases Nat.exists_infinite_primes ( n + m + 1 ) with ⟨ p, hp₁, hp₂ ⟩ ; exact ⟨ p, by linarith, ⟨ m, by linarith ⟩, hp₂ ⟩ ;

lemma f_additive {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) (h : a.Coprime b) : f (a * b) = f a + f b := by
  unfold f;
  simp_all +decide [ Nat.factorization_mul ];
  -- Since $a$ and $b$ are coprime, their prime factors are disjoint.
  have h_disjoint : Disjoint (a.primeFactors) (b.primeFactors) := by
    exact h.disjoint_primeFactors;
  rw [ show ( a.factorization + b.factorization ).support = a.primeFactors ∪ b.primeFactors from ?_, Finset.sum_union h_disjoint ];
  · congr! 1;
    · exact Finset.sum_congr rfl fun p hp => by rw [ Nat.factorization_eq_zero_of_not_dvd ( fun h => Finset.disjoint_left.mp h_disjoint hp <| Nat.mem_primeFactors.mpr ⟨ Nat.prime_of_mem_primeFactors hp, h, by aesop ⟩ ) ] ; ring_nf;
    · exact Finset.sum_congr rfl fun p hp => by rw [ Nat.factorization_eq_zero_of_not_dvd ( fun h => Finset.disjoint_left.mp h_disjoint ( Nat.mem_primeFactors.mpr ⟨ Nat.prime_of_mem_primeFactors hp, h, by aesop ⟩ ) hp ) ] ; ring_nf;
  · rw [ Finsupp.support_add_eq ] <;> aesop

set_option maxHeartbeats 0 in
lemma f_limsup_condition : ((Filter.atTop ⊓ Filter.principal {(p, k) : ℕ × ℕ | p.Prime}).limsup
      (fun (p, k) => (f (p^k) / (p^k : ℝ).log : EReal)) = ⊤) := by
        -- By definition of $f$, we know that $f(p^k) = \log(p^k) \cdot \log^*(p^k)$.
        have h_def : ∀ p k : ℕ, Nat.Prime p → k ≥ 1 → (f (p ^ k) : EReal) / (Real.log ((p : ℝ) ^ k)) = (logStar (p ^ k) : EReal) := by
          intros p k hp hk
          have h_f_div_log : f (p ^ k) / Real.log (p ^ k) = logStar (p ^ k) := by
            have := lemma1 p k hp hk; aesop;
          generalize_proofs at *;
          -- Since the division in the real numbers corresponds to the division in the EReal numbers, we can conclude the proof.
          convert h_f_div_log using 1
          generalize_proofs at *;
          norm_num [ ← EReal.coe_div, ← EReal.coe_mul ];
          norm_cast;
        -- Since $\log^*(p^k)$ tends to infinity as $(p, k)$ tends to infinity in the filter, the limit superior is also infinity.
        have h_logStar_inf : Filter.Tendsto (fun (x : ℕ × ℕ) => logStar (x.1 ^ x.2) : ℕ × ℕ → ℝ) (Filter.atTop ⊓ Filter.principal {(p, k) : ℕ × ℕ | Nat.Prime p}) Filter.atTop := by
          -- Since $p$ and $k$ are both going to infinity, their product $p^k$ will also go to infinity.
          have h_prod_inf : Filter.Tendsto (fun (x : ℕ × ℕ) => (x.1 : ℝ) ^ x.2) (Filter.atTop ⊓ Filter.principal {(p, k) : ℕ × ℕ | Nat.Prime p}) Filter.atTop := by
            rw [ Filter.tendsto_atTop ];
            norm_num [ Filter.eventually_inf_principal ];
            exact fun x => ⟨ ⌈x⌉₊ + 1, 1, fun p q hp hq hp' => le_trans ( Nat.le_ceil _ ) ( by norm_cast; nlinarith [ Nat.Prime.one_lt hp', Nat.pow_le_pow_right hp'.pos hq ] ) ⟩;
          have h_logStar_inf : Filter.Tendsto (fun (x : ℕ) => logStar x : ℕ → ℝ) Filter.atTop Filter.atTop := by
            exact tendsto_natCast_atTop_atTop.comp ( logStar_tendsto_atTop );
          convert h_logStar_inf.comp ( show Filter.Tendsto ( fun x : ℕ × ℕ => Nat.floor ( ( x.1 : ℝ ) ^ x.2 ) ) ( Filter.atTop ⊓ Filter.principal { ( p, k ) : ℕ × ℕ | Nat.Prime p } ) Filter.atTop from ?_ ) using 2;
          · norm_num [ Nat.floor_eq_iff, Real.rpow_nonneg ];
            rw [ show ⌊ ( _:ℝ ) ^ _⌋₊ = ( _:ℕ ) ^ _ from mod_cast Nat.floor_natCast _ ];
            norm_cast;
          · exact tendsto_nat_floor_atTop.comp h_prod_inf;
        -- Since these two functions are equal for sufficiently large $(p, k)$, their limit superiors are also equal.
        have h_eq : Filter.Tendsto (fun (x : ℕ × ℕ) => (f (x.1 ^ x.2) : EReal) / (Real.log ((x.1 : ℝ) ^ x.2))) (Filter.atTop ⊓ Filter.principal {(p, k) : ℕ × ℕ | Nat.Prime p}) (nhds ⊤) := by
          have h_eq : Filter.Tendsto (fun (x : ℕ × ℕ) => (logStar (x.1 ^ x.2) : EReal)) (Filter.atTop ⊓ Filter.principal {(p, k) : ℕ × ℕ | Nat.Prime p}) (nhds ⊤) := by
            norm_num +zetaDelta at *;
            rw [ EReal.tendsto_nhds_top_iff_real ];
            intro x; filter_upwards [ h_logStar_inf.eventually_gt_atTop x ] with y hy; exact_mod_cast hy;
          refine' h_eq.congr' _;
          rw [ Filter.EventuallyEq, Filter.eventually_inf_principal ];
          filter_upwards [ Filter.eventually_ge_atTop ( 1, 1 ) ] with x hx hx' using Eq.symm ( h_def x.1 x.2 hx' ( Nat.one_le_iff_ne_zero.mpr <| by aesop ) );
        convert h_eq.limsup_eq using 1;
        refine' Filter.neBot_iff.mpr _;
        norm_num [ Filter.inf_principal_eq_bot ];
        exact fun n m => by rcases Nat.exists_infinite_primes ( n + m + 1 ) with ⟨ p, hp₁, hp₂ ⟩ ; exact ⟨ p, by linarith, ⟨ m, by linarith ⟩, hp₂ ⟩ ;

/-
Let $f(n)$ be an additive function (so that $f(ab)=f(a)+f(b)$
if $(a,b)=1$ such that $\limsup_{p,k} f(p^k) \log(p^k) = ∞$.
Is it true that $\limsup_n (f(n+1)−f(n))/ \log n = ∞$?
-/
theorem erdos_897.parts.i : (∀ (f : ℕ → ℝ),
    (∀ᵉ (a > 0) (b > 0), a.Coprime b → f (a * b) = f a + f b) →
    ((Filter.atTop ⊓ Filter.principal {(p, k) : ℕ × ℕ | p.Prime}).limsup
      (fun (p, k) => (f (p^k) / (p^k : ℝ).log : EReal)) = ⊤) →
    Filter.atTop.limsup (fun (n : ℕ) => ((f (n+1) - f n) / (n : ℝ).log : EReal)) = ⊤) ↔
    false := by
  refine' iff_of_false _ ( by decide );
  push_neg;
  use f;
  refine' ⟨ _, _, _ ⟩;
  · intro a ha b hb hab; unfold f; simp +decide
    rw [ Nat.primeFactors_mul ha.ne' hb.ne', Finset.sum_union ];
    · refine' congrArg₂ ( · + · ) ( Finset.sum_congr rfl fun p hp => _ ) ( Finset.sum_congr rfl fun p hp => _ ) <;> simp_all +decide [ Nat.factorization_mul, ha.ne', hb.ne' ];
      · rw [ Nat.factorization_eq_zero_of_not_dvd ( fun h => hp.1.not_dvd_one <| hab.gcd_eq_one ▸ Nat.dvd_gcd hp.2 h ) ] ; aesop;
      · rw [ Nat.factorization_eq_zero_of_not_dvd ( fun h => hp.1.not_dvd_one <| hab.gcd_eq_one ▸ Nat.dvd_gcd h hp.2 ) ] ; aesop;
    · exact hab.disjoint_primeFactors;
  · convert f_hypothesis using 1;
  · refine' ne_of_lt ( lt_of_le_of_lt ( corollary1 ) _ );
    norm_cast

/-
Let $f(n)$ be an additive function (so that $f(ab)=f(a)+f(b)$
if $(a,b)=1$) such that $\limsup_{p,k} f(p^k) \log(p^k) = ∞$.
Is it true that $\limsup_n f(n+1)/ f(n) = ∞$?
-/
theorem erdos_897.parts.ii : (∀ (f : ℕ → ℝ),
    (∀ᵉ (a > 0) (b > 0), a.Coprime b → f (a * b) = f a + f b) →
    ((Filter.atTop ⊓ Filter.principal {(p, k) : ℕ × ℕ | p.Prime}).limsup
      (fun (p, k) => (f (p^k) / (p^k : ℝ).log : EReal)) = ⊤) →
    Filter.atTop.limsup (fun (n : ℕ) => (f (n+1) / f n : EReal)) = ⊤) ↔ false := by
  refine' iff_of_false _ ( by decide );
  push_neg;
  refine' ⟨ f, _, _, _ ⟩;
  · exact fun a ha b hb hab => f_additive ha.ne' hb.ne' hab;
  · convert f_limsup_condition using 1;
  · -- The ratio $f(n+1)/f(n)$ is eventually bounded by a real number $C$.
    have h_ratio_bounded : ∃ C : ℝ, ∀ᶠ n in Filter.atTop, f (n + 1) / f n ≤ C := by
      exact ⟨ _, ratio_bounded.choose_spec ⟩;
    obtain ⟨ C, hC ⟩ := h_ratio_bounded;
    refine' ne_of_lt ( lt_of_le_of_lt ( Filter.limsup_le_of_le _ _ ) _ );
    exact ↑C;
    · use ⊥;
      aesop;
    · filter_upwards [ hC ] with n hn;
      exact EReal.coe_le_coe_iff.mpr hn;
    · exact EReal.coe_lt_top _

#print axioms erdos_897.parts.i
-- 'erdos_897.parts.i' depends on axioms: [propext, Classical.choice, Quot.sound]

#print axioms erdos_897.parts.ii
-- 'erdos_897.parts.ii' depends on axioms: [propext, Classical.choice, Quot.sound]
